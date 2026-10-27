module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer
public import CFSG.Milestones.OO_odd_order_solvable
public import CFSG.GH74.GLS.Stage2.Signalizer.L199PartI

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.L199

open Subgroup CFSG
open scoped commutatorElement

universe u

theorem pCore_quotient_pCore {A : Type u} [Group A] (p : ℕ) [Fact p.Prime] :
    pCore p (A ⧸ pCore p A) = ⊥ := by
  set N : Subgroup A := pCore p A with hN
  set M : Subgroup (A ⧸ N) := pCore p (A ⧸ N) with hM
  set M' : Subgroup A := M.comap (QuotientGroup.mk' N) with hM'
  have hM'n : M'.Normal := (inferInstance : M.Normal).comap _
  have hpg : IsPGroup p ↥M' := by
    intro g
    have h1 := (pCore_isPGroup (p := p) (G := A ⧸ N)) ⟨QuotientGroup.mk' N g.1, g.2⟩
    obtain ⟨a, ha⟩ := h1
    have h2 : (g.1 ^ (p ^ a)) ∈ N := by
      have : (QuotientGroup.mk' N g.1) ^ (p ^ a) = 1 := by
        have := congrArg Subtype.val ha
        simpa using this
      rw [← map_pow] at this
      exact (QuotientGroup.eq_one_iff _).mp this
    have h3 := (pCore_isPGroup (p := p) (G := A)) ⟨g.1 ^ (p ^ a), h2⟩
    obtain ⟨b, hb⟩ := h3
    refine ⟨a + b, ?_⟩
    apply Subtype.ext
    have := congrArg Subtype.val hb
    simp only [OneMemClass.coe_one, SubmonoidClass.coe_pow] at this ⊢
    rw [pow_add, pow_mul]
    exact this
  have hle : M' ≤ N := le_sSup ⟨hM'n, hpg⟩
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  have : a ∈ M' := hx
  have := hle this
  simp only [Subgroup.mem_bot]
  exact (QuotientGroup.eq_one_iff _).mpr this

theorem part_two_base {X : Type u} [Group X] [Finite X] {z : X} {r : ℕ} {R : Subgroup X}
    (h : SigData X z r R) (hr : pCore r X = ⊥) (hR : R ≤ pPrimeCore 2 X) : R = ⊥ := by
  classical
  have : Fact r.Prime := ⟨h.prime⟩
  set Y : Subgroup X := pPrimeCore 2 X with hY
  have hYn : Y.Normal := pPrimeCore_normal
  have hYodd : Odd (Nat.card Y) := Nat.coprime_two_left.1 pPrimeCore_coprime_card
  have hsolv : Group.IsSolvable ↥Y := CFSG.Milestones.odd_order_solvable hYodd
  set F₀ : Subgroup ↥Y := fittingSubgroup ↥Y with hF₀
  set F : Subgroup X := F₀.map Y.subtype with hF
  have hFnormal : F.Normal := inferInstance
  have hnil : Group.IsNilpotent ↥F :=
    Group.nilpotent_of_mulEquiv (Subgroup.equivMapOfInjective F₀ Y.subtype Y.subtype_injective)
  have hFY : F ≤ Y := Subgroup.map_subtype_le F₀
  have hcore : ∀ q : ℕ, q.Prime → q ≠ 2 → R ≤ centralizer ((pCore q X : Subgroup X) : Set X) := by
    intro q hq hq2
    by_cases hqr : q = r
    · subst hqr
      rw [hr]
      intro x _
      simp [Subgroup.mem_centralizer_iff]
    · exact part_one h hq hq2 hqr
  have hRF : R ≤ centralizer (F : Set X) := by
    have hFeq : F = ⨆ q ∈ (Nat.card ↥F).primeFactors,
        ((default : Sylow q ↥F) : Subgroup ↥F).map F.subtype := by
      calc F = (⊤ : Subgroup ↥F).map F.subtype := by
            rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
        _ = _ := by
            rw [← Sylow.iSup_sylow_eq_top (G := ↥F)]
            simp [Subgroup.map_iSup]
    rw [hFeq]
    refine subgroup_le_centralizer_iSup_of_le_centralizer _ (fun q => ?_)
    refine subgroup_le_centralizer_iSup_of_le_centralizer _ (fun hqmem => ?_)
    have hqp : q.Prime := Nat.prime_of_mem_primeFactors hqmem
    have : Fact q.Prime := ⟨hqp⟩
    have hq2 : q ≠ 2 := by
      rintro rfl
      have h1 : 2 ∣ Nat.card ↥F := Nat.dvd_of_mem_primeFactors hqmem
      have h2 : 2 ∣ Nat.card ↥Y := h1.trans (Subgroup.card_dvd_of_le hFY)
      exact (Nat.not_even_iff_odd.2 hYodd) (even_iff_two_dvd.2 h2)
    have hS := _root_.Sylow.map_le_pCore hFnormal hnil q (default : Sylow q ↥F)
    exact (hcore q hqp hq2).trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hS))
  have hRF' : R ≤ F := by
    intro x hx
    have hxY : x ∈ Y := hR hx
    have hmem : (⟨x, hxY⟩ : ↥Y) ∈ centralizer (F₀ : Set ↥Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro f hf
      have hfF : (f : X) ∈ F := ⟨f, hf, rfl⟩
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 (hRF hx) (f : X) hfF)
    have := centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hsolv hmem
    exact ⟨_, this, rfl⟩
  have hRpg : IsPGroup r ↥(R.subgroupOf F) :=
    h.pgroup.of_equiv (Subgroup.subgroupOfEquivOfLe hRF').symm
  obtain ⟨S, hS⟩ := hRpg.exists_le_sylow
  have hSle := _root_.Sylow.map_le_pCore hFnormal hnil r S
  rw [eq_bot_iff]
  intro x hx
  have hxF : x ∈ F := hRF' hx
  have hmem : (⟨x, hxF⟩ : ↥F) ∈ R.subgroupOf F := hx
  have hxS : x ∈ S.map F.subtype := ⟨_, hS hmem, rfl⟩
  have := hSle hxS
  rw [hr] at this
  exact this

theorem part_two {X : Type u} [Group X] [Finite X] {z : X} {r : ℕ} {R : Subgroup X}
    (h : SigData X z r R) (hR : R ≤ pPrimeCore 2 X) : R ≤ pCore r X := by
  have : Fact r.Prime := ⟨h.prime⟩
  set Q : Subgroup X := pCore r X with hQ
  have hQn : Q.Normal := pCore_normal
  have hQodd : Odd (Nat.card Q) := by
    obtain ⟨k, hk⟩ := (pCore_isPGroup (p := r) (G := X)).exists_card_eq
    rw [hQ, hk]
    exact (h.prime.odd_of_ne_two h.ne_two).pow
  have hquot := h.quotient Q hQodd
  have hcore : pCore r (X ⧸ Q) = ⊥ := pCore_quotient_pCore r
  have hY : (pPrimeCore 2 X).map (QuotientGroup.mk' Q) ≤ pPrimeCore 2 (X ⧸ Q) :=
    le_sSup ⟨pPrimeCore_normal.map _ (QuotientGroup.mk'_surjective Q),
      Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd _ _) pPrimeCore_coprime_card⟩
  have hRbar : R.map (QuotientGroup.mk' Q) ≤ pPrimeCore 2 (X ⧸ Q) :=
    (Subgroup.map_mono hR).trans hY
  have hbot := part_two_base hquot hcore hRbar
  intro x hx
  have h1 : QuotientGroup.mk' Q x ∈ R.map (QuotientGroup.mk' Q) := ⟨x, hx, rfl⟩
  rw [hbot] at h1
  exact (QuotientGroup.eq_one_iff x).1 h1

end CFSG.GH74.GLS.Stage2.Signalizer.L199
