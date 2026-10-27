module

public import CFSG.CharacterTheory.Semidihedral.OddCoreQuotient
public import CFSG.CharacterTheory.Wreathed.BrauerWongSylowCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinConvention
public import CFSG.LieType.CurtisTits.Recognition

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.ComponentClassification.CatalogueBPrimeJoin
open scoped commutatorElement

section Core

variable {A B : Type*} [Group A] [Group B] [Finite A]

theorem pPrimeCore_eq_map_of_central (p : ℕ) [Fact p.Prime] (Ψ : A →* B)
    (hΨ : Function.Surjective Ψ) (hc : Ψ.ker ≤ Subgroup.center A) :
    CFSG.pPrimeCore p B = (CFSG.pPrimeCore p A).map Ψ := by
  have : Finite B := Finite.of_surjective Ψ hΨ
  refine le_antisymm ?_
    (CFSG.Semidihedral.OddCoreQuotient.pPrimeCore_map_le_of_surjective p Ψ hΨ)
  set R : Subgroup A := (CFSG.pPrimeCore p B).comap Ψ with hR
  have hRn : R.Normal := Subgroup.Normal.comap inferInstance Ψ
  let P : Sylow p ↥R := Classical.choice inferInstance
  have hPker : ∀ x ∈ (P : Subgroup ↥R), ((x : ↥R) : A) ∈ Ψ.ker := by
    intro x hx
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨x, hx⟩
    have hxk : ((x : ↥R) : A) ^ p ^ k = 1 := congrArg (fun y : ↥(P : Subgroup ↥R) => ((y : ↥R) : A)) hk
    have hmem : Ψ (x : A) ∈ CFSG.pPrimeCore p B := x.2
    set N := CFSG.pPrimeCore p B with hN
    have h1 : orderOf (⟨Ψ (x : A), hmem⟩ : ↥N) ∣ p ^ k :=
      orderOf_dvd_of_pow_eq_one (Subtype.ext (by simp [← map_pow, hxk]))
    have h2 : orderOf (⟨Ψ (x : A), hmem⟩ : ↥N) ∣ Nat.card N := orderOf_dvd_natCard _
    have h3 := Nat.eq_one_of_dvd_coprimes (CFSG.pPrimeCore_coprime_card.pow_left k) h1 h2
    exact congrArg Subtype.val (orderOf_eq_one_iff.1 h3)
  have hPc : (P : Subgroup ↥R) ≤ Subgroup.center ↥R := fun x hx =>
    Subgroup.mem_center_iff.2 fun g =>
      Subtype.ext (Subgroup.mem_center_iff.1 (hc (hPker x hx)) (g : A))
  have hcomp := CFSG.Wreathed.BrauerWong.pPrimeCore_isComplement'_of_le_center P hPc
  set D : Subgroup A := (CFSG.pPrimeCore p ↥R).map R.subtype with hD
  have hDn : D.Normal := by
    refine ⟨fun d hd a => ?_⟩
    obtain ⟨r, hr, rfl⟩ := hd
    have hmap := CFSG.pPrimeCore_map_iso p (MulAut.conjNormal (H := R) a)
    have : (MulAut.conjNormal (H := R) a) r ∈ CFSG.pPrimeCore p ↥R := by
      rw [← hmap]
      exact Subgroup.mem_map_of_mem _ hr
    exact ⟨_, this, by simp [MulAut.conjNormal_apply]⟩
  have hDle : D ≤ CFSG.pPrimeCore p A := by
    refine le_sSup ⟨hDn, ?_⟩
    rw [hD, Subgroup.card_map_of_injective R.subtype_injective]
    exact CFSG.pPrimeCore_coprime_card
  intro y hy
  obtain ⟨r', hr'⟩ := hΨ y
  have hr'R : r' ∈ R := by
    change Ψ r' ∈ CFSG.pPrimeCore p B
    rw [hr']
    exact hy
  obtain ⟨⟨d, q⟩, hdq⟩ := hcomp.2 ⟨r', hr'R⟩
  have hdq' : ((d : ↥R) : A) * ((q : ↥R) : A) = r' := congrArg Subtype.val hdq
  have hq1 : Ψ ((q : ↥R) : A) = 1 := hPker _ q.2
  refine Subgroup.mem_map.2 ⟨((d : ↥R) : A), hDle ⟨d, d.2, rfl⟩, ?_⟩
  rw [← hr', ← hdq', map_mul, hq1, mul_one]

theorem isQuasisimple_of_central_cover {N Q : Type*} [Group N] [Group Q] (f : N →* Q)
    (hf : Function.Surjective f) (hperf : Group.IsPerfect N) (hker : f.ker ≤ Subgroup.center N)
    (hQ : CFSG.IsQuasisimple Q) : CFSG.IsQuasisimple N := by
  obtain ⟨-, hsimple, hnc⟩ := hQ
  let g : N →* Q ⧸ Subgroup.center Q := (QuotientGroup.mk' (Subgroup.center Q)).comp f
  have hg : Function.Surjective g := (QuotientGroup.mk'_surjective _).comp hf
  have hW : g.ker ≤ Subgroup.center N := by
    have h1 : ⁅g.ker, (⊤ : Subgroup N)⁆ ≤ Subgroup.center N := by
      rw [Subgroup.commutator_le]
      intro w hw n _
      apply hker
      rw [MonoidHom.mem_ker, map_commutatorElement]
      have hfw : f w ∈ Subgroup.center Q := (QuotientGroup.eq_one_iff _).1 hw
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_center_iff.1 hfw (f n)).symm
    have h2 : ⁅⁅g.ker, (⊤ : Subgroup N)⁆, (⊤ : Subgroup N)⁆ = ⊥ := by
      refine le_antisymm ?_ bot_le
      calc ⁅⁅g.ker, (⊤ : Subgroup N)⁆, (⊤ : Subgroup N)⁆
          ≤ ⁅Subgroup.center N, (⊤ : Subgroup N)⁆ := Subgroup.commutator_mono_left h1
        _ = ⊥ := by
          refine le_antisymm ?_ bot_le
          rw [Subgroup.commutator_le]
          intro z hz n _
          rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
          exact (Subgroup.mem_center_iff.1 hz n).symm
    have h3 : ⁅⁅(⊤ : Subgroup N), g.ker⁆, (⊤ : Subgroup N)⁆ = ⊥ := by
      rw [Subgroup.commutator_comm (⊤ : Subgroup N) g.ker]; exact h2
    have h4 := Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := (⊤ : Subgroup N))
      (H₂ := (⊤ : Subgroup N)) (H₃ := g.ker) h3 h2
    have hc : ⁅(⊤ : Subgroup N), (⊤ : Subgroup N)⁆ = ⊤ := by
      rw [← commutator_def]; exact hperf.commutator_eq_top
    rw [hc] at h4
    intro w hw
    rw [Subgroup.mem_center_iff]
    intro n
    have : ⁅n, w⁆ ∈ ⁅(⊤ : Subgroup N), g.ker⁆ := Subgroup.commutator_mem_commutator trivial hw
    rw [h4, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this
  let e : N ⧸ g.ker ≃* Q ⧸ Subgroup.center Q := QuotientGroup.quotientKerEquivOfSurjective g hg
  refine CFSG.LieType.CurtisTits.isQuasisimple_of_isSimpleGroup_quotient g.ker hW hperf
    ((MulEquiv.isSimpleGroup_congr e).mpr hsimple) ?_
  obtain ⟨a, b, hab⟩ := hnc
  exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩

theorem exists_centralLift (p : ℕ) [Fact p.Prime] (Ψ : A →* B) (hΨ : Function.Surjective Ψ)
    (hc : Ψ.ker ≤ Subgroup.center A) :
    ∃ lam : (A ⧸ CFSG.pPrimeCore p A) →* (B ⧸ CFSG.pPrimeCore p B),
      (∀ a, lam (QuotientGroup.mk a) = QuotientGroup.mk (Ψ a)) ∧ Function.Surjective lam ∧
        lam.ker ≤ Subgroup.center (A ⧸ CFSG.pPrimeCore p A) := by
  have hle : CFSG.pPrimeCore p A ≤ (CFSG.pPrimeCore p B).comap Ψ := by
    rw [← Subgroup.map_le_iff_le_comap]
    exact CFSG.Semidihedral.OddCoreQuotient.pPrimeCore_map_le_of_surjective p Ψ hΨ
  refine ⟨QuotientGroup.map _ _ Ψ hle, fun a => rfl, ?_, ?_⟩
  · intro y
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨a, rfl⟩ := hΨ b
    exact ⟨QuotientGroup.mk a, rfl⟩
  · intro k hk
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective k
    have h1 : Ψ a ∈ CFSG.pPrimeCore p B := (QuotientGroup.eq_one_iff _).1 hk
    rw [pPrimeCore_eq_map_of_central p Ψ hΨ hc] at h1
    obtain ⟨o, ho, hoa⟩ := h1
    have hz : o⁻¹ * a ∈ Ψ.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, hoa, inv_mul_cancel]
    have hmk : (QuotientGroup.mk a : A ⧸ CFSG.pPrimeCore p A) = QuotientGroup.mk (o⁻¹ * a) := by
      have : a = o * (o⁻¹ * a) := by group
      conv_lhs => rw [this]
      rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff o).2 ho, one_mul]
    rw [hmk, Subgroup.mem_center_iff]
    intro g
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    exact congrArg _ (Subgroup.mem_center_iff.1 (hc hz) g)

theorem isPerfect_of_isPComponent {G : Type*} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    {L : Subgroup G} (hL : CFSG.IsPComponent p L) : Group.IsPerfect ↥L := by
  obtain ⟨-, hres, hq⟩ := (pComponent_iff_subnormal_generated_quasisimple p L).1 hL
  set N := CFSG.pPrimeCore p ↥L with hN
  set C : Subgroup ↥L := commutator ↥L with hC
  have hCn : C.Normal := inferInstance
  have hCN : C ⊔ N = ⊤ := by
    have h1 : C.map (QuotientGroup.mk' N) = ⊤ := by
      have := hq.1.commutator_eq_top
      rw [hC, commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)]
      rw [commutator_def] at this
      exact this
    have h2 := Subgroup.comap_map_eq (QuotientGroup.mk' N) C
    rw [h1, Subgroup.comap_top, QuotientGroup.ker_mk'] at h2
    exact h2.symm
  have hdvd : Nat.card (↥L ⧸ C) ∣ Nat.card N := by
    let f : ↥N →* ↥L ⧸ C := (QuotientGroup.mk' C).comp N.subtype
    have hf : Function.Surjective f := by
      intro y
      obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective y
      have hl : l ∈ C ⊔ N := by rw [hCN]; trivial
      obtain ⟨c, hc, n, hn, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hl
      refine ⟨⟨n, hn⟩, ?_⟩
      show (QuotientGroup.mk n : ↥L ⧸ C) = QuotientGroup.mk (c * n)
      rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff c).2 hc, one_mul]
    exact Subgroup.card_dvd_of_surjective hf
  have hle : primeResidual p ↥L ≤ C := by
    refine sSup_le fun P hP => ?_
    have hPm : IsPGroup p (P.map (QuotientGroup.mk' C)) := hP.map _
    obtain ⟨k, hk⟩ := hPm.exists_card_eq
    have hcard : Nat.card (P.map (QuotientGroup.mk' C)) = 1 := by
      refine Nat.eq_one_of_dvd_coprimes
        ((CFSG.pPrimeCore_coprime_card (p := p) (G := ↥L)).pow_left k) ?_ ?_
      · rw [hk]
      · exact (Subgroup.card_subgroup_dvd_card _).trans hdvd
    have hbot := (Subgroup.card_eq_one.1 hcard)
    intro x hx
    have : QuotientGroup.mk' C x ∈ P.map (QuotientGroup.mk' C) := Subgroup.mem_map_of_mem _ hx
    rw [hbot, Subgroup.mem_bot] at this
    exact (QuotientGroup.eq_one_iff x).1 this
  rw [hres] at hle
  exact ⟨top_le_iff.1 hle⟩

theorem ker_subgroupMap_le_center (Φ : A →* B) (hc : Φ.ker ≤ Subgroup.center A)
    (J : Subgroup A) : (Φ.subgroupMap J).ker ≤ Subgroup.center ↥J := by
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro g
  have hx' : ((x : ↥J) : A) ∈ Φ.ker := by
    have := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
    exact this
  exact Subtype.ext (Subgroup.mem_center_iff.1 (hc hx') (g : A))

theorem isPComponent_map_central (p : ℕ) [Fact p.Prime] (Φ : A →* B)
    (hΦ : Function.Surjective Φ) (hc : Φ.ker ≤ Subgroup.center A) {J : Subgroup A}
    (hJ : CFSG.IsPComponent p J) : CFSG.IsPComponent p (J.map Φ) := by
  have : Finite B := Finite.of_surjective Φ hΦ
  obtain ⟨hsn, hres, hq⟩ := (pComponent_iff_subnormal_generated_quasisimple p J).1 hJ
  set ψ := Φ.subgroupMap J with hψdef
  have hψ : Function.Surjective ψ := MonoidHom.subgroupMap_surjective Φ J
  have hkc := ker_subgroupMap_le_center Φ hc J
  refine (pComponent_iff_subnormal_generated_quasisimple p (J.map Φ)).2
    ⟨hsn.map hΦ, ?_, ?_⟩
  · have := primeResidual_map_surjective p ψ hψ
    rw [hres, Subgroup.map_top_of_surjective ψ hψ] at this
    exact this.symm
  · obtain ⟨lam, hlam, hlams, hlamk⟩ := exists_centralLift p ψ hψ hkc
    refine CFSG.LieType.CurtisTits.isQuasisimple_of_surjective hq hlams ?_
    by_contra hall
    push Not at hall
    have hcen : ∀ k : ↥J ⧸ CFSG.pPrimeCore p ↥J, k ∈ Subgroup.center (↥J ⧸ CFSG.pPrimeCore p ↥J) :=
      fun k => hlamk (MonoidHom.mem_ker.2 (hall k))
    obtain ⟨-, -, a, b, hab⟩ := hq
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    apply hab
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    exact congrArg _ (Subgroup.mem_center_iff.1 (hcen b) a)

theorem exists_isPComponent_map_central (p : ℕ) [Fact p.Prime] (Φ : A →* B)
    (hΦ : Function.Surjective Φ) (hc : Φ.ker ≤ Subgroup.center A) {J' : Subgroup B}
    (hJ' : CFSG.IsPComponent p J') :
    ∃ J : Subgroup A, CFSG.IsPComponent p J ∧ J.map Φ = J' := by
  have : Finite B := Finite.of_surjective Φ hΦ
  have hJ'perf := isPerfect_of_isPComponent p hJ'
  have hJ'res := primeResidual_eq_top_of_pComponent p J' hJ'
  have hJ'q := (pComponent_iff_subnormal_generated_quasisimple p J').1 hJ'
  set 𝒮 : Set (Subgroup A) := {S | S.IsSubnormal ∧ S.map Φ = J'} with h𝒮
  have hS₀ : J'.comap Φ ∈ 𝒮 :=
    ⟨hJ'q.1.comap Φ, Subgroup.map_comap_eq_self_of_surjective hΦ J'⟩
  obtain ⟨J, ⟨hJsn, hJmap⟩, hmin⟩ := (wellFounded_lt (α := Subgroup A)).has_min 𝒮 ⟨_, hS₀⟩
  subst hJmap
  set ψ := Φ.subgroupMap J with hψdef
  have hψ : Function.Surjective ψ := MonoidHom.subgroupMap_surjective Φ J
  have hkc := ker_subgroupMap_le_center Φ hc J
  have hsub : ∀ T : Subgroup ↥J, T.Characteristic → (T.map J.subtype).IsSubnormal := fun T hT =>
    (Subgroup.Normal.isSubnormal (inferInstance : T.Normal)).trans' hJsn
  have hperf : Group.IsPerfect ↥J := by
    have hmem : (commutator ↥J).map J.subtype ∈ 𝒮 := by
      refine ⟨hsub _ inferInstance, ?_⟩
      have h1 : (commutator ↥J).map ψ = commutator ↥(J.map Φ) := by
        rw [commutator_def, commutator_def, Subgroup.map_commutator,
          Subgroup.map_top_of_surjective ψ hψ]
      rw [Subgroup.map_map]
      have h2 : (J.map Φ).subtype.comp ψ = Φ.comp J.subtype := by ext x; rfl
      rw [← h2, ← Subgroup.map_map, h1, hJ'perf.commutator_eq_top, Subgroup.map_top,
        Subgroup.range_subtype]
    have hTeq := eq_of_le_of_not_lt (Subgroup.map_subtype_le _) (hmin _ hmem)
    have : commutator ↥J = ⊤ :=
      Subgroup.map_injective J.subtype_injective (by rw [hTeq, Subgroup.map_top, Subgroup.range_subtype])
    exact ⟨this⟩
  have hres : primeResidual p ↥J = ⊤ := by
    have hmem : (primeResidual p ↥J).map J.subtype ∈ 𝒮 := by
      have := primeResidual_characteristic p ↥J
      refine ⟨hsub _ inferInstance, ?_⟩
      rw [Subgroup.map_map]
      have h2 : (J.map Φ).subtype.comp ψ = Φ.comp J.subtype := by ext x; rfl
      rw [← h2, ← Subgroup.map_map, primeResidual_map_surjective p ψ hψ, hJ'res, Subgroup.map_top,
        Subgroup.range_subtype]
    have hTeq := eq_of_le_of_not_lt (Subgroup.map_subtype_le _) (hmin _ hmem)
    exact Subgroup.map_injective J.subtype_injective (by rw [hTeq, Subgroup.map_top, Subgroup.range_subtype])
  refine ⟨J, (pComponent_iff_subnormal_generated_quasisimple p J).2 ⟨hJsn, hres, ?_⟩, rfl⟩
  obtain ⟨lam, hlam, hlams, hlamk⟩ := exists_centralLift p ψ hψ hkc
  exact isQuasisimple_of_central_cover lam hlams (Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)) hlamk hJ'q.2.2

end Core

end CFSG.HardMathSupport.Solomon.Coordinator
