module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58NFn
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58NFo
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig33G
public import CFSG.Holt.General.ComponentsImage
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58NFj

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup Equiv CFSG.ComponentClassification CFSG.ComponentClassification.UnbalancedLayer
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

namespace NFAlt

open scoped Classical in
theorem fixedComponent_eq {n : ℕ} {τ : Perm (Fin n)} (hτ2 : orderOf τ = 2)
    {P : Subgroup (alternatingGroup (Fin n))}
    (hPF : P ≤ fixedSubgroup (MulAut.conjNormal (H := alternatingGroup (Fin n)) τ))
    (hP : IsPComponent 2 (P.subgroupOf
      (fixedSubgroup (MulAut.conjNormal (H := alternatingGroup (Fin n)) τ)))) :
    5 ≤ Nat.card (MulAction.fixedPoints (zpowers τ) (Fin n)) ∧
      ∀ x : Perm (Fin n), (∃ p ∈ P, (p : Perm (Fin n)) = x) ↔
        ∃ f ∈ alternatingGroup (MulAction.fixedPoints (zpowers τ) (Fin n)),
          (CatalogueBAlternating.fixedPointsNormalizerHom (zpowers τ) f : Perm (Fin n)) = x := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set c := (MulAut.conjNormal (H := alternatingGroup (Fin n)) :
    Perm (Fin n) →* MulAut (alternatingGroup (Fin n))) with hcdef
  have hcapp : ∀ x : alternatingGroup (Fin n), ((c τ x : alternatingGroup (Fin n)) : Perm (Fin n))
      = τ * x * τ⁻¹ := fun x => rfl
  set Q : Subgroup (Perm (Fin n)) := zpowers τ with hQdef
  have hQ : IsPGroup 2 Q := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hτ2, pow_one])
  set N := normalizer (Q : Set (Perm (Fin n))) with hNdef
  set F := fixedSubgroup (c τ) with hFdef
  have hmemF : ∀ x : alternatingGroup (Fin n), x ∈ F ↔ τ * (x : Perm (Fin n)) = x * τ := by
    intro x
    change c τ x = x ↔ _
    constructor
    · intro hx
      have h1 := congrArg Subtype.val hx
      rw [hcapp] at h1
      calc τ * (x : Perm (Fin n)) = τ * x * τ⁻¹ * τ := by group
        _ = x * τ := by rw [h1]
    · intro hx
      apply Subtype.ext
      rw [hcapp, hx]
      group
  have hcN : ∀ g : Perm (Fin n), τ * g = g * τ → g ∈ N := by
    intro g hg
    apply Subgroup.centralizer_le_normalizer
    rw [hQdef, ← Subgroup.zpowers_le, Subgroup.zpowers_le, mem_centralizer_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hh
    exact (Commute.zpow_left (show Commute τ g from hg) k).eq
  let ι : F →* N := ((alternatingGroup (Fin n)).subtype.comp F.subtype).codRestrict N
    fun x => hcN _ ((hmemF x.1).mp x.2)
  have hι : Function.Injective ι := by
    intro x y hxy
    have h1 : ((x : alternatingGroup (Fin n)) : Perm (Fin n)) = ((y : alternatingGroup (Fin n)) :
        Perm (Fin n)) := congrArg (fun z : N => (z : Perm (Fin n))) hxy
    exact Subtype.ext (Subtype.ext h1)
  set R : Subgroup N := (alternatingGroup (Fin n)).subgroupOf N with hRdef
  have hrange : ι.range = R := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      exact (x : alternatingGroup (Fin n)).2
    · intro y hy
      have hyA : (y : Perm (Fin n)) ∈ alternatingGroup (Fin n) := hy
      have hyτ : (y : Perm (Fin n)) * τ * (y : Perm (Fin n))⁻¹ ∈ Q :=
        (mem_normalizer_iff.mp y.2 τ).mp (mem_zpowers τ)
      have hyτ' : (y : Perm (Fin n)) * τ * (y : Perm (Fin n))⁻¹ = τ := by
        have hord : orderOf ((y : Perm (Fin n)) * τ * (y : Perm (Fin n))⁻¹) = 2 := by
          rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hτ2]
        obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hyτ
        rw [← hk] at hord ⊢
        rcases Int.emod_two_eq_zero_or_one k with hk2 | hk2
        · rw [← zpow_mod_orderOf, hτ2, show ((2 : ℕ) : ℤ) = 2 from rfl, hk2, zpow_zero,
            orderOf_one] at hord
          omega
        · rw [← zpow_mod_orderOf, hτ2, show ((2 : ℕ) : ℤ) = 2 from rfl, hk2, zpow_one]
      have hcomm : τ * (y : Perm (Fin n)) = (y : Perm (Fin n)) * τ := by
        calc τ * (y : Perm (Fin n)) = (y : Perm (Fin n)) * τ * (y : Perm (Fin n))⁻¹ * y := by
              rw [hyτ']
          _ = (y : Perm (Fin n)) * τ := by group
      exact ⟨⟨⟨y, hyA⟩, (hmemF ⟨y, hyA⟩).mpr hcomm⟩, Subtype.ext rfl⟩
  let e₁ : F ≃* R := (MonoidHom.ofInjective hι).trans (MulEquiv.subgroupCongr hrange)
  set L₀ := P.subgroupOf F with hL₀def
  have hL₁ : IsPComponent 2 (L₀.map e₁.toMonoidHom) :=
    LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2 e₁ hP
  have hL := CatalogueBAlternating.pComponent_of_normal_subgroup 2 R (L₀.map e₁.toMonoidHom) hL₁
  set L := (L₀.map e₁.toMonoidHom).map R.subtype with hLdef
  obtain ⟨hdeg, hLeq, -⟩ := CatalogueBAlternating.symmetric_normalizer_pComponent 2 Q hQ L hL
  refine ⟨hdeg, fun x => ?_⟩
  have hmemL : ∀ z : N, z ∈ L ↔ ∃ p ∈ P, (p : Perm (Fin n)) = z := by
    intro z
    constructor
    · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      exact ⟨(w : alternatingGroup (Fin n)), mem_subgroupOf.mp hw, rfl⟩
    · rintro ⟨p, hp, hpz⟩
      have hpF : p ∈ F := hPF hp
      refine ⟨e₁ ⟨p, hpF⟩, ⟨⟨p, hpF⟩, mem_subgroupOf.mpr hp, rfl⟩, ?_⟩
      apply Subtype.ext
      exact hpz
  constructor
  · rintro ⟨p, hp, rfl⟩
    have hpN : (p : Perm (Fin n)) ∈ N := hcN _ ((hmemF p).mp (hPF hp))
    have h1 : (⟨p, hpN⟩ : N) ∈ L := (hmemL _).mpr ⟨p, hp, rfl⟩
    rw [hLeq] at h1
    obtain ⟨f, hf, hfz⟩ := h1
    exact ⟨f, hf, congrArg Subtype.val hfz⟩
  · rintro ⟨f, hf, rfl⟩
    have h1 : CatalogueBAlternating.fixedPointsNormalizerHom (zpowers τ) f ∈ L := by
      rw [hLeq]
      exact ⟨f, hf, rfl⟩
    exact (hmemL _).mp h1

open scoped Classical in
theorem fixes_of_commute {n : ℕ} {Q : Subgroup (Perm (Fin n))}
    (hF : 4 ≤ Nat.card (MulAction.fixedPoints Q (Fin n))) {e : Perm (Fin n)}
    (hpres : ∀ x ∈ MulAction.fixedPoints Q (Fin n), e x ∈ MulAction.fixedPoints Q (Fin n))
    (hcomm : ∀ f ∈ alternatingGroup (MulAction.fixedPoints Q (Fin n)),
      e * (CatalogueBAlternating.fixedPointsNormalizerHom Q f : Perm (Fin n)) =
        (CatalogueBAlternating.fixedPointsNormalizerHom Q f : Perm (Fin n)) * e) :
    ∀ x ∈ MulAction.fixedPoints Q (Fin n), e x = x := by
  classical
  set Ω := MulAction.fixedPoints Q (Fin n) with hΩ
  intro x hx
  by_contra hne
  set q := e x with hqdef
  have hqx : q ≠ x := hne
  have hcard : 4 ≤ (Finset.univ : Finset Ω).card := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
    exact hF
  set S := ((Finset.univ : Finset Ω).erase ⟨x, hx⟩).erase ⟨q, hpres x hx⟩ with hSdef
  have hScard : 1 < S.card := by
    have h1 := Finset.card_erase_le (s := (Finset.univ : Finset Ω)) (a := ⟨x, hx⟩)
    rw [hSdef, Finset.card_erase_of_mem, Finset.card_erase_of_mem (Finset.mem_univ _)]
    · omega
    · rw [Finset.mem_erase]
      exact ⟨fun h => hqx (congrArg Subtype.val h), Finset.mem_univ _⟩
  obtain ⟨r, hr, s, hs, hrs⟩ := Finset.one_lt_card.mp hScard
  have hrq : r ≠ ⟨q, hpres x hx⟩ := (Finset.mem_erase.mp hr).1
  have hrx : r ≠ ⟨x, hx⟩ := (Finset.mem_erase.mp (Finset.mem_erase.mp hr).2).1
  have hsq : s ≠ ⟨q, hpres x hx⟩ := (Finset.mem_erase.mp hs).1
  have hsx : s ≠ ⟨x, hx⟩ := (Finset.mem_erase.mp (Finset.mem_erase.mp hs).2).1
  set f : Perm Ω := swap ⟨q, hpres x hx⟩ r * swap r s with hfdef
  have hfA : f ∈ alternatingGroup Ω := by
    rw [Perm.mem_alternatingGroup, hfdef, Perm.sign_mul, Perm.sign_swap (Ne.symm hrq),
      Perm.sign_swap hrs]
    decide
  have hfx : f ⟨x, hx⟩ = ⟨x, hx⟩ := by
    have hxq : (⟨x, hx⟩ : Ω) ≠ ⟨q, hpres x hx⟩ := fun h => hqx (congrArg Subtype.val h).symm
    rw [hfdef, Perm.mul_apply, swap_apply_of_ne_of_ne (Ne.symm hrx) (Ne.symm hsx),
      swap_apply_of_ne_of_ne hxq (Ne.symm hrx)]
  have hfq : f ⟨q, hpres x hx⟩ = r := by
    rw [hfdef, Perm.mul_apply, swap_apply_of_ne_of_ne (Ne.symm hrq) (Ne.symm hsq),
      swap_apply_left]
  have h1 := congrArg (fun z : Perm (Fin n) => z x) (hcomm f hfA)
  simp only [Perm.mul_apply, CatalogueBAlternating.fixedPointsNormalizerHom_coe] at h1
  rw [Perm.ofSubtype_apply_of_mem _ hx, hfx, Perm.ofSubtype_apply_of_mem _ (hpres x hx), hfq] at h1
  exact hrq (Subtype.ext h1.symm)

theorem mem_coreActionKernel_of_commute {X : Type*} [Group X] {M : Subgroup X} {g : X}
    (hg : ∀ m ∈ M, m * g = g * m) : g ∈ coreActionKernel M := by
  have hconj : ∀ m ∈ M, g * m * g⁻¹ = m := fun m hm => by rw [← hg m hm]; group
  refine mem_coreActionKernel.mpr ⟨?_, fun j hj => ?_⟩
  · rw [mem_normalizer_iff]
    intro m
    constructor
    · intro hm
      rw [hconj m hm]
      exact hm
    · intro hm
      have h1 : m = g⁻¹ * (g * m * g⁻¹) * g := by group
      have h2 : g⁻¹ * (g * m * g⁻¹) * g = g * m * g⁻¹ := by
        calc g⁻¹ * (g * m * g⁻¹) * g = g⁻¹ * ((g * m * g⁻¹) * g) := by group
          _ = g⁻¹ * (g * (g * m * g⁻¹)) := by rw [hg _ hm]
          _ = g * m * g⁻¹ := by group
      rw [h1, h2]
      exact hm
  · have h1 : g⁻¹ * j * g = j := by
      calc g⁻¹ * j * g = g⁻¹ * (j * g) := by group
        _ = g⁻¹ * (g * j) := by rw [hg j hj]
        _ = j := by group
    rw [show j⁻¹ * g⁻¹ * j * g = j⁻¹ * (g⁻¹ * j * g) by group, h1, inv_mul_cancel]
    exact one_mem _

end NFAlt

namespace Hyp52

variable {X : Type} [Group X] [Finite X]

theorem noFusion_of_alternating (h : Hyp52 X) {y : X} (hc : h.SecCond y)
    (hSyl : Seven.IsSylowIn (h.S ⊓ h.secG0 y) (centralizer ({h.a} : Set X) ⊓ h.secG0 y))
    {g : X} (hgG : g ∈ h.secG0 y)
    (hgN : g ∈ normalizer ((h.secJ0 y ⊔ h.secB0 y : Subgroup X) : Set X))
    (hgS : g ∈ normalizer ((h.S ⊓ h.secG0 y : Subgroup X) : Set X)) (hg2 : IsPGroup 2 (zpowers g))
    (hga : g * h.a * g⁻¹ * h.a⁻¹ ∈ h.secB0 y)
    (hb2 : (h.S ⊓ h.secG0 y ⊔ zpowers g) ⊓ normalizer (h.B : Set X) ≤ h.S ⊓ h.secG0 y)
    {M : Subgroup X} (hMB0 : M ≤ centralizer (h.secB0 y : Set X)) (hVM : h.V ≤ M)
    (hJM : h.secJ0 y ≤ M)
    (hMN : ∀ x ∈ h.secG0 y, x ∈ normalizer (h.secJ0 y : Set X) → x ∈ normalizer (M : Set X))
    {n : ℕ} (hn : 7 ≤ n) (θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n)) :
    g * h.a = h.a * g := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set G₀ := h.secG0 y with hG₀
  set S₀ := h.S ⊓ G₀ with hS₀
  set R := S₀ ⊔ zpowers g with hRdef
  have hS02 : IsPGroup 2 S₀ := h.isPGroup_S.to_le inf_le_left
  have hgS0 : zpowers g ≤ normalizer (S₀ : Set X) := zpowers_le.mpr hgS
  have hR2 : IsPGroup 2 R := IsPGroup.to_sup_of_normal_left' hS02 hg2 hgS0
  have hSJ : ∀ s ∈ S₀, s ∈ normalizer (h.secJ0 y : Set X) := fun s hs =>
    Hyp52.mem_normalizer_secJ0 (mem_inf.mp hs).2 (mem_inf.mp (h.S_le (mem_inf.mp hs).1)).2
  have hgJ : g ∈ normalizer (h.secJ0 y : Set X) := Hyp52.mem_normalizer_secJ0_of_sup hgN
  have hSN : S₀ ≤ normalizer (M : Set X) := fun s hs => hMN s (mem_inf.mp hs).2 (hSJ s hs)
  have hRN : R ≤ normalizer (M : Set X) := sup_le hSN (zpowers_le.mpr (hMN g hgG hgJ))
  have hP0S : h.secP0 y ≤ S₀ := inf_le_left
  have hBS : h.B ≤ S₀ := (Hyp52.SecCond.B_le_secP0 hc).trans hP0S
  have hyS : y ∈ S₀ := hP0S (Hyp52.SecCond.y_mem_secP0 hc)
  have haS : h.a ∈ S₀ := hP0S (Hyp52.SecCond.a_mem_secP0 hc)
  have haN : h.a ∈ normalizer (M : Set X) := hRN (mem_sup_left haS)
  have ha2 : h.a * h.a = 1 := by rw [← sq, ← h.orderOf_a, pow_orderOf_eq_one]
  have hMG : M ≤ G₀ := hMB0.trans (centralizer_le_normalizer _)
  have hB0K : h.secB0 y ≤ coreActionKernel M := fun b hb =>
    NFAlt.mem_coreActionKernel_of_commute fun m hm => (mem_centralizer_iff.mp (hMB0 hm) b hb).symm
  obtain ⟨ρ, hρ⟩ := SolMax.exists_isPermAction (M := M) (by omega) (by omega) θ
  have hρ1 : ∀ (x : X) (hx : x ∈ normalizer (M : Set X)), ρ ⟨x, hx⟩ = 1 →
      x ∈ coreActionKernel M := fun x hx h1 => hρ.mem_coreActionKernel hx h1
  have hU : R ⊓ coreActionKernel M ≤ h.secB0 y :=
    h.inf_coreActionKernel_le_secB0 hR2 (hBS.trans le_sup_left) (mem_sup_left hyS) hRN hVM
  let F : Subgroup X :=
    { carrier := {t | t ∈ normalizer (h.secB0 y : Set X) ∧ t * h.a * t⁻¹ * h.a⁻¹ ∈ h.secB0 y}
      one_mem' := ⟨one_mem _, by simp⟩
      mul_mem' := by
        rintro t₁ t₂ ⟨ht₁N, ht₁⟩ ⟨ht₂N, ht₂⟩
        refine ⟨mul_mem ht₁N ht₂N, ?_⟩
        rw [show t₁ * t₂ * h.a * (t₁ * t₂)⁻¹ * h.a⁻¹ =
          (t₁ * (t₂ * h.a * t₂⁻¹ * h.a⁻¹) * t₁⁻¹) * (t₁ * h.a * t₁⁻¹ * h.a⁻¹) by group]
        exact mul_mem ((mem_normalizer_iff.mp ht₁N _).mp ht₂) ht₁
      inv_mem' := by
        rintro t ⟨htN, ht⟩
        refine ⟨inv_mem htN, ?_⟩
        rw [show t⁻¹ * h.a * t⁻¹⁻¹ * h.a⁻¹ = t⁻¹ * (t * h.a * t⁻¹ * h.a⁻¹)⁻¹ * t⁻¹⁻¹ by group]
        exact (mem_normalizer_iff.mp (inv_mem htN) _).mp (inv_mem ht) }
  have hS0F : S₀ ≤ F := by
    intro s hs
    refine ⟨(mem_inf.mp hs).2, ?_⟩
    rw [show s * h.a * s⁻¹ * h.a⁻¹ = 1 by rw [h.comm_a (mem_inf.mp hs).1]; group]
    exact one_mem _
  have hRF : R ≤ F := sup_le hS0F (zpowers_le.mpr ⟨hgG, hga⟩)
  set σ := ρ ⟨h.a, haN⟩ with hσdef
  let ρR : ↥R →* Perm (Fin n) := ρ.comp (inclusion hRN)
  have hρR : ∀ r : ↥R, ρR r = ρ ⟨r, hRN r.2⟩ := fun _ => rfl
  set G' : Subgroup (Perm (Fin n)) := ρR.range with hG'def
  set H' : Subgroup (Perm (Fin n)) := (S₀.subgroupOf R).map ρR with hH'def
  set E' : Subgroup (Perm (Fin n)) := ((h.B).subgroupOf R).map ρR with hE'def
  have hG'2 : IsPGroup 2 G' := hR2.of_surjective ρR.rangeRestrict ρR.rangeRestrict_surjective
  have hH'G : H' ≤ G' := by
    rintro _ ⟨r, -, rfl⟩
    exact ⟨r, rfl⟩
  have hG'σ : G' ≤ centralizer ({σ} : Set (Perm (Fin n))) := by
    rintro _ ⟨r, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have hrF := hRF r.2
    have h1 : (r : X) * h.a * (r : X)⁻¹ * h.a⁻¹ ∈ coreActionKernel M := hB0K hrF.2
    have h2 := hρ.eq_one_of_mem_coreActionKernel (by omega) h1
    have h3 : (⟨(r : X) * h.a * (r : X)⁻¹ * h.a⁻¹, h1.1⟩ : ↥(normalizer (M : Set X))) =
        ⟨r, hRN r.2⟩ * ⟨h.a, haN⟩ * (⟨r, hRN r.2⟩ : ↥(normalizer (M : Set X)))⁻¹ *
          (⟨h.a, haN⟩ : ↥(normalizer (M : Set X)))⁻¹ := rfl
    rw [h3, map_mul, map_mul, map_mul, map_inv, map_inv] at h2
    rw [hρR]
    calc ρ ⟨r, hRN r.2⟩ * σ = ρ ⟨r, hRN r.2⟩ * σ * (ρ ⟨r, hRN r.2⟩)⁻¹ * σ⁻¹ * σ *
          ρ ⟨r, hRN r.2⟩ := by group
      _ = σ * ρ ⟨r, hRN r.2⟩ := by rw [h2, one_mul]
  have hN : ∀ π ∈ G', (∀ e ∈ E', π * e * π⁻¹ ∈ E') → π ∈ H' := by
    rintro _ ⟨r, rfl⟩ hπ
    have hconjB : ∀ (w : ↥R), (w : X) ∈ h.B → (r : X) * w * (r : X)⁻¹ ∈ h.B := by
      intro w hw
      obtain ⟨b, hb, hbw⟩ := hπ (ρR w) ⟨w, mem_subgroupOf.mpr hw, rfl⟩
      have h1 : ρR (b⁻¹ * (r * w * r⁻¹)) = 1 := by
        rw [map_mul, map_inv, map_mul, map_mul, map_inv, hbw]
        group
      have h2 : ((b⁻¹ * (r * w * r⁻¹) : ↥R) : X) ∈ coreActionKernel M :=
        hρ1 _ (hRN (b⁻¹ * (r * w * r⁻¹)).2) h1
      have h3 : ((b⁻¹ * (r * w * r⁻¹) : ↥R) : X) ∈ h.secB0 y :=
        hU (mem_inf.mpr ⟨(b⁻¹ * (r * w * r⁻¹)).2, h2⟩)
      have h4 : (r : X) * w * (r : X)⁻¹ = (b : X) * ((b⁻¹ * (r * w * r⁻¹) : ↥R) : X) := by
        simp [mul_assoc]
      rw [h4]
      exact h.B.mul_mem (mem_subgroupOf.mp hb) (h.secB0_le_B y h3)
    have hrB : (r : X) ∈ normalizer (h.B : Set X) := by
      have hle : (h.B).map (MulAut.conj (r : X)).toMonoidHom ≤ h.B := by
        rintro _ ⟨w, hw, rfl⟩
        exact hconjB ⟨w, (hBS.trans le_sup_left) hw⟩ hw
      have heq : (h.B).map (MulAut.conj (r : X)).toMonoidHom = h.B :=
        Subgroup.eq_of_le_of_card_ge hle (by
          rw [Subgroup.card_map_of_injective (MulAut.conj (r : X)).injective])
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq
    have hrS : (r : X) ∈ S₀ := hb2 (mem_inf.mpr ⟨r.2, hrB⟩)
    exact ⟨r, mem_subgroupOf.mpr hrS, rfl⟩
  set Z := M ⊓ centralizer ({h.a} : Set X) with hZdef
  have hZM : Z ≤ M := inf_le_left
  have hZN : Z ≤ normalizer (M : Set X) := hZM.trans le_normalizer
  let ψ : ↥Z →* Perm (Fin n) := ρ.comp (inclusion hZN)
  have hψ : ∀ z : ↥Z, ψ z = ((θ ((⟨z, hZM z.2⟩ : ↥M) : ↥M ⧸ pPrimeCore 2 ↥M) :
      alternatingGroup (Fin n)) : Perm (Fin n)) := fun z =>
    hρ.apply_of_mem (by omega) ⟨z, hZM z.2⟩
  set C := centralizer ({σ} : Set (Perm (Fin n))) ⊓ alternatingGroup (Fin n) with hCdef
  have hψC : ∀ z : ↥Z, ψ z ∈ C := by
    intro z
    refine mem_inf.mpr ⟨?_, ?_⟩
    · rw [mem_centralizer_singleton_iff]
      have hza : (z : X) * h.a = h.a * z := mem_centralizer_singleton_iff.mp (mem_inf.mp z.2).2
      show ρ ⟨z, hZN z.2⟩ * ρ ⟨h.a, haN⟩ = ρ ⟨h.a, haN⟩ * ρ ⟨z, hZN z.2⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hza
    · rw [hψ]
      exact (θ _).2
  have hψsurj : ∀ π ∈ C, ∃ z : ↥Z, ψ z = π := by
    intro π hπ
    obtain ⟨hπσ, hπA⟩ := mem_inf.mp hπ
    have hb : ((⟨π, hπA⟩ : alternatingGroup (Fin n)) : Perm (Fin n)) * ρ ⟨h.a, haN⟩ =
        ρ ⟨h.a, haN⟩ * ((⟨π, hπA⟩ : alternatingGroup (Fin n)) : Perm (Fin n)) :=
      mem_centralizer_singleton_iff.mp hπσ
    obtain ⟨x, hxa, hxθ⟩ := hρ.exists_lift haN ha2 hb
    refine ⟨⟨x, mem_inf.mpr ⟨x.2, hxa⟩⟩, ?_⟩
    rw [hψ]
    exact congrArg Subtype.val hxθ
  obtain ⟨-, PZ, hPZ⟩ := h.isSylowIn_inf_centralizer hSyl
    (hMB0.trans (centralizer_le_normalizer _)) hSN
  let ψC : ↥Z →* ↥C := ψ.codRestrict C hψC
  have hψCsurj : Function.Surjective ψC := fun π => by
    obtain ⟨z, hz⟩ := hψsurj π π.2
    exact ⟨z, Subtype.ext hz⟩
  let PC : Sylow 2 ↥C := PZ.mapSurjective hψCsurj
  set V : Subgroup (Perm (Fin n)) := ((S₀ ⊓ Z).subgroupOf Z).map ψ with hVdef
  have hVPC : V = (PC : Subgroup ↥C).map C.subtype := by
    rw [hVdef, Sylow.coe_mapSurjective, hPZ, Subgroup.map_map]
    rfl
  have hVC : V ≤ C := by rw [hVPC]; exact map_subtype_le _
  have hVmax : ∀ Q : Subgroup (Perm (Fin n)), Q ≤ C → IsPGroup 2 Q → V ≤ Q → Q = V := by
    intro Q hQC hQ2 hVQ
    have hle : (PC : Subgroup ↥C) ≤ Q.subgroupOf C := by
      intro w hw
      apply mem_subgroupOf.mpr
      exact hVQ (hVPC ▸ ⟨w, hw, rfl⟩)
    have heq := PC.is_maximal' hQ2.comap_subtype hle
    rw [hVPC, ← heq]
    exact (Subgroup.map_subgroupOf_eq_of_le hQC).symm
  have hVH : V ≤ H' := by
    rintro _ ⟨z, hz, rfl⟩
    have hzS : (z : X) ∈ S₀ := (mem_inf.mp (mem_subgroupOf.mp hz)).1
    exact ⟨⟨z, mem_sup_left hzS⟩, mem_subgroupOf.mpr hzS, rfl⟩
  have hσ2 : orderOf σ = 2 := by
    apply orderOf_eq_prime
    · rw [sq, hσdef, ← map_mul]
      have h1 : (⟨h.a, haN⟩ * ⟨h.a, haN⟩ : ↥(normalizer (M : Set X))) = 1 := Subtype.ext ha2
      rw [h1, map_one]
    · intro hσ1
      have haK : h.a ∈ coreActionKernel M := hρ1 h.a haN hσ1
      have haB0 := hU (mem_inf.mpr ⟨mem_sup_left haS, haK⟩)
      exact B5a.a_not_mem_B h (h.secB0_le_B y haB0)
  set Fx := fixedSubgroup (MulAut.conjNormal (H := alternatingGroup (Fin n)) σ) with hFxdef
  have hmemFx : ∀ x : alternatingGroup (Fin n), x ∈ Fx ↔ (x : Perm (Fin n)) ∈ C := by
    intro x
    change MulAut.conjNormal σ x = x ↔ _
    constructor
    · intro hx
      refine mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr ?_, x.2⟩
      have h1 := congrArg Subtype.val hx
      change σ * x * σ⁻¹ = x at h1
      calc (x : Perm (Fin n)) * σ = σ * x * σ⁻¹ * σ := by rw [h1]
        _ = σ * x := by group
    · intro hx
      apply Subtype.ext
      change σ * x * σ⁻¹ = x
      rw [← mem_centralizer_singleton_iff.mp (mem_inf.mp hx).1]
      group
  let θZ : ↥Z →* alternatingGroup (Fin n) :=
    (θ.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 ↥M))).comp (inclusion hZM)
  have hθZ : ∀ z : ↥Z, (θZ z : Perm (Fin n)) = ψ z := fun z => (hψ z).symm
  have hθZFx : ∀ z : ↥Z, θZ z ∈ Fx := fun z => (hmemFx _).mpr (by rw [hθZ]; exact hψC z)
  let φF : ↥Z →* ↥Fx := θZ.codRestrict Fx hθZFx
  have hφF : ∀ z : ↥Z, (((φF z : ↥Fx) : alternatingGroup (Fin n)) : Perm (Fin n)) = ψ z :=
    fun z => hθZ z
  have hφFsurj : Function.Surjective φF := by
    intro w
    obtain ⟨z, hz⟩ := hψsurj (w : Perm (Fin n)) ((hmemFx w).mp w.2)
    refine ⟨z, Subtype.ext (Subtype.ext ?_)⟩
    rw [hφF, hz]
  have hJ0Z : h.secJ0 y ≤ Z := le_inf hJM ((h.secJ0_le y).trans inf_le_left)
  have hJ0pc : IsPComponent 2 ((h.secJ0 y).subgroupOf Z) :=
    UnbalancedCorr.isPComponent_subgroupOf_of_le hJ0Z
      (le_inf inf_le_right (hZM.trans hMB0)) (Hyp52.isPComponent_secJ0 (h := h) (y := y))
  have hJ0ker : ¬ (h.secJ0 y).subgroupOf Z ≤ φF.ker := by
    intro hle
    have hJO : h.secJ0 y ≤ oddCoreIn M := by
      intro j hj
      have h1 := hle (mem_subgroupOf.mpr hj : (⟨j, hJ0Z hj⟩ : ↥Z) ∈ (h.secJ0 y).subgroupOf Z)
      rw [MonoidHom.mem_ker] at h1
      have h2 : θZ ⟨j, hJ0Z hj⟩ = 1 := congrArg Subtype.val h1
      change θ (QuotientGroup.mk' _ ⟨j, hJM hj⟩) = 1 at h2
      rw [map_eq_one_iff _ θ.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
      exact ⟨_, h2, rfl⟩
    have hodd : Nat.Coprime 2 (Nat.card (h.secJ0 y)) := by
      have h1 : Nat.card (h.secJ0 y) ∣ Nat.card (oddCoreIn M) := card_dvd_of_le hJO
      have h2 : Nat.Coprime 2 (Nat.card (oddCoreIn M)) := by
        rw [oddCoreIn, card_map_of_injective M.subtype_injective]
        exact pPrimeCore_coprime_card
      exact h2.coprime_dvd_right h1
    have htop : pPrimeCore 2 ↥(h.secJ0 y) = ⊤ := by
      rw [eq_top_iff]
      exact le_sSup ⟨inferInstance, by rwa [Subgroup.card_top]⟩
    have hq := Hyp52.isQuasisimple_secJ0 (h := h) (y := y)
    have : Nontrivial (↥(h.secJ0 y) ⧸ pPrimeCore 2 ↥(h.secJ0 y)) :=
      LocalCores.isQuasisimple_nontrivial hq
    have : Subsingleton (↥(h.secJ0 y) ⧸ pPrimeCore 2 ↥(h.secJ0 y)) :=
      QuotientGroup.subsingleton_iff.mpr htop
    exact false_of_nontrivial_of_subsingleton (↥(h.secJ0 y) ⧸ pPrimeCore 2 ↥(h.secJ0 y))
  set Jst := ((h.secJ0 y).subgroupOf Z).map φF with hJstdef
  have hJstpc : IsPComponent 2 Jst := CFSG.Holt.General.isPComponent_map hφFsurj hJ0pc hJ0ker
  set P := Jst.map Fx.subtype with hPdef
  have hPsub : P.subgroupOf Fx = Jst :=
    Subgroup.comap_map_eq_self_of_injective Fx.subtype_injective Jst
  obtain ⟨hdeg, hchar⟩ := NFAlt.fixedComponent_eq hσ2 (map_subtype_le Jst)
    (by rw [hPsub]; exact hJstpc)
  have hcharJ : ∀ x : Perm (Fin n), (∃ j ∈ h.secJ0 y, ∃ hj : j ∈ Z, ψ ⟨j, hj⟩ = x) ↔
      ∃ f ∈ alternatingGroup (MulAction.fixedPoints (zpowers σ) (Fin n)),
        (CatalogueBAlternating.fixedPointsNormalizerHom (zpowers σ) f : Perm (Fin n)) = x := by
    intro x
    rw [← hchar]
    constructor
    · rintro ⟨j, hj, hjZ, rfl⟩
      exact ⟨φF ⟨j, hjZ⟩, ⟨φF ⟨j, hjZ⟩, ⟨⟨j, hjZ⟩, mem_subgroupOf.mpr hj, rfl⟩, rfl⟩, hφF _⟩
    · rintro ⟨_, ⟨_, ⟨⟨j, hjZ⟩, hj, rfl⟩, rfl⟩, rfl⟩
      exact ⟨j, mem_subgroupOf.mp hj, hjZ, (hφF _).symm⟩
  set Ω := MulAction.fixedPoints (zpowers σ) (Fin n) with hΩdef
  let ιΩ : alternatingGroup Ω →* Perm (Fin n) :=
    ((normalizer ((zpowers σ : Subgroup (Perm (Fin n))) : Set (Perm (Fin n)))).subtype.comp
      (CatalogueBAlternating.fixedPointsNormalizerHom (zpowers σ))).comp
        (alternatingGroup Ω).subtype
  have hιΩ : Function.Injective ιΩ := by
    intro f₁ f₂ hf
    exact Subtype.ext (CatalogueBAlternating.fixedPointsNormalizerHom_injective _
      (Subtype.ext hf))
  have hOJ : ∀ o ∈ oddCoreIn (h.secJ0 y), ∀ ho : o ∈ Z, ψ ⟨o, ho⟩ = 1 := by
    set Oψ : Subgroup (Perm (Fin n)) := ((oddCoreIn (h.secJ0 y)).subgroupOf Z).map ψ with hOψ
    have hOJ0 : oddCoreIn (h.secJ0 y) ≤ h.secJ0 y := map_subtype_le _
    have hOrange : Oψ ≤ ιΩ.range := by
      rintro _ ⟨⟨o, hoZ⟩, ho, rfl⟩
      obtain ⟨f, hf, hfx⟩ := (hcharJ _).mp ⟨o, hOJ0 (mem_subgroupOf.mp ho), hoZ, rfl⟩
      exact ⟨⟨f, hf⟩, hfx⟩
    set O' : Subgroup (alternatingGroup Ω) := Oψ.comap ιΩ with hO'def
    have hO'n : O'.Normal := by
      constructor
      intro w hw f
      obtain ⟨j, hj, hjZ, hjf⟩ := (hcharJ (ιΩ f)).mpr ⟨f, f.2, rfl⟩
      obtain ⟨⟨o, hoZ⟩, ho, hoe⟩ := (mem_comap.mp hw : ιΩ w ∈ Oψ)
      have hoJ : o ∈ oddCoreIn (h.secJ0 y) := mem_subgroupOf.mp ho
      have hjoj : j * o * j⁻¹ ∈ oddCoreIn (h.secJ0 y) :=
        (mem_normalizer_iff.mp (le_normalizer_oddCoreIn_self _ hj) o).mp hoJ
      refine mem_comap.mpr ⟨⟨j * o * j⁻¹, Z.mul_mem (Z.mul_mem hjZ hoZ) (Z.inv_mem hjZ)⟩,
        mem_subgroupOf.mpr hjoj, ?_⟩
      have h1 : (⟨j * o * j⁻¹, Z.mul_mem (Z.mul_mem hjZ hoZ) (Z.inv_mem hjZ)⟩ : ↥Z) =
          ⟨j, hjZ⟩ * ⟨o, hoZ⟩ * (⟨j, hjZ⟩ : ↥Z)⁻¹ := rfl
      rw [h1, map_mul, map_mul, map_inv, hjf, hoe, map_mul, map_mul, map_inv]
    have hO'odd : Nat.Coprime 2 (Nat.card O') := by
      have h1 : Nat.card O' ∣ Nat.card Oψ := by
        have h2 : Nat.card O' = Nat.card (O'.map ιΩ) :=
          (Nat.card_congr (O'.equivMapOfInjective ιΩ hιΩ).toEquiv)
        rw [h2]
        exact card_dvd_of_le (Subgroup.map_comap_le ιΩ Oψ)
      have h3 : Nat.card Oψ ∣ Nat.card ((oddCoreIn (h.secJ0 y)).subgroupOf Z) :=
        card_map_dvd _ _
      have h4 : Nat.card ((oddCoreIn (h.secJ0 y)).subgroupOf Z) =
          Nat.card (oddCoreIn (h.secJ0 y)) :=
        Nat.card_congr (subgroupOfEquivOfLe (hOJ0.trans hJ0Z)).toEquiv
      have h5 : Nat.Coprime 2 (Nat.card (oddCoreIn (h.secJ0 y))) := by
        rw [oddCoreIn, card_map_of_injective (h.secJ0 y).subtype_injective]
        exact pPrimeCore_coprime_card
      rw [h4] at h3
      exact h5.coprime_dvd_right (h1.trans h3)
    have hΩ5 : 5 ≤ Nat.card Ω := hdeg
    have : IsSimpleGroup (alternatingGroup Ω) := alternatingGroup.isSimpleGroup hΩ5
    have hO'bot : O' = ⊥ := by
      rcases Subgroup.Normal.eq_bot_or_eq_top O' with h1 | h1
      · exact h1
      · exfalso
        have : Nontrivial Ω := Finite.one_lt_card_iff_nontrivial.mp (by omega)
        rw [h1, Subgroup.card_top, nat_card_alternatingGroup] at hO'odd
        have h2 : 2 ∣ (Nat.card Ω).factorial / 2 := by
          obtain ⟨c, hc⟩ : 4 ∣ (Nat.card Ω).factorial := Nat.dvd_factorial (by norm_num) (by omega)
          rw [hc, show 4 * c / 2 = 2 * c by omega]
          exact dvd_mul_right 2 c
        exact absurd (Nat.Coprime.coprime_dvd_right h2 hO'odd) (by decide)
    intro o ho hoZ
    have h1 : ψ ⟨o, hoZ⟩ ∈ Oψ := ⟨⟨o, hoZ⟩, mem_subgroupOf.mpr ho, rfl⟩
    obtain ⟨f, hf⟩ := hOrange h1
    have h2 : f ∈ O' := mem_comap.mpr (hf ▸ h1)
    rw [hO'bot, mem_bot] at h2
    rw [← hf, h2, map_one]
  have hJ0J : h.secJ0 y ≤ h.J := (GSLit.fixedLayer_le_inf h.J (h.secB0 y)).trans inf_le_left
  have hEF : ∀ e ∈ E', ∀ x, σ x = x → e x = x := by
    rintro _ ⟨⟨b, hbR⟩, hbB, rfl⟩ x hx
    have hbB' : b ∈ h.B := mem_subgroupOf.mp hbB
    have heσ : ρR ⟨b, hbR⟩ * σ = σ * ρR ⟨b, hbR⟩ :=
      mem_centralizer_singleton_iff.mp (hG'σ ⟨⟨b, hbR⟩, rfl⟩)
    have hbJ : b ∈ normalizer (h.secJ0 y : Set X) := hSJ b (hBS hbB')
    have hbK : b ∈ coreActionKernel h.J := (mem_inf.mp (h.B_le hbB')).2
    have hcommJ : ∀ j ∈ h.secJ0 y, ∀ hjZ : j ∈ Z,
        ρR ⟨b, hbR⟩ * ψ ⟨j, hjZ⟩ = ψ ⟨j, hjZ⟩ * ρR ⟨b, hbR⟩ := by
      intro j hj hjZ
      have hjJ : j ∈ h.J := hJ0J hj
      have hbjb : b * j * b⁻¹ ∈ h.secJ0 y := (mem_normalizer_iff.mp hbJ j).mp hj
      have hw1 : j⁻¹ * b⁻¹⁻¹ * j * b⁻¹ ∈ oddCoreIn h.J :=
        (mem_coreActionKernel.mp (inv_mem hbK)).2 j hjJ
      have hw2 : b * j * b⁻¹ * j⁻¹ ∈ oddCoreIn h.J := by
        have h1 : b * j * b⁻¹ * j⁻¹ = j * (j⁻¹ * b⁻¹⁻¹ * j * b⁻¹) * j⁻¹ := by group
        rw [h1]
        exact (mem_normalizer_iff.mp (le_normalizer_oddCoreIn_self _ hjJ) _).mp hw1
      have hw3 : b * j * b⁻¹ * j⁻¹ ∈ h.secJ0 y :=
        (h.secJ0 y).mul_mem hbjb ((h.secJ0 y).inv_mem hj)
      have hw : b * j * b⁻¹ * j⁻¹ ∈ oddCoreIn (h.secJ0 y) :=
        inf_oddCoreIn_le hJ0J (mem_inf.mpr ⟨hw3, hw2⟩)
      have hwZ : b * j * b⁻¹ * j⁻¹ ∈ Z := hJ0Z hw3
      have h4 := hOJ _ hw hwZ
      have h5 : ψ ⟨b * j * b⁻¹ * j⁻¹, hwZ⟩ =
          ρR ⟨b, hbR⟩ * ψ ⟨j, hjZ⟩ * (ρR ⟨b, hbR⟩)⁻¹ * (ψ ⟨j, hjZ⟩)⁻¹ := by
        show ρ ⟨_, hZN hwZ⟩ = ρ ⟨b, hRN hbR⟩ * ρ ⟨j, hZN hjZ⟩ * (ρ ⟨b, hRN hbR⟩)⁻¹ *
          (ρ ⟨j, hZN hjZ⟩)⁻¹
        rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
        rfl
      rw [h5] at h4
      calc ρR ⟨b, hbR⟩ * ψ ⟨j, hjZ⟩ = ρR ⟨b, hbR⟩ * ψ ⟨j, hjZ⟩ * (ρR ⟨b, hbR⟩)⁻¹ *
            (ψ ⟨j, hjZ⟩)⁻¹ * ψ ⟨j, hjZ⟩ * ρR ⟨b, hbR⟩ := by group
        _ = ψ ⟨j, hjZ⟩ * ρR ⟨b, hbR⟩ := by rw [h4, one_mul]
    have hfixΩ : ∀ z : Fin n, σ z = z → z ∈ Ω := by
      intro z hz
      rw [hΩdef, MulAction.mem_fixedPoints]
      rintro ⟨w, hw⟩
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hw
      exact Perm.zpow_apply_eq_self_of_apply_eq_self hz k
    have hΩfix : ∀ z ∈ Ω, σ z = z := fun z hz => hz ⟨σ, mem_zpowers σ⟩
    refine NFAlt.fixes_of_commute (Q := zpowers σ) (le_trans (by norm_num) hdeg) ?_ ?_ x
      (hfixΩ x hx)
    · intro z hz
      apply hfixΩ
      have h1 := congrArg (fun π : Perm (Fin n) => π z) heσ
      simp only [Perm.mul_apply, hΩfix z hz] at h1
      exact h1.symm
    · intro f hf
      obtain ⟨j, hj, hjZ, hjf⟩ := (hcharJ _).mpr ⟨f, hf, rfl⟩
      rw [← hjf]
      exact hcommJ j hj hjZ
  have hF2 : ∃ x₁ x₂ : Fin n, x₁ ≠ x₂ ∧ σ x₁ = x₁ ∧ σ x₂ = x₂ := by
    have : Nontrivial Ω := Finite.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩, hne⟩ := exists_pair_ne Ω
    exact ⟨x₁, x₂, fun h12 => hne (Subtype.ext h12), hx₁ ⟨σ, mem_zpowers σ⟩,
      hx₂ ⟨σ, mem_zpowers σ⟩⟩
  have hGH := NFAlt.eq_of_maximal_alternating hG'2 hH'G hVH hG'σ (hVC.trans inf_le_right)
    hVmax hEF hF2 hN
  have hgR : g ∈ R := mem_sup_right (mem_zpowers g)
  have hgH : ρR ⟨g, hgR⟩ ∈ H' := hGH ▸ ⟨⟨g, hgR⟩, rfl⟩
  obtain ⟨s, hs, hsg⟩ := hgH
  have h1 : ρR (s⁻¹ * ⟨g, hgR⟩) = 1 := by rw [map_mul, map_inv, hsg, inv_mul_cancel]
  have h2 : ((s⁻¹ * ⟨g, hgR⟩ : ↥R) : X) ∈ coreActionKernel M :=
    hρ1 _ (hRN (s⁻¹ * ⟨g, hgR⟩).2) h1
  have h3 := hU (mem_inf.mpr ⟨(s⁻¹ * ⟨g, hgR⟩).2, h2⟩)
  have h4 : g = (s : X) * ((s⁻¹ * ⟨g, hgR⟩ : ↥R) : X) := by simp
  have hgS0' : g ∈ S₀ := by
    rw [h4]
    exact S₀.mul_mem (mem_subgroupOf.mp hs) (hBS (h.secB0_le_B y h3))
  exact h.comm_a (mem_inf.mp hgS0').1

end Hyp52

end CFSG.ComponentClassification.GSThmB
