module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.LayerCoord

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open Subgroup

variable {B : Type} [Group B] [Finite B]

private theorem card_mul_le_card_of_inf_eq_bot {A A' Rb : Subgroup B} (hA : A ≤ Rb)
    (hA' : A' ≤ Rb) (hdis : A ⊓ A' = ⊥) :
    Nat.card ↥A * Nat.card ↥A' ≤ Nat.card ↥Rb := by
  have hdisj : Disjoint A A' := disjoint_iff.mpr hdis
  have hinj : Function.Injective
      (fun p : ↥A × ↥A' =>
        (⟨(p.1 : B) * (p.2 : B), Rb.mul_mem (hA p.1.2) (hA' p.2.2)⟩ : ↥Rb)) := by
    intro p q hpq
    have hpq' : (p.1 : B) * (p.2 : B) = (q.1 : B) * (q.2 : B) :=
      congrArg Subtype.val hpq
    exact Subgroup.mul_injective_of_disjoint hdisj hpq'
  have h := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_prod] at h

theorem exists_unique_component (hodd : CFSG.pPrimeCore 2 B = ⊥) (h2 : CFSG.pCore 2 B = ⊥)
    {Rb Yb : Subgroup B} (hRsq : ∀ x ∈ Rb, x ^ 2 = 1) (hRcomm : ∀ a ∈ Rb, ∀ b ∈ Rb, a * b = b * a)
    (hRne : Rb ≠ ⊥) (hRc : centralizer (Rb : Set B) ≤ Rb) (hRcard : Nat.card ↥Rb ≤ 2 ^ 12)
    (hirr : ∀ U : Subgroup B, U ≤ Rb → (∀ x ∈ normalizer (Rb : Set B), ∀ u ∈ U, x * u * x⁻¹ ∈ U) →
      U = ⊥ ∨ U = Rb)
    (hYn : ∀ y ∈ Yb, ∀ r ∈ Rb, y * r * y⁻¹ ∈ Rb)
    (hYcomp : ∀ K : Subgroup B, CFSG.IsComponent K → ∀ y ∈ Yb, ∀ k ∈ K, y * k * y⁻¹ ∈ K)
    (hlat1 : ∀ M : Subgroup B, M ≤ Rb → (∀ y ∈ Yb, ∀ m ∈ M, y * m * y⁻¹ ∈ M) →
      Nat.card ↥M ≤ 2 ^ 7 → ∀ y ∈ Yb, ∀ m ∈ M, y * m = m * y)
    (hlat2 : ∃ y ∈ Yb, ∃ r ∈ Rb, y * r ≠ r * y) :
    ∃ K : Subgroup B, CFSG.IsComponent K ∧ CFSG.layer B = K ∧ Rb ≤ K := by
  have hR2 : IsPGroup 2 ↥Rb := by
    rw [isPGroup_iff_orderOf_dvd_pow]
    intro x
    refine ⟨1, ?_⟩
    have hx2 : x ^ 2 = 1 := by
      apply Subtype.ext
      simpa using hRsq (x : B) x.2
    have hdvd : orderOf x ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hx2
    simpa using hdvd
  have hRle : Rb ≤ CFSG.layer B :=
    le_layer_of_selfCentralizing hodd h2 hR2 hRne hRc hirr
  have hR : SelfCentAbelian Rb := ⟨hRcomm, hRc, hRle⟩
  have hVY : ∀ K : Subgroup B, CFSG.IsComponent K →
      ∀ y ∈ Yb, ∀ m ∈ Rb ⊓ K, y * m * y⁻¹ ∈ Rb ⊓ K := by
    intro K hK y hy m hm
    rw [Subgroup.mem_inf] at hm ⊢
    exact ⟨hYn y hy m hm.1, hYcomp K hK y hy m hm.2⟩
  have hbig : ∃ K : Subgroup B, CFSG.IsComponent K ∧ 2 ^ 7 < Nat.card ↥(Rb ⊓ K) := by
    by_contra hcon
    push Not at hcon
    have hcent : Rb ≤ centralizer (Yb : Set B) := by
      refine (Rb_le_iSup_inf_component hodd h2 hR).trans ?_
      refine iSup_le fun K => ?_
      intro m hm
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact hlat1 (Rb ⊓ K.1) inf_le_left (hVY K.1 K.2) (hcon K.1 K.2) y hy m hm
    obtain ⟨y, hy, r, hr, hyr⟩ := hlat2
    have hcomm := hcent hr
    rw [Subgroup.mem_centralizer_iff] at hcomm
    exact hyr (hcomm y hy)
  obtain ⟨K₀, hK₀, hK₀big⟩ := hbig
  have hVne : Rb ⊓ K₀ ≠ ⊥ := Rb_inf_component_ne_bot hodd h2 hR hK₀
  have hdisInt : ∀ K₁ : Subgroup B, CFSG.IsComponent K₁ → K₁ ≠ K₀ →
      (Rb ⊓ K₀) ⊓ (Rb ⊓ K₁) = ⊥ := by
    intro K₁ hK₁ hne
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hx0, hx1⟩ := hx
    rw [Subgroup.mem_inf] at hx0 hx1
    obtain ⟨-, hxK0⟩ := hx0
    obtain ⟨-, hxK1⟩ := hx1
    have hle : K₁ ≤ centralizer (K₀ : Set B) := by
      rcases CFSG.LocalCores.distinct_components_commute hK₁ hK₀ with h | h
      · exact absurd h hne
      · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
    have hxcent : x ∈ centralizer (K₀ : Set B) := hle hxK1
    have hxcenter : (⟨x, hxK0⟩ : ↥K₀) ∈ center ↥K₀ := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp hxcent g g.2
    have hxone : (⟨x, hxK0⟩ : ↥K₀) = 1 := by
      have h := hxcenter
      rw [center_component_eq_bot hodd h2 hK₀] at h
      simpa using h
    simpa using congrArg Subtype.val hxone
  have hcardV : ∀ K₁ : Subgroup B, CFSG.IsComponent K₁ → K₁ ≠ K₀ →
      Nat.card ↥(Rb ⊓ K₀) * Nat.card ↥(Rb ⊓ K₁) ≤ 2 ^ 12 := by
    intro K₁ hK₁ hne
    exact (card_mul_le_card_of_inf_eq_bot inf_le_left inf_le_left
      (hdisInt K₁ hK₁ hne)).trans hRcard
  have hfix : ∀ x ∈ normalizer (Rb : Set B),
      K₀.map (MulAut.conj x).toMonoidHom = K₀ := by
    intro x hx
    by_contra hne
    have hK' : CFSG.IsComponent (K₀.map (MulAut.conj x).toMonoidHom) :=
      CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj x) hK₀
    have hmapRb : Rb.map (MulAut.conj x).toMonoidHom = Rb :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hx
    have hcard : Nat.card ↥(Rb ⊓ K₀.map (MulAut.conj x).toMonoidHom)
        = Nat.card ↥(Rb ⊓ K₀) := by
      have h1 : Rb ⊓ K₀.map (MulAut.conj x).toMonoidHom
          = (Rb ⊓ K₀).map (MulAut.conj x).toMonoidHom := by
        rw [Subgroup.map_inf Rb K₀ (MulAut.conj x).toMonoidHom
          (MulAut.conj x).injective, hmapRb]
      rw [h1, Subgroup.card_map_of_injective (MulAut.conj x).injective]
    have hK'big : 2 ^ 7 < Nat.card ↥(Rb ⊓ K₀.map (MulAut.conj x).toMonoidHom) := by
      rw [hcard]; exact hK₀big
    have hprod := hcardV (K₀.map (MulAut.conj x).toMonoidHom) hK' hne
    have hgt : 2 ^ 12 < Nat.card ↥(Rb ⊓ K₀)
        * Nat.card ↥(Rb ⊓ K₀.map (MulAut.conj x).toMonoidHom) := by
      have ha : 2 ^ 7 + 1 ≤ Nat.card ↥(Rb ⊓ K₀) := Nat.succ_le_of_lt hK₀big
      have hb : 2 ^ 7 + 1 ≤ Nat.card ↥(Rb ⊓ K₀.map (MulAut.conj x).toMonoidHom) :=
        Nat.succ_le_of_lt hK'big
      calc 2 ^ 12 < (2 ^ 7 + 1) * (2 ^ 7 + 1) := by norm_num
        _ ≤ Nat.card ↥(Rb ⊓ K₀)
            * Nat.card ↥(Rb ⊓ K₀.map (MulAut.conj x).toMonoidHom) := Nat.mul_le_mul ha hb
    exact (not_le_of_gt hgt) hprod
  have hK0norm : normalizer (Rb : Set B) ≤ normalizer (K₀ : Set B) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact hfix x hx
  have hK0cent : K₀ ⊓ centralizer (K₀ : Set B) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxK0, hxcent⟩ := hx
    have hxcenter : (⟨x, hxK0⟩ : ↥K₀) ∈ center ↥K₀ := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp hxcent g g.2
    have hxone : (⟨x, hxK0⟩ : ↥K₀) = 1 := by
      have h := hxcenter
      rw [center_component_eq_bot hodd h2 hK₀] at h
      simpa using h
    simpa using congrArg Subtype.val hxone
  set U : Subgroup B := Rb ⊓ centralizer (K₀ : Set B) with hUdef
  have hUinv : ∀ x ∈ normalizer (Rb : Set B), ∀ u ∈ U, x * u * x⁻¹ ∈ U := by
    intro x hx u hu
    rw [hUdef] at hu ⊢
    rw [Subgroup.mem_inf] at hu ⊢
    obtain ⟨huRb, huCent⟩ := hu
    refine ⟨?_, ?_⟩
    · have hx' := hx
      rw [Subgroup.mem_normalizer_iff] at hx'
      exact (hx' u).mp huRb
    · rw [Subgroup.mem_centralizer_iff]
      intro k hk
      rw [Subgroup.mem_centralizer_iff] at huCent
      have hkx : x⁻¹ * k * x ∈ K₀ := by
        have hxK0 := hK0norm hx
        rw [Subgroup.mem_normalizer_iff''] at hxK0
        exact (hxK0 k).mp hk
      have hcomm : u * (x⁻¹ * k * x) = (x⁻¹ * k * x) * u :=
        (huCent (x⁻¹ * k * x) hkx).symm
      calc k * (x * u * x⁻¹) = x * ((x⁻¹ * k * x) * u) * x⁻¹ := by group
        _ = x * (u * (x⁻¹ * k * x)) * x⁻¹ := by rw [← hcomm]
        _ = (x * u * x⁻¹) * k := by group
  have hUbot : U = ⊥ := by
    rcases hirr U (by rw [hUdef]; exact inf_le_left) hUinv with h | h
    · exact h
    · exfalso
      have hle : Rb ⊓ K₀ ≤ K₀ ⊓ centralizer (K₀ : Set B) := by
        intro m hm
        rw [Subgroup.mem_inf] at hm ⊢
        obtain ⟨hmRb, hmK⟩ := hm
        have hmU : m ∈ U := by rw [h]; exact hmRb
        rw [hUdef, Subgroup.mem_inf] at hmU
        exact ⟨hmK, hmU.2⟩
      have hbot : Rb ⊓ K₀ = ⊥ := by
        rw [← le_bot_iff]
        calc Rb ⊓ K₀ ≤ K₀ ⊓ centralizer (K₀ : Set B) := hle
          _ = ⊥ := hK0cent
      exact hVne hbot
  have huniq : ∀ K : Subgroup B, CFSG.IsComponent K → K = K₀ := by
    intro K hK
    by_contra hne
    have hle : K ≤ centralizer (K₀ : Set B) := by
      rcases CFSG.LocalCores.distinct_components_commute hK hK₀ with h | h
      · exact absurd h hne
      · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
    have hKU : Rb ⊓ K ≤ U := by
      intro m hm
      rw [Subgroup.mem_inf] at hm
      rw [hUdef, Subgroup.mem_inf]
      exact ⟨hm.1, hle hm.2⟩
    have hbot : Rb ⊓ K = ⊥ := by
      rw [← le_bot_iff]
      calc Rb ⊓ K ≤ U := hKU
        _ = ⊥ := hUbot
    exact (Rb_inf_component_ne_bot hodd h2 hR hK) hbot
  have hset : {K : Subgroup B | CFSG.IsComponent K} = {K₀} := by
    ext K
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · intro hK; exact huniq K hK
    · rintro rfl; exact hK₀
  have hlayer : CFSG.layer B = K₀ := by
    rw [CFSG.layer.eq_sSup B, hset, sSup_singleton]
  have hRle' : Rb ≤ K₀ := by
    rw [hlayer] at hRle
    exact hRle
  exact ⟨K₀, hK₀, hlayer, hRle'⟩

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
