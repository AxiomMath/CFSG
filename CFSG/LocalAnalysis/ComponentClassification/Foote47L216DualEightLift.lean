module

public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.ComponentClassification.Foote47L216

open Subgroup CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

private lemma d8lift_inf_eq_bot_of_isPGroup {P N : Subgroup G} (hP : IsPGroup 2 P)
    (hN : Odd (Nat.card N)) : P ⊓ N = ⊥ := by
  have h1 : IsPGroup 2 ↥(P ⊓ N) := hP.to_le inf_le_left
  obtain ⟨k, hk⟩ := h1.exists_card_eq
  have h3 : Odd (Nat.card ↥(P ⊓ N)) := hN.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right)
  rw [hk] at h3
  have hk0 : k = 0 := by
    by_contra hk0
    exact (Nat.not_even_iff_odd.mpr h3) (even_iff_two_dvd.mpr (dvd_pow_self 2 hk0))
  exact Subgroup.eq_bot_of_card_eq _ (by rw [hk, hk0, pow_zero])

omit [Finite G] in
private lemma d8lift_exists_isSylowOf_ge {A K : Subgroup G} (hA : IsPGroup 2 A) (hAK : A ≤ K) :
    ∃ S : Subgroup G, IsSylowOf 2 S K ∧ A ≤ S := by
  have hA' : IsPGroup 2 (A.subgroupOf K) := hA.comap_subtype
  obtain ⟨Q, hQ⟩ := hA'.exists_le_sylow
  refine ⟨(Q : Subgroup K).map K.subtype, ⟨Q, rfl⟩, fun x hx => ?_⟩
  have hx' : (⟨x, hAK hx⟩ : ↥K) ∈ A.subgroupOf K := hx
  exact ⟨⟨x, hAK hx⟩, hQ hx', rfl⟩

private lemma d8lift_exists_invariant_sylow {X T : Subgroup G} (hT : IsPGroup 2 T)
    (hTX : T ≤ Subgroup.normalizer (X : Set G)) :
    ∃ Q : Subgroup G, IsSylowOf 2 Q X ∧ T ≤ Subgroup.normalizer (Q : Set G) := by
  have hXT : X ⊔ T ≤ Subgroup.normalizer (X : Set G) :=
    sup_le Subgroup.le_normalizer hTX
  obtain ⟨S, hS, hTS⟩ := d8lift_exists_isSylowOf_ge hT (le_sup_right : T ≤ X ⊔ T)
  refine ⟨S ⊓ X, hS.inf_of_le_normalizer le_sup_left hXT, fun s hs => ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have hsS : s ∈ S := hTS hs
  have h1 := (Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer (H := S) hsS)) x
  have h2 := (Subgroup.mem_normalizer_iff.1 (hTX hs)) x
  simp only [Subgroup.mem_inf]
  rw [h1, h2]

theorem exists_isSylowOf_le_centralizer_l216 {O H W : Subgroup G} (hOodd : Odd (Nat.card O))
    (hWH : W ≤ normalizer (H : Set G)) (hWp : IsPGroup 2 W)
    (hWOH : ∀ w ∈ W, ∀ h ∈ H, w * h * w⁻¹ * h⁻¹ ∈ O) :
    ∃ V : Subgroup G, IsSylowOf 2 V H ∧ V ≤ centralizer (W : Set G) := by
  obtain ⟨V, hVsyl, hWV⟩ := d8lift_exists_invariant_sylow hWp hWH
  refine ⟨V, hVsyl, fun v hv => ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have hvH : v ∈ H := hVsyl.le hv
  have hwv : w * v * w⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.1 (hWV hw) v).1 hv
  have hcV : w * v * w⁻¹ * v⁻¹ ∈ V := V.mul_mem hwv (V.inv_mem hv)
  have hcO : w * v * w⁻¹ * v⁻¹ ∈ O := hWOH w hw v hvH
  have hbot : V ⊓ O = ⊥ := d8lift_inf_eq_bot_of_isPGroup hVsyl.isPGroup hOodd
  have hc1 : w * v * w⁻¹ * v⁻¹ = 1 := by
    have hmem : w * v * w⁻¹ * v⁻¹ ∈ V ⊓ O := ⟨hcV, hcO⟩
    rw [hbot] at hmem
    exact Subgroup.mem_bot.1 hmem
  calc w * v = w * v * w⁻¹ * v⁻¹ * (v * w) := by group
    _ = v * w := by rw [hc1, one_mul]

end CFSG.ComponentClassification.Foote47L216
