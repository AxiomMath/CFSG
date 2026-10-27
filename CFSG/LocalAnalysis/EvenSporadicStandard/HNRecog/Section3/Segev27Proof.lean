module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Seg27.Theta
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Seg27.Pairs

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem segev27_holds : Segev27 := by
  intro H _ a b hH hZ φ K hK01 hKa hKb hK23 i j hij
  obtain ⟨ψ⟩ := hH
  haveI : Finite H := Finite.of_equiv _ ψ.symm.toEquiv
  obtain ⟨θ, hθ, hA, hker⟩ := seg27_exists_theta ψ φ
  have hc : Nat.card (Subgroup.center H) = 4 := seg27_card_center ψ
  have hsq : ∀ z ∈ Subgroup.center H, z * z = 1 := fun z hz => seg27_mul_self_of_mem_center ψ hz
  obtain ⟨ha1, hb1, hab⟩ := seg27_ne_of_center hZ hc
  have haZ : a ∈ Subgroup.center H := by
    have h : a ∈ (Subgroup.center H : Set H) := by rw [hZ]; simp
    exact h
  have hbZ : b ∈ Subgroup.center H := by
    have h : b ∈ (Subgroup.center H : Set H) := by rw [hZ]; simp
    exact h
  have h5 : ∀ (k : Fin 4) (c : H), c ≠ 1 → c * c = 1 → k.val < 2 →
      K k ⊓ Subgroup.center H = Subgroup.zpowers c → Seg27Five φ c (K k) := by
    intro k c hc1 hcc hk hKc
    obtain ⟨hs, -, hA5, hsix⟩ := hK01 k hk
    exact ⟨hs, hA5, hsix, hc1, hcc, hKc⟩
  have h50 : Seg27Five φ a (K 0) := h5 0 a ha1 (hsq a haZ) (by decide) hKa
  have h51 : Seg27Five φ b (K 1) := h5 1 b hb1 (hsq b hbZ) (by decide) hKb
  have h2 := hK23 2 (by decide)
  have h3 := hK23 3 (by decide)
  have e01 := seg27_pair_five_five φ hθ hA hker hZ hsq hab h50 h51
  have e02 := seg27_pair_five_six φ hθ hA hker h50 h2
  have e03 := seg27_pair_five_six φ hθ hA hker h50 h3
  have e12 := seg27_pair_five_six φ hθ hA hker h51 h2
  have e13 := seg27_pair_five_six φ hθ hA hker h51 h3
  have e23 := seg27_pair_six_six φ hθ hA h2 h3
  have sym : ∀ i j : Fin 4, (∃ t ∈ K i ⊓ K j, orderOf t = 2) →
      ∃ t ∈ K j ⊓ K i, orderOf t = 2 := by
    rintro i j ⟨t, ht, h⟩
    exact ⟨t, by rwa [inf_comm], h⟩
  fin_cases i <;> fin_cases j <;>
    first
    | exact absurd rfl hij
    | exact e01 | exact e02 | exact e03 | exact e12 | exact e13 | exact e23
    | exact sym _ _ e01 | exact sym _ _ e02 | exact sym _ _ e03 | exact sym _ _ e12
    | exact sym _ _ e13 | exact sym _ _ e23

end CFSG.EvenSporadicStandard.HNRecog.Section3
