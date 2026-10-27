module

public import CFSG.LocalAnalysis.EvenBN.Common.SL2Module

public section

namespace CFSG.LocalAnalysis.EvenBN.Common

open Subgroup Matrix
open scoped MatrixGroups

section General

variable {G H : Type*} [Group G] [Group H]

theorem fst_eq_one_of_comap_inl_eq_bot (hG : center G = ⊥) {N : Subgroup (G × H)}
    (hN : N.Normal) (h : N.comap (MonoidHom.inl G H) = ⊥) {n : G × H} (hn : n ∈ N) :
    n.1 = 1 := by
  have hc : n.1 ∈ center G := by
    rw [mem_center_iff]
    intro g
    have hc : ((g, 1) * n * (g, 1)⁻¹ * n⁻¹ : G × H) ∈ N :=
      mul_mem (hN.conj_mem n hn (g, 1)) (inv_mem hn)
    have hmem : g * n.1 * g⁻¹ * n.1⁻¹ ∈ N.comap (MonoidHom.inl G H) := by
      show ((g * n.1 * g⁻¹ * n.1⁻¹, 1) : G × H) ∈ N
      convert hc using 1
      ext <;> simp
    rw [h, mem_bot] at hmem
    exact mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 hmem)
  rw [hG, mem_bot] at hc
  exact hc

theorem snd_eq_one_of_comap_inr_eq_bot (hH : center H = ⊥) {N : Subgroup (G × H)}
    (hN : N.Normal) (h : N.comap (MonoidHom.inr G H) = ⊥) {n : G × H} (hn : n ∈ N) :
    n.2 = 1 := by
  have hc : n.2 ∈ center H := by
    rw [mem_center_iff]
    intro g
    have hc : ((1, g) * n * (1, g)⁻¹ * n⁻¹ : G × H) ∈ N :=
      mul_mem (hN.conj_mem n hn (1, g)) (inv_mem hn)
    have hmem : g * n.2 * g⁻¹ * n.2⁻¹ ∈ N.comap (MonoidHom.inr G H) := by
      show (((1 : G), g * n.2 * g⁻¹ * n.2⁻¹) : G × H) ∈ N
      convert hc using 1
      ext <;> simp
    rw [h, mem_bot] at hmem
    exact mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 hmem)
  rw [hH, mem_bot] at hc
  exact hc

theorem normal_prod_eq_of_isSimpleGroup [IsSimpleGroup G] [IsSimpleGroup H] (hG : center G = ⊥)
    (hH : center H = ⊥) {N : Subgroup (G × H)} (hN : N.Normal) :
    N = ⊥ ∨ N = (⊤ : Subgroup G).prod ⊥ ∨ N = (⊥ : Subgroup G).prod ⊤ ∨ N = ⊤ := by
  have : (N.comap (MonoidHom.inl G H)).Normal := hN.comap _
  have : (N.comap (MonoidHom.inr G H)).Normal := hN.comap _
  have hinl : ∀ a : G, N.comap (MonoidHom.inl G H) = ⊤ → ((a, 1) : G × H) ∈ N :=
    fun a h => show a ∈ N.comap (MonoidHom.inl G H) by rw [h]; exact mem_top a
  have hinr : ∀ b : H, N.comap (MonoidHom.inr G H) = ⊤ → (((1 : G), b) : G × H) ∈ N :=
    fun b h => show b ∈ N.comap (MonoidHom.inr G H) by rw [h]; exact mem_top b
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.comap (MonoidHom.inl G H)) with h1 | h1 <;>
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.comap (MonoidHom.inr G H)) with h2 | h2
  · left
    refine eq_bot_iff.2 fun n hn => ?_
    rw [mem_bot]
    exact Prod.ext (fst_eq_one_of_comap_inl_eq_bot hG hN h1 hn)
      (snd_eq_one_of_comap_inr_eq_bot hH hN h2 hn)
  · right; right; left
    ext ⟨a, b⟩
    rw [mem_prod, mem_bot]
    refine ⟨fun hn => ⟨fst_eq_one_of_comap_inl_eq_bot hG hN h1 hn, mem_top _⟩, ?_⟩
    rintro ⟨rfl, -⟩
    exact hinr b h2
  · right; left
    ext ⟨a, b⟩
    rw [mem_prod, mem_bot]
    refine ⟨fun hn => ⟨mem_top _, snd_eq_one_of_comap_inr_eq_bot hH hN h2 hn⟩, ?_⟩
    rintro ⟨-, rfl⟩
    exact hinl a h1
  · right; right; right
    refine eq_top_iff.2 fun n _ => ?_
    have := mul_mem (hinl n.1 h1) (hinr n.2 h2)
    simpa using this

end General

variable {k : Type*} [Field k] [CharP k 2]

theorem center_sl2_eq_bot_of_charTwo : center (SL(2, k)) = ⊥ := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  refine eq_bot_iff.2 fun A hA => ?_
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
  rw [Fintype.card_fin] at hr
  have h5 : (r - 1) ^ 2 = 0 := by linear_combination hr + (1 - r) * h2
  have hr1 : r = 1 := sub_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h5)
  subst hr1
  rw [mem_bot]
  ext i j
  simpa [scalar_apply, one_apply] using (congrFun (congrFun hrA i) j).symm

theorem normal_sl2_prod_eq (h4 : 4 ≤ Nat.card k) {N : Subgroup (SL(2, k) × SL(2, k))}
    (hN : N.Normal) :
    N = ⊥ ∨ N = (⊤ : Subgroup SL(2, k)).prod ⊥ ∨ N = (⊥ : Subgroup SL(2, k)).prod ⊤ ∨ N = ⊤ := by
  have := sl2_isSimpleGroup_of_charTwo h4
  exact normal_prod_eq_of_isSimpleGroup center_sl2_eq_bot_of_charTwo
    center_sl2_eq_bot_of_charTwo hN

theorem normal_eq_of_mulEquiv_sl2_prod (h4 : 4 ≤ Nat.card k) {X : Type*} [Group X]
    (ψ : X ≃* SL(2, k) × SL(2, k)) {N : Subgroup X} (hN : N.Normal) :
    N = ⊥ ∨ N = ((⊤ : Subgroup SL(2, k)).prod ⊥).comap ψ.toMonoidHom ∨
      N = ((⊥ : Subgroup SL(2, k)).prod ⊤).comap ψ.toMonoidHom ∨ N = ⊤ := by
  have hN' : (N.map ψ.toMonoidHom).Normal := hN.map _ ψ.surjective
  have hNe : N = (N.map ψ.toMonoidHom).comap ψ.toMonoidHom :=
    (comap_map_eq_self_of_injective ψ.injective N).symm
  rcases normal_sl2_prod_eq h4 hN' with h | h | h | h
  · exact Or.inl ((map_eq_bot_iff_of_injective _ ψ.injective).1 h)
  · exact Or.inr (Or.inl (hNe.trans (by rw [h])))
  · exact Or.inr (Or.inr (Or.inl (hNe.trans (by rw [h]))))
  · exact Or.inr (Or.inr (Or.inr (hNe.trans (by rw [h, comap_top]))))

end CFSG.LocalAnalysis.EvenBN.Common
