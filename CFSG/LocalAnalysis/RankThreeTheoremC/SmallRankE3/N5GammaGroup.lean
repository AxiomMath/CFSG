module

public import CFSG.GH74.Uniqueness.SU.SU1Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

theorem n5_two_le_pRank_of_inner {A : Type} [Group A] [Finite A] {K B : Subgroup A} {p : ℕ}
    (hp : p.Prime) (hB : CFSG.Open.IsElemAbelian p B) (hBc : Nat.card B = p ^ 2)
    (hZ : ∀ k ∈ K, (∀ l ∈ K, k * l = l * k) → k = 1)
    (hfaith : ∀ b ∈ B, b ≠ 1 → ¬ ∀ k ∈ K, b * k = k * b)
    (hinner : ∀ b ∈ B, ∃ k ∈ K, ∀ l ∈ K, b * l * b⁻¹ = k * l * k⁻¹) :
    2 ≤ CFSG.Open.pRank p K := by
  have uniq : ∀ u ∈ K, ∀ v ∈ K, (∀ l ∈ K, u * l * u⁻¹ = v * l * v⁻¹) → u = v := by
    intro u hu v hv h
    have hc : v⁻¹ * u ∈ K := K.mul_mem (K.inv_mem hv) hu
    have hcomm : ∀ l ∈ K, v⁻¹ * u * l = l * (v⁻¹ * u) := by
      intro l hl
      have hconj : v⁻¹ * u * l * (v⁻¹ * u)⁻¹ = l := by
        calc v⁻¹ * u * l * (v⁻¹ * u)⁻¹ = v⁻¹ * (u * l * u⁻¹) * v := by group
          _ = v⁻¹ * (v * l * v⁻¹) * v := by rw [h l hl]
          _ = l := by group
      exact mul_inv_eq_iff_eq_mul.mp hconj
    exact (inv_mul_eq_one.mp (hZ _ hc hcomm)).symm
  choose f hfK hf using hinner
  have hmul : ∀ a b : A, ∀ ha : a ∈ B, ∀ hb : b ∈ B, ∀ hab : a * b ∈ B,
      f (a * b) hab = f a ha * f b hb := by
    intro a b ha hb hab
    refine uniq (f (a * b) hab) (hfK _ _) (f a ha * f b hb)
      (K.mul_mem (hfK a ha) (hfK b hb)) ?_
    intro l hl
    have hm : f b hb * l * (f b hb)⁻¹ ∈ K :=
      K.mul_mem (K.mul_mem (hfK b hb) hl) (K.inv_mem (hfK b hb))
    calc f (a * b) hab * l * (f (a * b) hab)⁻¹ = a * b * l * (a * b)⁻¹ :=
          (hf (a * b) hab l hl).symm
      _ = a * (b * l * b⁻¹) * a⁻¹ := by group
      _ = a * (f b hb * l * (f b hb)⁻¹) * a⁻¹ := by rw [hf b hb l hl]
      _ = f a ha * (f b hb * l * (f b hb)⁻¹) * (f a ha)⁻¹ := hf a ha _ hm
      _ = f a ha * f b hb * l * (f a ha * f b hb)⁻¹ := by group
  obtain ⟨ψ, hψ⟩ : ∃ ψ : B →* A, ∀ x : B, ψ x = f x.1 x.2 :=
    ⟨MonoidHom.mk' (fun x : B => f x.1 x.2)
      (fun x y => hmul x.1 y.1 x.2 y.2 (B.mul_mem x.2 y.2)), fun x => rfl⟩
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    by_contra hne
    have hx1 : (x : A) ≠ 1 := fun h => hne (Subtype.ext h)
    have h2 : f x.1 x.2 = 1 := (hψ x).symm.trans hx
    exact hfaith x.1 x.2 hx1 (fun l hl => by
      have h1 := hf x.1 x.2 l hl
      rw [h2] at h1
      simp only [one_mul, inv_one, mul_one] at h1
      exact mul_inv_eq_iff_eq_mul.mp h1)
  have hEK : ψ.range ≤ K := by
    intro y hy
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hy
    rw [hψ x]
    exact hfK x.1 x.2
  have hcard : Nat.card ψ.range = p ^ 2 := by
    rw [← hBc]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hBcomm := (CFSG.GH74.Uniqueness.SU.SU1.isElemAbelian_iff.mp hB).1
  have hBexp := (CFSG.GH74.Uniqueness.SU.SU1.isElemAbelian_iff.mp hB).2
  have hE : CFSG.Open.IsElemAbelian p ψ.range := by
    refine CFSG.GH74.Uniqueness.SU.SU1.isElemAbelian_iff.mpr ⟨?_, ?_⟩
    · intro a ha b hb
      obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp ha
      obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hb
      have hxy : x * y = y * x := Subtype.ext (hBcomm x.1 x.2 y.1 y.2)
      rw [← map_mul, ← map_mul, hxy]
    · intro a ha
      obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp ha
      have hxp : x ^ p = 1 := Subtype.ext (hBexp x.1 x.2)
      rw [← map_pow, hxp, map_one]
  exact CFSG.GH74.Uniqueness.SU.SU1.le_pRank hp.one_lt hEK hE hcard

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
