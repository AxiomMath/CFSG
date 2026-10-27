module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitGoldschmidt
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma412Inner
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitWGroup

public section

namespace CFSG.ComponentClassification.GrSLit.KSw

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS

variable {G : Type} [Group G] [Finite G]

theorem exists_isExtremalIn_conj {T : Subgroup G} (hT2 : IsPGroup 2 T) (hTidx : ¬ 2 ∣ T.index)
    {b : G} (hb : ∃ n : ℕ, orderOf b = 2 ^ n) : ∃ c : G, IsExtremalIn T (c⁻¹ * b * c) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨D, hDC, hD2, hDidx, hbD⟩ := GH74.GLS.Bg.Thompson.exists_sylow_centralizer (p := 2) hb
  obtain ⟨c, -, hc⟩ := GH74.GLS.Bg.Thompson.exists_conj_into_sylow (N := ⊤) (S₀ := T) le_top hD2
    le_top hT2 (by rwa [relIndex_top_right])
  have hyT : c⁻¹ * b * c ∈ T := hc b hbD
  refine ⟨c, isExtremalIn_of_thompson hyT ⟨inf_le_right, hT2.to_le inf_le_left, ?_⟩⟩
  set f : G →* G := (MulAut.conj c⁻¹).toMonoidHom with hf
  have hfinj : Function.Injective f := (MulAut.conj c⁻¹).injective
  have hCy : centralizer ({c⁻¹ * b * c} : Set G) = (centralizer ({b} : Set G)).map f :=
    GH74.GLS.Bg.Thompson.centralizer_conj_eq b c
  have hD'le : D.map f ≤ T ⊓ centralizer ({c⁻¹ * b * c} : Set G) := by
    rintro z ⟨d, hd, rfl⟩
    refine ⟨?_, ?_⟩
    · simpa [hf, MulAut.conj_apply] using hc d hd
    · rw [hCy]
      exact ⟨d, hDC hd, rfl⟩
  have h1 := relIndex_mul_relIndex (D.map f) (T ⊓ centralizer ({c⁻¹ * b * c} : Set G))
    (centralizer ({c⁻¹ * b * c} : Set G)) hD'le inf_le_right
  have h2 : (D.map f).relIndex (centralizer ({c⁻¹ * b * c} : Set G)) =
      D.relIndex (centralizer ({b} : Set G)) := by
    rw [hCy]
    exact relIndex_map_map_of_injective D _ hfinj
  intro hdvd
  apply hDidx
  rw [← h2, ← h1]
  exact Dvd.dvd.mul_left hdvd _

omit [Finite G] in
theorem isExtremalIn_of_isSylowTwoIn {S T : Subgroup G} {b : G}
    (hS : IsSylowTwoIn S (centralizer ({b} : Set G))) (hST : S ≤ T) (hT2 : IsPGroup 2 T)
    (hbT : b ∈ T) : IsExtremalIn T b := by
  have heq := hS.eq_of_le (le_inf hST hS.1) inf_le_right (hT2.to_le inf_le_left)
  refine ⟨hbT, ?_⟩
  rw [heq]
  exact hS.2

omit [Finite G] in
theorem mem_withKernel_conjugate_iff {K : Subgroup G} {g y : G} :
    y ∈ withKernel (conjugate K g) ↔ g * y * g⁻¹ ∈ withKernel K := by
  have hC : coreActionKernel (conjugate K g) = conjugate (coreActionKernel K) g := by
    ext x
    rw [mem_conjugate_iff, FooteLit.mem_coreActionKernel_conjugate_iff]
  have h : withKernel (conjugate K g) = conjugate (withKernel K) g := by
    rw [withKernel, withKernel, hC]
    exact (Subgroup.map_sup _ _ _).symm
  rw [h, mem_conjugate_iff]

omit [Finite G] in
theorem conj_sq_not_mem_withKernel {W K T : Subgroup G} {t : G} (htT : t ∈ T)
    (hr2 : ∀ m ∈ normalizer (W : Set G), conjugate K m = K ∨ conjugate K m = conjugate K t)
    (hE5 : ∀ v ∈ T, v ∉ normalizer (K : Set G) → v * v ∉ withKernel K) {v : G} (hvT : v ∈ T)
    (hvK : v ∉ normalizer (K : Set G)) (htvK : t * v * t⁻¹ ∉ normalizer (K : Set G)) {m : G}
    (hm : m ∈ normalizer (W : Set G)) : m⁻¹ * (v * v) * m ∉ withKernel K := by
  intro h
  have h1 : v * v ∈ withKernel (conjugate K m⁻¹) := by
    rw [mem_withKernel_conjugate_iff, inv_inv]
    exact h
  rcases hr2 m⁻¹ (inv_mem hm) with h2 | h2
  · rw [h2] at h1
    exact hE5 v hvT hvK h1
  · rw [h2, mem_withKernel_conjugate_iff,
      show t * (v * v) * t⁻¹ = t * v * t⁻¹ * (t * v * t⁻¹) by group] at h1
    exact hE5 _ (mul_mem (mul_mem htT hvT) (inv_mem htT)) htvK h1

omit [Finite G] in
theorem conj_mem_withKernel_of_mem_sup {W K : Subgroup G} {t : G}
    (hr2 : ∀ m ∈ normalizer (W : Set G), conjugate K m = K ∨ conjugate K m = conjugate K t)
    (htM : t ∈ normalizer (W : Set G)) (hKtK : conjugate K t ≤ coreActionKernel K) {y : G}
    (hy : y ∈ K ⊔ conjugate K t) {m : G} (hm : m ∈ normalizer (W : Set G)) :
    m⁻¹ * y * m ∈ withKernel K := by
  have hle : ∀ g ∈ normalizer (W : Set G), conjugate K g ≤ withKernel K := fun g hg => by
    rcases hr2 g hg with h | h
    · rw [h]
      exact le_sup_left
    · rw [h]
      exact hKtK.trans le_sup_right
  have h1 : m⁻¹ * y * m ∈ conjugate (K ⊔ conjugate K t) m := by
    rw [mem_conjugate_iff, show m * (m⁻¹ * y * m) * m⁻¹ = y by group]
    exact hy
  have h2 : conjugate (K ⊔ conjugate K t) m = conjugate K m ⊔ conjugate K (t * m) := by
    rw [← conjugate_conjugate]
    exact Subgroup.map_sup _ _ _
  rw [h2] at h1
  exact (sup_le (hle m hm) (hle (t * m) (mul_mem htM hm))) h1

end CFSG.ComponentClassification.GrSLit.KSw
