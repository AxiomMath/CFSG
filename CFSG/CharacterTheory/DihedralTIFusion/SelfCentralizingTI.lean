module

public import CFSG.Foundations.Basic

public section

namespace CFSG.DihedralTIFusion

variable {W : Type*} [Group W]

theorem normalizer_diff_one (K : Subgroup W) :
    Subgroup.normalizer ((K : Set W) \ {1}) = Subgroup.normalizer (K : Set W) := by
  have key : ∀ (g n : W), n ≠ 1 →
      ((n ∈ (K : Set W) \ {1} ↔ g * n * g⁻¹ ∈ (K : Set W) \ {1}) ↔
        (n ∈ (K : Set W) ↔ g * n * g⁻¹ ∈ (K : Set W))) := by
    intro g n hn
    have hgn : g * n * g⁻¹ ≠ 1 := fun h => hn (conj_eq_one_iff.mp h)
    simp only [Set.mem_sdiff, Set.mem_singleton_iff, hn, hgn, not_false_eq_true, and_true]
  ext g
  rw [Subgroup.mem_set_normalizer_iff, Subgroup.mem_set_normalizer_iff]
  constructor
  · intro h n
    by_cases hn : n = 1
    · subst hn
      simp only [mul_one, mul_inv_cancel, SetLike.mem_coe, one_mem]
    · exact (key g n hn).mp (h n)
  · intro h n
    by_cases hn : n = 1
    · subst hn
      simp
    · exact (key g n hn).mpr (h n)

theorem self_centralizing_subgroup_TI {K : Subgroup W} (hK : K ≠ ⊥)
    (hC : ∀ k ∈ K, k ≠ 1 → Subgroup.centralizer ({k} : Set W) = K) :
    IsMulCommutative K ∧ Subgroup.centralizer (K : Set W) = K ∧
      IsTISubset ((K : Set W) \ {1}) (Subgroup.normalizer (K : Set W)) := by
  have hcomm : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a := by
    intro a ha b hb
    by_cases ha1 : a = 1
    · simp [ha1]
    · have hb' : b ∈ Subgroup.centralizer ({a} : Set W) := by rw [hC a ha ha1]; exact hb
      exact (Subgroup.mem_centralizer_singleton_iff.mp hb').symm
  obtain ⟨k, hkK, hk1⟩ := (Subgroup.bot_or_exists_ne_one K).resolve_left hK
  refine ⟨⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩, ?_, ?_⟩
  · apply le_antisymm
    · calc Subgroup.centralizer (K : Set W) ≤ Subgroup.centralizer ({k} : Set W) :=
            Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hkK)
        _ = K := hC k hkK hk1
    · intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact hcomm y hy x hx
  refine ⟨⟨k, hkK, hk1⟩, fun h => h.2 rfl, normalizer_diff_one K, ?_⟩
  intro g hg
  ext x
  simp only [Set.mem_inter_iff, Set.mem_image, Set.mem_empty_iff_false, iff_false, not_and]
  rintro ⟨hxK, hx1⟩ ⟨y, ⟨hyK, hy1⟩, hxy⟩
  subst hxy
  apply hg
  rw [Subgroup.mem_set_normalizer_iff]
  intro n
  have hCx := hC _ hxK hx1
  have hCy := hC y hyK hy1
  constructor
  · intro hn
    have h1 : n ∈ Subgroup.centralizer ({g⁻¹ * y * g} : Set W) := by rw [hCx]; exact hn
    rw [Subgroup.mem_centralizer_singleton_iff] at h1
    rw [SetLike.mem_coe, ← hCy, Subgroup.mem_centralizer_singleton_iff]
    calc g * n * g⁻¹ * y = g * (n * (g⁻¹ * y * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * y * g) * n) * g⁻¹ := by rw [h1]
      _ = y * (g * n * g⁻¹) := by group
  · intro hn
    have h1 : g * n * g⁻¹ ∈ Subgroup.centralizer ({y} : Set W) := by rw [hCy]; exact hn
    rw [Subgroup.mem_centralizer_singleton_iff] at h1
    rw [SetLike.mem_coe, ← hCx, Subgroup.mem_centralizer_singleton_iff]
    calc n * (g⁻¹ * y * g) = g⁻¹ * ((g * n * g⁻¹) * y) * g := by group
      _ = g⁻¹ * (y * (g * n * g⁻¹)) * g := by rw [h1]
      _ = g⁻¹ * y * g * n := by group

end CFSG.DihedralTIFusion
