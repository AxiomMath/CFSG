module

public import CFSG.LocalAnalysis.RankThreeUC.Section9.Context
import all CFSG.LocalAnalysis.RankThreeUC.Section9.Context

public section

namespace CFSG.LocalAnalysis.RankThreeUC.ProofSupport.Y2ConjugationInvariance

open CFSG.LocalAnalysis.RankThreeUC CFSG.LocalAnalysis.RankThreeUC.Section9 CFSG.Open CFSG.LocalAnalysis.RankThreeUC SourceSetting Subgroup

variable {G : Type} [Group G] [Finite G]

theorem map_conj_eq_self {M : Subgroup G} {g : G} (hg : g ∈ M) :
    M.map (MulAut.conj g).toMonoidHom = M := by
  ext x
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact M.mul_mem (M.mul_mem hg hy) (M.inv_mem hg)
  · intro hx
    exact ⟨g⁻¹ * x * g, M.mul_mem (M.mul_mem (M.inv_mem hg) hx) hg, by simp [mul_assoc]⟩

theorem map_le_map_iff (g : G) {X Z : Subgroup G} :
    X.map (MulAut.conj g).toMonoidHom ≤ Z.map (MulAut.conj g).toMonoidHom ↔ X ≤ Z :=
  Subgroup.map_le_map_iff_of_injective (MulAut.conj g).injective

theorem map_inj (g : G) {X Z : Subgroup G} :
    X.map (MulAut.conj g).toMonoidHom = Z.map (MulAut.conj g).toMonoidHom ↔ X = Z :=
  (Subgroup.map_injective (MulAut.conj g).injective).eq_iff

theorem exists_eq_map (g : G) (N : Subgroup G) :
    ∃ N' : Subgroup G, N = N'.map (MulAut.conj g).toMonoidHom :=
  ⟨N.comap (MulAut.conj g).toMonoidHom,
    (Subgroup.map_comap_eq_self_of_surjective (MulAut.conj g).surjective N).symm⟩

theorem map_oPrimeResidual (g : G) (p : ℕ) (Y : Subgroup G) :
    (oPrimeResidual p Y).map (MulAut.conj g).toMonoidHom =
      oPrimeResidual p (Y.map (MulAut.conj g).toMonoidHom) := by
  unfold oPrimeResidual
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_setOf_eq, Subgroup.mem_map]
  constructor
  · rintro ⟨y, ⟨hy, k, hk⟩, rfl⟩
    exact ⟨⟨y, hy, rfl⟩, k, by rw [MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq]; exact hk⟩
  · rintro ⟨⟨y, hy, rfl⟩, k, hk⟩
    exact ⟨y, ⟨hy, k, by rw [← hk, MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq]⟩, rfl⟩

theorem map_map_conj (a b : G) (X : Subgroup G) :
    (X.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      X.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

theorem map_map_conj_conj (g h : G) (X : Subgroup G) :
    (X.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      (X.map (MulAut.conj g).toMonoidHom).map (MulAut.conj (g * h * g⁻¹)).toMonoidHom := by
  rw [map_map_conj, map_map_conj]
  congr 2
  simp [mul_assoc]

theorem map_normalClosureUnder (g : G) (X H : Subgroup G) :
    (normalClosureUnder X H).map (MulAut.conj g).toMonoidHom =
      normalClosureUnder (X.map (MulAut.conj g).toMonoidHom) (H.map (MulAut.conj g).toMonoidHom) := by
  unfold normalClosureUnder
  rw [Subgroup.map_iSup]
  apply le_antisymm
  · refine iSup_le fun h => ?_
    rw [map_map_conj_conj]
    exact le_iSup (fun h : H.map (MulAut.conj g).toMonoidHom =>
      (X.map (MulAut.conj g).toMonoidHom).map (MulAut.conj (h : G)).toMonoidHom)
      ⟨g * h * g⁻¹, ⟨h, h.2, by simp⟩⟩
  · refine iSup_le fun h => ?_
    obtain ⟨k, hk, hkh⟩ := h.2
    have h2 : (h : G) = g * k * g⁻¹ := by rw [← hkh]; simp
    rw [h2, ← map_map_conj_conj]
    exact le_iSup (fun h : H => (X.map (MulAut.conj (h : G)).toMonoidHom).map
      (MulAut.conj g).toMonoidHom) ⟨k, hk⟩

theorem map_pCoreOf (g : G) (p : ℕ) (H : Subgroup G) :
    (pCoreOf p H).map (MulAut.conj g).toMonoidHom =
      pCoreOf p (H.map (MulAut.conj g).toMonoidHom) :=
  (CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv p (MulAut.conj g) H).symm

theorem map_normalizer (g : G) (A : Subgroup G) :
    (Subgroup.normalizer (A : Set G)).map (MulAut.conj g).toMonoidHom =
      Subgroup.normalizer ((A.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) :=
  Subgroup.map_equiv_normalizer_eq A (MulAut.conj g)

theorem map_pRank (g : G) (p : ℕ) (hp : 1 < p) (H : Subgroup G) :
    CFSG.Open.pRank p (H.map (MulAut.conj g).toMonoidHom) = CFSG.Open.pRank p H :=
  CFSG.RankThreeCoreUniqueness.Helpers.pRank_map_automorphism p hp H (MulAut.conj g)

theorem card_map (g : G) (X : Subgroup G) :
    Nat.card (X.map (MulAut.conj g).toMonoidHom) = Nat.card X :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem mem_maxSubgroupsContaining_map_iff (g : G) (N Y : Subgroup G) :
    N.map (MulAut.conj g).toMonoidHom ∈ maxSubgroupsContaining (Y.map (MulAut.conj g).toMonoidHom) ↔
      N ∈ maxSubgroupsContaining Y := by
  unfold maxSubgroupsContaining
  simp only [Set.mem_setOf_eq]
  exact and_congr (OrderIso.isCoatom_iff (MulEquiv.mapSubgroup (MulAut.conj g)) N) (map_le_map_iff g)

theorem maxSubgroupsContaining_map_eq_singleton_iff {M : Subgroup G} {g : G} (hg : g ∈ M)
    (Y : Subgroup G) :
    maxSubgroupsContaining (Y.map (MulAut.conj g).toMonoidHom) = {M} ↔
      maxSubgroupsContaining Y = {M} := by
  have hM := map_conj_eq_self hg
  have e : ∀ N : Subgroup G, N.map (MulAut.conj g).toMonoidHom = M ↔ N = M := fun N => by
    have := map_inj g (X := N) (Z := M)
    rw [hM] at this
    exact this
  constructor
  · intro h
    ext N
    rw [← mem_maxSubgroupsContaining_map_iff g, h, Set.mem_singleton_iff, Set.mem_singleton_iff, e]
  · intro h
    ext N
    obtain ⟨N', rfl⟩ := exists_eq_map g N
    rw [mem_maxSubgroupsContaining_map_iff, h, Set.mem_singleton_iff, Set.mem_singleton_iff, e]

theorem map_le_map_conj_mul_iff (g h : G) (A B : Subgroup G) :
    A.map (MulAut.conj g).toMonoidHom ≤ B.map (MulAut.conj (g * h)).toMonoidHom ↔
      A ≤ B.map (MulAut.conj h).toMonoidHom := by
  rw [← map_map_conj, map_le_map_iff]

theorem mem_uniqueSet_map_iff {M : Subgroup G} {g : G} (hg : g ∈ M) (D : Subgroup G) :
    D.map (MulAut.conj g).toMonoidHom ∈ uniqueSet M ↔ D ∈ uniqueSet M := by
  have hM := map_conj_eq_self hg
  unfold uniqueSet
  simp only [Set.mem_setOf_eq]
  refine and_congr ?_ ⟨fun H h hh => ?_, fun H h hh => ?_⟩
  · conv_lhs => rw [← hM]
    exact map_le_map_iff g
  · have h1 := H (g * h) ((map_le_map_conj_mul_iff g h D M).mpr hh)
    have h2 := map_map_conj h g M
    rw [h1] at h2
    exact (map_inj g).mp (h2.trans hM.symm)
  · have hh' : D ≤ M.map (MulAut.conj (g⁻¹ * h)).toMonoidHom := by
      rw [← map_le_map_conj_mul_iff g (g⁻¹ * h), mul_inv_cancel_left]; exact hh
    have h1 := H (g⁻¹ * h) hh'
    have h2 := map_map_conj (g⁻¹ * h) g M
    rw [mul_inv_cancel_left, h1, hM] at h2
    exact h2.symm

theorem le_M_map_iff {M : Subgroup G} {g : G} (hg : g ∈ M) (X : Subgroup G) :
    X.map (MulAut.conj g).toMonoidHom ≤ M ↔ X ≤ M := by
  conv_lhs => rw [← map_conj_eq_self hg]
  exact map_le_map_iff g

theorem mem_YSet_map_conj_iff {G : Type} [Group G] [Finite G] {M : Subgroup G} {g : G}
    (hg : g ∈ M) {Y : Subgroup G} :
    Y ∈ Section9.YSet M ↔ Y.map (MulAut.conj g).toMonoidHom ∈ Section9.YSet M := by
  unfold Section9.YSet
  simp only [Set.mem_setOf_eq]
  rw [le_M_map_iff hg, ne_eq, ne_eq, maxSubgroupsContaining_map_eq_singleton_iff hg]
  refine and_congr Iff.rfl (and_congr Iff.rfl ⟨fun H D hD hc => ?_, fun H D hD hc => ?_⟩)
  · obtain ⟨D', rfl⟩ := exists_eq_map g D
    rw [mem_uniqueSet_map_iff hg]
    rw [map_le_map_iff] at hD
    exact H D' hD (by rw [← card_map g]; exact hc)
  · rw [← mem_uniqueSet_map_iff hg]
    exact H _ ((map_le_map_iff g).mpr hD) (by rw [card_map]; exact hc)

theorem mem_HSet_map_conj_iff {G : Type} [Group G] [Finite G] {M : Subgroup G} {g : G}
    (hg : g ∈ M) {Y H : Subgroup G} :
    H ∈ Section9.HSet M Y ↔ H.map (MulAut.conj g).toMonoidHom ∈ Section9.HSet M (Y.map (MulAut.conj g).toMonoidHom) := by
  unfold Section9.HSet
  simp only [Set.mem_setOf_eq]
  rw [map_le_map_iff, le_M_map_iff hg, ← map_oPrimeResidual, ← map_normalClosureUnder,
    map_pRank g 3 (by norm_num)]

theorem mem_invariantPPrimeSubgroups_map_conj_iff {M : Subgroup G} {g : G} (hg : g ∈ M)
    (Y A : Subgroup G) (p : ℕ) :
    A.map (MulAut.conj g).toMonoidHom ∈ invariantPPrimeSubgroups M (Y.map (MulAut.conj g).toMonoidHom) p ↔
      A ∈ invariantPPrimeSubgroups M Y p := by
  unfold invariantPPrimeSubgroups
  simp only [Set.mem_setOf_eq]
  rw [le_M_map_iff hg, ← map_normalizer, map_le_map_iff, card_map]

theorem quotientIsTwoGroup_map_iff (g : G) (p : ℕ) (Y : Subgroup G) :
    QuotientIsTwoGroup p (Y.map (MulAut.conj g).toMonoidHom) ↔ QuotientIsTwoGroup p Y := by
  unfold QuotientIsTwoGroup
  rw [← map_oPrimeResidual]
  constructor
  · intro H y hy
    obtain ⟨k, hk⟩ := H _ (Subgroup.mem_map_of_mem _ hy)
    refine ⟨k, ?_⟩
    rw [← map_pow] at hk
    exact (Subgroup.mem_map_iff_mem (MulAut.conj g).injective).mp hk
  · intro H y hy
    obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.mp hy
    obtain ⟨k, hk⟩ := H y' hy'
    exact ⟨k, by rw [← map_pow]; exact Subgroup.mem_map_of_mem _ hk⟩

theorem mem_Y2Set_map_conj_iff {G : Type} [Group G] [Finite G] {M : Subgroup G} {g : G}
    (hg : g ∈ M) {Y : Subgroup G} :
    Y ∈ Section9.Y2Set M ↔ Y.map (MulAut.conj g).toMonoidHom ∈ Section9.Y2Set M := by
  unfold Section9.Y2Set
  simp only [Set.mem_setOf_eq]
  rw [← mem_YSet_map_conj_iff hg, ne_eq, ne_eq, maxSubgroupsContaining_map_eq_singleton_iff hg,
    quotientIsTwoGroup_map_iff]
  refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr ⟨fun H N hN => ?_, fun H N hN => ?_⟩
    (and_congr ⟨fun H A hA => ?_, fun H A hA => ?_⟩ Iff.rfl)))
  · obtain ⟨N', rfl⟩ := exists_eq_map g N
    rw [mem_maxSubgroupsContaining_map_iff] at hN
    rcases H hN with h | h
    · exact Or.inl ((mem_HSet_map_conj_iff hg).mp h)
    · right
      rw [Set.mem_singleton_iff] at h ⊢
      rw [h, map_conj_eq_self hg]
  · have hN' : N.map (MulAut.conj g).toMonoidHom ∈
        maxSubgroupsContaining (Y.map (MulAut.conj g).toMonoidHom) :=
      (mem_maxSubgroupsContaining_map_iff g N Y).mpr hN
    rcases H hN' with h | h
    · exact Or.inl ((mem_HSet_map_conj_iff hg).mpr h)
    · right
      rw [Set.mem_singleton_iff] at h ⊢
      have := map_inj g (X := N) (Z := M)
      rw [map_conj_eq_self hg] at this
      exact this.mp h
  · obtain ⟨A', rfl⟩ := exists_eq_map g A
    rw [mem_invariantPPrimeSubgroups_map_conj_iff hg] at hA
    rw [← map_oPrimeResidual, ← Subgroup.map_commutator, ← map_pCoreOf, map_le_map_iff]
    exact H A' hA
  · have := H (A.map (MulAut.conj g).toMonoidHom)
      ((mem_invariantPPrimeSubgroups_map_conj_iff hg Y A 3).mpr hA)
    rwa [← map_oPrimeResidual, ← Subgroup.map_commutator, ← map_pCoreOf, map_le_map_iff] at this

end CFSG.LocalAnalysis.RankThreeUC.ProofSupport.Y2ConjugationInvariance
