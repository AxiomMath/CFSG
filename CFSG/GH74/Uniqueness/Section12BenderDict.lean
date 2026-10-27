module

public import CFSG.GH74.Uniqueness.Section12Basic
public import CFSG.GH74.Uniqueness.Section7Cor713Data

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem ZDSetup.ncard_alphaOrbit (S : ZDSetup X Z M) (F : Subgroup X) :
    (alphaOrbit M F).ncard = ((M ⊓ F).subgroupOf F).index := by
  classical
  let p0 : omega M := ⟨M, self_mem_omega M⟩
  have hstab : MulAction.stabilizer ↥F p0 = (M ⊓ F).subgroupOf F := by
    ext f
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    have h1 : (f • p0 : omega M) = p0 ↔ conjugate M (f : X)⁻¹ = M := by
      constructor
      · intro h
        exact congrArg Subtype.val h
      · intro h
        exact Subtype.ext h
    rw [h1, S.prodDisc.conjugate_eq_iff_mem (self_mem_omega M), M.inv_mem_iff]
    exact ⟨fun h => ⟨h, f.2⟩, fun h => h.1⟩
  have horb : alphaOrbit M F = Subtype.val '' (MulAction.orbit ↥F p0 : Set (omega M)) := by
    ext γ
    constructor
    · rintro ⟨f, hf, rfl⟩
      refine ⟨⟨conjugate M f, conjugate_mem_omega (self_mem_omega M) f⟩,
        ⟨⟨f⁻¹, F.inv_mem hf⟩, ?_⟩, rfl⟩
      apply Subtype.ext
      show conjugate M (f⁻¹)⁻¹ = conjugate M f
      rw [inv_inv]
    · rintro ⟨⟨β, hβ⟩, ⟨g, hg⟩, rfl⟩
      refine ⟨(g : X)⁻¹, F.inv_mem g.2, ?_⟩
      exact congrArg Subtype.val hg
  rw [horb, Set.ncard_image_of_injective _ Subtype.val_injective, ← MulAction.index_stabilizer,
    hstab]

theorem ZDSetup.exists_not_commute (S : ZDSetup X Z M) : ¬ ∀ a b : X, a * b = b * a := by
  obtain ⟨t, -, htM⟩ := S.exists_mem_not_mem
  obtain ⟨z, hz, hzM⟩ := S.exists_mem_inter
  intro hall
  apply htM
  refine (S.prodDisc.2.2.1 z hz hzM t).mp ?_
  rw [hall t⁻¹ z, mul_assoc, inv_mul_cancel, mul_one]
  exact hzM

theorem BenderSub.center_le
    (S : ZDSetup X Z M) {F : Subgroup X} {n i e : ℕ}
    (hB : BenderSub Z M F n i e) : ∀ x ∈ center ↥F, (x : X) ∈ M := by
  have hnsF : ¬ Group.IsSolvable ↥F := by
    intro hsol
    have hsolv : Group.IsSolvable (↥F ⧸ center ↥F) :=
      Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective (center ↥F))
    have hbg := Bender.isBenderGroup_iff_exists_benderType.mpr ⟨n, i, e, hB.bender⟩
    have := isSimpleGroup_of_isBenderGroup hbg
    obtain ⟨x, y, hxy⟩ := exists_not_commute_of_isBenderGroup hbg
    exact hxy ((IsSimpleGroup.comm_iff_isSolvable.mpr hsolv) x y)
  have hrank2 := S.cor713_two_le_twoRank_zHull hB.ne_top hB.not_le hB.nonempty
    (by rw [hB.zhull]; exact hnsF)
  set O : Subgroup X := pPrimeCoreIn F with hO
  have hOodd : Odd (Nat.card O) := odd_card_pPrimeCoreIn F
  have hFN : F ≤ normalizer (O : Set X) := pPrimeCoreIn_normalizes F
  have hrank : 2 ≤ Open.pRank 2 (zHull Z (normalizer (O : Set X))) := by
    have h1 : Open.pRank 2 (zHull Z F) = Open.twoRank ↥(zHull Z F) := by
      rw [Open.twoRank]
      exact CFSG.RankThreeCoreUniqueness.Helpers.pRank_subgroup_eq_internal_top 2 (by norm_num) _
    have h2 : zHull Z F ≤ zHull Z (normalizer (O : Set X)) :=
      Subgroup.closure_mono (Set.inter_subset_inter_right Z hFN)
    exact hrank2.trans (h1 ▸ CFSG.SectionRank.pRank_mono (by norm_num) h2)
  obtain ⟨s, hsZ, hsFM⟩ := hB.nonempty
  have hsF : s ∈ F := (Subgroup.mem_inf.mp hsFM).1
  have hsM : s ∈ M := (Subgroup.mem_inf.mp hsFM).2
  have hOM : O ≤ M := S.lemma313 hOodd hrank hsZ (hFN hsF) (self_mem_omega M)
    ((S.prodDisc.conjugate_eq_iff_mem (self_mem_omega M)).mpr hsM)
  intro x hx
  exact hOM (by
    rw [hO, hB.core]
    exact ⟨x, hx, rfl⟩)

theorem BenderSub.index_eq
    (S : ZDSetup X Z M) {F : Subgroup X} {n i e : ℕ}
    (hB : BenderSub Z M F n i e) : ((M ⊓ F).subgroupOf F).index = (2 ^ n) ^ i + 1 := by
  obtain ⟨T, hT⟩ := hB.borel
  have hker : (QuotientGroup.mk' (center ↥F)).ker ≤ (M ⊓ F).subgroupOf F := by
    rw [QuotientGroup.ker_mk']
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨hB.center_le S x hx, x.2⟩)
  rw [← Subgroup.index_map_eq ((M ⊓ F).subgroupOf F) (QuotientGroup.mk'_surjective (center ↥F))
    hker, hT]
  obtain ⟨t, hc⟩ := hB.bender.exists_benderCore T
  exact hc.index_eq

theorem ZDSetup.omegaFix_eq_alphaOrbit (S : ZDSetup X Z M) {u : X} (hu2 : orderOf u = 2)
    (huM : u ∈ M) {m j e : ℕ} (hB : BenderSub Z M (cenHull Z u) m j e) :
    omegaFix M ({u} : Set X) = alphaOrbit M (cenHull Z u) := by
  have hLC : cenHull Z u ≤ centralizer ({u} : Set X) := Cor713.zHull_le (Z := Z) _
  have hCM : ¬ centralizer ({u} : Set X) ≤ M := fun h => hB.not_le (hLC.trans h)
  have hne : (Z ∩ ((centralizer ({u} : Set X) ⊓ M : Subgroup X) : Set X)).Nonempty := by
    obtain ⟨z, hz, hzFM⟩ := hB.nonempty
    exact ⟨z, hz, Subgroup.mem_inf.mpr
      ⟨hLC (Subgroup.mem_inf.mp hzFM).1, (Subgroup.mem_inf.mp hzFM).2⟩⟩
  have horb := S.cor713_alphaOrbit_eq hCM hne
  have hMu : conjugate M u = M :=
    (S.prodDisc.conjugate_eq_iff_mem (self_mem_omega M)).mpr huM
  ext β
  constructor
  · intro hβ
    have hβu : conjugate β u = β := hβ.2 u (Set.mem_singleton u)
    obtain ⟨c, hcC, hc⟩ := S.exists_centralizer_conj hu2 (self_mem_omega M) hβ.1 hMu hβu
    have hmem : β ∈ alphaOrbit M (centralizer ({u} : Set X)) := ⟨c, hcC, hc⟩
    rw [horb] at hmem
    exact hmem
  · rintro ⟨l, hl, rfl⟩
    refine ⟨conjugate_mem_omega (self_mem_omega M) l, fun g hg => ?_⟩
    rw [Set.mem_singleton_iff.mp hg, conjugate_conjugate,
      (Subgroup.mem_centralizer_singleton_iff.mp (hLC hl)), ← conjugate_conjugate, hMu]

theorem ZDSetup.ncard_omegaFix_of_benderSub
    (S : ZDSetup X Z M) {u : X} (hu2 : orderOf u = 2)
    (huM : u ∈ M) {m j e : ℕ} (hB : BenderSub Z M (cenHull Z u) m j e) :
    (omegaFix M ({u} : Set X)).ncard = (2 ^ m) ^ j + 1 := by
  rw [S.omegaFix_eq_alphaOrbit hu2 huM hB, S.ncard_alphaOrbit, hB.index_eq S]

end CFSG.GH74.Uniqueness
