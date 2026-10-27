module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627Key
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627Good
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627Wreath
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627Faithful
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627Cover
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.RelativePairGeometry

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem mem_map_conj_inv_iff (H : Subgroup G) (k w : G) :
    w ∈ H.map (MulAut.conj k⁻¹).toMonoidHom ↔ k * w * k⁻¹ ∈ H := by
  rw [mem_map_equiv, MulAut.conj_symm_apply, inv_inv]

omit [Finite G] in
private theorem le_normalizer_inf_of_le {A K L : Subgroup G} (hK : A ≤ normalizer (K : Set G))
    (hL : A ≤ normalizer (L : Set G)) : A ≤ normalizer ((K ⊓ L : Subgroup G) : Set G) := by
  intro a ha
  rw [mem_normalizer_iff]
  intro n
  have h1 := mem_normalizer_iff.mp (hK ha) n
  have h2 := mem_normalizer_iff.mp (hL ha) n
  simp only [mem_inf] at h1 h2 ⊢
  rw [h1, h2]

omit [Finite G] in
private theorem le_normalizer_map_conj_inv {B S : Subgroup G} {h : G}
    (hhB : h ∈ normalizer (B : Set G)) (hBS : B ≤ normalizer (S : Set G)) :
    B ≤ normalizer ((S.map (MulAut.conj h⁻¹).toMonoidHom : Subgroup G) : Set G) := by
  rw [← map_equiv_normalizer_eq]
  intro b hb
  rw [mem_map_equiv, MulAut.conj_symm_apply, inv_inv]
  exact hBS ((mem_normalizer_iff.mp hhB b).mp hb)

omit [Finite G] in
private theorem mem_centralizer_of_conj_mem_centralizer {x y h v : G}
    (hhy : (zpowers x).map (MulAut.conj h).toMonoidHom = zpowers y)
    (hv : h * v * h⁻¹ ∈ centralizer ({y} : Set G)) : v ∈ centralizer ({x} : Set G) := by
  have hxy : h * x * h⁻¹ ∈ zpowers y := by
    rw [← hhy]
    exact mem_map_of_mem _ (mem_zpowers x)
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hxy
  have hvy : (h * v * h⁻¹) * y = y * (h * v * h⁻¹) := mem_centralizer_singleton_iff.mp hv
  have hcomm : (h * v * h⁻¹) * (h * x * h⁻¹) = (h * x * h⁻¹) * (h * v * h⁻¹) := by
    rw [← hk]
    exact (Commute.zpow_right hvy k).eq
  rw [mem_centralizer_singleton_iff]
  have key : h * (v * x) * h⁻¹ = h * (x * v) * h⁻¹ :=
    calc h * (v * x) * h⁻¹ = (h * v * h⁻¹) * (h * x * h⁻¹) := by group
      _ = (h * x * h⁻¹) * (h * v * h⁻¹) := hcomm
      _ = h * (x * v) * h⁻¹ := by group
  exact mul_left_cancel (mul_right_cancel key)

private theorem le_of_plane_of_point (hS : Setting G) (hU0 : FullCoreLocal G)
    (hD2 : TheoremD2 G) (h627 : GL83SmallRankProp627 G) (h614 : GL83SmallRankProp614 G)
    {P : Sylow 3 G} {M : Subgroup G} (hsit : SmallRankSituation G 3 P M)
    (hsolv : Group.IsSolvable M)
    (e : (P : Subgroup G) ≃* (Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3))) {x₁ z : G}
    (hx₁ : SmallRankPoint P M x₁) (hz : SmallRankCentral P z) {T : Subgroup G}
    (hT : SmallRankSylowTwo P M T) {H : Subgroup G} (hH : IsTwoLocal H)
    (hBH : zpowers x₁ ⊔ zpowers z ≤ H) : H ≤ M := by
  obtain ⟨hPM, -⟩ := sylow_le_of_isCoreMaxLocal hS hsit.mem_sigmaA hsit.isCoreMaxLocal
  obtain ⟨-, hcov, -⟩ := smallRankCaseTwo_of_prop627 hS hU0 hD2 h627 h614 hsit hsolv e hx₁ hT
  have hB := SmallRankPlane.of_situation hS hsit hx₁ hz
  obtain ⟨y, hyB, hyZ, hne⟩ := exists_pCoreOf_inf_centralizer_ne_bot hS hsit hx₁ hz hH hBH
  obtain ⟨h, ⟨hhP, hhB⟩, hhy⟩ := exists_mem_normalizer_conj_zpowers hS hsit hx₁ hz hyB hyZ
  set S : Subgroup G := pCoreOf 2 H ⊓ centralizer ({y} : Set G)
  have hS2 : IsPGroup 2 S := (pCoreOf_isPGroup 2 H).to_le inf_le_left
  have hBy : zpowers x₁ ⊔ zpowers z ≤ centralizer ({y} : Set G) := fun b hb =>
    mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hB.isElemAbelian.1.is_comm.comm ⟨b, hb⟩ ⟨y, hyB⟩))
  have hBS : zpowers x₁ ⊔ zpowers z ≤ normalizer (S : Set G) :=
    le_normalizer_inf_of_le (hBH.trans (localGroup_le_normalizer_pCoreOf 2 H))
      (hBy.trans le_normalizer)
  have hS'M : S.map (MulAut.conj h⁻¹).toMonoidHom ≤ M :=
    le_of_covering hS hsit hsolv hx₁ hz hcov (hS2.map _)
      (fun v hv => mem_centralizer_of_conj_mem_centralizer hhy
        (((mem_map_conj_inv_iff S h v).mp hv).2))
      (le_normalizer_map_conj_inv hhB hBS)
  have hSM : S ≤ M :=
    (conjugate_subgroup_le_iff_of_conjugator_mem S M h⁻¹ (inv_mem (hPM hhP))).1 hS'M
  exact h614 3 P M hsit x₁ z hx₁ hz H hH hBH
    ⟨S, le_inf (inf_le_left.trans (pCoreOf_le 2 H)) hSM, hS2, hne, hBS⟩

theorem le_of_plane_of_prop627 (hS : Setting G) (hU0 : FullCoreLocal G) (hD2 : TheoremD2 G)
    (h627 : GL83SmallRankProp627 G) (h614 : GL83SmallRankProp614 G) {P : Sylow 3 G}
    {M : Subgroup G} (hsit : SmallRankSituation G 3 P M) (hsolv : Group.IsSolvable M)
    (e : (P : Subgroup G) ≃* (Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3))) {x z : G}
    (hxP : x ∈ (P : Subgroup G)) (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1)
    (hxM : ¬ centralizer ({x} : Set G) ≤ M) (hz : SmallRankCentral P z) {H : Subgroup G}
    (hH : IsTwoLocal H) (hBH : zpowers x ⊔ zpowers z ≤ H) : H ≤ M := by
  obtain ⟨hPM, -⟩ := sylow_le_of_isCoreMaxLocal hS hsit.mem_sigmaA hsit.isCoreMaxLocal
  obtain ⟨x₁, hx₁⟩ := exists_smallRankPoint hS hU0 hsit.mem_sigmaA hsit.isCoreMaxLocal
    hsit.not_gamma_one_le hsit.largeObstruction_empty
  obtain ⟨T, hT⟩ := exists_smallRankSylowTwo hS hsit.mem_sigmaA hsit.isCoreMaxLocal
  obtain ⟨g, hgP, hg⟩ := exists_conj_zpowers_of_smallRankPoint hS hsit e hx₁ hxP hx1 hx3 hxM
  have hH₁ : IsTwoLocal (H.map (MulAut.conj g⁻¹).toMonoidHom) :=
    twoLocal_map_automorphism H hH _
  have hBH₁ : zpowers x₁ ⊔ zpowers z ≤ H.map (MulAut.conj g⁻¹).toMonoidHom := by
    refine sup_le ?_ ?_
    · rw [zpowers_le, mem_map_conj_inv_iff]
      have hmem : g * x₁ * g⁻¹ ∈ zpowers x := by
        rw [hg]
        exact mem_map_of_mem _ (mem_zpowers x₁)
      exact (le_sup_left.trans hBH) hmem
    · rw [zpowers_le, mem_map_conj_inv_iff]
      have hgz : g * z = z * g := mem_centralizer_iff.mp hz.centralizes g hgP
      rw [hgz, mul_assoc, mul_inv_cancel, mul_one]
      exact hBH (mem_sup_right (mem_zpowers z))
  have hH₁M := le_of_plane_of_point hS hU0 hD2 h627 h614 hsit hsolv e hx₁ hz hT hH₁ hBH₁
  exact (conjugate_subgroup_le_iff_of_conjugator_mem H M g⁻¹ (inv_mem (hPM hgP))).1 hH₁M

end CFSG.LocalAnalysis.RankThreeTheoremC
