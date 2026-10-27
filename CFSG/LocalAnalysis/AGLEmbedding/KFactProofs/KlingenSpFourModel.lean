module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.KlingenSpFourMat
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.KlingenSpFourAlg
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeKill
import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherMaximal
import CFSG.ClassicalGroups.Symplectic.Simple

public section

namespace CFSG.AGLEmbedding.KlingenSpFour

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open scoped MatrixGroups

variable (p : ℕ) [Fact p.Prime]

abbrev PSp4 : Type := StatedProj (StatedSp 2 (ZMod p))

instance : Finite (PSp4 p) :=
  CFSG.ClassicalGroups.Symplectic.finite_statedProj_statedSp 2 (ZMod p)

noncomputable def heisG : HeisData p (PSp4 p) where
  e s t u := proj 2 (ZMod p) (eEl s t u)
  e_mul s t u s' t' u' := by rw [← map_mul, eEl_mul]
  e_inj s t u s' t' u' h := eEl_inj (proj_injOn_unipotent (by norm_num)
    (eEl_mem_unipotent _ _ _) (eEl_mem_unipotent _ _ _) h)

noncomputable def xG : XData p (PSp4 p) where
  x a b c := proj 2 (ZMod p) (xEl a b c)
  x_mul a b c a' b' c' := by rw [← map_mul, xEl_mul]
  x_inj a b c a' b' c' h := xEl_inj (proj_injOn_unipotent (by norm_num)
    (xEl_mem_unipotent _ _ _) (xEl_mem_unipotent _ _ _) h)

noncomputable def lG : SL(2, ZMod p) →* PSp4 p := (proj 2 (ZMod p)).comp iotaSp

theorem lG_conj (g : SL(2, ZMod p)) (s t u : ZMod p) :
    lG p g * (heisG p).e s t u * (lG p g)⁻¹ =
      (heisG p).e (g 1 1 * s - g 1 0 * t) (g 0 0 * t - g 0 1 * s)
        (u + s * t - (g 1 1 * s - g 1 0 * t) * (g 0 0 * t - g 0 1 * s)) := by
  simp only [lG, heisG, MonoidHom.comp_apply]
  rw [← map_mul, ← map_inv, ← map_mul, iotaSp_conj]

theorem two_ne_zero_zmod (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have h2 : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h2
  exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).mp h2)

theorem exists_klingenAlt (hp2 : p ≠ 2) :
    ∃ T : Sylow p (PSp4 p), KlingenAlt p (PSp4 p) T ∧
      3 ≤ Open.pRank p (T : Subgroup (PSp4 p)) := by
  have hp : p.Prime := Fact.out
  obtain ⟨T, hT⟩ := exists_sylow_projUnipotent (K := ZMod p) p (r := 2) (by norm_num)
  set H := heisG p with hH
  set X := xG p with hX
  have hET : H.E ≤ (T : Subgroup (PSp4 p)) := by
    rintro g ⟨s, t, u, rfl⟩
    rw [hT]
    exact Subgroup.mem_map_of_mem _ (eEl_mem_unipotent s t u)
  have hUT : X.U ≤ (T : Subgroup (PSp4 p)) := by
    rintro g ⟨a, b, c, rfl⟩
    rw [hT]
    exact Subgroup.mem_map_of_mem _ (xEl_mem_unipotent a b c)
  have hrankU : 3 ≤ Open.pRank p X.U :=
    CFSG.SectionRank.le_pRank hp.one_lt le_rfl X.isElemAbelian_U X.card_U
  have hrankT : 3 ≤ Open.pRank p (T : Subgroup (PSp4 p)) :=
    hrankU.trans (PreuniquenessRankFour.Helpers.pRank_mono p hp hUT)
  refine ⟨T, ?_, hrankT⟩
  have hcent : ∀ y ∈ H.D, y ∈ Subgroup.centralizer ((T : Subgroup (PSp4 p)) : Set (PSp4 p)) →
      y ∈ (Subgroup.center H.E).map H.E.subtype := by
    rintro y ⟨s, u, rfl⟩ hy
    have hxT : X.x 0 1 0 ∈ (T : Subgroup (PSp4 p)) := by
      rw [hT]; exact Subgroup.mem_map_of_mem _ (xEl_mem_unipotent 0 1 0)
    have hcomm := Subgroup.mem_centralizer_iff.mp hy _ hxT
    have h2 : eEl s 0 u * xEl 0 1 0 = xEl 0 1 0 * eEl s 0 u := by
      apply proj_injOn_unipotent (by norm_num)
        (mul_mem (eEl_mem_unipotent _ _ _) (xEl_mem_unipotent _ _ _))
        (mul_mem (xEl_mem_unipotent _ _ _) (eEl_mem_unipotent _ _ _))
      simp only [map_mul]
      exact hcomm.symm
    have hs : s = 0 := by
      have := eEl_xEl_comm h2
      exact (mul_eq_zero.mp this).resolve_left (two_ne_zero_zmod p hp2)
    subst hs
    rw [HeisData.map_center_E H hp2]
    exact ⟨u, rfl⟩
  set PS : Subgroup (PSp4 p) := projStabilizer 2 (ZMod p) (flag 2 (ZMod p) 2) with hPS
  have hPScoatom : IsCoatom PS :=
    isCoatom_projStabilizer_flag (r := 2) (d := 2) (by norm_num) le_rfl
  have hfwd : ∀ y ∈ PS, ∀ n ∈ X.U, y * n * y⁻¹ ∈ X.U := by
    rintro _ ⟨h, hh, rfl⟩ _ ⟨a, b, c, rfl⟩
    obtain ⟨a', b', c', hab⟩ := stabilizer_conj_xEl hh a b c
    refine ⟨a', b', c', ?_⟩
    show _ = proj 2 (ZMod p) (xEl a' b' c')
    rw [← hab]
    simp only [map_mul, map_inv]
    rfl
  have hPSN : PS ≤ Subgroup.normalizer (X.U : Set (PSp4 p)) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro n
    refine ⟨fun hn => hfwd y hy n hn, fun hn => ?_⟩
    have := hfwd y⁻¹ (PS.inv_mem hy) _ hn
    simpa [mul_assoc] using this
  have hWC : Subgroup.normalizer (X.U : Set (PSp4 p)) ≤
      Open.GLBWeakCore p (T : Subgroup (PSp4 p)) :=
    PreuniquenessRankFour.Helpers.normalizer_le_weakCore p hUT (hrankU.trans' (by norm_num))
      (hrankU.trans (PreuniquenessRankFour.Helpers.pRank_mono p hp le_sup_left))
  let g₀ : SL(2, ZMod p) := ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩
  have hx₀P : lG p g₀ ∉ PS := by
    intro hmem
    have h1 : iotaSp g₀ ∈ stabilizer 2 (ZMod p) (flag 2 (ZMod p) 2) := by
      rw [← comap_projStabilizer]
      exact hmem
    exact iotaSp_not_mem_stabilizer g₀ (by simp [g₀]) h1
  have hx₀L : lG p g₀ ∈ (lG p).range := MonoidHom.mem_range.mpr ⟨g₀, rfl⟩
  have hx₀D : lG p g₀ ∈ Subgroup.normalizer (H.D : Set (PSp4 p)) := by
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨s, u, rfl⟩
    have h := lG_conj p g₀ s 0 u
    rw [mul_inv_eq_iff_eq_mul] at h
    have : (heisG p).e (g₀ 1 1 * s - g₀ 1 0 * 0) (g₀ 0 0 * 0 - g₀ 0 1 * s)
        (u + s * 0 - (g₀ 1 1 * s - g₀ 1 0 * 0) * (g₀ 0 0 * 0 - g₀ 0 1 * s)) =
        (heisG p).e s 0 u := by
      congr 1 <;> simp [g₀]
    rw [this] at h
    exact h.symm
  have hgen : ∀ M : Subgroup (PSp4 p), lG p g₀ ∈ M →
      Open.GLBWeakCore p (T : Subgroup (PSp4 p)) ⊔ M = ⊤ := by
    intro M hM
    have hPle : PS ≤ Open.GLBWeakCore p (T : Subgroup (PSp4 p)) ⊔ M :=
      le_sup_of_le_left (hPSN.trans hWC)
    refine hPScoatom.2 _ (lt_of_le_of_ne hPle fun h => hx₀P ?_)
    rw [h]
    exact Subgroup.mem_sup_right hM
  exact ⟨H.E, H.D, (lG p).range, hET, H.card_E, fun x hx => H.pow_eq_one_of_mem_E hx,
    H.card_center_E hp2, H.D_le_E, H.isElemAbelian_D, H.card_D, hcent,
    (H.map_center_E hp2).symm ▸ H.l_range_le_centralizer hp2 (lG p) (lG_conj p),
    ⟨H.coordE hp2, H.sl_action hp2 (lG p) (lG_conj p)⟩, hgen _ hx₀D, hgen _ hx₀L⟩

end CFSG.AGLEmbedding.KlingenSpFour
