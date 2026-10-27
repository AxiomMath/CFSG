module

public import CFSG.GroupTheory.SimpleNormalHom
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.GH312.PSp45Wedge
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.GH312.SoGroup5Card
import CFSG.Adapters.RankTwoModelTransports
import CFSG.ClassicalGroups.Symplectic.Simple
import CFSG.ClassicalInvolution.Orders.Symplectic

public section

namespace CFSG.EvenSporadicStandard.TwoHS.GH312

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

theorem conj_proj_statedSp_eq_conjAut (s : StatedSp 2 (ZMod 5)) :
    MulAut.conj (proj 2 (ZMod 5) s) = conjAut 2 (ZMod 5) ⟨s, statedSp_le_gsp s.2⟩ := by
  ext y
  induction y using QuotientGroup.induction_on with
  | H g =>
    change _ = conjAut 2 (ZMod 5) _ (proj 2 (ZMod 5) g)
    rw [conjAut_proj]
    simp only [MulAut.conj_apply, proj, QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_inv]
    congr 1

theorem natCard_statedProj_statedSp_zmod_five :
    Nat.card (StatedProj (StatedSp 2 (ZMod 5))) = 4680000 := by
  have h := CFSG.ClassicalInvolution.card_statedProj_statedSp_of_two_ne_zero (K := ZMod 5)
    (n := 2) (by decide) (by norm_num)
  rw [Nat.card_zmod] at h
  have hp : (∏ j ∈ Finset.Icc 1 2, (5 ^ (2 * j) - 1)) = 24 * 624 := by
    simp [Finset.prod_Icc_succ_top]
  rw [hp] at h
  omega

theorem nonempty_mulEquiv_pgsp45_of_zmod_five {X : Type} [Group X] [Finite X] (T : Subgroup X)
    [T.Normal] (e : T ≃* StatedProj (StatedSp 2 (ZMod 5)))
    (hC : Subgroup.centralizer (T : Set X) = ⊥) (hT : T ≠ ⊤) : Nonempty (X ≃* PGSp45) := by
  haveI : IsSimpleGroup (StatedProj (StatedSp 2 (ZMod 5))) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp (ZMod 5) 2 (by norm_num)
      (Or.inl (Or.inr (by rw [Nat.card_zmod]; norm_num)))
  haveI : IsSimpleGroup T := e.isSimpleGroup
  let aut : X →* MulAut (StatedProj (StatedSp 2 (ZMod 5))) :=
    (MulAut.congr e).toMonoidHom.comp MulAut.conjNormal
  let aut' : X →* (conjAut 2 (ZMod 5)).range :=
    aut.codRestrict _ fun x => range_conjAut_eq_top ▸ Subgroup.mem_top _
  let ψ : X →* soGroup5 := rangeToSoGroup5.comp aut'
  have hcardT : Nat.card T = 4680000 := by
    rw [Nat.card_congr e.toEquiv, natCard_statedProj_statedSp_zmod_five]
  have hφ : ∃ t ∈ T, ψ t ≠ 1 := by
    let s : StatedSp 2 (ZMod 5) := ⟨diagTwoOneThreeOneGsp, by
      rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff]
      simpa [diagTwoOneThreeOneGsp] using diagTwoOneThreeOne_symplectic⟩
    refine ⟨e.symm (proj 2 (ZMod 5) s), (e.symm (proj 2 (ZMod 5) s)).2, ?_⟩
    have haut : aut (e.symm (proj 2 (ZMod 5) s)) = conjAut 2 (ZMod 5) diagTwoOneThreeOneGsp := by
      have : (⟨s, statedSp_le_gsp s.2⟩ : gsp 2 (ZMod 5)) = diagTwoOneThreeOneGsp := rfl
      rw [← this, ← conj_proj_statedSp_eq_conjAut]
      ext y
      simp [aut, MulAut.congr_apply, MulAut.conjNormal_val]
    have : aut' (e.symm (proj 2 (ZMod 5) s)) =
        ⟨conjAut 2 (ZMod 5) diagTwoOneThreeOneGsp, diagTwoOneThreeOneGsp, rfl⟩ :=
      Subtype.ext haut
    simp only [ψ, MonoidHom.comp_apply, this, rangeToSoGroup5_apply]
    exact gspToSoGroup5_diag_ne_one
  have hcard : Nat.card soGroup5 ≤ 2 * Nat.card T := by
    rw [hcardT]; exact card_soGroup5_le
  exact ⟨MulEquiv.ofBijective ψ (ψ.bijective_of_simple_normal T hC hT hφ hcard)⟩

noncomputable def statedProjStatedSpEquivZModFive {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 5) : StatedProj (StatedSp 2 K) ≃* StatedProj (StatedSp 2 (ZMod 5)) :=
  haveI := Fintype.ofFinite K
  let φ : K ≃+* ZMod 5 :=
    (ZMod.ringEquivOfPrime K Nat.prime_five (by rw [← Nat.card_eq_fintype_card, hK])).symm
  CFSG.Adapters.RankTwoModelTransports.statedProjCongr
    (CFSG.Adapters.RankTwoModelTransports.glCongr φ)
    (CFSG.Adapters.RankTwoModelTransports.glCongr_statedSp φ 2)
    (CFSG.Adapters.RankTwoModelTransports.glCongr_statedScalars φ)

theorem ne_top_of_two_pow_seven_dvd {X : Type} [Group X] (T : Subgroup X) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = 5) (e : T ≃* StatedProj (StatedSp 2 K))
    (hX : 2 ^ 7 ∣ Nat.card X) : T ≠ ⊤ := by
  rintro rfl
  have h : Nat.card X = 4680000 := by
    rw [← Subgroup.card_top (G := X), Nat.card_congr e.toEquiv,
      Nat.card_congr (statedProjStatedSpEquivZModFive hK).toEquiv,
      natCard_statedProj_statedSp_zmod_five]
  rw [h] at hX
  norm_num at hX

theorem nonempty_mulEquiv_pgsp45_of_card_five {X : Type} [Group X] [Finite X] (T : Subgroup X)
    [T.Normal] {K : Type} [Field K] [Finite K] (hK : Nat.card K = 5)
    (e : T ≃* StatedProj (StatedSp 2 K)) (hC : Subgroup.centralizer (T : Set X) = ⊥)
    (hT : T ≠ ⊤) : Nonempty (X ≃* PGSp45) :=
  nonempty_mulEquiv_pgsp45_of_zmod_five T (e.trans (statedProjStatedSpEquivZModFive hK)) hC hT

theorem nonempty_mulEquiv_pgsp45_of_statedClassicalModel {X : Type} [Group X] [Finite X]
    (T : Subgroup X) [T.Normal] {p f : ℕ} (hq : p ^ f = 5)
    (hM : StatedClassicalModel T .PSp 2 p f) (hC : Subgroup.centralizer (T : Set X) = ⊥)
    (hT : T ≠ ⊤) : Nonempty (X ≃* PGSp45) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hM
  exact nonempty_mulEquiv_pgsp45_of_card_five T (by rw [hK, hq]) e hC hT

end CFSG.EvenSporadicStandard.TwoHS.GH312
