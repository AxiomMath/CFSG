module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.U48Row50
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBetaZ

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.U48

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB TauCeti
open CFSG.LocalAnalysis.GLTheoremA.CatB
open CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.RankThree.PartTwo.KFacts.KS21.U58 (K card_K ω3 orderOf_ω3 ω3_pow)
open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits

theorem center_su_three_eight_ne_bot : Subgroup.center (Su K 2 3 3) ≠ ⊥ := by
  intro hbot
  set ζ : K := ((ω3 : Kˣ) : K) with hζ
  have hζ3 : ζ ^ 3 = 1 := by
    have := congrArg (fun u : Kˣ => (u : K)) ω3_pow
    simpa [hζ] using this
  have hζ1 : ζ ≠ 1 := by
    intro h
    have h1 : (ω3 : Kˣ) = 1 := Units.ext h
    have h2 := orderOf_ω3
    rw [h1] at h2
    simp at h2
  have hσ : unitaryInvolution K 2 3 ζ = ζ ^ 8 := by
    rw [unitaryInvolution_apply]
    norm_num
  have hdet : (Matrix.scalar (Fin 3) ζ).det = 1 := by
    simp [hζ3]
  have hunit : conjTr (unitaryInvolution K 2 3) (Matrix.scalar (Fin 3) ζ) * Matrix.scalar (Fin 3) ζ = 1 := by
    have h1 : conjTr (unitaryInvolution K 2 3) (Matrix.scalar (Fin 3) ζ) =
        Matrix.scalar (Fin 3) (unitaryInvolution K 2 3 ζ) := by
      unfold conjTr
      ext i j
      by_cases hij : i = j
      · subst hij; simp
      · simp [Matrix.scalar_apply, Matrix.diagonal_apply_ne, hij, Ne.symm hij]
    rw [h1, hσ, ← map_mul, ← pow_succ, show 8 + 1 = 3 * 3 by norm_num, pow_mul, hζ3, one_pow, map_one]
  let z : Su K 2 3 3 := ⟨Matrix.SpecialLinearGroup.toGL ⟨Matrix.scalar (Fin 3) ζ, hdet⟩, hdet, hunit⟩
  have hzm : suMat z = Matrix.scalar (Fin 3) ζ := rfl
  have hz : z ∈ Subgroup.center (Su K 2 3 3) := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply suMat_injective
    rw [suMat_mul, suMat_mul]
    show suMat g * suMat z = suMat z * suMat g
    rw [hzm]
    exact ((Matrix.scalar_commute ζ (fun r => Commute.all _ _) (suMat g)).eq).symm
  rw [hbot, Subgroup.mem_bot] at hz
  have h1 := congrArg suMat hz
  rw [hzm, suMat_one] at h1
  have h2 := congrFun (congrFun h1 0) 0
  simp at h2
  exact hζ1 h2

theorem center_pquot_ne_bot_of_su {G : Type} [Group G] {J : Subgroup G} (ε : PQuot 3 J ≃* Su K 2 3 3) :
    Subgroup.center (PQuot 3 J) ≠ ⊥ := by
  intro h
  apply center_su_three_eight_ne_bot
  rw [← CFSG.LieType.Universal.Unitary.map_center_mulEquiv ε, h, Subgroup.map_bot]

end CFSG.LocalAnalysis.GLTheoremA.CatB.U48

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA.CatB
open CFSG.LocalAnalysis.GLTheoremA.CatB.U48
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU48 (SU4 μ3)

section Row


theorem u48Cent3Centre_holds (G : Type) [Group G] [Finite G] (X L : Subgroup G) (y : G)
    (hL : GLAPComponent 3 X L) (hcat : catalogIs (PSimple 3 L) S9.isU4eight) (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1)
    (hyc : IsCentralIn 3 y L) :
    Subgroup.center (PQuot 3 (GLAPLayer 3 (L ⊓ Subgroup.centralizer ({y} : Set G)))) ≠ ⊥ := by
  have hZ := center_pquot_eq_bot_of_u48 hL hcat
  let e := pqModelP hZ hcat
  have hφs : Function.Surjective (piOf L e) := piOf_surjective L e
  obtain ⟨g, t, ht, hgt⟩ := exists_conj_of_central (piOf L e) hφs (not_three_dvd_card_ker_piOf e)
    hy3 hy1 hyc
  let φ' : ↥L →* SU4 := (MulAut.conj g).toMonoidHom.comp (piOf L e)
  have hφ's : Function.Surjective φ' := (MulAut.conj g).surjective.comp hφs
  have hker' : ¬ 3 ∣ Nat.card φ'.ker := by
    have : φ'.ker = (piOf L e).ker :=
      MonoidHom.ker_comp_of_injective _ _ (MulAut.conj g).injective
    rw [this]
    exact not_three_dvd_card_ker_piOf e
  have hφ'y : φ' ⟨y, hyc.1⟩ = yStd t := hgt
  obtain ⟨J, hJ, hJl, -, ⟨ε⟩⟩ := layerY φ' hφ's hker' ht hyc.1 hy3 hφ'y
  subst hJl
  exact center_pquot_ne_bot_of_su ε

theorem u48Cent3AtK_holds (G : Type) [Group G] [Finite G] : U48Cent3AtK G :=
  ⟨u48Cent3At_holds G, fun X L y hL hcat hy3 hy1 hyc => u48Cent3Centre_holds G X L y hL hcat hy3 hy1 hyc⟩

end Row

end CFSG.LocalAnalysis.GLTheoremA

end
