module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I2016U6Diag
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U4InnU6e

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.I2016U6

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Fischer CFSG.LocalAnalysis.GLTheoremA.LevelLieU6
  CFSG.LocalAnalysis.GLTheoremA.CatB.U4InnU6 CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LieType.BorelTits
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)
open scoped commutatorElement

theorem u6Key_holds : U6Key := by
  intro β hβ3 hβ1 H P T hHβ hA6 hPβ hPq hT0 hT2 hTβ hHT
  classical
  obtain ⟨B, hB, ⟨c, hBc⟩, hβB⟩ := LevelLieU6.exists_unitary_of_pow_three β hβ3
  have hns : ¬ ∃ c : F4ˣ, B = Matrix.GeneralLinearGroup.scalar (Fin 6) c := by
    rintro ⟨c₀, hc₀⟩
    apply hβ1
    ext x
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
    rw [MulAut.one_apply]
    refine hβB u u ?_
    rw [hc₀, ← (commute_scalar c₀ (u : GL (Fin 6) F4)).eq, mul_inv_cancel_right]
  by_cases hB3 : B ^ 3 = 1
  ·
    obtain ⟨Pm, d, hd⟩ := exists_diag6 ⟨B, hB⟩ (Subtype.ext hB3)
    obtain ⟨D, hDdef⟩ : ∃ D : GL (Fin 6) F4,
        D = ((Pm⁻¹ * ⟨B, hB⟩ * Pm : primeFormUnitary hF4 (idGram F4 6)) : GL (Fin 6) F4) :=
      ⟨_, rfl⟩
    have hDeq : D = (Pm : GL (Fin 6) F4)⁻¹ * B * (Pm : GL (Fin 6) F4) := by rw [hDdef]; rfl
    have hDu : D ∈ primeFormUnitary hF4 (idGram F4 6) := by
      rw [hDdef]
      exact Subtype.property _
    have hD : (D : Matrix (Fin 6) (Fin 6) F4) = Matrix.diagonal d := by rw [hDdef]; exact hd
    have hnc : ¬ ∀ i, d i = d 0 := by
      intro hconst
      apply hns
      have hd0 : d 0 ≠ 0 := d_ne_zero hD 0
      refine ⟨Units.mk0 (d 0) hd0, ?_⟩
      have hDs : D = Matrix.GeneralLinearGroup.scalar (Fin 6) (Units.mk0 (d 0) hd0) := by
        apply Units.ext
        rw [hD, Matrix.GeneralLinearGroup.coe_scalar]
        ext i j
        by_cases hij : i = j
        · subst hij
          simp [hconst i]
        · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
      have hB' : B = (Pm : GL (Fin 6) F4) * D * (Pm : GL (Fin 6) F4)⁻¹ := by
        rw [hDeq]
        group
      rw [hB', hDs, (commute_scalar (Units.mk0 (d 0) hd0) (Pm : GL (Fin 6) F4)).eq,
        mul_inv_cancel_right]
    let πD : M6 →* S6 := covM6.comp (conjM6 Pm).toMonoidHom
    have hπs : Function.Surjective πD := by
      intro y
      obtain ⟨u, hu⟩ := covM6_surjective y
      obtain ⟨v, hv⟩ := (conjM6 Pm).surjective u
      exact ⟨v, by show covM6 (conjM6 Pm v) = y; rw [hv, hu]⟩
    have hπk : ∀ z ∈ πD.ker, ∃ c : F4ˣ,
        (z : GL (Fin 6) F4) = Matrix.GeneralLinearGroup.scalar (Fin 6) c := by
      intro z hz
      have hz' : conjM6 Pm z ∈ covM6.ker := hz
      rw [covM6, QuotientGroup.ker_mk', Subgroup.mem_subgroupOf] at hz'
      obtain ⟨c', hc'⟩ := hz'
      refine ⟨c', ?_⟩
      have h1 : ((conjM6 Pm z : M6) : GL (Fin 6) F4) =
          (Pm : GL (Fin 6) F4) * z * (Pm : GL (Fin 6) F4)⁻¹ := rfl
      have h2 : (z : GL (Fin 6) F4) = (Pm : GL (Fin 6) F4)⁻¹ *
          ((Pm : GL (Fin 6) F4) * z * (Pm : GL (Fin 6) F4)⁻¹) * (Pm : GL (Fin 6) F4) := by
        group
      rw [h2, ← h1, ← hc', mul_assoc, ← (commute_scalar c' (Pm : GL (Fin 6) F4)).eq,
        inv_mul_cancel_left]
    have hαβ : ∀ u : M6, πD (conjM6 ⟨D, hDu⟩ u) = β (πD u) := by
      intro u
      have hv : ((conjM6 Pm (conjM6 ⟨D, hDu⟩ u) : M6) : GL (Fin 6) F4) =
          B * ((conjM6 Pm u : M6) : GL (Fin 6) F4) * B⁻¹ := by
        show (Pm : GL (Fin 6) F4) * (D * (u : GL (Fin 6) F4) * D⁻¹) * (Pm : GL (Fin 6) F4)⁻¹ =
          B * ((Pm : GL (Fin 6) F4) * u * (Pm : GL (Fin 6) F4)⁻¹) * B⁻¹
        rw [hDeq]
        group
      exact (hβB (conjM6 Pm u) _ hv).symm
    exact u6KeyDiag hD hDu hnc πD hπs hπk β hαβ H P T hHβ hA6 hPβ hPq hT0 hT2 hTβ hHT
  ·
    exfalso
    have hc1 : c ≠ 1 := fun h => hB3 (by rw [hBc, h, map_one])
    obtain ⟨Tq, _, f, hf, hTs, hTc, hker⟩ := hPq
    haveI : IsSimpleGroup Tq := hTs
    haveI : Finite Tq := Nat.finite_of_card_ne_zero (by rw [hTc]; norm_num)
    haveI : Group.IsPerfect Tq := CatB.I1431YD4.isPerfect_of_simple (by rw [hTc]; norm_num)
    have hαβB : ∀ k : M6, covM6 (conjM6 ⟨B, hB⟩ k) = β (covM6 k) :=
      fun k => (hβB k (conjM6 ⟨B, hB⟩ k) rfl).symm
    obtain ⟨LP, hLPperf, hLPfix, hLPP, hLPs⟩ :=
      exists_perfect_lift covM6_surjective covM6_ker_le_center hαβB P hPβ f hf
    have hLPC : LP ≤ CenD B := by
      rw [← u4Fix_conjM6 ⟨B, hB⟩]
      exact hLPfix
    have hdvdLP : 25920 ∣ Nat.card LP := by
      let φP : ↥LP →* Tq := f.comp ((covM6.comp LP.subtype).codRestrict P (fun x => hLPP x.1 x.2))
      have hφP : Function.Surjective φP := by
        intro t
        obtain ⟨x, hx, h, hxf⟩ := hLPs t
        exact ⟨⟨x, hx⟩, hxf⟩
      have := Subgroup.card_dvd_of_surjective hφP
      rwa [hTc] at this
    have h504 := perfect_card_nine ⟨B, hB⟩ hc1 hBc hLPC (Subgroup.isPerfect_iff.2 hLPperf)
    have := hdvdLP.trans h504
    norm_num at this

end CFSG.LocalAnalysis.GLTheoremA.CatB.I2016U6

namespace CFSG.LocalAnalysis.GLTheoremA.I2016

theorem i2016FactU6_holds : I2016FactU6 :=
  CatB.I2016U6.i2016FactU6_of_key CatB.I2016U6.u6Key_holds

end CFSG.LocalAnalysis.GLTheoremA.I2016

end
