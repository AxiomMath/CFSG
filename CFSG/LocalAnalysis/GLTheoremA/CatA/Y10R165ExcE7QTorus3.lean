module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE7QTorus
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Lin10
public import CFSG.RankThree.Classical2.NegativeExchangedSL3

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE7Three

open Matrix CFSG.Open CFSG.RankThree.Classical2
open CFSG.LocalAnalysis.GLTheoremA.Y10F.LinEngine
open scoped MatrixGroups Pointwise

variable {K : Type} [Field K] [Finite K] [CharP K 2]
  {L : Type} [Field L] [Algebra K L]

private def f2BlockSL6 : Multiplicative (Fin 3 → ZMod 3) →* SL(6, K) :=
  (CFSG.RankThree.PartOne.KFCL.BlockSL.reindexSL
    (sixBlockEquiv 6 (by norm_num))).symm.toMonoidHom.comp
    (f2BlockHom (F := K) 0 :
      Multiplicative (Fin 3 → ZMod 3) →*
        Matrix.SpecialLinearGroup (Fin 2 ⊕ (Fin 2 ⊕ (Fin 2 ⊕ Fin 0))) K)

private theorem f2BlockSL6_injective : Function.Injective (f2BlockSL6 (K := K)) := by
  intro a b h
  change (CFSG.RankThree.PartOne.KFCL.BlockSL.reindexSL
      (sixBlockEquiv 6 (by norm_num))).symm
        (f2BlockHom (F := K) (m := 0) a) =
      (CFSG.RankThree.PartOne.KFCL.BlockSL.reindexSL
        (sixBlockEquiv 6 (by norm_num))).symm
        (f2BlockHom (F := K) (m := 0) b) at h
  exact @f2BlockHom_injective K _ _ 0 a b
    ((CFSG.RankThree.PartOne.KFCL.BlockSL.reindexSL
      (sixBlockEquiv 6 (by norm_num))).symm.injective h)

private theorem center_fixSubgroup_split_eq_bot {Φ' : SL(6, L) ≃* SL(6, L)} {H : SL(6, L)}
    (hfix : ∀ X : SL(6, L), X ∈ fixSubgroup Φ' ↔
      ∃ Y : SL(6, K), X = H * Matrix.SpecialLinearGroup.map (algebraMap K L) Y * H⁻¹)
    (hK2 : Nat.card K = 2) :
    Subgroup.center ↥(fixSubgroup Φ') = ⊥ := by
  classical
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  obtain ⟨Y, hY⟩ := (hfix x).1 x.2
  have hYc : Y ∈ Subgroup.center SL(6, K) := by
    rw [Subgroup.mem_center_iff]
    intro Z
    have hmem : H * Matrix.SpecialLinearGroup.map (algebraMap K L) Z * H⁻¹ ∈
        fixSubgroup Φ' := (hfix _).2 ⟨Z, rfl⟩
    have hcomm := (Subgroup.mem_center_iff.1 hx
      (⟨H * Matrix.SpecialLinearGroup.map (algebraMap K L) Z * H⁻¹, hmem⟩ :
        ↥(fixSubgroup Φ'))).symm
    have hcomm' : (x : SL(6, L)) *
        (H * Matrix.SpecialLinearGroup.map (algebraMap K L) Z * H⁻¹) =
        (H * Matrix.SpecialLinearGroup.map (algebraMap K L) Z * H⁻¹) * (x : SL(6, L)) :=
      congrArg Subtype.val hcomm
    rw [hY] at hcomm'
    have h2 := congrArg (fun t : SL(6, L) => H⁻¹ * t * H) hcomm'
    have h3 : Matrix.SpecialLinearGroup.map (algebraMap K L) (Y * Z) =
        Matrix.SpecialLinearGroup.map (algebraMap K L) (Z * Y) := by
      simpa [map_mul, mul_assoc] using h2
    have h4 := CFSG.RankThree.Classical2.specialLinearGroup_map_injective (n := 6)
      (RingHom.injective (algebraMap K L)) h3
    simpa [mul_comm] using h4.symm
  have hcard := CFSG.RankThree.Classical2.natCard_center_specialLinearGroup (K := K) (n := 6)
    (by norm_num)
  rw [hK2] at hcard
  have hcenter : Subgroup.center SL(6, K) = ⊥ := by
    rw [← Subgroup.card_eq_one, hcard]
    norm_num
  have hY1 : Y = 1 := by
    have : Y ∈ (⊥ : Subgroup SL(6, K)) := by rw [← hcenter]; exact hYc
    simpa using this
  refine Subtype.ext ?_
  rw [hY, hY1]
  simp

theorem exists_elemAbelian_pRank_three_of_fixSubgroup_split_f2
    {Φ' : SL(6, L) ≃* SL(6, L)} {H : SL(6, L)}
    (hfix : ∀ X : SL(6, L), X ∈ fixSubgroup Φ' ↔
      ∃ Y : SL(6, K), X = H * Matrix.SpecialLinearGroup.map (algebraMap K L) Y * H⁻¹)
    (hK2 : Nat.card K = 2)
    {J : Type*} [Group J] [Finite J] (ρ : ↥(fixSubgroup Φ') →* J)
    (hρ : Function.Surjective ρ)
    (hc : ∀ z ∈ ρ.ker, ∀ u : ↥(fixSubgroup Φ'), z * u = u * z)
    (hk : Nat.card ρ.ker ∣ 6) :
    ∃ F : Subgroup J, IsElemAbelian 3 F ∧ 3 ≤ CFSG.Open.pRank 3 F := by
  classical
  have hcenter := center_fixSubgroup_split_eq_bot hfix hK2
  have hker : ρ.ker = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hzc : z ∈ Subgroup.center ↥(fixSubgroup Φ') := by
      rw [Subgroup.mem_center_iff]
      intro u
      exact (hc z hz u).symm
    rw [hcenter] at hzc
    simpa using hzc
  have hρinj : Function.Injective ρ := (MonoidHom.ker_eq_bot_iff ρ).1 hker
  let φ : Multiplicative (Fin 3 → ZMod 3) →* ↥(fixSubgroup Φ') :=
    (splitModelHom hfix).comp (f2BlockSL6 (K := K))
  have hφ : Function.Injective φ :=
    (splitModelHom_injective hfix).comp (f2BlockSL6_injective (K := K))
  refine ⟨(ρ.comp φ).range, ?_, ?_⟩
  · rw [← Subgroup.map_top (ρ.comp φ)]
    refine CFSG.SectionRank.isElemAbelian_map (p := 3) ?_ (ρ.comp φ)
    refine ⟨⟨⟨fun a b => mul_comm' a b⟩⟩, fun x _ => ?_⟩
    exact pow_three_multiplicative_fin_three x
  · have hcard : Nat.card ↥((ρ.comp φ).range) = 3 ^ 3 := by
      rw [← Nat.card_congr (MonoidHom.ofInjective (fun a b h => hφ (hρinj h))).toEquiv]
      simp [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
    exact CFSG.SectionRank.le_pRank (p := 3) (by norm_num) le_rfl
      (by
        rw [← Subgroup.map_top (ρ.comp φ)]
        exact CFSG.SectionRank.isElemAbelian_map (p := 3)
          ⟨⟨⟨fun a b => mul_comm' a b⟩⟩, fun x _ => pow_three_multiplicative_fin_three x⟩
          (ρ.comp φ))
      hcard

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE7Three
