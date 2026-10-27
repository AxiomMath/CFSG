module

public import CFSG.ClassicalInvolution.Q3.TL4LinkLieDefs
public import CFSG.ClassicalInvolution.Q3.Q3MTM11
public import CFSG.ClassicalInvolution.ModelFacts.TG3F3
public import CFSG.GH74.GLS.LU.StdPairLin
public import CFSG.ClassicalInvolution.Asc77.AscT8X4
public import CFSG.ClassicalInvolution.Asc77.AscT8YA3
public import CFSG.ClassicalInvolution.AschTight.S1916F2a
public import CFSG.ClassicalInvolution.AschTight.S19BCSW
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.InnerOvergroup
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Reduction
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm1RTwin
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm7RCore
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPair
public import CFSG.ClassicalInvolution.Q3.Q3AMDBStmt
public import CFSG.ClassicalInvolution.Q3.Q3MTKind
public import CFSG.ClassicalInvolution.Q3.Q3T6BSymEx
public import CFSG.ClassicalInvolution.Q3.Q3T6DCfg
public import CFSG.ClassicalInvolution.Q3.Q3T6DPart1
public import CFSG.ClassicalInvolution.Q3.Q3T6OpenSDEnd
public import CFSG.ClassicalInvolution.Q3.Q3T8B10
public import CFSG.ClassicalInvolution.Q3.Q3T8P26T01
public import CFSG.ClassicalInvolution.Q3.Q3T8P26T02
public import CFSG.ClassicalInvolution.Q3.Q3T8P26TH01
public import CFSG.ClassicalInvolution.Q3.Q3TIYOAMain
public import CFSG.ClassicalInvolution.Q3.TL3S8Gold
public import CFSG.ClassicalInvolution.Q3.TL3S8Sd
public import CFSG.ClassicalInvolution.Q3.TL4Conn274M
public import CFSG.ClassicalInvolution.Q3.TL4Conn278ANMu
public import CFSG.ClassicalInvolution.Q3.TL4LinkCases
public import CFSG.ClassicalInvolution.Q3.TL4OddConv
public import CFSG.ClassicalInvolution.Q3.TL4OddFrThird
public import CFSG.ClassicalInvolution.Q3.TL4OddMu4
public import CFSG.ClassicalInvolution.Q3.TL4SecIdLeaves
public import CFSG.ClassicalInvolution.Q3.TL4SepSub
public import CFSG.ClassicalInvolution.Q3.TL4VtxFree
public import CFSG.ClassicalInvolution.SmallCases.NobqFinal
public import CFSG.Foundations
public import CFSG.Goldschmidt.Steps.G310Core2
public import CFSG.Goldschmidt.Steps.G37Core
public import CFSG.Goldschmidt75.TheoremB
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingCore
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingEscape
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingInherit
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingOddQuotient
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingThreeOne
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3WeakClosure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
public import CFSG.Permutation.BurnsideSchur
public import CFSG.Timmesfeld.Moufang.Three

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped MatrixGroups Matrix

local notation "𝔽₃" => GaloisField 3 1

section Group

@[expose] def NoC4C2 (X : Type) [Group X] : Prop :=
  ∀ u z : X, u ^ 4 = 1 → u ^ 2 ≠ 1 → z * z = 1 → z ≠ 1 → z * u = u * z → z = u ^ 2

theorem NoC4C2.of_bijective {G H : Type} [Group G] [Group H] (h : NoC4C2 G) (ψ : G →* H)
    (hψ : Function.Bijective ψ) : NoC4C2 H := by
  intro u z hu4 hu2 hz2 hz1 hc
  obtain ⟨u', rfl⟩ := hψ.2 u
  obtain ⟨z', rfl⟩ := hψ.2 z
  have e := h u' z' (hψ.1 (by rw [map_pow, hu4, map_one]))
    (fun h' => hu2 (by rw [← map_pow, h', map_one])) (hψ.1 (by rw [map_mul, hz2, map_one]))
    (fun h' => hz1 (by rw [h', map_one])) (hψ.1 (by rw [map_mul, map_mul, hc]))
  rw [e, map_pow]

variable {X : Type} [Group X] {Φ : Set (Subgroup X)}

theorem omegaStarNbr_eq_empty_of_noC4C2 (hR : TypeRFam 3 Φ) (hno : NoC4C2 X) {L : Subgroup X}
    (hL : L ∈ Φ) : omegaStarNbr Φ L = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun J hJ => ?_
  obtain ⟨hJΦ, hJL, U, ⟨Rs, hRs, hURs, hcyc, hidx⟩, hUJ, hUN⟩ := hJ
  obtain ⟨M, hM, hRsM⟩ := exists_isSylow2In_of_mem_RSet hRs
  obtain ⟨e⟩ := hR.quat M hM Rs hRsM
  have hcard8 : Nat.card Rs = 8 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    norm_num
  have hcardU : Nat.card U = 4 := by
    have h1 := Subgroup.relIndex_mul_card (H := U) (K := Rs)
    rw [inf_of_le_left hURs, hidx, hcard8] at h1
    omega
  obtain ⟨u, hu⟩ := IsCyclic.exists_generator (α := ↥U)
  have hou : orderOf (u : X) = 4 := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hu, hcardU]
  have hu4 : (u : X) ^ 4 = 1 := by rw [← hou]; exact pow_orderOf_eq_one _
  have hu2 : (u : X) ^ 2 ≠ 1 := fun h => by
    have := orderOf_dvd_of_pow_eq_one h
    rw [hou] at this
    omega
  obtain ⟨⟨zL, hzL⟩, -⟩ := hR.hyp.omega1 L hL
  obtain ⟨⟨zJ, hzJ⟩, -⟩ := hR.hyp.omega1 J hJΦ
  have hcz : zL * u = u * zL := by
    have h1 := hzL.conj (u : X)
    rw [conjSub_eq_of_mem_normalizer (hUN u.2)] at h1
    have h2 := hzL.eq h1
    calc zL * (u : X) = (u : X) * zL * (u : X)⁻¹ * (u : X) := by rw [← h2]
      _ = (u : X) * zL := by group
  have hzLu := hno u zL hu4 hu2 hzL.sq hzL.ne_one hcz
  have hu2J : (u : X) ^ 2 = zJ := by
    have hmem : (u : X) ^ 2 ∈ J := J.pow_mem (hUJ u.2) 2
    have hsq : (u : X) ^ 2 * (u : X) ^ 2 = 1 := by rw [← pow_add]; exact hu4
    exact (hzJ.unique _ hmem hsq).resolve_left hu2
  apply hJL
  refine hR.noTwins L hL J ⟨hJΦ, zL, hzL, ?_⟩
  rw [hzLu, hu2J]
  exact hzJ

end Group

section SL3

open CFSG.GH74.GLS.LU in
theorem sl3_noC4C2 : NoC4C2 SL(3, 𝔽₃) := by
  intro u z hu4 hu2 hz2 hz1 hcomm
  have h2 := ModelFacts.TG3.two_ne_zero_three
  have hw2 : u ^ 2 * u ^ 2 = 1 := by rw [← pow_add]; exact hu4
  have hZZ : (z : Matrix (Fin 3) (Fin 3) 𝔽₃) * z = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, hz2, Matrix.SpecialLinearGroup.coe_one]
  have hWW : ((u ^ 2 : SL(3, 𝔽₃)) : Matrix (Fin 3) (Fin 3) 𝔽₃) * (u ^ 2 : SL(3, 𝔽₃)) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, hw2, Matrix.SpecialLinearGroup.coe_one]
  have hW : ((u ^ 2 : SL(3, 𝔽₃)) : Matrix (Fin 3) (Fin 3) 𝔽₃) =
      (u : Matrix (Fin 3) (Fin 3) 𝔽₃) * u := by
    rw [pow_two, Matrix.SpecialLinearGroup.coe_mul]
  have hUZ : (u : Matrix (Fin 3) (Fin 3) 𝔽₃) * z = (z : Matrix (Fin 3) (Fin 3) 𝔽₃) * u := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, hcomm]
  have hWZ : ((u ^ 2 : SL(3, 𝔽₃)) : Matrix (Fin 3) (Fin 3) 𝔽₃) * z =
      (z : Matrix (Fin 3) (Fin 3) 𝔽₃) * (u ^ 2 : SL(3, 𝔽₃)) := by
    rw [hW, Matrix.mul_assoc, hUZ, ← Matrix.mul_assoc, hUZ, Matrix.mul_assoc]
  have hdz := finrank_eigSpace_neg_one_eq_two h2 hz2 hz1
  have hdz1 := finrank_eigSpace_one_of_finrank_neg_one h2 hZZ hdz
  have hdw := finrank_eigSpace_neg_one_eq_two h2 hw2 hu2
  have hdw1 := finrank_eigSpace_one_of_finrank_neg_one h2 hWW hdw
  obtain ⟨v₀, hv₀, hv₀0, hspan⟩ := exists_smul_of_mem_line hdz1
  obtain ⟨a, ha⟩ := hspan _ (mulVec_mem_eigSpace_of_commute hUZ hv₀)
  have ha2 : a * a = 1 := by
    rcases ModelFacts.TG3.eq_zero_or_one_or_neg_one_three a with h | h | h
    · exfalso
      apply hv₀0
      have h0 : (u : Matrix (Fin 3) (Fin 3) 𝔽₃) *ᵥ v₀ = 0 := by rw [ha, h, zero_smul]
      have h3 : v₀ = ((u⁻¹ : SL(3, 𝔽₃)) : Matrix (Fin 3) (Fin 3) 𝔽₃) *ᵥ
          ((u : Matrix (Fin 3) (Fin 3) 𝔽₃) *ᵥ v₀) := by
        rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
          Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
      rw [h3, h0, Matrix.mulVec_zero]
    · rw [h, one_mul]
    · rw [h]
      ring
  have hle : Models.eigSpace (z : Matrix (Fin 3) (Fin 3) 𝔽₃) 1 ≤
      Models.eigSpace ((u ^ 2 : SL(3, 𝔽₃)) : Matrix (Fin 3) (Fin 3) 𝔽₃) 1 := by
    intro v hv
    obtain ⟨c, rfl⟩ := hspan v hv
    rw [Models.mem_eigSpace_one, Matrix.mulVec_smul, hW, ← Matrix.mulVec_mulVec, ha,
      Matrix.mulVec_smul, ha, smul_smul, smul_smul, mul_assoc, ha2, mul_one]
  have heq := Submodule.eq_of_le_of_finrank_eq hle (by rw [hdz1, hdw1])
  have hle' : Models.eigSpace (z : Matrix (Fin 3) (Fin 3) 𝔽₃) (-1) ≤
      Models.eigSpace ((u ^ 2 : SL(3, 𝔽₃)) : Matrix (Fin 3) (Fin 3) 𝔽₃) (-1) := by
    intro v hv
    have hsum : v + ((u ^ 2 : SL(3, 𝔽₃)) : Matrix (Fin 3) (Fin 3) 𝔽₃) *ᵥ v ∈
        Models.eigSpace (z : Matrix (Fin 3) (Fin 3) 𝔽₃) (-1) :=
      Submodule.add_mem _ hv (mulVec_mem_eigSpace_of_commute hWZ hv)
    have hsumW : v + ((u ^ 2 : SL(3, 𝔽₃)) : Matrix (Fin 3) (Fin 3) 𝔽₃) *ᵥ v ∈
        Models.eigSpace (z : Matrix (Fin 3) (Fin 3) 𝔽₃) 1 := by
      rw [heq, Models.mem_eigSpace_one, Matrix.mulVec_add, Matrix.mulVec_mulVec, hWW,
        Matrix.one_mulVec, add_comm]
    have h0 := Submodule.disjoint_def.mp (Models.isCompl_eigSpace h2 hZZ).disjoint _ hsum hsumW
    rw [Models.mem_eigSpace_neg_one]
    exact eq_neg_of_add_eq_zero_right h0
  refine (Subtype.ext (Matrix.ext_iff_mulVec.mpr fun v => ?_)).symm
  have hv : v ∈ Models.eigSpace (z : Matrix (Fin 3) (Fin 3) 𝔽₃) (-1) ⊔
      Models.eigSpace (z : Matrix (Fin 3) (Fin 3) 𝔽₃) 1 := by
    rw [(Models.isCompl_eigSpace h2 hZZ).sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := Submodule.mem_sup.mp hv
  rw [Matrix.mulVec_add, Matrix.mulVec_add, Models.mem_eigSpace_neg_one.mp (hle' hv₁),
    Models.mem_eigSpace_neg_one.mp hv₁, Models.mem_eigSpace_one.mp (hle hv₂),
    Models.mem_eigSpace_one.mp hv₂]

theorem center_sl3_eq_bot : Subgroup.center SL(3, 𝔽₃) = ⊥ := by
  rw [eq_bot_iff]
  intro c hc
  obtain ⟨r, hr, hrc⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
  rw [Fintype.card_fin] at hr
  rw [Subgroup.mem_bot]
  rcases ModelFacts.TG3.eq_zero_or_one_or_neg_one_three r with h | h | h
  · rw [h] at hr
    norm_num at hr
  · apply Subtype.ext
    rw [← hrc, h, map_one, Matrix.SpecialLinearGroup.coe_one]
  · exfalso
    rw [h] at hr
    have h1 : (2 : 𝔽₃) = 0 := by linear_combination -hr
    exact ModelFacts.TG3.two_ne_zero_three h1

end SL3

section Cit3


theorem lieKindZ2NoStar_proved : LieKindZ2NoStar := by
  intro X _ _ Φ c hc hsec hshape L hL
  obtain ⟨hR, -, -, -⟩ := hsec
  obtain ⟨ψ, hψ, hker, -⟩ := hshape
  refine omegaStarNbr_eq_empty_of_noC4C2 hR ?_ hL
  rcases hc with rfl | rfl
  · have hinj : Function.Injective ψ := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      exact hker.trans (le_of_eq center_sl3_eq_bot)
    exact sl3_noC4C2.of_bijective ψ ⟨hinj, hψ⟩
  · have hinj : Function.Injective ψ := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      exact hker.trans (le_of_eq Q3W.center_m11_eq_bot)
    exact NoC4C2.of_bijective (fun _ _ hu4 hu2 hz2 hz1 hc => Q3MT.m11_no_c4_c2 hu4 hu2 hz2 hz1 hc)
      ψ ⟨hinj, hψ⟩

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
