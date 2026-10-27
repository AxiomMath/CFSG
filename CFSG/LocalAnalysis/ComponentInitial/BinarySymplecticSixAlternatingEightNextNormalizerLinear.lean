module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixAlternatingEightCharacteristic
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymmetricThreeLinear

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.AlternatingEight

open Subgroup Matrix FusionOrbits
open scoped Pointwise

theorem natCard_vecThree : Nat.card (Fin 3 → ZMod 2) = 8 := by
  rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  rfl

theorem le_four_of_dvd_eight {c : ℕ} (h : c ∣ 8) (hne : c ≠ 8) : c ≤ 4 := by
  have key : ∀ c, c ≤ 8 → c ∣ 8 → c ≠ 8 → c ≤ 4 := by decide
  exact key c (Nat.le_of_dvd (by norm_num) h) h hne

theorem mat_eq_one_of_forall_mulVec {M : Matrix (Fin 3) (Fin 3) (ZMod 2)}
    (h : ∀ v : Fin 3 → ZMod 2, M *ᵥ v = v) : M = 1 := by
  rw [← Matrix.toLin'.injective.eq_iff]
  refine LinearMap.ext fun v => ?_
  rw [Matrix.toLin'_apply, h, Matrix.toLin'_one, LinearMap.id_apply]

@[expose] def fixVec (D : GL (Fin 3) (ZMod 2)) : AddSubgroup (Fin 3 → ZMod 2) :=
  (LinearMap.eqLocus (Matrix.mulVecLin (D : Matrix (Fin 3) (Fin 3) (ZMod 2)))
    LinearMap.id).toAddSubgroup

theorem mem_fixVec {D : GL (Fin 3) (ZMod 2)} {v : Fin 3 → ZMod 2} :
    v ∈ fixVec D ↔ (D : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v = v :=
  Iff.rfl

theorem card_fixVec_le {D : GL (Fin 3) (ZMod 2)} (hD : D ≠ 1) : Nat.card (fixVec D) ≤ 4 := by
  have hdvd : Nat.card (fixVec D) ∣ 8 := by
    have h := AddSubgroup.card_addSubgroup_dvd_card (fixVec D)
    rwa [natCard_vecThree] at h
  refine le_four_of_dvd_eight hdvd fun h8 =>
    hD (Units.ext (mat_eq_one_of_forall_mulVec fun v => ?_))
  have htop : fixVec D = ⊤ := AddSubgroup.eq_top_of_card_eq _ (by rw [h8, natCard_vecThree])
  have hv : v ∈ fixVec D := htop ▸ AddSubgroup.mem_top v
  exact hv

@[expose] def fixSym (D : GL (Fin 3) (ZMod 2)) : AddSubgroup (binarySymMatrices 3) :=
  (LinearMap.eqLocus (symThreeCongrHom D).toLinearMap LinearMap.id).toAddSubgroup

theorem mem_fixSym {D : GL (Fin 3) (ZMod 2)} {B : binarySymMatrices 3} :
    B ∈ fixSym D ↔ symThreeCongr D B = B :=
  Iff.rfl

theorem altLabel_mem_altSym (v : Fin 3 → ZMod 2) :
    DegreeEight.altLabel v ∈ BinarySymThreeOrbit.altSym := by
  rw [BinarySymThreeOrbit.mem_altSym_iff]
  funext i
  fin_cases i <;> rfl

theorem natCard_altSym : Nat.card BinarySymThreeOrbit.altSym = 8 := by
  have e : (Fin 3 → ZMod 2) ≃ BinarySymThreeOrbit.altSym :=
    Equiv.ofBijective (fun v => ⟨DegreeEight.altLabel v, altLabel_mem_altSym v⟩)
      ⟨fun v w h => DegreeEight.altLabel_injective (congrArg Subtype.val h), fun B =>
        ⟨symThreeOff ((B : binarySymMatrices 3) : Matrix (Fin 3) (Fin 3) (ZMod 2)),
          Subtype.ext (eq_altLabel_of_diag_eq_zero
            (BinarySymThreeOrbit.mem_altSym_iff.1 B.2)).symm⟩⟩
  rw [← Nat.card_congr e, natCard_vecThree]

theorem card_fixAlt_le {D : GL (Fin 3) (ZMod 2)} (hD : D ≠ 1) :
    Nat.card (fixSym D ⊓ BinarySymThreeOrbit.altSym : AddSubgroup (binarySymMatrices 3)) ≤ 4 := by
  have hle : fixSym D ⊓ BinarySymThreeOrbit.altSym ≤ BinarySymThreeOrbit.altSym := inf_le_right
  have hdvd : Nat.card (fixSym D ⊓ BinarySymThreeOrbit.altSym :
      AddSubgroup (binarySymMatrices 3)) ∣ 8 := by
    rw [← natCard_altSym]
    exact AddSubgroup.card_dvd_of_le hle
  refine le_four_of_dvd_eight hdvd fun h8 => hD ?_
  have heq : fixSym D ⊓ BinarySymThreeOrbit.altSym = BinarySymThreeOrbit.altSym :=
    AddSubgroup.eq_of_le_of_card_ge hle (by rw [h8, natCard_altSym])
  have hfix : ∀ v : Fin 3 → ZMod 2,
      ((D⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ *ᵥ v = v := by
    intro v
    have h : DegreeEight.altLabel v ∈ fixSym D ⊓ BinarySymThreeOrbit.altSym := by
      rw [heq]
      exact altLabel_mem_altSym v
    have h2 := mem_fixSym.1 (AddSubgroup.mem_inf.1 h).1
    rw [DegreeEight.symThreeCongr_altLabel] at h2
    exact DegreeEight.altLabel_injective h2
  have h1 := mat_eq_one_of_forall_mulVec hfix
  have h2 : ((D⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 1 := by
    rw [← Matrix.transpose_transpose ((D⁻¹ : GL (Fin 3) (ZMod 2)) :
      Matrix (Fin 3) (Fin 3) (ZMod 2)), h1, Matrix.transpose_one]
  exact inv_eq_one.1 (Units.ext h2)

theorem card_fixSym_le {D : GL (Fin 3) (ZMod 2)} (hD : D ≠ 1) : Nat.card (fixSym D) ≤ 16 := by
  set δ : fixSym D →+ (Fin 3 → ZMod 2) :=
    symThreeDiagLin.toAddMonoidHom.comp (fixSym D).subtype with hδ
  have h1 := δ.ker.card_mul_index
  rw [AddSubgroup.index_ker] at h1
  have hrange : Nat.card δ.range ≤ 4 := by
    refine le_trans (AddSubgroup.card_le_of_le ?_) (card_fixVec_le hD)
    rintro _ ⟨B, rfl⟩
    rw [mem_fixVec]
    change (D : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ symThreeDiag ((B : binarySymMatrices 3) :
      Matrix (Fin 3) (Fin 3) (ZMod 2)) = symThreeDiag ((B : binarySymMatrices 3) :
        Matrix (Fin 3) (Fin 3) (ZMod 2))
    rw [← symThreeDiag_coe_congr, mem_fixSym.1 B.2]
  have hker : Nat.card δ.ker ≤ 4 := by
    refine le_trans (Nat.card_le_card_of_injective (fun k : δ.ker =>
      (⟨(k : fixSym D), AddSubgroup.mem_inf.2 ⟨(k : fixSym D).2,
        BinarySymThreeOrbit.mem_altSym_iff.2 k.2⟩⟩ :
          (fixSym D ⊓ BinarySymThreeOrbit.altSym : AddSubgroup (binarySymMatrices 3))))
      fun k k' h => ?_) (card_fixAlt_le hD)
    have h1 := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext h1)
  rw [← h1]
  calc Nat.card δ.ker * Nat.card δ.range ≤ 4 * 4 := Nat.mul_le_mul hker hrange
    _ = 16 := rfl

@[expose] def unipotentFour : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 1, 0; 0, 1, 1; 0, 0, 1]

theorem unipotentFour_det : unipotentFour.det = 1 := by
  decide +kernel

theorem unipotentFour_sq : unipotentFour * unipotentFour ≠ 1 := by
  decide +kernel

theorem unipotentFour_four :
    unipotentFour * unipotentFour * (unipotentFour * unipotentFour) = 1 := by
  decide +kernel

theorem card_le_four_of_mul_self (U : Subgroup (GL (Fin 3) (ZMod 2)))
    (hU : ∀ x ∈ U, x * x = 1) : Nat.card U ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : ∀ (P : Subgroup (GL (Fin 3) (ZMod 2))), IsPGroup 2 P → Nat.card P ≤ 8 := by
    intro P hP
    obtain ⟨n, hn⟩ := hP.exists_card_eq
    have hdvd : 2 ^ n ∣ 168 := by
      rw [← hn, ← card_GL_three_two]
      exact Subgroup.card_subgroup_dvd_card P
    have hn3 : n ≤ 3 := by
      by_contra h
      have h16 : 2 ^ 4 ∣ 168 := (Nat.pow_dvd_pow 2 (by omega)).trans hdvd
      norm_num at h16
    rw [hn]
    calc 2 ^ n ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hn3
      _ = 8 := rfl
  have hU2 : IsPGroup 2 U := fun x => ⟨1, by
    rw [pow_one, sq]
    exact Subtype.ext (hU x x.2)⟩
  obtain ⟨n, hn⟩ := hU2.exists_card_eq
  by_contra hlt
  have hcard : Nat.card U = 8 := by
    have h8 := hp U hU2
    rw [hn] at h8 hlt ⊢
    have hn3 : n ≤ 3 := by
      by_contra h
      have : 2 ^ 4 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    interval_cases n <;> simp_all
  obtain ⟨P, hP⟩ := hU2.exists_le_sylow
  have hPU : (P : Subgroup (GL (Fin 3) (ZMod 2))) = U :=
    (Subgroup.eq_of_le_of_card_ge hP (by rw [hcard]; exact hp P P.isPGroup')).symm
  set w := glOfDet unipotentFour unipotentFour_det with hw
  have hw2 : w * w ≠ 1 := fun h => unipotentFour_sq (by
    have h1 := congrArg (fun x : GL (Fin 3) (ZMod 2) => (x : Matrix (Fin 3) (Fin 3) (ZMod 2))) h
    simpa [hw, coe_glOfDet] using h1)
  have hw4 : w ^ 2 ^ 2 = 1 := by
    apply Units.ext
    rw [show (2 : ℕ) ^ 2 = 4 from rfl, Units.val_pow_eq_pow_val, Units.val_one, hw, coe_glOfDet,
      show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq]
    exact unipotentFour_four
  have hW : IsPGroup 2 (zpowers w) := by
    refine IsPGroup.of_card (n := 2) ?_
    rw [Nat.card_zpowers]
    refine orderOf_eq_prime_pow (n := 1) ?_ hw4
    rw [pow_one, sq]
    exact hw2
  obtain ⟨Q, hQ⟩ := hW.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (GL (Fin 3) (ZMod 2)) P Q
  have hwQ : w ∈ (Q : Subgroup (GL (Fin 3) (ZMod 2))) := hQ (mem_zpowers w)
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    ← map_inv, MulAut.smul_def, MulAut.conj_apply, inv_inv, hPU] at hwQ
  have h := hU _ hwQ
  apply hw2
  calc w * w = g * ((g⁻¹ * w * g) * (g⁻¹ * w * g)) * g⁻¹ := by group
    _ = 1 := by rw [h, mul_one, mul_inv_cancel]

theorem eq_bot_of_normal_isPGroup_two (N : Subgroup (GL (Fin 3) (ZMod 2))) (hN : N.Normal)
    (hN2 : IsPGroup 2 N) : N = ⊥ := by
  have := hN
  rcases isSimpleGroup_GL_three_two.eq_bot_or_eq_top_of_normal N with h | h
  · exact h
  · exfalso
    obtain ⟨n, hn⟩ := hN2.exists_card_eq
    rw [h, Subgroup.card_top, card_GL_three_two] at hn
    rcases le_or_gt n 7 with h7 | h8
    · have := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) h7
      omega
    · have := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (Nat.succ_le_of_lt h8)
      omega

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.AlternatingEight
