module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E8FiveTwoDich

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSE8Five

namespace Two

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KE
  CFSG.RankThree.Lattice CFSG.RankThree.E6
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Foote.Coordinator.SplitFrame
  CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest4Griess
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest4Twist
  CFSG.HardMathSupport.Timmesfeld.Steinberg
open scoped MatrixGroups

set_option linter.unusedSectionVars false

section ConjX

variable {L : Type} [Field L]

theorem modEq_of_zpow_eq {u : Lˣ} (hu : IsPrimitiveRoot u 5) {n m : ℤ} (h : u ^ n = u ^ m) :
    n % 5 = m % 5 := by
  have h1 : u ^ (n - m) = 1 := by rw [_root_.zpow_sub, h, mul_inv_cancel]
  have h2 := (hu.zpow_eq_one_iff_dvd _).1 h1
  omega

theorem xExpA_inj : ∀ i j : Fin 5, xExpA i % 5 = xExpA j % 5 → i = j := by decide +kernel

theorem xExpB_inj : ∀ i j : Fin 5, xExpB i % 5 = xExpB j % 5 → i = j := by decide +kernel

theorem eq_pow_mul_of_actsBy {ζ : L} (hζ : IsPrimitiveRoot ζ 5) {g x : ModGL Tag.E8 L}
    (hg : g ∈ torusGroup Tag.E8 L) (hx : x ∈ torusGroup Tag.E8 L) {MA MB : GL (Fin 5) L}
    (hgA : ActsBy (rhoSigmaE8A4 L e8VA) g MA) (hxA : ActsBy (rhoSigmaE8A4 L e8VA) x MA)
    (hgB : ActsBy (rhoSigmaE8A4 L e8VB) g MB) (hxB : ActsBy (rhoSigmaE8A4 L e8VB) x MB) :
    ∃ m : ℕ, g = griessZ hζ ^ m * x := by
  have ht : g * x⁻¹ ∈ torusGroup Tag.E8 L := mul_mem hg (inv_mem hx)
  obtain ⟨b, hb⟩ :=
    CFSG.LieType.SeitzGeneration.ExcHighThree.exists_rootDiagUnit_of_mem_torusGroup ht
  have hA : ActsBy (rhoSigmaE8A4 L e8VA) (g * x⁻¹) 1 := by
    have := hgA.mul hxA.inv'
    rwa [mul_inv_cancel] at this
  have hB : ActsBy (rhoSigmaE8A4 L e8VB) (g * x⁻¹) 1 := by
    have := hgB.mul hxB.inv'
    rwa [mul_inv_cancel] at this
  obtain ⟨j, hj⟩ := eq_pow_z_of_trivial_action hζ (b := b)
    (fun X => by
      rw [hb]
      have := hA X
      rwa [conjSLn_one'] at this)
    (fun X => by
      rw [hb]
      have := hB X
      rwa [conjSLn_one'] at this)
  refine ⟨j, ?_⟩
  have h2 : g * x⁻¹ = griessZ hζ ^ j := hb.symm.trans hj
  rw [← h2]
  group

theorem exists_conj_x [IsAlgClosed L] {ζ : L} (hζ : IsPrimitiveRoot ζ 5)
    {Ye Ue Ye' Ue' : SL(5, L)}
    (hcomm : (rhoSigmaE8A4 L e8VA Ye * rhoSigmaE8A4 L e8VB Ue) *
        (rhoSigmaE8A4 L e8VA Ye' * rhoSigmaE8A4 L e8VB Ue') =
      (rhoSigmaE8A4 L e8VA Ye' * rhoSigmaE8A4 L e8VB Ue') *
        (rhoSigmaE8A4 L e8VA Ye * rhoSigmaE8A4 L e8VB Ue))
    (he'5 : (rhoSigmaE8A4 L e8VA Ye' * rhoSigmaE8A4 L e8VB Ue') ^ 5 = 1)
    (hnc : Ye * Ye' ≠ Ye' * Ye) :
    ∃ (ξ : ModGL Tag.E8 L) (m : ℕ), ξ ∈ mulSub L ∧
      ξ⁻¹ * (rhoSigmaE8A4 L e8VA Ye * rhoSigmaE8A4 L e8VB Ue) * ξ =
        griessZ hζ ^ m * griessX hζ := by
  obtain ⟨κ, κ', hκ, hκ', hκ5, hκ'5, hiff⟩ := pair_data hcomm
  have hκ1 : κ ≠ 1 := fun h1 => hnc (sl_comm_iff.2 (Tw.commute_of_one (h1 ▸ hκ)))
  have hκprim : IsPrimitiveRoot κ 5 := isPrimitiveRoot_five_of_ne_one hκ5 hκ1
  have hκ'prim : IsPrimitiveRoot κ' 5 :=
    isPrimitiveRoot_five_of_ne_one hκ'5 fun h => hκ1 (hiff.2 h)
  obtain ⟨cA, -, hcA⟩ := (pow_five_scalar he'5).1
  obtain ⟨cB, -, hcB⟩ := (pow_five_scalar he'5).2
  have hroot : ∀ n : ℤ, ((griessU hζ ^ n : Lˣ) : L) ^ 5 = 1 := fun n => by
    have h : (griessU hζ ^ n) ^ 5 = 1 := by
      rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast,
        (griessU_prim hζ).pow_eq_one, _root_.one_zpow]
    simpa using congrArg Units.val h
  obtain ⟨SA, hSA⟩ := exists_conj_diag_enum hκprim (sl_isUnit Ye) (sl_isUnit Ye') hκ hcA Ye.2
    (fun i => ((griessU hζ ^ xExpA i : Lˣ) : L))
    (fun i j hij => xExpA_inj i j (modEq_of_zpow_eq (griessU_prim hζ) (Units.ext hij)))
    (fun i => hroot _)
  obtain ⟨SB, hSB⟩ := exists_conj_diag_enum hκ'prim (sl_isUnit Ue) (sl_isUnit Ue') hκ' hcB Ue.2
    (fun i => ((griessU hζ ^ xExpB i : Lˣ) : L))
    (fun i j hij => xExpB_inj i j (modEq_of_zpow_eq (griessU_prim hζ) (Units.ext hij)))
    (fun i => hroot _)
  obtain ⟨SA', μA, hμA, hSA'⟩ := exists_sl_of_gl SA
  obtain ⟨SB', μB, hμB, hSB'⟩ := exists_sl_of_gl SB
  have hWA := conj_eq_diag_of_simul hμA hSA hSA'
  have hWB := conj_eq_diag_of_simul hμB hSB hSB'
  set WA : SL(5, L) := SA'⁻¹ * Ye * SA' with hWAdef
  set WB : SL(5, L) := SB'⁻¹ * Ue * SB' with hWBdef
  have hgA : ActsBy (rhoSigmaE8A4 L e8VA) (rhoSigmaE8A4 L e8VA WA * rhoSigmaE8A4 L e8VB WB)
      (diagGLn (fun i => griessU hζ ^ xExpA i)) := by
    have h := actsBy_lift_A WA WB
    have hG : Matrix.SpecialLinearGroup.toGL WA = diagGLn (fun i => griessU hζ ^ xExpA i) :=
      Units.ext hWA
    rwa [hG] at h
  have hgB : ActsBy (rhoSigmaE8A4 L e8VB) (rhoSigmaE8A4 L e8VA WA * rhoSigmaE8A4 L e8VB WB)
      (diagGLn (fun i => griessU hζ ^ xExpB i)) := by
    have h := actsBy_lift_B WA WB
    have hG : Matrix.SpecialLinearGroup.toGL WB = diagGLn (fun i => griessU hζ ^ xExpB i) :=
      Units.ext hWB
    rwa [hG] at h
  have hgT : rhoSigmaE8A4 L e8VA WA * rhoSigmaE8A4 L e8VB WB ∈ torusGroup Tag.E8 L :=
    mul_mem (rhoSigmaE8A4_diagonal e8VA WA fun i j hij => by
        rw [hWA]; exact Matrix.diagonal_apply_ne _ hij)
      (rhoSigmaE8A4_diagonal e8VB WB fun i j hij => by
        rw [hWB]; exact Matrix.diagonal_apply_ne _ hij)
  obtain ⟨m, hm⟩ := eq_pow_mul_of_actsBy hζ hgT (griessX_torus hζ) hgA (actsBy_x_A hζ)
    hgB (actsBy_x_B hζ)
  refine ⟨rhoSigmaE8A4 L e8VA SA' * rhoSigmaE8A4 L e8VB SB', m,
    mul_mem (rhoA_le_mulSub ⟨SA', rfl⟩) (rhoB_le_mulSub ⟨SB', rfl⟩), ?_⟩
  rw [conj_lift]
  exact hm

end ConjX

section ActualCubeMover

variable {L : Type} [Field L] [IsAlgClosed L]

theorem exists_conj_actual_lift_to_griessZ
    {ζ : L} (hζ : IsPrimitiveRoot ζ 5)
    {Y U Yb Ub : SL(5, L)}
    (hcomm : (rhoSigmaE8A4 L e8VA Y * rhoSigmaE8A4 L e8VB U) *
        (rhoSigmaE8A4 L e8VA Yb * rhoSigmaE8A4 L e8VB Ub) =
      (rhoSigmaE8A4 L e8VA Yb * rhoSigmaE8A4 L e8VB Ub) *
        (rhoSigmaE8A4 L e8VA Y * rhoSigmaE8A4 L e8VB U))
    (hb5 : (rhoSigmaE8A4 L e8VA Yb * rhoSigmaE8A4 L e8VB Ub) ^ 5 = 1)
    (hYnc : Y * Yb ≠ Yb * Y) :
    ∃ γ ∈ adjointGroup Tag.E8 L,
      γ * (rhoSigmaE8A4 L e8VA Y * rhoSigmaE8A4 L e8VB U) * γ⁻¹ = griessZ hζ := by
  let a : ModGL Tag.E8 L := rhoSigmaE8A4 L e8VA Y * rhoSigmaE8A4 L e8VB U
  let b : ModGL Tag.E8 L := rhoSigmaE8A4 L e8VA Yb * rhoSigmaE8A4 L e8VB Ub
  have hcomm_ab : a * b = b * a := by simpa [a, b] using hcomm
  have hb5' : b ^ 5 = 1 := by simpa [b] using hb5
  obtain ⟨ξ, m, hξmul, hξ⟩ :=
    exists_conj_x (L := L) hζ (Ye := Y) (Ue := U) (Ye' := Yb) (Ue' := Ub)
      hcomm_ab hb5' hYnc
  let n : ℕ := 5 - (m % 5)
  have hξz : Commute ξ (griessZ hζ) := mulSub_comm_z hζ hξmul
  have hξzpow : ξ⁻¹ * griessZ hζ ^ n = griessZ hζ ^ n * ξ⁻¹ :=
    (hξz.inv_left.pow_right n).eq
  have hYnc' : Yb * Y ≠ Y * Yb := fun h => hYnc h.symm
  obtain ⟨δ, hδmul, _, _, hδa⟩ :=
    exists_central_shear_of_noncommuting_A_lifts (L := L) hζ
      (a := b) (b := a) (Y := Yb) (U := Ub) (Y' := Y) (U' := U)
      rfl rfl (by simpa [a, b] using hcomm.symm) hYnc' n
  have hnm : 5 ∣ n + m := by
    have hm_lt : m % 5 < 5 := Nat.mod_lt m (by norm_num)
    have hm := Nat.mod_add_div m 5
    dsimp [n]
    omega
  have hzp : griessZ hζ ^ n * (griessZ hζ ^ m * griessX hζ) =
      griessZ hζ ^ (n + m) * griessX hζ := by
    rw [← mul_assoc, ← pow_add]
  have hznm : griessZ hζ ^ (n + m) = 1 := by
    obtain ⟨k, hk⟩ := hnm
    rw [hk, pow_mul, griessZ_pow_five hζ, one_pow]
  let γ : ModGL Tag.E8 L := (nU L)⁻¹ * ξ⁻¹ * δ
  have hnU : nU L ∈ adjointGroup Tag.E8 L := by
    simpa [nU] using canonicalRep_mem_adjointGroup (coxeterSystem Tag.E8) L uW
  have hγadj : γ ∈ adjointGroup Tag.E8 L := by
    dsimp [γ]
    exact mul_mem (mul_mem (inv_mem hnU) (inv_mem (mulSub_le_adjointGroup hξmul)))
      (mulSub_le_adjointGroup hδmul)
  have hγa : γ * a * γ⁻¹ = griessZ hζ := by
    calc γ * a * γ⁻¹
        = (nU L)⁻¹ * ξ⁻¹ * (δ * a * δ⁻¹) * ξ * nU L := by
          dsimp [γ]
          group
      _ = (nU L)⁻¹ * ξ⁻¹ * (griessZ hζ ^ n * a) * ξ * nU L := by rw [hδa]
      _ = (nU L)⁻¹ * (griessZ hζ ^ n * (ξ⁻¹ * a * ξ)) * nU L := by
          calc
            (nU L)⁻¹ * ξ⁻¹ * (griessZ hζ ^ n * a) * ξ * nU L
                = (nU L)⁻¹ * (ξ⁻¹ * (griessZ hζ ^ n * a) * ξ) * nU L := by
                    simp only [mul_assoc]
            _ = (nU L)⁻¹ * (griessZ hζ ^ n * (ξ⁻¹ * a * ξ)) * nU L := by
                    rw [show ξ⁻¹ * (griessZ hζ ^ n * a) * ξ =
                        griessZ hζ ^ n * (ξ⁻¹ * a * ξ) by
                      calc
                        ξ⁻¹ * (griessZ hζ ^ n * a) * ξ
                            = (ξ⁻¹ * griessZ hζ ^ n) * a * ξ := by simp only [mul_assoc]
                        _ = (griessZ hζ ^ n * ξ⁻¹) * a * ξ := by rw [hξzpow]
                        _ = griessZ hζ ^ n * (ξ⁻¹ * a * ξ) := by simp only [mul_assoc]]
      _ = (nU L)⁻¹ * (griessZ hζ ^ n * (griessZ hζ ^ m * griessX hζ)) * nU L := by
          rw [hξ]
      _ = (nU L)⁻¹ * (griessZ hζ ^ (n + m) * griessX hζ) * nU L := by
          rw [hzp]
      _ = (nU L)⁻¹ * griessX hζ * nU L := by rw [hznm, one_mul]
      _ = griessZ hζ := by
          rw [x_eq_conj_z L hζ]
          group
  exact ⟨γ, hγadj, by simpa [a] using hγa⟩

theorem exists_normalizer_mover_of_cube
    (h5 : (5 : L) ≠ 0) {ζ : L} (hζ : IsPrimitiveRoot ζ 5)
    {A : Subgroup (ModGL Tag.E8 L)} (hAmul : A ≤ mulSub L)
    (hA5 : CFSG.Open.IsElemAbelian 5 A)
    {a b : ModGL Tag.E8 L} (hbas : CubeBasis (griessZ hζ) a b)
    (hgen : A = Subgroup.closure ({griessZ hζ, a, b} : Set (ModGL Tag.E8 L)))
    (hnt : ¬ ∃ g ∈ adjointGroup Tag.E8 L,
      ∀ x ∈ A, g⁻¹ * x * g ∈ torusGroup Tag.E8 L) :
    ∃ n ∈ adjointGroup Tag.E8 L,
      Subgroup.map (MulAut.conj n).toMonoidHom A = A ∧
        n * griessZ hζ * n⁻¹ = a := by
  have haA : a ∈ A := by
    rw [hgen]
    exact Subgroup.subset_closure (by simp)
  have hbA : b ∈ A := by
    rw [hgen]
    exact Subgroup.subset_closure (by simp)
  have ha : a ∈ mulSub L := hAmul haA
  have hb : b ∈ mulSub L := hAmul hbA
  have hntA : ¬ ∃ g ∈ adjointGroup Tag.E8 L,
      ∀ x ∈ A, g⁻¹ * x * g ∈ torusGroup Tag.E8 L := hnt
  have hntE : ¬ ∃ g ∈ adjointGroup Tag.E8 L,
      ∀ x ∈ Subgroup.closure ({griessZ hζ, a, b} : Set (ModGL Tag.E8 L)),
        g⁻¹ * x * g ∈ torusGroup Tag.E8 L := by
    simpa [← hgen] using hntA
  obtain ⟨Y, U, Yb, Ub, hae, hbe, hYnc⟩ :=
    nc_lifts_of_nontoral h5 hζ ha hb hbas.comm_bc.eq hbas.pow_b hbas.pow_c
      (mulSub_comm_z hζ ha).symm (mulSub_comm_z hζ hb).symm hntE
  obtain ⟨γ, hγadj, hγa⟩ :=
    exists_conj_actual_lift_to_griessZ (L := L) hζ (Y := Y) (U := U)
      (Yb := Yb) (Ub := Ub) (by simpa only [hae, hbe] using hbas.comm_bc.eq)
      (by simpa only [hbe] using hbas.pow_c) hYnc
  have hγa_actual : γ * a * γ⁻¹ = griessZ hζ := by
    simpa only [← hae] using hγa
  let A' : Subgroup (ModGL Tag.E8 L) :=
    Subgroup.map (MulAut.conj γ).toMonoidHom A
  have hA'5 : CFSG.Open.IsElemAbelian 5 A' := hA5.map (MulAut.conj γ).toMonoidHom
  have hcardA : Nat.card A = 5 ^ 3 := by
    rw [hgen]
    exact hbas.card
  have hcardA' : Nat.card A' = 5 ^ 3 := by
    rw [show A' = Subgroup.map (MulAut.conj γ).toMonoidHom A from rfl]
    rw [Subgroup.card_map_of_injective (MulAut.conj γ).injective, hcardA]
  have hA'le : A' ≤ mulSub L := by
    intro x hx
    change x ∈ A.map (MulAut.conj γ).toMonoidHom at hx
    obtain ⟨y, hyA, rfl⟩ := Subgroup.mem_map.mp hx
    change γ * y * γ⁻¹ ∈ mulSub L
    have hyadj : y ∈ adjointGroup Tag.E8 L := mulSub_le_adjointGroup (hAmul hyA)
    have hxadj : γ * y * γ⁻¹ ∈ adjointGroup Tag.E8 L :=
      mul_mem (mul_mem hγadj hyadj) (inv_mem hγadj)
    have hxmem : γ * y * γ⁻¹ ∈ A' :=
      Subgroup.mem_map_of_mem (MulAut.conj γ).toMonoidHom hyA
    have hzmem : griessZ hζ ∈ A' := by
      rw [← hγa_actual]
      exact Subgroup.mem_map_of_mem (MulAut.conj γ).toMonoidHom haA
    have hcomm : (γ * y * γ⁻¹) * griessZ hζ = griessZ hζ * (γ * y * γ⁻¹) :=
      congrArg Subtype.val (hA'5.1.is_comm.comm ⟨_, hxmem⟩ ⟨_, hzmem⟩)
    exact centralizer_le_mulSub hζ hxadj hcomm
  have hntA' : ¬ ∃ g ∈ adjointGroup Tag.E8 L,
      ∀ x ∈ A', g⁻¹ * x * g ∈ torusGroup Tag.E8 L := by
    rintro ⟨g, hg, hgA'⟩
    apply hntA
    refine ⟨γ⁻¹ * g, mul_mem (inv_mem hγadj) hg, fun e he => ?_⟩
    have hγeA' : γ * e * γ⁻¹ ∈ A' :=
      Subgroup.mem_map_of_mem (MulAut.conj γ).toMonoidHom he
    have hgγe := hgA' (γ * e * γ⁻¹) hγeA'
    simpa [mul_assoc] using hgγe
  obtain ⟨e, heA', e', he'A', hze, hbas', hgen'⟩ :=
    exists_z_cube_of_nontoral_le_mulSub h5 hζ A' hA'le hA'5
      (le_of_eq hcardA'.symm) hntA'
  have he : e ∈ mulSub L := hA'le heA'
  have he' : e' ∈ mulSub L := hA'le he'A'
  have hntE' : ¬ ∃ g ∈ adjointGroup Tag.E8 L,
      ∀ x ∈ Subgroup.closure ({griessZ hζ, e, e'} : Set (ModGL Tag.E8 L)),
        g⁻¹ * x * g ∈ torusGroup Tag.E8 L := by
    simpa [hgen'] using hntA'
  obtain ⟨η, hηmul, hηmap⟩ :=
    exists_conj_cube_of_basis (L := L) (a := e) (b := e') (a' := a) (b' := b)
      h5 hζ he he' ha hb hbas' hbas hntE' hntE
  have hηA : Subgroup.map (MulAut.conj η).toMonoidHom A' = A := by
    rw [← hgen', hgen]
    exact hηmap
  let n : ModGL Tag.E8 L := η * γ
  have hnadj : n ∈ adjointGroup Tag.E8 L := by
    dsimp [n]
    exact mul_mem (mulSub_le_adjointGroup hηmul) hγadj
  have hnA : Subgroup.map (MulAut.conj n).toMonoidHom A = A := by
    have hcomp : (MulAut.conj η).toMonoidHom.comp (MulAut.conj γ).toMonoidHom =
        (MulAut.conj n).toMonoidHom := by
      ext x
      simp [n, MulAut.conj_apply, mul_assoc]
    calc
      Subgroup.map (MulAut.conj n).toMonoidHom A
          = Subgroup.map ((MulAut.conj η).toMonoidHom.comp
              (MulAut.conj γ).toMonoidHom) A := by rw [← hcomp]
      _ = Subgroup.map (MulAut.conj η).toMonoidHom
            (Subgroup.map (MulAut.conj γ).toMonoidHom A) := by
            rw [Subgroup.map_map]
      _ = A := by
            rw [show Subgroup.map (MulAut.conj γ).toMonoidHom A = A' from rfl, hηA]
  have hn_a : n * a * n⁻¹ = griessZ hζ := by
    dsimp [n]
    calc
      (η * γ) * a * (η * γ)⁻¹ = η * (γ * a * γ⁻¹) * η⁻¹ := by group
      _ = η * griessZ hζ * η⁻¹ := by rw [hγa_actual]
      _ = griessZ hζ := by
            rw [show η * griessZ hζ = griessZ hζ * η from mulSub_comm_z hζ hηmul]
            group
  let n' : ModGL Tag.E8 L := n⁻¹
  have hn'adj : n' ∈ adjointGroup Tag.E8 L := by
    dsimp [n']
    exact inv_mem hnadj
  have hn'A : Subgroup.map (MulAut.conj n').toMonoidHom A = A := by
    have hconj : MulAut.conj n' = (MulAut.conj n)⁻¹ := by
      dsimp [n']
      exact map_inv (MulAut.conj) n
    rw [hconj]
    exact (Subgroup.map_symm_eq_iff_map_eq (K := A) (H := A) (e := MulAut.conj n)).mpr hnA
  have hn'_z : n' * griessZ hζ * n'⁻¹ = a := by
    dsimp [n']
    calc
      n⁻¹ * griessZ hζ * (n⁻¹)⁻¹ = n⁻¹ * (n * a * n⁻¹) * n := by rw [hn_a, inv_inv]
      _ = a := by group
  exact ⟨n', hn'adj, hn'A, hn'_z⟩


end ActualCubeMover

end Two

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSE8Five
