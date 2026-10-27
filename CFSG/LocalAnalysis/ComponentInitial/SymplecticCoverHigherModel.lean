module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixCoverModel
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverHigher

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.SymplecticCoverHigher

open Matrix CFSG.Assembly.LowTwoRank SymplecticFlag SymplecticTorusWeyl MatrixExtension
  BinarySymplecticSix CFSG.LieType.Universal.SpecialLinear
open scoped commutatorElement

variable {n : ℕ}

@[expose] def rootX (i j : Fin n) : StatedSp n (ZMod 2) :=
  if h : i = j then 1 else leviSp (binaryTransvection h)

theorem rootX_of_ne {i j : Fin n} (h : i ≠ j) : rootX i j = leviSp (binaryTransvection h) :=
  dite_eq_right h

variable (n) in
@[expose] def rootData : LinearCover.TypeARoots (StatedSp n (ZMod 2)) n where
  x := rootX
  mul_self i j hij := by rw [rootX_of_ne hij, ← map_mul, binaryTransvection_mul_self, map_one]
  comm i j k l hij hkl hjk hil := by
    rw [rootX_of_ne hij, rootX_of_ne hkl, ← map_mul, ← map_mul,
      binaryTransvection_commute hij hkl hjk (Ne.symm hil)]
  commutator i j l hij hjl hil := by
    rw [rootX_of_ne hij, rootX_of_ne hjl, rootX_of_ne hil, ← map_commutatorElement,
      commutatorElement_binaryTransvection hij hjl hil]

theorem rootData_x (i j : Fin n) : (rootData n).x i j = rootX i j :=
  rfl

theorem coe_rootX {i j : Fin n} (h : i ≠ j) :
    (((rootX i j : StatedSp n (ZMod 2)) : GL (Fin n ⊕ Fin n) (ZMod 2)) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (ZMod 2)) =
      1 + single (Sum.inl i) (Sum.inl j) 1 + single (Sum.inr j) (Sum.inr i) 1 := by
  rw [rootX_of_ne h, coe_leviSp, binaryTransvection_inv, binaryTransvection_coe]
  ext (a | a) (b | b) <;> simp [single_apply, one_apply, and_comm]

theorem coe_tauSym_binaryOff (i j : Fin n) :
    (((tauSym n (Multiplicative.ofAdd ⟨binaryOff i j, binaryOff_mem_binarySymMatrices i j⟩) :
      StatedSp n (ZMod 2)) : GL (Fin n ⊕ Fin n) (ZMod 2)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (ZMod 2)) =
      1 + single (Sum.inl i) (Sum.inr j) 1 + single (Sum.inl j) (Sum.inr i) 1 := by
  rw [coe_tauSym, toAdd_ofAdd]
  ext (a | a) (b | b) <;> simp [binaryOff, single_apply, one_apply]

@[expose] def swapFun (T : Finset (Fin n)) : Fin n ⊕ Fin n → Fin n ⊕ Fin n :=
  Sum.elim (fun a => if a ∈ T then Sum.inr a else Sum.inl a)
    (fun a => if a ∈ T then Sum.inl a else Sum.inr a)

theorem swapFun_involutive (T : Finset (Fin n)) : Function.Involutive (swapFun T) := by
  rintro (a | a) <;> by_cases ha : a ∈ T <;> simp [swapFun, ha]

@[expose] def swapPerm (T : Finset (Fin n)) : Equiv.Perm (Fin n ⊕ Fin n) :=
  (swapFun_involutive T).toPerm _

theorem swapPerm_apply (T : Finset (Fin n)) (x : Fin n ⊕ Fin n) :
    swapPerm T x = swapFun T x :=
  rfl

theorem swapPerm_symm (T : Finset (Fin n)) : (swapPerm T).symm = swapPerm T :=
  Function.Involutive.toPerm_symm _

theorem swapPerm_mem (T : Finset (Fin n)) : swapPerm T ∈ signedPermGroup n := by
  rintro (a | a) <;> by_cases ha : a ∈ T <;> simp [swapPerm_apply, swapFun, ha]

theorem dotSign_zmod_two (w : Equiv.Perm (Fin n ⊕ Fin n)) : dotSign (K := ZMod 2) w = 1 := by
  funext x
  rcases x with i | i
  · rfl
  · simp only [dotSign, Sum.elim_inr, Pi.one_apply]
    rcases w (Sum.inr i) with j | j
    · exact (show (-1 : ZMod 2) = 1 by decide)
    · rfl

@[expose] def swapElt (T : Finset (Fin n)) : StatedSp n (ZMod 2) :=
  dotW (ZMod 2) ⟨swapPerm T, swapPerm_mem T⟩

theorem coe_swapElt (T : Finset (Fin n)) :
    (((swapElt T : StatedSp n (ZMod 2)) : GL (Fin n ⊕ Fin n) (ZMod 2)) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (ZMod 2)) = signedPerm (swapPerm T) 1 := by
  rw [swapElt, coe_dotW, dotSign_zmod_two]

theorem swapElt_mul_rootX {T : Finset (Fin n)} {i j : Fin n} (hij : i ≠ j) (hi : i ∉ T)
    (hj : j ∈ T) :
    swapElt T * rootX i j =
      tauSym n (Multiplicative.ofAdd ⟨binaryOff i j, binaryOff_mem_binarySymMatrices i j⟩) *
        swapElt T := by
  apply statedSp_ext
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [coe_swapElt, coe_rootX hij, coe_tauSym_binaryOff, Matrix.mul_add, Matrix.mul_add,
    Matrix.mul_one, Matrix.add_mul, Matrix.add_mul, Matrix.one_mul, signedPerm_mul_single,
    signedPerm_mul_single, single_mul_signedPerm, single_mul_signedPerm, swapPerm_symm]
  simp [swapPerm_apply, swapFun, hi, hj]

theorem swapElt_mul_rootX_mul_inv {T : Finset (Fin n)} {i j : Fin n} (hij : i ≠ j) (hi : i ∉ T)
    (hj : j ∈ T) :
    swapElt T * rootX i j * (swapElt T)⁻¹ =
      tauSym n (Multiplicative.ofAdd ⟨binaryOff i j, binaryOff_mem_binarySymMatrices i j⟩) := by
  rw [swapElt_mul_rootX hij hi hj, mul_inv_cancel_right]

theorem unitriangularGL_le_closure :
    unitriangularGL n (ZMod 2) ≤ Subgroup.closure {g | ∃ i j : Fin n, ∃ h : i < j,
      binaryTransvection h.ne = g} := by
  intro A hA
  have hA' : (⟨(A : Matrix (Fin n) (Fin n) (ZMod 2)), hA.det_eq_one⟩ :
      SpecialLinearGroup (Fin n) (ZMod 2)) ∈ LinearFlag.unitriangular n (ZMod 2) :=
    ⟨fun a b hab => hA.1 hab, hA.2⟩
  have h := Subgroup.mem_map_of_mem SpecialLinearGroup.toGL
    (LinearCover.unitriangular_le_closure_rootSL (by rw [Nat.card_zmod]) hA')
  rw [MonoidHom.map_closure] at h
  have hA'' : SpecialLinearGroup.toGL (⟨(A : Matrix (Fin n) (Fin n) (ZMod 2)), hA.det_eq_one⟩ :
      SpecialLinearGroup (Fin n) (ZMod 2)) = A := Units.ext rfl
  rw [hA''] at h
  refine Subgroup.closure_mono ?_ h
  rintro _ ⟨_, ⟨i, j, hij, rfl⟩, rfl⟩
  refine ⟨i, j, hij, Units.ext ?_⟩
  change (transvection i j 1 : Matrix (Fin n) (Fin n) (ZMod 2)) =
    ((LinearCover.rootSL i j : SpecialLinearGroup (Fin n) (ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2))
  rw [LinearCover.coe_rootSL_of_ne hij.ne]

theorem leviSp_mem_closure_rootX {A : GL (Fin n) (ZMod 2)} (hA : A ∈ unitriangularGL n (ZMod 2)) :
    leviSp A ∈ Subgroup.closure {g | ∃ i j : Fin n, i < j ∧ rootX i j = g} := by
  have h := Subgroup.mem_map_of_mem leviSp (unitriangularGL_le_closure hA)
  rw [MonoidHom.map_closure] at h
  refine Subgroup.closure_mono ?_ h
  rintro _ ⟨_, ⟨i, j, hij, rfl⟩, rfl⟩
  exact ⟨i, j, hij, rootX_of_ne hij.ne⟩

theorem card_binarySymMatrices (n : ℕ) :
    Nat.card (binarySymMatrices n) = 2 ^ (n * (n + 1) / 2) := by
  have h := card_symmetric (K := ZMod 2) n
  rw [Nat.card_zmod] at h
  rw [← h]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun X => mem_binarySymMatrices)

theorem half_add_half (n : ℕ) : n * (n - 1) / 2 + n * (n + 1) / 2 = n ^ 2 := by
  rcases n with _ | s
  · rfl
  · have h1 : (s + 1) * (s + 1 + 1) = (s + 1) * (s + 1 - 1) + 2 * (s + 1) := by
      rw [Nat.add_sub_cancel]
      ring
    have h2 : 2 ∣ (s + 1) * (s + 1 - 1) := by
      rw [Nat.add_sub_cancel]
      exact (Nat.even_mul_succ_self s).two_dvd.trans (by rw [mul_comm])
    rw [h1, Nat.add_mul_div_left _ _ two_pos]
    obtain ⟨t, ht⟩ := h2
    rw [ht, Nat.mul_div_cancel_left _ two_pos]
    have : (s + 1) ^ 2 = 2 * t + (s + 1) := by
      rw [← ht, Nat.add_sub_cancel]
      ring
    omega

theorem nonempty_mulEquiv_statedSp_of_lieModel_n {J : Type} [Group J]
    (hJ : CFSG.Blueprint.LieModel J .PSp n 2 1) : Nonempty (J ≃* StatedSp n (ZMod 2)) := by
  rcases hJ with ⟨-, hc⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hc
    have : Fintype K := Fintype.ofFinite K
    have hK2 : Nat.card K = 2 := by rw [hK, pow_one]
    have hcard : Fintype.card K = Fintype.card (ZMod 2) := by
      rw [ZMod.card, ← Nat.card_eq_fintype_card, hK2]
    exact ⟨(e.trans ((QuotientGroup.quotientMulEquivOfEq
      (statedScalars_subgroupOf_eq_bot hK2 n)).trans QuotientGroup.quotientBot)).trans
      (statedSpCongr (FiniteField.ringEquivOfCardEq hcard) n)⟩
  all_goals exact absurd ht (by decide)

end CFSG.LocalAnalysis.ComponentInitial.SymplecticCoverHigher
