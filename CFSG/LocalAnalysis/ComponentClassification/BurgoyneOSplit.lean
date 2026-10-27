module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOCore

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.O

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldAut)
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.PSL (compInd commute_compInd_iff diagGL coe_diagGL
  signMat
  signMat_mul_self commute_signMat_iff reflGL reflGL_mem rotGL rotGL_mem rotMat
  rotMat_neg_one_zero rotMat_apply_left commutatorElement_reflGL_rotGL eq_one_of_fix_circle
  mem_of_mem_oddCoreIn)
open scoped commutatorElement

variable {K : Type} [Field K] {d : ℕ}

theorem offDiag_eq_zero_of_commute_sign_on (h2 : (2 : K) ≠ 0) {I : Finset (Fin d)}
    (hI : 3 ≤ I.card) {D : Matrix (Fin d) (Fin d) K}
    (hs : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → D * signMat K {i, j} = signMat K {i, j} * D)
    {x y : Fin d} (hxy : x ≠ y) (hxI : x ∈ I ∨ y ∈ I) : D x y = 0 := by
  have hpick : ∀ a b : Fin d, ∃ z ∈ I, z ≠ a ∧ z ≠ b := by
    intro a b
    have hc : 0 < ((I.erase a).erase b).card := by
      have h1 := Finset.pred_card_le_card_erase (s := I) (a := a)
      have h2 := Finset.pred_card_le_card_erase (s := I.erase a) (a := b)
      omega
    obtain ⟨z, hz⟩ := Finset.card_pos.1 hc
    simp only [Finset.mem_erase] at hz
    exact ⟨z, hz.2.2, hz.2.1, hz.1⟩
  have key : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → ∀ u v, (u ∈ ({i, j} : Finset (Fin d)) ↔
      v ∉ ({i, j} : Finset (Fin d))) → D u v = 0 := by
    intro i hi j hj hij u v huv
    have e := congrFun (congrFun (hs i hi j hj hij) u) v
    simp only [signMat, mul_diagonal, diagonal_mul] at e
    by_cases hv : v ∈ ({i, j} : Finset (Fin d))
    · have hu : u ∉ ({i, j} : Finset (Fin d)) := fun hu => (huv.1 hu) hv
      simp only [hv, hu, ↓reduceIte] at e
      have : (2 : K) * D u v = 0 := by linear_combination -e
      exact (mul_eq_zero.1 this).resolve_left h2
    · have hu : u ∈ ({i, j} : Finset (Fin d)) := huv.2 hv
      simp only [hv, hu, ↓reduceIte] at e
      have : (2 : K) * D u v = 0 := by linear_combination e
      exact (mul_eq_zero.1 this).resolve_left h2
  rcases hxI with hx | hy
  · obtain ⟨z, hz, hzx, hzy⟩ := hpick x y
    refine key x hx z hz (Ne.symm hzx) x y ⟨fun _ => ?_, fun _ => by simp⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Ne.symm hxy, Ne.symm hzy⟩
  · obtain ⟨z, hz, hzx, hzy⟩ := hpick x y
    have hxn : x ∉ ({y, z} : Finset (Fin d)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hxy, Ne.symm hzx⟩
    exact key y hy z hz (Ne.symm hzy) x y
      ⟨fun h => absurd h hxn, fun h => absurd (Finset.mem_insert_self y _) h⟩

theorem conj_apply_diag_of_isolated {D : GL (Fin d) K} {i : Fin d}
    (hr : ∀ x, x ≠ i → (D : Matrix (Fin d) (Fin d) K) i x = 0)
    (hc : ∀ x, x ≠ i → (D : Matrix (Fin d) (Fin d) K) x i = 0) (M : Matrix (Fin d) (Fin d) K) :
    ((D : Matrix (Fin d) (Fin d) K) * M * ((D⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) i i =
      M i i := by
  set Di := ((D⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)
  have h1 : Di * (D : Matrix (Fin d) (Fin d) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h1' : (D : Matrix (Fin d) (Fin d) K) * Di = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hii : Di i i * (D : Matrix (Fin d) (Fin d) K) i i = 1 := by
    have e := congrFun (congrFun h1 i) i
    rwa [Matrix.mul_apply, Finset.sum_eq_single i (fun k _ hk => by rw [hc k hk, mul_zero])
      (by simp), one_apply_eq] at e
  have hDi : ∀ l, l ≠ i → Di l i = 0 := by
    intro l hl
    have e := congrFun (congrFun h1 l) i
    rw [Matrix.mul_apply, Finset.sum_eq_single i (fun k _ hk => by rw [hc k hk, mul_zero])
      (by simp), one_apply_ne hl] at e
    have hD0 : (D : Matrix (Fin d) (Fin d) K) i i ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hii
      exact zero_ne_one hii
    exact (mul_eq_zero.1 e).resolve_right hD0
  rw [Matrix.mul_apply, Finset.sum_eq_single i (fun l _ hl => by rw [hDi l hl, mul_zero])
    (by simp), Matrix.mul_apply, Finset.sum_eq_single i (fun k _ hk => by
      rw [hr k hk, zero_mul]) (by simp)]
  linear_combination M i i * hii

theorem reflGL_mem_oIsoBlock {w : Fin d → K} (hw : ∀ i, w i ≠ 0) {J : Finset (Fin d)}
    {i : Fin d} (hi : i ∈ J) : reflGL (K := K) i ∈ oIsoBlock K hw J := by
  rw [mem_oIsoBlock_iff]
  refine ⟨reflGL_mem hw i, fun x y hxy => ?_⟩
  change signMat K {i} x y = _
  have hx : x ≠ i ∨ y ≠ i := by
    rcases hxy with hx | hy
    · exact Or.inl fun h => hx (h ▸ hi)
    · exact Or.inr fun h => hy (h ▸ hi)
  simp only [signMat, diagonal_apply, Finset.mem_singleton]
  by_cases hxy' : x = y
  · subst hxy'
    simp only [↓reduceIte]
    rcases hx with hx | hx <;> simp [hx]
  · simp [hxy']

theorem rotGL_mem_oIsoBlock {w : Fin d → K} (hw : ∀ i, w i ≠ 0) {J : Finset (Fin d)}
    {i j : Fin d} (hi : i ∈ J) (hj : j ∈ J) (hij : i ≠ j) (hwij : w i = w j) {a b : K}
    (hab : a ^ 2 + b ^ 2 = 1) : rotGL i j hij hab ∈ oIsoBlock K hw J := by
  rw [mem_oIsoBlock_iff]
  refine ⟨rotGL_mem hw hij hwij hab, fun x y hxy => ?_⟩
  change rotMat i j a b x y = _
  have hx : (x ≠ i ∧ x ≠ j) ∨ (y ≠ i ∧ y ≠ j) := by
    rcases hxy with hx | hy
    · exact Or.inl ⟨fun h => hx (h ▸ hi), fun h => hx (h ▸ hj)⟩
    · exact Or.inr ⟨fun h => hy (h ▸ hi), fun h => hy (h ▸ hj)⟩
  simp only [rotMat, PSL.planeP, PSL.planeN, Matrix.add_apply, Matrix.smul_apply,
    Matrix.sub_apply, single_apply, one_apply, smul_eq_mul]
  by_cases hxy' : x = y
  · subst hxy'
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [Ne.symm h1, Ne.symm h2]
  · rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [hxy', Ne.symm h1, Ne.symm h2]

theorem comm_mem_oBlock {w : Fin d → K} (hw : ∀ i, w i ≠ 0) {J : Finset (Fin d)}
    {i j : Fin d} (hi : i ∈ J) (hj : j ∈ J) (hij : i ≠ j) (hwij : w i = w j) {a b : K}
    (hab : a ^ 2 + b ^ 2 = 1) :
    ⁅reflGL (K := K) i, rotGL i j hij hab⁆ ∈ oBlock K hw J :=
  commutator_mem_commutator (reflGL_mem_oIsoBlock hw hi)
    (rotGL_mem_oIsoBlock hw hi hj hij hwij hab)

theorem signGL_pair_mem_oBlock {w : Fin d → K} (hw : ∀ i, w i ≠ 0) {J : Finset (Fin d)}
    {i j : Fin d} (hi : i ∈ J) (hj : j ∈ J) (hij : i ≠ j) (hwij : w i = w j) :
    signGL K {i, j} ∈ oBlock K hw J := by
  have hab : (0 : K) ^ 2 + 1 ^ 2 = 1 := by ring
  have e : ⁅reflGL (K := K) i, rotGL i j hij hab⁆ = signGL K {i, j} := by
    apply Units.ext
    rw [commutatorElement_reflGL_rotGL, show (0 : K) ^ 2 - 1 ^ 2 = -1 by ring,
      show -(2 * (0 : K) * 1) = 0 by ring, rotMat_neg_one_zero hij, coe_signGL]
  rw [← e]
  exact comm_mem_oBlock hw hi hj hij hwij hab

theorem commPair_val {Q : QuadraticForm K (Fin d → K)} (g : similarityPairs Q) (A : GL (Fin d) K)
    (hA : A ∈ matrixIsometries Q) (hτA : glFieldAut (Fin d) K g.val.right A = A) :
    (g * linPair A hA * g⁻¹ * (linPair A hA)⁻¹ : similarityPairs Q).val.left =
        g.val.left * A * g.val.left⁻¹ * A⁻¹ ∧
      (g * linPair A hA * g⁻¹ * (linPair A hA)⁻¹ : similarityPairs Q).val.right = 1 := by
  have hr : (g.val * (linPair A hA).val * g.val⁻¹).right = 1 := by
    rw [SemidirectProduct.mul_right, SemidirectProduct.mul_right, SemidirectProduct.inv_right,
      linPair_right, mul_one, mul_inv_cancel]
  refine ⟨?_, ?_⟩
  · change (g.val * (linPair A hA).val * g.val⁻¹ * (linPair A hA).val⁻¹).left = _
    rw [SemidirectProduct.mul_left, hr, map_one, MulAut.one_apply, SemidirectProduct.inv_left,
      linPair_right, inv_one, map_one, MulAut.one_apply, linPair_left, SemidirectProduct.mul_left,
      SemidirectProduct.mul_left, SemidirectProduct.mul_right, SemidirectProduct.inv_left,
      linPair_left, linPair_right, hτA, mul_one, ← MulAut.mul_apply, ← map_mul, mul_inv_cancel,
      map_one, MulAut.one_apply]
  · change (g.val * (linPair A hA).val * g.val⁻¹ * (linPair A hA).val⁻¹).right = 1
    rw [coordinateSemilinearGroup_mul_field, coordinateSemilinearGroup_mul_field,
      coordinateSemilinearGroup_mul_field, coordinateSemilinearGroup_inv_field,
      coordinateSemilinearGroup_inv_field, linPair_right]
    simp

theorem map_signMat_field (τ : K ≃+* K) (J : Finset (Fin d)) :
    (signMat K J).map τ = signMat K J := by
  ext a b
  simp only [signMat, map_apply, diagonal_apply]
  split_ifs <;> simp

theorem split_core [Finite K] (hK : ringChar K ≠ 2) {w : Fin d → K} (hw : ∀ i, w i ≠ 0)
    (hker : OKer (oQ (diagGL hw)))
    (hinj : Function.Injective (MulAut.conj : StatedProj (matrixDerived (oQ (diagGL hw))) →*
      MulAut (StatedProj (matrixDerived (oQ (diagGL hw))))))
    {B : Subgroup (MulAut (StatedProj (matrixDerived (oQ (diagGL hw)))))}
    (hB : (MulAut.conj : StatedProj (matrixDerived (oQ (diagGL hw))) →*
      MulAut (StatedProj (matrixDerived (oQ (diagGL hw))))).range ≤ B)
    {J : Finset (Fin d)} (hJd : 2 * J.card ≠ d) {I : Finset (Fin d)} (hI : I = J ∨ I = Jᶜ)
    (hI3 : 3 ≤ I.card) (hIexc : ¬ (Nat.card K = 3 ∧ I.card ≤ 4))
    {I₀ : Finset (Fin d)} (hI₀ : I₀ ⊆ I) (hI₀3 : 3 ≤ I₀.card)
    (hI₀w : ∀ i ∈ I₀, ∀ j ∈ I₀, w i = w j)
    (hI₀c : ∀ x ∈ I, ∀ y ∈ I, x ∉ I₀ → y ∉ I₀ → x = y)
    {g : similarityPairs (oQ (diagGL hw))}
    (hy : oκ _ g ∈ oddCoreIn B (oκ _ (sgnPair (Ring.two_ne_zero hK) hw J))) :
    g.val.right = 1 ∧
      signMat K J * (g.val.left : Matrix (Fin d) (Fin d) K) =
        (g.val.left : Matrix (Fin d) (Fin d) K) * signMat K J ∧
      ∀ x ∈ I, ∀ y, y ≠ x → (g.val.left : Matrix (Fin d) (Fin d) K) x y = 0 ∧
        (g.val.left : Matrix (Fin d) (Fin d) K) y x = 0 := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hHeq : matrixDerived (oQ (diagGL hw)) = ⁅CatalogueBGraphForm.isometryGroup d K (diagGL hw),
      CatalogueBGraphForm.isometryGroup d K (diagGL hw)⁆ :=
    matrixDerived_oQ h2 (diagGL hw) (diagGL_transpose hw)
  have hIH : oBlock K hw I ≤ matrixDerived (oQ (diagGL hw)) := by
    rw [hHeq]; exact oBlock_le hw I
  set D := g.val.left with hD
  set τ := g.val.right with hτ
  have hodd := odd_orderOf_of_mem_oddCoreIn hy
  have hτm : τ ^ orderOf (oκ _ g) = 1 := hker.right_pow_eq_one (pow_orderOf_eq_one _)
  have hfix : ∀ X : matrixDerived (oQ (diagGL hw)), (X : GL (Fin d) K) ∈ oBlock K hw I →
      (D : Matrix (Fin d) (Fin d) K) * ((X : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map τ *
        ((D⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
          ((X : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) :=
    fun X hX => block_fix_of_components hK hw hinj hB hJd hI hI3 hIexc hy hX
  have hfix' : ∀ X : GL (Fin d) K, X ∈ oBlock K hw I →
      (D : Matrix (Fin d) (Fin d) K) * (X : Matrix (Fin d) (Fin d) K).map τ *
        ((D⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = X :=
    fun X hX => hfix ⟨X, hIH hX⟩ hX
  have hS : ∀ i ∈ I₀, ∀ j ∈ I₀, i ≠ j → (D : Matrix (Fin d) (Fin d) K) * signMat K {i, j} =
      signMat K {i, j} * D := by
    intro i hi j hj hij
    have e := hfix' _ (signGL_pair_mem_oBlock hw (hI₀ hi) (hI₀ hj) hij (hI₀w i hi j hj))
    rw [coe_signGL, map_signMat_field] at e
    calc (D : Matrix (Fin d) (Fin d) K) * signMat K {i, j} =
        (D : Matrix (Fin d) (Fin d) K) * signMat K {i, j} *
          (((D⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * D) := by
            rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
      _ = signMat K {i, j} * D := by rw [← Matrix.mul_assoc, e]
  have hiso₀ : ∀ x y, x ≠ y → (x ∈ I₀ ∨ y ∈ I₀) → (D : Matrix (Fin d) (Fin d) K) x y = 0 :=
    fun x y hxy hxI => offDiag_eq_zero_of_commute_sign_on h2 hI₀3 hS hxy hxI
  obtain ⟨i, hi, j, hj, hij⟩ : ∃ i ∈ I₀, ∃ j ∈ I₀, i ≠ j := by
    obtain ⟨i, hi⟩ := Finset.card_pos.1 (by omega : 0 < I₀.card)
    obtain ⟨j, hj⟩ := Finset.card_pos.1 (by
      have := Finset.pred_card_le_card_erase (s := I₀) (a := i); omega : 0 < (I₀.erase i).card)
    exact ⟨i, hi, j, (Finset.mem_erase.1 hj).2, Ne.symm (Finset.mem_erase.1 hj).1⟩
  have hτ1 : τ = 1 := by
    refine eq_one_of_fix_circle hK fun a b hab => ?_
    have e := hfix' _ (comm_mem_oBlock hw (hI₀ hi) (hI₀ hj) hij (hI₀w i hi j hj) hab)
    have e' := congrFun (congrFun e i) i
    rw [conj_apply_diag_of_isolated (fun x hx => hiso₀ i x (Ne.symm hx) (Or.inl hi))
      (fun x hx => hiso₀ x i hx (Or.inr hi)), map_apply, commutatorElement_reflGL_rotGL,
      rotMat_apply_left hij] at e'
    have hb : b ^ 2 = 1 - a ^ 2 := by linear_combination hab
    rw [hb] at e'
    have hτa2 : τ (a ^ 2) = a ^ 2 := by
      have e2 : τ (2 * a ^ 2 - 1) = 2 * a ^ 2 - 1 := by
        have h3 : (2 * a ^ 2 - 1 : K) = a ^ 2 - (1 - a ^ 2) := by ring
        rw [h3]
        exact e'
      rw [map_sub, map_mul, map_one, map_ofNat] at e2
      have : (2 : K) * (τ (a ^ 2) - a ^ 2) = 0 := by linear_combination e2
      exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left h2)
    rw [map_pow] at hτa2
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hτa2 with h | h
    · exact h
    · have hpow : ∀ m : ℕ, (τ ^ m) a = (-1) ^ m * a := by
        intro m
        induction m with
        | zero => simp
        | succ m ih =>
          rw [pow_succ]
          change (τ ^ m) (τ a) = _
          rw [h, map_neg, ih, pow_succ]
          ring
      have := hpow (orderOf (oκ _ g))
      rw [hτm, hodd.neg_one_pow] at this
      change a = -1 * a at this
      have ha0 : a = 0 := by
        have : (2 : K) * a = 0 := by linear_combination this
        exact (mul_eq_zero.1 this).resolve_left h2
      rw [h, ha0, neg_zero]
  have hsgnI : signGL K J ∈ matrixIsometries (oQ (diagGL hw)) :=
    (mem_matrixIsometries_oQ h2 _ (diagGL_transpose hw) _).2 (signGL_mem hw J)
  have hτS : glFieldAut (Fin d) K τ (signGL K J) = signGL K J := by
    apply Units.ext
    rw [coe_glFieldAut, coe_signGL, map_signMat_field]
  have hcomm : oκ _ (g * sgnPair h2 hw J * g⁻¹ * (sgnPair h2 hw J)⁻¹) = 1 := by
    have hc := mem_centralizer_singleton_iff.1 (mem_of_mem_oddCoreIn hy).2
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc, mul_inv_cancel_right, mul_inv_cancel]
  obtain ⟨-, c, hc⟩ := hker _ hcomm
  obtain ⟨hcl, -⟩ := commPair_val g (signGL K J) hsgnI hτS
  have hDS : (D : Matrix (Fin d) (Fin d) K) * signMat K J = (c : K) • (signMat K J * D) := by
    have e1 : D * signGL K J * D⁻¹ * (signGL K J)⁻¹ = GeneralLinearGroup.scalar (Fin d) c := by
      rw [← hcl, hc]
      rfl
    have e2 : D * signGL K J = GeneralLinearGroup.scalar (Fin d) c * signGL K J * D := by
      rw [← e1]
      group
    have e3 := congrArg (fun M : GL (Fin d) K => (M : Matrix (Fin d) (Fin d) K)) e2
    simp only [Units.val_mul, GeneralLinearGroup.coe_scalar, coe_signGL] at e3
    rw [e3, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul,
      Matrix.smul_mul]
  have hDii : (D : Matrix (Fin d) (Fin d) K) i i ≠ 0 := by
    intro h0
    have hcol : (D : Matrix (Fin d) (Fin d) K) *ᵥ Pi.single i 1 = 0 := by
      funext x
      rw [mulVec_single_one, col_apply, Pi.zero_apply]
      by_cases hx : x = i
      · rw [hx, h0]
      · exact hiso₀ x i hx (Or.inr hi)
    have := congrArg (fun v => ((D⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ v) hcol
    simp only [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec,
      mulVec_zero] at this
    have h1 := congrFun this i
    simp at h1
  have hc1 : (c : K) = 1 := by
    have e := congrFun (congrFun hDS i) i
    rw [Matrix.smul_apply, signMat, mul_diagonal, diagonal_mul, smul_eq_mul] at e
    have hsi : (if i ∈ J then (-1 : K) else 1) ≠ 0 := by split_ifs <;> simp
    have : ((D : Matrix (Fin d) (Fin d) K) i i * (if i ∈ J then (-1 : K) else 1)) *
        (1 - c) = 0 := by linear_combination e
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h (mul_ne_zero hDii hsi)
    · exact (sub_eq_zero.1 h).symm
  have hDS' : signMat K J * (D : Matrix (Fin d) (Fin d) K) = (D : Matrix (Fin d) (Fin d) K) *
      signMat K J := by rw [hDS, hc1, one_smul]
  refine ⟨hτ1, hDS', ?_⟩
  have hblock := (commute_compInd_iff J _).1 ((commute_signMat_iff h2 J _).1 hDS')
  have hsep : ∀ x ∈ I, ∀ y ∉ I, (x ∈ J ↔ y ∉ J) ∧ (y ∈ J ↔ x ∉ J) := by
    intro x hxI y hyI
    rcases hI with hIJ | hIJ
    · rw [hIJ] at hxI hyI
      exact ⟨⟨fun _ => hyI, fun _ => hxI⟩, ⟨fun h => absurd h hyI, fun h => absurd hxI h⟩⟩
    · rw [hIJ, Finset.mem_compl] at hxI
      rw [hIJ, Finset.mem_compl, not_not] at hyI
      exact ⟨⟨fun h => absurd h hxI, fun h => absurd hyI h⟩, ⟨fun _ => hxI, fun _ => hyI⟩⟩
  intro x hx y hyx
  by_cases hx₀ : x ∈ I₀
  · exact ⟨hiso₀ x y (Ne.symm hyx) (Or.inl hx₀), hiso₀ y x hyx (Or.inr hx₀)⟩
  by_cases hy₀ : y ∈ I₀
  · exact ⟨hiso₀ x y (Ne.symm hyx) (Or.inr hy₀), hiso₀ y x hyx (Or.inl hy₀)⟩
  by_cases hyI : y ∈ I
  · exact absurd (hI₀c y hyI x hx hy₀ hx₀) hyx
  · exact ⟨hblock x y (hsep x hx y hyI).1, hblock y x (hsep x hx y hyI).2⟩

end CFSG.ComponentClassification.Burgoyne.O
