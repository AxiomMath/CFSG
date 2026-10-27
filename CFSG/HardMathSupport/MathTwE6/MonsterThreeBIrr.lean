module

public import CFSG.HardMathSupport.MathTwE6.M3BIrrCheck
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThreeBCQ
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThreeBFibre

public section

namespace CFSG.HardMathSupport.MathTwE6.M3BIrr

open _root_.Timmesfeld.M3B (F3 Vec Mat fsum vget vofFn zeroV mget mofFn mmul mone meq mpow
  mOfRows)
open Matrix
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF (vfun toMat toMatrix
  toMatrix_apply toMatrix_mmul toMatrix_mone toMatrix_mpow vget_vofFn vfun_zeroV fsum_eq
  mget_mofFn meq_sound)

theorem vfun_axpy (c : F3) (x y : Vec) : vfun (axpy c x y) = vfun x + ThreeBNF.toZ c • vfun y := by
  funext i
  simp only [axpy, vfun, vget_vofFn, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rfl

theorem vfun_vmul (x : Vec) (A : Mat) : vfun (vmul x A) = vfun x ᵥ* toMatrix A := by
  funext j
  simp only [vmul, vfun, vget_vofFn, Matrix.vecMul, dotProduct, toMatrix_apply]
  rw [fsum_eq]
  rfl

theorem vfun_unitV (j : Fin 12) : vfun (unitV j) = Pi.single j 1 := by
  funext i
  simp only [unitV, vfun, vget_vofFn, Pi.single_apply]
  split_ifs <;> rfl

theorem vfun_eq_of_veq {x y : Vec} (h : veq x y = true) : vfun x = vfun y := by
  unfold veq at h
  simp only [List.all_eq_true, beq_iff_eq] at h
  funext i
  exact congrArg ThreeBNF.toZ (h i (List.mem_finRange i))

theorem toMatrix_eq_of_meq {A A' : Mat} (h : meq A A' = true) : toMatrix A = toMatrix A' :=
  congrArg Matrix.of (meq_sound h)

theorem toMatrix_madd (A B : Mat) : toMatrix (madd A B) = toMatrix A + toMatrix B := by
  ext i j
  simp only [toMatrix_apply, madd, mget_mofFn, Matrix.add_apply]
  rfl

theorem toMatrix_mzero : toMatrix mzero = 0 := by
  ext i j
  simp only [toMatrix_apply, mzero, mget_mofFn, Matrix.zero_apply]
  rfl

theorem toMatrix_scalar (c : F3) :
    toMatrix (mofFn fun i j => if i = j then c else 0) = Matrix.diagonal fun _ => ThreeBNF.toZ c := by
  ext i j
  simp only [toMatrix_apply, mget_mofFn, Matrix.diagonal_apply]
  split_ifs <;> rfl

variable {W : Submodule (ZMod 3) (Fin 12 → ZMod 3)}

theorem polyEval_mem {A : Mat} (hA : ∀ v ∈ W, v ᵥ* toMatrix A ∈ W) :
    ∀ (cs : List ℕ) {v}, v ∈ W → v ᵥ* toMatrix (polyEval cs A) ∈ W
  | [], v, _ => by rw [polyEval, List.foldr_nil, toMatrix_mzero, Matrix.vecMul_zero]; exact W.zero_mem
  | c :: cs, v, hv => by
    have h := polyEval_mem hA cs (hA v hv)
    rw [polyEval, List.foldr_cons, ← polyEval, toMatrix_madd, toMatrix_scalar, toMatrix_mmul,
      Matrix.vecMul_add, ← Matrix.vecMul_vecMul]
    refine W.add_mem ?_ h
    have e : v ᵥ* Matrix.diagonal (fun _ => ThreeBNF.toZ (Fin.ofNat 3 c)) = ThreeBNF.toZ (Fin.ofNat 3 c) • v := by
      funext j
      rw [Matrix.vecMul_diagonal, Pi.smul_apply, smul_eq_mul, mul_comm]
    rw [e]
    exact W.smul_mem _ hv

section Spin

variable {A B : Mat} (hA : ∀ v ∈ W, v ᵥ* toMatrix A ∈ W) (hB : ∀ v ∈ W, v ᵥ* toMatrix B ∈ W)
include hA hB

theorem axpy_mem (c : F3) {x y : Vec} (hx : vfun x ∈ W) (hy : vfun y ∈ W) :
    vfun (axpy c x y) ∈ W := by
  rw [vfun_axpy]
  exact W.add_mem hx (W.smul_mem _ hy)

theorem reduce_mem : ∀ (bas : List (Fin 12 × Vec)) {x : Vec}, (∀ pb ∈ bas, vfun pb.2 ∈ W) →
    vfun x ∈ W → vfun (reduce bas x) ∈ W
  | [], x, _, hx => hx
  | pb :: bas, x, hbas, hx => by
    unfold reduce
    rw [List.foldl_cons]
    exact reduce_mem bas (fun pb' h => hbas pb' (List.mem_cons_of_mem _ h))
      (axpy_mem hA hB _ hx (hbas pb List.mem_cons_self))

theorem spinLoop_mem : ∀ (n : ℕ) (bas : List (Fin 12 × Vec)) (q : List Vec),
    (∀ pb ∈ bas, vfun pb.2 ∈ W) → (∀ x ∈ q, vfun x ∈ W) →
    ∀ pb ∈ spinLoop A B n bas q, vfun pb.2 ∈ W
  | 0, bas, _, hbas, _ => by rw [spinLoop]; exact hbas
  | _ + 1, bas, [], hbas, _ => by rw [spinLoop]; exact hbas
  | n + 1, bas, x :: q, hbas, hq => by
    have hx := hq x List.mem_cons_self
    have hq' : ∀ y ∈ q, vfun y ∈ W := fun y hy => hq y (List.mem_cons_of_mem _ hy)
    have hr := reduce_mem hA hB bas hbas hx
    rw [spinLoop]
    split_ifs
    · exact spinLoop_mem n bas q hbas hq'
    · have hr' := axpy_mem hA hB (vget (reduce bas x) (pivot (reduce bas x)))
        (by rw [vfun_zeroV]; exact W.zero_mem) hr
      refine spinLoop_mem n _ _ ?_ ?_
      · intro pb hpb
        rcases List.mem_append.1 hpb with h | h
        · obtain ⟨qb, hqb, rfl⟩ := List.mem_map.1 h
          exact axpy_mem hA hB _ (hbas qb hqb) hr'
        · rw [List.mem_singleton] at h
          rw [h]
          exact hr'
      · intro y hy
        rcases List.mem_append.1 hy with h | h
        · exact hq' y h
        · rcases List.mem_pair.1 h with rfl | rfl
          · rw [vfun_vmul]; exact hA _ hr'
          · rw [vfun_vmul]; exact hB _ hr'

theorem eq_top_of_spinFull {v : Vec} (h : spinFull A B v = true) (hv : vfun v ∈ W) : W = ⊤ := by
  classical
  have hunit : ∀ j : Fin 12, (Pi.single j 1 : Fin 12 → ZMod 3) ∈ W := by
    intro j
    unfold spinFull at h
    simp only [List.all_eq_true, List.any_eq_true] at h
    obtain ⟨pb, hpb, heq⟩ := h j (List.mem_finRange j)
    have hmem := spinLoop_mem hA hB 64 [] [v] (by simp) (by simpa using hv) pb hpb
    rw [vfun_eq_of_veq heq, vfun_unitV] at hmem
    exact hmem
  rw [eq_top_iff]
  intro x _
  rw [pi_eq_sum_univ x]
  refine W.sum_mem fun j _ => W.smul_mem _ ?_
  have e : (fun k => if j = k then (1 : ZMod 3) else 0) = Pi.single j 1 := by
    funext k
    simp only [Pi.single_apply, eq_comm]
  rw [e]
  exact hunit j

end Spin

theorem vfun_vec3 (y : Fin 12 → ZMod 3) (hy : ∀ j : Fin 12, 3 ≤ j.val → y j = 0) :
    vfun (vec3 (y 0) (y 1) (y 2)) = y := by
  funext j
  simp only [vec3, vfun, vget_vofFn]
  have hj := j.isLt
  rcases j with ⟨j, hj'⟩
  interval_cases j <;> first | rfl | exact (hy _ (by norm_num)).symm

theorem eq_bot_or_eq_top_of_irrCheck (h : irrCheck () = true)
    (hA : ∀ v ∈ W, v ᵥ* toMatrix (matA ()) ∈ W) (hB : ∀ v ∈ W, v ᵥ* toMatrix (matB ()) ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  classical
  unfold irrCheck at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨_, _⟩, hsum⟩, h0⟩, h1⟩, h2⟩, h3⟩ := h
  by_cases hW : W = ⊥
  · exact Or.inl hW
  obtain ⟨x, hxW, hx0⟩ := (Submodule.ne_bot_iff W).1 hW
  right
  set P : ℕ → Matrix (Fin 12) (Fin 12) (ZMod 3) := fun i =>
    toMatrix (polyEval (idemCoeffs.getD i []) (matA ())) with hP
  have hsum' : P 0 + P 1 + (P 2 + P 3) = 1 := by
    have := toMatrix_eq_of_meq hsum
    simpa only [toMatrix_madd, toMatrix_mone] using this
  have hex : ∃ i ∈ ({0, 1, 2, 3} : Finset ℕ), x ᵥ* P i ≠ 0 := by
    by_contra hne
    push Not at hne
    apply hx0
    have e : x = x ᵥ* P 0 + x ᵥ* P 1 + (x ᵥ* P 2 + x ᵥ* P 3) := by
      rw [← Matrix.vecMul_add, ← Matrix.vecMul_add, ← Matrix.vecMul_add, hsum',
        Matrix.vecMul_one]
    rw [e, hne 0 (by simp), hne 1 (by simp), hne 2 (by simp), hne 3 (by simp)]
    simp
  obtain ⟨i, hi, hxi⟩ := hex
  have hok : idemOK (matA ()) (matB ()) i = true := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  unfold idemOK at hok
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    beq_iff_eq] at hok
  obtain ⟨⟨hfac, hsupp⟩, hspin⟩ := hok
  have hPi : P i = toMatrix (matCi i) * toMatrix (matBi i) := by
    rw [hP]
    simp only
    rw [toMatrix_eq_of_meq hfac, toMatrix_mmul]
  set y := x ᵥ* toMatrix (matCi i) with hy
  have hy0 : ∀ j : Fin 12, 3 ≤ j.val → y j = 0 := by
    intro j hj
    rw [hy, Matrix.vecMul, dotProduct]
    refine Finset.sum_eq_zero fun r _ => ?_
    rcases hsupp r (List.mem_finRange r) j (List.mem_finRange j) with h | h
    · omega
    · rw [toMatrix_apply, h]
      exact mul_zero _
  have hxP : x ᵥ* P i = vfun (vmul (vec3 (y 0) (y 1) (y 2)) (matBi i)) := by
    rw [vfun_vmul, vfun_vec3 y hy0, hy, Matrix.vecMul_vecMul, hPi]
  have hmem : x ᵥ* P i ∈ W := polyEval_mem hA _ hxW
  rcases hspin (y 0) (List.mem_finRange _) (y 1) (List.mem_finRange _) (y 2)
      (List.mem_finRange _) with hz | hfull
  · exfalso
    apply hxi
    rw [hxP]
    have hy' : y = 0 := by
      funext j
      rcases j with ⟨j, hj⟩
      by_cases h3 : 3 ≤ j
      · exact hy0 ⟨j, hj⟩ h3
      · interval_cases j
        · exact hz.1.1
        · exact hz.1.2
        · exact hz.2
    have hv : vfun (vec3 (y 0) (y 1) (y 2)) = 0 := by rw [vfun_vec3 y hy0, hy']
    rw [vfun_vmul, hv, Matrix.zero_vecMul]
  · rw [hxP] at hmem
    exact eq_top_of_spinFull hA hB hfull hmem

section Application

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG.AGLEmbedding.Norton.MON5_7 CFSG.Monster.Generated CFSG.Monster.B.Pinned
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF (QQ tbL tbL_mem_evalG actMat_evalG
  actMat_pow' conj_q_mem_of_mem evalG letterG)
open _root_.Timmesfeld.M3B (matOf LM)

noncomputable def coordSpace (N : Subgroup Gmat) (hN : N ≤ QQ) :
    Submodule (ZMod 3) (Fin 12 → ZMod 3) :=
  AddSubgroup.toZModSubmodule 3
    { carrier := {v | ∃ x ∈ N, coord 3 tbq tbw tbM x = v}
      add_mem' := by
        rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
        exact ⟨x * y, N.mul_mem hx hy, tbCommData.coord_mul (hN hx) (hN hy)⟩
      zero_mem' := ⟨1, N.one_mem, tbCommData.coord_one⟩
      neg_mem' := by
        rintro _ ⟨x, hx, rfl⟩
        exact ⟨x⁻¹, N.inv_mem hx, tbCommData.coord_inv (hN hx)⟩ }

theorem coordSpace_invariant {N : Subgroup Gmat} (hN : N ≤ QQ) {h : Gmat} (hL : h ∈ tbL)
    (hh : h ∈ Subgroup.normalizer (N : Set Gmat)) :
    ∀ v ∈ coordSpace N hN, v ᵥ* CommData.actMat 3 tbq tbw tbM h ∈ coordSpace N hN := by
  rintro _ ⟨x, hx, rfl⟩
  have hinv : h⁻¹ ∈ Subgroup.normalizer (N : Set Gmat) := Subgroup.inv_mem _ hh
  have hx' : h⁻¹ * x * h ∈ N := by
    have := (Subgroup.mem_normalizer_iff.1 hinv x).1 hx
    rwa [inv_inv] at this
  exact ⟨h⁻¹ * x * h, hx', tbCommData.coord_conj (conj_q_mem_of_mem hL) (hN hx)⟩

theorem pow_invariant {W : Submodule (ZMod 3) (Fin 12 → ZMod 3)}
    {T : Matrix (Fin 12) (Fin 12) (ZMod 3)} (hT : ∀ v ∈ W, v ᵥ* T ∈ W) :
    ∀ k : ℕ, ∀ v ∈ W, v ᵥ* T ^ k ∈ W
  | 0, v, hv => by rwa [pow_zero, Matrix.vecMul_one]
  | k + 1, v, hv => by
    rw [pow_succ, ← Matrix.vecMul_vecMul]
    exact hT _ (pow_invariant hT k v hv)

theorem invariant_word {N : Subgroup Gmat} (hN : N ≤ QQ)
    (hnorm : ∀ g ∈ tbL, g ^ (10 : ℕ).factorial ∈ Subgroup.normalizer (N : Set Gmat))
    (t : _root_.Timmesfeld.M3B.WT) (k : ℕ) :
    ∀ v ∈ coordSpace N hN,
      v ᵥ* toMatrix (matOf (LM ()) t) ^ ((10 : ℕ).factorial * k) ∈ coordSpace N hN := by
  have hg := tbL_mem_evalG t
  have h := coordSpace_invariant hN (tbL.pow_mem hg _) (hnorm _ hg)
  rw [actMat_pow' hg, actMat_evalG] at h
  intro v hv
  rw [pow_mul]
  exact pow_invariant h k v hv

theorem tbL_dichotomy (hirr : irrCheck () = true) (N : Subgroup Gmat) (hN : N ≤ QQ)
    (hnorm : ∀ g ∈ tbL, g ^ (10 : ℕ).factorial ∈ Subgroup.normalizer (N : Set Gmat)) :
    N ≤ Subgroup.zpowers tbw ∨ N = QQ := by
  classical
  haveI : Finite Gmat := ThreeBNF.finite_Gmat
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hirr' := hirr
  unfold irrCheck at hirr'
  simp only [Bool.and_eq_true] at hirr'
  obtain ⟨⟨⟨⟨⟨⟨hA13, hB11⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hirr'
  have hA13' : toMatrix (matA ()) ^ 13 = 1 := by
    rw [← toMatrix_mpow, toMatrix_eq_of_meq hA13, toMatrix_mone]
  have hB11' : toMatrix (matB ()) ^ 11 = 1 := by
    rw [← toMatrix_mpow, toMatrix_eq_of_meq hB11, toMatrix_mone]
  set W := coordSpace N hN with hW
  have hA : ∀ v ∈ W, v ᵥ* toMatrix (matA ()) ∈ W := by
    intro v hv
    have h := invariant_word hN hnorm w₁ 4 v hv
    have e : toMatrix (matOf (LM ()) w₁) ^ ((10 : ℕ).factorial * 4) = toMatrix (matA ()) := by
      have h1 : (toMatrix (matOf (LM ()) w₁) ^ 2520) ^ 13 = 1 := by
        rw [← toMatrix_mpow]; exact hA13'
      rw [matA, toMatrix_mpow, show (10 : ℕ).factorial * 4 = 2520 * (13 * 443 + 1) by decide,
        pow_mul, pow_add, pow_mul, h1, one_pow, one_mul, pow_one]
    rwa [e] at h
  have hB : ∀ v ∈ W, v ᵥ* toMatrix (matB ()) ∈ W := by
    intro v hv
    have h := invariant_word hN hnorm w₂ 10 v hv
    have e : toMatrix (matOf (LM ()) w₂) ^ ((10 : ℕ).factorial * 10) = toMatrix (matB ()) := by
      have h1 : (toMatrix (matOf (LM ()) w₂) ^ 2520) ^ 11 = 1 := by
        rw [← toMatrix_mpow]; exact hB11'
      rw [matB, toMatrix_mpow, show (10 : ℕ).factorial * 10 = 2520 * (11 * 1309 + 1) by decide,
        pow_mul, pow_add, pow_mul, h1, one_pow, one_mul, pow_one]
    rwa [e] at h
  have hker : ∀ g ∈ QQ, coord 3 tbq tbw tbM g = 0 → g ∈ Subgroup.zpowers tbw := by
    intro g hg h0
    have hk : (⟨g, hg⟩ : QQ) ∈ tbCommData.coordHom.ker := by
      rw [MonoidHom.mem_ker, CommData.coordHom_apply]
      simp only [h0, ofAdd_zero]
    rw [tbCommData.ker_coordHom] at hk
    exact Subgroup.mem_subgroupOf.1 hk
  rcases eq_bot_or_eq_top_of_irrCheck hirr hA hB with hbot | htop
  · left
    intro x hx
    have hv : coord 3 tbq tbw tbM x ∈ W := ⟨x, hx, rfl⟩
    rw [hbot, Submodule.mem_bot] at hv
    exact hker x (hN hx) hv
  · right
    have hall : ∀ v, ∃ x ∈ N, coord 3 tbq tbw tbM x = v := by
      intro v
      have hv : v ∈ W := by rw [htop]; exact Submodule.mem_top
      exact hv
    have hrep : ∀ i : Fin 12, ∃ x ∈ N, ∃ c ∈ Subgroup.zpowers tbw, x = c * tbq i := by
      intro i
      obtain ⟨x, hx, hxc⟩ := hall (coord 3 tbq tbw tbM (tbq i))
      have hqQ : tbq i ∈ QQ := Subgroup.subset_closure ⟨i, rfl⟩
      refine ⟨x, hx, x * (tbq i)⁻¹, hker _ (QQ.mul_mem (hN hx) (QQ.inv_mem hqQ)) ?_, by group⟩
      rw [tbCommData.coord_mul (hN hx) (QQ.inv_mem hqQ), tbCommData.coord_inv hqQ, hxc,
        add_neg_cancel]
    obtain ⟨x, hx, c, hc, rfl⟩ := hrep ⟨1, by norm_num⟩
    obtain ⟨y, hy, d, hd, rfl⟩ := hrep ⟨0, by norm_num⟩
    have hcQ : ∀ g ∈ QQ, Commute c g := fun g hg =>
      (tbCommData.commute_of_mem hg hc).symm
    have hdQ : ∀ g ∈ QQ, Commute d g := fun g hg =>
      (tbCommData.commute_of_mem hg hd).symm
    have hq : ∀ i, tbq i ∈ QQ := fun i => Subgroup.subset_closure ⟨i, rfl⟩
    have hdq : d * tbq ⟨0, by norm_num⟩ ∈ QQ :=
      QQ.mul_mem ((Subgroup.zpowers_le.2 tbCommData.mem_z) hd) (hq _)
    have hcomm : bcomm (c * tbq ⟨1, by norm_num⟩) (d * tbq ⟨0, by norm_num⟩) = tbw := by
      rw [bcomm_mul_left, (bcomm_eq_one_iff.2 (hcQ _ hdq).eq), mul_one, inv_mul_cancel, one_mul,
        bcomm_swap, bcomm_mul_left, bcomm_eq_one_iff.2 (hdQ _ (hq _)).eq, mul_one,
        inv_mul_cancel, one_mul, ← bcomm_swap, tbCommData.bcomm_q, tbM_val, pow_one]
    have hw : tbw ∈ N := by
      rw [← hcomm, bcomm]
      exact N.mul_mem (N.mul_mem (N.mul_mem (N.inv_mem hx) (N.inv_mem hy)) hx) hy
    apply le_antisymm hN
    intro g hg
    obtain ⟨x', hx', hxg⟩ := hall (coord 3 tbq tbw tbM g)
    have h0 : x'⁻¹ * g ∈ Subgroup.zpowers tbw := by
      refine hker _ (QQ.mul_mem (QQ.inv_mem (hN hx')) hg) ?_
      rw [tbCommData.coord_mul (QQ.inv_mem (hN hx')) hg, tbCommData.coord_inv (hN hx'), hxg,
        neg_add_cancel]
    have hzN : Subgroup.zpowers tbw ≤ N := Subgroup.zpowers_le.2 hw
    have := N.mul_mem hx' (hzN h0)
    rwa [mul_inv_cancel_left] at this

end Application

end CFSG.HardMathSupport.MathTwE6.M3BIrr
