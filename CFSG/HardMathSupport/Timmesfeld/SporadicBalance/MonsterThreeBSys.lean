module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThreeBBridge
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON5_7.ThreeBDatum
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThreeBChecks

public section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF

open CFSG.AGLEmbedding.Norton.MON5_7 CFSG.Monster.Generated
open _root_.Timmesfeld.M3B (F3 Vec Mat E AD vget vofFn zeroV mget aget mOfRows mofFn adOfRows
  mRows xRows yRows c1 c2 B0 Da Db LA)

section Generic

variable {G : Type*} [Group G] {n : ℕ}

theorem betaC_zero_left (B : Fin n → Fin n → ZMod 3) (w : Fin n → ZMod 3) :
    betaC n B 0 w = 0 := by
  simp [betaC]

theorem betaC_add_left (B : Fin n → Fin n → ZMod 3) (u v w : Fin n → ZMod 3) :
    betaC n B (u + v) w = betaC n B u w + betaC n B v w := by
  simp only [betaC, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp [add_mul]

theorem emul_eone_left (B : Fin n → Fin n → ZMod 3) (x : Elt n) : emul B eone x = x := by
  simp only [emul, eone, zero_add, betaN3_eq, betaC_zero_left, add_zero]

theorem epow_three (B : Fin n → Fin n → ZMod 3) (x : Elt n) : epow B x 3 = eone := by
  simp only [epow, emul_eone_left]
  simp only [emul, betaN3_eq, betaC_add_left, eone]
  refine Prod.ext ?_ ?_
  · funext i
    simp only [Pi.add_apply, Pi.zero_apply]
    have : (3 : ZMod 3) = 0 := rfl
    linear_combination (x.1 i) * this
  · have : (3 : ZMod 3) = 0 := rfl
    linear_combination (x.2 + betaC n B x.1 x.1) * this

theorem Sys.nf_pow_three {S : Sys G n} (hS : S.Good) (x : Elt n) : S.nf x ^ 3 = 1 := by
  rw [← Sys.nf_epow hS, epow_three, Sys.nf_eone]

theorem Sys.nf_inv {S : Sys G n} (hS : S.Good) (x : Elt n) :
    (S.nf x)⁻¹ = S.nf (epow S.B x 2) := by
  rw [Sys.nf_epow hS, inv_eq_of_mul_eq_one_right]
  rw [← pow_succ', Sys.nf_pow_three hS]

@[expose] def ecomm (B : Fin n → Fin n → ZMod 3) (x y : Elt n) : Elt n :=
  emul B (emul B (emul B (epow B x 2) (epow B y 2)) x) y

theorem Sys.nf_ecomm {S : Sys G n} (hS : S.Good) (x y : Elt n) :
    (S.nf x)⁻¹ * (S.nf y)⁻¹ * S.nf x * S.nf y = S.nf (ecomm S.B x y) := by
  rw [Sys.nf_inv hS, Sys.nf_inv hS, Sys.nf_mul hS, Sys.nf_mul hS, Sys.nf_mul hS]
  rfl

theorem secN3_single : ∀ (n : ℕ) (s : Fin n → G) (i : Fin n), secN3 n s (Pi.single i 1) = s i
  | 0, _, i => i.elim0
  | n + 1, s, i => by
    rw [secN3]
    refine Fin.cases ?_ (fun j => ?_) i
    · have h : (fun k : Fin n => (Pi.single (0 : Fin (n + 1)) (1 : ZMod 3) : Fin (n + 1) → ZMod 3)
          k.succ) = 0 := by
        funext k; simp [Fin.succ_ne_zero]
      rw [h, secN3_zero, mul_one, Pi.single_eq_same, ZMod.val_one, pow_one]
    · have h : (fun k : Fin n => (Pi.single j.succ (1 : ZMod 3) : Fin (n + 1) → ZMod 3) k.succ) =
          Pi.single j 1 := by
        funext k; simp [Pi.single_apply, Fin.succ_inj]
      rw [h, secN3_single n _ j]
      simp [(Fin.succ_ne_zero j).symm]

theorem isAct_one (S : Sys G n) : IsAct S 1 ((fun i => (Pi.single i 1, 0)), 1) := by
  refine ⟨fun i => ?_, ?_⟩
  · rw [inv_one, one_mul, mul_one, Sys.nf, secN3_single]
    simp
  · rw [inv_one, one_mul, mul_one]
    exact (pow_one S.z).symm

end Generic

theorem toE_ecomm (B : Mat) (x y : E) :
    toE (_root_.Timmesfeld.M3B.ecomm B x y) = ecomm (toMat B) (toE x) (toE y) := by
  simp only [_root_.Timmesfeld.M3B.ecomm, ecomm, toE_emul, toE_epow]

theorem eeq_sound {x y : E} (h : _root_.Timmesfeld.M3B.eeq x y = true) : toE x = toE y := by
  unfold _root_.Timmesfeld.M3B.eeq at h
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  refine Prod.ext (funext fun i => ?_) (congrArg toZ h.2)
  exact congrArg toZ (h.1 i (List.mem_finRange i))

theorem adEq_sound {D D' : AD} (h : _root_.Timmesfeld.M3B.adEq D D' = true) : toD D = toD D' := by
  unfold _root_.Timmesfeld.M3B.adEq at h
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  refine Prod.ext (funext fun i => eeq_sound (h.1 i (List.mem_finRange i))) (congrArg toZ h.2)

theorem mget_mofFn (f : Fin 12 → Fin 12 → F3) (i j : Fin 12) : mget (mofFn f) i j = f i j := by
  unfold mget mofFn
  rw [ofFn_get!, vget_vofFn]

theorem mget_mOfRows (R : List (List ℕ)) (i j : Fin 12) :
    mget (mOfRows R) i j = Fin.ofNat 3 ((R.getD i.val []).getD j.val 0) := by
  unfold mOfRows
  rw [mget_mofFn]

theorem aget_adOfRows (R : List (List ℕ)) (c : List ℕ) (lam : ℕ) (i : Fin 12) :
    aget (adOfRows R c lam) i = ((mOfRows R)[i.val]!, Fin.ofNat 3 (c.getD i.val 0)) := by
  unfold adOfRows aget
  rw [ofFn_get!]

theorem vfun_row (R : List (List ℕ)) (i : Fin 12) :
    vfun (mOfRows R)[i.val]! = fun j => (((R.getD i.val []).getD j.val 0 : ℕ) : ZMod 3) := by
  funext j
  have h := mget_mOfRows R i j
  unfold mget at h
  exact congrArg toZ h

section Words

variable {G : Type*} [Group G] {n : ℕ}

@[expose] def idD (n : ℕ) : ActD n := ((fun i => (Pi.single i 1, 0)), 1)

theorem IsAct.inv_of_comp {S : Sys G n} (hS : S.Good) {g : G} {D E : ActD n} (h : IsAct S g D)
    (hc : comp S.B E D = idD n) : IsAct S g⁻¹ E := by
  have hrow : ∀ i, subst S.B D (E.1 i) = (Pi.single i 1, 0) := fun i =>
    congrFun (congrArg Prod.fst hc) i
  have hlam : E.2 * D.2 = 1 := congrArg Prod.snd hc
  refine ⟨fun i => ?_, ?_⟩
  · have e := h.conj_nf hS (E.1 i)
    rw [hrow i] at e
    have e2 : S.nf (Pi.single i 1, 0) = S.s i := by
      rw [Sys.nf, secN3_single]; simp
    rw [e2] at e
    rw [inv_inv, ← e]
    group
  · have e : g⁻¹ * S.z ^ E.2.val * g = S.z := by
      rw [← conj_pow_inv, h.2, ← pow_mul, ← pow_val_mul hS.z3, mul_comm D.2 E.2, hlam,
        ZMod.val_one, pow_one]
    rw [inv_inv]
    calc g * S.z * g⁻¹ = g * (g⁻¹ * S.z ^ E.2.val * g) * g⁻¹ := by rw [e]
      _ = S.z ^ E.2.val := by group

@[expose] def evalG (gs : ℕ → G) : _root_.Timmesfeld.M3B.WT → G
  | .gen i => gs i
  | .mul a b => evalG gs a * evalG gs b
  | .pow t k => evalG gs t ^ k

end Words

section Datum

@[expose] noncomputable def tbSys : Sys Gmat 12 := ⟨tbq, tbw, tbM⟩

theorem tbSys_good : tbSys.Good where
  z3 := tbw_pow_three
  zs i := (tbq_mul_tbw i).symm
  s3 := tbq_pow_three
  comm i j := by
    have h := tbCommData.bcomm_q i j
    show tbq i * tbq j = tbq j * tbq i * tbw ^ (tbM i j).val
    rw [← h]
    simp only [CFSG.Monster.B.Pinned.bcomm]
    group

theorem mRows_eq : mRows = tbMRows := rfl

theorem xRows_eq : xRows = tbXRows := rfl

theorem yRows_eq : yRows = tbYRows := rfl

theorem toMat_B0 : toMat (B0 ()) = tbM := by
  funext i j
  rw [toMat, B0, mget_mOfRows, mRows_eq]
  rfl

theorem tbSys_B : tbSys.B = toMat (B0 ()) := toMat_B0.symm

theorem tbSys_nf_zero (e : ZMod 3) : tbSys.nf (0, e) = tbw ^ e.val := by
  rw [Sys.nf, secN3_zero, one_mul]; rfl

theorem tbw_eq_bcomm : tbw = (tbq 1)⁻¹ * (tbq 0)⁻¹ * tbq 1 * tbq 0 := by
  have h := tbCommData.bcomm_q 1 0
  have hv : (tbM 1 0).val = 1 := tbM_val
  rw [hv, pow_one] at h
  rw [← h]
  rfl

theorem isAct_of_rows {g : Gmat} {D : AD}
    (hrows : ∀ i, g⁻¹ * tbq i * g = tbSys.nf ((toD D).1 i))
    (hz : _root_.Timmesfeld.M3B.eeq (_root_.Timmesfeld.M3B.ecomm (B0 ()) (aget D 1) (aget D 0))
      (zeroV, D.2) = true) :
    IsAct tbSys g (toD D) := by
  refine ⟨hrows, ?_⟩
  have e1 : g⁻¹ * tbw * g = (g⁻¹ * tbq 1 * g)⁻¹ * (g⁻¹ * tbq 0 * g)⁻¹ * (g⁻¹ * tbq 1 * g) *
      (g⁻¹ * tbq 0 * g) := by
    rw [tbw_eq_bcomm]; group
  have e2 := eeq_sound hz
  rw [toE_ecomm, toE_zero_pair] at e2
  show g⁻¹ * tbw * g = tbw ^ (toZ D.2).val
  rw [e1, hrows, hrows, Sys.nf_ecomm tbSys_good, tbSys_B]
  show tbSys.nf (ecomm (toMat (B0 ())) (toE (aget D 1)) (toE (aget D 0))) = tbw ^ D.2.val
  rw [e2]
  exact tbSys_nf_zero (toZ D.2)

theorem rows_of_adOfRows {g : Gmat} {R : List (List ℕ)} {c : List ℕ} {lam : ℕ}
    (h : ∀ i : Fin 12, g⁻¹ * tbq i * g =
      (List.ofFn fun j => tbq j ^ (tbMat R i j).val).prod * tbw ^ c.getD i.val 0) (i : Fin 12) :
    g⁻¹ * tbq i * g = tbSys.nf ((toD (adOfRows R c lam)).1 i) := by
  rw [h i]
  show _ = secN3 12 tbq (vfun (aget (adOfRows R c lam) i).1) *
    tbw ^ (toZ (aget (adOfRows R c lam) i).2).val
  rw [aget_adOfRows, vfun_row, secN3_eq_prod]
  congr 1
  show tbw ^ c.getD i.val 0 = tbw ^ (c.getD i.val 0 % 3)
  rw [pow_mod_three tbw_pow_three]

theorem isAct_b₁ : IsAct tbSys tbb₁ (toD (Da ())) :=
  isAct_of_rows (rows_of_adOfRows (R := xRows) (c := c1) (lam := 2) fun i => tbb₁_conj i)
    (by decide +kernel)

theorem isAct_b₂ : IsAct tbSys tbb₂ (toD (Db ())) :=
  isAct_of_rows (rows_of_adOfRows (R := yRows) (c := c2) (lam := 1) fun i => tbb₂_conj i)
    (by decide +kernel)

theorem toD_adOne : toD _root_.Timmesfeld.M3B.adOne = idD 12 := by
  refine Prod.ext (funext fun i => ?_) rfl
  show toE (aget _root_.Timmesfeld.M3B.adOne i) = (Pi.single i 1, 0)
  unfold _root_.Timmesfeld.M3B.adOne aget
  rw [ofFn_get!]
  unfold toE
  rw [vfun_vofFn]
  refine Prod.ext (funext fun j => ?_) rfl
  rcases eq_or_ne i j with rfl | h
  · simp only [ite_true, Pi.single_eq_same]; rfl
  · simp only [h, ite_false, Pi.single_eq_of_ne (Ne.symm h)]; rfl

theorem isAct_adOne : IsAct tbSys 1 (toD _root_.Timmesfeld.M3B.adOne) := by
  rw [toD_adOne]; exact isAct_one tbSys

theorem isAct_q (j : Fin 12) : IsAct tbSys (tbq j) (toD (_root_.Timmesfeld.M3B.adQ (B0 ()) j)) := by
  refine ⟨fun i => ?_, ?_⟩
  · have hrow : (toD (_root_.Timmesfeld.M3B.adQ (B0 ()) j)).1 i = (Pi.single i 1, tbM i j) := by
      show toE (aget (_root_.Timmesfeld.M3B.adQ (B0 ()) j) i) = _
      unfold _root_.Timmesfeld.M3B.adQ aget
      rw [ofFn_get!]
      unfold toE
      rw [vfun_vofFn]
      refine Prod.ext (funext fun k => ?_) ?_
      · rcases eq_or_ne i k with rfl | h
        · simp only [ite_true, Pi.single_eq_same]; rfl
        · simp only [h, ite_false, Pi.single_eq_of_ne (Ne.symm h)]; rfl
      · show toZ (mget (B0 ()) i j) = tbM i j
        rw [← toMat_B0]; rfl
    rw [hrow, Sys.nf, secN3_single]
    have h : tbq i * tbq j = tbq j * tbq i * tbw ^ (tbM i j).val := tbSys_good.comm i j
    show (tbq j)⁻¹ * tbq i * tbq j = tbq i * tbw ^ (tbM i j).val
    calc (tbq j)⁻¹ * tbq i * tbq j = (tbq j)⁻¹ * (tbq i * tbq j) := by group
      _ = (tbq j)⁻¹ * (tbq j * tbq i * tbw ^ (tbM i j).val) := by rw [h]
      _ = tbq i * tbw ^ (tbM i j).val := by group
  · show (tbq j)⁻¹ * tbw * tbq j = tbw ^ (toZ 1).val
    rw [toZ_one, ZMod.val_one, pow_one]
    have := tbq_mul_tbw j
    calc (tbq j)⁻¹ * tbw * tbq j = (tbq j)⁻¹ * (tbw * tbq j) := by group
      _ = (tbq j)⁻¹ * (tbq j * tbw) := by rw [this]
      _ = tbw := by group

@[expose] noncomputable def letterG (i : ℕ) : Gmat :=
  if i = 0 then tbb₁ else if i = 1 then tbb₂ else if i = 2 then tbb₁⁻¹ else if i = 3 then tbb₂⁻¹
  else if h : i - 4 < 12 then tbq ⟨i - 4, h⟩ else 1

theorem isAct_letter (hinv : letterInvCheck () = true) (i : ℕ) :
    IsAct tbSys (letterG i) (toD ((LA ()).getD i _root_.Timmesfeld.M3B.adOne)) := by
  unfold letterInvCheck at hinv
  simp only [Bool.and_eq_true] at hinv
  have hc : ∀ {E D : AD}, _root_.Timmesfeld.M3B.adEq (_root_.Timmesfeld.M3B.comp (B0 ()) E D)
      _root_.Timmesfeld.M3B.adOne = true → comp tbSys.B (toD E) (toD D) = idD 12 := by
    intro E D h
    rw [tbSys_B, ← toD_comp, adEq_sound h, toD_adOne]
  rcases i with _ | _ | _ | _ | i
  · exact isAct_b₁
  · exact isAct_b₂
  · exact isAct_b₁.inv_of_comp tbSys_good (hc hinv.1)
  · exact isAct_b₂.inv_of_comp tbSys_good (hc hinv.2)
  · have hne : i + 4 ≠ 0 ∧ i + 4 ≠ 1 ∧ i + 4 ≠ 2 ∧ i + 4 ≠ 3 := by omega
    by_cases hi : i < 12
    · have h1 : letterG (i + 4) = tbq ⟨i, hi⟩ := by
        unfold letterG
        rw [ite_eq_right hne.1, ite_eq_right hne.2.1, ite_eq_right hne.2.2.1,
          ite_eq_right hne.2.2.2, dite_eq_left (by omega)]
        congr 1
      have h2 : (LA ()).getD (i + 4) _root_.Timmesfeld.M3B.adOne =
          _root_.Timmesfeld.M3B.adQ (B0 ()) ⟨i, hi⟩ := by
        unfold LA _root_.Timmesfeld.M3B.letterAD
        simp [Array.getD]
        rw [dite_eq_left (by omega)]
      rw [h1, h2]
      exact isAct_q ⟨i, hi⟩
    · have h1 : letterG (i + 4) = 1 := by
        unfold letterG
        rw [ite_eq_right hne.1, ite_eq_right hne.2.1, ite_eq_right hne.2.2.1,
          ite_eq_right hne.2.2.2, dite_eq_right (by omega)]
      have h2 : (LA ()).getD (i + 4) _root_.Timmesfeld.M3B.adOne = _root_.Timmesfeld.M3B.adOne := by
        unfold LA _root_.Timmesfeld.M3B.letterAD
        simp [Array.getD]
        omega
      rw [h1, h2]
      exact isAct_adOne

theorem isAct_adPow {g : Gmat} {D : AD} (h : IsAct tbSys g (toD D)) :
    ∀ k, IsAct tbSys (g ^ k) (toD (_root_.Timmesfeld.M3B.adPow (B0 ()) D k))
  | 0 => by rw [pow_zero]; exact isAct_adOne
  | k + 1 => by
    rw [pow_succ, _root_.Timmesfeld.M3B.adPow, toD_comp, ← tbSys_B]
    exact (isAct_adPow h k).mul tbSys_good h

theorem isAct_evalG (hinv : letterInvCheck () = true) :
    ∀ t : _root_.Timmesfeld.M3B.WT,
      IsAct tbSys (evalG letterG t) (toD (_root_.Timmesfeld.M3B.adOf (B0 ()) (LA ()) t))
  | .gen i => isAct_letter hinv i
  | .mul a b => by
    rw [evalG, _root_.Timmesfeld.M3B.adOf, toD_comp, ← tbSys_B]
    exact (isAct_evalG hinv a).mul tbSys_good (isAct_evalG hinv b)
  | .pow t k => by
    rw [evalG, _root_.Timmesfeld.M3B.adOf]
    exact isAct_adPow (isAct_evalG hinv t) k

end Datum

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF
