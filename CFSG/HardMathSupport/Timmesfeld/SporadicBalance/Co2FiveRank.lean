module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2Five
public import Certificates.Certificate13611
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Core

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.Co2Cert CFSG.RankThree.Native CFSG.Blueprint
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Native

open scoped Matrix

theorem foldl_dot22_zmod (x y : ℕ) (m : ℕ) (init : Bool) :
    (if (List.range m).foldl (fun acc j => acc ^^ (x.testBit j && y.testBit j)) init = true
        then (1 : ZMod 2) else 0) =
      (if init = true then 1 else 0) +
        ∑ j ∈ Finset.range m,
          (if (x.testBit j && y.testBit j) = true then (1 : ZMod 2) else 0) := by
  induction m with
  | zero => cases init <;> simp
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      Finset.sum_range_succ, ← add_assoc, ← ih]
    generalize (List.range m).foldl (fun acc j => acc ^^ (x.testBit j && y.testBit j)) init = b
    cases b <;> cases x.testBit m <;> cases y.testBit m <;> decide

theorem toVecD_dotProduct22 (x y : ℕ) :
    toVecD 22 x ⬝ᵥ toVecD 22 y = if dot22 x y = true then 1 else 0 := by
  unfold dot22
  rw [foldl_dot22_zmod]
  simp only [Bool.false_eq_true, ↓reduceIte, zero_add]
  rw [dotProduct, ← Fin.sum_univ_eq_sum_range
      (fun j => if (x.testBit j && y.testBit j) = true then (1 : ZMod 2) else 0) 22]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [toVecD_apply, toVecD_apply]
  cases x.testBit j.val <;> cases y.testBit j.val <;> simp

theorem rank_sub_one_conj {n : ℕ} {g c ci : Matrix (Fin n) (Fin n) (ZMod 2)} (h : c * ci = 1) :
    (c * g * ci - 1).rank = (g - 1).rank := by
  have e : c * g * ci - 1 = c * (g - 1) * ci := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h]
  rw [e, Matrix.rank_mul_eq_left_of_isUnit_det _ _ (Matrix.isUnit_det_of_left_inverse h),
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ (Matrix.isUnit_det_of_right_inverse h)]

theorem rank_pow_sub_one_le {n : ℕ} (g : Matrix (Fin n) (Fin n) (ZMod 2)) (a : ℕ) :
    (g ^ a - 1).rank ≤ (g - 1).rank := by
  rw [← mul_geom_sum]
  exact Matrix.rank_mul_le_left _ _

theorem rank_pow_sub_one_eq {n : ℕ} {g : Matrix (Fin n) (Fin n) (ZMod 2)} {a b : ℕ}
    (hb : (g ^ a) ^ b = g) : (g ^ a - 1).rank = (g - 1).rank := by
  refine le_antisymm (rank_pow_sub_one_le g a) ?_
  conv_lhs => rw [← hb]
  exact rank_pow_sub_one_le _ b

theorem rank_co2_eq_of_conj {σ τ : NativeSporadic.Co2} (g : NativeSporadic.Co2)
    (h : g * σ * g⁻¹ = τ) : (σ.val.val - 1).rank = (τ.val.val - 1).rank := by
  have e : τ.val.val = g.val.val * σ.val.val * (g⁻¹).val.val := by
    rw [← h]
    rfl
  have hg : g.val.val * (g⁻¹).val.val = 1 := by
    show ((g * g⁻¹ : NativeSporadic.Co2) : Matrix (Fin 22) (Fin 22) (ZMod 2)) = 1
    rw [mul_inv_cancel]
    rfl
  rw [e, rank_sub_one_conj hg]

theorem rank_co2_pow_eq {σ : NativeSporadic.Co2} (hσ : orderOf σ = 5) {a : ℕ}
    (ha : ¬ 5 ∣ a) : ((σ ^ a).val.val - 1).rank = (σ.val.val - 1).rank := by
  obtain ⟨b, hb⟩ : ∃ b, (σ ^ a) ^ b = σ := by
    refine ⟨a ^ 3, ?_⟩
    rw [← pow_mul]
    conv_rhs => rw [← pow_one σ]
    rw [pow_eq_pow_iff_modEq, hσ]
    have h4 : (a * a ^ 3) % 5 = 1 := by
      have hr : a % 5 < 5 := Nat.mod_lt _ (by norm_num)
      have hr0 : a % 5 ≠ 0 := fun h0 => ha (Nat.dvd_of_mod_eq_zero h0)
      rw [Nat.mul_mod, Nat.pow_mod]
      interval_cases (a % 5) <;> simp_all
    exact h4
  have hb' : ((σ.val.val) ^ a) ^ b = σ.val.val := by
    have := congrArg (fun u : NativeSporadic.Co2 => u.val.val) hb
    simpa using this
  have e : (σ ^ a).val.val = σ.val.val ^ a := by simp
  rw [e]
  exact rank_pow_sub_one_eq hb'

section Lines


theorem co2FiveLine_mem (j : Fin 31) : co2FiveLine j ∈ co2P := by
  obtain ⟨⟨hQP, -, -, -⟩, ⟨hlines, -⟩, -⟩ := R3E_Co2_full_five_centralizer_structures
  have h : Subgroup.zpowers (co2FiveLine j) ∈
      {H : Subgroup (Equiv.Perm (Fin 2300)) | H ≤ co2FiveQ ∧ Nat.card H = 5} := by
    rw [hlines]
    exact ⟨j, rfl⟩
  exact hQP (h.1 (Subgroup.mem_zpowers _))

@[expose] noncomputable def co2LineElt (j : Fin 31) : NativeSporadic.Co2 :=
  co2PermEquiv.symm ⟨co2FiveLine j, co2FiveLine_mem j⟩

theorem co2PermEquiv_co2LineElt (j : Fin 31) :
    (co2PermEquiv (co2LineElt j) : Equiv.Perm (Fin 2300)) = co2FiveLine j := by
  rw [co2LineElt, MulEquiv.apply_symm_apply]

theorem sub_one_mulVec_co2Vec (j : Fin 31) (i : Fin 2300) :
    ((co2LineElt j).val.val - 1) *ᵥ co2Vec i = toVecD 22 (co2LineDiff j i) := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← co2Vec_permEquiv, co2PermEquiv_co2LineElt]
  have hrep := (rep_co2FiveLine j).apply i.2
  set k := co2FiveLine j i with hk
  have hk' : (co2FiveLineArr j)[(i : ℕ)]! = (k : ℕ) := by rw [hrep]
  rw [co2Vec_eq k.2, co2Vec_eq i.2, co2LineDiff, hk', toVecD_xor, sub_eq_add_neg]
  congr 1
  funext c
  exact ZMod.neg_eq_self_mod_two _

theorem le_rank_of_check (j : Fin 31) {idx dual : List ℕ}
    (h : co2RankCheckOf j idx dual = true) :
    idx.length ≤ ((co2LineElt j).val.val - 1).rank := by
  unfold co2RankCheckOf at h
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq, List.mem_range,
    decide_eq_true_eq] at h
  obtain ⟨⟨hidx, hlen⟩, hpair⟩ := h
  set m := idx.length with hm
  set A := (co2LineElt j).val.val - 1 with hA
  have hidx' : ∀ l : Fin m, idx.getD l 0 < 2300 := fun l =>
    hidx _ (List.getD_eq_getElem idx 0 l.2 ▸ List.getElem_mem l.2)
  set D : Matrix (Fin m) (Fin 22) (ZMod 2) :=
    Matrix.of fun l c => toVecD 22 (co2LineDiff j (idx.getD l 0)) c with hD
  set U : Matrix (Fin m) (Fin 22) (ZMod 2) :=
    Matrix.of fun l c => co2Vec (idx.getD l 0) c with hU
  set F : Matrix (Fin 22) (Fin m) (ZMod 2) :=
    Matrix.of fun c k => toVecD 22 (dual.getD k 0) c with hF
  have hDU : D = U * Aᵀ := by
    ext l c
    have e := congrFun (sub_one_mulVec_co2Vec j ⟨idx.getD l 0, hidx' l⟩) c
    rw [hD, Matrix.of_apply, ← e, Matrix.mul_apply, Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hU, Matrix.of_apply, Matrix.transpose_apply, mul_comm]
  have hDF : D * F = 1 := by
    ext l k
    rw [Matrix.mul_apply, Matrix.one_apply]
    have e : ∑ c, D l c * F c k = toVecD 22 (dual.getD k 0) ⬝ᵥ
        toVecD 22 (co2LineDiff j (idx.getD l 0)) := by
      rw [dotProduct]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [hD, hF, Matrix.of_apply, Matrix.of_apply, mul_comm]
    rw [e, toVecD_dotProduct22, hpair k k.2 l l.2]
    by_cases hkl : (k : ℕ) = l
    · have : l = k := Fin.ext hkl.symm
      simp [this]
    · have : l ≠ k := fun e => hkl (by rw [e])
      simp [hkl, this]
  calc m = (1 : Matrix (Fin m) (Fin m) (ZMod 2)).rank := by rw [Matrix.rank_one, Fintype.card_fin]
    _ = (D * F).rank := by rw [hDF]
    _ ≤ D.rank := Matrix.rank_mul_le_left D F
    _ = (U * Aᵀ).rank := by rw [hDU]
    _ ≤ Aᵀ.rank := Matrix.rank_mul_le_right U Aᵀ
    _ = A.rank := Matrix.rank_transpose A


theorem le_rank_co2LineElt :
    20 ≤ ((co2LineElt 0).val.val - 1).rank ∧ 16 ≤ ((co2LineElt 1).val.val - 1).rank := by
  have h : co2RankCheck () = true := Certificates.certificate13611
  unfold co2RankCheck at h
  rw [Bool.and_eq_true] at h
  exact ⟨le_rank_of_check 0 h.1, le_rank_of_check 1 h.2⟩

end Lines

section Five


theorem orderOf_co2FiveLine (j : Fin 31) : orderOf (co2FiveLine j) = 5 := by
  obtain ⟨-, ⟨hlines, -⟩, -⟩ := R3E_Co2_full_five_centralizer_structures
  have h : Subgroup.zpowers (co2FiveLine j) ∈
      {H : Subgroup (Equiv.Perm (Fin 2300)) | H ≤ co2FiveQ ∧ Nat.card H = 5} := by
    rw [hlines]
    exact ⟨j, rfl⟩
  rw [← Nat.card_zpowers]
  exact h.2

theorem orderOf_co2LineElt (j : Fin 31) : orderOf (co2LineElt j) = 5 := by
  have e : orderOf (co2LineElt j) = orderOf (⟨co2FiveLine j, co2FiveLine_mem j⟩ : ↥co2P) :=
    @MulEquiv.orderOf_eq ↥co2P _ NativeSporadic.Co2 Units.instMonoid co2PermEquiv.symm _
  rw [e, Subgroup.orderOf_mk, orderOf_co2FiveLine]

theorem exists_conj_pow_co2LineElt {σ : NativeSporadic.Co2} (hσ : orderOf σ = 5) :
    ∃ (r : Fin 2) (a : ℕ) (g : NativeSporadic.Co2), ¬ 5 ∣ a ∧
      g * σ * g⁻¹ = co2LineElt (co2FiveRepLine r) ^ a := by
  obtain ⟨⟨hQP, -, hQcard, -⟩, ⟨hlines, -⟩, htrans, -⟩ :=
    R3E_Co2_full_five_centralizer_structures
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set s : ↥co2P := co2PermEquiv σ with hs
  have hso : orderOf (s : Equiv.Perm (Fin 2300)) = 5 := by
    rw [Subgroup.orderOf_coe, hs, MulEquiv.orderOf_eq, hσ]
  obtain ⟨g, hgP, hgQ⟩ := Co3T.exists_conj_mem_of_full hQP
    (by rw [hQcard, factorization_card_co2P_five]; norm_num) s.2 hso
  set t := g⁻¹ * (s : Equiv.Perm (Fin 2300)) * g with htdef
  have hto : orderOf t = 5 := by
    have := (MulAut.conj g⁻¹ : Equiv.Perm (Fin 2300) ≃* Equiv.Perm (Fin 2300)).orderOf_eq
      (s : Equiv.Perm (Fin 2300))
    simpa [MulAut.conj_apply, htdef, hso] using this
  have hmem : Subgroup.zpowers t ∈
      {H : Subgroup (Equiv.Perm (Fin 2300)) | H ≤ co2FiveQ ∧ Nat.card H = 5} :=
    ⟨(Subgroup.zpowers_le).2 hgQ, by rw [Nat.card_zpowers, hto]⟩
  rw [hlines] at hmem
  obtain ⟨j, hj⟩ := hmem
  obtain ⟨hhP, hconj⟩ := htrans j
  set h := co2FiveTransporter j with hhdef
  set i := co2FiveRecordOf j with hidef
  set xr := co2FiveLine (co2FiveRepLine i) with hxr
  have htx : t ∈ Subgroup.zpowers (co2FiveLine j) := by
    have : t ∈ Subgroup.zpowers t := Subgroup.mem_zpowers t
    rwa [← hj] at this
  obtain ⟨k, hk⟩ : ∃ k : ℕ, co2FiveLine j ^ k = t := by
    have := (mem_powers_iff_mem_zpowers (y := t) (x := co2FiveLine j)).2 htx
    exact this
  have hj5 : orderOf (co2FiveLine j) = 5 := orderOf_co2FiveLine j
  have hk5 : ¬ 5 ∣ k := by
    intro hdvd
    obtain ⟨m, rfl⟩ := hdvd
    rw [pow_mul, ← hj5, pow_orderOf_eq_one, one_pow] at hk
    rw [← hk, orderOf_one] at hto
    omega
  have hcP : g * h ∈ co2P := co2P.mul_mem hgP hhP
  have hxr' : h⁻¹ * co2FiveLine j * h = xr := by
    rw [← hconj]
    group
  have hkey : (g * h)⁻¹ * (s : Equiv.Perm (Fin 2300)) * (g * h) = xr ^ k := by
    calc (g * h)⁻¹ * (s : Equiv.Perm (Fin 2300)) * (g * h) = h⁻¹ * t * h := by
          rw [htdef]; group
      _ = h⁻¹ * co2FiveLine j ^ k * h := by rw [hk]
      _ = (h⁻¹ * co2FiveLine j * h) ^ k := by
          have e := conj_pow (a := h⁻¹) (b := co2FiveLine j) (i := k)
          rw [inv_inv] at e
          exact e.symm
      _ = xr ^ k := by rw [hxr']
  set c : ↥co2P := ⟨g * h, hcP⟩ with hc
  have hkeyP : c⁻¹ * s * c = (⟨xr, co2FiveLine_mem _⟩ : ↥co2P) ^ k := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow]
    exact hkey
  refine ⟨i, k, (co2PermEquiv.symm c)⁻¹, hk5, ?_⟩
  have e := congrArg co2PermEquiv.symm hkeyP
  rw [map_mul, map_mul, map_inv, map_pow, hs, MulEquiv.symm_apply_apply] at e
  rw [inv_inv, co2LineElt, ← e]

theorem sixteen_le_rank_co2 {σ : NativeSporadic.Co2}
    (hσ : orderOf σ = 5) : 16 ≤ (σ.val.val - 1).rank := by
  obtain ⟨r, a, g, ha, hg⟩ := exists_conj_pow_co2LineElt hσ
  rw [rank_co2_eq_of_conj g hg, rank_co2_pow_eq (orderOf_co2LineElt _) ha]
  obtain ⟨h0, h1⟩ := le_rank_co2LineElt
  fin_cases r
  · exact le_trans (by norm_num) h0
  · exact h1

theorem exists_conj_pow_x0_of_central {π : ↥co2P} (hπ : orderOf π = 5) {S1 : Subgroup ↥co2P}
    (hS1p : IsPGroup 5 S1) (hcard : 125 ≤ Nat.card S1) (hπS : π ∈ S1)
    (hc : ∀ x ∈ S1, x * π = π * x) :
    ∃ (g : ↥co2P) (k : ℕ), ¬ 5 ∣ k ∧
      g * π * g⁻¹ = (⟨co2FiveLine 0, co2FiveLine_mem 0⟩ : ↥co2P) ^ k := by
  obtain ⟨-, -, -, -, hC0, -, hAC, -, hAcard, -, hcentcard, -, -⟩ :=
    R3E_Co2_full_five_centralizer_structures
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hAP : co2FiveA ≤ co2P := hAC.trans (hC0.le.trans inf_le_right)
  have hfac : (Nat.card ↥co2P).factorization 5 = 3 := factorization_card_co2P_five
  have hS1le : Nat.card S1 ≤ 5 ^ 3 :=
    card_le_of_isPGroup_of_dvd Nat.prime_five hS1p (n := Nat.card ↥co2P) (e := 3)
      (by rw [card_co2P]; norm_num) (Subgroup.card_subgroup_dvd_card _)
  have hS1eq : Nat.card S1 = 5 ^ (Nat.card ↥co2P).factorization 5 := by
    rw [hfac]
    norm_num at hS1le ⊢
    omega
  set A1 : Subgroup ↥co2P := co2FiveA.subgroupOf co2P with hA1
  have hA1card : Nat.card A1 = 5 ^ (Nat.card ↥co2P).factorization 5 := by
    rw [hA1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAP).toEquiv, hAcard, hfac]
    norm_num
  let SS : Sylow 5 ↥co2P := Sylow.ofCard S1 hS1eq
  let AA : Sylow 5 ↥co2P := Sylow.ofCard A1 hA1card
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥co2P SS AA
  have hmem : ∀ y : ↥co2P, g * y * g⁻¹ ∈ A1 ↔ y ∈ S1 := by
    intro y
    have e : (A1 : Subgroup ↥co2P) = ((g • SS : Sylow 5 ↥co2P) : Subgroup ↥co2P) := by
      rw [hg]
      rfl
    rw [e, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
      ← map_inv, MulAut.conj_apply, inv_inv]
    have e2 : g⁻¹ * (g * y * g⁻¹) * g = y := by group
    rw [e2]
    rfl
  set u : ↥co2P := g * π * g⁻¹ with hu
  have huA : (u : Equiv.Perm (Fin 2300)) ∈ co2FiveA := Subgroup.mem_subgroupOf.1 ((hmem π).2 hπS)
  have huC0 : (u : Equiv.Perm (Fin 2300)) ∈ co2FiveC0 := hAC huA
  have hucent : (u : Equiv.Perm (Fin 2300)) ∈
      Subgroup.centralizer (co2FiveA : Set (Equiv.Perm (Fin 2300))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    set a' : ↥co2P := ⟨a, hAP ha⟩
    have ha' : a' ∈ A1 := Subgroup.mem_subgroupOf.2 ha
    have hb : g⁻¹ * a' * g ∈ S1 := by
      rw [← hmem]
      have e : g * (g⁻¹ * a' * g) * g⁻¹ = a' := by group
      rw [e]
      exact ha'
    have hcomm := hc _ hb
    have : a' * u = u * a' := by
      calc a' * u = g * ((g⁻¹ * a' * g) * π) * g⁻¹ := by rw [hu]; group
        _ = g * (π * (g⁻¹ * a' * g)) * g⁻¹ := by rw [hcomm]
        _ = u * a' := by rw [hu]; group
    exact congrArg Subtype.val this
  have hx0C : co2FiveLine 0 ∈ Subgroup.centralizer (co2FiveA : Set (Equiv.Perm (Fin 2300))) ⊓
      co2FiveC0 := by
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have := hAC ha
      rw [hC0] at this
      exact Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 this).1
    · rw [hC0]
      exact Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 rfl, co2FiveLine_mem 0⟩
  have hzp : Subgroup.zpowers (co2FiveLine 0) =
      Subgroup.centralizer (co2FiveA : Set (Equiv.Perm (Fin 2300))) ⊓ co2FiveC0 :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hx0C)
      (by rw [hcentcard, Nat.card_zpowers, orderOf_co2FiveLine])
  have hux : (u : Equiv.Perm (Fin 2300)) ∈ Subgroup.zpowers (co2FiveLine 0) := by
    rw [hzp]
    exact ⟨hucent, huC0⟩
  obtain ⟨k, hk⟩ : ∃ k : ℕ, co2FiveLine 0 ^ k = u :=
    (mem_powers_iff_mem_zpowers (y := (u : Equiv.Perm (Fin 2300)))
      (x := co2FiveLine 0)).2 hux
  have huo : orderOf u = 5 := by
    have := (MulAut.conj g : ↥co2P ≃* ↥co2P).orderOf_eq π
    rw [MulAut.conj_apply] at this
    rw [hu, this, hπ]
  have hk5 : ¬ 5 ∣ k := by
    intro hdvd
    obtain ⟨m, rfl⟩ := hdvd
    rw [pow_mul, ← orderOf_co2FiveLine 0, pow_orderOf_eq_one, one_pow] at hk
    have hu1 : u = 1 := Subtype.ext hk.symm
    rw [hu1, orderOf_one] at huo
    omega
  refine ⟨g, k, hk5, ?_⟩
  apply Subtype.ext
  rw [Subgroup.coe_pow]
  exact hk.symm

@[expose] noncomputable def co2PermHom' : NativeSporadic.Co2 →* ↥co2P := by
  with_reducible_and_instances exact co2PermEquiv.toMonoidHom

theorem co2PermHom'_apply (u : NativeSporadic.Co2) : co2PermHom' u = co2PermEquiv u := rfl

theorem twenty_le_rank_co2 {σ : NativeSporadic.Co2}
    (hσ : orderOf σ = 5) {S : Subgroup NativeSporadic.Co2} (hS : IsPGroup 5 S)
    (hcard : 125 ≤ Nat.card S) (hσS : σ ∈ S) (hc : ∀ x ∈ S, x * σ = σ * x) :
    20 ≤ (σ.val.val - 1).rank := by
  have hinj : Function.Injective co2PermHom' := co2PermEquiv.injective
  have hπo : orderOf (co2PermEquiv σ) = 5 := by
    rw [← co2PermHom'_apply, orderOf_injective co2PermHom' hinj, hσ]
  obtain ⟨g, k, hk5, hg⟩ := exists_conj_pow_x0_of_central hπo (S1 := S.map co2PermHom')
    (hS.map _) (by rw [Subgroup.card_map_of_injective hinj]; exact hcard) ⟨σ, hσS, rfl⟩
    (by
      rintro _ ⟨x, hx, rfl⟩
      rw [co2PermHom'_apply, ← map_mul, ← map_mul, hc x hx])
  have e := congrArg co2PermEquiv.symm hg
  rw [map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply, map_pow] at e
  have e' : co2PermEquiv.symm g * σ * (co2PermEquiv.symm g)⁻¹ = co2LineElt 0 ^ k := e
  rw [rank_co2_eq_of_conj _ e', rank_co2_pow_eq (orderOf_co2LineElt 0) hk5]
  exact le_rank_co2LineElt.1

end Five

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
