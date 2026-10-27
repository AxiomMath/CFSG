module

public import CFSG.LocalAnalysis.ComponentInitial.MonE7Table
public import CFSG.LocalAnalysis.ComponentInitial.MonE7TraceIndex
public import CFSG.LocalAnalysis.ComponentInitial.MonE7TypeA
public import CFSG.YGroups.Exact.Y321

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.MonE7

open CFSG.YGroups (YGroup yGen yRels)
open CFSG.Certificates.CosetEnumeration (evalWord evalWord_nil evalWord_cons)

theorem checkPerm_spec {i r : ℕ} (hi : i < 7) (hr : r < 576) :
    tE i r < 576 ∧ tE i (tE i r) = r := by
  have h := e7_table_checks.1
  simp only [checkPerm, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at h
  exact h i hi r hr

@[expose] def tPerm (i : ℕ) : Equiv.Perm (Fin 576) :=
  if hi : i < 7 then
    { toFun := fun x => ⟨tE i x, (checkPerm_spec hi x.2).1⟩
      invFun := fun x => ⟨tE i x, (checkPerm_spec hi x.2).1⟩
      left_inv := fun x => Fin.ext (checkPerm_spec hi x.2).2
      right_inv := fun x => Fin.ext (checkPerm_spec hi x.2).2 }
  else 1

theorem tPerm_apply {i : ℕ} (hi : i < 7) (x : Fin 576) : (tPerm i x : ℕ) = tE i x := by
  simp [tPerm, hi]

theorem evalWord_tPerm_apply :
    ∀ w : List ℕ, (∀ a ∈ w, a < 7) → ∀ x : Fin 576, ((evalWord tPerm w) x : ℕ) = applyRev w x
  | [], _, x => by simp [evalWord, applyRev]
  | a :: w, hw, x => by
    rw [evalWord_cons, Equiv.Perm.mul_apply, tPerm_apply (hw a (by simp)),
      evalWord_tPerm_apply w (fun b hb => hw b (by simp [hb])) x]
    rfl

theorem tPerm_rels : ∀ w ∈ yRels 3 2 1, evalWord tPerm w = 1 := by
  intro w hw
  have h := e7_table_checks.2.1
  simp only [checkRels, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  ext x
  rw [evalWord_tPerm_apply w (CFSG.YGroups.lt_ngen_of_mem_yRels hw), Equiv.Perm.one_apply,
    h w hw x x.2]

@[expose] def e7Rho : YGroup 3 2 1 →* Equiv.Perm (Fin 576) :=
  CFSG.YGroups.yModelHom tPerm tPerm_rels

theorem e7Rho_yGen {c : ℕ} (hc : c < 7) : e7Rho (yGen 3 2 1 c) = tPerm c :=
  CFSG.YGroups.yModelHom_yGen hc

theorem e7Rho_evalWord (w : List ℕ) (hw : ∀ a ∈ w, a < 7) :
    e7Rho (evalWord (yGen 3 2 1) w) = evalWord tPerm w := by
  induction w with
  | nil => simp [evalWord]
  | cons a w ih =>
    rw [evalWord_cons, map_mul, e7Rho_yGen (hw a (by simp)), ih (fun b hb => hw b (by simp [hb])),
      evalWord_cons]

@[expose] def e7U : Subgroup (YGroup 3 2 1) := Subgroup.closure (yGen 3 2 1 '' Set.Iio 6)

theorem evalWord_replicate_pair (m a b : ℕ) :
    evalWord (yGen 3 2 1) (List.replicate m [a, b]).flatten =
      (yGen 3 2 1 a * yGen 3 2 1 b) ^ m := by
  induction m with
  | zero => simp [evalWord]
  | succ m ih =>
    rw [List.replicate_succ, List.flatten_cons, CFSG.Certificates.CosetEnumeration.evalWord_append,
      ih, pow_succ']
    simp [evalWord, mul_assoc]

theorem pairWord_mem : ∀ a < 7, ∀ b < 7, a < b → CFSG.YGroups.pairWord 3 2 1 a b ∈ yRels 3 2 1 := by
  decide

theorem yGen_pair_pow {a b : ℕ} (ha : a < 7) (hb : b < 7) (hab : a < b) :
    (yGen 3 2 1 a * yGen 3 2 1 b) ^ CFSG.YGroups.pairExp 3 2 1 a b = 1 := by
  rw [← evalWord_replicate_pair]
  exact CFSG.YGroups.evalWord_yGen_of_mem (pairWord_mem a ha b hb hab)

theorem yGen_pair_pow' {a b : ℕ} (ha : a < 7) (hb : b < 7) (hab : a ≠ b) :
    (yGen 3 2 1 a * yGen 3 2 1 b) ^ CFSG.YGroups.pairExp 3 2 1 (min a b) (max a b) = 1 := by
  rcases lt_or_gt_of_ne hab with h | h
  · rw [min_eq_left h.le, max_eq_right h.le]
    exact yGen_pair_pow ha hb h
  · rw [min_eq_right h.le, max_eq_left h.le]
    have h1 := yGen_pair_pow hb ha h
    have h2 : yGen 3 2 1 a * yGen 3 2 1 b = (yGen 3 2 1 b * yGen 3 2 1 a)⁻¹ := by
      rw [mul_inv_rev, CFSG.YGroups.yGen_inv, CFSG.YGroups.yGen_inv]
    rw [h2, inv_pow, h1, inv_one]

theorem chainE_facts :
    (∀ k < 6, chainE k < 6) ∧ (∀ k < 6, ∀ j < 6, chainE k = chainE j → k = j) ∧
    (∀ k < 5, CFSG.YGroups.pairExp 3 2 1 (min (chainE k) (chainE (k + 1)))
      (max (chainE k) (chainE (k + 1))) = 3) ∧
    (∀ k < 6, ∀ j < 6, k + 2 ≤ j → CFSG.YGroups.pairExp 3 2 1 (min (chainE k) (chainE j))
      (max (chainE k) (chainE j)) = 2) := by
  decide

theorem phi_rels : ∀ r ∈ typeARels 6,
    FreeGroup.lift (fun k : Fin 6 => yGen 3 2 1 (chainE k)) r = 1 := by
  obtain ⟨hlt, hinj, h3, h2⟩ := chainE_facts
  rintro r (⟨i, rfl⟩ | ⟨i, j, hij, rfl⟩ | ⟨i, j, hij, rfl⟩)
  · rw [map_pow, FreeGroup.lift_apply_of, pow_two, CFSG.YGroups.yGen_mul_self]
  · rw [map_pow, map_mul, FreeGroup.lift_apply_of, FreeGroup.lift_apply_of]
    have hk : (i : ℕ) < 5 := by omega
    have hj : (j : ℕ) = i + 1 := hij
    have hne : chainE i ≠ chainE j := fun h => by
      have := hinj i i.2 j j.2 h
      omega
    have := yGen_pair_pow' (by have := hlt i i.2; omega) (by have := hlt j j.2; omega) hne
    rwa [hj, h3 i hk, ← hj] at this
  · rw [map_pow, map_mul, FreeGroup.lift_apply_of, FreeGroup.lift_apply_of]
    have hne : chainE i ≠ chainE j := fun h => by
      have := hinj i i.2 j j.2 h
      omega
    have := yGen_pair_pow' (by have := hlt i i.2; omega) (by have := hlt j j.2; omega) hne
    rwa [h2 i i.2 j j.2 hij] at this

@[expose] def e7Phi : TypeA 6 →* YGroup 3 2 1 := PresentedGroup.toGroup phi_rels

theorem e7Phi_sA (k : Fin 6) : e7Phi (sA k) = yGen 3 2 1 (chainE k) :=
  PresentedGroup.toGroup.of _

theorem range_e7Phi : e7Phi.range = e7U := by
  have hset : Set.range (fun k : Fin 6 => yGen 3 2 1 (chainE k)) = yGen 3 2 1 '' Set.Iio 6 := by
    obtain ⟨hlt, hinj, -, -⟩ := chainE_facts
    have hsurj : ∀ c < 6, ∃ k : Fin 6, chainE k = c := by decide
    ext g
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨chainE k, hlt k k.2, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      obtain ⟨k, hk⟩ := hsurj c hc
      exact ⟨k, by simp only; rw [hk]⟩
  rw [MonoidHom.range_eq_map, ← closure_range_sA, MonoidHom.map_closure, e7U, ← hset,
    ← Set.range_comp]
  congr 2
  funext k
  exact e7Phi_sA k

theorem toPerm_bijective (m : ℕ) : Function.Bijective (toPerm m) := by
  obtain ⟨hfin, hle⟩ := card_typeA_le m
  have hcard : Nat.card (Equiv.Perm (Fin (m + 1))) = (m + 1).factorial := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  exact (toPerm_surjective m).bijective_of_nat_card_le (hcard ▸ hle)

theorem oE_lt : ∀ x < 7, oE x < 576 := by decide

theorem oE_inj : ∀ x < 7, ∀ y < 7, oE x = oE y → x = y := by decide

@[expose] def oF (x : Fin 7) : Fin 576 := ⟨oE x, oE_lt x x.2⟩

theorem oF_injective : Function.Injective oF := fun x y h =>
  Fin.ext (oE_inj x x.2 y y.2 (congrArg Fin.val h))

theorem swap_val : ∀ (k : Fin 6) (x : Fin 7),
    ((Equiv.swap k.castSucc k.succ x : Fin 7) : ℕ) = swapNat k x := by
  decide

theorem checkOrbit_spec {k x : ℕ} (hk : k < 6) (hx : x < 7) :
    tE (chainE k) (oE x) = oE (swapNat k x) := by
  have h := e7_table_checks.2.2.2.2.1
  simp only [checkOrbit, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact h k hk x hx

theorem chainE_lt {k : ℕ} (hk : k < 6) : chainE k < 7 := by
  have := chainE_facts.1 k hk
  omega

theorem rho_phi_oE (a : TypeA 6) (x : Fin 7) :
    e7Rho (e7Phi a) (oF x) = oF (toPerm 6 a x) := by
  have ha : a ∈ Subgroup.closure (Set.range (sA (m := 6))) := by
    rw [closure_range_sA]; trivial
  induction ha using Subgroup.closure_induction generalizing x with
  | mem y hy =>
    obtain ⟨k, rfl⟩ := hy
    apply Fin.ext
    rw [e7Phi_sA, e7Rho_yGen (chainE_lt k.2), tPerm_apply (chainE_lt k.2), toPerm_sA, adjSwap]
    simp only [oF]
    rw [checkOrbit_spec k.2 x.2, swap_val]
  | one => simp
  | mul y z _ _ hy hz =>
    rw [map_mul, map_mul, Equiv.Perm.mul_apply, hz, hy, map_mul, Equiv.Perm.mul_apply]
  | inv y _ hy =>
    have h1 := hy (toPerm 6 y⁻¹ x)
    rw [← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one, Equiv.Perm.one_apply] at h1
    rw [map_inv, map_inv, Equiv.Perm.inv_eq_iff_eq, h1]

theorem rhoPhi_injective : Function.Injective (e7Rho.comp e7Phi) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have ha' : e7Rho (e7Phi a) = 1 := ha
  have h : toPerm 6 a = 1 := Equiv.ext fun x => by
    have h1 := rho_phi_oE a x
    rw [ha', Equiv.Perm.one_apply] at h1
    exact (oF_injective h1).symm
  exact (toPerm_bijective 6).1 (h.trans (map_one _).symm)

theorem e7Phi_injective : Function.Injective e7Phi :=
  Function.Injective.of_comp (f := e7Rho) rhoPhi_injective

theorem card_e7U : Nat.card e7U = 5040 := by
  rw [← range_e7Phi, ← Nat.card_congr (MonoidHom.ofInjective e7Phi_injective).toEquiv]
  obtain ⟨-, -, h⟩ := type_A_coxeter_normal_form 6
  rw [h]
  rfl

@[expose] def e7UEquiv : e7U ≃* Equiv.Perm (Fin 7) :=
  ((MulEquiv.subgroupCongr range_e7Phi).symm.trans
    (MonoidHom.ofInjective e7Phi_injective).symm).trans
    (MulEquiv.ofBijective (toPerm 6) (toPerm_bijective 6))

theorem index_e7U : e7U.index = 576 := by
  have h := e7U.card_mul_index
  rw [card_e7U, CFSG.YGroups.card_y321] at h
  omega

theorem checkFix_spec {j : ℕ} (hj : j < 6) : tE j 0 = 0 := by
  have h := e7_table_checks.2.2.1
  simp only [checkFix, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact h j hj

theorem checkTree_spec {r : ℕ} (hr0 : 0 < r) (hr : r < 576) :
    parE r < r ∧ labE r < 7 ∧ tE (labE r) (parE r) = r := by
  have h := e7_table_checks.2.2.2.1
  simp only [checkTree, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h (r - 1) (by omega)
  rw [Nat.sub_add_cancel hr0] at h1 h2 h3
  exact ⟨h1, h2, h3⟩

theorem exists_rho_apply_zero : ∀ r : ℕ, (hr : r < 576) →
    ∃ g : YGroup 3 2 1, e7Rho g 0 = ⟨r, hr⟩ := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro hr
    rcases Nat.eq_zero_or_pos r with rfl | hr0
    · exact ⟨1, by rw [map_one, Equiv.Perm.one_apply]; rfl⟩
    · obtain ⟨h1, h2, h3⟩ := checkTree_spec hr0 hr
      obtain ⟨g, hg⟩ := ih (parE r) h1 (by omega)
      refine ⟨yGen 3 2 1 (labE r) * g, Fin.ext ?_⟩
      rw [map_mul, Equiv.Perm.mul_apply, hg, e7Rho_yGen h2, tPerm_apply h2]
      exact h3

theorem e7U_le_stab : ∀ g ∈ e7U, e7Rho g 0 = 0 := by
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨j, hj, rfl⟩ := hy
    have hj' : j < 6 := hj
    apply Fin.ext
    rw [e7Rho_yGen (by omega), tPerm_apply (by omega)]
    exact checkFix_spec hj'
  | one => rw [map_one, Equiv.Perm.one_apply]
  | mul y z _ _ hy hz => rw [map_mul, Equiv.Perm.mul_apply, hz, hy]
  | inv y _ hy => rw [map_inv, Equiv.Perm.inv_eq_iff_eq, hy]

theorem mem_e7U_iff (g : YGroup 3 2 1) : g ∈ e7U ↔ e7Rho g 0 = 0 := by
  let _ : MulAction (YGroup 3 2 1) (Fin 576) := MulAction.compHom (Fin 576) e7Rho
  have : Finite (YGroup 3 2 1) := CFSG.YGroups.y321.1
  have horbit : MulAction.orbit (YGroup 3 2 1) (0 : Fin 576) = Set.univ := by
    refine Set.eq_univ_of_forall fun r => ?_
    obtain ⟨g, hg⟩ := exists_rho_apply_zero r r.2
    exact ⟨g, hg⟩
  have hidx := MulAction.index_stabilizer (YGroup 3 2 1) (0 : Fin 576)
  rw [horbit, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at hidx
  have hcard := (MulAction.stabilizer (YGroup 3 2 1) (0 : Fin 576)).card_mul_index
  rw [hidx, CFSG.YGroups.card_y321] at hcard
  have hle : e7U ≤ MulAction.stabilizer (YGroup 3 2 1) (0 : Fin 576) := fun g hg =>
    MulAction.mem_stabilizer_iff.2 (e7U_le_stab g hg)
  rw [Subgroup.eq_of_le_of_card_ge hle (by rw [card_e7U]; omega)]
  exact MulAction.mem_stabilizer_iff

theorem e7Rho_injective : Function.Injective e7Rho := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hU : g ∈ e7U := (mem_e7U_iff g).2 (by rw [hg, Equiv.Perm.one_apply])
  rw [← range_e7Phi] at hU
  obtain ⟨a, rfl⟩ := hU
  have h : toPerm 6 a = 1 := Equiv.ext fun x => by
    have h1 := rho_phi_oE a x
    rw [hg, Equiv.Perm.one_apply] at h1
    exact (oF_injective h1).symm
  rw [(toPerm_bijective 6).1 (h.trans (map_one _).symm), map_one]

@[expose] def cosetRow : Quotient (QuotientGroup.rightRel e7U) → Fin 576 :=
  Quotient.lift (fun x => e7Rho x⁻¹ 0) (fun x y hxy => by
    have h1 := e7U_le_stab _ (e7U.inv_mem (QuotientGroup.rightRel_apply.1 hxy))
    have h2 : y⁻¹ = x⁻¹ * (y * x⁻¹)⁻¹ := by group
    change e7Rho x⁻¹ 0 = e7Rho y⁻¹ 0
    rw [h2, map_mul, Equiv.Perm.mul_apply, h1])

theorem cosetRow_mk (x : YGroup 3 2 1) :
    cosetRow (Quotient.mk _ x) = e7Rho x⁻¹ 0 := rfl

theorem cosetRow_rmul (q : Quotient (QuotientGroup.rightRel e7U)) (g : YGroup 3 2 1) :
    cosetRow (rmul e7U q g) = e7Rho g⁻¹ (cosetRow q) := by
  induction q using Quotient.inductionOn with
  | h x => rw [rmul_mk, cosetRow_mk, cosetRow_mk, mul_inv_rev, map_mul, Equiv.Perm.mul_apply]

theorem cosetRow_bijective : Function.Bijective cosetRow := by
  constructor
  · intro q q' h
    induction q using Quotient.inductionOn with
    | h x =>
      induction q' using Quotient.inductionOn with
      | h y =>
        rw [cosetRow_mk, cosetRow_mk] at h
        refine Quotient.sound (QuotientGroup.rightRel_apply.2 ((mem_e7U_iff _).2 ?_))
        rw [map_mul, Equiv.Perm.mul_apply, h, ← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel,
          map_one, Equiv.Perm.one_apply]
  · intro r
    obtain ⟨g, hg⟩ := exists_rho_apply_zero r r.2
    exact ⟨Quotient.mk _ g⁻¹, by rw [cosetRow_mk, inv_inv, hg]⟩

theorem cosetRow_rmul_yGen (q : Quotient (QuotientGroup.rightRel e7U)) {i : ℕ} (hi : i < 7) :
    (cosetRow (rmul e7U q (yGen 3 2 1 i)) : ℕ) = tE i (cosetRow q) := by
  rw [cosetRow_rmul, CFSG.YGroups.yGen_inv, e7Rho_yGen hi, tPerm_apply hi]

theorem eq_one_of_rmul_eq {g : YGroup 3 2 1}
    (hg : ∀ q : Quotient (QuotientGroup.rightRel e7U), rmul e7U q g = q) : g = 1 := by
  have h : e7Rho g⁻¹ = 1 := Equiv.ext fun r => by
    obtain ⟨q, rfl⟩ := cosetRow_bijective.2 r
    rw [← cosetRow_rmul, hg, Equiv.Perm.one_apply]
  rw [← inv_inv g, e7Rho_injective (h.trans (map_one _).symm), inv_one]

@[expose] def e7f : YGroup 3 2 1 := evalWord (yGen 3 2 1) fWord

theorem evalWord_replicate (m : ℕ) (w : List ℕ) :
    evalWord (yGen 3 2 1) (List.replicate m w).flatten = evalWord (yGen 3 2 1) w ^ m := by
  induction m with
  | zero => simp [evalWord]
  | succ m ih =>
    rw [List.replicate_succ, List.flatten_cons, CFSG.Certificates.CosetEnumeration.evalWord_append,
      ih, pow_succ']

theorem e7f_eq : e7f = (yGen 3 2 1 0 * yGen 3 2 1 1 * yGen 3 2 1 2 * yGen 3 2 1 3 *
    yGen 3 2 1 4 * yGen 3 2 1 5 * yGen 3 2 1 6) ^ 9 := by
  have h : List.range 7 = [0, 1, 2, 3, 4, 5, 6] := rfl
  rw [e7f, fWord, evalWord_replicate, h]
  simp only [evalWord_cons, evalWord_nil, mul_one, mul_assoc]

theorem fWord_lt : ∀ a ∈ fWord, a < 7 := by decide

theorem checkF_spec {r : ℕ} (hr : r < 576) :
    fE r < 576 ∧ applyRev fWord r = fE r ∧ fE (fE r) = r ∧
      ∀ i < 7, fE (tE i r) = tE i (fE r) := by
  have h := e7_table_checks.2.2.2.2.2.1
  simp only [checkF, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h r hr
  exact ⟨h1, h2, h3, h4⟩

theorem e7Rho_e7f_apply (x : Fin 576) : (e7Rho e7f x : ℕ) = fE x := by
  rw [e7f, e7Rho_evalWord _ fWord_lt, evalWord_tPerm_apply _ fWord_lt, (checkF_spec x.2).2.1]

theorem rho_f_ne_one : e7Rho e7f ≠ 1 := by
  intro h
  have h1 := e7Rho_e7f_apply 0
  rw [h, Equiv.Perm.one_apply] at h1
  have h2 := e7_table_checks.2.2.2.2.2.2
  simp only [checkFne, bne_iff_ne, ne_eq] at h2
  exact h2 h1.symm

theorem rho_f_sq : e7Rho e7f ^ 2 = 1 := by
  ext x
  rw [pow_two, Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
  have h1 := e7Rho_e7f_apply x
  have h2 := e7Rho_e7f_apply (e7Rho e7f x)
  rw [h2, h1, (checkF_spec x.2).2.2.1]

theorem rho_f_comm {i : ℕ} (hi : i < 7) : tPerm i * e7Rho e7f = e7Rho e7f * tPerm i := by
  ext x
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, tPerm_apply hi, e7Rho_e7f_apply,
    e7Rho_e7f_apply, tPerm_apply hi, (checkF_spec x.2).2.2.2 i hi]

theorem e7f_ne_one : e7f ≠ 1 := fun h => rho_f_ne_one (by rw [h, map_one])

theorem e7f_sq : e7f ^ 2 = 1 :=
  e7Rho_injective (by rw [map_pow, map_one]; exact rho_f_sq)

theorem e7f_comm_yGen {i : ℕ} (hi : i < 7) : yGen 3 2 1 i * e7f = e7f * yGen 3 2 1 i :=
  e7Rho_injective (by rw [map_mul, map_mul, e7Rho_yGen hi]; exact rho_f_comm hi)

theorem e7f_mem_center : e7f ∈ Subgroup.center (YGroup 3 2 1) := by
  rw [Subgroup.mem_center_iff]
  intro g
  have hg : g ∈ Subgroup.closure (yGen 3 2 1 '' Set.Iio (CFSG.YGroups.ngen 3 2 1)) := by
    rw [CFSG.YGroups.closure_yGen]; trivial
  induction hg using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨i, hi, rfl⟩ := hy
    exact e7f_comm_yGen hi
  | one => rw [one_mul, mul_one]
  | mul y z _ _ hy hz => rw [mul_assoc, hz, ← mul_assoc, hy, mul_assoc]
  | inv y _ hy =>
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hy, mul_assoc, mul_inv_cancel, mul_one]

theorem orderOf_e7f : orderOf e7f = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime e7f_sq e7f_ne_one

theorem e7_exact_order_and_central_involution :
    Nonempty (e7U ≃* Equiv.Perm (Fin 7)) ∧ e7U.index = 576 ∧
      Nat.card (YGroup 3 2 1) = 2903040 ∧
      (∃ e : Quotient (QuotientGroup.rightRel e7U) ≃ Fin 576, e (Quotient.mk _ 1) = 0 ∧
        ∀ q, ∀ i < 7, (e (rmul e7U q (yGen 3 2 1 i)) : ℕ) = tE i (e q)) ∧
      (∀ g : YGroup 3 2 1, (∀ q, rmul e7U q g = q) → g = 1) ∧
      (yGen 3 2 1 0 * yGen 3 2 1 1 * yGen 3 2 1 2 * yGen 3 2 1 3 * yGen 3 2 1 4 *
          yGen 3 2 1 5 * yGen 3 2 1 6) ^ 9 ∈ Subgroup.center (YGroup 3 2 1) ∧
      orderOf ((yGen 3 2 1 0 * yGen 3 2 1 1 * yGen 3 2 1 2 * yGen 3 2 1 3 * yGen 3 2 1 4 *
          yGen 3 2 1 5 * yGen 3 2 1 6) ^ 9) = 2 := by
  rw [← e7f_eq]
  refine ⟨⟨e7UEquiv⟩, index_e7U, CFSG.YGroups.card_y321,
    ⟨Equiv.ofBijective cosetRow cosetRow_bijective, ?_, fun q i hi => cosetRow_rmul_yGen q hi⟩,
    fun g hg => eq_one_of_rmul_eq hg, e7f_mem_center, orderOf_e7f⟩
  rw [Equiv.ofBijective_apply, cosetRow_mk, inv_one, map_one, Equiv.Perm.one_apply]

end CFSG.LocalAnalysis.ComponentInitial.MonE7
