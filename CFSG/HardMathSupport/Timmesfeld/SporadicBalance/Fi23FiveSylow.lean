module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Five
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.CommutingPair
public import CFSG.Sporadic.Fi23.Tr.Points
public import Certificates.Certificate16946

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Proving CFSG.Blueprint
  CFSG.Sporadic.Fi23 CFSG.Sporadic.Fi23.Native CFSG.Sporadic.Th.Native CFSG.Perm
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.CommutingPair
open CFSG.Sporadic.Th hiding J a b closure_ab gA gB rows_B_cube

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace Fi23Five


section RepGeneral

variable {G : Type*} [Group G] [MulAction G (Fin 31671)]

theorem eqTab_of_rep_eq {A B : Table} {g : G} (hA : Rep 31671 A g) (hB : Rep 31671 B g) :
    eqTab A B = true := by
  unfold eqTab
  rw [List.all_eq_true]
  intro i hi
  rw [beq_iff_eq, hA i (List.mem_range.1 hi), hB i (List.mem_range.1 hi)]

theorem ne_one_of_rep {T : Table} {g : G} (hT : Rep 31671 T g) (h : eqTab T (idT 31671) = false) :
    g ≠ 1 := by
  intro h1
  rw [h1] at hT
  rw [eqTab_of_rep_eq hT (Rep.idT (by norm_num))] at h
  exact absurd h (by decide)

theorem ne_pow_of_rep {T U : Table} {f g : G} (hT : Rep 31671 T f) (hU : Rep 31671 U g) (k : ℕ)
    (h : eqTab T (powT 31671 k U) = false) : f ≠ g ^ k := by
  intro h1
  rw [h1] at hT
  rw [eqTab_of_rep_eq hT (hU.powT (by norm_num) k)] at h
  exact absurd h (by decide)

end RepGeneral

section Bridge


theorem eqTab_spec {A B : Table} (h : eqTab A B = true) : ∀ i < 31671, ap A i = ap B i := by
  intro i hi
  unfold eqTab at h
  rw [List.all_eq_true] at h
  exact beq_iff_eq.1 (h i (List.mem_range.2 hi))

theorem eqTab_of_rep {A B : Table} {g : CFSG.Sporadic.Fi23.J} (hA : Rep 31671 A g) (hB : Rep 31671 B g) :
    eqTab A B = true := by
  unfold eqTab
  rw [List.all_eq_true]
  intro i hi
  rw [beq_iff_eq, hA i (List.mem_range.1 hi), hB i (List.mem_range.1 hi)]

theorem eq_of_eqTab {A B : Table} {g h : CFSG.Sporadic.Fi23.J} (hA : Rep 31671 A g) (hB : Rep 31671 B h)
    (hAB : eqTab A B = true) : g = h :=
  rep_unique hA fun i hi => by rw [eqTab_spec hAB i hi, hB i hi]

theorem rep_dTable : Rep 31671 (dTable orb) d := Rep.powT (by norm_num) (rep_dWordTab dWord) 7

theorem rep_genTables_neg_two : Rep 31671 (genTables orb (-2)) b⁻¹ := by
  have h := rep_gen (-2)
  have e : genG (-2) = b⁻¹ := by
    unfold genG
    simp only [show (-2 : ℤ) ≠ 1 by decide, show (-2 : ℤ) ≠ -1 by decide,
      show (-2 : ℤ) ≠ 2 by decide, ite_false]
  rwa [e] at h

theorem treeAct_dTable_spec : ∀ k, ∀ m < 31671,
    treeAct orb.par orb.lab orb.alpha orb.beta (dTable orb) (genTables orb (-2)) k m =
      idx 31671 (conjPt k) m :=
  treeAct_spec rep_alpha rep_beta rep_genTables_neg_two rep_dTable a_inv conjPt conjPt_eq

theorem commB_iff {i j : ℕ} (hi : i < 31671) (hj : j < 31671) :
    commB orb (dTable orb) (genTables orb (-2)) i j = true ↔
      conjPt i * conjPt j = conjPt j * conjPt i := by
  rw [conjPt_commute_iff hi hj, act23_spec i j hj]
  unfold commB
  rw [beq_iff_eq, treeAct_dTable_spec i j hj]

theorem rep_treeActTab_dTable (k : ℕ) :
    Rep 31671 (treeActTab orb (dTable orb) (genTables orb (-2)) k) (conjPt k) := by
  intro m hm
  have h := treeAct_dTable_spec k m hm
  have hlt : treeAct orb.par orb.lab orb.alpha orb.beta (dTable orb) (genTables orb (-2)) k m <
      2 ^ 32 := by
    rw [h]; exact (idx_lt _ hm).trans (by norm_num)
  unfold treeActTab
  rw [ap_ofFn _ hm, UInt32.toNat_ofNat', Nat.mod_eq_of_lt hlt, h]

theorem rep_starWordTab_dTable (w : List ℕ) :
    Rep 31671 (starWordTab orb (dTable orb) (genTables orb (-2)) w) (w.map conjPt).prod := by
  induction w with
  | nil => simpa [starWordTab] using Rep.idT (G := J) (n := 31671) (by norm_num)
  | cons k w ih =>
    rw [starWordTab, List.foldr_cons, List.map_cons, List.prod_cons]
    exact (rep_treeActTab_dTable k).compT ih

theorem mem_fixList_iff {W : Table} {w : CFSG.Sporadic.Fi23.J} (hW : Rep 31671 W w) {i : ℕ} (hi : i < 31671) :
    i ∈ fixList W ↔ conjPt i * w = w * conjPt i := by
  unfold fixList
  rw [List.mem_filter, List.mem_range, beq_iff_eq, hW i hi, idx_of_lt w hi]
  constructor
  · rintro ⟨-, h⟩
    have h' : w • (⟨i, hi⟩ : Fin 31671) = ⟨i, hi⟩ := Fin.ext h
    have h2 := (smul_eq_iff w ⟨i, hi⟩ ⟨i, hi⟩).1 h'
    calc conjPt i * w = (w * conjPt i * w⁻¹) * w := by rw [h2]
      _ = w * conjPt i := by group
  · intro h
    refine ⟨hi, ?_⟩
    have h2 : w * conjPt i * w⁻¹ = conjPt i := by rw [← h]; group
    exact congrArg Fin.val ((smul_eq_iff w ⟨i, hi⟩ ⟨i, hi⟩).2 h2)

theorem lt_of_mem_fixList {W : Table} {i : ℕ} (h : i ∈ fixList W) : i < 31671 := by
  unfold fixList at h
  exact List.mem_range.1 (List.mem_filter.1 h).1

theorem graph_of_check {W : Table} {w : CFSG.Sporadic.Fi23.J} (hW : Rep 31671 W w)
    (hg : graphOK (commB orb (dTable orb) (genTables orb (-2))) (fixList W) = true) :
    (∃ e ∈ D23, e * w = w * e) ∧
    (∀ x ∈ D23, x * w = w * x → ∃ y ∈ D23, y * w = w * y ∧ y ≠ x ∧ x * y = y * x) ∧
    (∀ x ∈ D23, x * w = w * x → ∀ y ∈ D23, y * w = w * y → x * y ≠ y * x →
      ∃ z ∈ D23, z * w = w * z ∧ z * x = x * z ∧ z * y = y * z) := by
  unfold graphOK at hg
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, List.any_eq_true,
    Bool.or_eq_true, bne_iff_ne, ne_eq] at hg
  obtain ⟨⟨hne, h1⟩, h2⟩ := hg
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨i, hi⟩ := List.exists_mem_of_ne_nil (fixList W) (by
      intro h0
      rw [h0] at hne
      exact absurd hne (by decide))
    have hilt := lt_of_mem_fixList hi
    exact ⟨conjPt i, conjPt_mem_D23 hilt, (mem_fixList_iff hW hilt).1 hi⟩
  · intro x hx hxw
    obtain ⟨⟨i, hi⟩, rfl⟩ := (isConj_d_iff x).1 hx
    have hiF : i ∈ fixList W := (mem_fixList_iff hW hi).2 hxw
    obtain ⟨j, hjF, hji, hc⟩ := h1 i hiF
    have hjlt := lt_of_mem_fixList hjF
    refine ⟨conjPt j, conjPt_mem_D23 hjlt, (mem_fixList_iff hW hjlt).1 hjF, ?_,
      (commB_iff hi hjlt).1 hc⟩
    intro h
    exact hji (conjPt_injOn hjlt hi h)
  · intro x hx hxw y hy hyw hxy
    obtain ⟨⟨i, hi⟩, rfl⟩ := (isConj_d_iff x).1 hx
    obtain ⟨⟨j, hj⟩, rfl⟩ := (isConj_d_iff y).1 hy
    have hiF : i ∈ fixList W := (mem_fixList_iff hW hi).2 hxw
    have hjF : j ∈ fixList W := (mem_fixList_iff hW hj).2 hyw
    rcases h2 i hiF j hjF with hc | ⟨k, hkF, hki, hkj⟩
    · exact absurd ((commB_iff hi hj).1 hc) hxy
    · have hklt := lt_of_mem_fixList hkF
      exact ⟨conjPt k, conjPt_mem_D23 hklt, (mem_fixList_iff hW hklt).1 hkF,
        ((commB_iff hklt hi).1 hki), ((commB_iff hklt hj).1 hkj)⟩

end Bridge

section Main


theorem fi23Five_parts :
    (∀ k ∈ fivePathOf orb, k < 31671) ∧
    fi23FiveCore orb (dTable orb) (genTables orb (-2)) (eTab orb)
      (starWordTab orb (dTable orb) (genTables orb (-2)) (fivePathOf orb)) = true := by
  have h := Certificates.certificate16946
  unfold fi23FiveOK at h
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1, h.2⟩

@[expose] noncomputable def eFive : CFSG.Sporadic.Fi23.J := wordG genG eLetters

@[expose] noncomputable def fFive : CFSG.Sporadic.Fi23.J := ((fivePathOf orb).map conjPt).prod

theorem rep_eFive : Rep 31671 (eTab orb) eFive :=
  Rep.wordT (by norm_num) eLetters fun l _ => rep_gen l

theorem rep_fFive :
    Rep 31671 (starWordTab orb (dTable orb) (genTables orb (-2)) (fivePathOf orb)) fFive :=
  rep_starWordTab_dTable (fivePathOf orb)

theorem oPrimeCoreTrivialAt_Fi23J_five : OPrimeCoreTrivialAt 5 CFSG.Sporadic.Fi23.J := by
  obtain ⟨-, hc⟩ := fi23Five_parts
  unfold fi23FiveCore at hc
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, List.mem_range,
    Bool.or_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨⟨⟨⟨h5e', he1'⟩, h5f'⟩, hcomm'⟩, hpow'⟩, hgraph⟩ := hc
  have hn : (31671 : ℕ) < 2 ^ 32 := by norm_num
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h5e := eq_of_eqTab (rep_eFive.powT hn 5) (Rep.idT hn) h5e'
  have h5f := eq_of_eqTab (rep_fFive.powT hn 5) (Rep.idT hn) h5f'
  have hcomm := eq_of_eqTab (rep_eFive.compT rep_fFive) (rep_fFive.compT rep_eFive) hcomm'
  have he1 := ne_one_of_rep rep_eFive he1'
  have hpow : ∀ k < 5, fFive ≠ eFive ^ k := fun k hk =>
    ne_pow_of_rep rep_fFive rep_eFive k (hpow' k hk)
  have hQ := card_closure_pair_eq_sq hcomm h5e h5f he1 hpow (by rw [card_J]; norm_num)
  have hQfull : Nat.card (Subgroup.closure ({eFive, fFive} : Set J)) =
      5 ^ (Nat.card (⊤ : Subgroup J)).factorization 5 := by
    rw [hQ, Subgroup.card_top, card_J,
      show (4089470473293004800 : ℕ) = 5 ^ 2 * 163578818931720192 by norm_num,
      factorization_pow_mul Nat.prime_five 2 _ (by norm_num)]
  intro s hs
  obtain ⟨g, -, hgQ⟩ := Co3T.exists_conj_mem_of_full le_top hQfull (Subgroup.mem_top s) hs
  obtain ⟨a, ha, b, hb, hw⟩ := exists_pow_mul_pow_of_mem (by norm_num) hcomm h5e h5f hgQ
  have hwo : orderOf (g⁻¹ * s * g) = 5 := by rw [orderOf_inv_mul_mul, hs]
  have hab : a + b ≠ 0 := by
    intro h0
    have ha0 : a = 0 := by omega
    have hb0 : b = 0 := by omega
    rw [ha0, hb0, pow_zero, pow_zero, mul_one] at hw
    rw [hw, orderOf_one] at hwo
    exact absurd hwo (by norm_num)
  have hW := (rep_eFive.powT hn a).compT (rep_fFive.powT hn b)
  rw [← hw] at hW
  obtain ⟨hT0, hT1, hT2⟩ := graph_of_check hW ((hgraph a ha b hb).resolve_left hab)
  have hbot := gLAPPrimeCoreOf_fi23_five_eq_bot hwo hT0 hT1 hT2
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  have hx' := @conj_mem_gLAPPrimeCoreOf_centralizer J (inferInstance : Group J) 5 g⁻¹ s x hx
  rw [inv_inv, hbot, Subgroup.mem_bot] at hx'
  exact eq_one_of_inv_mul_mul_eq_one hx'

end Main

end Fi23Five

open Fi23Five

theorem sporadicOPrimeHolds_Fi23_five :
    SporadicOPrimeHolds .Fi23 5 := by
  intro S _ _ _ ⟨e⟩
  have e0 : S ≃* NativeSporadic.Fi23 := e
  exact @OPrimeCoreTrivialAt.of_mulEquiv 5 S _ ↥J inferInstance (e0.trans fi23EquivJ)
    oPrimeCoreTrivialAt_Fi23J_five

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
