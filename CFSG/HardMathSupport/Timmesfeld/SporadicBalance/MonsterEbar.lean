module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterEbarInputs
public import CFSG.Monster.Existence.TwoB

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterEbar

open CFSG.Monster CFSG.Monster.B CFSG.Monster.AxisCount CFSG.AGLEmbedding.Norton.MON5_7
  CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.Visible CFSG.Monster.Generated
  CFSG.Monster.B.Rep4371 CFSG.Monster.Existence CFSG.Monster.Griess

@[expose] noncomputable def rhoG (q : Model.Pauli) : Gmat := gw [Native.Gen.rho q]

theorem coe_rhoG (q : Model.Pauli) : ((rhoG q : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB) = rhoEquiv (pauliQ q) := by
  show wordLin [Native.Gen.rho q] = rhoEquiv (pauliQ q)
  rw [wordLin_cons, wordLin_nil, one_mul]
  rfl

theorem rhoG_mul (x y : Model.Pauli) : rhoG (x.mul y) = rhoG y * rhoG x := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, coe_rhoG, coe_rhoG, coe_rhoG, pauliQ_mul, rhoEquiv_mul]

theorem rhoG_one : rhoG (false, 0, 0) = 1 := by
  have h := rhoG_mul (false, 0, 0) (false, 0, 0)
  have e : Model.Pauli.mul (false, 0, 0) (false, 0, 0) = (false, 0, 0) := by decide
  rw [e] at h
  exact mul_left_cancel (h.symm.trans (mul_one _).symm)

theorem rhoG_mem (q : Model.Pauli) : rhoG q ∈ rhoQ.subgroupOf Gmat := by
  rw [Subgroup.mem_subgroupOf, coe_rhoG]
  exact mem_rhoQ.2 ⟨_, rfl⟩

theorem toC_inj_of_lt {a b : ℕ} (ha : a < 4096) (hb : b < 4096) (h : toC a = toC b) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 12
  · have := congrArg (fun c => basisC.repr c ⟨i, hi⟩) h
    simp only [repr_toC_apply] at this
    exact boolZ_injective this
  · have h12 : 4096 ≤ 2 ^ i := by
      calc 4096 = 2 ^ 12 := by norm_num
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (not_lt.1 hi)
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ha h12),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hb h12)]

theorem toD_inj_of_lt {d e : ℕ} (hd : d < 4096) (he : e < 4096) (h : toD d = toD e) : d = e := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 12
  · have := congrArg (fun δ => pair (basisC ⟨i, hi⟩) δ) h
    simp only [pair_basisC_toD] at this
    exact boolZ_injective this
  · have h12 : 4096 ≤ 2 ^ i := by
      calc 4096 = 2 ^ 12 := by norm_num
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (not_lt.1 hi)
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hd h12),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le he h12)]

theorem eq_of_rhoG_eq {x y : Model.Pauli} (hx : validB x = true) (hy : validB y = true)
    (h : rhoG x = rhoG y) : x = y := by
  have h1 : rhoEquiv (pauliQ x) = rhoEquiv (pauliQ y) := by
    rw [← coe_rhoG, ← coe_rhoG, h]
  have h2 : toSC x = toSC y := spinEquiv.injective (rhoEquiv_injective h1)
  simp only [validB, Bool.and_eq_true, decide_eq_true_eq] at hx hy
  obtain ⟨s, a, d⟩ := x
  obtain ⟨t, b, e⟩ := y
  have hs : boolZ s = boolZ t := congrArg SpinCoord.s h2
  have ha : toC a = toC b := congrArg SpinCoord.a h2
  have hd : toD d = toD e := congrArg SpinCoord.δ h2
  have hs' : s = t := boolZ_injective hs
  have ha' : a = b := toC_inj_of_lt hx.1 hy.1 ha
  have hd' : d = e := toD_inj_of_lt hx.2 hy.2 hd
  rw [hs', ha', hd']

theorem validB_mul {x y : Model.Pauli} (hx : validB x = true) (hy : validB y = true) :
    validB (x.mul y) = true := by
  unfold validB at hx hy ⊢
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hx hy ⊢
  have h1 : x.2.1 ^^^ y.2.1 < 2 ^ 12 :=
    Nat.xor_lt_two_pow (by simpa using hx.1) (by simpa using hy.1)
  have h2 : x.2.2 ^^^ y.2.2 < 2 ^ 12 :=
    Nat.xor_lt_two_pow (by simpa using hx.2) (by simpa using hy.2)
  exact ⟨by simpa [Model.Pauli.mul] using h1, by simpa [Model.Pauli.mul] using h2⟩

theorem natCard_rhoQ_subgroupOf_Gmat : Nat.card (rhoQ.subgroupOf Gmat) = 2 ^ 25 := by
  have hle : rhoQ ≤ Gmat := fun f hf => by
    obtain ⟨r, rfl⟩ := mem_rhoQ.1 hf
    exact Hmat_le_Gmat (rhoEquiv_mem_Gvis r)
  have hle' : rhoQ ≤ Gvis := fun f hf => by
    obtain ⟨r, rfl⟩ := mem_rhoQ.1 hf
    exact rhoEquiv_mem_Gvis r
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, ← natCard_rhoQvis,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle').toEquiv]

@[expose] def coordP (t : Bool × Fin 4096 × Fin 4096) : Model.Pauli := (t.1, t.2.1, t.2.2)

theorem validB_coordP (t : Bool × Fin 4096 × Fin 4096) : validB (coordP t) = true := by
  simp [validB, coordP]

theorem exists_rhoG_eq (e : rhoQ.subgroupOf Gmat) :
    ∃ t : Bool × Fin 4096 × Fin 4096, rhoG (coordP t) = (e : Gmat) := by
  let φ : Bool × Fin 4096 × Fin 4096 → rhoQ.subgroupOf Gmat := fun t =>
    ⟨rhoG (coordP t), rhoG_mem _⟩
  have hinj : Function.Injective φ := by
    intro t t' h
    have h' := eq_of_rhoG_eq (validB_coordP t) (validB_coordP t')
      (congrArg Subtype.val h)
    obtain ⟨s, A, D⟩ := t
    obtain ⟨s', A', D'⟩ := t'
    simp only [coordP, Prod.mk.injEq] at h'
    obtain ⟨rfl, hA, hD⟩ := h'
    rw [Fin.val_inj] at hA hD
    rw [hA, hD]
  have hcard : Nat.card (rhoQ.subgroupOf Gmat) ≤ Nat.card (Bool × Fin 4096 × Fin 4096) := by
    rw [natCard_rhoQ_subgroupOf_Gmat, Nat.card_prod, Nat.card_prod, Nat.card_eq_fintype_card,
      Nat.card_eq_fintype_card, Fintype.card_bool, Fintype.card_fin]
    norm_num
  obtain ⟨t, ht⟩ := (hinj.bijective_of_nat_card_le hcard).2 e
  exact ⟨t, congrArg Subtype.val ht⟩

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterEbar
