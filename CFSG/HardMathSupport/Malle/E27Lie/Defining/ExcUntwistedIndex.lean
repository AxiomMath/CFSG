module

public import CFSG.HardMathSupport.Malle.E27Lie.Defining.ExcUntwisted
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434RemG23
public import CFSG.HardMathSupport.Foote.E27.SporCentKill
public import CFSG.HardMathSupport.Malle.E27Lie.Cross.AssemblyIn

public section

namespace CFSG.HardMathSupport.Malle.E27Lie

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Foote.E27
  TauCeti CFSG.TauCetiBridge.Even CFSG.Timmesfeld.ExceptionalOrders

theorem hroots_G2 :
    {α : Fin Tag.G2.rank → ℤ | IsRoot .G2 α ∧ 0 < height α ∧ 2 ≤ height α}.ncard + Tag.G2.rank =
      {α : Fin Tag.G2.rank → ℤ | IsRoot .G2 α ∧ 0 < height α ∧ 1 ≤ height α}.ncard := by
  rw [ncard_setOf_isRoot_and (fun α => 0 < height α ∧ 2 ≤ height α),
    ncard_setOf_isRoot_and (fun α => 0 < height α ∧ 1 ≤ height α)]
  decide +kernel

theorem hroots_F4 :
    {α : Fin Tag.F4.rank → ℤ | IsRoot .F4 α ∧ 0 < height α ∧ 2 ≤ height α}.ncard + Tag.F4.rank =
      {α : Fin Tag.F4.rank → ℤ | IsRoot .F4 α ∧ 0 < height α ∧ 1 ≤ height α}.ncard := by
  rw [ncard_setOf_isRoot_and (fun α => 0 < height α ∧ 2 ≤ height α),
    ncard_setOf_isRoot_and (fun α => 0 < height α ∧ 1 ≤ height α)]
  decide +kernel

theorem hroots_E6 :
    {α : Fin Tag.E6.rank → ℤ | IsRoot .E6 α ∧ 0 < height α ∧ 2 ≤ height α}.ncard + Tag.E6.rank =
      {α : Fin Tag.E6.rank → ℤ | IsRoot .E6 α ∧ 0 < height α ∧ 1 ≤ height α}.ncard := by
  rw [ncard_setOf_isRoot_and (fun α => 0 < height α ∧ 2 ≤ height α),
    ncard_setOf_isRoot_and (fun α => 0 < height α ∧ 1 ≤ height α)]
  decide +kernel

theorem hroots_E7 :
    {α : Fin Tag.E7.rank → ℤ | IsRoot .E7 α ∧ 0 < height α ∧ 2 ≤ height α}.ncard + Tag.E7.rank =
      {α : Fin Tag.E7.rank → ℤ | IsRoot .E7 α ∧ 0 < height α ∧ 1 ≤ height α}.ncard := by
  rw [ncard_setOf_isRoot_and (fun α => 0 < height α ∧ 2 ≤ height α),
    ncard_setOf_isRoot_and (fun α => 0 < height α ∧ 1 ≤ height α)]
  decide +kernel

theorem hroots_E8 :
    {α : Fin Tag.E8.rank → ℤ | IsRoot .E8 α ∧ 0 < height α ∧ 2 ≤ height α}.ncard + Tag.E8.rank =
      {α : Fin Tag.E8.rank → ℤ | IsRoot .E8 α ∧ 0 < height α ∧ 1 ≤ height α}.ncard := by
  rw [ncard_setOf_isRoot_and (fun α => 0 < height α ∧ 2 ≤ height α),
    ncard_setOf_isRoot_and (fun α => 0 < height α ∧ 1 ≤ height α)]
  decide +kernel


theorem false_of_untwisted_char_three {X : Type} [Group X] [Finite X] {K R T : Subgroup X}
    {z : X} (h : E27Config X K R T z) (hz : z ∈ K) (τ : Tag) (c : PrimePower → LieTypeIndex)
    (hB : UntwistedBridgeAll τ c) (q : PrimePower) (hv : (c q).Valid) (hp : q.p = 3)
    (hroots : {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α ∧ 2 ≤ height α}.ncard + τ.rank =
      {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α ∧ 1 ≤ height α}.ncard)
    (h81 : 81 ≤ 3 ^ (q.exponent * τ.rank))
    (e : ↥K ≃* (CFSGIndex.lie ⟨c q, hv⟩).Group) : False := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  set F := GaloisField q.p q.exponent
  have hF : Nat.card F = q.p ^ q.exponent := GaloisField.card _ _ q.exponent_pos.ne'
  have hF' : Nat.card F = q.card := by rw [hF, PrimePower.card_def]
  obtain ⟨b⟩ := hB q hv F hF'
  have : CharP F 3 := hp ▸ (inferInstance : CharP F q.p)
  let e' : ↥K ≃* adjointGroup τ F :=
    e.trans (b.symm.trans ((QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
      QuotientGroup.quotientBot))
  exact false_of_adjointGroup_char_three h hz τ F e' hroots
    (by rw [hF, hp, ← pow_mul]; exact h81)

theorem false_of_G2_three
    {X : Type} [Group X] [Finite X] {K R T : Subgroup X} {z : X} (h : E27Config X K R T z)
    (hz : z ∈ K) (q : PrimePower) (hv : (LieTypeIndex.G2 q).Valid) (hp : q.p = 3)
    (hf : q.exponent = 1) (e : ↥K ≃* (CFSGIndex.lie ⟨.G2 q, hv⟩).Group) : False := by
  have hK : Nat.card (ZMod 3) = q.card := by
    rw [Nat.card_zmod, PrimePower.card_def, hp, hf, pow_one]
  obtain ⟨b⟩ := CFSG.TauCetiBridge.untwistedBridge_G2 q hv (by rw [hp]; decide) (ZMod 3) hK
  let φ : ↥K ≃* ↥CFSG.RankThree.PartTwo.Census.Carrier.G2Three.R3 :=
    e.trans (b.symm.trans CFSG.RankThree.PartTwo.Census.Carrier.G2Three.adjointQuotientEquivR3)
  have : Finite ↥CFSG.RankThree.PartTwo.Census.Carrier.G2Three.R3 := Finite.of_equiv _ φ.toEquiv
  obtain ⟨z', -, -, -, hzc, hgood⟩ :=
    CFSG.RankThree.PartTwo.Sec4.Item434RemG23.exists_hgood
      CFSG.RankThree.PartTwo.Sec4.Item434RemG23.sylCheck_true
      CFSG.RankThree.PartTwo.Sec4.Item434RemG23.k2Check_true
      CFSG.RankThree.PartTwo.Sec4.Item434RemG23.sylWord_lt
  refine E27Config.false_of_e81_cover h hz φ
    (CFSG.RankThree.PartTwo.Sec4.Item434RemG23.sylow_le_R3
      CFSG.RankThree.PartTwo.Sec4.Item434RemG23.sylWord_lt)
    CFSG.RankThree.PartTwo.Sec4.Item434RemG23.card_sylow_eq ?_ hzc hgood
  rw [CFSG.RankThree.PartTwo.Census.Carrier.G2Three.card_R3,
    CFSG.RankThree.PartTwo.Sec4.Item434RemG23.factorization_three_card]
  norm_num

@[expose] def IdxChar3ExcUntwisted (i : LieTypeIndex) : Prop :=
  ∃ q : PrimePower, q.p = 3 ∧ (i = .G2 q ∨ i = .F4 q ∨ i = .E6 q ∨ i = .E7 q ∨ i = .E8 q)

theorem innerLeaf_char3ExcUntwisted :
    InnerLeaf IdxChar3ExcUntwisted := by
  intro X _ _ K R T z h hz d hd e
  obtain ⟨i, hv⟩ := d
  obtain ⟨q, hp, hi⟩ := hd
  obtain ⟨e⟩ := e
  have hf := q.exponent_pos
  rcases hi with rfl | rfl | rfl | rfl | rfl
  · by_cases hf1 : q.exponent = 1
    · exact false_of_G2_three h hz q hv hp hf1 e
    · refine false_of_untwisted_char_three h hz .G2 LieTypeIndex.G2 chevalleyBridgesAll.g2 q hv
        hp hroots_G2 ?_ e
      calc 81 = 3 ^ 4 := by norm_num
        _ ≤ 3 ^ (q.exponent * Tag.G2.rank) := Nat.pow_le_pow_right (by norm_num) (by
          show 4 ≤ q.exponent * 2
          omega)
  · refine false_of_untwisted_char_three h hz .F4 LieTypeIndex.F4 chevalleyBridgesAll.f4 q hv hp
      hroots_F4 ?_ e
    calc 81 = 3 ^ 4 := by norm_num
      _ ≤ 3 ^ (q.exponent * Tag.F4.rank) := Nat.pow_le_pow_right (by norm_num) (by
        show 4 ≤ q.exponent * 4
        omega)
  · refine false_of_untwisted_char_three h hz .E6 LieTypeIndex.E6 chevalleyBridgesAll.e6 q hv hp
      hroots_E6 ?_ e
    calc 81 = 3 ^ 4 := by norm_num
      _ ≤ 3 ^ (q.exponent * Tag.E6.rank) := Nat.pow_le_pow_right (by norm_num) (by
        show 4 ≤ q.exponent * 6
        omega)
  · refine false_of_untwisted_char_three h hz .E7 LieTypeIndex.E7 chevalleyBridgesAll.e7 q hv hp
      hroots_E7 ?_ e
    calc 81 = 3 ^ 4 := by norm_num
      _ ≤ 3 ^ (q.exponent * Tag.E7.rank) := Nat.pow_le_pow_right (by norm_num) (by
        show 4 ≤ q.exponent * 7
        omega)
  · refine false_of_untwisted_char_three h hz .E8 LieTypeIndex.E8 chevalleyBridgesAll.e8 q hv hp
      hroots_E8 ?_ e
    calc 81 = 3 ^ 4 := by norm_num
      _ ≤ 3 ^ (q.exponent * Tag.E8.rank) := Nat.pow_le_pow_right (by norm_num) (by
        show 4 ≤ q.exponent * 8
        omega)

end CFSG.HardMathSupport.Malle.E27Lie
