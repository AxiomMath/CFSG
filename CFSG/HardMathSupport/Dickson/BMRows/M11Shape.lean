module

public import CFSG.HardMathSupport.Dickson.BMRows.M11Cent
public import CFSG.HardMathSupport.Dickson.BMRows.M11Types

public section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Dickson.BMRows.M11

open CFSG.Monster CFSG.Monster.Generated CFSG.Monster.Existence
  CFSG.AGLEmbedding.Norton.MON5_7 CFSG.AGLEmbedding.Norton.Gen11
  CFSG.AGLEmbedding.Norton.MON11_13 CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterElevenLocal
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterEleven
open CFSG.HardMathSupport.Dickson.I271 (ShapeRkAt CentShapeRk CentShape)
open scoped commutatorElement

@[expose] def CentElevenBound : Prop :=
  Nat.card (Subgroup.centralizer ({gw gen11W0} : Set Gmat)) ≤ 1045440

section Bound

theorem m12K_noncomm : ∃ a b : m12K, a * b ≠ b * a := by
  have := isSimpleGroup_m12K
  by_contra hc
  push_neg at hc
  letI : CommGroup m12K := { (inferInstance : Group m12K) with mul_comm := hc }
  have hp := IsSimpleGroup.prime_card (α := m12K)
  rw [card_m12K] at hp
  norm_num at hp

theorem m12L_eq_centralizer_of_bound (h : CentElevenBound) :
    m12L = Subgroup.centralizer ({gw gen11W0} : Set Gmat) :=
  Subgroup.eq_of_le_of_card_ge m12L_le_centralizer (by rw [card_m12L]; exact h)

theorem conj_mem_m12K_of_bound (h : CentElevenBound) :
    ∀ g ∈ Subgroup.centralizer ({gw gen11W0} : Set Gmat), ∀ l ∈ m12K, g * l * g⁻¹ ∈ m12K := by
  intro g hg l hl
  rw [← m12L_eq_centralizer_of_bound h] at hg
  obtain ⟨⟨k, y⟩, rfl⟩ := hg
  rw [m12LHom_apply]
  have hyl : (y : Gmat) * l = l * y := (commute_m12K_zpowers ⟨l, hl⟩ y).eq.symm
  have he : (k : Gmat) * y * l * ((k : Gmat) * y)⁻¹ = k * l * (k : Gmat)⁻¹ := by
    rw [mul_assoc (k : Gmat) y l, hyl]
    group
  rw [he]
  exact m12K.mul_mem (m12K.mul_mem k.2 hl) (m12K.inv_mem k.2)

theorem isPGroup_inf_centralizer_m12K (h : CentElevenBound) :
    IsPGroup 11 ↥(Subgroup.centralizer ({gw gen11W0} : Set Gmat) ⊓
      Subgroup.centralizer (m12K : Set Gmat)) := by
  have := isSimpleGroup_m12K
  have hZ : Subgroup.center m12K = ⊥ := I271.center_eq_bot_of_simple_nonab m12K_noncomm
  have hle : Subgroup.centralizer ({gw gen11W0} : Set Gmat) ⊓
      Subgroup.centralizer (m12K : Set Gmat) ≤ Subgroup.zpowers (gw gen11W0) := by
    intro g hg'
    obtain ⟨hg, hgK⟩ := Subgroup.mem_inf.1 hg'
    rw [← m12L_eq_centralizer_of_bound h] at hg
    obtain ⟨⟨k, y⟩, rfl⟩ := hg
    rw [m12LHom_apply] at hgK ⊢
    have hkZ : k ∈ Subgroup.center m12K := by
      rw [Subgroup.mem_center_iff]
      intro q
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      have h1 : (q : Gmat) * (k * y) = k * y * q := Subgroup.mem_centralizer_iff.1 hgK q q.2
      have hyq : (y : Gmat) * q = q * y := (commute_m12K_zpowers q y).eq.symm
      have h2 : (q : Gmat) * k * y = k * q * y := by
        rw [mul_assoc (q : Gmat), h1, mul_assoc (k : Gmat) (y : Gmat), hyq, ← mul_assoc]
      exact mul_right_cancel h2
    rw [hZ, Subgroup.mem_bot] at hkZ
    rw [hkZ, OneMemClass.coe_one, one_mul]
    exact y.2
  have hx : IsPGroup 11 ↥(Subgroup.zpowers (gw gen11W0)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_x11, pow_one])
  exact hx.to_le hle

theorem shapeRkAt_x11 (h : CentElevenBound) : ShapeRkAt 11 GoodM12 TrivRk (gw gen11W0) := by
  have := isSimpleGroup_m12K
  have hnab := m12K_noncomm
  have hp : Nat.Prime 11 := by norm_num
  have hpK : 11 ∣ Nat.card m12K := by rw [card_m12K]; norm_num
  have hZ : Subgroup.center m12K = ⊥ := I271.center_eq_bot_of_simple_nonab hnab
  have hLq : CFSG.Open.IsQuasisimple m12K := by
    refine ⟨?_, ((QuotientGroup.quotientMulEquivOfEq hZ).trans
      QuotientGroup.quotientBot).isSimpleGroup⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator m12K) with h' | h'
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      have h1 : ⁅a, b⁆ = 1 := by
        rw [← Subgroup.mem_bot, ← h']
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      exact hab (commutatorElement_eq_one_iff_mul_comm.1 h1)
    · exact h'
  have hcore : CFSG.Open.GLAPPrimeCore 11 m12K = ⊥ := I271.glaPPrimeCore_eq_bot_of_simple hp hpK
  obtain ⟨e⟩ := nonempty_m12K_mulEquiv
  exact I271.shapeRkAt_of_normal_quasisimple hp m12K_le_centralizer (conj_mem_m12K_of_bound h)
    hLq hpK (isPGroup_inf_centralizer_m12K h) ⟨(I271.pSimpleEquivSelf m12K hcore hZ).trans e⟩
    trivial

end Bound

section Fusion

theorem exists_conj_pow_x11 {k : Gmat} (hk : orderOf k = 11) :
    ∃ g : Gmat, ∃ j : ℕ, k = g * gw gen11W0 ^ j * g⁻¹ ∧ gw gen11W0 ^ j ≠ 1 := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have hfac : (Nat.card Gmat).factorization 11 = 2 := by
    have h : CFSG.Open.monsterOrder =
        11 ^ 2 * 6677829956979445255259999214559593033105408000000000 := by
      norm_num [CFSG.Open.monsterOrder]
    rw [CFSG.YGroups.Y443.natCard_Gmat_eq_monsterOrder, h,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow (by norm_num), Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  obtain ⟨hx, hy, hxy, hx1, h3, h4, -, -⟩ := eleven_gw_facts
  have hy3 := eleven_data_facts.1
  have hrot := CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.eleven_rot_fact
    Certificates.certificate41508
  have hc : Commute (gw gen11W0) (gw gen11W1) := hxy
  obtain ⟨g, j, hgj⟩ := exists_conj_pow_of_eleven_lines (x₃ := gw gen11W2) (x₄ := gw gen11W3) hx hy
    hxy (by rw [h3, mul_inv_cancel_right, ((hc.pow_pow 6 3).symm).eq])
    (by rw [hy3, mul_inv_cancel_right]) (by rw [h4, mul_inv_cancel_right])
    (by rw [hrot, mul_inv_cancel_right]) hx1 hfac hk
  refine ⟨g, j, hgj, fun h1 => ?_⟩
  rw [h1, mul_one, mul_inv_cancel] at hgj
  rw [hgj, orderOf_one] at hk
  norm_num at hk

theorem shapeRkAt_gmat_eleven (h : CentElevenBound) {k : Gmat} (hk : orderOf k = 11) :
    ShapeRkAt 11 GoodM12 TrivRk k := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  obtain ⟨g, j, hgj, hj1⟩ := exists_conj_pow_x11 hk
  have h1 : ShapeRkAt 11 GoodM12 TrivRk (gw gen11W0 ^ j) :=
    I271.ShapeRkAt.of_centralizer_eq (centralizer_pow_eq_of_prime orderOf_x11 hj1).symm
      (shapeRkAt_x11 h)
  have h2 := I271.ShapeRkAt.of_equiv (by norm_num) (fun _ _ _ _ f hg => GoodM12.of_equiv f hg)
    (fun _ _ _ _ _ _ => trivial) (MulAut.conj g) h1
  rwa [MulAut.conj_apply, ← hgj] at h2

end Fusion

section Bender

theorem centElevenBound_of_B
    (hB : ∀ y : CFSG.Blueprint.NativeSporadic.B, orderOf y = 11 →
      Nat.card (Subgroup.centralizer ({y} : Set CFSG.Blueprint.NativeSporadic.B)) ≤ 1320) :
    CentElevenBound :=
  (card_centralizer_x11 hB).le

end Bender

end CFSG.HardMathSupport.Dickson.BMRows.M11
