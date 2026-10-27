module

public import CFSG.Monster.B.TwoA.Amalgam.FischerNodesFi22
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.ShapeWeak
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.SimpleLeaf
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.RkBMFi22Inv
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeA
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterInversion
public import CFSG.Monster.Existence.MilestoneInputs

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.Blueprint CFSG.Monster.GMS CFSG.Monster.B CFSG.Monster.Existence
  CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Amalgam CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier CFSG.Yardstones.Md0ec50421ce4

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Generic

theorem tabBThree_card_centralizer_equiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) (x : G) :
    Nat.card (Subgroup.centralizer ({e x} : Set H)) =
      Nat.card (Subgroup.centralizer ({x} : Set G)) := by
  refine (Nat.card_congr (Equiv.subtypeEquiv e.toEquiv fun g => ?_)).symm
  simp only [Subgroup.mem_centralizer_singleton_iff, MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe]
  constructor
  · intro h
    rw [← map_mul, ← map_mul, h]
  · intro h
    exact e.injective (by rw [map_mul, map_mul, h])

theorem tabBThree_shapeRkAt_of_decomp {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {Good Rk : ∀ (T : Type) [Group T], Prop} {Q H : Subgroup G} {s : G} (hsp : s ^ p = 1)
    (hqs : ∀ q ∈ Q, q * s = s * q) (hHQ : H ≤ Q)
    (hdecomp : ∀ g ∈ Subgroup.centralizer ({s} : Set G), ∃ k : ℕ, ∃ q ∈ Q, g = s ^ k * q)
    (hHn : ∀ q ∈ Q, ∀ h ∈ H, q * h * q⁻¹ ∈ H) (hLq : CFSG.Open.IsQuasisimple ↥H)
    (hpL : p ∣ Nat.card ↥H) (hCQH : ∀ q ∈ Q, (∀ h ∈ H, q * h = h * q) → q = 1)
    (hG : Good (PSimple p H)) (hR : Rk (PQuot p H)) : ShapeRkAt p Good Rk s := by
  have hQC : Q ≤ Subgroup.centralizer ({s} : Set G) :=
    fun q hq => Subgroup.mem_centralizer_singleton_iff.2 (hqs q hq)
  have hLn : ∀ g ∈ Subgroup.centralizer ({s} : Set G), ∀ l ∈ H, g * l * g⁻¹ ∈ H := by
    intro g hg h hh
    obtain ⟨k, q, hq, rfl⟩ := hdecomp g hg
    have hqh := hHn q hq h hh
    have hc : Commute s (q * h * q⁻¹) := (hqs _ (hHQ hqh)).symm
    have hcomm' : s ^ k * (q * h * q⁻¹) = q * h * q⁻¹ * s ^ k := (hc.pow_left k).eq
    have e : s ^ k * q * h * (s ^ k * q)⁻¹ = q * h * q⁻¹ := by
      calc s ^ k * q * h * (s ^ k * q)⁻¹ = s ^ k * (q * h * q⁻¹) * (s ^ k)⁻¹ := by group
        _ = q * h * q⁻¹ := by rw [hcomm', mul_inv_cancel_right]
    rw [e]
    exact hqh
  have hcent : IsPGroup p ↥(Subgroup.centralizer ({s} : Set G) ⊓
      Subgroup.centralizer (H : Set G)) := by
    haveI : Fact p.Prime := ⟨hp⟩
    refine IsPGroup.iff_orderOf.2 fun g => ?_
    obtain ⟨hgC, hgH⟩ := Subgroup.mem_inf.1 g.2
    obtain ⟨k, q, hq, hgq⟩ := hdecomp _ hgC
    have hq1 : q = 1 := by
      refine hCQH q hq fun h hh => ?_
      have hgh : (g : G) * h = h * g := (Subgroup.mem_centralizer_iff.1 hgH h hh).symm
      have hsh : s ^ k * h = h * s ^ k :=
        ((Commute.pow_left (show Commute s h from (hqs h (hHQ hh)).symm) k)).eq
      have : s ^ k * (q * h) = s ^ k * (h * q) := by
        calc s ^ k * (q * h) = (g : G) * h := by rw [hgq, mul_assoc]
          _ = h * g := hgh
          _ = h * s ^ k * q := by rw [hgq, mul_assoc]
          _ = s ^ k * (h * q) := by rw [← hsh, mul_assoc]
      exact mul_left_cancel this
    rw [hq1, mul_one] at hgq
    have hgp : g ^ p = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, hgq, ← pow_mul, mul_comm, pow_mul, hsp, one_pow, Subgroup.coe_one]
    have hdvd : orderOf g ∣ p ^ 1 := orderOf_dvd_of_pow_eq_one (by rw [pow_one]; exact hgp)
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 hdvd
    exact ⟨j, hj⟩
  exact shapeRkAt_of_normal_quasisimple hp (hHQ.trans hQC) hLn hLq hpL hcent hG hR

end Generic

section Fi22

theorem tabBThree_good_rk_fi22 (hOut : SporadicOuterLeTwo) (hSpM : SporadicMultipliers)
    (hBr : SporadicBridges) {G : Type} [Group G] [Finite G] {H : Subgroup G} [IsSimpleGroup ↥H]
    (hcenter : Subgroup.center ↥H = ⊥) (hLq : CFSG.Open.IsQuasisimple ↥H)
    (hpL : 3 ∣ Nat.card ↥H) (eF : ↥H ≃* NativeSporadic.Fi22) :
    GoodSpor 3 [.Fi22] (PSimple 3 H) ∧ RkSpor 3 [.Fi22] (PQuot 3 H) := by
  have hcore : GLAPPrimeCore 3 ↥H = ⊥ := glaPPrimeCore_eq_bot_of_simple Nat.prime_three hpL
  obtain ⟨eB⟩ : Nonempty (NativeSporadic.Fi22 ≃* (TauCeti.CFSGIndex.sporadic .Fi22).Group) :=
    hBr .Fi22
  refine ⟨Or.inr (Or.inr ⟨.Fi22, List.mem_singleton_self _,
    ⟨(pSimpleEquivSelf H hcore hcenter).trans (eF.trans eB)⟩⟩), ?_⟩
  exact RkSpor.of_equiv (pQuotEquivSelf H hcore).symm
    (rkSpor_Fi22_three_of_quasisimple hOut hSpM hBr hLq
      (by rw [hcenter]; exact IsPGroup.of_bot) fun _ => hcenter)

end Fi22

section Shat

theorem tabBThree_shapeRkAt_typeThree (hOut : SporadicOuterLeTwo) (hSpM : SporadicMultipliers)
    (hBr : SporadicBridges) {v w : CVert} (hw : w ∈ sphereThree v)
    (hcard : Nat.card (Subgroup.centralizer ({clabelS v * clabelS w} : Set Shat)) ≤
      3 * Nat.card (vStab v ⊓ vStab w : Subgroup Shat)) :
    ShapeRkAt 3 (GoodSpor 3 [.Fi22]) (RkSpor 3 [.Fi22]) (clabelS v * clabelS w) := by
  obtain ⟨hHQ, hHnorm, hcenter, hCQH⟩ : cnGroup v w ≤ vStab v ⊓ vStab w ∧
      ((cnGroup v w).subgroupOf (vStab v ⊓ vStab w)).Normal ∧
      Subgroup.center (cnGroup v w) = ⊥ ∧
      (∀ q ∈ vStab v ⊓ vStab w, (∀ h ∈ cnGroup v w, q * h = h * q) → q = 1) := by
    obtain ⟨θ₀, -, hTT⟩ := native_order_three_common_neighbor_three_transposition_group
    obtain ⟨h1, h2, -, -, -, -, -, -, -, h10, -, -, -, h14, -⟩ := hTT v w hw
    exact ⟨h1, h2, h10, h14⟩
  obtain ⟨hsimp, hcardH, hcomm⟩ : IsSimpleGroup (cnGroup v w) ∧
      Nat.card (cnGroup v w) = 64561751654400 ∧ commutator (cnGroup v w) = ⊤ := by
    obtain ⟨h1, -, h3, h4, -⟩ := native_three_transposition_group_simple v w hw
    exact ⟨h1, h3, h4⟩
  obtain ⟨eF⟩ := native_three_transposition_group_nonempty_mulEquiv_Fi22 hw
  have h3 : orderOf (clabel v * clabel w) = 3 :=
    ((native_order_three_label_products_and_dihedral_triples v).1 w hw).1
  have hd2 : clabelS v * clabelS v = 1 := by
    have := pow_orderOf_eq_one (clabelS v)
    rwa [orderOf_clabelS, sq] at this
  have he2 : clabelS w * clabelS w = 1 := by
    have := pow_orderOf_eq_one (clabelS w)
    rwa [orderOf_clabelS, sq] at this
  have hso : orderOf (clabelS v * clabelS w) = 3 := by
    rw [← Subgroup.orderOf_coe, Subgroup.coe_mul, coe_clabelS, coe_clabelS]
    exact h3
  obtain ⟨s, hs⟩ : ∃ s : Shat, s = clabelS v * clabelS w := ⟨_, rfl⟩
  rw [← hs] at hcard hso ⊢
  have hs3 : s * s * s = 1 := by
    have := pow_orderOf_eq_one s
    rwa [hso, pow_three'] at this
  have hqs : ∀ q ∈ vStab v ⊓ vStab w, q * s = s * q := by
    intro q hq
    have h1 := commute_of_mem_vStab (Subgroup.mem_inf.1 hq).1
    have h2 := commute_of_mem_vStab (Subgroup.mem_inf.1 hq).2
    rw [hs]
    calc q * (clabelS v * clabelS w) = q * clabelS v * clabelS w := by rw [mul_assoc]
      _ = clabelS v * q * clabelS w := by rw [h1]
      _ = clabelS v * (q * clabelS w) := by rw [mul_assoc]
      _ = clabelS v * (clabelS w * q) := by rw [h2]
      _ = clabelS v * clabelS w * q := by rw [mul_assoc]
  have hQC : vStab v ⊓ vStab w ≤ Subgroup.centralizer ({s} : Set Shat) :=
    fun q hq => Subgroup.mem_centralizer_singleton_iff.2 (hqs q hq)
  have hsQ : s ∉ vStab v ⊓ vStab w := by
    intro hsQ
    have h1 := commute_of_mem_vStab (Subgroup.mem_inf.1 hsQ).1
    rw [hs] at h1
    have h2 : s * s = 1 := by
      rw [hs]
      calc clabelS v * clabelS w * (clabelS v * clabelS w)
          = clabelS v * clabelS w * clabelS v * clabelS w := by simp only [mul_assoc]
        _ = clabelS v * (clabelS v * clabelS w) * clabelS w := by rw [h1]
        _ = 1 := by rw [← mul_assoc, hd2, one_mul, he2]
    have h4 : s = 1 := by
      calc s = s * s * s * (s * s)⁻¹ := by group
        _ = 1 := by rw [hs3, h2, inv_one, one_mul]
    rw [h4, orderOf_one] at hso
    exact absurd hso (by norm_num)
  have hdecomp := mem_pow_mul_of_card_le (Subgroup.mem_centralizer_singleton_iff.2 rfl) hQC hs3
    hsQ hcard
  have hHn : ∀ q ∈ vStab v ⊓ vStab w, ∀ h ∈ cnGroup v w, q * h * q⁻¹ ∈ cnGroup v w := by
    intro q hq h hh
    have := hHnorm.conj_mem ⟨h, hHQ hh⟩ (Subgroup.mem_subgroupOf.2 hh) ⟨q, hq⟩
    rw [Subgroup.mem_subgroupOf] at this
    exact this
  have hLq : CFSG.Open.IsQuasisimple ↥(cnGroup v w) :=
    ⟨hcomm, MulEquiv.isSimpleGroup ((QuotientGroup.quotientMulEquivOfEq hcenter).trans
      QuotientGroup.quotientBot)⟩
  have hpL : 3 ∣ Nat.card ↥(cnGroup v w) := by rw [hcardH]; norm_num
  obtain ⟨hG, hR⟩ := tabBThree_good_rk_fi22 hOut hSpM hBr hcenter hLq hpL eF
  have hs3' : s ^ 3 = 1 := by rw [pow_three']; exact hs3
  exact tabBThree_shapeRkAt_of_decomp Nat.prime_three hs3' hqs hHQ hdecomp hHn hLq hpL hCQH hG hR

end Shat

section Baby

theorem tabBThree_card_centralizer_babyToShat (t : NativeSporadic.B) :
    Nat.card (Subgroup.centralizer ({babyToShat t} : Set Shat)) =
      Nat.card (Subgroup.centralizer ({t} : Set NativeSporadic.B)) := by
  with_reducible_and_instances exact tabBThree_card_centralizer_equiv babyToShat t

theorem tabBThree_typeThree_of_inverted {s d : NativeSporadic.B} (hs : orderOf s = 3)
    (hd : BabyInv 0 d) (hinv : d * s * d⁻¹ = s⁻¹) :
    ∃ v w : CVert, w ∈ sphereThree v ∧ babyToShat s = clabelS v * clabelS w := by
  have hcls : ∀ t : NativeSporadic.B, BabyInv 0 t → IsConj t (babyRep 1) := fun t ht =>
    babyTableIII.2 0 t (babyRep 1) ht babyInv_zero_babyRep_one
  obtain ⟨x, hx⟩ := (babyInv_zero_iff_clabelS hcls d).1 hd
  have hs' : orderOf (babyToShat s) = 3 := by
    rw [← hs]
    with_reducible_and_instances exact MulEquiv.orderOf_eq babyToShat s
  have hinv' : clabelS x * babyToShat s * (clabelS x)⁻¹ = (babyToShat s)⁻¹ := by
    rw [hx, ← map_inv, ← map_mul, ← map_mul, hinv, map_inv]
  have hx2 : clabelS x * clabelS x = 1 := by
    have := pow_orderOf_eq_one (clabelS x)
    rwa [orderOf_clabelS, sq] at this
  have hodd : Odd (orderOf (babyToShat s)) := by rw [hs']; decide
  obtain ⟨y, hy⟩ := CTIB.exists_clabelS_eq_of_isConj (isConj_mul_of_inverts_odd hinv' hodd)
  have hsxy : babyToShat s = clabelS y * clabelS x := by rw [hy, mul_assoc, hx2, mul_one]
  have hamb := ambientRootOrbitsHyp
  have hL := labelsInput_of_ambient hamb
  have hdiam := CTIB.dist_le_three_of_inputs hL (outerInput_of_ambient hamb)
    (pathInput_of_ambient hamb) (typeThreeBoundInput_of_ambient hamb)
  refine ⟨y, x, ?_, hsxy⟩
  rcases CTIB.commute_or_three_or_four hdiam hL y x with hc | ⟨hw, -⟩ | ⟨-, h4⟩
  · exfalso
    have h2 : babyToShat s ^ 2 = 1 := by
      rw [hsxy]
      exact CTIB.sq_clabelS_mul_of_commute hc
    have := orderOf_le_of_pow_eq_one (by norm_num) h2
    omega
  · exact hw
  · exfalso
    rw [← hsxy, hs'] at h4
    exact absurd h4 (by norm_num)

@[expose] def TabBThreeACard : Prop :=
  ∀ s : NativeSporadic.B, orderOf s = 3 →
    (∃ d : NativeSporadic.B, BabyInv 0 d ∧ d * s * d⁻¹ = s⁻¹) →
      Nat.card (Subgroup.centralizer ({s} : Set NativeSporadic.B)) ≤ 387370509926400

theorem tabBThreeACard_of_bThreeABound (h : BThreeABound) : TabBThreeACard := by
  rintro s hs ⟨d, hd, hinv⟩
  obtain ⟨v, w, hw, hvw⟩ := tabBThree_typeThree_of_inverted hs hd hinv
  have hQ := (native_order_three_common_neighbors_exact_3510.1 v w hw).2.2.2.2.2
  have h1 := h v w hw
  rw [hQ, ← hvw, tabBThree_card_centralizer_babyToShat] at h1
  exact h1.trans (by norm_num)

theorem tabBThree_shapeRkAt'_of_inverted (hOut : SporadicOuterLeTwo)
    (hSpM : SporadicMultipliers) (hBr : SporadicBridges) (hA : TabBThreeACard)
    {s d : NativeSporadic.B} (hs : orderOf s = 3) (hd : BabyInv 0 d) (hinv : d * s * d⁻¹ = s⁻¹) :
    ShapeRkAt' 3 (GoodSpor 3 [.Fi22]) (RkSpor 3 [.Fi22]) s := by
  haveI : Finite NativeSporadic.B := CFSG.Monster.B.Pinned.finite_B
  obtain ⟨v, w, hw, hvw⟩ := tabBThree_typeThree_of_inverted hs hd hinv
  have hQ := (native_order_three_common_neighbors_exact_3510.1 v w hw).2.2.2.2.2
  have hcard : Nat.card (Subgroup.centralizer ({clabelS v * clabelS w} : Set Shat)) ≤
      3 * Nat.card (vStab v ⊓ vStab w : Subgroup Shat) := by
    rw [hQ, ← hvw, tabBThree_card_centralizer_babyToShat]
    exact (hA s hs ⟨d, hd, hinv⟩).trans (by norm_num)
  have hS := tabBThree_shapeRkAt_typeThree hOut hSpM hBr hw hcard
  have h : ShapeRkAt 3 (GoodSpor 3 [.Fi22]) (RkSpor 3 [.Fi22])
      (babyToShat.symm (clabelS v * clabelS w)) := by
    with_reducible_and_instances
      exact ShapeRkAt.of_equiv Nat.prime_three (fun _ _ _ _ e h => GoodSpor.of_equiv e h)
        (fun _ _ _ _ e h => RkSpor.of_equiv e h) babyToShat.symm hS
  rw [← hvw, MulEquiv.symm_apply_apply] at h
  exact h.toWeak Nat.prime_three

end Baby

end CFSG.HardMathSupport.Dickson.I271
