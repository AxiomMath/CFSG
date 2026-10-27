module

public import CFSG.Monster.Existence.MilestoneInputs
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeA
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterInversion

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.BM

open CFSG.Monster.GMS CFSG.Blueprint.NativeSporadic CFSG.Monster.B CFSG.Monster.Existence
  CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Amalgam CFSG.HardMathSupport.Timmesfeld.SporadicBalance

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Generic

theorem exists_comap_simple {G X : Type*} [Group G] [Group X] (e : G ≃* X) (K : Subgroup X)
    (hK : IsSimpleGroup K) (hnc : ¬ IsMulCommutative K) :
    ∃ H : Subgroup G, IsSimpleGroup H ∧ (∃ a b : H, a * b ≠ b * a) ∧ Nat.card H = Nat.card K ∧
      ∀ g : G, g ∈ H ↔ e g ∈ K := by
  let f : K.comap e.toMonoidHom ≃* K := MulEquiv.ofBijective (e.toMonoidHom.subgroupComap K)
    ⟨MonoidHom.subgroupComap_injective _ _ e.injective,
      MonoidHom.subgroupComap_surjective _ _ e.surjective⟩
  refine ⟨K.comap e.toMonoidHom, f.isSimpleGroup, ?_, Nat.card_congr f.toEquiv,
    fun _ => Iff.rfl⟩
  obtain ⟨a, b, hab⟩ : ∃ a b : K, a * b ≠ b * a := by
    by_contra hcon
    exact hnc ⟨⟨fun a b => of_not_not fun h => hcon ⟨a, b, h⟩⟩⟩
  refine ⟨f.symm a, f.symm b, fun h => hab ?_⟩
  have := congrArg f h
  rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at this

end Generic

section Inverted


theorem B_inverted_data {s d : CFSG.Blueprint.NativeSporadic.B} (hs : orderOf s = 3)
    (hd : CFSG.Monster.GMS.BabyInv 0 d) (hinv : d * s * d⁻¹ = s⁻¹) :
    ∃ H : Subgroup CFSG.Blueprint.NativeSporadic.B, IsSimpleGroup ↥H ∧
      (∃ a b : ↥H, a * b ≠ b * a) ∧
      Nat.card ↥H = 64561751654400 ∧ (∀ h ∈ H, d * h = h * d) ∧ (∀ h ∈ H, s * h = h * s) ∧
      (∀ q : CFSG.Blueprint.NativeSporadic.B, d * q = q * d → s * q = q * s →
        ∀ h ∈ H, q * h * q⁻¹ ∈ H) ∧
      (∀ q : CFSG.Blueprint.NativeSporadic.B, d * q = q * d → s * q = q * s →
        (∀ h ∈ H, q * h = h * q) → q = 1) := by
  have hcls : ∀ t : B, BabyInv 0 t → IsConj t (babyRep 1) := fun t ht =>
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
  have hinj : Function.Injective clabel :=
    CTIB.clabel_injective_of_inputs hL (outerInput_of_ambient hamb) (pathInput_of_ambient hamb)
      (typeThreeBoundInput_of_ambient hamb)
  have hw : x ∈ sphereThree y := by
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
  obtain ⟨hsimp, hnc, hcard, -⟩ := native_three_transposition_group_simple y x hw
  obtain ⟨θ₀, -, hTT⟩ := native_order_three_common_neighbor_three_transposition_group
  obtain ⟨hle, -, -, -, -, -, -, -, -, -, -, -, -, hCQ, -⟩ := hTT y x hw
  have hQ : ∀ q : B, d * q = q * d → s * q = q * s → babyToShat q ∈ vStab y ⊓ vStab x := by
    intro q hdq hsq
    have h1 : Commute (babyToShat q) (clabelS x) := by
      rw [hx]
      exact (show Commute d q from hdq).symm.map babyToShat
    have h2 : Commute (babyToShat q) (babyToShat s) :=
      (show Commute s q from hsq).symm.map babyToShat
    have h3 : Commute (babyToShat q) (clabelS y) := by
      rw [hy]
      exact h2.mul_right h1
    exact Subgroup.mem_inf.2 ⟨(CTIB.commute_clabelS_iff hinj y _).1 h3,
      (CTIB.commute_clabelS_iff hinj x _).1 h1⟩
  obtain ⟨H, hHs, hHnc, hHcard, hmem⟩ : ∃ H : Subgroup B, IsSimpleGroup H ∧
      (∃ a b : H, a * b ≠ b * a) ∧ Nat.card H = Nat.card (cnGroup y x) ∧
      ∀ g : B, g ∈ H ↔ babyToShat g ∈ cnGroup y x := by
    with_reducible_and_instances exact exists_comap_simple babyToShat (cnGroup y x) hsimp hnc
  refine ⟨H, hHs, hHnc, hHcard.trans hcard, ?_, ?_, ?_, ?_⟩
  · intro h hh
    have c : Commute (babyToShat h) (clabelS x) :=
      commute_of_mem_vStab (Subgroup.mem_inf.1 (hle ((hmem h).1 hh))).2
    rw [hx] at c
    apply babyToShat.injective
    rw [map_mul, map_mul]
    exact c.eq.symm
  · intro h hh
    have hq := Subgroup.mem_inf.1 (hle ((hmem h).1 hh))
    have c1 : Commute (babyToShat h) (clabelS y) := commute_of_mem_vStab hq.1
    have c2 : Commute (babyToShat h) (clabelS x) := commute_of_mem_vStab hq.2
    have c : Commute (babyToShat h) (babyToShat s) := by
      rw [hsxy]
      exact c1.mul_right c2
    apply babyToShat.injective
    rw [map_mul, map_mul]
    exact c.eq.symm
  · intro q hdq hsq h hh
    refine (hmem _).2 ?_
    rw [map_mul, map_mul, map_inv]
    exact conj_mem_cnGroup (hQ q hdq hsq) ((hmem h).1 hh)
  · intro q hdq hsq hc
    apply babyToShat.injective
    rw [map_one]
    refine hCQ _ (hQ q hdq hsq) fun k hk => ?_
    have hk' : babyToShat.symm k ∈ H := (hmem _).2 (by rw [MulEquiv.apply_symm_apply]; exact hk)
    have := congrArg babyToShat (hc _ hk')
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at this

end Inverted

end CFSG.HardMathSupport.Dickson.Sec6.BM
