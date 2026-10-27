module

public import CFSG.CharacterTheory.Wreathed.SquareRootSmallCharacterRigidityCentralizers
public import CFSG.CharacterTheory.Wreathed.BrauerWongModel

public noncomputable section

namespace CFSG.Wreathed.BrauerWong

open CFSG.Wreathed CFSG.Wreathed.WreathCentralSquare
open CFSG.BenderSuzuki.PFchapter1section1

universe u

variable {G : Type u} [Group G]

section Model

theorem originalRoot_pow_odd (m k : ℕ) :
    originalRoot m ^ (2 * k + 1) = element m ((k + 1 : ℕ) : ZMod m) (k : ZMod m) 1 := by
  rw [pow_succ, pow_mul, originalRoot_sq, Original.a_eq, element_base_pow, originalRoot_eq,
    element_base_mul]
  simp only [nsmul_eq_mul, mul_one, add_zero, Nat.cast_add, Nat.cast_one]

theorem odd_mod_two_pow_iff (n : ℕ) (hn : 1 ≤ n) (k : ℕ) : Odd (k % 2 ^ n) ↔ Odd k := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  rw [pow_succ, Nat.odd_iff, Nat.odd_iff, Nat.mod_mul_left_mod]

theorem natCast_val_odd_iff (n : ℕ) (hn : 1 ≤ n) (k : ℕ) :
    Odd ((k : ZMod (2 ^ n)).val) ↔ Odd k := by
  rw [ZMod.val_natCast, odd_mod_two_pow_iff n hn]

theorem val_odd_iff_add (n : ℕ) (hn : 1 ≤ n) (c d : ZMod (2 ^ n)) :
    Odd (c + d).val ↔ Odd (c.val + d.val) := by
  let : NeZero (2 ^ n) := ⟨pow_ne_zero _ two_ne_zero⟩
  rw [ZMod.val_add, odd_mod_two_pow_iff n hn]

end Model

variable {n : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))

theorem orderOf_lt_of_mem_modelBase {x : G} (hx : x ∈ modelBase S e) :
    orderOf x < 2 * 2 ^ n := by
  obtain ⟨w, hw, rfl⟩ := hx
  rw [orderOf_injective _ (wreathModelHom_injective S e)]
  obtain ⟨⟨a, b, f⟩, rfl⟩ := (coordinateEquiv (2 ^ n)).symm.surjective w
  change element _ a b f ∈ baseSubgroup _ at hw
  rw [element_mem_base] at hw
  subst hw
  exact element_base_order_lt_twice_modulus _ (pow_pos two_pos _) a b

theorem orderOf_ne_of_mem_rightConjugate_modelV (hn : 2 ≤ n) {x s : G}
    (hx : x ∈ rightConjugate (modelV S e) s) :
    orderOf x ≠ 2 * 2 ^ n := by
  obtain ⟨v, hv, rfl⟩ := hx
  obtain ⟨w, hw, rfl⟩ := hv
  change orderOf ((MulAut.conj s⁻¹) (wreathModelHom S e w)) ≠ _
  rw [MulEquiv.orderOf_eq, orderOf_injective _ (wreathModelHom_injective S e)]
  exact V_orderOf_ne n hn w hw

theorem wreathedFusionDecomposition_mem_sylow (hn : 2 ≤ n) {P : Subgroup G} {x : G}
    (hxP : x ∈ P) (hx : orderOf x = 2 * 2 ^ n) {g : G}
    (hchain : WreathedFusionDecomposition (S : Subgroup G) e P g) :
    g ∈ (S : Subgroup G) := by
  induction hchain with
  | one => exact (S : Subgroup G).one_mem
  | @tail g h T _ hTS hcur hstep ih =>
      have hxT : g⁻¹ * x * g ∈ T := hcur ⟨x, hxP, by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]⟩
      have hord : orderOf (g⁻¹ * x * g) = 2 * 2 ^ n := by
        rw [show g⁻¹ * x * g = (MulAut.conj g⁻¹) x by simp,
          MulEquiv.orderOf_eq, hx]
      rcases hstep with ⟨rfl, hh⟩ | ⟨hT, -⟩ | ⟨⟨s, hT⟩, -⟩
      · exact (S : Subgroup G).mul_mem ih hh
      · rw [ambient_original_base_eq_modelBase] at hT
        subst hT
        exact absurd hord (orderOf_lt_of_mem_modelBase S e hxT).ne
      · rw [ambient_original_v_eq_modelV] at hT
        subst hT
        exact absurd hord (orderOf_ne_of_mem_rightConjugate_modelV S e hn hxT)

theorem root_pow_odd_ncard (hn : 2 ≤ n) :
    Set.ncard {g : G | ∃ h : ℕ, Odd h ∧ h < 2 ^ n ∧
      g = wreathModelHom S e (originalRoot (2 ^ n)) ^ h} = 2 ^ (n - 1) := by
  set R := wreathModelHom S e (originalRoot (2 ^ n))
  have hR : orderOf R = 2 * 2 ^ n := by
    rw [orderOf_injective _ (wreathModelHom_injective S e)]
    exact originalRoot_orderOf n hn
  have htwo : 2 ^ n = 2 * 2 ^ (n - 1) := (twice_half_two_pow n (by omega)).symm
  have hset : {g : G | ∃ h : ℕ, Odd h ∧ h < 2 ^ n ∧ g = R ^ h} =
      (fun k : ℕ => R ^ (2 * k + 1)) '' Set.Iio (2 ^ (n - 1)) := by
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_image, Set.mem_Iio]
    constructor
    · rintro ⟨h, ⟨k, rfl⟩, hlt, rfl⟩
      exact ⟨k, by omega, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨2 * k + 1, ⟨k, rfl⟩, by omega, rfl⟩
  rw [hset, Set.InjOn.ncard_image, Set.ncard_Iio_nat]
  intro k hk k' hk' hkk'
  have hinj := pow_injOn_Iio_orderOf (x := R)
  have h1 : 2 * k + 1 ∈ Set.Iio (orderOf R) := by
    simp only [Set.mem_Iio] at hk ⊢
    omega
  have h2 : 2 * k' + 1 ∈ Set.Iio (orderOf R) := by
    simp only [Set.mem_Iio] at hk' ⊢
    omega
  have := hinj h1 h2 hkk'
  omega

variable [Finite G]

include e in
theorem exists_sylow_conj_of_maximal_order (hn : 2 ≤ n) {x : G}
    (hxS : x ∈ (S : Subgroup G)) (hx : orderOf x = 2 * 2 ^ n) (g : G)
    (hg : g⁻¹ * x * g ∈ (S : Subgroup G)) :
    ∃ s ∈ (S : Subgroup G), s⁻¹ * x * s = g⁻¹ * x * g := by
  let P := Subgroup.zpowers x
  have hxP : x ∈ P := Subgroup.mem_zpowers _
  have hPS : P ≤ (S : Subgroup G) := Subgroup.zpowers_le.mpr hxS
  have hgP : rightConjugate P g ≤ (S : Subgroup G) := by
    rw [rightConjugate, Subgroup.conjBy, MonoidHom.map_zpowers]
    apply Subgroup.zpowers_le.mpr
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using hg
  obtain ⟨z, hchain, -, hzg⟩ := wreathed_fusion_decomposition S n hn e P hPS g hgP
  exact ⟨z, wreathedFusionDecomposition_mem_sylow S e hn hxP hx hchain, hzg x hxP⟩

omit [Finite G] in
theorem maximal_order_iff (hn : 2 ≤ n) (g : G) (hg : g ∈ (S : Subgroup G)) :
    orderOf g = 2 * 2 ^ n ↔
      ∃ a b : ℕ, Odd (a + b) ∧
        g = wreathModelHom S e (Original.z (2 ^ n)) *
          wreathModelHom S e (Original.s (2 ^ n)) ^ a *
            wreathModelHom S e (Original.t (2 ^ n)) ^ b := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hform (a b : ℕ) : wreathModelHom S e (Original.z (2 ^ (k + 1))) *
      wreathModelHom S e (Original.s (2 ^ (k + 1))) ^ a *
        wreathModelHom S e (Original.t (2 ^ (k + 1))) ^ b =
      wreathModelHom S e (element _ (b : ZMod (2 ^ (k + 1))) (a : ZMod (2 ^ (k + 1))) 1) := by
    rw [← map_pow, ← map_pow, ← map_mul, ← map_mul]
    congr 1
    simp only [Original.z, Original.s, Original.t, element_base_pow, nsmul_eq_mul, mul_one,
      mul_zero, add_zero, zero_add, element_swap_mul]
  obtain ⟨w, rfl⟩ := exists_wreathModelHom_eq S e hg
  rw [orderOf_injective _ (wreathModelHom_injective S e)]
  obtain ⟨⟨c, d, f⟩, rfl⟩ := (coordinateEquiv (2 ^ (k + 1))).symm.surjective w
  change orderOf (element _ c d f) = _ ↔ ∃ a b : ℕ, _ ∧ wreathModelHom S e (element _ c d f) = _
  rw [element_maximal_order_iff]
  constructor
  · rintro ⟨rfl, hodd⟩
    refine ⟨d.val, c.val, ?_, ?_⟩
    · rw [add_comm]
      exact (val_odd_iff_add (k + 1) (by omega) c d).mp hodd
    · rw [hform, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  · rintro ⟨a, b, hodd, heq⟩
    rw [hform] at heq
    have h := (element_eq_iff _ _ _ _ _ _ _).mp (wreathModelHom_injective S e heq)
    obtain ⟨rfl, rfl, rfl⟩ := h
    refine ⟨rfl, ?_⟩
    rw [← Nat.cast_add, natCast_val_odd_iff (k + 1) (by omega), add_comm]
    exact hodd

omit [Finite G] in
theorem modelHom_root_pow_odd (h : ℕ) :
    wreathModelHom S e (originalRoot (2 ^ n)) ^ (2 * h + 1) =
      wreathModelHom S e (element _ ((h + 1 : ℕ) : ZMod (2 ^ n)) (h : ZMod (2 ^ n)) 1) := by
  rw [← map_pow, originalRoot_pow_odd]

omit [Finite G] in
theorem exists_isConj_root_pow (hn : 2 ≤ n) (g : G) (hg : g ∈ (S : Subgroup G))
    (hord : orderOf g = 2 * 2 ^ n) :
    ∃ h : ℕ, Odd h ∧ 1 ≤ h ∧ h < 2 ^ n ∧
      ∃ s ∈ (S : Subgroup G), s⁻¹ * g * s = wreathModelHom S e (originalRoot (2 ^ n)) ^ h := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  obtain ⟨w, rfl⟩ := exists_wreathModelHom_eq S e hg
  rw [orderOf_injective _ (wreathModelHom_injective S e)] at hord
  obtain ⟨⟨c, d, f⟩, rfl⟩ := (coordinateEquiv (2 ^ (k + 1))).symm.surjective w
  change orderOf (element _ c d f) = _ at hord
  obtain ⟨rfl, hodd⟩ := (element_maximal_order_iff k c d f).mp hord
  set h := (c + d).val
  obtain ⟨j, hj⟩ := hodd
  have hlt : h < 2 ^ (k + 1) := ZMod.val_lt _
  refine ⟨h, ⟨j, hj⟩, by omega, hlt, ?_⟩
  have hconj : IsConj (element (2 ^ (k + 1)) c d 1)
      (element _ ((j + 1 : ℕ) : ZMod (2 ^ (k + 1))) (j : ZMod (2 ^ (k + 1))) 1) := by
    rw [swap_isConj_iff]
    have hcd : c + d = ((c + d).val : ZMod (2 ^ (k + 1))) := (ZMod.natCast_zmod_val _).symm
    rw [hcd]
    change ((h : ℕ) : ZMod (2 ^ (k + 1))) = _
    rw [hj]
    push_cast
    ring
  obtain ⟨t, ht⟩ := isConj_iff.mp hconj
  refine ⟨wreathModelHom S e t⁻¹, wreathModelHom_mem S e _, ?_⟩
  rw [hj, modelHom_root_pow_odd, ← ht]
  change (wreathModelHom S e t⁻¹)⁻¹ * wreathModelHom S e (element _ c d 1) *
    wreathModelHom S e t⁻¹ = _
  simp only [map_mul, map_inv, inv_inv]

theorem root_pow_isConj_iff (hn : 2 ≤ n) (h h' : ℕ) (hh : Odd h) (hh' : Odd h')
    (hlt : h < 2 ^ n) (hlt' : h' < 2 ^ n)
    (hconj : IsConj (wreathModelHom S e (originalRoot (2 ^ n)) ^ h)
      (wreathModelHom S e (originalRoot (2 ^ n)) ^ h')) : h = h' := by
  obtain ⟨j, rfl⟩ := hh
  obtain ⟨j', rfl⟩ := hh'
  set R := wreathModelHom S e (originalRoot (2 ^ n))
  have hR : orderOf (R ^ (2 * j + 1)) = 2 * 2 ^ n := by
    rw [modelHom_root_pow_odd, orderOf_injective _ (wreathModelHom_injective S e)]
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [element_maximal_order_iff]
    refine ⟨rfl, ?_⟩
    rw [← Nat.cast_add, natCast_val_odd_iff (k + 1) (by omega)]
    exact ⟨j, by ring⟩
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  have hgS : g⁻¹⁻¹ * R ^ (2 * j + 1) * g⁻¹ ∈ (S : Subgroup G) := by
    rw [inv_inv, hg]
    exact (S : Subgroup G).pow_mem (wreathModelHom_mem S e _) _
  obtain ⟨s, hs, hseq⟩ := exists_sylow_conj_of_maximal_order S e hn
    ((S : Subgroup G).pow_mem (wreathModelHom_mem S e _) _) hR g⁻¹ hgS
  rw [inv_inv, hg] at hseq
  obtain ⟨u, rfl⟩ := exists_wreathModelHom_eq S e hs
  rw [modelHom_root_pow_odd, modelHom_root_pow_odd, ← map_inv, ← map_mul, ← map_mul] at hseq
  have hw := wreathModelHom_injective S e hseq
  have hc : IsConj (element (2 ^ n) ((j + 1 : ℕ) : ZMod (2 ^ n)) (j : ZMod (2 ^ n)) 1)
      (element (2 ^ n) ((j' + 1 : ℕ) : ZMod (2 ^ n)) (j' : ZMod (2 ^ n)) 1) :=
    isConj_iff.mpr ⟨u⁻¹, by rw [inv_inv]; exact hw⟩
  rw [swap_isConj_iff] at hc
  have hc' : ((2 * j + 1 : ℕ) : ZMod (2 ^ n)) = ((2 * j' + 1 : ℕ) : ZMod (2 ^ n)) := by
    push_cast at hc ⊢
    linear_combination hc
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt hlt'] at hc'
  exact hc'

include e in
theorem exists_sylow_centralizer_eq_zpowers (hn : 2 ≤ n) (y : G) (hy : orderOf y = 2 * 2 ^ n) :
    ∃ P : Sylow 2 (Subgroup.centralizer ({y} : Set G)),
      (P : Subgroup _).map (Subgroup.centralizer ({y} : Set G)).subtype =
        Subgroup.zpowers y := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let C : Subgroup G := Subgroup.centralizer ({y} : Set G)
  let yC : C := ⟨y, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hyC : orderOf yC = 2 ^ (n + 1) := by
    rw [Subgroup.orderOf_mk, hy, pow_succ, Nat.mul_comm]
  have hZp : IsPGroup 2 (Subgroup.zpowers yC) :=
    IsPGroup.of_card (by rw [Nat.card_zpowers, hyC])
  obtain ⟨P, hZP⟩ := hZp.exists_le_sylow
  let Q : Subgroup G := (P : Subgroup C).map C.subtype
  have hQ : IsPGroup 2 Q := P.isPGroup'.map C.subtype
  obtain ⟨S', hQS⟩ := hQ.exists_le_sylow
  have hyP : yC ∈ (P : Subgroup C) := hZP (Subgroup.mem_zpowers yC)
  have hyS : y ∈ (S' : Subgroup G) := hQS ⟨yC, hyP, rfl⟩
  let yS : S' := ⟨y, hyS⟩
  let e' : S' ≃* Wreath (2 ^ n) := (Sylow.equiv S S').symm.trans e
  have hye : orderOf (e' yS) = 2 * 2 ^ n := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hy]
  have hcentral : Subgroup.centralizer ({e' yS} : Set (Wreath (2 ^ n))) =
      Subgroup.zpowers (e' yS) := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    subst n
    exact CFSG.Wreathed.SquareRootSmallCharacterRigidity.maximal_order_centralizer_eq_zpowers
      k _ hye
  refine ⟨P, le_antisymm ?_ ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    have hpS : (p : G) ∈ (S' : Subgroup G) := hQS ⟨p, hp, rfl⟩
    let pS : S' := ⟨p, hpS⟩
    have hcomm : Commute pS yS := by
      apply Subtype.ext
      exact Subgroup.mem_centralizer_singleton_iff.mp p.2
    have hemem : e' pS ∈ Subgroup.zpowers (e' yS) := by
      rw [← hcentral]
      exact Subgroup.mem_centralizer_singleton_iff.mpr (hcomm.map e').eq
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hemem
    have hpseq : yS ^ k = pS := e'.injective (by rw [map_zpow]; exact hk)
    apply Subgroup.mem_zpowers_iff.mpr
    refine ⟨k, ?_⟩
    exact congrArg (fun s : S' => (s : G)) hpseq
  · rw [Subgroup.zpowers_le]
    exact ⟨yC, hyP, rfl⟩

theorem exists_sylow_centralizer_root_zpow (hn : 2 ≤ n) (h : ℤ) (hh : Odd h) :
    ∃ P : Sylow 2 (Subgroup.centralizer
        ({wreathModelHom S e (originalRoot (2 ^ n)) ^ h} : Set G)),
      (P : Subgroup _).map (Subgroup.centralizer
          ({wreathModelHom S e (originalRoot (2 ^ n)) ^ h} : Set G)).subtype =
        Subgroup.zpowers (wreathModelHom S e (originalRoot (2 ^ n))) := by
  set R := wreathModelHom S e (originalRoot (2 ^ n))
  have hR : orderOf R = 2 * 2 ^ n := by
    rw [orderOf_injective _ (wreathModelHom_injective S e)]
    exact originalRoot_orderOf n hn
  have hcop : Nat.Coprime (orderOf R) h.natAbs := by
    rw [hR, ← pow_succ']
    apply Nat.Coprime.pow_left
    rw [Nat.coprime_two_left]
    exact Int.natAbs_odd.mpr hh
  have hRh : orderOf (R ^ h) = 2 * 2 ^ n := by
    rw [orderOf_zpow, Nat.Coprime.gcd_eq_one hcop, Nat.div_one, hR]
  have hzp : Subgroup.zpowers (R ^ h) = Subgroup.zpowers R := by
    apply Subgroup.eq_of_le_of_card_ge
    · exact Subgroup.zpowers_le.mpr (Subgroup.zpow_mem _ (Subgroup.mem_zpowers R) h)
    · rw [Nat.card_zpowers, Nat.card_zpowers, hRh, hR]
  obtain ⟨P, hP⟩ := exists_sylow_centralizer_eq_zpowers S e hn (R ^ h) hRh
  exact ⟨P, hP.trans hzp⟩

end CFSG.Wreathed.BrauerWong
