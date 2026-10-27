module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81E6PXC
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81E6PXT

public section

namespace CFSG.ComponentClassification.GSThmB

namespace P211X

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer P211
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

variable {X : Type} [Group X] {Q : ℕ → Prop}

theorem v2_centerQuotient_lt_of_comm {G : Type*} [Group G] [Finite G] {s : G}
    (hs : orderOf s = 2) {C : Subgroup G} (hmemC : ∀ x : G, x ∈ C → x * s = s * x)
    (L : Subgroup C) :
    padicValNat 2 (Nat.card (L ⧸ center L)) < padicValNat 2 (Nat.card G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL'C : L.map C.subtype ≤ C := map_subtype_le L
  have hLL' : Nat.card (L.map C.subtype) = Nat.card L := card_map_of_injective C.subtype_injective
  have hvL : padicValNat 2 (Nat.card L) = padicValNat 2 (Nat.card (L ⧸ center L)) +
      padicValNat 2 (Nat.card (center L)) := by
    rw [card_eq_card_quotient_mul_card_subgroup (center L),
      padicValNat.mul Nat.card_pos.ne' Nat.card_pos.ne']
  have hvG : padicValNat 2 (Nat.card (L.map C.subtype)) ≤ padicValNat 2 (Nat.card G) :=
    (padicValNat_dvd_iff_le Nat.card_pos.ne').1
      (pow_padicValNat_dvd.trans (card_subgroup_dvd_card _))
  rw [hLL'] at hvG
  rw [← not_le]
  intro hlt
  have heq : padicValNat 2 (Nat.card (L.map C.subtype)) = padicValNat 2 (Nat.card G) := by
    rw [hLL']
    omega
  obtain ⟨P⟩ : Nonempty (Sylow 2 (L.map C.subtype)) := inferInstance
  have hT : Nat.card ((P : Subgroup (L.map C.subtype)).map (L.map C.subtype).subtype) =
      2 ^ (Nat.card G).factorization 2 := by
    rw [card_map_of_injective (L.map C.subtype).subtype_injective, P.card_eq_multiplicity,
      Nat.factorization_def _ Nat.prime_two, Nat.factorization_def _ Nat.prime_two, heq]
  set T : Subgroup G := (P : Subgroup (L.map C.subtype)).map (L.map C.subtype).subtype
    with hTdef
  have hTL' : T ≤ L.map C.subtype := map_subtype_le _
  have hsT : zpowers s ≤ normalizer (T : Set G) := by
    rw [zpowers_le]
    exact centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun t ht =>
      hmemC t (hL'C (hTL' ht)))
  have hps : IsPGroup 2 (zpowers s) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hs, pow_one])
  have hmax := (Sylow.ofCard T hT).is_maximal'
    ((IsPGroup.of_card hT).to_sup_of_normal_left' hps hsT) le_sup_left
  have hsT' : s ∈ T := by
    have h1 : s ∈ T ⊔ zpowers s := (le_sup_right : zpowers s ≤ T ⊔ zpowers s) (mem_zpowers s)
    rw [hmax] at h1
    exact h1
  obtain ⟨x, hxL, hx⟩ := mem_map.mp (hTL' hsT')
  have hxs : ((x : C) : G) = s := hx
  have hxZ : (⟨x, hxL⟩ : L) ∈ center L := by
    rw [mem_center_iff]
    intro y
    apply Subtype.ext
    apply Subtype.ext
    change ((y : C) : G) * (x : G) = (x : G) * ((y : C) : G)
    rw [hxs]
    exact hmemC _ (y : C).2
  have hord : orderOf (⟨⟨x, hxL⟩, hxZ⟩ : center L) = 2 := by
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, ← Subgroup.orderOf_coe x, hxs, hs]
  have h2 : 2 ∣ Nat.card (center L) := hord ▸ orderOf_dvd_natCard _
  have := one_le_padicValNat_of_dvd (p := 2) Nat.card_pos.ne' h2
  omega

theorem v2_centerQuotient_lt {G : Type*} [Group G] [Finite G] {s : G} (hs : orderOf s = 2)
    (L : Subgroup (fixedSubgroup (MulAut.conj s))) :
    padicValNat 2 (Nat.card (L ⧸ center L)) < padicValNat 2 (Nat.card G) := by
  refine v2_centerQuotient_lt_of_comm hs (fun x hx => ?_) L
  have h1 : MulAut.conj s x = x := hx
  rw [MulAut.conj_apply] at h1
  calc x * s = s * x * s⁻¹ * s := by rw [h1]
    _ = s * x := by group

theorem orderOf_conj_eq {G : Type*} [Group G] (hZ : center G = ⊥) (s : G) :
    orderOf (MulAut.conj s) = orderOf s := by
  refine orderOf_injective _ (fun x y hxy => ?_) s
  have hc : y⁻¹ * x ∈ center G := mem_center_iff.mpr fun g => by
    have h1 := congrArg (fun φ : MulAut G => φ g) hxy
    simp only [MulAut.conj_apply] at h1
    calc g * (y⁻¹ * x) = y⁻¹ * (y * g * y⁻¹) * x := by group
      _ = y⁻¹ * (x * g * x⁻¹) * x := by rw [h1]
      _ = y⁻¹ * x * g := by group
  rw [hZ, mem_bot, inv_mul_eq_one] at hc
  exact hc.symm

theorem center_fstar_eq_bot (hC : centralizer (generalizedFitting X : Set X) = ⊥) :
    center ↥(generalizedFitting X) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have hz' : (z : X) ∈ centralizer (generalizedFitting X : Set X) :=
    mem_centralizer_iff.mpr fun y hy => congrArg Subtype.val ((mem_center_iff.mp hz) ⟨y, hy⟩)
  rw [hC, mem_bot] at hz'
  exact mem_bot.mpr (Subtype.ext hz')

theorem CompOrd.of_card_dvd {G : Type*} [Group G] [Finite G]
    (h : ∀ v, v ∣ Nat.card G → Q v) : CompOrd Q G := fun L _ =>
  h _ ((card_quotient_dvd_card (center L)).trans (card_subgroup_dvd_card L))

theorem p211_of_outer [Finite X] (hC : centralizer (generalizedFitting X : Set X) = ⊥)
    (hsolv : Group.IsSolvable (OuterAutomorphisms.Outer ↥(generalizedFitting X)))
    (hQS : CatLeaf.FixedTwoComponentsQuasisimple ↥(generalizedFitting X)) {n : ℕ}
    (hF : padicValNat 2 (Nat.card (generalizedFitting X)) = 2 * n)
    (hout : ∀ β : MulAut ↥(generalizedFitting X), orderOf β = 2 →
      β ∉ OuterAutomorphisms.inner ↥(generalizedFitting X) →
        CompOrd (fun v => padicValNat 2 v < 2 * n) (fixedSubgroup β))
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) {J D : Subgroup X}
    (hJt : IsSec8JType (J ⧸ pPrimeCore 2 J) p f) (hDJ : D ≤ J)
    (hDsyl : ∃ R : Sylow 2 ↥J, (R : Subgroup ↥J) = D.subgroupOf J)
    (hbound : ∀ R : Subgroup X, R ≤ generalizedFitting X → IsPGroup 2 R →
      Nat.card R ≤ 2 * Nat.card D ^ 2)
    {b : X} {K : Subgroup X} (hb : b * b = 1) (hb1 : b ≠ 1)
    (hKC : K ≤ centralizer ({b} : Set X))
    (hK : IsPComponent 2 (K.subgroupOf (centralizer ({b} : Set X))))
    (hKt : IsSec8Socle (K ⧸ pPrimeCore 2 K) p f) : False := by
  obtain ⟨N, hN⟩ := exists_derivedSeries_le_of_isSolvable (OuterAutomorphisms.inner _) hsolv
  have hKF : K ≤ generalizedFitting X :=
    le_fstar_of_perfect hC (MulEquiv.refl _) hN (commutator_eq_of_isPComp hKC hK)
  obtain ⟨-, hKv, hFv⟩ := p211_two_adic hp hp2 hf hJt hDJ hDsyl hbound hKt
  obtain ⟨β, hβ, L, hL, hLv⟩ := exists_fixed_component hC hQS hb hb1 hKC hK hKF
    (center_socle_eq_bot hp hp2 hf hKt)
  have hlt : padicValNat 2 (Nat.card (L ⧸ center L)) < 2 * n := by
    by_cases hin : β ∈ OuterAutomorphisms.inner ↥(generalizedFitting X)
    · obtain ⟨s, rfl⟩ := hin
      have hs : orderOf s = 2 := (orderOf_conj_eq (center_fstar_eq_bot hC) s).symm.trans hβ
      have h1 := v2_centerQuotient_lt hs L
      rw [hF] at h1
      exact h1
    · exact hout β hβ hin L hL
  omega

theorem v2_ordG2 {q : ℕ} (hq : Odd q) (hq3 : 3 ≤ q) :
    padicValNat 2 (Open.ordG2 q) = 2 * padicValNat 2 (q ^ 2 - 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : q ^ 6 ≠ 0 := pow_ne_zero _ (by omega)
  have h2 : q ^ 6 - 1 ≠ 0 := pow_sub_one_ne_zero (by omega) (by norm_num)
  have h3 : q ^ 2 - 1 ≠ 0 := pow_sub_one_ne_zero (by omega) (by norm_num)
  have h6 : q ^ 6 - 1 = (q ^ 2) ^ 3 - 1 := by rw [← pow_mul]
  rw [Open.ordG2, padicValNat.mul (mul_ne_zero h1 h2) h3, padicValNat.mul h1 h2,
    v2_odd' hq.pow.not_two_dvd_nat, h6,
    v2_cube_sub hq.pow (le_trans hq3 (Nat.le_self_pow two_ne_zero q))]
  ring

theorem v2_ordTrialityD4 {q : ℕ} (hq : Odd q) (hq3 : 3 ≤ q) :
    padicValNat 2 (Open.ordTrialityD4 q) = 2 * padicValNat 2 (q ^ 2 - 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h0 : q ^ 12 ≠ 0 := pow_ne_zero _ (by omega)
  have h1 : q ^ 8 + q ^ 4 + 1 ≠ 0 := by omega
  have h2 : q ^ 6 - 1 ≠ 0 := pow_sub_one_ne_zero (by omega) (by norm_num)
  have h3 : q ^ 2 - 1 ≠ 0 := pow_sub_one_ne_zero (by omega) (by norm_num)
  have h6 : q ^ 6 - 1 = (q ^ 2) ^ 3 - 1 := by rw [← pow_mul]
  have hodd : Odd (q ^ 8 + q ^ 4 + 1) := (hq.pow.add_odd hq.pow).add_one
  rw [Open.ordTrialityD4, padicValNat.mul (mul_ne_zero (mul_ne_zero h0 h1) h2) h3,
    padicValNat.mul (mul_ne_zero h0 h1) h2, padicValNat.mul h0 h1,
    v2_odd' hq.pow.not_two_dvd_nat, v2_odd' hodd.not_two_dvd_nat, h6,
    v2_cube_sub hq.pow (le_trans hq3 (Nat.le_self_pow two_ne_zero q))]
  ring

theorem v2_sq_sq_sub {q : ℕ} (hq : Odd q) (hq3 : 3 ≤ q) :
    padicValNat 2 ((q ^ 2) ^ 2 - 1) = padicValNat 2 (q ^ 2 - 1) + 1 := by
  have h4 : q ^ 2 % 4 = 1 := by
    obtain ⟨k, rfl⟩ := hq
    rw [show (2 * k + 1) ^ 2 = 4 * (k * k + k) + 1 by ring]
    omega
  rw [v2_sq_sub (le_trans hq3 (Nat.le_self_pow two_ne_zero q)), v2_add_of_mod_four h4]

end P211X

end CFSG.ComponentClassification.GSThmB
