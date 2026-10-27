module

public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicTwoAutomorphisms
public import CFSG.LocalAnalysis.LargeEvenClassification.FrattiniKernelCount
public import CFSG.LocalAnalysis.LargeEvenClassification.MacWilliamsFrattini

public section

namespace CFSG.LargeEvenClassification.Helpers

open scoped commutatorElement

theorem cyclicTwoAut_isPGroup (n : ℕ) : IsPGroup 2 (CyclicTwoAut n) :=
  IsPGroup.of_card (cyclicTwoAut_card n)

theorem cyclicTwo_scalar_subgroup_rank (n : ℕ) (B : Subgroup (CyclicTwoAut n))
    (hle : B ≤ (cyclicTwoScalar n).range) : pGeneratorRank 2 B ≤ 2 := by
  let e := MonoidHom.ofInjective (cyclicTwoScalar_injective n)
  let embedding : B →* (ZMod (2 ^ (n + 2) * 2))ˣ :=
    e.symm.toMonoidHom.comp (B.inclusion hle)
  have hinjective : Function.Injective embedding :=
    e.symm.injective.comp (Subgroup.inclusion_injective hle)
  let transported := (cyclicTwoUnitEquiv n).toMonoidHom.comp embedding
  exact two_group_embedding_binary_units_rank (n + 3) transported
    ((cyclicTwoUnitEquiv n).injective.comp hinjective)

theorem cyclicTwo_subgroup_generator_bound (n : ℕ) (H : Subgroup (CyclicTwoAut n)) :
    pGeneratorRank 2 H ≤ 4 := by
  exact cyclicTwoAction_four_generator_rank (2 ^ (n + 2)) (dvd_pow_self 2 (by omega)) H.subtype
    ((cyclicTwoAut_isPGroup n).to_subgroup H) Subtype.val_injective (n + 3) (pow_succ _ _).symm

theorem cyclic_two_group_subgroup_contains_involution {G : Type*} [Group G] [Finite G] [IsCyclic G]
    (hpgroup : IsPGroup 2 G) (δ : G) (horder : orderOf δ = 2)
    (D : Subgroup G) (hne : D ≠ ⊥) : δ ∈ D := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD := hpgroup.to_subgroup D
  rcases hD.card_eq_or_dvd with hone | hdivides
  · exact False.elim (hne (Subgroup.card_eq_one.mp hone))
  · obtain ⟨d, hd⟩ := exists_prime_orderOf_dvd_card' 2 hdivides
    have hvalOrder : orderOf d.val = 2 :=
      (orderOf_injective D.subtype Subtype.val_injective d).trans hd
    have heq := cyclic_two_group_involutions_unique d.val δ hvalOrder horder
    exact heq ▸ d.property

theorem commutator_mul_central_right {G : Type*} [Group G] (a b c d : G)
    (hc : ∀ g : G, Commute c g) (hd : ∀ g : G, Commute d g) :
    ⁅a * c, b * d⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul, (hc _).commutator_eq, mul_one,
    commutatorElement_mul_right_eq_mul_conj, (hd a).symm.commutator_eq]
  simp [mul_assoc]

theorem cyclicTwo_shear_lift_normal_form (n : ℕ) (g : CyclicTwoAut n)
    (v w : ZMod 2) (hshear : cyclicTwoShearHom n g = Multiplicative.ofAdd (v, w)) :
    ∃ u : (ZMod (2 ^ (n + 2) * 2))ˣ,
      g = cyclicTwoTau n ^ v.val * cyclicTwoRho n ^ w.val * cyclicTwoScalar n u := by
  obtain ⟨v', w', u, hg⟩ := cyclicTwoAut_normal_form n g
  have hmap := hshear
  rw [hg] at hmap
  simp only [map_mul, map_pow, cyclicTwoShearHom_tau,
    cyclicTwoShearHom_rho, cyclicTwoShearHom_scalar] at hmap
  have hcoords := congrArg Multiplicative.toAdd hmap
  change v'.val • ((1, 0) : ZMod 2 × ZMod 2) + w'.val • ((0, 1) : ZMod 2 × ZMod 2) + 0 =
    (v, w) at hcoords
  have hv : v' = v := by
    have h := congrArg Prod.fst hcoords
    simpa [nsmul_eq_mul] using h
  have hw : w' = w := by
    have h := congrArg Prod.snd hcoords
    simpa [nsmul_eq_mul] using h
  exact ⟨u, hv ▸ hw ▸ hg⟩

theorem cyclicTwo_shear_lift_commutator (n : ℕ) (g h : CyclicTwoAut n)
    (hg : cyclicTwoShearHom n g = Multiplicative.ofAdd (1, 0))
    (hh : cyclicTwoShearHom n h = Multiplicative.ofAdd (0, 1)) : ⁅g, h⁆ = cyclicTwoDelta n := by
  obtain ⟨u, hu⟩ := cyclicTwo_shear_lift_normal_form n g 1 0 hg
  obtain ⟨v, hv⟩ := cyclicTwo_shear_lift_normal_form n h 0 1 hh
  rw [hu, hv]
  simp only [ZMod.val_one, ZMod.val_zero, pow_one, pow_zero, mul_one, one_mul]
  rw [commutator_mul_central_right]
  · exact cyclicTwoTauRho_commutator n
  · exact cyclicTwoScalar_central n u
  · exact cyclicTwoScalar_central n v

theorem cyclicTwo_delta_mem_cyclic_scalars (n : ℕ) :
    cyclicTwoDelta n ∈ Subgroup.zpowers (cyclicTwoC n) := by
  rw [← cyclicTwoC_half_power]
  exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _

theorem cyclicTwo_delta_order (n : ℕ) : orderOf (cyclicTwoDelta n) = 2 :=
  orderOf_eq_prime_iff.mpr ⟨cyclicTwoDelta_square n, cyclicTwoDelta_ne_one n⟩

theorem cyclicTwo_no_delta_quotient_injective (n : ℕ) (H : Subgroup (CyclicTwoAut n))
    (hdelta : cyclicTwoDelta n ∉ H) :
    Function.Injective ((QuotientGroup.mk' (Subgroup.zpowers (cyclicTwoC n))).comp H.subtype) := by
  let P := Subgroup.zpowers (cyclicTwoC n)
  let δ : P := ⟨cyclicTwoDelta n, cyclicTwo_delta_mem_cyclic_scalars n⟩
  have horder : orderOf δ = 2 :=
    (orderOf_injective P.subtype Subtype.val_injective δ).symm.trans (cyclicTwo_delta_order n)
  have hintersection : H.subgroupOf P = ⊥ := by
    by_contra hne
    have hmem := cyclic_two_group_subgroup_contains_involution
      ((cyclicTwoAut_isPGroup n).to_subgroup P) δ horder (H.subgroupOf P) hne
    exact hdelta hmem
  let f := (QuotientGroup.mk' P).comp H.subtype
  apply (f.ker_eq_bot_iff).mp
  apply le_antisymm _ bot_le
  intro x hx
  have hxP : (x : CyclicTwoAut n) ∈ P := (QuotientGroup.eq_one_iff _).mp hx
  have hxIntersection : (⟨x.val, hxP⟩ : P) ∈ H.subgroupOf P := x.property
  rw [hintersection] at hxIntersection
  have hone := congrArg Subtype.val (Subgroup.mem_bot.mp hxIntersection)
  exact Subgroup.mem_bot.mpr (Subtype.ext hone)

theorem cyclicTwo_three_generators_contains_delta (n : ℕ) (H : Subgroup (CyclicTwoAut n))
    (hrank : 3 ≤ pGeneratorRank 2 H) : cyclicTwoDelta n ∈ H := by
  by_contra hdelta
  let P := Subgroup.zpowers (cyclicTwoC n)
  let projection := QuotientGroup.mk' P
  let f := projection.comp H.subtype
  have hinjective : Function.Injective f := cyclicTwo_no_delta_quotient_injective n H hdelta
  obtain ⟨hcommutative, hexponent, hcard⟩ := cyclicTwoAut_cyclic_scalar_quotient n
  let : CommGroup (CyclicTwoAut n ⧸ P) := {
    (inferInstance : Group (CyclicTwoAut n ⧸ P)) with mul_comm := @mul_comm' _ _ hcommutative }
  have hHcommutative : IsMulCommutative H := by
    apply IsMulCommutative.of_comm
    intro x y
    apply hinjective
    simp only [map_mul]
    exact mul_comm _ _
  let : CommGroup H := { (inferInstance : Group H) with mul_comm := @mul_comm' _ _ hHcommutative }
  have hHexponent (x : H) : x ^ 2 = 1 := by
    apply hinjective
    rw [map_pow, map_one]
    exact hexponent (f x)
  have hpH := (cyclicTwoAut_isPGroup n).to_subgroup H
  have hrankLog := elementary_pGeneratorRank_eq_log_card Nat.prime_two hHexponent
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨r, hr⟩ := hpH.exists_card_eq
  have hrge : 3 ≤ r := by
    rw [hrankLog, hr, Nat.log_pow (by decide : 1 < 2)] at hrank
    exact hrank
  have hHcard : 8 ≤ Nat.card H := by
    rw [hr]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hrge
  have hrangeCard : Nat.card H = Nat.card f.range :=
    Nat.card_congr (MonoidHom.ofInjective hinjective).toEquiv
  have hfull : f.range = ⊤ := by
    apply Subgroup.eq_of_le_of_card_ge le_top
    rw [Nat.card_congr (Subgroup.topEquiv (G := CyclicTwoAut n ⧸ P)).toEquiv, ← hrangeCard]
    exact hcard ▸ hHcard
  have hsurjective : Function.Surjective f := MonoidHom.range_eq_top.mp hfull
  obtain ⟨g, hg⟩ := hsurjective (projection (cyclicTwoTau n))
  obtain ⟨h, hh⟩ := hsurjective (projection (cyclicTwoRho n))
  have hscalar (x : H) (a : CyclicTwoAut n) (heq : f x = projection a) :
      ∃ u : (ZMod (2 ^ (n + 2) * 2))ˣ, x.val = a * cyclicTwoScalar n u := by
    have hmem : a⁻¹ * x.val ∈ P := by
      apply (QuotientGroup.eq_one_iff _).mp
      change projection (a⁻¹ * x.val) = 1
      rw [map_mul, map_inv, show projection x.val = projection a from heq, inv_mul_cancel]
    have hPscalar : P ≤ (cyclicTwoScalar n).range :=
      Subgroup.zpowers_le.mpr ⟨cyclicTwoFive n, rfl⟩
    obtain ⟨u, hu⟩ := hPscalar hmem
    exact ⟨u, by rw [hu]; exact (mul_inv_cancel_left a x.val).symm⟩
  obtain ⟨u, hu⟩ := hscalar g (cyclicTwoTau n) hg
  obtain ⟨v, hv⟩ := hscalar h (cyclicTwoRho n) hh
  have hcommutator : ⁅g.val, h.val⁆ = cyclicTwoDelta n := by
    rw [hu, hv, commutator_mul_central_right]
    · exact cyclicTwoTauRho_commutator n
    · exact cyclicTwoScalar_central n u
    · exact cyclicTwoScalar_central n v
  apply hdelta
  rw [← hcommutator]
  exact (⁅g, h⁆ : H).property

theorem cyclic_two_power_subgroup {G : Type*} [Group G] [Finite G]
    (c : G) (m : ℕ) (horder : orderOf c = 2 ^ m) (D : Subgroup G)
    (hle : D ≤ Subgroup.zpowers c) :
    ∃ k : ℕ, k ≤ m ∧ D = Subgroup.zpowers (c ^ (2 ^ k)) := by
  let P := Subgroup.zpowers c
  have hpP : IsPGroup 2 P := IsPGroup.of_card ((Nat.card_zpowers c).trans horder)
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨r, hr⟩ := (hpP.to_subgroup (D.subgroupOf P)).exists_card_eq
  have hDcard : Nat.card D = 2 ^ r :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv).symm.trans hr
  have hrle : r ≤ m := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    rw [← hDcard, ← horder, ← Nat.card_zpowers]
    exact Subgroup.card_le_of_le hle
  refine ⟨m - r, by omega, ?_⟩
  let E := Subgroup.zpowers (c ^ (2 ^ (m - r)))
  have hEle : E ≤ P := Subgroup.zpowers_le.mpr (P.pow_mem (Subgroup.mem_zpowers _) _)
  have hEcard : Nat.card E = 2 ^ r := by
    rw [Nat.card_zpowers, orderOf_pow, horder,
      Nat.gcd_eq_right (Nat.pow_dvd_pow 2 (by omega : m - r ≤ m))]
    have hfactor : 2 ^ m = 2 ^ r * 2 ^ (m - r) := by
      rw [← pow_add, Nat.add_sub_of_le hrle]
    rw [hfactor, Nat.mul_div_cancel]
    positivity
  have heq : D.subgroupOf P = E.subgroupOf P := by
    apply IsCyclic.subgroup_eq_iff_card_eq.mpr
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEle).toEquiv, hDcard, hEcard]
  ext x
  constructor
  · intro hx
    have hsub : (⟨x, hle hx⟩ : P) ∈ D.subgroupOf P := hx
    have hsubE : (⟨x, hle hx⟩ : P) ∈ E.subgroupOf P := heq ▸ hsub
    exact hsubE
  · intro hx
    have hsub : (⟨x, hEle hx⟩ : P) ∈ E.subgroupOf P := hx
    have hsubD : (⟨x, hEle hx⟩ : P) ∈ D.subgroupOf P := heq.symm ▸ hsub
    exact hsubD

theorem cyclicTwo_scalar_subgroup_commutative (n : ℕ) (B : Subgroup (CyclicTwoAut n))
    (hle : B ≤ (cyclicTwoScalar n).range) : IsMulCommutative B := by
  apply IsMulCommutative.of_comm
  intro x y
  apply Subtype.ext
  obtain ⟨u, hu⟩ := hle x.property
  change x.val * y.val = y.val * x.val
  rw [← hu]
  exact (cyclicTwoScalar_central n u y.val).eq

theorem commutative_two_group_square_kernel_card {G : Type*} [CommGroup G] [Finite G]
    (hpgroup : IsPGroup 2 G) :
    Nat.card (powMonoidHom 2 : G →* G).ker = 2 ^ pGeneratorRank 2 G := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨r, hr⟩ := (hpgroup.to_quotient (frattini G)).exists_card_eq
  rw [← commutative_frattini_card_eq_power_kernel Nat.prime_two hpgroup]
  change Nat.card (G ⧸ frattini G) = 2 ^ Nat.log 2 (Nat.card (G ⧸ frattini G))
  rw [hr, Nat.log_pow (by decide : 1 < 2)]

theorem cyclicTwo_scalar_involutions_mem (n : ℕ) (B : Subgroup (CyclicTwoAut n))
    (hle : B ≤ (cyclicTwoScalar n).range) (hrank : 2 ≤ pGeneratorRank 2 B)
    (u : (ZMod (2 ^ (n + 2) * 2))ˣ) (hsquare : u ^ 2 = 1) : cyclicTwoScalar n u ∈ B := by
  let U := (ZMod (2 ^ (n + 2) * 2))ˣ
  let e := MonoidHom.ofInjective (cyclicTwoScalar_injective n)
  let embedding : B →* U := e.symm.toMonoidHom.comp (B.inclusion hle)
  have hinjective : Function.Injective embedding :=
    e.symm.injective.comp (Subgroup.inclusion_injective hle)
  have hrepresent (b : B) : cyclicTwoScalar n (embedding b) = b.val :=
    congrArg Subtype.val (e.apply_symm_apply (B.inclusion hle b))
  let : CommGroup B := { (inferInstance : Group B) with
    mul_comm := @mul_comm' _ _ (cyclicTwo_scalar_subgroup_commutative n B hle) }
  have hpB := (cyclicTwoAut_isPGroup n).to_subgroup B
  have hpU : IsPGroup 2 U := (binary_units_isPGroup (n + 3)).of_injective
    (cyclicTwoUnitEquiv n).toMonoidHom (cyclicTwoUnitEquiv n).injective
  have hUrank : pGeneratorRank 2 U ≤ 2 := by
    exact two_group_embedding_binary_units_rank (n + 3)
      (cyclicTwoUnitEquiv n).toMonoidHom (cyclicTwoUnitEquiv n).injective
  let K := (powMonoidHom 2 : U →* U).ker
  let D := (powMonoidHom 2 : B →* B).ker
  let f : D →* K := {
    toFun := fun b => ⟨embedding b.val, by
      change (embedding b.val) ^ 2 = 1
      rw [← map_pow, show b.val ^ 2 = 1 from b.property, map_one]⟩
    map_one' := Subtype.ext (map_one embedding)
    map_mul' := fun x y => Subtype.ext (map_mul embedding x.val y.val) }
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    exact hinjective (congrArg Subtype.val h)
  have hDcard : Nat.card D = 4 := by
    rw [commutative_two_group_square_kernel_card hpB,
      le_antisymm (cyclicTwo_scalar_subgroup_rank n B hle) hrank]
    decide
  have hKcard : Nat.card K ≤ 4 := by
    rw [commutative_two_group_square_kernel_card hpU]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hUrank
  have hfull : f.range = ⊤ := by
    apply Subgroup.eq_of_le_of_card_ge le_top
    rw [Nat.card_congr (Subgroup.topEquiv (G := K)).toEquiv,
      ← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv, hDcard]
    exact hKcard
  obtain ⟨b, hb⟩ := (MonoidHom.range_eq_top.mp hfull) (⟨u, hsquare⟩ : K)
  have heq : embedding b.val = u := congrArg Subtype.val hb
  rw [← heq, hrepresent]
  exact b.val.property

theorem cyclicTwo_scalar_rank_two_subgroup (n : ℕ) (B : Subgroup (CyclicTwoAut n))
    (hle : B ≤ (cyclicTwoScalar n).range) (hrank : 2 ≤ pGeneratorRank 2 B) :
    ∃ k : ℕ, k ≤ n + 1 ∧
      B = Subgroup.zpowers (cyclicTwoC n ^ (2 ^ k)) ⊔ Subgroup.zpowers (cyclicTwoZ n) := by
  have hz : cyclicTwoZ n ∈ B := by
    apply cyclicTwo_scalar_involutions_mem n B hle hrank (-1)
    apply Units.ext
    change (-1 : ZMod (2 ^ (n + 2) * 2)) ^ 2 = 1
    ring
  let P := Subgroup.zpowers (cyclicTwoC n)
  let D := B ⊓ P
  obtain ⟨k, hk, hD⟩ := cyclic_two_power_subgroup (cyclicTwoC n) (n + 1)
    (cyclicTwoC_order n) D inf_le_right
  refine ⟨k, hk, ?_⟩
  rw [← hD]
  apply le_antisymm
  · intro g hg
    obtain ⟨u, hu⟩ := hle hg
    obtain ⟨j, e, heq⟩ := cyclicTwo_scalar_normal_form n u
    have hnormal : g = cyclicTwoC n ^ j * cyclicTwoZ n ^ e.val := by
      rw [← hu, heq, map_mul, map_zpow, map_pow]
      rfl
    have hzpow : cyclicTwoZ n ^ e.val ∈ B := B.pow_mem hz _
    have hcB : cyclicTwoC n ^ j ∈ B := by
      have hproduct := B.mul_mem hg (B.inv_mem hzpow)
      rw [hnormal, mul_inv_cancel_right] at hproduct
      exact hproduct
    rw [hnormal]
    exact Subgroup.mul_mem_sup ⟨hcB, P.zpow_mem (Subgroup.mem_zpowers _) _⟩
      (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _)
  · exact sup_le inf_le_left (Subgroup.zpowers_le.mpr hz)

theorem cyclicTwo_rank_four_scalar_squares (n : ℕ) (H : Subgroup (CyclicTwoAut n))
    (hrank : pGeneratorRank 2 H = 4) :
    pGeneratorRank 2 ↥(H ⊓ (cyclicTwoScalar n).range) = 2 ∧
      Function.Surjective ((cyclicTwoShearHom n).comp H.subtype) ∧
      (∀ x : H, ∃ b : ↥(H ⊓ (cyclicTwoScalar n).range), b.val ^ 2 = x.val ^ 2) ∧
      ∃ b : ↥(H ⊓ (cyclicTwoScalar n).range), b.val ^ 2 = cyclicTwoDelta n := by
  let V := Multiplicative (ZMod 2 × ZMod 2)
  let f := (cyclicTwoShearHom n).comp H.subtype
  let q := f.rangeRestrict
  let N := q.ker
  let B := H ⊓ (cyclicTwoScalar n).range
  have hpH := (cyclicTwoAut_isPGroup n).to_subgroup H
  have hpR := hpH.of_surjective q f.rangeRestrict_surjective
  let : CommGroup f.range := { (inferInstance : Group f.range) with
    mul_comm := fun x y => by
      apply Subtype.ext
      apply Multiplicative.toAdd.injective
      exact add_comm _ _ }
  have hNmem (x : H) : x ∈ N ↔ x.val ∈ (cyclicTwoScalar n).range := by
    change q x = 1 ↔ _
    have hq : q x = 1 ↔ f x = 1 := Subtype.ext_iff
    rw [hq]
    change x.val ∈ (cyclicTwoShearHom n).ker ↔ _
    rw [cyclicTwoShearHom_kernel]
  let e : N ≃* B := {
    toFun := fun x => ⟨x.val.val, x.val.property, (hNmem x.val).mp x.property⟩
    invFun := fun x => ⟨⟨x.val, x.property.1⟩, (hNmem _).mpr x.property.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_mul' := fun _ _ => rfl }
  have hNequiv := pGeneratorRank_mulEquiv Nat.prime_two (hpH.to_subgroup N) e
  have hNcommutative : IsMulCommutative N := by
    apply IsMulCommutative.of_comm
    intro x y
    apply e.injective
    simp only [map_mul]
    let : CommGroup B := { (inferInstance : Group B) with
      mul_comm := @mul_comm' _ _ (cyclicTwo_scalar_subgroup_commutative n B inf_le_right) }
    exact mul_comm _ _
  have hNrank : pGeneratorRank 2 N ≤ 2 :=
    hNequiv ▸ cyclicTwo_scalar_subgroup_rank n B inf_le_right
  have hRexponent (x : f.range) : x ^ 2 = 1 := by
    apply Subtype.ext
    change Multiplicative.ofAdd (2 • x.val.toAdd) = 1
    have hbinary : ∀ x : ZMod 2 × ZMod 2, 2 • x = 0 := by decide +kernel
    rw [hbinary]
    rfl
  have hRrank : pGeneratorRank 2 f.range ≤ 2 := by
    rw [elementary_pGeneratorRank_eq_log_card Nat.prime_two hRexponent]
    have hcard : Nat.card f.range ≤ 4 := by
      have hVcard : Nat.card V = 4 := by rw [Nat.card_eq_fintype_card]; decide +kernel
      exact hVcard ▸ f.range.card_le_card_group
    exact (Nat.log_mono_right hcard).trans (by decide : Nat.log 2 4 ≤ 2)
  let equivalence := QuotientGroup.quotientKerEquivOfSurjective q f.rangeRestrict_surjective
  have hquotient := pGeneratorRank_mulEquiv Nat.prime_two (hpH.to_quotient N) equivalence
  have hbound := pGeneratorRank_extension_le Nat.prime_two hpH N
  rw [hquotient, hrank] at hbound
  have hNrankEq : pGeneratorRank 2 N = 2 := by omega
  have hRrankEq : pGeneratorRank 2 f.range = 2 := by omega
  have hsurjective : Function.Surjective f := by
    have hcard : Nat.card f.range = 4 := by
      let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨r, hr⟩ := hpR.exists_card_eq
      have hrankLog := hRrankEq
      rw [elementary_pGeneratorRank_eq_log_card Nat.prime_two hRexponent,
        hr, Nat.log_pow (by decide : 1 < 2)] at hrankLog
      rw [hr, hrankLog]
      decide
    have hfull : f.range = ⊤ := by
      apply Subgroup.eq_of_le_of_card_ge le_top
      rw [Nat.card_congr (Subgroup.topEquiv (G := V)).toEquiv, hcard,
        Nat.card_eq_fintype_card]
      decide +kernel
    exact MonoidHom.range_eq_top.mp hfull
  have hsaving (b : N) (hfrattini : b.val ∈ frattini H) : ∃ a : N, a ^ 2 = b := by
    by_contra hnoPower
    have hsave := pGeneratorRank_normal_square_saving Nat.prime_two hpH N hNcommutative
      b hfrattini hnoPower
    rw [hquotient, hrank] at hsave
    omega
  have hsquares (x : H) : ∃ b : B, b.val ^ 2 = x.val ^ 2 := by
    have hmem : x ^ 2 ∈ N := by
      change q (x ^ 2) = 1
      rw [map_pow]
      exact hRexponent (q x)
    obtain ⟨a, ha⟩ := hsaving ⟨x ^ 2, hmem⟩ (pGroup_pow_mem_frattini Nat.prime_two hpH x)
    exact ⟨e a, congrArg (fun b : N => b.val.val) ha⟩
  have hdelta : ∃ b : B, b.val ^ 2 = cyclicTwoDelta n := by
    obtain ⟨g, hg⟩ := hsurjective (Multiplicative.ofAdd (1, 0))
    obtain ⟨h, hh⟩ := hsurjective (Multiplicative.ofAdd (0, 1))
    have hcommutator := cyclicTwo_shear_lift_commutator n g.val h.val hg hh
    have hmem : ⁅g, h⁆ ∈ N := by
      change q ⁅g, h⁆ = 1
      rw [map_commutatorElement]
      exact (Commute.all _ _).commutator_eq
    obtain ⟨a, ha⟩ := hsaving ⟨⁅g, h⁆, hmem⟩
      (pGroup_commutator_mem_frattini Nat.prime_two hpH g h)
    exact ⟨e a, (congrArg (fun b : N => b.val.val) ha).trans hcommutator⟩
  exact ⟨hNequiv ▸ hNrankEq, hsurjective, hsquares, hdelta⟩

theorem cyclicTwo_scalar_square_root_mem (n : ℕ) (B : Subgroup (CyclicTwoAut n))
    (hle : B ≤ (cyclicTwoScalar n).range) (hrank : 2 ≤ pGeneratorRank 2 B)
    (u : (ZMod (2 ^ (n + 2) * 2))ˣ) (b : B)
    (hsquare : b.val ^ 2 = (cyclicTwoScalar n u) ^ 2) : cyclicTwoScalar n u ∈ B := by
  obtain ⟨v, hv⟩ := hle b.property
  have hunitSquare : v ^ 2 = u ^ 2 := by
    apply cyclicTwoScalar_injective n
    rw [map_pow, map_pow, hv]
    exact hsquare
  have hratio : (u * v⁻¹) ^ 2 = 1 := by
    rw [mul_pow, inv_pow, ← hunitSquare, mul_inv_cancel]
  have hmem := cyclicTwo_scalar_involutions_mem n B hle hrank (u * v⁻¹) hratio
  have hproduct := B.mul_mem hmem b.property
  rw [map_mul, map_inv, hv, mul_assoc, inv_mul_cancel, mul_one] at hproduct
  exact hproduct

theorem cyclicTwo_rank_four_pure_shears (n : ℕ) (H : Subgroup (CyclicTwoAut n))
    (hrank : pGeneratorRank 2 H = 4) : cyclicTwoTau n ∈ H ∧ cyclicTwoRho n ∈ H := by
  obtain ⟨hBrank, hsurjective, hsquares, _⟩ := cyclicTwo_rank_four_scalar_squares n H hrank
  let B := H ⊓ (cyclicTwoScalar n).range
  have hpure (a : CyclicTwoAut n) (ha : a ^ 2 = 1)
      (v w : ZMod 2) (hnormal : cyclicTwoTau n ^ v.val * cyclicTwoRho n ^ w.val = a) : a ∈ H := by
    obtain ⟨g, hg⟩ := hsurjective (Multiplicative.ofAdd (v, w))
    obtain ⟨u, hu⟩ := cyclicTwo_shear_lift_normal_form n g.val v w hg
    rw [hnormal] at hu
    obtain ⟨b, hb⟩ := hsquares g
    have hsquare : b.val ^ 2 = (cyclicTwoScalar n u) ^ 2 := by
      rw [hb, hu, ((cyclicTwoScalar_central n u a).symm).mul_pow, ha, one_mul]
    have hscalar := cyclicTwo_scalar_square_root_mem n B inf_le_right hBrank.ge u b hsquare
    have hHscalar := hscalar.1
    have hmem := H.mul_mem g.property (H.inv_mem hHscalar)
    rw [hu, mul_inv_cancel_right] at hmem
    exact hmem
  constructor
  · exact hpure (cyclicTwoTau n) (cyclicTwoTau_square n) 1 0 (by
      simp only [ZMod.val_one, ZMod.val_zero, pow_one, pow_zero, mul_one])
  · exact hpure (cyclicTwoRho n) (cyclicTwoRho_square n) 0 1 (by
      simp only [ZMod.val_one, ZMod.val_zero, pow_one, pow_zero, one_mul])

instance cyclicTwoZ_zpowers_normal (n : ℕ) : (Subgroup.zpowers (cyclicTwoZ n)).Normal := by
  apply subgroup_normal_of_central
  rw [← cyclicTwoAut_scalar_center]
  exact Subgroup.zpowers_le.mpr ⟨-1, rfl⟩

theorem cyclicTwo_rank_four_subgroup_classification (n : ℕ) (H : Subgroup (CyclicTwoAut n))
    (hrank : pGeneratorRank 2 H = 4) :
    1 ≤ n ∧ ∃ k : ℕ, k ≤ n - 1 ∧
      H = Subgroup.closure ({cyclicTwoTau n, cyclicTwoRho n, cyclicTwoZ n,
        cyclicTwoC n ^ (2 ^ k)} : Set (CyclicTwoAut n)) := by
  let B := H ⊓ (cyclicTwoScalar n).range
  obtain ⟨hBrank, _, _, b, hb⟩ := cyclicTwo_rank_four_scalar_squares n H hrank
  obtain ⟨k, hk, hB⟩ := cyclicTwo_scalar_rank_two_subgroup n B inf_le_right hBrank.ge
  have hklower : k < n := by
    by_contra hbad
    have hnk : n ≤ k := by omega
    let s := cyclicTwoC n ^ (2 ^ k)
    have hsquare : s ^ 2 = 1 := by
      change (cyclicTwoC n ^ (2 ^ k)) ^ 2 = 1
      rw [← pow_mul, ← pow_succ 2 k]
      apply orderOf_dvd_iff_pow_eq_one.mp
      rw [cyclicTwoC_order]
      exact Nat.pow_dvd_pow 2 (by omega : n + 1 ≤ k + 1)
    have hmem : b.val ∈ Subgroup.zpowers s ⊔ Subgroup.zpowers (cyclicTwoZ n) := hB ▸ b.property
    obtain ⟨p, hp, z, hz, hproduct⟩ := Subgroup.mem_sup_of_normal_right.mp hmem
    have hpSquare : p ^ 2 = 1 := by
      rcases zpowers_involution_cases s hsquare hp with h | h <;> simp only [h, one_pow, hsquare]
    have hzSquare : z ^ 2 = 1 := by
      rcases zpowers_involution_cases (cyclicTwoZ n) (cyclicTwoZ_square n) hz with h | h
      · rw [h, one_pow]
      · rw [h, cyclicTwoZ_square]
    have hscalar : p ∈ (cyclicTwoScalar n).range := by
      apply (Subgroup.zpowers_le.mpr ?_) hp
      exact ⟨cyclicTwoFive n ^ (2 ^ k), by rw [map_pow]; rfl⟩
    obtain ⟨u, hu⟩ := hscalar
    have hbSquare : b.val ^ 2 = 1 := by
      rw [← hproduct]
      have hcommute : Commute p z := hu ▸ cyclicTwoScalar_central n u z
      rw [hcommute.mul_pow, hpSquare, hzSquare, mul_one]
    exact cyclicTwoDelta_ne_one n (hb.symm.trans hbSquare)
  have hn : 1 ≤ n := by omega
  refine ⟨hn, k, by omega, ?_⟩
  obtain ⟨hτ, hρ⟩ := cyclicTwo_rank_four_pure_shears n H hrank
  let Generated := Subgroup.closure ({cyclicTwoTau n, cyclicTwoRho n, cyclicTwoZ n,
    cyclicTwoC n ^ (2 ^ k)} : Set (CyclicTwoAut n))
  have hBGenerated : B ≤ Generated := by
    rw [hB]
    apply sup_le
    · exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
    · exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
  have hz : cyclicTwoZ n ∈ H := by
    have hzB : cyclicTwoZ n ∈ B := hB ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    exact hzB.1
  have hc : cyclicTwoC n ^ (2 ^ k) ∈ H := by
    have hcB : cyclicTwoC n ^ (2 ^ k) ∈ B := hB ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
    exact hcB.1
  apply le_antisymm
  · intro g hg
    obtain ⟨v, w, u, hu⟩ := cyclicTwoAut_normal_form n g
    have hliftH : cyclicTwoTau n ^ v.val * cyclicTwoRho n ^ w.val ∈ H :=
      H.mul_mem (H.pow_mem hτ _) (H.pow_mem hρ _)
    have hscalarH : cyclicTwoScalar n u ∈ H := by
      have hmem := H.mul_mem (H.inv_mem hliftH) hg
      rw [hu, inv_mul_cancel_left] at hmem
      exact hmem
    have hscalar : cyclicTwoScalar n u ∈ B := ⟨hscalarH, u, rfl⟩
    rw [hu]
    exact Generated.mul_mem
      (Generated.mul_mem
        (Generated.pow_mem (Subgroup.subset_closure (by simp)) _)
        (Generated.pow_mem (Subgroup.subset_closure (by simp)) _)) (hBGenerated hscalar)
  · apply (Subgroup.closure_le _).mpr
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> assumption

theorem rank_two_cyclic_times_two_automorphism_generator_strata (n : ℕ)
    (H : Subgroup (CyclicTwoAut n)) :
    Group.rank H ≤ 4 ∧ (3 ≤ Group.rank H → cyclicTwoDelta n ∈ H) ∧
      (Group.rank H = 4 → 1 ≤ n ∧ ∃ k : ℕ, k ≤ n - 1 ∧
        H = Subgroup.closure ({cyclicTwoTau n, cyclicTwoRho n, cyclicTwoZ n,
          cyclicTwoC n ^ (2 ^ k)} : Set (CyclicTwoAut n))) := by
  rw [← pGeneratorRank_eq_group_rank Nat.prime_two ((cyclicTwoAut_isPGroup n).to_subgroup H)]
  exact ⟨cyclicTwo_subgroup_generator_bound n H, cyclicTwo_three_generators_contains_delta n H,
    cyclicTwo_rank_four_subgroup_classification n H⟩

end CFSG.LargeEvenClassification.Helpers
