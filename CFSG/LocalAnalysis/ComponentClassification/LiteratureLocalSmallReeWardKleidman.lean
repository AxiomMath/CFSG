module

public import CFSG.LocalAnalysis.ComponentClassification.LiteratureLocalSmallReeMaximal
public import CFSG.LocalAnalysis.ComponentClassification.LiteratureLocalSmallReeOuter
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import Certificates.Data.ExceptionalSL3

public noncomputable section

namespace CFSG.ComponentClassification.LiteratureLocal

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.Walter.Ree.Model SmallRee
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open scoped MatrixGroups

section Transport

variable {G H : Type*} [Group G] [Group H]

theorem map_centralizer_singleton_mulEquiv (φ : G ≃* H) (x : G) :
    (Subgroup.centralizer ({x} : Set G)).map φ.toMonoidHom =
      Subgroup.centralizer ({φ x} : Set H) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hz' : z * x = x * z := Subgroup.mem_centralizer_singleton_iff.1 hz
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    change φ z * φ x = φ x * φ z
    rw [← map_mul, hz', map_mul]
  · intro hy
    have hy' : y * φ x = φ x * y := Subgroup.mem_centralizer_singleton_iff.1 hy
    refine ⟨φ.symm y, Subgroup.mem_centralizer_singleton_iff.2 ?_, φ.apply_symm_apply y⟩
    apply φ.injective
    rw [map_mul, map_mul, φ.apply_symm_apply, hy']

theorem isCoatom_map_mulEquiv (φ : G ≃* H) (A : Subgroup G) :
    IsCoatom (A.map φ.toMonoidHom) ↔ IsCoatom A :=
  OrderIso.isCoatom_iff φ.mapSubgroup A

theorem isConj_map_mulEquiv (φ : G ≃* H) {x y : G} (h : IsConj x y) : IsConj (φ x) (φ y) := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  exact isConj_iff.2 ⟨φ c, by rw [← map_inv, ← map_mul, ← map_mul, hc]⟩

theorem zpowers_inf_eq_bot_of_not_mem {x : G} (hx : orderOf x = 2) {L : Subgroup G}
    (hxL : x ∉ L) : Subgroup.zpowers x ⊓ L = ⊥ := by
  rw [eq_bot_iff]
  rintro z ⟨hz, hzL⟩
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
  rw [Subgroup.mem_bot]
  have hx2 : x ^ (2 : ℤ) = 1 := by
    have h := pow_orderOf_eq_one x
    rw [hx] at h
    exact_mod_cast h
  rcases Int.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · rw [← two_mul, zpow_mul, hx2, one_zpow]
  · exfalso
    rw [zpow_add, zpow_mul, hx2, one_zpow, one_mul, zpow_one] at hzL
    exact hxL hzL

theorem center_centralizer_eq_zpowers {x : G} {L : Subgroup G}
    (hLC : L ≤ Subgroup.centralizer ({x} : Set G))
    (hsup : Subgroup.zpowers x ⊔ L = Subgroup.centralizer ({x} : Set G))
    (hZL : Subgroup.center L = ⊥) :
    (Subgroup.center (Subgroup.centralizer ({x} : Set G))).map
      (Subgroup.centralizer ({x} : Set G)).subtype = Subgroup.zpowers x := by
  have hxC : x ∈ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 rfl
  apply le_antisymm
  · rintro _ ⟨z, hz, rfl⟩
    show (z : G) ∈ Subgroup.zpowers x
    have hzC : (z : G) ∈ Subgroup.zpowers x ⊔ L := by
      rw [hsup]
      exact z.2
    have hnorm : Subgroup.zpowers x ≤ Subgroup.normalizer (L : Set G) := by
      rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
      intro l
      constructor
      · intro hl
        have h1 := Subgroup.mem_centralizer_singleton_iff.1 (hLC hl)
        rw [← h1, mul_inv_cancel_right]
        exact hl
      · intro hl
        have h1 := Subgroup.mem_centralizer_singleton_iff.1 (hLC hl)
        have h2 : l = x * l * x⁻¹ := by
          have h3 : x * l = x * (x * l * x⁻¹) := by
            rw [← h1]
            group
          exact mul_left_cancel h3
        rw [h2]
        exact hl
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnorm,
      Set.mem_mul] at hzC
    obtain ⟨y, hy, l, hl, hyl⟩ := hzC
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    have hlZ : (⟨l, hl⟩ : L) ∈ Subgroup.center L := by
      rw [Subgroup.mem_center_iff]
      intro m
      apply Subtype.ext
      have hmC : (m : G) ∈ Subgroup.centralizer ({x} : Set G) := hLC m.2
      have hzm : Commute (m : G) z :=
        congrArg Subtype.val ((Subgroup.mem_center_iff.1 hz) ⟨m, hmC⟩)
      have hmx : Commute (m : G) x := Subgroup.mem_centralizer_singleton_iff.1 hmC
      have hxm : Commute (m : G) (x ^ n) := hmx.zpow_right n
      have e : l = (x ^ n)⁻¹ * z := by
        rw [← hyl]
        group
      change (m : G) * l = l * m
      rw [e]
      exact (hxm.inv_right.mul_right hzm).eq
    rw [hZL, Subgroup.mem_bot] at hlZ
    have hl1 : l = 1 := congrArg Subtype.val hlZ
    rw [← hyl, hl1, mul_one]
    exact Subgroup.zpow_mem_zpowers x n
  · rw [Subgroup.zpowers_le]
    refine ⟨⟨x, hxC⟩, Subgroup.mem_center_iff.2 fun g => ?_, rfl⟩
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 g.2)

end Transport


theorem ward_kleidman_small_Ree_involution_centralizer_maximal (a : ℕ) (ha : 1 ≤ a) (G : Type)
    [Group G] (h : ReeTitsModel G .twistedG2 3 (2 * a + 1)) :
    Finite G ∧
    ((∃ x : G, orderOf x = 2) ∧ ∀ x y : G, orderOf x = 2 → orderOf y = 2 → IsConj x y) ∧
    (∀ x : G, orderOf x = 2 → ∃ L : Subgroup G, L ≤ Subgroup.centralizer ({x} : Set G) ∧
      Subgroup.zpowers x ⊓ L = ⊥ ∧ Subgroup.zpowers x ⊔ L = Subgroup.centralizer ({x} : Set G) ∧
      Nonempty (L ≃* PSL(2, GaloisField 3 (2 * a + 1))) ∧
      (Subgroup.center (Subgroup.centralizer ({x} : Set G))).map
        (Subgroup.centralizer ({x} : Set G)).subtype = Subgroup.zpowers x) ∧
    (∀ x : G, orderOf x = 2 → IsCoatom (Subgroup.centralizer ({x} : Set G))) ∧
    (IsCyclic (Outer G) ∧ Nat.card (Outer G) = 2 * a + 1 ∧ Odd (Nat.card (Outer G))) := by
  obtain ⟨hfin, -, -, -, hiso⟩ := small_Ree_model_Schreier G 3 (2 * a + 1) h
  obtain ⟨-, a', ha', K, _, _, hK, hmod⟩ := h
  have haa : a' = a := by omega
  rw [haa] at hmod
  have := Fintype.ofFinite K
  have : CharP K ReeTag.G2.prime := charP_of_card_eq_prime_pow (f := 2 * a + 1) (by
    rw [← Nat.card_eq_fintype_card, hK]
    rfl)
  obtain ⟨e⟩ := hiso a K rfl hK hmod
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element ReeTag.G2.tag
  set J := smallReeJTHyp ha hK
  have ht : (J.t : ModGL ReeTag.G2.tag K) = smallReeH a K (-1) := rfl
  have hfus : ∀ y : ReeTag.G2.reeGamma K a, orderOf y = 2 →
      ∃ c : ReeTag.G2.reeGamma K a, c * J.t * c⁻¹ = y := by
    intro y hy
    obtain ⟨-, -, -, -, -, hf⟩ := small_Ree_prime_field_involution_fusion a K hK w₀ hw₀
    have hy' : orderOf (y : ModGL ReeTag.G2.tag K) = 2 := by rw [Subgroup.orderOf_coe, hy]
    obtain ⟨g, hgΓ, hg⟩ := hf _ y.2 hy'
    have h1 : (⟨g, hgΓ⟩ : ReeTag.G2.reeGamma K a) * y *
        (⟨g, hgΓ⟩ : ReeTag.G2.reeGamma K a)⁻¹ = J.t :=
      Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ht]; exact hg)
    refine ⟨(⟨g, hgΓ⟩ : ReeTag.G2.reeGamma K a)⁻¹, ?_⟩
    rw [← h1]
    group
  have hstruct : ∀ x : G, orderOf x = 2 → ∃ ψ : ReeTag.G2.reeGamma K a ≃* G, ψ J.t = x := by
    intro x hx
    have hx' : orderOf (e x) = 2 := by rw [MulEquiv.orderOf_eq, hx]
    obtain ⟨c, hc⟩ := hfus _ hx'
    refine ⟨(MulAut.conj c).trans e.symm, ?_⟩
    rw [MulEquiv.trans_apply, MulAut.conj_apply, hc, MulEquiv.symm_apply_apply]
  have hJinf : Subgroup.zpowers J.t ⊓ J.F = ⊥ :=
    zpowers_inf_eq_bot_of_not_mem J.orderOf_t J.t_not_mem
  have hZF : Subgroup.center J.F = ⊥ := by
    have h1 := CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv J.iso
    rw [CFSG.GorensteinWalter.psl2_center_eq_bot] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ (f := J.iso.toMonoidHom) J.iso.injective).1 h1
  have hmax := centralizer_torusInv_isCoatom ha hK
  obtain ⟨hcyc, hcard⟩ := outer_reeGamma_cyclic ha hK
  refine ⟨hfin, ⟨⟨e.symm J.t, by rw [MulEquiv.orderOf_eq]; exact J.orderOf_t⟩, ?_⟩, ?_, ?_, ?_⟩
  ·
    intro x y hx hy
    have hx' : orderOf (e x) = 2 := by rw [MulEquiv.orderOf_eq, hx]
    have hy' : orderOf (e y) = 2 := by rw [MulEquiv.orderOf_eq, hy]
    obtain ⟨c, hc⟩ := hfus _ hx'
    obtain ⟨d, hd⟩ := hfus _ hy'
    have h1 : IsConj (e x) (e y) := by
      rw [← hc, ← hd]
      exact (isConj_iff.2 ⟨c, rfl⟩).symm.trans (isConj_iff.2 ⟨d, rfl⟩)
    have h2 := isConj_map_mulEquiv e.symm h1
    rwa [MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply] at h2
  ·
    intro x hx
    obtain ⟨ψ, hψ⟩ := hstruct x hx
    have hC := map_centralizer_singleton_mulEquiv ψ J.t
    rw [hψ] at hC
    have hzx : Subgroup.zpowers x = (Subgroup.zpowers J.t).map ψ.toMonoidHom := by
      rw [MonoidHom.map_zpowers]
      exact congrArg Subgroup.zpowers hψ.symm
    have hLC : J.F.map ψ.toMonoidHom ≤ Subgroup.centralizer ({x} : Set G) := by
      rw [← hC]
      exact Subgroup.map_mono J.le_centralizer
    have hsup : Subgroup.zpowers x ⊔ J.F.map ψ.toMonoidHom =
        Subgroup.centralizer ({x} : Set G) := by
      rw [hzx, ← Subgroup.map_sup, ← J.centralizer_eq, hC]
    have hZL : Subgroup.center (J.F.map ψ.toMonoidHom) = ⊥ := by
      have h1 := CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv
        (J.F.equivMapOfInjective ψ.toMonoidHom ψ.injective)
      rw [hZF, Subgroup.map_bot] at h1
      exact h1.symm
    refine ⟨J.F.map ψ.toMonoidHom, hLC, ?_, hsup,
      ⟨(J.F.equivMapOfInjective ψ.toMonoidHom ψ.injective).symm.trans J.iso⟩,
      center_centralizer_eq_zpowers hLC hsup hZL⟩
    rw [hzx, ← Subgroup.map_inf_eq _ _ ψ.toMonoidHom ψ.injective, hJinf, Subgroup.map_bot]
  ·
    intro x hx
    obtain ⟨ψ, hψ⟩ := hstruct x hx
    have hC := map_centralizer_singleton_mulEquiv ψ J.t
    rw [hψ] at hC
    rw [← hC, isCoatom_map_mulEquiv]
    exact hmax
  ·
    have eOut := CFSG.ComponentClassification.OuterAutomorphisms.equivalence e
    have hcardG : Nat.card (Outer G) = 2 * a + 1 := by
      rw [Nat.card_congr eOut.toEquiv, hcard]
    refine ⟨(MulEquiv.isCyclic eOut).2 hcyc, hcardG, ?_⟩
    rw [hcardG]
    exact odd_two_mul_add_one a

end CFSG.ComponentClassification.LiteratureLocal
