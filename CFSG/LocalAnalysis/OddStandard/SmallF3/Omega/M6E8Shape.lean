module

public import CFSG.GF2Type.Aschbacher1976Common.DihedralEvenRank
import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitTwoGroupShapes
import CFSG.CharacterTheory.Semidihedral.ElementOrders

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

private lemma m6e8_dihedral_orderOf {m : ℕ} [NeZero m] (g : DihedralGroup m)
    (hg : g ∉ Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup m)) :
    orderOf g = 2 := by
  cases g with
  | r i =>
    exfalso
    apply hg
    have hr : DihedralGroup.r i = (DihedralGroup.r 1 : DihedralGroup m) ^ i.val := by
      rw [DihedralGroup.r_one_pow, ZMod.natCast_zmod_val]
    rw [hr]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
  | sr i => exact DihedralGroup.orderOf_sr i

private lemma m6e8_semidihedral_orderOf {n : ℕ} (hn : 3 ≤ n)
    (g : CFSG.Open.SemidihedralGroup n)
    (hg : g ∉ CFSG.Semidihedral.rotationSubgroup n) : orderOf g ≤ 4 := by
  set c := CFSG.Semidihedral.coordinateEquiv n hn g with hc
  have hcoord : CFSG.Semidihedral.element n hn c.1 c.2 = g := by
    rw [hc]
    exact CFSG.Semidihedral.element_coordinates n hn g
  have hε : c.2 ≠ 0 := by
    intro h0
    apply hg
    rw [← hcoord]
    exact (CFSG.Semidihedral.element_mem_rotationSubgroup_iff n hn c.1 c.2).mpr h0
  have hεval : c.2.val = 1 := by
    have hlt : c.2.val < 2 := ZMod.val_lt c.2
    have hne : c.2.val ≠ 0 := fun h => hε ((ZMod.val_eq_zero c.2).mp h)
    omega
  have hrepr : g = CFSG.Semidihedral.r n ^ c.1.val * CFSG.Semidihedral.s n := by
    rw [← hcoord, CFSG.Semidihedral.element_eq, hεval, pow_one]
  rw [hrepr]
  have hz : (CFSG.Semidihedral.z n ^ c.1.val) ^ 2 = 1 := by
    rw [show (CFSG.Semidihedral.z n ^ c.1.val) ^ 2 =
        (CFSG.Semidihedral.z n ^ 2) ^ c.1.val by rw [← pow_mul, ← pow_mul, mul_comm],
      CFSG.Semidihedral.z_sq n hn, one_pow]
  have h4pow : (CFSG.Semidihedral.r n ^ c.1.val * CFSG.Semidihedral.s n) ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul,
      CFSG.Semidihedral.reflection_square_nat n hn c.1.val, hz]
  exact Nat.le_of_dvd (by decide : 0 < 4) (orderOf_dvd_iff_pow_eq_one.mpr h4pow)

private lemma m6e8_dihedral_shape {K : Type} [Group K] [Finite K] {m : ℕ} [NeZero m]
    (e : K ≃* DihedralGroup m) (h4dvd : 4 ∣ m) :
    ∃ A : Subgroup K, IsCyclic A ∧ A.index = 2 ∧ 4 ∣ Nat.card A ∧
      (∀ k : K, k ∉ A → orderOf k < Nat.card A) ∧
      CFSG.GF2Type.Aschbacher1976Common.TwoGenSubgroups K := by
  let A : Subgroup K := Subgroup.zpowers (e.symm (DihedralGroup.r 1))
  have hA : A = Subgroup.zpowers (e.symm (DihedralGroup.r 1)) := rfl
  have hAcyc : IsCyclic A := by rw [hA]; exact Subgroup.isCyclic_zpowers _
  have hcardA : Nat.card A = m := by
    rw [hA, Nat.card_zpowers, MulEquiv.orderOf_eq, DihedralGroup.orderOf_r_one]
  have hidx : A.index = 2 := by
    rw [hA]
    have h := (Subgroup.zpowers (e.symm (DihedralGroup.r 1))).card_mul_index
    rw [Nat.card_zpowers, MulEquiv.orderOf_eq, DihedralGroup.orderOf_r_one,
      Nat.card_congr e.toEquiv, DihedralGroup.nat_card] at h
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (NeZero.ne m))
      (by rw [h, mul_comm])
  have h4 : 4 ∣ Nat.card A := by rw [hcardA]; exact h4dvd
  have hm4 : 4 ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne m)) h4dvd
  have hAord : ∀ k : K, k ∉ A → orderOf k < Nat.card A := by
    intro k hk
    have hkrot : e k ∉ Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup m) := by
      intro hmem
      apply hk
      rw [hA]
      have h2 := Subgroup.mem_map_of_mem e.symm.toMonoidHom hmem
      rw [MonoidHom.map_zpowers] at h2
      simpa using h2
    rw [hcardA, show orderOf k = orderOf (e k) from (MulEquiv.orderOf_eq e k).symm,
      m6e8_dihedral_orderOf (e k) hkrot]
    omega
  refine ⟨A, hAcyc, hidx, h4, hAord, ?_⟩
  exact CFSG.GF2Type.Aschbacher1976Common.twoGen_of_mulEquiv e
    (CFSG.GF2Type.Aschbacher1976Common.twoGen_dihedral m)

private lemma m6e8_semidihedral_shape {K : Type} [Group K] [Finite K] {n : ℕ} (hn : 4 ≤ n)
    (e : K ≃* CFSG.Open.SemidihedralGroup n) :
    ∃ A : Subgroup K, IsCyclic A ∧ A.index = 2 ∧ 4 ∣ Nat.card A ∧
      (∀ k : K, k ∉ A → orderOf k < Nat.card A) ∧
      CFSG.GF2Type.Aschbacher1976Common.TwoGenSubgroups K := by
  have hn3 : 3 ≤ n := by omega
  let A : Subgroup K := Subgroup.zpowers (e.symm (CFSG.Semidihedral.r n))
  have hA : A = Subgroup.zpowers (e.symm (CFSG.Semidihedral.r n)) := rfl
  have hAeq : A = (CFSG.Semidihedral.rotationSubgroup n).map e.symm.toMonoidHom := by
    rw [hA, CFSG.Semidihedral.rotationSubgroup, MonoidHom.map_zpowers]
    rfl
  have hAcyc : IsCyclic A := by rw [hA]; exact Subgroup.isCyclic_zpowers _
  have hidx : A.index = 2 := by
    rw [hAeq, Subgroup.index_map_of_bijective e.symm.bijective,
      CFSG.Semidihedral.rotationSubgroup_index n hn3]
  have hcardA : Nat.card A = CFSG.Semidihedral.modulus n := by
    rw [hA, Nat.card_zpowers, MulEquiv.orderOf_eq, CFSG.Semidihedral.orderOf_r n hn3]
  have h4 : 4 ∣ Nat.card A := by
    rw [hcardA, CFSG.Semidihedral.modulus]
    simpa using pow_dvd_pow (2 : ℕ) (show 2 ≤ n - 1 by omega)
  have hmod : 4 < CFSG.Semidihedral.modulus n := by
    rw [CFSG.Semidihedral.modulus]
    have h8 : 2 ^ 3 ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    norm_num at h8
    omega
  have hAord : ∀ k : K, k ∉ A → orderOf k < Nat.card A := by
    intro k hk
    have hkrot : e k ∉ CFSG.Semidihedral.rotationSubgroup n := by
      intro hmem
      apply hk
      rw [hAeq]
      simpa using Subgroup.mem_map_of_mem e.symm.toMonoidHom hmem
    have hle : orderOf (e k) ≤ 4 := m6e8_semidihedral_orderOf hn3 (e k) hkrot
    rw [hcardA]
    exact lt_of_le_of_lt ((MulEquiv.orderOf_eq e k).symm ▸ hle) hmod
  refine ⟨A, hAcyc, hidx, h4, hAord, ?_⟩
  exact CFSG.GF2Type.Aschbacher1976Common.twoGen_of_mulEquiv e
    (CFSG.GF2Type.Aschbacher1976Common.twoGen_semidihedral n hn)

theorem m6e8_shape_of_suzuki {K : Type} [Group K] [Finite K] (hK : IsPGroup 2 K) {t : K}
    (hcard : Nat.card (centralizer ({t} : Set K)) = 4)
    (hexp : ∀ x ∈ centralizer ({t} : Set K), x ^ 2 = 1) (h8 : 8 ≤ Nat.card K) :
    ∃ A : Subgroup K, IsCyclic A ∧ A.index = 2 ∧ 4 ∣ Nat.card A ∧
      (∀ k : K, k ∉ A → orderOf k < Nat.card A) ∧
      CFSG.GF2Type.Aschbacher1976Common.TwoGenSubgroups K := by
  rcases CFSG.ComponentClassification.AschbacherToolkit.suzuki_two_group hK hcard hexp with
    ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
  · haveI : NeZero (2 ^ (n - 1)) := ⟨pow_ne_zero _ (by norm_num)⟩
    have hcardK : Nat.card K = 2 * 2 ^ (n - 1) := by
      rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    have hm4 : 4 ≤ 2 ^ (n - 1) := by omega
    have hn3 : 3 ≤ n := by
      by_contra h
      push Not at h
      have hle : 2 ^ (n - 1) ≤ 2 ^ 1 :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      norm_num at hle
      omega
    exact m6e8_dihedral_shape e
      (by simpa using pow_dvd_pow (2 : ℕ) (show 2 ≤ n - 1 by omega))
  · exact m6e8_semidihedral_shape hn e

theorem m6e8_shape_subgroup {G : Type} [Group G] [Finite G] {K : Subgroup G} {y : G}
    (hK : IsPGroup 2 K) (hyK : y ∈ K) (hcard : Nat.card ↥(K ⊓ centralizer ({y} : Set G)) = 4)
    (hexp : ∀ x ∈ K ⊓ centralizer ({y} : Set G), x ^ 2 = 1) (h8 : 8 ≤ Nat.card K) :
    ∃ A : Subgroup G, A ≤ K ∧ IsCyclic A ∧ A.relIndex K = 2 ∧ 4 ∣ Nat.card A ∧
      (∀ k ∈ K, k ∉ A → orderOf k < Nat.card A) ∧
      CFSG.GF2Type.Aschbacher1976Common.TwoGenSubgroups K := by
  have hcent_eq : Subgroup.centralizer ({⟨y, hyK⟩} : Set ↥K) =
      (K ⊓ Subgroup.centralizer ({y} : Set G)).subgroupOf K := by
    ext x
    simp only [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf,
      Subgroup.mem_inf]
    constructor
    · intro h
      exact ⟨x.2, congrArg Subtype.val h⟩
    · rintro ⟨-, h⟩
      exact Subtype.ext h
  have hcard' : Nat.card (Subgroup.centralizer ({⟨y, hyK⟩} : Set ↥K)) = 4 := by
    rw [hcent_eq]
    have hmap : ((K ⊓ Subgroup.centralizer ({y} : Set G)).subgroupOf K).map K.subtype =
        K ⊓ Subgroup.centralizer ({y} : Set G) := by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr inf_le_left]
    rw [← Subgroup.card_map_of_injective K.subtype_injective, hmap, hcard]
  have hexp' : ∀ x ∈ Subgroup.centralizer ({⟨y, hyK⟩} : Set ↥K), x ^ 2 = 1 := by
    intro x hx
    have hx' : (x : G) ∈ K ⊓ Subgroup.centralizer ({y} : Set G) := by
      rw [hcent_eq] at hx
      exact hx
    apply Subtype.ext
    simpa using hexp (x : G) hx'
  obtain ⟨A', hA'cyc, hA'idx, hA'4, hA'ord, hA'2gen⟩ :=
    m6e8_shape_of_suzuki (K := ↥K) hK hcard' hexp' h8
  have hcardmap : Nat.card (A'.map K.subtype) = Nat.card A' :=
    Subgroup.card_map_of_injective K.subtype_injective
  refine ⟨A'.map K.subtype, Subgroup.map_subtype_le A', ?_, ?_, ?_, ?_, hA'2gen⟩
  · exact (Subgroup.equivMapOfInjective A' K.subtype K.subtype_injective).isCyclic.mp hA'cyc
  · change ((A'.map K.subtype).subgroupOf K).index = 2
    rw [← Subgroup.comap_subtype,
      Subgroup.comap_map_eq_self_of_injective K.subtype_injective A', hA'idx]
  · rw [hcardmap]; exact hA'4
  · intro k hkK hkA
    have hk' : (⟨k, hkK⟩ : ↥K) ∉ A' := by
      intro hmem
      exact hkA (by simpa using Subgroup.mem_map_of_mem K.subtype hmem)
    have h1 := hA'ord ⟨k, hkK⟩ hk'
    rw [Subgroup.orderOf_mk] at h1
    rw [← hcardmap] at h1
    exact h1

end CFSG.OddStandard.SmallF3.Omega
