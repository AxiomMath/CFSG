module

public import CFSG.GH74.GLS.Stage1.Thm4.L97b
public import CFSG.GH74.GLS.Bg.Iii2.Basic
public import CFSG.GH74.GLS.C3.Layer1.St1RigOrd

public section

namespace CFSG.GH74.GLS.Stage1.Thm4.P92

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage1.Thm2.Recip CFSG.GH74.GLS.Stage1.Thm3.Sec5
  CFSG.GH74.GLS.C3.Layer1.PumpRigid CFSG.ABGLocalTools
open scoped commutatorElement

section Elementary

variable {G : Type} [Group G]

theorem comm_of_sq {E : Subgroup G} (h : ∀ x ∈ E, x * x = 1) :
    ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
  intro a ha b hb
  have hab := h (a * b) (E.mul_mem ha hb)
  have ha' := inv_eq_of_mul_eq_one_right (h a ha)
  have hb' := inv_eq_of_mul_eq_one_right (h b hb)
  have h1 : a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right hab).symm
  rw [mul_inv_rev, ha', hb'] at h1
  exact h1

theorem isPGroup_two_of_sq {E : Subgroup G} (h : ∀ a ∈ E, a * a = 1) : IsPGroup 2 ↥E := by
  rw [IsPGroup.iff_orderOf]
  intro g
  have hg : (g : G) * g = 1 := h g g.2
  have hg2 : g ^ 2 = 1 := Subtype.ext (by rw [sq]; exact hg)
  rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hg2) with h | h
  · exact ⟨0, by simpa using h⟩
  · exact ⟨1, by simpa using h⟩

theorem mem_zpowers_involution {y x : G} (hy : y * y = 1) (hx : x ∈ zpowers y) : x = 1 ∨ x = y := by
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hx
  have h2 : y ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hy
  rcases Int.even_or_odd j with ⟨m, hm⟩ | ⟨m, hm⟩
  · left
    rw [hm, ← two_mul, zpow_mul, h2, one_zpow]
  · right
    rw [hm, zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]

end Elementary

variable {G : Type} [Group G] [Finite G] {Lh : Type} [Group Lh]

structure Env (G : Type) [Group G] [Finite G] (Lh : Type) [Group Lh] (n : ℕ) : Prop where
  std : Std0 G
  n8 : 8 ≤ n
  n11 : n ≤ 11
  hL : IsDoubleCoverOfAlt Lh n

variable {n : ℕ}

theorem Env.rank4 (E : Env G Lh n) : pRank 2 G ≤ 4 := E.std.rank.2

theorem Env.hR (E : Env G Lh n) :
    ∀ y : G, orderOf y = 2 → 3 ≤ pRank 2 ↥(centralizer ({y} : Set G)) := fun y hy =>
  TwoThin.rankThreeCentralizers G E.std.kps.1 E.std.kps.2.1 E.std.rank.1 y hy

omit [Finite G] in
theorem rig_ilo {z : G} {K : Subgroup G} (h : IsRigidOfType Lh z K) : IsILo 2 z K := h.1.1

omit [Finite G] in
theorem rig_ord {z : G} {K : Subgroup G} (h : IsRigidOfType Lh z K) : orderOf z = 2 := h.1.1.1

omit [Finite G] in
theorem rig_pcomp {z : G} {K : Subgroup G} (h : IsRigidOfType Lh z K) :
    IsPCompIn 2 (centralizer ({z} : Set G)) K := h.1.1.2.2

omit [Finite G] in
theorem rig_le_cen {z : G} {K : Subgroup G} (h : IsRigidOfType Lh z K) :
    K ≤ centralizer ({z} : Set G) := h.1.1.2.2.1

theorem Env.unique (E : Env G Lh n) {z : G} {K K' : Subgroup G} (hK : IsRigidOfType Lh z K)
    (hK' : IsRigidOfType Lh z K') : K = K' :=
  L97.rigid_unique E.rank4 E.n8 E.hL hK hK'

theorem Env.norm (E : Env G Lh n) {z : G} {K : Subgroup G} (hK : IsRigidOfType Lh z K) {c : G}
    (hc : c ∈ centralizer ({z} : Set G)) : c ∈ normalizer (K : Set G) := by
  have h1 : Thm3.Sec4.cmap c K = K := E.unique (isRigidOfType_cmap hK hc) hK
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h1

theorem Env.rigidSet_eq (E : Env G Lh n) {z : G} {K : Subgroup G} (hK : IsRigidOfType Lh z K) :
    RigidSet Lh z = {K} := by
  ext K'
  exact ⟨fun h => E.unique h hK, fun h => by rw [Set.mem_singleton_iff] at h; rw [h]; exact hK⟩

theorem Env.kz_eq (E : Env G Lh n) {z : G} {K : Subgroup G} (hK : IsRigidOfType Lh z K) :
    Kz Lh z = K := by
  unfold Kz; rw [E.rigidSet_eq hK, sSup_singleton]

theorem sylow_inf {z : G} {K T : Subgroup G} (hK : IsRigidOfType Lh z K)
    (hT : IsSylowOf 2 T (centralizer ({z} : Set G))) : IsSylowOf 2 (T ⊓ K) K := by
  have hKC := rig_pcomp hK
  obtain ⟨Kc, hKcomp, hsub, hmap, hmin⟩ := hKC.2
  have hT' : QuasithinUnique.IsSylowTwoOf T (centralizer ({z} : Set G)) :=
    Bg.Iii2.isSylowTwoOf_iff'.2 hT
  exact Bg.Iii2.isSylowTwoOf_iff'.1
    (QuasithinUnique.RankOneRecog.isSylowTwoOf_inf_of_subnormal hT' hKC.1 hsub)

omit [Finite G] in
theorem exists_sylow_mem [Finite G] {C : Subgroup G} {x : G} (hxC : x ∈ C) (hx : x * x = 1) :
    ∃ T : Subgroup G, IsSylowOf 2 T C ∧ x ∈ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hW : IsPGroup 2 ↥(zpowers (⟨x, hxC⟩ : ↥C)) := by
    refine isPGroup_two_of_sq (fun a ha => ?_)
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp ha
    have h2 : (⟨x, hxC⟩ : ↥C) ^ (2 : ℤ) = 1 := by
      rw [zpow_two]; exact Subtype.ext hx
    rw [← zpow_add, ← two_mul, zpow_mul, h2, one_zpow]
  obtain ⟨S, hS⟩ := hW.exists_le_sylow
  exact ⟨(S : Subgroup ↥C).map C.subtype, ⟨S, rfl⟩, ⟨⟨x, hxC⟩, hS (Subgroup.mem_zpowers _), rfl⟩⟩

omit [Finite G] in
theorem exists_sylow_ge [Finite G] {C S : Subgroup G} (hS : IsPGroup 2 ↥S) (hSC : S ≤ C) :
    ∃ T : Subgroup G, IsSylowOf 2 T C ∧ S ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS' : IsPGroup 2 ↥(S.subgroupOf C) := hS.of_equiv (Subgroup.subgroupOfEquivOfLe hSC).symm
  obtain ⟨Q, hQ⟩ := hS'.exists_le_sylow
  refine ⟨(Q : Subgroup ↥C).map C.subtype, ⟨Q, rfl⟩, fun x hx => ?_⟩
  exact ⟨⟨x, hSC hx⟩, hQ hx, rfl⟩

theorem exists_involution_normal_center {T N : Subgroup G} (hT : IsPGroup 2 ↥T) (hNT : N ≤ T)
    (hN : ∀ t ∈ T, ∀ n ∈ N, t * n * t⁻¹ ∈ N) (hne : N ≠ ⊥) :
    ∃ w ∈ N, orderOf w = 2 ∧ ∀ t ∈ T, t * w = w * t := by
  have hnil : Group.IsNilpotent ↥T := hT.isNilpotent
  let N₀ : Subgroup ↥T := N.subgroupOf T
  have hN₀ : N₀.Normal := ⟨fun n hn g => by
    have := hN (g : G) g.2 (n : G) (Subgroup.mem_subgroupOf.mp hn)
    exact Subgroup.mem_subgroupOf.mpr (by simpa using this)⟩
  have hN₀ne : N₀ ≠ ⊥ := by
    intro h
    apply hne
    rw [eq_bot_iff]
    intro n hn
    have hmem : (⟨n, hNT hn⟩ : ↥T) ∈ N₀ := Subgroup.mem_subgroupOf.mpr hn
    rw [h, Subgroup.mem_bot] at hmem
    have : n = 1 := congrArg Subtype.val hmem
    rw [this]; exact Subgroup.one_mem _
  have hX := Group.IsNilpotent.inf_center_ne_bot_of_normal hN₀ne
  obtain ⟨w, hw, hwo⟩ := CFSG.ABGLocalTools.exists_mem_orderOf_eq_two
    (hT.to_subgroup (N₀ ⊓ center ↥T)) hX
  refine ⟨(w : G), Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp hw).1, ?_, fun t ht => ?_⟩
  · rw [Subgroup.orderOf_coe]
    exact hwo
  · have := Subgroup.mem_center_iff.mp (Subgroup.mem_inf.mp hw).2 ⟨t, ht⟩
    exact congrArg Subtype.val this

omit [Finite G] in
theorem isRigidOfType_of_pumpUpLT {x u : G} {K J : Subgroup G} (hK : IsRigidOfType Lh x K)
    (hlt : PumpUpLT 2 x K u J) : IsRigidOfType Lh u J := by
  obtain ⟨e⟩ := hK.1.2 u J (LongPumpUp.single' hlt)
  refine ⟨⟨hlt.2.1, fun x' K' hl => ?_⟩, ?_⟩
  · obtain ⟨e'⟩ := hK.1.2 x' K' (LongPumpUp.trans' (LongPumpUp.single' hlt) hl)
    exact ⟨e'.trans e.symm⟩
  · obtain ⟨e₀⟩ := hK.2
    exact ⟨e.trans e₀⟩

end CFSG.GH74.GLS.Stage1.Thm4.P92
