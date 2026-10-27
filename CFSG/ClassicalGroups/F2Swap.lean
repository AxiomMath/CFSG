module

public import CFSG.ClassicalGroups.F2Fixed

public section

namespace CFSG.ClassicalGroups.F2Swap

open CFSG.ClassicalGroups.F2Fixed

section Invariant

variable (G : Type*) [Group G] {M : Type*} [AddCommGroup M] [DistribMulAction G M]

@[expose] def invSub (Y : AddSubgroup M) : Subgroup G where
  carrier := {h | ∀ m ∈ Y, h • m ∈ Y ∧ h⁻¹ • m ∈ Y}
  one_mem' := fun m hm => by simpa using hm
  mul_mem' := fun {a b} ha hb m hm => by
    refine ⟨?_, ?_⟩
    · rw [mul_smul]; exact (ha _ (hb m hm).1).1
    · rw [mul_inv_rev, mul_smul]; exact (hb _ (ha m hm).2).2
  inv_mem' := fun {a} ha m hm => ⟨(ha m hm).2, by rw [inv_inv]; exact (ha m hm).1⟩

variable {G}

theorem mem_invSub_of_mul_self {Y : AddSubgroup M} {a : G} (ha2 : a * a = 1)
    (h : ∀ m ∈ Y, a • m ∈ Y) : a ∈ invSub G Y := fun m hm =>
  ⟨h m hm, by rw [inv_eq_of_mul_eq_one_right ha2]; exact h m hm⟩

end Invariant

section Braid

variable {G : Type*} [Group G] {M : Type*} [AddCommGroup M] [DistribMulAction G M]

theorem comm_eq_of_braid (h2 : ∀ m : M, m + m = 0) {y z : G} (hy : y * y = 1) (hz : z * z = 1)
    (hbr : y * z * y = z * y * z) (hfix : fixedSub M {y} ⊓ fixedSub M {z} = ⊥) {x : M}
    (hx : y • x = x) : comm M z x = (y * z) • x := by
  have hzz : ∀ n : M, z • z • n = n := fun n => by rw [← mul_smul, hz, one_smul]
  have e1 : y • (y * z) • x = z • x := by rw [← mul_smul, ← mul_assoc, hy, one_mul]
  have e2 : z • (y * z) • x = (y * z) • x :=
    calc z • (y * z) • x = (z * y * z) • x := by rw [← mul_smul, mul_assoc]
      _ = (y * z * y) • x := by rw [hbr]
      _ = (y * z) • y • x := mul_smul _ _ _
      _ = (y * z) • x := by rw [hx]
  have hv : x + z • x + (y * z) • x ∈ fixedSub M {y} ⊓ fixedSub M {z} := by
    refine ⟨fun g hg => ?_, fun g hg => ?_⟩
    · rw [Set.mem_singleton_iff.mp hg, smul_add, smul_add, hx, e1, mul_smul]
      abel
    · rw [Set.mem_singleton_iff.mp hg, smul_add, smul_add, hzz, e2]
      abel
  rw [hfix, AddSubgroup.mem_bot] at hv
  have h3 : x + z • x = (y * z) • x := by
    have := eq_neg_of_add_eq_zero_left hv
    rw [this, neg_eq_of_add_eq_zero_right (h2 ((y * z) • x))]
  rw [comm_apply, sub_eq_add_of_exp2 h2, add_comm, h3]

end Braid

section Swap

variable {G : Type*} [Group G] {M : Type*} [AddCommGroup M] [DistribMulAction G M]

theorem mem_map_smul {g : G} {U : AddSubgroup M} {m : M} :
    m ∈ U.map (DistribSMul.toAddMonoidHom M g) ↔ ∃ x ∈ U, g • x = m := by
  simp only [AddSubgroup.mem_map]
  rfl

theorem mem_sup_map_smul {g : G} {U : AddSubgroup M} {m : M} :
    m ∈ U ⊔ U.map (DistribSMul.toAddMonoidHom M g) ↔ ∃ x ∈ U, ∃ x' ∈ U, m = x + g • x' := by
  rw [AddSubgroup.mem_sup]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    obtain ⟨x', hx', rfl⟩ := mem_map_smul.mp hb
    exact ⟨a, ha, x', hx', rfl⟩
  · rintro ⟨x, hx, x', hx', rfl⟩
    exact ⟨x, hx, g • x', mem_map_smul.mpr ⟨x', hx', rfl⟩, rfl⟩

theorem map_smul_map_smul_inv (g : G) (U : AddSubgroup M) :
    (U.map (DistribSMul.toAddMonoidHom M g)).map (DistribSMul.toAddMonoidHom M g⁻¹) = U := by
  ext m
  rw [AddSubgroup.mem_map]
  constructor
  · rintro ⟨_, hy, rfl⟩
    obtain ⟨x, hx, rfl⟩ := mem_map_smul.mp hy
    show g⁻¹ • g • x ∈ U
    rwa [inv_smul_smul]
  · intro hm
    exact ⟨g • m, mem_map_smul.mpr ⟨m, hm, rfl⟩, inv_smul_smul g m⟩

theorem mem_iff_of_image_conj {L L' : Subgroup G} {g : G}
    (hconj : (fun s => g * s * g⁻¹) '' (L : Set G) = (L' : Set G)) (s : G) :
    s ∈ L ↔ g * s * g⁻¹ ∈ L' := by
  constructor
  · intro hs
    rw [← SetLike.mem_coe, ← hconj]
    exact ⟨s, hs, rfl⟩
  · intro hs
    rw [← SetLike.mem_coe, ← hconj] at hs
    obtain ⟨s', hs', he⟩ := hs
    have : s' = s := mul_left_cancel (mul_right_cancel he)
    rwa [this] at hs'

theorem smul_mem_fixedSub_of_image_conj {L L' : Subgroup G} {g : G}
    (hconj : (fun s => g * s * g⁻¹) '' (L : Set G) = (L' : Set G)) {m : M}
    (hm : m ∈ fixedSub M (L : Set G)) : g • m ∈ fixedSub M (L' : Set G) := by
  have := smul_mem_fixedSub_conj g hm
  rwa [hconj] at this

theorem inv_mul_mul_mem_normalizer {L L' : Subgroup G} {g : G}
    (hconj : (fun s => g * s * g⁻¹) '' (L : Set G) = (L' : Set G)) {n : G}
    (hn : n ∈ Subgroup.normalizer (L' : Set G)) :
    g⁻¹ * n * g ∈ Subgroup.normalizer (L : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hn ⊢
  intro s
  have e : g * ((g⁻¹ * n * g) * s * (g⁻¹ * n * g)⁻¹) * g⁻¹ = n * (g * s * g⁻¹) * n⁻¹ := by
    group
  rw [mem_iff_of_image_conj hconj s, mem_iff_of_image_conj hconj
    ((g⁻¹ * n * g) * s * (g⁻¹ * n * g)⁻¹), e]
  exact hn _

theorem normalizer_invariant_map {L L' : Subgroup G} {g : G}
    (hconj : (fun s => g * s * g⁻¹) '' (L : Set G) = (L' : Set G)) {U : AddSubgroup M}
    (hUN : ∀ n ∈ Subgroup.normalizer (L : Set G), ∀ x ∈ U, n • x ∈ U) :
    ∀ n ∈ Subgroup.normalizer (L' : Set G), ∀ x ∈ U.map (DistribSMul.toAddMonoidHom M g),
      n • x ∈ U.map (DistribSMul.toAddMonoidHom M g) := by
  intro n hn x hx
  obtain ⟨x₀, hx₀, rfl⟩ := mem_map_smul.mp hx
  refine mem_map_smul.mpr ⟨(g⁻¹ * n * g) • x₀,
    hUN _ (inv_mul_mul_mem_normalizer hconj hn) x₀ hx₀, ?_⟩
  calc g • (g⁻¹ * n * g) • x₀ = (g * (g⁻¹ * n * g)) • x₀ := (mul_smul _ _ _).symm
    _ = (n * g) • x₀ := by rw [show g * (g⁻¹ * n * g) = n * g by group]
    _ = n • g • x₀ := mul_smul _ _ _

theorem map_smul_le_fixedSub {L L' : Subgroup G} {g : G}
    (hconj : (fun s => g * s * g⁻¹) '' (L : Set G) = (L' : Set G)) {U : AddSubgroup M}
    (hU : U ≤ fixedSub M (L : Set G)) :
    U.map (DistribSMul.toAddMonoidHom M g) ≤ fixedSub M (L' : Set G) := by
  rintro _ hm
  obtain ⟨x, hx, rfl⟩ := mem_map_smul.mp hm
  exact smul_mem_fixedSub_of_image_conj hconj (hU hx)

variable [Finite M]

theorem comm_eq_mul_smul_of_nonA2 (h2 : ∀ m : M, m + m = 0) {L L' : Subgroup G} {g : G}
    (hconj : (fun s => g * s * g⁻¹) '' (L : Set G) = (L' : Set G))
    (hdec : IsCompl (fixedSub M (L : Set G)) (fixedSub M (L' : Set G)))
    {U : AddSubgroup M} (hU : U ≤ fixedSub M (L : Set G)) {a y : G} (ha : a ∈ L')
    (ha2 : a * a = 1) (hLa : Subgroup.closure ((L : Set G) ∪ {a}) = ⊤) (hy : y ∈ L)
    (hy2 : y * y = 1) (hL'y : Subgroup.closure ((L' : Set G) ∪ {y}) = ⊤)
    (hbr : y * a * y = a * y * a) {x : M} (hx : x ∈ U) : comm M a x = (y * a) • x := by
  have hcard : Nat.card (fixedSub M (L : Set G)) = Nat.card (fixedSub M (L' : Set G)) := by
    rw [← hconj, card_fixedSub_conj]
  obtain ⟨hfa, -, -⟩ := pair_facts h2 ha ha2 hLa hdec hcard
  obtain ⟨hfy, -, -⟩ := pair_facts h2 hy hy2 hL'y hdec.symm hcard.symm
  have hfix : fixedSub M {y} ⊓ fixedSub M {a} = ⊥ := by
    rw [hfy, hfa]
    exact hdec.inf_eq_bot
  exact comm_eq_of_braid h2 hy2 ha2 hbr hfix (hU hx y hy)

theorem comm_mem_map_of_nonA2 (h2 : ∀ m : M, m + m = 0) {L L' : Subgroup G} {g : G}
    (hconj : (fun s => g * s * g⁻¹) '' (L : Set G) = (L' : Set G))
    (hdec : IsCompl (fixedSub M (L : Set G)) (fixedSub M (L' : Set G)))
    {U : AddSubgroup M} (hU : U ≤ fixedSub M (L : Set G))
    (hUN : ∀ n ∈ Subgroup.normalizer (L : Set G), ∀ x ∈ U, n • x ∈ U)
    {a y : G} (ha : a ∈ L') (ha2 : a * a = 1)
    (hLa : Subgroup.closure ((L : Set G) ∪ {a}) = ⊤)
    (hy : y ∈ L) (hy2 : y * y = 1) (hL'y : Subgroup.closure ((L' : Set G) ∪ {y}) = ⊤)
    (hbr : y * a * y = a * y * a) (hn : g⁻¹ * (y * a) ∈ Subgroup.normalizer (L : Set G))
    {x : M} (hx : x ∈ U) : comm M a x ∈ U.map (DistribSMul.toAddMonoidHom M g) := by
  refine mem_map_smul.mpr ⟨(g⁻¹ * (y * a)) • x, hUN _ hn x hx, ?_⟩
  rw [comm_eq_mul_smul_of_nonA2 h2 hconj hdec hU ha ha2 hLa hy hy2 hL'y hbr hx, ← mul_smul,
    mul_inv_cancel_left]

theorem le_invSub_of_generators (h2 : ∀ m : M, m + m = 0) {L L' : Subgroup G} {g : G}
    (hconj : (fun s => g * s * g⁻¹) '' (L : Set G) = (L' : Set G))
    (hdec : IsCompl (fixedSub M (L : Set G)) (fixedSub M (L' : Set G)))
    {U : AddSubgroup M} (hU : U ≤ fixedSub M (L : Set G))
    (hUN : ∀ n ∈ Subgroup.normalizer (L : Set G), ∀ x ∈ U, n • x ∈ U) {S : Set G}
    (hS : L' ≤ Subgroup.closure S)
    (hdata : ∀ a ∈ S, a ∈ L' ∧ a * a = 1 ∧ Subgroup.closure ((L : Set G) ∪ {a}) = ⊤ ∧
      ∃ y ∈ L, y * y = 1 ∧ Subgroup.closure ((L' : Set G) ∪ {y}) = ⊤ ∧ y * a * y = a * y * a ∧
        g⁻¹ * (y * a) ∈ Subgroup.normalizer (L : Set G)) :
    L' ≤ invSub G (U ⊔ U.map (DistribSMul.toAddMonoidHom M g)) := by
  refine hS.trans ((Subgroup.closure_le _).mpr fun a haS => ?_)
  obtain ⟨ha, ha2, hLa, y, hy, hy2, hL'y, hbr, hn⟩ := hdata a haS
  refine mem_invSub_of_mul_self ha2 fun m hm => ?_
  obtain ⟨x, hx, x', hx', rfl⟩ := mem_sup_map_smul.mp hm
  have hc := comm_mem_map_of_nonA2 h2 hconj hdec hU hUN ha ha2 hLa hy hy2 hL'y hbr hn hx
  have hfix : a • g • x' = g • x' :=
    smul_mem_fixedSub_of_image_conj hconj (hU hx') a ha
  have hx1 : a • x = x + comm M a x := by rw [comm_apply]; abel
  rw [smul_add, hfix, hx1]
  exact add_mem (add_mem (AddSubgroup.mem_sup_left hx) (AddSubgroup.mem_sup_right hc))
    (AddSubgroup.mem_sup_right (mem_map_smul.mpr ⟨x', hx', rfl⟩))

theorem invariant_of_two_sided {L L' : Subgroup G} {g : G} (hLL : L ⊔ L' = ⊤)
    {U : AddSubgroup M}
    (h1 : L' ≤ invSub G (U ⊔ U.map (DistribSMul.toAddMonoidHom M g)))
    (h2 : L ≤ invSub G (U.map (DistribSMul.toAddMonoidHom M g) ⊔
      (U.map (DistribSMul.toAddMonoidHom M g)).map (DistribSMul.toAddMonoidHom M g⁻¹))) :
    ∀ h : G, ∀ m ∈ U ⊔ U.map (DistribSMul.toAddMonoidHom M g),
      h • m ∈ U ⊔ U.map (DistribSMul.toAddMonoidHom M g) := by
  rw [map_smul_map_smul_inv, sup_comm] at h2
  have : L ⊔ L' ≤ invSub G (U ⊔ U.map (DistribSMul.toAddMonoidHom M g)) := sup_le h2 h1
  rw [hLL] at this
  intro h m hm
  exact (this (Subgroup.mem_top h) m hm).1

end Swap

section SubgroupOf

variable {G₀ : Type*} [Group G₀]

theorem zpowers_subgroupOf {E : Subgroup G₀} {x : G₀} (hx : x ∈ E) :
    (Subgroup.zpowers x).subgroupOf E = Subgroup.zpowers (⟨x, hx⟩ : E) := by
  ext y
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, Subtype.ext (by simpa using hn)⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, by simpa using congrArg Subtype.val hn⟩

theorem closure_subgroupOf_union_singleton {E H₁ : Subgroup G₀} {x : G₀} (hH₁ : H₁ ≤ E)
    (hx : x ∈ E) (h : H₁ ⊔ Subgroup.zpowers x = E) :
    Subgroup.closure ((H₁.subgroupOf E : Set E) ∪ {⟨x, hx⟩}) = ⊤ := by
  rw [Subgroup.closure_union, Subgroup.closure_eq, ← Subgroup.zpowers_eq_closure,
    ← zpowers_subgroupOf hx, ← Subgroup.subgroupOf_sup hH₁ (Subgroup.zpowers_le.mpr hx), h,
    Subgroup.subgroupOf_self]

theorem sup_subgroupOf_eq_top {E A A' : Subgroup G₀} (hA : A ≤ E) (hA' : A' ≤ E)
    (h : A ⊔ A' = E) : A.subgroupOf E ⊔ A'.subgroupOf E = ⊤ := by
  rw [← Subgroup.subgroupOf_sup hA hA', h, Subgroup.subgroupOf_self]

end SubgroupOf

end CFSG.ClassicalGroups.F2Swap
