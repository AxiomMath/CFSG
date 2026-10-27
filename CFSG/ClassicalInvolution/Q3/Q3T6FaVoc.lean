module

public import CFSG.ClassicalInvolution.Uniform.UMember
public import CFSG.ClassicalInvolution.Q3.Q3T6LinEquiv

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T6

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Uniform
open scoped MatrixGroups

section SectionMember

variable {G : Type} [Group G]

structure IsSectionMemberU (t : MemberType) (Y K : Subgroup G) (z : G) : Prop where
  admissible : t.Admissible
  le : K ≤ Y
  orderOf_eq_two : orderOf z = 2
  mem : z ∈ K
  subnormal : IsSubnormal K (Subgroup.centralizer ({z} : Set G) ⊓ Y)
  witness : t.Witness K
  perfect : ¬ t.IsSolvableType → Group.IsPerfect K

namespace IsSectionMemberU

variable {t : MemberType} {Y K : Subgroup G} {z : G}

theorem sq (h : IsSectionMemberU t Y K z) : z * z = 1 := by
  rw [← pow_two, ← h.orderOf_eq_two]
  exact pow_orderOf_eq_one z

theorem ne_one (h : IsSectionMemberU t Y K z) : z ≠ 1 := by
  intro hz
  have h2 := h.orderOf_eq_two
  rw [hz, orderOf_one] at h2
  exact absurd h2 (by norm_num)

theorem central (h : IsSectionMemberU t Y K z) {k : G} (hk : k ∈ K) : k * z = z * k :=
  Subgroup.mem_centralizer_singleton_iff.mp (isSubnormal_le h.subnormal hk).1

theorem restrict (h : IsSectionMemberU t Y K z) {H : Subgroup G} (hHY : H ≤ Y) (hKH : K ≤ H) :
    IsSectionMemberU t H K z :=
  { h with
    le := hKH
    subnormal := by
      have h1 := isSubnormal_inf h.subnormal H
      rwa [inf_eq_left.mpr hKH, inf_assoc, inf_eq_right.mpr hHY] at h1 }

theorem conj (h : IsSectionMemberU t Y K z) {n : G} (hn : n ∈ Y) :
    IsSectionMemberU t Y (conjSub n K) (n * z * n⁻¹) where
  admissible := h.admissible
  le := by
    have := conjSub_mono (n := n) h.le
    rwa [conjSub_eq_self_of_mem hn] at this
  orderOf_eq_two := by rw [orderOf_conj_eq]; exact h.orderOf_eq_two
  mem := conj_mem_conjSub h.mem
  subnormal := by
    have h1 := isSubnormal_map_conj h.subnormal n
    have h2 : (Subgroup.centralizer ({z} : Set G) ⊓ Y).map (MulAut.conj n).toMonoidHom =
        Subgroup.centralizer ({n * z * n⁻¹} : Set G) ⊓ Y := by
      rw [Subgroup.map_inf_eq _ _ (MulAut.conj n).toMonoidHom (MulAut.conj n).injective,
        map_conj_centralizer_singleton]
      show _ ⊓ conjSub n Y = _
      rw [conjSub_eq_self_of_mem hn]
    exact h2 ▸ h1
  witness := by
    let e : K ≃* conjSub n K :=
      K.equivMapOfInjective (MulAut.conj n).toMonoidHom (MulAut.conj n).injective
    exact MemberType.Witness.of_mulEquiv e h.witness
  perfect hns := by
    have := h.perfect hns
    let e : K ≃* conjSub n K :=
      K.equivMapOfInjective (MulAut.conj n).toMonoidHom (MulAut.conj n).injective
    exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective

theorem toIn (h : IsSectionMemberU t Y K z) : ∃ hz : z ∈ Y, IsClassicalMemberU t (K.subgroupOf Y) (⟨z, hz⟩ : Y) := by
  have hzY : z ∈ Y := h.le h.mem
  have e : K.subgroupOf Y ≃* K := Subgroup.subgroupOfEquivOfLe h.le
  refine ⟨hzY, ?_⟩
  exact
    { admissible := h.admissible
      orderOf_eq_two := by rw [Subgroup.orderOf_mk]; exact h.orderOf_eq_two
      mem := Subgroup.mem_subgroupOf.mpr h.mem
      subnormal := by
        have h2 : (Subgroup.centralizer ({z} : Set G) ⊓ Y).subgroupOf Y =
            Subgroup.centralizer ({(⟨z, hzY⟩ : Y)} : Set Y) := by
          ext x
          simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
            Set.mem_singleton_iff, forall_eq]
          exact ⟨fun hx => Subtype.ext hx.1, fun hx => ⟨congrArg Subtype.val hx, x.2⟩⟩
        rw [← h2]
        exact isSubnormal_subgroupOf h.subnormal Y
      witness := MemberType.Witness.of_mulEquiv e.symm h.witness
      perfect := fun hns => by
        have := h.perfect hns
        exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective }

theorem toClassical (h : IsSectionMemberU t ⊤ K z) : IsClassicalMemberU t K z where
  admissible := h.admissible
  orderOf_eq_two := h.orderOf_eq_two
  mem := h.mem
  subnormal := by simpa using h.subnormal
  witness := h.witness
  perfect := h.perfect

end IsSectionMemberU

theorem isSectionMemberU_of_isClassicalMemberU {t : MemberType} {K : Subgroup G} {z : G}
    (h : IsClassicalMemberU t K z) {Y : Subgroup G} (hKY : K ≤ Y) : IsSectionMemberU t Y K z where
  admissible := h.admissible
  le := hKY
  orderOf_eq_two := h.orderOf_eq_two
  mem := h.mem
  subnormal := by
    have := isSubnormal_inf h.subnormal Y
    rwa [inf_eq_left.mpr hKY] at this
  witness := h.witness
  perfect := h.perfect

theorem isSectionMemberU_self {t : MemberType} {J : Subgroup G} {v : G}
    (h : IsClassicalMemberU t J v) :
    IsSectionMemberU t (Subgroup.centralizer ({v} : Set G)) J v where
  admissible := h.admissible
  le := isSubnormal_le h.subnormal
  orderOf_eq_two := h.orderOf_eq_two
  mem := h.mem
  subnormal := by rw [inf_idem]; exact h.subnormal
  witness := h.witness
  perfect := h.perfect

end SectionMember

section Noncomm

theorem Fa.sl2_not_comm (F : Type) [Field F] : ¬ ∀ a b : SL(2, F), a * b = b * a := by
  intro h
  let a : SL(2, F) := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
  let b : SL(2, F) := ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩
  have h1 := congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F) 0 0) (h a b)
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul] at h1
  simp [a, b, Matrix.mul_apply, Fin.sum_univ_two] at h1

variable {p f : ℕ} {Y : Type} [Group Y] {L : Subgroup Y} {z : Y}

theorem exists_noncomm_of_sl2 (h : IsClassicalMemberU (.sl2 p f) L z) :
    ∃ x ∈ L, ∃ y ∈ L, x * y ≠ y * x := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hp, ⟨e⟩⟩ := h.witness
  have := hp
  refine Fa.sl2_not_comm (GaloisField p f) fun a b => ?_
  obtain ⟨a', ha'⟩ := QuotientGroup.mk'_surjective (classicalInvolutionOddCore L) (e.symm a)
  obtain ⟨b', hb'⟩ := QuotientGroup.mk'_surjective (classicalInvolutionOddCore L) (e.symm b)
  apply e.symm.injective
  rw [map_mul, map_mul, ← ha', ← hb', ← map_mul, ← map_mul]
  exact congrArg _ (Subtype.ext (hcon a' a'.2 b' b'.2))

theorem not_le_center_of_sl2 (h : IsClassicalMemberU (.sl2 p f) L z) :
    ¬ L ≤ Subgroup.center Y := by
  intro hle
  obtain ⟨x, hx, y, hy, hxy⟩ := exists_noncomm_of_sl2 h
  exact hxy (Subgroup.mem_center_iff.mp (hle hx) y).symm

end Noncomm

section Transport

theorem Fa.map_centralizer_singleton {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y') (z : Y) :
    (Subgroup.centralizer ({z} : Set Y)).map e.toMonoidHom =
      Subgroup.centralizer ({e z} : Set Y') := by
  ext x'
  obtain ⟨x, rfl⟩ := e.surjective x'
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply, Subgroup.mem_centralizer_iff,
    Subgroup.mem_centralizer_iff]
  simp only [Set.mem_singleton_iff, forall_eq]
  rw [← map_mul, ← map_mul, e.injective.eq_iff]

theorem isClassicalMemberU_map_mulEquiv {t : MemberType} {Y Y' : Type} [Group Y] [Group Y']
    (e : Y ≃* Y') {L : Subgroup Y} {z : Y} (h : IsClassicalMemberU t L z) :
    IsClassicalMemberU t (L.map e.toMonoidHom) (e z) where
  admissible := h.admissible
  orderOf_eq_two := by rw [MulEquiv.orderOf_eq]; exact h.orderOf_eq_two
  mem := Subgroup.mem_map_of_mem _ h.mem
  subnormal := by
    rw [← Fa.map_centralizer_singleton e z]
    exact isSubnormal_map_mulEquiv e h.subnormal
  witness := by
    let eL : L ≃* L.map e.toMonoidHom := L.equivMapOfInjective e.toMonoidHom e.injective
    exact MemberType.Witness.of_mulEquiv eL h.witness
  perfect hns := by
    have := h.perfect hns
    let eL : L ≃* L.map e.toMonoidHom := L.equivMapOfInjective e.toMonoidHom e.injective
    exact Group.IsPerfect.ofSurjective (f := eL.toMonoidHom) eL.surjective

end Transport

section Perfect

theorem Fa.false_of_perfect_quotient {F : Type} [Field F] (hF : Nat.card F = 3) {L : Type}
    [Group L] [Group.IsPerfect L] (N : Subgroup L) [N.Normal] (e : L ⧸ N ≃* SL(2, F)) :
    False := by
  have hQ : Group.IsPerfect (L ⧸ N) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
  have hS : Group.IsPerfect SL(2, F) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  exact commutator_ne_top_of_equiv_sl2_of_card_three hF (MulEquiv.refl _) hS.commutator_eq_top

variable {p f : ℕ} {Y : Type} [Group Y] {L : Subgroup Y} {z : Y}

theorem not_isPerfect_of_isClassicalMemberU_three (h : IsClassicalMemberU (.sl2 p f) L z)
    (h3 : p ^ f = 3) : ¬ Group.IsPerfect L := by
  intro hperf
  obtain ⟨hp, ⟨e⟩⟩ := h.witness
  have := hp
  exact Fa.false_of_perfect_quotient
    (by rw [natCard_galoisField_eq (p := p) (f := f) h.admissible.2.2]; exact h3)
    (classicalInvolutionOddCore L) e

theorem Fa.false_of_isClassicalMember [Fact p.Prime] (h3 : p ^ f = 3)
    (h : IsClassicalMember p f L z) : False := by
  have hf : 0 < f := Nat.pos_of_ne_zero (by rintro rfl; simp at h3)
  have := h.perfect
  obtain ⟨e⟩ := h.nonempty_equiv
  exact Fa.false_of_perfect_quotient
    (by rw [natCard_galoisField_eq (p := p) (f := f) hf]; exact h3)
    (classicalInvolutionOddCore L) e

theorem Fa.eq_empty_of_forall_isClassicalMember [Fact p.Prime] (h3 : p ^ f = 3)
    {Ω : Set (Subgroup Y)} (hcl : ∀ K ∈ Ω, ∃ w : Y, IsClassicalMember p f K w) : Ω = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun K hK => ?_
  obtain ⟨w, hw⟩ := hcl K hK
  exact Fa.false_of_isClassicalMember h3 hw

end Perfect

end CFSG.ClassicalInvolution.Q3.Q3T6
