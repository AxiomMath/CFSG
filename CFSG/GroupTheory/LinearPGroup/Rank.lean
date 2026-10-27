module

public import CFSG.GroupTheory.LinearPGroup.Weights
public import CFSG.GroupTheory.GeneratorBounds
public import CFSG.GH74.Defs

public section

namespace CFSG.LinearPGroup

theorem rank_le_of_isPGroup_of_isAlgClosed {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K : Type*} [Field K] [IsAlgClosed K] {p : ℕ} [Fact p.Prime] (hp : (p : K) ≠ 0)
    (P : Subgroup (GL ι K)) [Finite P] (hP : IsPGroup p P) :
    Group.rank P ≤ 2 * Fintype.card ι - 1 := by
  classical
  obtain ⟨A, hAn, hAc, hAcent⟩ :=
    CFSG.GroupTheory.exists_normal_commutative_centralizer_le hP
  haveI : A.Normal := hAn
  have hcardA : (Nat.card A : K) ≠ 0 := by
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp (hP.to_subgroup A)
    rw [hm, Nat.cast_pow]
    exact pow_ne_zero m hp
  obtain ⟨k, hk_le, χ, π, hχ, hπ⟩ :=
    exists_weights_of_normal_commutative P A (fun a b => hAc.is_comm.comm a b) hcardA
  have hrankA : Group.rank A ≤ k :=
    CFSG.GroupTheory.rank_le_of_jointly_injective_characters χ hχ
  have hker_le : π.ker ≤ A := by
    intro x hx
    refine hAcent ?_
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (hπ x hx ⟨a, ha⟩).symm
  have hrankP : Group.rank P ≤ Group.rank A + Group.rank (P ⧸ A) :=
    CFSG.PreuniquenessRankFour.Helpers.subgroup_rank_le_rank_add_quotient_rank A
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  ·
    have hAtriv : Subsingleton A := by
      rw [← Group.rank_eq_zero_iff]
      omega
    haveI : Subsingleton A := hAtriv
    have hmem : ∀ x : P, x ∈ A := by
      intro x
      refine hAcent ?_
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hy1 : y = 1 := by
        have h1 : (⟨y, hy⟩ : A) = ⟨1, A.one_mem⟩ := Subsingleton.elim _ _
        simpa using congrArg (fun a : A => (a : P)) h1
      rw [hy1, mul_one, one_mul]
    have hPsub : Subsingleton P := by
      refine ⟨fun x y => ?_⟩
      have hx1 : x = 1 := by
        have h1 : (⟨x, hmem x⟩ : A) = ⟨1, A.one_mem⟩ := Subsingleton.elim _ _
        simpa using congrArg (fun a : A => (a : P)) h1
      have hy1 : y = 1 := by
        have h1 : (⟨y, hmem y⟩ : A) = ⟨1, A.one_mem⟩ := Subsingleton.elim _ _
        simpa using congrArg (fun a : A => (a : P)) h1
      rw [hx1, hy1]
    have hrankP0 : Group.rank P = 0 := Group.rank_eq_zero P
    rw [hrankP0]
    omega
  ·
    have hrankQ : Group.rank (P ⧸ A) ≤ k - 1 := by
      have hsurj : Function.Surjective
          (QuotientGroup.map π.ker A (MonoidHom.id P) (by simpa using hker_le)) :=
        QuotientGroup.map_surjective_of_surjective π.ker A (MonoidHom.id P)
          (by simpa using QuotientGroup.mk_surjective) (by simpa using hker_le)
      have hrange : IsPGroup p π.range :=
        hP.of_surjective π.rangeRestrict π.rangeRestrict_surjective
      have h := CFSG.GroupTheory.rank_le_pred_of_injective_perm hrange hkpos
        π.range.subtype π.range.subtype_injective
      rw [← Group.rank_congr (QuotientGroup.quotientKerEquivRange π)] at h
      exact (Group.rank_le_of_surjective _ hsurj).trans h
    have h1 : Group.rank P ≤ k + (k - 1) :=
      hrankP.trans (add_le_add hrankA hrankQ)
    have h2 : k + (k - 1) ≤ 2 * Fintype.card ι - 1 := by omega
    exact h1.trans h2

theorem rank_le_of_isPGroup {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [Field K]
    {p : ℕ} [Fact p.Prime] (hp : (p : K) ≠ 0) (P : Subgroup (GL ι K)) [Finite P]
    (hP : IsPGroup p P) : Group.rank P ≤ 2 * Fintype.card ι - 1 := by
  classical
  let L := AlgebraicClosure K
  let f : GL ι K →* GL ι L := Matrix.GeneralLinearGroup.map (algebraMap K L)
  have hf : Function.Injective f :=
    Matrix.GeneralLinearGroup.map_injective (algebraMap K L).injective
  let P' : Subgroup (GL ι L) := P.map f
  let e : P ≃* P' := Subgroup.equivMapOfInjective P f hf
  have hP' : IsPGroup p P' := hP.map f
  haveI : Finite P' :=
    Finite.of_injective (fun x : P' => e.symm x) e.symm.injective
  have hpL : (p : L) ≠ 0 := by
    intro h
    apply hp
    apply (algebraMap K L).injective
    simpa using h
  have hmain : Group.rank P' ≤ 2 * Fintype.card ι - 1 :=
    rank_le_of_isPGroup_of_isAlgClosed hpL P' hP'
  rw [Group.rank_congr e]
  exact hmain

theorem sectionalTwoRankLE_GL (ι : Type) [Fintype ι] [DecidableEq ι] (K : Type) [Field K]
    [Finite K] (h2 : (2 : K) ≠ 0) :
    CFSG.GH74.SectionalTwoRankLE (GL ι K) (2 * Fintype.card ι - 1) := by
  classical
  intro P hP
  obtain ⟨S, hS_card, hS_top⟩ := Group.rank_spec P
  have hbound : Group.rank P ≤ 2 * Fintype.card ι - 1 :=
    rank_le_of_isPGroup (p := 2) h2 P hP
  refine ⟨S.image P.subtype, ?_, ?_⟩
  · calc (S.image P.subtype).card ≤ S.card := Finset.card_image_le
      _ = Group.rank P := hS_card
      _ ≤ 2 * Fintype.card ι - 1 := hbound
  · rw [Finset.coe_image, ← MonoidHom.map_closure, hS_top, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]

end CFSG.LinearPGroup

end
