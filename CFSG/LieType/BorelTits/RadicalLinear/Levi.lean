module

public import CFSG.LieType.BorelTits.RadicalLinear.LeviMaps
public import CFSG.LieType.BorelTits.RadicalLinear.QuasisimpleImage

public section

namespace CFSG.LieType.BorelTits.RadicalLinear

open Matrix CFSG.StandardType.GGOppRad

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [Field K] [Finite K]
  {G : Type*} [Group G]

theorem exists_levi_of_isQuasisimple (hK3 : Nat.card K ≠ 3) (π : SpecialLinearGroup ι K →* G)
    (hπ : Function.Surjective π) (hker : π.ker = Subgroup.center (SpecialLinearGroup ι K))
    (ℓ : ι → ℕ) (g : SpecialLinearGroup ι K) (U : Subgroup G)
    (hU : U = ((stdU (K := K) ℓ).map (MulAut.conj g).toMonoidHom).map π)
    (hP : (Subgroup.normalizer (U : Set G)).comap π =
      (stdP (K := K) ℓ).map (MulAut.conj g).toMonoidHom)
    (S : Subgroup (↥(Subgroup.normalizer (U : Set G)) ⧸
      U.subgroupOf (Subgroup.normalizer (U : Set G))))
    (hSn : S.Normal) (hS : CFSG.IsQuasisimple S) :
    ∃ i : Fin (levelsCard ℓ), 2 ≤ levelCount ℓ i ∧ ¬ (levelCount ℓ i = 2 ∧ Nat.card K = 2) ∧
      ∃ Z' ≤ Subgroup.center S, ∃ _ : Z'.Normal,
        Nonempty (S ⧸ Z' ≃* ProjectiveSpecialLinearGroup (Block ℓ (levels ℓ i)) K) := by
  classical
  have hθ : Function.Surjective (leviTheta π U ℓ g hP) :=
    leviTheta_surjective π U ℓ g hP hπ
  have h3 : ∀ x : ℕ, (leviTheta π U ℓ g hP).ker ≤ (leviF ℓ g x).ker := fun x =>
    leviTheta_ker_le_leviF_ker π U ℓ g hP hU hker x
  let Psi : ∀ i : Fin (levelsCard ℓ),
      leviX U →* PGL (Block ℓ (levels ℓ i)) K := fun i =>
    leviPsi π U ℓ g hP hθ (levels ℓ i) (h3 (levels ℓ i))
  let J : ∀ i : Fin (levelsCard ℓ),
      Subgroup (PGL (Block ℓ (levels ℓ i)) K) := fun i =>
    slImage (Block ℓ (levels ℓ i)) K
  let good : Fin (levelsCard ℓ) → Prop := fun i =>
    2 ≤ levelCount ℓ i ∧ ¬ (levelCount ℓ i = 2 ∧ Nat.card K = 2)
  have hcomm : ∀ x y : leviX U, (∀ i, Psi i x = 1) → (∀ i, Psi i y = 1) →
      x * y = y * x := fun x y hx hy =>
    leviPsi_comm π U ℓ g hP hU hθ h3 x y hx hy
  have hbad : ∀ i, ¬ good i → IsSolvable (Psi i).range := by
    intro i hi
    have hm : 1 ≤ levelCount ℓ i := one_le_levelCount ℓ i
    have hcard : Fintype.card (Block ℓ (levels ℓ i)) = levelCount ℓ i :=
      card_subtype_eq_levelCount ℓ i
    haveI : Group.IsSolvable (PGL (Block ℓ (levels ℓ i)) K) := by
      by_cases h2 : 2 ≤ levelCount ℓ i
      · have hmn : levelCount ℓ i = 2 ∧ Nat.card K = 2 := by
          by_contra h
          exact hi ⟨h2, h⟩
        exact isSolvable_pgl_of_card_eq_two (Block ℓ (levels ℓ i)) K
          (by rw [hcard]; exact hmn.1) hmn.2
      · have h1 : levelCount ℓ i = 1 := by omega
        exact isSolvable_pgl_of_card_eq_one (Block ℓ (levels ℓ i)) K
          (by rw [hcard]; exact h1)
    exact (inferInstance : Group.IsSolvable (Psi i).range)
  have hsimple : ∀ i, good i → IsSimpleGroup (J i) := by
    intro i hi
    have hcard : Fintype.card (Block ℓ (levels ℓ i)) = levelCount ℓ i :=
      card_subtype_eq_levelCount ℓ i
    refine isSimpleGroup_slImage (Block ℓ (levels ℓ i)) K ?_ ?_
    · rw [hcard]
      exact hi.1
    · rintro ⟨h2, hKle⟩
      have hKge : 2 ≤ Nat.card K := by
        have h := Finite.one_lt_card (α := K)
        omega
      have hK2 : Nat.card K = 2 := by omega
      exact hi.2 ⟨by rw [← hcard]; exact h2, hK2⟩
  have hle : ∀ i, good i → J i ≤ (Psi i).range := by
    intro i _ y hy
    obtain ⟨A, hA⟩ := MonoidHom.mem_range.mp hy
    let s : stdP (K := K) ℓ :=
      ⟨blockEmbed ℓ (levels ℓ i) A, blockEmbed_mem_stdP ℓ (levels ℓ i) A⟩
    let p : leviP ℓ g := ⟨MulAut.conj g (s : SpecialLinearGroup ι K),
      Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom s.2⟩
    have hinner : leviInner ℓ g p = s := by
      apply Subtype.ext
      rw [leviInner_apply]
      exact MulEquiv.symm_apply_apply (MulAut.conj g) (s : SpecialLinearGroup ι K)
    refine ⟨leviTheta π U ℓ g hP p, ?_⟩
    calc Psi i (leviTheta π U ℓ g hP p) = leviF ℓ g (levels ℓ i) p :=
          leviPsi_apply π U ℓ g hP hθ (levels ℓ i) (h3 (levels ℓ i)) p
      _ = QuotientGroup.mk' (Subgroup.center (GL (Block ℓ (levels ℓ i)) K))
            (blockHom ℓ (levels ℓ i) (leviInner ℓ g p)) :=
          leviF_apply ℓ g (levels ℓ i) p
      _ = QuotientGroup.mk' (Subgroup.center (GL (Block ℓ (levels ℓ i)) K))
            (blockHom ℓ (levels ℓ i) s) := by rw [hinner]
      _ = QuotientGroup.mk' (Subgroup.center (GL (Block ℓ (levels ℓ i)) K))
            (SpecialLinearGroup.toGL A) := by
          rw [show blockHom ℓ (levels ℓ i) s =
            SpecialLinearGroup.toGL A from blockHom_blockEmbed ℓ (levels ℓ i) A]
      _ = y := hA
  have hcommJ : ∀ i, good i → commutator (PGL (Block ℓ (levels ℓ i)) K) ≤ J i :=
    fun i _ => commutator_le_slImage (Block ℓ (levels ℓ i)) K
  obtain ⟨i, hgood, hmap, hkerS⟩ :=
    exists_map_eq_of_isQuasisimple Psi J good hcomm hbad hsimple hle hcommJ hSn hS
  refine ⟨i, hgood.1, hgood.2, ?_⟩
  refine ⟨(Psi i).ker.subgroupOf S, hkerS,
    (MonoidHom.normal_ker (Psi i)).subgroupOf S, ?_⟩
  obtain ⟨e1⟩ := nonempty_quotient_ker_subgroupOf_equiv (Psi i) S
  obtain ⟨e2⟩ := nonempty_slImage_equiv (Block ℓ (levels ℓ i)) K
  exact ⟨e1.trans ((MulEquiv.subgroupCongr hmap).trans e2)⟩

end CFSG.LieType.BorelTits.RadicalLinear
