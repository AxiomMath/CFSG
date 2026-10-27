module

public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.Algebra.Group.PUnit
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

@[expose] def PerfectCoreThree (P : Type*) [Group P] : Prop :=
  ∀ k : ℕ, derivedSeries P (k + 1) = derivedSeries P k →
    derivedSeries P k = ⊥ ∨ 3 ∣ Nat.card (derivedSeries P k)

section DerivedSeries

variable {P : Type*} [Group P]

theorem derivedSeries_eq_of_succ_eq {k : ℕ} (h : derivedSeries P (k + 1) = derivedSeries P k)
    (m : ℕ) (hm : k ≤ m) : derivedSeries P m = derivedSeries P k := by
  induction m, hm using Nat.le_induction with
  | base => rfl
  | succ m _ ih =>
    rw [derivedSeries_succ, ih, ← derivedSeries_succ, h]

theorem eq_bot_of_succ_eq [Group.IsSolvable P] {k : ℕ}
    (h : derivedSeries P (k + 1) = derivedSeries P k) : derivedSeries P k = ⊥ := by
  obtain ⟨n, hn⟩ := Group.IsSolvable.solvable (G := P)
  rw [← derivedSeries_eq_of_succ_eq h (max k n) (le_max_left _ _)]
  exact eq_bot_iff.mpr (hn ▸ derivedSeries_antitone P (le_max_right _ _))

theorem derivedSeries_succ_eq_of_finite [Finite P] :
    ∃ k : ℕ, derivedSeries P (k + 1) = derivedSeries P k := by
  have : Finite (Subgroup P) :=
    Finite.of_injective (fun H : Subgroup P => (H : Set P)) SetLike.coe_injective
  obtain ⟨i, j, hij, hf⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => derivedSeries P n)
  wlog hlt : i < j generalizing i j
  · exact this j i hij.symm hf.symm (lt_of_le_of_ne (not_lt.mp hlt) hij.symm)
  refine ⟨i, le_antisymm (derivedSeries_antitone P (Nat.le_succ i)) ?_⟩
  calc derivedSeries P i = derivedSeries P j := hf
    _ ≤ derivedSeries P (i + 1) := derivedSeries_antitone P hlt

theorem subgroup_eq_bot_of_perfect_of_solvable {D : Subgroup P} (hDD : ⁅D, D⁆ = D)
    [Group.IsSolvable D] : D = ⊥ := by
  by_contra hne
  have : Nontrivial D := (Subgroup.bot_or_nontrivial D).resolve_left hne
  have : Group.IsPerfect D := Subgroup.isPerfect_iff.mpr hDD
  exact Group.IsPerfect.not_isSolvable D inferInstance

theorem PerfectCoreThree.of_isSolvable [Group.IsSolvable P] : PerfectCoreThree P :=
  fun _ h => Or.inl (eq_bot_of_succ_eq h)

end DerivedSeries

theorem isSolvable_of_subsingleton {K : Type*} [Group K] [Subsingleton K] : Group.IsSolvable K :=
  Group.isSolvable_of_isSolvable_injective (f := (1 : K →* Unit))
    (Function.injective_of_subsingleton _)

theorem perfectCoreThree_of_two {P A B : Type*} [Group P] [Group A] [Group B] (f₁ : P →* A)
    (f₂ : P →* B) (h₁ : Function.Surjective f₁) (h₂ : Function.Surjective f₂)
    (hker : Group.IsSolvable ↥(f₁.ker ⊓ f₂.ker)) (hA : PerfectCoreThree A)
    (hB : PerfectCoreThree B) : PerfectCoreThree P := by
  intro k hk
  set D := derivedSeries P k with hD
  have hDD : ⁅D, D⁆ = D := by rw [hD, ← derivedSeries_succ]; exact hk
  have hk₁ : derivedSeries A (k + 1) = derivedSeries A k := by
    rw [← map_derivedSeries_eq h₁ (k + 1), hk, map_derivedSeries_eq h₁ k]
  have hk₂ : derivedSeries B (k + 1) = derivedSeries B k := by
    rw [← map_derivedSeries_eq h₂ (k + 1), hk, map_derivedSeries_eq h₂ k]
  have e₁ : derivedSeries A k = D.map f₁ := (map_derivedSeries_eq h₁ k).symm
  have e₂ : derivedSeries B k = D.map f₂ := (map_derivedSeries_eq h₂ k).symm
  rcases hA k hk₁ with hA0 | hA3
  · rcases hB k hk₂ with hB0 | hB3
    · left
      rw [e₁, Subgroup.map_eq_bot_iff] at hA0
      rw [e₂, Subgroup.map_eq_bot_iff] at hB0
      have hDK : D ≤ f₁.ker ⊓ f₂.ker := le_inf hA0 hB0
      have : Group.IsSolvable D :=
        Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hDK)
      exact subgroup_eq_bot_of_perfect_of_solvable hDD
    · right
      rw [e₂] at hB3
      exact hB3.trans (Subgroup.card_map_dvd D f₂)
  · right
    rw [e₁] at hA3
    exact hA3.trans (Subgroup.card_map_dvd D f₁)

theorem PerfectCoreThree.of_surjective {P Q : Type*} [Group P] [Group Q] (f : P →* Q)
    (hf : Function.Surjective f) (hker : Group.IsSolvable f.ker) (hQ : PerfectCoreThree Q) :
    PerfectCoreThree P :=
  perfectCoreThree_of_two f f hf hf (by rwa [inf_idem]) hQ hQ

theorem PerfectCoreThree.of_mulEquiv {P Q : Type*} [Group P] [Group Q] (e : P ≃* Q)
    (hQ : PerfectCoreThree Q) : PerfectCoreThree P := by
  refine PerfectCoreThree.of_surjective e.toMonoidHom e.surjective ?_ hQ
  have hsub : Subsingleton (MonoidHom.ker e.toMonoidHom) :=
    ⟨fun a b => Subtype.ext (e.injective ((MonoidHom.mem_ker.mp a.2).trans
      (MonoidHom.mem_ker.mp b.2).symm))⟩
  exact isSolvable_of_subsingleton

theorem perfectCoreThree_perm (n : ℕ) : PerfectCoreThree (Equiv.Perm (Fin n)) := by
  by_cases hn : n ≤ 4
  · have : Group.IsSolvable (Equiv.Perm (Fin n)) := Equiv.Perm.isSolvable (by simpa using hn)
    exact PerfectCoreThree.of_isSolvable
  · have h5 : 5 ≤ Nat.card (Fin n) := by simp; omega
    have hA : ⁅alternatingGroup (Fin n), alternatingGroup (Fin n)⁆ = alternatingGroup (Fin n) :=
      commutator_alternatingGroup_eq_self h5
    have hser : ∀ k : ℕ, derivedSeries (Equiv.Perm (Fin n)) (k + 1) =
        alternatingGroup (Fin n) := by
      intro k
      induction k with
      | zero =>
        rw [derivedSeries_one]
        exact alternatingGroup.commutator_perm_eq h5
      | succ k ih => rw [derivedSeries_succ, ih, hA]
    have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
    intro k hk
    right
    cases k with
    | zero =>
      exfalso
      have h0 : derivedSeries (Equiv.Perm (Fin n)) 1 = ⊤ := hk
      rw [hser 0] at h0
      have hidx := alternatingGroup.index_eq_two (α := Fin n)
      rw [h0, Subgroup.index_top] at hidx
      omega
    | succ k =>
      rw [hser k, nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
      have h3 : 3 ∣ n.factorial := Nat.dvd_factorial (by norm_num) (by omega)
      obtain ⟨m, hm⟩ : 2 ∣ n.factorial := Nat.dvd_factorial (by norm_num) (by omega)
      rw [hm, Nat.mul_div_cancel_left _ (by norm_num)]
      rw [hm] at h3
      exact Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) h3

theorem perfectCoreThree_perm_prod (r s : ℕ) :
    PerfectCoreThree (Equiv.Perm (Fin r) × Equiv.Perm (Fin s)) := by
  refine perfectCoreThree_of_two (MonoidHom.fst _ _) (MonoidHom.snd _ _)
    (fun a => ⟨(a, 1), rfl⟩) (fun b => ⟨(1, b), rfl⟩) ?_ (perfectCoreThree_perm r)
    (perfectCoreThree_perm s)
  have : Subsingleton ↥((MonoidHom.fst (Equiv.Perm (Fin r)) (Equiv.Perm (Fin s))).ker ⊓
      (MonoidHom.snd (Equiv.Perm (Fin r)) (Equiv.Perm (Fin s))).ker) :=
    ⟨fun a b => Subtype.ext (Prod.ext ((MonoidHom.mem_ker.mp a.2.1).trans
      (MonoidHom.mem_ker.mp b.2.1).symm) ((MonoidHom.mem_ker.mp a.2.2).trans
      (MonoidHom.mem_ker.mp b.2.2).symm))⟩
  exact isSolvable_of_subsingleton

theorem isSolvable_of_perfectCoreThree {Y : Type*} [Group Y] [Finite Y] (hY : PerfectCoreThree Y)
    (h3 : ∀ D : Subgroup Y, ⁅D, D⁆ = D → ¬ 3 ∣ Nat.card D) : Group.IsSolvable Y := by
  obtain ⟨k, hk⟩ := derivedSeries_succ_eq_of_finite (P := Y)
  have hDD : ⁅derivedSeries Y k, derivedSeries Y k⁆ = derivedSeries Y k := by
    rw [← derivedSeries_succ]
    exact hk
  rcases hY k hk with h | h
  · exact ⟨⟨k, h⟩⟩
  · exact absurd h (h3 _ hDD)

end CFSG.LocalAnalysis.RankThreeTheoremC
