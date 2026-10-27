module

public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import CFSG.CharacterTheory.Semidihedral.Local.FourQuaternionAutomorphisms

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.Lc

theorem perflc_solvable_mulAut {Q : Type*} [Group Q] (hQ : Nonempty (Q ≃* QuaternionGroup 2)) :
    Group.IsSolvable (MulAut Q) := by
  obtain ⟨hX, -, ⟨ρ, -, -, hker⟩, -⟩ :=
    CFSG.Semidihedral.Local.quaternionEight_automorphism_action hQ
  have hfin : Finite {H : Subgroup Q // IsCyclic H ∧ Nat.card H = 4} :=
    Nat.finite_of_card_ne_zero (by rw [hX]; norm_num)
  have hsolv : Group.IsSolvable (Equiv.Perm {H : Subgroup Q // IsCyclic H ∧ Nat.card H = 4}) :=
    Equiv.Perm.isSolvable (by rw [hX]; norm_num)
  obtain ⟨e⟩ := hQ
  have : Finite Q := Finite.of_equiv (QuaternionGroup 2) e.symm.toEquiv
  have hQcard : Nat.card Q = 2 ^ 3 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    norm_num
  have : Group.IsNilpotent Q := (IsPGroup.of_card hQcard).isNilpotent
  exact Group.isSolvable_of_ker_le_range (MulAut.conj : Q →* MulAut Q) ρ hker.le

theorem perflc_hom_eq_one {A B : Type*} [Group A] [Group B] [Group.IsPerfect A]
    [Group.IsSolvable B] (f : A →* B) (a : A) : f a = 1 := by
  have : Group.IsPerfect f.range := Group.IsPerfect.range f
  have hs : Subsingleton f.range := by
    by_contra h
    rw [not_subsingleton_iff_nontrivial] at h
    exact Group.IsPerfect.not_isSolvable f.range inferInstance
  exact congrArg Subtype.val (hs.elim (⟨f a, a, rfl⟩ : f.range) 1)

private abbrev cj {G : Type*} [Group G] (c : G) (H : Subgroup G) : Subgroup G :=
  H.map (MulAut.conj c).toMonoidHom

private theorem mem_cj {G : Type*} [Group G] {c x : G} {H : Subgroup G} :
    x ∈ cj c H ↔ c⁻¹ * x * c ∈ H := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro h
    exact ⟨c⁻¹ * x * c, h, by simp [MulAut.conj_apply, mul_assoc]⟩

private theorem cj_one {G : Type*} [Group G] (H : Subgroup G) : cj 1 H = H := by
  ext x
  simp [mem_cj]

private theorem cj_mul {G : Type*} [Group G] (a b : G) (H : Subgroup G) :
    cj (a * b) H = cj a (cj b H) := by
  ext x
  simp only [mem_cj]
  rw [show (a * b)⁻¹ * x * (a * b) = b⁻¹ * (a⁻¹ * x * a) * b by group]

private noncomputable def actHom {G : Type*} [Group G] (A : Subgroup G) (S : Set (Subgroup G))
    (hS : ∀ a ∈ A, ∀ H ∈ S, cj a H ∈ S) : A →* Equiv.Perm S where
  toFun a :=
    { toFun := fun H => ⟨cj (a : G) H.1, hS a a.2 H.1 H.2⟩
      invFun := fun H => ⟨cj (a : G)⁻¹ H.1, hS _ (A.inv_mem a.2) H.1 H.2⟩
      left_inv := fun H => Subtype.ext (by
        show cj (a : G)⁻¹ (cj (a : G) H.1) = H.1
        rw [← cj_mul, inv_mul_cancel, cj_one])
      right_inv := fun H => Subtype.ext (by
        show cj (a : G) (cj (a : G)⁻¹ H.1) = H.1
        rw [← cj_mul, mul_inv_cancel, cj_one]) }
  map_one' := Equiv.ext fun H => Subtype.ext (cj_one H.1)
  map_mul' a b := Equiv.ext fun H => Subtype.ext (cj_mul (a : G) (b : G) H.1)

private theorem le_centralizer_of_fix {G : Type*} [Group G] {Q A : Subgroup G}
    (hQ : Nonempty (↥Q ≃* QuaternionGroup 2)) (hfix : ∀ a ∈ A, cj a Q = Q)
    (hperf : Group.IsPerfect ↥A) : A ≤ Subgroup.centralizer (Q : Set G) := by
  have hAN : A ≤ Subgroup.normalizer (Q : Set G) := fun a ha =>
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hfix a ha)
  have := perflc_solvable_mulAut hQ
  intro a ha
  have h1 := perflc_hom_eq_one (Q.normalizerMonoidHom.comp (Subgroup.inclusion hAN)) ⟨a, ha⟩
  have h2 : Subgroup.inclusion hAN ⟨a, ha⟩ ∈ Q.normalizerMonoidHom.ker := h1
  rw [Subgroup.normalizerMonoidHom_ker] at h2
  exact h2

private theorem le_centralizer_sup {G : Type*} [Group G] {P P' A : Subgroup G}
    (hP : A ≤ Subgroup.centralizer (P : Set G)) (hP' : A ≤ Subgroup.centralizer (P' : Set G)) :
    A ≤ Subgroup.centralizer ((P ⊔ P' : Subgroup G) : Set G) := by
  intro a ha
  have h : ∀ Q : Subgroup G, A ≤ Subgroup.centralizer (Q : Set G) →
      Q ≤ Subgroup.centralizer ({a} : Set G) := fun Q hQ x hx => by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact ((Subgroup.mem_centralizer_iff.mp (hQ ha)) x hx).symm
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  exact (Subgroup.mem_centralizer_iff.mp (sup_le (h P hP) (h P' hP') hg) a rfl).symm

theorem perfect_centralizes_twins {G : Type*} [Group G] {P P' A : Subgroup G} {t : G}
    (hP : Nonempty (↥P ≃* QuaternionGroup 2)) (hP' : Nonempty (↥P' ≃* QuaternionGroup 2))
    (hne : P ≠ P')
    (hperm : ∀ c ∈ Subgroup.centralizer ({t} : Set G),
      (P.map (MulAut.conj c).toMonoidHom = P ∨ P.map (MulAut.conj c).toMonoidHom = P') ∧
      (P'.map (MulAut.conj c).toMonoidHom = P ∨ P'.map (MulAut.conj c).toMonoidHom = P'))
    (hAt : A ≤ Subgroup.centralizer ({t} : Set G)) (hperf : Group.IsPerfect ↥A) :
    A ≤ Subgroup.centralizer ((P ⊔ P' : Subgroup G) : Set G) := by
  have hS : ∀ a ∈ A, ∀ H ∈ ({P, P'} : Set (Subgroup G)), cj a H ∈ ({P, P'} : Set (Subgroup G)) := by
    intro a ha H hH
    obtain ⟨h1, h2⟩ := hperm a (hAt ha)
    rcases hH with rfl | rfl
    · exact h1
    · exact h2
  have hcard : Nat.card ({P, P'} : Set (Subgroup G)) = 2 := by
    rw [Nat.card_coe_set_eq]
    exact Set.ncard_pair hne
  have : Finite ({P, P'} : Set (Subgroup G)) := inferInstance
  have : Group.IsSolvable (Equiv.Perm ({P, P'} : Set (Subgroup G))) :=
    Equiv.Perm.isSolvable (by rw [hcard]; norm_num)
  have := hperf
  have hfix : ∀ a ∈ A, ∀ H ∈ ({P, P'} : Set (Subgroup G)), cj a H = H := fun a ha H hH =>
    congrArg (fun σ : Equiv.Perm ({P, P'} : Set (Subgroup G)) => (σ ⟨H, hH⟩ : Subgroup G))
      (perflc_hom_eq_one (actHom A _ hS) ⟨a, ha⟩)
  have hAP := le_centralizer_of_fix hP (fun a ha => hfix a ha P (Set.mem_insert _ _)) hperf
  have hAP' := le_centralizer_of_fix hP'
    (fun a ha => hfix a ha P' (Set.mem_insert_of_mem _ rfl)) hperf
  exact le_centralizer_sup hAP hAP'

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.Lc
