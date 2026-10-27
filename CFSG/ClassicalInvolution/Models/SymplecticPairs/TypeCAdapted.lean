module

public import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCShortRoot

public section

namespace CFSG.ClassicalInvolution.Models.SymplecticPairs

open Matrix CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

section Predicate

variable {M : Type*} [Group M]

@[expose] def IsAdaptedShort (TA TB : Subgroup M) (zA : M) (S : Subgroup M) : Prop :=
  ∃ x ∈ TA, ∃ y ∈ TB, x * y ∉ Subgroup.center M ∧
    ¬ Subgroup.centralizer ({x * y} : Set M) ≤ Subgroup.centralizer ({zA} : Set M) ∧
    S = ⁅Subgroup.centralizer ({x * y} : Set M), Subgroup.centralizer ({x * y} : Set M)⁆

theorem map_centralizer_singleton {M' : Type*} [Group M'] (e : M ≃* M') (d : M) :
    (Subgroup.centralizer ({d} : Set M)).map e.toMonoidHom =
      Subgroup.centralizer ({e d} : Set M') := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hy]
  · intro hx
    refine ⟨e.symm x, ?_, by simp⟩
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hx

theorem mem_center_map_iff {M' : Type*} [Group M'] (e : M ≃* M') (d : M) :
    e d ∈ Subgroup.center M' ↔ d ∈ Subgroup.center M := by
  simp only [Subgroup.mem_center_iff]
  constructor
  · intro h g
    apply e.injective
    rw [map_mul, map_mul]
    exact h (e g)
  · intro h g'
    obtain ⟨g, rfl⟩ := e.surjective g'
    rw [← map_mul, ← map_mul, h g]

theorem isAdaptedShort_map_iff {M' : Type*} [Group M'] (e : M ≃* M') (TA TB : Subgroup M) (zA : M)
    (S : Subgroup M) :
    IsAdaptedShort TA TB zA S ↔
      IsAdaptedShort (TA.map e.toMonoidHom) (TB.map e.toMonoidHom) (e zA)
        (S.map e.toMonoidHom) := by
  have hle : ∀ C D : Subgroup M, C.map e.toMonoidHom ≤ D.map e.toMonoidHom ↔ C ≤ D := fun C D =>
    Subgroup.map_le_map_iff_of_injective e.injective
  constructor
  · rintro ⟨x, hx, y, hy, h1, h2, h3⟩
    refine ⟨e x, ⟨x, hx, rfl⟩, e y, ⟨y, hy, rfl⟩, ?_, ?_, ?_⟩
    · rw [← map_mul, mem_center_map_iff]
      exact h1
    · rw [← map_mul, ← map_centralizer_singleton, ← map_centralizer_singleton, hle]
      exact h2
    · rw [← map_mul, ← map_centralizer_singleton, ← Subgroup.map_commutator, h3]
  · rintro ⟨x', ⟨x, hx, rfl⟩, y', ⟨y, hy, rfl⟩, h1, h2, h3⟩
    simp only [MulEquiv.coe_toMonoidHom] at h1 h2 h3
    refine ⟨x, hx, y, hy, ?_, ?_, ?_⟩
    · rw [← map_mul, mem_center_map_iff] at h1
      exact h1
    · rw [← map_mul, ← map_centralizer_singleton, ← map_centralizer_singleton, hle] at h2
      exact h2
    · rw [← map_mul, ← map_centralizer_singleton, ← Subgroup.map_commutator] at h3
      exact Subgroup.map_injective e.injective h3

end Predicate

section Ambient

variable {Γ : Type*} [Group Γ]

theorem map_subtype_centralizer_singleton (M : Subgroup Γ) (d : M) :
    (Subgroup.centralizer ({d} : Set M)).map M.subtype =
      M ⊓ Subgroup.centralizer ({(d : Γ)} : Set Γ) := by
  ext g
  simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.coe_subtype]
  constructor
  · rintro ⟨g', hg', rfl⟩
    exact ⟨g'.2, congrArg Subtype.val hg'⟩
  · rintro ⟨hg, hc⟩
    exact ⟨⟨g, hg⟩, Subtype.ext hc, rfl⟩

theorem isAdaptedShortIn_iff_isAdaptedShort {M TA TB : Subgroup Γ} {zA : Γ} {S : Subgroup Γ}
    (hTA : TA ≤ M) (hTB : TB ≤ M) (hz : zA ∈ M) (hS : S ≤ M) :
    IsAdaptedShortIn M TA TB zA S ↔
      IsAdaptedShort (TA.subgroupOf M) (TB.subgroupOf M) (⟨zA, hz⟩ : M) (S.subgroupOf M) := by
  constructor
  · rintro ⟨x, hx, y, hy, h1, h2, h3⟩
    set x' : M := ⟨x, hTA hx⟩ with hx'
    set y' : M := ⟨y, hTB hy⟩ with hy'
    have hd : ((x' * y' : M) : Γ) = x * y := rfl
    have hmap := map_subtype_centralizer_singleton M (x' * y')
    rw [hd] at hmap
    refine ⟨x', hx, y', hy, ?_, ?_, ?_⟩
    · intro hc
      apply h1
      intro g hg
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hc ⟨g, hg⟩)
    · intro h
      apply h2
      intro g hg
      rw [← hmap] at hg
      obtain ⟨g', hg', rfl⟩ := Subgroup.mem_map.1 hg
      have := h hg'
      rw [Subgroup.mem_centralizer_singleton_iff] at this ⊢
      exact congrArg Subtype.val this
    · rw [h3, ← hmap, ← Subgroup.map_commutator]
      exact Subgroup.comap_map_eq_self_of_injective M.subtype_injective _
  · rintro ⟨x', hx, y', hy, h1, h2, h3⟩
    have hd : ((x' * y' : M) : Γ) = (x' : Γ) * (y' : Γ) := rfl
    have hmap := map_subtype_centralizer_singleton M (x' * y')
    rw [hd] at hmap
    refine ⟨x', hx, y', hy, ?_, ?_, ?_⟩
    · intro h
      apply h1
      rw [Subgroup.mem_center_iff]
      intro g
      refine Subtype.ext ?_
      exact Subgroup.mem_centralizer_singleton_iff.1 (h g.2)
    · intro h
      apply h2
      intro g' hg'
      have : (g' : Γ) ∈ M ⊓ Subgroup.centralizer ({(x' : Γ) * (y' : Γ)} : Set Γ) := by
        rw [← hmap]
        exact ⟨g', hg', rfl⟩
      have := h this
      rw [Subgroup.mem_centralizer_singleton_iff] at this ⊢
      exact Subtype.ext this
    · rw [← Subgroup.map_subgroupOf_eq_of_le hS, h3, Subgroup.map_commutator, hmap]

end Ambient

section Model

variable {K : Type} [Field K] {n : ℕ} {i j : Fin n}

theorem planeTorus_le {k : Fin n} (hk : k = i ∨ k = j) :
    planeTorus K n k ≤ suppGroup (coords i ∪ coords j) := by
  rintro _ ⟨u, -, rfl⟩
  rcases hk with rfl | rfl
  · exact suppGroup_mono Set.subset_union_left (isSupp_longBlock _ _)
  · exact suppGroup_mono Set.subset_union_right (isSupp_longBlock _ _)

theorem longInv_mem_suppGroup {k : Fin n} (hk : k = i ∨ k = j) :
    longInv K n k ∈ suppGroup (coords i ∪ coords j) := by
  rcases hk with rfl | rfl
  · exact suppGroup_mono Set.subset_union_left (isSupp_longBlock _ _)
  · exact suppGroup_mono Set.subset_union_right (isSupp_longBlock _ _)

theorem shortBlock_range_le (hij : i ≠ j) :
    (shortBlock K hij).range ≤ suppGroup (coords i ∪ coords j) := by
  rintro _ ⟨A, rfl⟩
  exact isSupp_shortBlock hij A

theorem shortGroupNeg_le (hij : i ≠ j) : shortGroupNeg K hij ≤ suppGroup (coords i ∪ coords j) := by
  rintro _ ⟨_, ⟨A, rfl⟩, rfl⟩
  exact mul_mem (mul_mem planeWeyl_mem (shortBlock_range_le hij ⟨A, rfl⟩)) (inv_mem planeWeyl_mem)

theorem subgroupOf_eq_iff {M S X : Subgroup (StatedSp n K)} (hS : S ≤ M) (hX : X ≤ M) :
    S.subgroupOf M = X.subgroupOf M ↔ S = X := by
  rw [Subgroup.subgroupOf_inj, inf_eq_left.2 hS, inf_eq_left.2 hX]

theorem isAdaptedShort_iff (hij : i ≠ j) (h2 : (2 : K) ≠ 0)
    (hex : ∃ a : Kˣ, (a : K) ≠ ((a⁻¹ : Kˣ) : K))
    (S : Subgroup (suppGroup (coords i ∪ coords j) : Subgroup (StatedSp n K))) :
    IsAdaptedShort ((planeTorus K n i).subgroupOf (suppGroup (coords i ∪ coords j)))
        ((planeTorus K n j).subgroupOf (suppGroup (coords i ∪ coords j)))
        (⟨longInv K n i, longInv_mem_suppGroup (Or.inl rfl)⟩ :
          (suppGroup (coords i ∪ coords j) : Subgroup (StatedSp n K))) S ↔
      S = (shortBlock K hij).range.subgroupOf (suppGroup (coords i ∪ coords j)) ∨
        S = (shortGroupNeg K hij).subgroupOf (suppGroup (coords i ∪ coords j)) := by
  have hS'le :
      S.map (suppGroup (coords i ∪ coords j)).subtype ≤ suppGroup (coords i ∪ coords j) := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hS' : (S.map (suppGroup (coords i ∪ coords j)).subtype).subgroupOf
      (suppGroup (coords i ∪ coords j)) = S :=
    Subgroup.comap_map_eq_self_of_injective (suppGroup (coords i ∪ coords j)).subtype_injective S
  have key := isAdaptedShortIn_iff_isAdaptedShort (planeTorus_le (Or.inl rfl))
    (planeTorus_le (Or.inr rfl)) (longInv_mem_suppGroup (Or.inl rfl)) hS'le
  rw [hS'] at key
  have e1 : S = (shortBlock K hij).range.subgroupOf (suppGroup (coords i ∪ coords j)) ↔
      S.map (suppGroup (coords i ∪ coords j)).subtype = (shortBlock K hij).range := by
    rw [← subgroupOf_eq_iff hS'le (shortBlock_range_le hij), hS']
  have e2 : S = (shortGroupNeg K hij).subgroupOf (suppGroup (coords i ∪ coords j)) ↔
      S.map (suppGroup (coords i ∪ coords j)).subtype = shortGroupNeg K hij := by
    rw [← subgroupOf_eq_iff hS'le (shortGroupNeg_le hij), hS']
  rw [← key, isAdaptedShortIn_iff hij h2 hex, e1, e2]

theorem isAdaptedShort_iff_of_mulEquiv {M : Type*} [Group M] (hij : i ≠ j) (h2 : (2 : K) ≠ 0)
    (hex : ∃ a : Kˣ, (a : K) ≠ ((a⁻¹ : Kˣ) : K))
    (e : (suppGroup (coords i ∪ coords j) : Subgroup (StatedSp n K)) ≃* M) {TA TB : Subgroup M}
    {zA : M}
    (hTA : ((planeTorus K n i).subgroupOf (suppGroup (coords i ∪ coords j))).map e.toMonoidHom = TA)
    (hTB : ((planeTorus K n j).subgroupOf (suppGroup (coords i ∪ coords j))).map e.toMonoidHom = TB)
    (hz : e ⟨longInv K n i, longInv_mem_suppGroup (Or.inl rfl)⟩ = zA) (S : Subgroup M) :
    IsAdaptedShort TA TB zA S ↔
      S = ((shortBlock K hij).range.subgroupOf (suppGroup (coords i ∪ coords j))).map
          e.toMonoidHom ∨
        S = ((shortGroupNeg K hij).subgroupOf (suppGroup (coords i ∪ coords j))).map
          e.toMonoidHom := by
  subst hTA hTB hz
  have hS : S = (S.map e.symm.toMonoidHom).map e.toMonoidHom := by
    rw [Subgroup.map_map]
    ext x
    simp
  rw [hS, ← isAdaptedShort_map_iff e, isAdaptedShort_iff hij h2 hex]
  have hinj : ∀ A B : Subgroup (suppGroup (coords i ∪ coords j) : Subgroup (StatedSp n K)),
      A.map e.toMonoidHom = B.map e.toMonoidHom ↔ A = B := fun A B =>
    ⟨fun h => Subgroup.map_injective e.injective h, fun h => h ▸ rfl⟩
  rw [hinj, hinj]

end Model

end CFSG.ClassicalInvolution.Models.SymplecticPairs
