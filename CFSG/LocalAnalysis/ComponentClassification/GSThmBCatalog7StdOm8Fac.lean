module

public import CFSG.LocalAnalysis.ComponentInitial.LocalBMaximalPropagation
public import CFSG.ClassicalInvolution.Orders.OrthogonalIndex
public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorOrthWitness
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorOrthogonal

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB.Catalog7Std.Om8

open CFSG Subgroup Module QuadraticMap CFSG.ClassicalGroups.Orthogonal

section Product

variable {X Y : Type*} [Group X] [Group Y]

theorem pComponent_map_injective_normal [Finite Y] (φ : X →* Y) (hφ : Function.Injective φ)
    [φ.range.Normal] {L : Subgroup X} (hL : IsPComponent 2 L) : IsPComponent 2 (L.map φ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set e := MonoidHom.ofInjective hφ
  have h1 := CatalogueBAlternating.pComponent_of_normal_subgroup 2 φ.range (L.map e.toMonoidHom)
    (CatalogueBAlternating.pComponent_map_equiv 2 e L hL)
  have h2 : (L.map e.toMonoidHom).map φ.range.subtype = L.map φ := by
    rw [map_map]
    rfl
  rwa [h2] at h1

theorem map_inl_eq_prod_bot (L : Subgroup X) :
    L.map (MonoidHom.inl X Y) = L.prod (⊥ : Subgroup Y) := by
  ext ⟨x, y⟩
  constructor
  · rintro ⟨l, hl, h⟩
    simp only [MonoidHom.inl_apply, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hl, Subgroup.one_mem _⟩
  · rintro ⟨hx, hy⟩
    refine ⟨x, hx, ?_⟩
    simp only [MonoidHom.inl_apply, Prod.mk.injEq, true_and]
    exact ((Subgroup.mem_bot).mp hy).symm

theorem map_inr_eq_bot_prod (L : Subgroup Y) :
    L.map (MonoidHom.inr X Y) = (⊥ : Subgroup X).prod L := by
  ext ⟨x, y⟩
  constructor
  · rintro ⟨l, hl, h⟩
    simp only [MonoidHom.inr_apply, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨Subgroup.one_mem _, hl⟩
  · rintro ⟨hx, hy⟩
    refine ⟨y, hy, ?_⟩
    simp only [MonoidHom.inr_apply, Prod.mk.injEq, and_true]
    exact ((Subgroup.mem_bot).mp hx).symm

theorem inl_range_normal : (MonoidHom.inl X Y).range.Normal := by
  constructor
  rintro _ ⟨x, rfl⟩ ⟨a, b⟩
  exact ⟨a * x * a⁻¹, by simp⟩

theorem inr_range_normal : (MonoidHom.inr X Y).range.Normal := by
  constructor
  rintro _ ⟨y, rfl⟩ ⟨a, b⟩
  exact ⟨b * y * b⁻¹, by simp⟩

variable [Finite X] [Finite Y]

theorem isPComponent_prod_bot {L : Subgroup X} (hL : IsPComponent 2 L) :
    IsPComponent 2 (L.prod (⊥ : Subgroup Y)) := by
  have := inl_range_normal (X := X) (Y := Y)
  have h := pComponent_map_injective_normal (MonoidHom.inl X Y)
    (fun _ _ h => (Prod.ext_iff.mp h).1) hL
  rwa [map_inl_eq_prod_bot] at h

theorem isPComponent_bot_prod {L : Subgroup Y} (hL : IsPComponent 2 L) :
    IsPComponent 2 ((⊥ : Subgroup X).prod L) := by
  have := inr_range_normal (X := X) (Y := Y)
  have h := pComponent_map_injective_normal (MonoidHom.inr X Y)
    (fun _ _ h => (Prod.ext_iff.mp h).2) hL
  rwa [map_inr_eq_bot_prod] at h

end Product

section Orthogonal

variable {K W : Type} [Field K] [Finite K] [AddCommGroup W] [Module K W] [FiniteDimensional K W]

theorem isPComponent_commutator {Q : QuadraticForm K W}
    (hq : IsQuasisimple (commutator (TauCeti.QuadraticMap.orthogonalGroup Q))) :
    IsPComponent 2 (commutator (TauCeti.QuadraticMap.orthogonalGroup Q)) :=
  LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent
    ⟨hq, (inferInstance : (commutator (TauCeti.QuadraticMap.orthogonalGroup Q)).Normal).isSubnormal⟩

open LocalAnalysis.ComponentInitial CatalogueBOrthogonalFourSplit in
theorem exists_pComponent_split_four (hodd : Odd (Nat.card K)) (hK3 : Nat.card K ≠ 3)
    {Q : QuadraticForm K W} (hQ : Q.polarBilin.Nondegenerate) (hdim : finrank K W = 4)
    (hS : ∃ S : Submodule K W, finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0) :
    ∃ L : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q), IsPComponent 2 L := by
  have hK2 : Nat.card K ≠ 2 := fun h => absurd (h ▸ hodd) (by decide)
  obtain ⟨-, e', -, -, hsup, hq₁, -, hn₁, -, -, -, -⟩ :=
    orthogonal_split_four_derived hK2 hK3 Q hQ hdim hS
  set L := (determinantLeftFactor K).map e'.symm.toMonoidHom
  have hLD : L ≤ commutator (TauCeti.QuadraticMap.orthogonalGroup Q) := hsup ▸ le_sup_left
  have hsub : L.IsSubnormal :=
    Subgroup.IsSubnormal.trans hLD hn₁.isSubnormal
      (inferInstance : (commutator (TauCeti.QuadraticMap.orthogonalGroup Q)).Normal).isSubnormal
  exact ⟨L, LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent ⟨hq₁, hsub⟩⟩

open LocalAnalysis.ComponentInitial in
theorem exists_pComponent_of_dim (hodd : Odd (Nat.card K)) {Q : QuadraticForm K W}
    (hQ : Q.polarBilin.Nondegenerate)
    (hdim : finrank K W = 5 ∨ (finrank K W = 4 ∧ Nat.card K ≠ 3) ∨
      (finrank K W = 4 ∧ ¬ ∃ S : Submodule K W, finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0)) :
    ∃ L : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q), IsPComponent 2 L := by
  rcases hdim with h5 | ⟨h4, hK3⟩ | ⟨h4, hno⟩
  · exact ⟨_, isPComponent_commutator
      (OddSelector.commutator_orthogonalGroup_quasisimple hodd Q hQ (by omega))⟩
  · by_cases hS : ∃ S : Submodule K W, finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0
    · exact exists_pComponent_split_four hodd hK3 hQ h4 hS
    · obtain ⟨-, -, -, -, -, -, -, -, hq, -⟩ := orthogonal_nonsplit_four_derived hodd Q hQ h4 hS
      exact ⟨_, isPComponent_commutator hq⟩
  · obtain ⟨-, -, -, -, -, -, -, -, hq, -⟩ := orthogonal_nonsplit_four_derived hodd Q hQ h4 hno
    exact ⟨_, isPComponent_commutator hq⟩

omit [Finite K] [FiniteDimensional K W] in
theorem reflect_mul_reflect_mem_commutator (h2 : (2 : K) ≠ 0) {Q : QuadraticForm K W}
    {u v : W} (hu : Q u = 1) (hv : Q v = 1) :
    (⟨reflect Q u * reflect Q v, mul_mem (reflect_mem_orthogonalGroup Q u)
      (reflect_mem_orthogonalGroup Q v)⟩ : TauCeti.QuadraticMap.orthogonalGroup Q) ∈
      commutator (TauCeti.QuadraticMap.orthogonalGroup Q) := by
  have h := OddClassSelector.reflect_mul_reflect_mem h2 (by rw [hu]; exact one_ne_zero)
    (by rw [hv]; exact one_ne_zero) ⟨1, by rw [hu, hv]⟩
  rw [← Subgroup.map_subtype_commutator] at h
  obtain ⟨x, hx, hxv⟩ := h
  have hx' : x = ⟨reflect Q u * reflect Q v, mul_mem (reflect_mem_orthogonalGroup Q u)
      (reflect_mem_orthogonalGroup Q v)⟩ := Subtype.ext hxv
  rw [← hx']
  exact hx

theorem exists_unit_orthogonal_basis (hodd : Odd (Nat.card K)) {Q : QuadraticForm K W}
    (hQ : Q.polarBilin.Nondegenerate) (hd : 2 ≤ finrank K W) :
    ∃ e : Basis (Fin (finrank K W)) K W, (∀ i j, i ≠ j → polar Q (e i) (e j) = 0) ∧
      ∀ i : Fin (finrank K W), (i : ℕ) < finrank K W - 1 → Q (e i) = 1 := by
  have h2 : (2 : K) ≠ 0 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  have hsymm : LinearMap.BilinForm.IsSymm Q.polarBilin :=
    ⟨fun x y => QuadraticMap.polar_comm Q x y⟩
  obtain ⟨hval, hbas⟩ :=
    LocalAnalysis.ComponentInitial.finite_odd_symmetric_equal_value_orthogonal_basis
      hodd rfl hd hQ hsymm
  obtain ⟨m0, hm0⟩ := hval 2 h2
  obtain ⟨e, heo, -, hea, -⟩ := hbas 2 m0 h2 hm0
  refine ⟨e, fun i j hij => heo hij, fun i hi => ?_⟩
  have h := hea i hi
  change polar Q (e i) (e i) = 2 at h
  rw [OddClassSelector.polar_self_eq] at h
  exact mul_left_cancel₀ h2 (h.trans (mul_one 2).symm)

end Orthogonal

end CFSG.ComponentClassification.GSThmB.Catalog7Std.Om8
