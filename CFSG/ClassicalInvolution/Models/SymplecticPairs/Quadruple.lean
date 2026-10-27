module

public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Intrinsic
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.ShortRoot

public section

namespace CFSG.ClassicalInvolution.Models.SymplecticPairs

open Matrix CFSG.Assembly.LowTwoRank
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open scoped MatrixGroups

variable {K : Type} [Field K] {m : ℕ}

section Standard

theorem planeGroup_std_four :
    planeGroup (Submodule.span K {(Pi.single (Sum.inl (0 : Fin (m + 1 + 1))) 1 :
        Fin (m + 1 + 1) ⊕ Fin (m + 1 + 1) → K), Pi.single (Sum.inr 0) 1, Pi.single (Sum.inl 1) 1,
      Pi.single (Sum.inr 1) 1}) = suppGroup (coords (0 : Fin (m + 1 + 1)) ∪ coords 1) := by
  have hS : ParClosed (coords (0 : Fin (m + 1 + 1)) ∪ coords 1) := by
    intro a ha
    rcases ha with ha | ha
    · exact Or.inl (parClosed_coords 0 a ha)
    · exact Or.inr (parClosed_coords 1 a ha)
  rw [planeGroup, ← fixing_supported_eq hS]
  congr 1
  ext v
  rw [Set.mem_ofPred_eq, mem_orthSet_span]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq,
    form_single_right, par_inl, par_inr, sgn_inl, sgn_inr]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩ t ht
    rcases ht with ht | ht
    · rcases mem_coords.1 ht with rfl | rfl
      · simpa using h2
      · simpa using h1
    · rcases mem_coords.1 ht with rfl | rfl
      · simpa using h4
      · simpa using h3
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [h _ (Or.inl (inr_mem_coords 0))]
    · simp [h _ (Or.inl (inl_mem_coords 0))]
    · simp [h _ (Or.inr (inr_mem_coords 1))]
    · simp [h _ (Or.inr (inl_mem_coords 1))]

end Standard

section Frame

theorem fin_zero_ne_one : (0 : Fin (m + 1 + 1)) ≠ 1 := fun h => by
  simpa using congrArg Fin.val h

structure IsSymplecticFrame (u₁ w₁ u₂ w₂ : Fin (m + 1 + 1) ⊕ Fin (m + 1 + 1) → K) : Prop where
  h₁ : form u₁ w₁ = 1
  h₂ : form u₂ w₂ = 1
  o₁ : form u₁ u₂ = 0
  o₂ : form u₁ w₂ = 0
  o₃ : form w₁ u₂ = 0
  o₄ : form w₁ w₂ = 0

@[expose] def CarriesFrame (g : StatedSp (m + 1 + 1) K)
    (u₁ w₁ u₂ w₂ : Fin (m + 1 + 1) ⊕ Fin (m + 1 + 1) → K) : Prop :=
  mat _ K g *ᵥ Pi.single (Sum.inl 0) 1 = u₁ ∧ mat _ K g *ᵥ Pi.single (Sum.inr 0) 1 = w₁ ∧
    mat _ K g *ᵥ Pi.single (Sum.inl 1) 1 = u₂ ∧ mat _ K g *ᵥ Pi.single (Sum.inr 1) 1 = w₂

variable {u₁ w₁ u₂ w₂ : Fin (m + 1 + 1) ⊕ Fin (m + 1 + 1) → K}

theorem IsSymplecticFrame.exists_carries (hq : IsSymplecticFrame u₁ w₁ u₂ w₂) :
    ∃ g : StatedSp (m + 1 + 1) K, CarriesFrame g u₁ w₁ u₂ w₂ :=
  exists_sp_apply_eq_two u₁ w₁ u₂ w₂ hq.h₁ hq.h₂ hq.o₁ hq.o₂ hq.o₃ hq.o₄

theorem CarriesFrame.inv_mul_mem {g g' : StatedSp (m + 1 + 1) K} (hg : CarriesFrame g u₁ w₁ u₂ w₂)
    (hg' : CarriesFrame g' u₁ w₁ u₂ w₂) :
    g⁻¹ * g' ∈ suppGroup (coords (0 : Fin (m + 1 + 1)) ∪ coords 1)ᶜ := by
  have hS : ParClosed (coords (0 : Fin (m + 1 + 1)) ∪ coords 1) := by
    intro a ha
    rcases ha with ha | ha
    · exact Or.inl (parClosed_coords 0 a ha)
    · exact Or.inr (parClosed_coords 1 a ha)
  have key : ∀ t : Fin (m + 1 + 1) ⊕ Fin (m + 1 + 1), ∀ u : Fin (m + 1 + 1) ⊕ Fin (m + 1 + 1) → K,
      mat _ K g *ᵥ Pi.single t 1 = u → mat _ K g' *ᵥ Pi.single t 1 = u →
        mat _ K (g⁻¹ * g') *ᵥ Pi.single t 1 = Pi.single t 1 := fun t u h h' => by
    rw [map_mul, ← Matrix.mulVec_mulVec, h']
    exact ((mulVec_eq_iff g _ _).1 h).symm
  rw [mem_suppGroup_iff hS.compl]
  intro t ht r
  have ht' : t ∈ coords (0 : Fin (m + 1 + 1)) ∪ coords 1 := by
    by_contra h'
    exact ht h'
  have hmv : mat _ K (g⁻¹ * g') *ᵥ Pi.single t 1 = Pi.single t 1 := by
    rcases ht' with ht' | ht'
    · rcases mem_coords.1 ht' with rfl | rfl
      · exact key _ _ hg.1 hg'.1
      · exact key _ _ hg.2.1 hg'.2.1
    · rcases mem_coords.1 ht' with rfl | rfl
      · exact key _ _ hg.2.2.1 hg'.2.2.1
      · exact key _ _ hg.2.2.2 hg'.2.2.2
  have := congrFun hmv r
  rw [mulVec_single_one_apply] at this
  rw [this, Pi.single_apply, Matrix.one_apply]

theorem CarriesFrame.map_range_shortBlock_eq {g g' : StatedSp (m + 1 + 1) K}
    (hg : CarriesFrame g u₁ w₁ u₂ w₂) (hg' : CarriesFrame g' u₁ w₁ u₂ w₂) :
    (shortBlock K (fin_zero_ne_one (m := m))).range.map (MulAut.conj g).toMonoidHom =
      (shortBlock K (fin_zero_ne_one (m := m))).range.map (MulAut.conj g').toMonoidHom := by
  have hh := hg.inv_mul_mem hg'
  have hc : ∀ s ∈ (shortBlock K (fin_zero_ne_one (m := m))).range,
      g' * s * g'⁻¹ = g * s * g⁻¹ := by
    rintro _ ⟨A, rfl⟩
    have hs : shortBlock K (fin_zero_ne_one (m := m)) A ∈
        suppGroup (coords (0 : Fin (m + 1 + 1)) ∪ coords 1) :=
      isSupp_shortBlock fin_zero_ne_one A
    have hcomm := (commute_suppGroup_compl hs hh).eq
    calc g' * shortBlock K fin_zero_ne_one A * g'⁻¹
        = g * ((g⁻¹ * g') * shortBlock K fin_zero_ne_one A * (g⁻¹ * g')⁻¹) * g⁻¹ := by group
      _ = g * (shortBlock K fin_zero_ne_one A) * g⁻¹ := by
        rw [← hcomm]
        group
  ext x
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s, hs, hc s hs⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s, hs, (hc s hs).symm⟩

theorem CarriesFrame.mulVec_conj_shortBlock {g : StatedSp (m + 1 + 1) K}
    (hg : CarriesFrame g u₁ w₁ u₂ w₂) (A : SL(2, K)) :
    mat _ K (g * shortBlock K (fin_zero_ne_one (m := m)) A * g⁻¹) *ᵥ u₁ =
        (A : Matrix (Fin 2) (Fin 2) K) 0 0 • u₁ + (A : Matrix (Fin 2) (Fin 2) K) 1 0 • u₂ ∧
      mat _ K (g * shortBlock K (fin_zero_ne_one (m := m)) A * g⁻¹) *ᵥ u₂ =
        (A : Matrix (Fin 2) (Fin 2) K) 0 1 • u₁ + (A : Matrix (Fin 2) (Fin 2) K) 1 1 • u₂ ∧
      mat _ K (g * shortBlock K (fin_zero_ne_one (m := m)) A * g⁻¹) *ᵥ w₁ =
        ((A⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 0 0 • w₁ +
          ((A⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 0 1 • w₂ ∧
      mat _ K (g * shortBlock K (fin_zero_ne_one (m := m)) A * g⁻¹) *ᵥ w₂ =
        ((A⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 1 0 • w₁ +
          ((A⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 1 1 • w₂ := by
  obtain ⟨h1, h2, h3, h4⟩ := hg
  have conjact : ∀ v : Fin (m + 1 + 1) ⊕ Fin (m + 1 + 1) → K,
      mat _ K (g * shortBlock K (fin_zero_ne_one (m := m)) A * g⁻¹) *ᵥ (mat _ K g *ᵥ v) =
        mat _ K g *ᵥ (mat _ K (shortBlock K (fin_zero_ne_one (m := m)) A) *ᵥ v) := fun v => by
    have e : mat _ K (g * shortBlock K (fin_zero_ne_one (m := m)) A * g⁻¹) *ᵥ (mat _ K g *ᵥ v) =
        mat _ K g *ᵥ (mat _ K (shortBlock K (fin_zero_ne_one (m := m)) A) *ᵥ
          (mat _ K g⁻¹ *ᵥ (mat _ K g *ᵥ v))) := by
      simp only [map_mul, Matrix.mulVec_mulVec, Matrix.mul_assoc]
    rw [e, mulVec_inv_mulVec]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← h1, conjact, shortBlock_mulVec_inl_left, Matrix.mulVec_add, Matrix.mulVec_smul,
      Matrix.mulVec_smul, h1, h3]
  · rw [← h3, conjact, shortBlock_mulVec_inl_right, Matrix.mulVec_add, Matrix.mulVec_smul,
      Matrix.mulVec_smul, h1, h3]
  · rw [← h2, conjact, shortBlock_mulVec_inr_left, Matrix.mulVec_add, Matrix.mulVec_smul,
      Matrix.mulVec_smul, h2, h4]
  · rw [← h4, conjact, shortBlock_mulVec_inr_right, Matrix.mulVec_add, Matrix.mulVec_smul,
      Matrix.mulVec_smul, h2, h4]

theorem CarriesFrame.planeGroup_pair_two {g : StatedSp (m + 1 + 1) K}
    (hg : CarriesFrame g u₁ w₁ u₂ w₂) :
    planeGroup (Submodule.span K {u₂, w₂}) =
      (longRootSp2 K (m + 1 + 1) 1).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨-, -, h3, h4⟩ := hg
  rw [← h3, ← h4, planeGroup_span_conj, ← planeGroup_stdPlane]
  rfl

theorem CarriesFrame.planeGroup_four {g : StatedSp (m + 1 + 1) K}
    (hg : CarriesFrame g u₁ w₁ u₂ w₂) :
    planeGroup (Submodule.span K {u₁, w₁, u₂, w₂}) =
      (suppGroup (coords (0 : Fin (m + 1 + 1)) ∪ coords 1)).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨h1, h2, h3, h4⟩ := hg
  rw [← planeGroup_std_four, ← planeGroup_map_conj, Submodule.map_span]
  simp only [Set.image_insert_eq, Set.image_singleton, Matrix.mulVecLin_apply, h1, h2, h3, h4]

theorem CarriesFrame.planeGroup_sup {g : StatedSp (m + 1 + 1) K}
    (hg : CarriesFrame g u₁ w₁ u₂ w₂) :
    planeGroup (Submodule.span K {u₂, w₂}) ⊔
        (shortBlock K (fin_zero_ne_one (m := m))).range.map (MulAut.conj g).toMonoidHom =
      planeGroup (Submodule.span K {u₁, w₁, u₂, w₂}) := by
  rw [hg.planeGroup_pair_two, hg.planeGroup_four, ← Subgroup.map_sup, sup_comm]
  exact congrArg _ (shortBlock_sup_longBlock_eq_suppGroup fin_zero_ne_one)

theorem CarriesFrame.symplecticBlockStandardPair {g : StatedSp (m + 1 + 1) K}
    (hg : CarriesFrame g u₁ w₁ u₂ w₂) :
    SymplecticBlockStandardPair K
      (planeGroup (Submodule.span K {u₂, w₂}) ⊔
        (shortBlock K (fin_zero_ne_one (m := m))).range.map (MulAut.conj g).toMonoidHom)
      (planeGroup (Submodule.span K {u₂, w₂}))
      ((shortBlock K (fin_zero_ne_one (m := m))).range.map (MulAut.conj g).toMonoidHom) := by
  rw [hg.planeGroup_pair_two, ← Subgroup.map_sup]
  exact symplecticBlockStandardPair_conj fin_zero_ne_one g

@[expose] noncomputable def shortRootGroup (hq : IsSymplecticFrame u₁ w₁ u₂ w₂) :
    Subgroup (StatedSp (m + 1 + 1) K) :=
  (shortBlock K (fin_zero_ne_one (m := m))).range.map
    (MulAut.conj hq.exists_carries.choose).toMonoidHom

theorem shortRootGroup_eq (hq : IsSymplecticFrame u₁ w₁ u₂ w₂) {g : StatedSp (m + 1 + 1) K}
    (hg : CarriesFrame g u₁ w₁ u₂ w₂) :
    shortRootGroup hq =
      (shortBlock K (fin_zero_ne_one (m := m))).range.map (MulAut.conj g).toMonoidHom :=
  hq.exists_carries.choose_spec.map_range_shortBlock_eq hg

theorem IsSymplecticFrame.planeGroup_sup_shortRootGroup (hq : IsSymplecticFrame u₁ w₁ u₂ w₂) :
    planeGroup (Submodule.span K {u₂, w₂}) ⊔ shortRootGroup hq =
      planeGroup (Submodule.span K {u₁, w₁, u₂, w₂}) ∧
    SymplecticBlockStandardPair K (planeGroup (Submodule.span K {u₂, w₂}) ⊔ shortRootGroup hq)
      (planeGroup (Submodule.span K {u₂, w₂})) (shortRootGroup hq) := by
  rw [shortRootGroup_eq hq hq.exists_carries.choose_spec]
  exact ⟨hq.exists_carries.choose_spec.planeGroup_sup,
    hq.exists_carries.choose_spec.symplecticBlockStandardPair⟩

end Frame

end CFSG.ClassicalInvolution.Models.SymplecticPairs
