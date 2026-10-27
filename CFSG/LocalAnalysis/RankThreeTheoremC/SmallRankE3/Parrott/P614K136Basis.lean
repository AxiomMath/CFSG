module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614K136Flag

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614K136

open CFSG.LieType.BorelTits CFSG.Open Subgroup Module
open scoped MatrixGroups

variable {F : Type*} [Field F] {K : Type*} [Group K]

theorem span_range_coe_basis {ι : Type*} (C : Submodule F (Fin 3 → F)) (cB : Basis ι F C) :
    Submodule.span F (Set.range fun i => (cB i : Fin 3 → F)) = C := by
  have : (Set.range fun i => (cB i : Fin 3 → F)) = C.subtype '' Set.range cB := by
    rw [← Set.range_comp]
    rfl
  rw [this, ← Submodule.map_span, cB.span_eq, Submodule.map_top, Submodule.range_subtype]

theorem linearIndependent_coe_basis {ι : Type*} (C : Submodule F (Fin 3 → F)) (cB : Basis ι F C) :
    LinearIndependent F fun i => (cB i : Fin 3 → F) :=
  cB.linearIndependent.map' C.subtype C.ker_subtype

theorem exists_not_mem_of_ne_top {C : Submodule F (Fin 3 → F)} (hC : C ≠ ⊤) :
    ∃ u : Fin 3 → F, u ∉ C := by
  by_contra h
  push Not at h
  exact hC (eq_top_iff.2 fun v _ => h v)

theorem exists_basis_plane (C : Submodule F (Fin 3 → F)) (hC : finrank F C = 2) :
    ∃ b : Basis (Fin 3) F (Fin 3 → F), ∀ w, w ∈ C ↔ b.repr w 0 = 0 := by
  let cB := Module.finBasisOfFinrankEq F C hC
  set v : Fin 2 → (Fin 3 → F) := fun i => (cB i : Fin 3 → F) with hv
  have hCtop : C ≠ ⊤ := by
    intro h
    rw [h, finrank_top] at hC
    simp at hC
  obtain ⟨u, hu⟩ := exists_not_mem_of_ne_top hCtop
  have hspan : Submodule.span F (Set.range v) = C := span_range_coe_basis C cB
  have hli : LinearIndependent F (Fin.cons u v : Fin 3 → (Fin 3 → F)) :=
    linearIndependent_fin_cons.2 ⟨linearIndependent_coe_basis C cB, hspan ▸ hu⟩
  let b := basisOfLinearIndependentOfCardEqFinrank hli (by simp)
  have hb : ⇑b = Fin.cons u v := coe_basisOfLinearIndependentOfCardEqFinrank hli _
  have hbs : ∀ i : Fin 2, b i.succ = v i := fun i => by rw [hb]; rfl
  refine ⟨b, fun w => ⟨fun hw => ?_, fun hw => ?_⟩⟩
  · have hle : C ≤ LinearMap.ker (b.coord 0) := by
      rw [← hspan, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, Basis.coord_apply, ← hbs i, b.repr_self,
        Finsupp.single_apply, if_neg (Fin.succ_ne_zero i)]
    have := hle hw
    rwa [LinearMap.mem_ker, Basis.coord_apply] at this
  · rw [← b.sum_repr w, Fin.sum_univ_succ, hw, zero_smul, zero_add]
    refine C.sum_mem fun i _ => C.smul_mem _ ?_
    rw [hbs i]
    exact (cB i).2

theorem exists_basis_line (C : Submodule F (Fin 3 → F)) (hC : finrank F C = 1) :
    ∃ b : Basis (Fin 3) F (Fin 3 → F), ∀ w, w ∈ C ↔ b.repr w 0 = 0 ∧ b.repr w 1 = 0 := by
  let cB := Module.finBasisOfFinrankEq F C hC
  set v : Fin 1 → (Fin 3 → F) := fun i => (cB i : Fin 3 → F) with hv
  have hCtop : C ≠ ⊤ := by
    intro h
    rw [h, finrank_top] at hC
    simp at hC
  obtain ⟨u₁, hu₁⟩ := exists_not_mem_of_ne_top hCtop
  have hspan : Submodule.span F (Set.range v) = C := span_range_coe_basis C cB
  have hli₁ : LinearIndependent F (Fin.cons u₁ v : Fin 2 → (Fin 3 → F)) :=
    linearIndependent_fin_cons.2 ⟨linearIndependent_coe_basis C cB, hspan ▸ hu₁⟩
  have hspan₂ : Submodule.span F (Set.range (Fin.cons u₁ v : Fin 2 → (Fin 3 → F))) ≠ ⊤ := by
    intro h
    have h1 := finrank_span_eq_card hli₁
    rw [h, finrank_top] at h1
    simp at h1
  obtain ⟨u₂, hu₂⟩ := exists_not_mem_of_ne_top hspan₂
  have hli : LinearIndependent F (Fin.cons u₂ (Fin.cons u₁ v) : Fin 3 → (Fin 3 → F)) :=
    linearIndependent_fin_cons.2 ⟨hli₁, hu₂⟩
  let b := basisOfLinearIndependentOfCardEqFinrank hli (by simp)
  have hb : ⇑b = Fin.cons u₂ (Fin.cons u₁ v) := coe_basisOfLinearIndependentOfCardEqFinrank hli _
  have hb2 : b 2 = v 0 := by rw [hb]; rfl
  refine ⟨b, fun w => ⟨fun hw => ?_, fun ⟨h0, h1⟩ => ?_⟩⟩
  · have hle : C ≤ LinearMap.ker (b.coord 0) ⊓ LinearMap.ker (b.coord 1) := by
      rw [← hspan, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      have hi : i = 0 := Subsingleton.elim i 0
      subst hi
      rw [SetLike.mem_coe, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.mem_ker,
        Basis.coord_apply, Basis.coord_apply, ← hb2, b.repr_self, Finsupp.single_apply,
        Finsupp.single_apply, if_neg (by decide), if_neg (by decide)]
      exact ⟨rfl, rfl⟩
    have := hle hw
    rw [Submodule.mem_inf, LinearMap.mem_ker, LinearMap.mem_ker, Basis.coord_apply,
      Basis.coord_apply] at this
    exact this
  · rw [← b.sum_repr w, Fin.sum_univ_three, h0, h1, zero_smul, zero_smul, zero_add, zero_add,
      hb2]
    exact C.smul_mem _ (cB 0).2

section Adapted

variable (σ : K ≃* SL(3, F)) (b : Basis (Fin 3) F (Fin 3 → F))

@[expose] noncomputable def adaptedHom : K →* SL(3, F) where
  toFun x := mkSL F (LinearMap.toMatrix b b (rep σ x)) (by rw [LinearMap.det_toMatrix, det_rep])
  map_one' := Subtype.ext (by rw [coe_mkSL, coe_SL_one, map_one, LinearMap.toMatrix_one])
  map_mul' x y := Subtype.ext (by
    rw [coe_SL_mul, coe_mkSL, coe_mkSL, coe_mkSL, map_mul, LinearMap.toMatrix_mul])

theorem coe_adaptedHom (x : K) :
    ((adaptedHom σ b x : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      LinearMap.toMatrix b b (rep σ x) := rfl

theorem adaptedHom_bijective : Function.Bijective (adaptedHom σ b) := by
  constructor
  · intro x y h
    have h' := congrArg (fun A : SL(3, F) => (A : Matrix (Fin 3) (Fin 3) F)) h
    simp only [coe_adaptedHom] at h'
    exact rep_injective σ ((LinearMap.toMatrix b b).injective h')
  · intro B
    set L := Matrix.toLin b b (B : Matrix (Fin 3) (Fin 3) F) with hL
    have hdet : (LinearMap.toMatrix' L).det = 1 := by
      rw [LinearMap.det_toMatrix', hL, LinearMap.det_toLin]
      exact B.2
    refine ⟨σ.symm (mkSL F (LinearMap.toMatrix' L) hdet), ?_⟩
    apply Subtype.ext
    change LinearMap.toMatrix b b (rep σ _) = _
    rw [rep_apply, MulEquiv.apply_symm_apply, coe_mkSL, Matrix.toLin'_toMatrix', hL,
      LinearMap.toMatrix_toLin]

@[expose] noncomputable def adaptedEquiv : K ≃* SL(3, F) :=
  MulEquiv.ofBijective (adaptedHom σ b) (adaptedHom_bijective σ b)

theorem coe_adaptedEquiv (x : K) :
    ((adaptedEquiv σ b x : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      LinearMap.toMatrix b b (rep σ x) := rfl

theorem repr_rep (x : K) (w : Fin 3 → F) (i : Fin 3) :
    b.repr (rep σ x w) i =
      ∑ j, (adaptedEquiv σ b x : Matrix (Fin 3) (Fin 3) F) i j * b.repr w j := by
  rw [coe_adaptedEquiv, ← LinearMap.toMatrix_mulVec_repr b b (rep σ x) w]
  rfl

theorem entry_adaptedEquiv (x : K) (i j : Fin 3) :
    (adaptedEquiv σ b x : Matrix (Fin 3) (Fin 3) F) i j = b.repr (rep σ x (b j)) i := by
  rw [coe_adaptedEquiv, LinearMap.toMatrix_apply]

theorem maps_plane_iff {C : Submodule F (Fin 3 → F)} (hb : ∀ w, w ∈ C ↔ b.repr w 0 = 0)
    (x : K) : (∀ v ∈ C, rep σ x v ∈ C) ↔ adaptedEquiv σ b x ∈ parA F := by
  have hb1 : b 1 ∈ C := (hb _).2 (by rw [b.repr_self, Finsupp.single_apply, if_neg (by decide)])
  have hb2 : b 2 ∈ C := (hb _).2 (by rw [b.repr_self, Finsupp.single_apply, if_neg (by decide)])
  rw [mem_parA]
  constructor
  · intro h
    rw [entry_adaptedEquiv, entry_adaptedEquiv]
    exact ⟨(hb _).1 (h _ hb1), (hb _).1 (h _ hb2)⟩
  · rintro ⟨h1, h2⟩ v hv
    rw [hb, repr_rep, Fin.sum_univ_three, h1, h2, (hb v).1 hv]
    ring

theorem maps_line_iff {C : Submodule F (Fin 3 → F)}
    (hb : ∀ w, w ∈ C ↔ b.repr w 0 = 0 ∧ b.repr w 1 = 0) (x : K) :
    (∀ v ∈ C, rep σ x v ∈ C) ↔ adaptedEquiv σ b x ∈ parB F := by
  have hb2 : b 2 ∈ C := (hb _).2 (by
    rw [b.repr_self, Finsupp.single_apply, Finsupp.single_apply, if_neg (by decide),
      if_neg (by decide)]
    exact ⟨rfl, rfl⟩)
  rw [mem_parB]
  constructor
  · intro h
    rw [entry_adaptedEquiv, entry_adaptedEquiv]
    exact (hb _).1 (h _ hb2)
  · rintro ⟨h1, h2⟩ v hv
    obtain ⟨hv0, hv1⟩ := (hb v).1 hv
    rw [hb, repr_rep, repr_rep, Fin.sum_univ_three, Fin.sum_univ_three, h1, h2, hv0, hv1]
    constructor <;> ring

end Adapted

theorem exists_parabolic [Finite F] [CharP F 2] [Finite K] (σ : K ≃* SL(3, F))
    {R : Subgroup K} (hR : IsPGroup 2 R) (hR1 : R ≠ ⊥) (hRi : 2 ∣ R.index)
    (hRc : pCoreOf 2 (normalizer (R : Set K)) = R) :
    (∃ τ : K ≃* SL(3, F), ∀ x, x ∈ normalizer (R : Set K) ↔ τ x ∈ parA F) ∨
      (∃ τ : K ≃* SL(3, F), ∀ x, x ∈ normalizer (R : Set K) ↔ τ x ∈ parB F) := by
  obtain ⟨C, hC, hN⟩ := exists_stab σ hR hR1 hRi hRc
  rcases hC with hC | hC
  · right
    obtain ⟨b, hb⟩ := exists_basis_line C hC
    refine ⟨adaptedEquiv σ b, fun x => ?_⟩
    rw [hN]
    constructor
    · intro h
      exact (maps_line_iff σ b hb x).1 fun v hv => (h v hv).1
    · intro h v hv
      refine ⟨(maps_line_iff σ b hb x).2 h v hv, (maps_line_iff σ b hb x⁻¹).2 ?_ v hv⟩
      rw [map_inv]
      exact inv_mem h
  · left
    obtain ⟨b, hb⟩ := exists_basis_plane C hC
    refine ⟨adaptedEquiv σ b, fun x => ?_⟩
    rw [hN]
    constructor
    · intro h
      exact (maps_plane_iff σ b hb x).1 fun v hv => (h v hv).1
    · intro h v hv
      refine ⟨(maps_plane_iff σ b hb x).2 h v hv, (maps_plane_iff σ b hb x⁻¹).2 ?_ v hv⟩
      rw [map_inv]
      exact inv_mem h

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614K136
