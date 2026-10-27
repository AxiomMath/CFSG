module

public import CFSG.GH74.GLS.IVK.Statements.Sec4
public import CFSG.GH74.GLS.IVK.L2.Lemma13f
public import CFSG.RankThree.CentralCover.LinearUnitaryFourGroupWitness
public import CFSG.RankThree.PartOne.KC.OrthogonalMatrixModelTransport
public import CFSG.GH74.GLS.Stage1.Thm6.Prod.Resid

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG.GH74.GLS.IVK CFSG.GorensteinWalter CFSG.Assembly.LowTwoRank
  CFSG.RankThree.CentralCover

section Std44Defs

variable (F : Type) [Field F]

@[expose] noncomputable def linU₀ : StatedProj (StatedSL 3 F) :=
  statedProjMk (StatedSL 3 F) ⟨oddDiag₃ F, Subgroup.subset_closure (det_oddDiag₃ F)⟩

@[expose] noncomputable def linU₀' : StatedProj (StatedSL 3 F) :=
  statedProjMk (StatedSL 3 F) ⟨oddDiag₂ F, Subgroup.subset_closure (det_oddDiag₂ F)⟩

variable {q : ℕ}

@[expose] noncomputable def uniU₀ (hq : Odd q) : StatedProj (StatedSU 3 q F) :=
  statedProjMk (StatedSU 3 q F)
    ⟨oddDiag₃ F, Subgroup.subset_closure ⟨det_oddDiag₃ F, unitary_oddDiag₃ hq⟩⟩

@[expose] noncomputable def uniU₀' (hq : Odd q) : StatedProj (StatedSU 3 q F) :=
  statedProjMk (StatedSU 3 q F)
    ⟨oddDiag₂ F, Subgroup.subset_closure ⟨det_oddDiag₂ F, unitary_oddDiag₂ hq⟩⟩

end Std44Defs

section Targets

@[expose] def LinConj (F : Type) [Field F] : Prop :=
  ∀ v v' : StatedProj (StatedSL 3 F), orderOf v = 2 → orderOf v' = 2 → v ≠ v' → v * v' = v' * v →
    ∃ g : StatedProj (StatedSL 3 F), g * v * g⁻¹ = linU₀ F ∧ g * v' * g⁻¹ = linU₀' F

@[expose] def LinGen (F : Type) [Field F] : Prop :=
  (3 < Nat.card F → Subgroup.closure
      ((Ez (linU₀ F) : Set (StatedProj (StatedSL 3 F))) ∪ (Ez (linU₀' F) : Set _)) = ⊤) ∧
  (Nat.card F = 3 → Subgroup.closure
      ((O2z (linU₀ F) : Set (StatedProj (StatedSL 3 F))) ∪ (O2z (linU₀' F) : Set _)) = ⊤)

@[expose] def UniConj (F : Type) [Field F] {q : ℕ} (hq : Odd q) : Prop :=
  ∀ v v' : StatedProj (StatedSU 3 q F), orderOf v = 2 → orderOf v' = 2 → v ≠ v' → v * v' = v' * v →
    ∃ g : StatedProj (StatedSU 3 q F), g * v * g⁻¹ = uniU₀ F hq ∧ g * v' * g⁻¹ = uniU₀' F hq

@[expose] def UniGen (F : Type) [Field F] {q : ℕ} (hq : Odd q) : Prop :=
  (3 < q → Subgroup.closure
      ((Ez (uniU₀ F hq) : Set (StatedProj (StatedSU 3 q F))) ∪ (Ez (uniU₀' F hq) : Set _)) = ⊤) ∧
  (q = 3 → Subgroup.closure
      ((O2z (uniU₀ F hq) : Set (StatedProj (StatedSU 3 q F))) ∪ (O2z (uniU₀' F hq) : Set _)) = ⊤)

end Targets

section Reduction

variable {K X : Type} [Group K] [Group X]

@[expose] noncomputable def centralizerEquiv (φ : K ≃* X) (u : K) :
    ↥(centralizer ({u} : Set K)) ≃* ↥(centralizer ({φ u} : Set X)) :=
  (φ.subgroupMap (centralizer ({u} : Set K))).trans (MulEquiv.subgroupCongr (by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : y ∈ centralizer ({u} : Set K) := hy
      rw [Subgroup.mem_centralizer_singleton_iff] at hy'
      show φ y ∈ centralizer ({φ u} : Set X)
      rw [Subgroup.mem_centralizer_singleton_iff]
      rw [← map_mul, ← map_mul, hy']
    · intro hx
      have hx' : x ∈ centralizer ({φ u} : Set X) := hx
      rw [Subgroup.mem_centralizer_singleton_iff] at hx'
      refine ⟨φ.symm x, ?_, φ.apply_symm_apply x⟩
      show φ.symm x ∈ centralizer ({u} : Set K)
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply φ.injective
      rw [map_mul, map_mul, φ.apply_symm_apply]
      exact hx'))

theorem centralizerEquiv_coe (φ : K ≃* X) (u : K) (y : ↥(centralizer ({u} : Set K))) :
    ((centralizerEquiv φ u y : ↥(centralizer ({φ u} : Set X))) : X) = φ (y : K) := rfl

theorem comp_centralizerEquiv (φ : K ≃* X) (u : K) :
    φ.toMonoidHom.comp (centralizer ({u} : Set K)).subtype =
      (centralizer ({φ u} : Set X)).subtype.comp (centralizerEquiv φ u).toMonoidHom := by
  ext y
  rfl

theorem Ez_map (φ : K ≃* X) (u : K) : (Ez u).map φ.toMonoidHom = Ez (φ u) := by
  unfold Ez
  rw [Subgroup.map_map, comp_centralizerEquiv, ← Subgroup.map_map,
    CFSG.RankThree.PartOne.KCOrthogonalModel.layer_map_mulEquiv (centralizerEquiv φ u)]

theorem O2z_map [Finite K] (φ : K ≃* X) (u : K) : (O2z u).map φ.toMonoidHom = O2z (φ u) := by
  unfold O2z
  rw [Subgroup.map_map, comp_centralizerEquiv, ← Subgroup.map_map,
    CFSG.GH74.GLS.Stage1.Thm6.Prod.map_oResidual (centralizerEquiv φ u).toMonoidHom (centralizerEquiv φ u).surjective Nat.prime_two]


theorem closure_union_eq_top_of_map (φ : K ≃* X) (A B : Subgroup K) (A' B' : Subgroup X)
    (hA : A.map φ.toMonoidHom = A') (hB : B.map φ.toMonoidHom = B')
    (h : Subgroup.closure ((A' : Set X) ∪ (B' : Set X)) = ⊤) :
    Subgroup.closure ((A : Set K) ∪ (B : Set K)) = ⊤ := by
  have h1 : (Subgroup.closure ((A : Set K) ∪ (B : Set K))).map φ.toMonoidHom = ⊤ := by
    rw [MonoidHom.map_closure, Set.image_union, ← Subgroup.coe_map, ← Subgroup.coe_map, hA, hB]
    exact h
  rw [← Subgroup.comap_map_eq_self_of_injective (f := φ.toMonoidHom) φ.injective
    (Subgroup.closure ((A : Set K) ∪ (B : Set K))), h1, Subgroup.comap_top]

theorem exists_iso_pair (e : K ≃* X) (u₀ u₀' : X)
    (hconj : ∀ v v' : X, orderOf v = 2 → orderOf v' = 2 → v ≠ v' → v * v' = v' * v →
      ∃ g : X, g * v * g⁻¹ = u₀ ∧ g * v' * g⁻¹ = u₀')
    {U : Subgroup K} (hU : IsFourSubgroup U) {u u' : K} (hu : u ∈ U) (hu' : u' ∈ U)
    (hu2 : orderOf u = 2) (hu2' : orderOf u' = 2) (hne : u ≠ u') :
    ∃ φ : K ≃* X, φ u = u₀ ∧ φ u' = u₀' := by
  obtain ⟨hcomm, -⟩ := isFourSubgroup_props hU
  have hc : u * u' = u' * u := hcomm u hu u' hu'
  have h1 : orderOf (e u) = 2 := by rw [MulEquiv.orderOf_eq]; exact hu2
  have h2 : orderOf (e u') = 2 := by rw [MulEquiv.orderOf_eq]; exact hu2'
  have h3 : e u ≠ e u' := fun h => hne (e.injective h)
  have h4 : e u * e u' = e u' * e u := by rw [← map_mul, ← map_mul, hc]
  obtain ⟨g, hg1, hg2⟩ := hconj _ _ h1 h2 h3 h4
  refine ⟨e.trans (MulAut.conj g), ?_, ?_⟩
  · simpa [MulAut.conj_apply] using hg1
  · simpa [MulAut.conj_apply] using hg2

theorem ivk_4_4a_of_std [Finite K] (e : K ≃* X) (u₀ u₀' : X) (q : ℕ)
    (hconj : ∀ v v' : X, orderOf v = 2 → orderOf v' = 2 → v ≠ v' → v * v' = v' * v →
      ∃ g : X, g * v * g⁻¹ = u₀ ∧ g * v' * g⁻¹ = u₀')
    (hE : 3 < q → Subgroup.closure ((Ez u₀ : Set X) ∪ (Ez u₀' : Set X)) = ⊤)
    (hO : q = 3 → Subgroup.closure ((O2z u₀ : Set X) ∪ (O2z u₀' : Set X)) = ⊤)
    {U : Subgroup K} (hU : IsFourSubgroup U) {u u' : K} (hu : u ∈ U) (hu' : u' ∈ U)
    (hu2 : orderOf u = 2) (hu2' : orderOf u' = 2) (hne : u ≠ u') :
    (3 < q → Subgroup.closure ((Ez u : Set K) ∪ (Ez u' : Set K)) = ⊤) ∧
    (q = 3 → Subgroup.closure ((O2z u : Set K) ∪ (O2z u' : Set K)) = ⊤) := by
  obtain ⟨φ, hφ1, hφ2⟩ := exists_iso_pair e u₀ u₀' hconj hU hu hu' hu2 hu2' hne
  refine ⟨fun hq => closure_union_eq_top_of_map φ _ _ _ _ ?_ ?_ (hE hq),
    fun hq => closure_union_eq_top_of_map φ _ _ _ _ ?_ ?_ (hO hq)⟩
  · rw [Ez_map, hφ1]
  · rw [Ez_map, hφ2]
  · rw [O2z_map, hφ1]
  · rw [O2z_map, hφ2]

end Reduction

section Assembly

theorem ivk_4_4a_of_targets
    (hLC : ∀ (F : Type) [Field F] [Finite F], Odd (Nat.card F) → LinConj F)
    (hLG : ∀ (F : Type) [Field F] [Finite F], Odd (Nat.card F) → LinGen F)
    (hUC : ∀ (F : Type) [Field F] [Finite F] {q : ℕ} (hq : Odd q), Nat.card F = q ^ 2 → UniConj F hq)
    (hUG : ∀ (F : Type) [Field F] [Finite F] {q : ℕ} (hq : Odd q), Nat.card F = q ^ 2 → UniGen F hq) :
    IVK_4_4a := by
  intro K _ _ ε p n hp hp2 hK U hU u hu u' hu' hu2 hu2' hne
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hqodd : Odd (p ^ n) := hpodd.pow
  rcases hK with ⟨-, F, _, _, hF, ⟨e⟩⟩ | ⟨-, F, _, _, hF, ⟨e⟩⟩
  · have hodd : Odd (Nat.card F) := hF ▸ hqodd
    have := ivk_4_4a_of_std e (linU₀ F) (linU₀' F) (p ^ n) (hLC F hodd)
      (by rw [← hF]; exact (hLG F hodd).1) (by rw [← hF]; exact (hLG F hodd).2) hU hu hu' hu2 hu2' hne
    exact this
  · have := ivk_4_4a_of_std e (uniU₀ F hqodd) (uniU₀' F hqodd) (p ^ n) (hUC F hqodd hF)
      (hUG F hqodd hF).1 (hUG F hqodd hF).2 hU hu hu' hu2 hu2' hne
    exact this

end Assembly

end CFSG.GH74.GLS.IVK.Proofs2
