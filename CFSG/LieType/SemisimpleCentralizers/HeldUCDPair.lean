module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LieType.SemisimpleCentralizers.HeldUCDKBlock
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentInitial.CoprimeFixedCommutator

public section

open CFSG.LocalAnalysis.ComponentInitial

namespace CFSG.LieType.SemisimpleCentralizers.HeldUCD

open Matrix Polynomial

open scoped _root_.Classical

variable {L : Type} [Field L] {n : ℕ}

@[expose] noncomputable def adjL (τ : L ≃+* L) (T : (Fin n → L) →ₗ[L] (Fin n → L)) :
    (Fin n → L) →ₗ[L] (Fin n → L) :=
  Matrix.toLin' (adjM τ (LinearMap.toMatrix' T))

theorem hfm_adjL (τ : L ≃+* L) (T : (Fin n → L) →ₗ[L] (Fin n → L)) (x y : Fin n → L) :
    hfm τ (T x) y = hfm τ x (adjL τ T y) := by
  have h := hfm_mulVec τ (LinearMap.toMatrix' T) x y
  rw [LinearMap.toMatrix'_mulVec] at h
  rw [adjL, Matrix.toLin'_apply]
  exact h

theorem adjL_comp (τ : L ≃+* L) (S T : (Fin n → L) →ₗ[L] (Fin n → L)) :
    adjL τ (S ∘ₗ T) = adjL τ T ∘ₗ adjL τ S := by
  rw [adjL, adjL, adjL, LinearMap.toMatrix'_comp, adjM_mul, Matrix.toLin'_mul]

theorem adjL_id (τ : L ≃+* L) : adjL τ (LinearMap.id : (Fin n → L) →ₗ[L] (Fin n → L)) = LinearMap.id := by
  rw [adjL, LinearMap.toMatrix'_id, adjM_one, Matrix.toLin'_one]

section Ext

variable {τ : L ≃+* L} {m : ℕ} {s : Matrix (Fin n) (Fin n) L} {F : Finset L[X]}
  {a b : L[X] → L[X]} {f : L[X]}

@[expose] noncomputable def prjV (s : Matrix (Fin n) (Fin n) L) (b : L[X] → L[X])
    (F : Finset L[X]) (f : L[X])
    (hP : ∀ x : Fin n → L, Pmat s b F f *ᵥ (Pmat s b F f *ᵥ x) = Pmat s b F f *ᵥ x) :
    (Fin n → L) →ₗ[L] Vf s b F f :=
  LinearMap.codRestrict (Vf s b F f) (Matrix.toLin' (Pmat s b F f)) (fun x => mem_Vf.mpr (hP x))

theorem coe_prjV (hP : ∀ x : Fin n → L, Pmat s b F f *ᵥ (Pmat s b F f *ᵥ x) = Pmat s b F f *ᵥ x)
    (x : Fin n → L) : ((prjV s b F f hP x : Vf s b F f) : Fin n → L) = Pmat s b F f *ᵥ x := rfl

theorem prjV_incl (hP : ∀ x : Fin n → L, Pmat s b F f *ᵥ (Pmat s b F f *ᵥ x) = Pmat s b F f *ᵥ x)
    (y : Vf s b F f) : prjV s b F f hP (y : Fin n → L) = y := by
  apply Subtype.ext
  rw [coe_prjV]
  exact mem_Vf.mp y.2

@[expose] noncomputable def Eext (s : Matrix (Fin n) (Fin n) L) (b : L[X] → L[X])
    (F : Finset L[X]) (f : L[X])
    (hP : ∀ x : Fin n → L, Pmat s b F f *ᵥ (Pmat s b F f *ᵥ x) = Pmat s b F f *ᵥ x)
    (a : Vf s b F f →ₗ[L] Vf s b F f) : (Fin n → L) →ₗ[L] (Fin n → L) :=
  ((Vf s b F f).subtype ∘ₗ a ∘ₗ prjV s b F f hP) + (LinearMap.id - Matrix.toLin' (Pmat s b F f))

theorem Eext_apply (hP : ∀ x : Fin n → L, Pmat s b F f *ᵥ (Pmat s b F f *ᵥ x) = Pmat s b F f *ᵥ x)
    (a : Vf s b F f →ₗ[L] Vf s b F f) (x : Fin n → L) :
    Eext s b F f hP a x = (a (prjV s b F f hP x) : Fin n → L) + (x - Pmat s b F f *ᵥ x) := by
  simp only [Eext, LinearMap.add_apply, LinearMap.comp_apply, Submodule.subtype_apply,
    LinearMap.sub_apply, LinearMap.id_apply, Matrix.toLin'_apply]

theorem Eext_mem (hP : ∀ x : Fin n → L, Pmat s b F f *ᵥ (Pmat s b F f *ᵥ x) = Pmat s b F f *ᵥ x)
    (a : Vf s b F f →ₗ[L] Vf s b F f) (y : Vf s b F f) :
    Eext s b F f hP a (y : Fin n → L) = (a y : Fin n → L) := by
  rw [Eext_apply, prjV_incl, mem_Vf.mp y.2, sub_self, add_zero]

theorem Eext_one (hP : ∀ x : Fin n → L, Pmat s b F f *ᵥ (Pmat s b F f *ᵥ x) = Pmat s b F f *ᵥ x)
    (x : Fin n → L) : Eext s b F f hP LinearMap.id x = x := by
  rw [Eext_apply, LinearMap.id_apply, coe_prjV, add_sub_cancel]

theorem Eext_comp (hP : ∀ x : Fin n → L, Pmat s b F f *ᵥ (Pmat s b F f *ᵥ x) = Pmat s b F f *ᵥ x)
    (a a' : Vf s b F f →ₗ[L] Vf s b F f) (x : Fin n → L) :
    Eext s b F f hP (a ∘ₗ a') x = Eext s b F f hP a (Eext s b F f hP a' x) := by
  have hy := Eext_apply hP a' x
  have hPy : Pmat s b F f *ᵥ (Eext s b F f hP a' x) =
      (a' (prjV s b F f hP x) : Fin n → L) := by
    rw [hy, Matrix.mulVec_add, mem_Vf.mp (a' (prjV s b F f hP x)).2, Matrix.mulVec_sub, hP,
      sub_self, add_zero]
  have hprj : prjV s b F f hP (Eext s b F f hP a' x) = a' (prjV s b F f hP x) := by
    apply Subtype.ext
    rw [coe_prjV, hPy]
  rw [Eext_apply hP (a ∘ₗ a') x, Eext_apply hP a (Eext s b F f hP a' x), hprj, hPy, hy,
    add_sub_cancel_left, LinearMap.comp_apply]

theorem Eext_comm_P (hP : ∀ x : Fin n → L, Pmat s b F f *ᵥ (Pmat s b F f *ᵥ x) = Pmat s b F f *ᵥ x)
    (a : Vf s b F f →ₗ[L] Vf s b F f) (x : Fin n → L) :
    Pmat s b F f *ᵥ Eext s b F f hP a x = Eext s b F f hP a (Pmat s b F f *ᵥ x) := by
  have hPy := Eext_apply hP a x
  rw [hPy, Matrix.mulVec_add, mem_Vf.mp (a (prjV s b F f hP x)).2, Matrix.mulVec_sub, hP, sub_self,
    add_zero, Eext_apply hP a (Pmat s b F f *ᵥ x)]
  have hprj : prjV s b F f hP (Pmat s b F f *ᵥ x) = prjV s b F f hP x := by
    apply Subtype.ext
    rw [coe_prjV, coe_prjV, hP]
  rw [hprj, hP, sub_self, add_zero]

theorem Pmat_mul_s : Pmat s b F f * s = s * Pmat s b F f := by
  rw [Pmat]
  calc aeval s (b f * gcF F f) * s = aeval s (b f * gcF F f) * aeval s (X : L[X]) := by
        rw [aeval_X]
    _ = aeval s (X : L[X]) * aeval s (b f * gcF F f) := by
        rw [← map_mul, ← map_mul, mul_comm]
    _ = s * aeval s (b f * gcF F f) := by rw [aeval_X]

theorem coe_root_smul [Fact (∀ x ∈ Vf s b F f, aeval s f *ᵥ x = 0)] (y : Vf s b F f) :
    ((AdjoinRoot.root f • y : Vf s b F f) : Fin n → L) = s *ᵥ (y : Fin n → L) := by
  rw [← AdjoinRoot.mk_X, coe_smul_mk, aeval_X]

theorem Eext_comm_s [Fact (∀ x ∈ Vf s b F f, aeval s f *ᵥ x = 0)]
    (hP : ∀ x : Fin n → L, Pmat s b F f *ᵥ (Pmat s b F f *ᵥ x) = Pmat s b F f *ᵥ x)
    (a : Vf s b F f →ₗ[AdjoinRoot f] Vf s b F f) (x : Fin n → L) :
    s *ᵥ Eext s b F f hP (a.restrictScalars L) x =
      Eext s b F f hP (a.restrictScalars L) (s *ᵥ x) := by
  have hPs : Pmat s b F f *ᵥ (s *ᵥ x) = s *ᵥ (Pmat s b F f *ᵥ x) := by
    rw [Matrix.mulVec_mulVec, Pmat_mul_s, ← Matrix.mulVec_mulVec]
  have hprj : prjV s b F f hP (s *ᵥ x) = AdjoinRoot.root f • prjV s b F f hP x := by
    apply Subtype.ext
    rw [coe_prjV, coe_root_smul, coe_prjV, hPs]
  have hak : ∀ y : Vf s b F f, (a.restrictScalars L) (AdjoinRoot.root f • y) =
      AdjoinRoot.root f • (a.restrictScalars L) y := fun y => map_smul a _ y
  rw [Eext_apply hP, Eext_apply hP, hprj, hak, coe_root_smul, hPs]
  simp only [Matrix.mulVec_add, Matrix.mulVec_sub]

theorem Eext_comp_map (hP : ∀ x : Fin n → L, Pmat s b F f *ᵥ (Pmat s b F f *ᵥ x) = Pmat s b F f *ᵥ x)
    (a a' : Vf s b F f →ₗ[L] Vf s b F f) :
    Eext s b F f hP (a ∘ₗ a') = Eext s b F f hP a ∘ₗ Eext s b F f hP a' := by
  apply LinearMap.ext
  intro x
  exact Eext_comp hP a a' x

end Ext

section Partner

variable {τ : L ≃+* L} {m : ℕ} {s : Matrix (Fin n) (Fin n) L} {F : Finset L[X]}
  {a b : L[X] → L[X]} {f g : L[X]}

theorem hfm_mulVec_right (hτ : ∀ x, τ (τ x) = x) (X : Matrix (Fin n) (Fin n) L)
    (u z : Fin n → L) : hfm τ u (X *ᵥ z) = hfm τ (adjM τ X *ᵥ u) z := by
  rw [hfm_mulVec, adjM_adjM τ hτ]

@[expose] noncomputable def natL (τ : L ≃+* L) (s : Matrix (Fin n) (Fin n) L) (b : L[X] → L[X])
    (F : Finset L[X]) (g : L[X])
    (hPg : ∀ x : Fin n → L, Pmat s b F g *ᵥ (Pmat s b F g *ᵥ x) = Pmat s b F g *ᵥ x)
    (E : (Fin n → L) →ₗ[L] (Fin n → L)) : Vf s b F g →ₗ[L] Vf s b F g :=
  prjV s b F g hPg ∘ₗ adjL τ E ∘ₗ (Vf s b F g).subtype

theorem coe_natL (τ : L ≃+* L) (hPg : ∀ x : Fin n → L, Pmat s b F g *ᵥ (Pmat s b F g *ᵥ x) = Pmat s b F g *ᵥ x)
    (E : (Fin n → L) →ₗ[L] (Fin n → L)) (y : Vf s b F g) :
    ((natL τ s b F g hPg E y : Vf s b F g) : Fin n → L) = Pmat s b F g *ᵥ (adjL τ E (y : Fin n → L)) := by
  rw [natL, LinearMap.comp_apply, LinearMap.comp_apply, Submodule.subtype_apply, coe_prjV]

theorem hfm_natL (hτ : ∀ x, τ (τ x) = x) (hgf : adjM τ (Pmat s b F g) = Pmat s b F f)
    (hPg : ∀ x : Fin n → L, Pmat s b F g *ᵥ (Pmat s b F g *ᵥ x) = Pmat s b F g *ᵥ x)
    (hPf : ∀ x : Fin n → L, Pmat s b F f *ᵥ (Pmat s b F f *ᵥ x) = Pmat s b F f *ᵥ x)
    (a a' : Vf s b F f →ₗ[L] Vf s b F f) (ha : ∀ x, a' (a x) = x)
    (x : Vf s b F f) (y : Vf s b F g) :
    hfm τ (x : Fin n → L) (y : Fin n → L) =
      hfm τ (a x : Fin n → L)
        ((natL τ s b F g hPg (Eext s b F f hPf a') y : Vf s b F g) : Fin n → L) := by
  have hz : hfm τ (a x : Fin n → L)
      ((natL τ s b F g hPg (Eext s b F f hPf a') y : Vf s b F g) : Fin n → L) =
      hfm τ (a x : Fin n → L) (adjL τ (Eext s b F f hPf a') (y : Fin n → L)) := by
    rw [coe_natL, hfm_mulVec_right hτ (Pmat s b F g), hgf, mem_Vf.mp (a x).2]
  rw [hz, ← hfm_adjL τ _ _ _, Eext_mem hPf a' (a x), ha]

theorem hfm_sub_right' (x y y' : Fin n → L) :
    hfm τ x (y - y') = hfm τ x y - hfm τ x y' := by
  simp [hfm, mul_sub, Finset.sum_sub_distrib]

theorem toMatrix'_mulVec_eq_of_commute {E : (Fin n → L) →ₗ[L] (Fin n → L)}
    {M : Matrix (Fin n) (Fin n) L} (h : ∀ x, E (M *ᵥ x) = M *ᵥ E x) :
    LinearMap.toMatrix' E * M = M * LinearMap.toMatrix' E := by
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul, Matrix.toLin'_mul, Matrix.toLin'_toMatrix']
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, Matrix.toLin'_apply]
  exact h x

theorem adjL_comm_of (hfg : adjM τ (Pmat s b F f) = Pmat s b F g) {E : (Fin n → L) →ₗ[L] (Fin n → L)}
    (hE : LinearMap.toMatrix' E * Pmat s b F f = Pmat s b F f * LinearMap.toMatrix' E) (z : Fin n → L) :
    adjL τ E (Pmat s b F g *ᵥ z) = Pmat s b F g *ᵥ adjL τ E z := by
  have hc := congrArg (adjM τ) hE
  rw [adjM_mul, adjM_mul, hfg] at hc
  rw [adjL, Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← hc,
    Matrix.mulVec_mulVec]

theorem natL_comp (hfg : adjM τ (Pmat s b F f) = Pmat s b F g)
    (hPg : ∀ x : Fin n → L, Pmat s b F g *ᵥ (Pmat s b F g *ᵥ x) = Pmat s b F g *ᵥ x)
    (E1 E2 : (Fin n → L) →ₗ[L] (Fin n → L))
    (hE1 : LinearMap.toMatrix' E1 * Pmat s b F f = Pmat s b F f * LinearMap.toMatrix' E1) :
    natL τ s b F g hPg E1 ∘ₗ natL τ s b F g hPg E2 = natL τ s b F g hPg (E2 ∘ₗ E1) := by
  apply LinearMap.ext
  intro y
  apply Subtype.ext
  rw [LinearMap.comp_apply, coe_natL, coe_natL, coe_natL, adjL_comp, LinearMap.comp_apply,
    adjL_comm_of hfg hE1, hPg]

end Partner

end CFSG.LieType.SemisimpleCentralizers.HeldUCD

end
