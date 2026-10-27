module

public import CFSG.LieType.SemisimpleCentralizers.HeldUCDGroup
public import CFSG.LieType.SemisimpleCentralizers.HeldUCDBlocks

public section

open CFSG.LocalAnalysis.ComponentInitial

namespace CFSG.LieType.SemisimpleCentralizers.HeldUCD

open Matrix Polynomial

open scoped _root_.Classical

variable {L : Type} [Field L] {n : ℕ}

section Index

variable {τ : L ≃+* L} {m : ℕ} {s : Matrix (Fin n) (Fin n) L} {F : Finset L[X]}
  {a b : L[X] → L[X]}

theorem exists_piI (H : PrimaryHyp τ s m F a b) (f : ↥(Fset s b F)) :
    ∃ g : ↥(Fset s b F), adjM τ (Pmat s b F f.1) = Pmat s b F g.1 := by
  obtain ⟨g, hgF, hg⟩ := H.exists_adjM_Pmat' (mem_Fset.mp f.2).1 (mem_Fset.mp f.2).2
  have hne : Pmat s b F g ≠ 0 := by
    rw [← hg]
    intro h
    apply (mem_Fset.mp f.2).2
    rw [← adjM_adjM τ H.hτ (Pmat s b F f.1), h, adjM_zero' τ]
  exact ⟨⟨g, mem_Fset.mpr ⟨hgF, hne⟩⟩, hg⟩

@[expose] noncomputable def ordI (f : ↥(Fset s b F)) : ℕ :=
  (Fintype.equivFin ↥(Fset s b F) f : ℕ)

@[expose] noncomputable def piI (H : PrimaryHyp τ s m F a b) (f : ↥(Fset s b F)) : ↥(Fset s b F) :=
  Classical.choose (exists_piI H f)

theorem adjM_piI (H : PrimaryHyp τ s m F a b) (f : ↥(Fset s b F)) :
    adjM τ (Pmat s b F f.1) = Pmat s b F (piI H f).1 :=
  Classical.choose_spec (exists_piI H f)

theorem piI_piI (H : PrimaryHyp τ s m F a b) (f : ↥(Fset s b F)) : piI H (piI H f) = f := by
  apply Subtype.ext
  have h : Pmat s b F (piI H (piI H f)).1 = Pmat s b F f.1 := by
    rw [← adjM_piI H (piI H f), ← adjM_piI H f, adjM_adjM τ H.hτ]
  exact Pmat_eq_of_eq H.hirr H.hmon H.hprod H.hsm H.hab (mem_Fset.mp (piI H (piI H f)).2).1
    (mem_Fset.mp f.2).1 (mem_Fset.mp (piI H (piI H f)).2).2 h

end Index

section Instances

variable {τ : L ≃+* L} {m : ℕ} {s : Matrix (Fin n) (Fin n) L} {F : Finset L[X]} {a b : L[X] → L[X]}

theorem Pmat_mulVec_s (f : L[X]) (x : Fin n → L) :
    Pmat s b F f *ᵥ (s *ᵥ x) = s *ᵥ (Pmat s b F f *ᵥ x) := by
  rw [Matrix.mulVec_mulVec, Pmat_mul_s, ← Matrix.mulVec_mulVec]

end Instances

section Partner

variable {τ : L ≃+* L} {m : ℕ} {s : Matrix (Fin n) (Fin n) L} {F : Finset L[X]} {a b : L[X] → L[X]}

theorem adjL_comm_s (hs : adjM τ s * s = 1) {E : (Fin n → L) →ₗ[L] (Fin n → L)}
    (hE : ∀ x, E (s *ᵥ x) = s *ᵥ E x) (x : Fin n → L) :
    adjL τ E (s *ᵥ x) = s *ᵥ adjL τ E x := by
  have hM : LinearMap.toMatrix' E * s = s * LinearMap.toMatrix' E :=
    toMatrix'_mulVec_eq_of_commute hE
  have hc := congrArg (adjM τ) hM
  rw [adjM_mul, adjM_mul] at hc
  have hS' : s * adjM τ s = 1 := mul_eq_one_comm.mp hs
  have hA : adjM τ (LinearMap.toMatrix' E) * s = s * adjM τ (LinearMap.toMatrix' E) := by
    calc adjM τ (LinearMap.toMatrix' E) * s
        = (s * adjM τ s) * adjM τ (LinearMap.toMatrix' E) * s := by rw [hS', one_mul]
      _ = s * (adjM τ s * adjM τ (LinearMap.toMatrix' E)) * s := by simp only [mul_assoc]
      _ = s * (adjM τ (LinearMap.toMatrix' E) * adjM τ s) * s := by rw [hc]
      _ = s * adjM τ (LinearMap.toMatrix' E) * (adjM τ s * s) := by simp only [mul_assoc]
      _ = s * adjM τ (LinearMap.toMatrix' E) := by rw [hs, mul_one]
  rw [adjL, Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec, hA,
    ← Matrix.mulVec_mulVec]

@[expose] noncomputable def natE (H : PrimaryHyp τ s m F a b) (src : ↥(Fset s b F))
    [Fact (∀ x ∈ Vf s b F src.1, aeval s src.1 *ᵥ x = 0)]
    (u : (Vf s b F src.1 →ₗ[AdjoinRoot src.1] Vf s b F src.1)ˣ) : Vend L n :=
  Eext s b F src.1 (Pmat_idem_index H src) ((u⁻¹).val.restrictScalars L)

theorem natE_comm_s (H : PrimaryHyp τ s m F a b) (src : ↥(Fset s b F))
    [Fact (∀ x ∈ Vf s b F src.1, aeval s src.1 *ᵥ x = 0)]
    (u : (Vf s b F src.1 →ₗ[AdjoinRoot src.1] Vf s b F src.1)ˣ) (x : Fin n → L) :
    natE H src u (s *ᵥ x) = s *ᵥ natE H src u x :=
  (Eext_comm_s (Pmat_idem_index H src) (u⁻¹).val x).symm

theorem natE_matrix_comm (H : PrimaryHyp τ s m F a b) (src : ↥(Fset s b F))
    [Fact (∀ x ∈ Vf s b F src.1, aeval s src.1 *ᵥ x = 0)]
    (u : (Vf s b F src.1 →ₗ[AdjoinRoot src.1] Vf s b F src.1)ˣ) :
    LinearMap.toMatrix' (natE H src u) * Pmat s b F src.1 =
      Pmat s b F src.1 * LinearMap.toMatrix' (natE H src u) :=
  toMatrix'_mulVec_eq_of_commute (fun x =>
    (Eext_comm_P (Pmat_idem_index H src) ((u⁻¹).val.restrictScalars L) x).symm)

theorem natE_comp (H : PrimaryHyp τ s m F a b) (src : ↥(Fset s b F))
    [Fact (∀ x ∈ Vf s b F src.1, aeval s src.1 *ᵥ x = 0)]
    (u v : (Vf s b F src.1 →ₗ[AdjoinRoot src.1] Vf s b F src.1)ˣ) :
    natE H src v ∘ₗ natE H src u = natE H src (u * v) := by
  unfold natE
  rw [← Eext_comp_map]
  congr 1

@[expose] noncomputable def natLU (H : PrimaryHyp τ s m F a b) (src tgt : ↥(Fset s b F))
    [Fact (∀ x ∈ Vf s b F src.1, aeval s src.1 *ᵥ x = 0)]
    (u : (Vf s b F src.1 →ₗ[AdjoinRoot src.1] Vf s b F src.1)ˣ) :
    Vf s b F tgt.1 →ₗ[L] Vf s b F tgt.1 :=
  natL τ s b F tgt.1 (Pmat_idem_index H tgt) (natE H src u)

theorem natLU_mul (H : PrimaryHyp τ s m F a b) (src tgt : ↥(Fset s b F))
    [Fact (∀ x ∈ Vf s b F src.1, aeval s src.1 *ᵥ x = 0)]
    (hpair : adjM τ (Pmat s b F tgt.1) = Pmat s b F src.1)
    (u v : (Vf s b F src.1 →ₗ[AdjoinRoot src.1] Vf s b F src.1)ˣ) :
    natLU H src tgt (u * v) = natLU H src tgt u ∘ₗ natLU H src tgt v := by
  have hfg : adjM τ (Pmat s b F src.1) = Pmat s b F tgt.1 := by
    rw [← hpair, adjM_adjM τ H.hτ]
  unfold natLU
  rw [natL_comp hfg (Pmat_idem_index H tgt) (natE H src u) (natE H src v) (natE_matrix_comm H src u),
    natE_comp H src u v]

theorem natLU_one (H : PrimaryHyp τ s m F a b) (src tgt : ↥(Fset s b F))
    [Fact (∀ x ∈ Vf s b F src.1, aeval s src.1 *ᵥ x = 0)] :
    natLU H src tgt 1 = LinearMap.id := by
  have hid : (((1 : (Vf s b F src.1 →ₗ[AdjoinRoot src.1] Vf s b F src.1)ˣ)⁻¹).val.restrictScalars L) =
      LinearMap.id := LinearMap.ext fun x => rfl
  have hE : natE H src 1 = LinearMap.id := by
    apply LinearMap.ext
    intro x
    unfold natE
    rw [hid]
    exact Eext_one (Pmat_idem_index H src) x
  apply LinearMap.ext
  intro y
  apply Subtype.ext
  unfold natLU
  rw [coe_natL, hE, adjL_id, LinearMap.id_apply, LinearMap.id_apply, mem_Vf.mp y.2]

theorem natLU_comm_root (H : PrimaryHyp τ s m F a b) (src tgt : ↥(Fset s b F))
    [Fact (∀ x ∈ Vf s b F src.1, aeval s src.1 *ᵥ x = 0)]
    [Fact (∀ x ∈ Vf s b F tgt.1, aeval s tgt.1 *ᵥ x = 0)]
    (u : (Vf s b F src.1 →ₗ[AdjoinRoot src.1] Vf s b F src.1)ˣ) (y : Vf s b F tgt.1) :
    AdjoinRoot.root tgt.1 • natLU H src tgt u y = natLU H src tgt u (AdjoinRoot.root tgt.1 • y) := by
  apply Subtype.ext
  unfold natLU
  rw [coe_root_smul, coe_natL, coe_natL, coe_root_smul, ← Pmat_mulVec_s,
    ← adjL_comm_s H.hs (natE_comm_s H src u)]

@[expose] noncomputable def natUnit (H : PrimaryHyp τ s m F a b) (src tgt : ↥(Fset s b F))
    [Fact (∀ x ∈ Vf s b F src.1, aeval s src.1 *ᵥ x = 0)]
    [Fact (∀ x ∈ Vf s b F tgt.1, aeval s tgt.1 *ᵥ x = 0)]
    (hpair : adjM τ (Pmat s b F tgt.1) = Pmat s b F src.1)
    (u : (Vf s b F src.1 →ₗ[AdjoinRoot src.1] Vf s b F src.1)ˣ) :
    (Vf s b F tgt.1 →ₗ[AdjoinRoot tgt.1] Vf s b F tgt.1)ˣ where
  val := KLin (natLU H src tgt u) (natLU_comm_root H src tgt u)
  inv := KLin (natLU H src tgt u⁻¹) (natLU_comm_root H src tgt u⁻¹)
  val_inv := by
    apply LinearMap.ext
    intro y
    have h := natLU_mul H src tgt hpair u u⁻¹
    rw [mul_inv_cancel, natLU_one] at h
    simp only [Module.End.mul_apply, Module.End.one_apply]
    exact (LinearMap.congr_fun h y).symm
  inv_val := by
    apply LinearMap.ext
    intro y
    have h := natLU_mul H src tgt hpair u⁻¹ u
    rw [inv_mul_cancel, natLU_one] at h
    simp only [Module.End.mul_apply, Module.End.one_apply]
    exact (LinearMap.congr_fun h y).symm

theorem hfm_natUnit (H : PrimaryHyp τ s m F a b) (hτ : ∀ x, τ (τ x) = x) (src tgt : ↥(Fset s b F))
    [Fact (∀ x ∈ Vf s b F src.1, aeval s src.1 *ᵥ x = 0)]
    [Fact (∀ x ∈ Vf s b F tgt.1, aeval s tgt.1 *ᵥ x = 0)]
    (hpair : adjM τ (Pmat s b F tgt.1) = Pmat s b F src.1)
    (u : (Vf s b F src.1 →ₗ[AdjoinRoot src.1] Vf s b F src.1)ˣ)
    (x : Vf s b F src.1) (y : Vf s b F tgt.1) :
    hfm τ (x : Fin n → L) (y : Fin n → L) =
      hfm τ ((u.val x : Vf s b F src.1) : Fin n → L)
        (((natUnit H src tgt hpair u).val y : Vf s b F tgt.1) : Fin n → L) := by
  have ha : ∀ z, (u⁻¹).val.restrictScalars L (u.val.restrictScalars L z) = z := by
    intro z
    have h : ((u⁻¹).val * u.val) z = z := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Module.End.one_apply]
    exact h
  exact hfm_natL hτ hpair (Pmat_idem_index H tgt) (Pmat_idem_index H src)
    (u.val.restrictScalars L) ((u⁻¹).val.restrictScalars L) ha x y

end Partner

end CFSG.LieType.SemisimpleCentralizers.HeldUCD

end
