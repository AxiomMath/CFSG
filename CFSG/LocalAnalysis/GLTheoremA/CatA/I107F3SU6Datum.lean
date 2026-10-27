module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107F3SU6DatumAlg
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107F3SU6Data
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaLinear
public import CFSG.Assembly.GL83LieDefs
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicAlphaData

public section

namespace CFSG.LocalAnalysis.GLTheoremA.U6Herm

open CFSG.Assembly CFSG.GH74.KGroups CFSG.AGLEmbedding CFSG.AGLEmbedding.R3
open scoped MatrixGroups

section Group

variable {F : Type} [Field F] [CjField F]

@[expose] def suMonoid (F : Type) [Field F] [CjField F] :
    Submonoid (Matrix (Fin 6) (Fin 6) F) where
  carrier := {M | IsSU M}
  one_mem' := ⟨Matrix.det_one, by rw [conjT_one, Matrix.one_mul]⟩
  mul_mem' {M N} hM hN :=
    ⟨by rw [Matrix.det_mul, hM.1, hN.1, one_mul], by
      calc conjT (M * N) * (M * N) = conjT N * (conjT M * M) * N := by
            rw [conjT_mul]; simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hM.2, Matrix.mul_one, hN.2]⟩

@[expose] def suUnit (x : suMonoid F) : GL (Fin 6) F :=
  ⟨x.1, conjT x.1, mul_eq_one_comm.mpr x.2.2, x.2.2⟩

theorem suUnit_mem (x : suMonoid F) : suUnit x ∈ LargeEvenSUGroup (Fin 6) F 2 := by
  unfold LargeEvenSUGroup
  exact Subgroup.subset_closure ⟨x.2.1, x.2.2⟩

@[expose] def toR : suMonoid F →* LargeEvenProj (LargeEvenSUGroup (Fin 6) F 2) where
  toFun x := QuotientGroup.mk ⟨suUnit x, suUnit_mem x⟩
  map_one' := by
    have h : (⟨suUnit 1, suUnit_mem 1⟩ : ↥(LargeEvenSUGroup (Fin 6) F 2)) = 1 :=
      Subtype.ext (Units.ext rfl)
    rw [h]
    exact QuotientGroup.mk_one _
  map_mul' x y := by
    rw [← QuotientGroup.mk_mul]
    exact congrArg QuotientGroup.mk (Subtype.ext (Units.ext rfl))

theorem eq_smul_of_toR_eq_one {x : suMonoid F} (h : toR x = 1) :
    ∃ u : F, x.1 = u • (1 : Matrix (Fin 6) (Fin 6) F) := by
  have h' := (QuotientGroup.eq_one_iff _).1 h
  rw [Subgroup.mem_subgroupOf] at h'
  obtain ⟨u, hu⟩ := h'
  refine ⟨u, ?_⟩
  have := congrArg (fun g : GL (Fin 6) F => (g : Matrix (Fin 6) (Fin 6) F)) hu
  simp only [Matrix.GeneralLinearGroup.coe_scalar] at this
  rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal] at this
  exact this.symm

@[expose] def hermSub (F : Type) [Field F] [CjField F] :
    AddSubgroup (Matrix (Fin 3) (Fin 3) F) where
  carrier := {X | conjT X = X}
  zero_mem' := conjT_zero
  add_mem' {X Y} hX hY := by
    change conjT (X + Y) = X + Y
    rw [conjT_add, (hX : conjT X = X), (hY : conjT Y = Y)]
  neg_mem' {X} hX := by
    change conjT (-X) = -X
    rw [conjT_neg, (hX : conjT X = X)]

@[expose] def radM (H : Hyp F) : Multiplicative (hermSub F) →* suMonoid F where
  toFun X := ⟨H.B (Multiplicative.toAdd X).1, H.B_isSU (Multiplicative.toAdd X).2⟩
  map_one' := Subtype.ext (by simp [H.B_zero])
  map_mul' X Y := Subtype.ext (by simp [H.B_mul])

@[expose] def radR (H : Hyp F) :
    Multiplicative (hermSub F) →* LargeEvenProj (LargeEvenSUGroup (Fin 6) F 2) :=
  toR.comp (radM H)

theorem eq_one_of_radR_eq_one (H : Hyp F) {x : Multiplicative (hermSub F)} (h : radR H x = 1) :
    x = 1 := by
  obtain ⟨u, hu⟩ := eq_smul_of_toR_eq_one h
  have h0 := H.eq_zero_of_B_eq_smul hu
  apply Multiplicative.toAdd.injective
  exact Subtype.ext h0

theorem prod_map_ofAdd {G T : Type} [Group G] [AddCommGroup T] (ρ : Multiplicative T →* G)
    {ι : Type} (l : List ι) (x : ι → T) :
    (l.map fun k => ρ (Multiplicative.ofAdd (x k))).prod =
      ρ (Multiplicative.ofAdd (l.map x).sum) := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, ofAdd_add]

theorem prod_pow_eq (H : Hyp F) {n : ℕ} (v : Fin n → hermSub F) (e : Fin n → ℕ) :
    ((List.finRange n).map fun k => radR H (Multiplicative.ofAdd (v k)) ^ e k).prod =
      radR H (Multiplicative.ofAdd (∑ k, e k • v k)) := by
  have h1 : ∀ k, radR H (Multiplicative.ofAdd (v k)) ^ e k =
      radR H (Multiplicative.ofAdd (e k • v k)) := fun k => by rw [← map_pow, ofAdd_nsmul]
  simp only [h1]
  rw [prod_map_ofAdd (radR H) (List.finRange n) fun k => e k • v k, ← Fin.sum_univ_def]

theorem radR_sq (H : Hyp F) (X : hermSub F) : radR H (Multiplicative.ofAdd X) ^ 2 = 1 := by
  have h : X + X = 0 := Subtype.ext (matrix_add_self X.1)
  rw [← map_pow, ← ofAdd_nsmul, two_nsmul, h, ofAdd_zero, map_one]

theorem radR_comm (H : Hyp F) (X Y : hermSub F) :
    radR H (Multiplicative.ofAdd X) * radR H (Multiplicative.ofAdd Y) =
      radR H (Multiplicative.ofAdd Y) * radR H (Multiplicative.ofAdd X) := by
  rw [← (radR H).map_mul, ← (radR H).map_mul, mul_comm]

@[expose] def levi (H : Hyp F) {A A' : Matrix (Fin 3) (Fin 3) F} (hA : conjT A * A' = 1)
    (h1 : A.det = 1) (h2 : A'.det = 1) : suMonoid F :=
  ⟨H.L A A', H.L_isSU hA h1 h2⟩

theorem levi_conj (H : Hyp F) {A A' : Matrix (Fin 3) (Fin 3) F} (hA : conjT A * A' = 1)
    (h1 : A.det = 1) (h2 : A'.det = 1) (X : hermSub F) :
    toR (levi H hA h1 h2) * radR H (Multiplicative.ofAdd X) * (toR (levi H hA h1 h2))⁻¹ =
      radR H (Multiplicative.ofAdd ⟨A * X.1 * conjT A, conjT_conj_herm X.2 A⟩) := by
  rw [mul_inv_eq_iff_eq_mul]
  simp only [radR, MonoidHom.comp_apply, ← map_mul]
  exact congrArg toR (Subtype.ext (H.L_mul_B hA X.1))

end Group

section Basis

variable {F : Type} [Field F] [CjField F] (ψ : GF4 ≃+* F)

@[expose] def hermElt (i : Fin 9) : hermSub F := ⟨hermB ψ i, conjT_hermB ψ i⟩

@[expose] noncomputable def radBasis (i : Fin 9) : LargeEvenProj (LargeEvenSUGroup (Fin 6) F 2) :=
  radR (hyp ψ) (Multiplicative.ofAdd (hermElt ψ i))

@[expose] noncomputable def leviElt (j : Fin 3) : LargeEvenProj (LargeEvenSUGroup (Fin 6) F 2) :=
  toR (levi (hyp ψ) (conjT_actA_mul ψ j) (det_actA ψ j) (det_actA' ψ j))

theorem radBasis_comm (i j : Fin 9) : radBasis ψ i * radBasis ψ j = radBasis ψ j * radBasis ψ i :=
  radR_comm _ _ _

theorem radBasis_sq (i : Fin 9) : radBasis ψ i ^ 2 = 1 := radR_sq _ _

theorem radBasis_indep (c : Fin 9 → ZMod 2) :
    ((List.finRange 9).map fun k => radBasis ψ k ^ (c k).val).prod = 1 → c = 0 := by
  intro h
  unfold radBasis at h
  rw [prod_pow_eq] at h
  have h1 := ofAdd_eq_one.1 (eq_one_of_radR_eq_one _ h)
  have h2 := congrArg (fun X : hermSub F => (X : Matrix (Fin 3) (Fin 3) F)) h1
  simp only [AddSubmonoidClass.coe_finsetSum, AddSubgroup.coe_nsmul, ZeroMemClass.coe_zero] at h2
  exact hermB_indep ψ c h2

theorem leviElt_act (tab : Fin 3 → Fin 9 → Fin 9 → ℕ)
    (h : ∀ (j : Fin 3) (i : Fin 9),
      A4 j * H4 i * conjT (A4 j) = ∑ k : Fin 9, tab j k i • H4 k) (j : Fin 3) (i : Fin 9) :
    leviElt ψ j * radBasis ψ i * (leviElt ψ j)⁻¹ =
      ((List.finRange 9).map fun k => radBasis ψ k ^ tab j k i).prod := by
  unfold leviElt radBasis
  rw [levi_conj, prod_pow_eq]
  congr 2
  apply Subtype.ext
  simp only [AddSubmonoidClass.coe_finsetSum, AddSubgroup.coe_nsmul]
  exact act_identity ψ tab h j i

end Basis

theorem act4_u6 : ∀ (j : Fin 3) (i : Fin 9), A4 j * H4 i * conjT (A4 j) =
    ∑ k : Fin 9, (actMatN 2 u6Mod.basis.length (u6Mod.acts.get j) k i).val • H4 k := by
  decide +kernel

section Spec

variable (F : Type) [Field F] [Finite F] (hF : Nat.card F = 4)

@[expose] noncomputable def psiOf : GF4 ≃+* F :=
  haveI := Fintype.ofFinite F
  FiniteField.ringEquivOfCardEq
    (show Fintype.card GF4 = Fintype.card F from
      (show Fintype.card GF4 = 4 from rfl).trans (Nat.card_eq_fintype_card.symm.trans hF).symm)

@[expose] noncomputable def u6a (i : Fin u6Mod.basis.length) :
    LargeEvenProj (LargeEvenSUGroup (Fin 6) F 2) :=
  @radBasis F _ (cjField_of_equiv (psiOf F hF)) (psiOf F hF) i

@[expose] noncomputable def u6g (j : Fin u6Mod.acts.length) :
    LargeEvenProj (LargeEvenSUGroup (Fin 6) F 2) :=
  @leviElt F _ (cjField_of_equiv (psiOf F hF)) (psiOf F hF) j

theorem u6_comm (i j : Fin u6Mod.basis.length) :
    u6a F hF i * u6a F hF j = u6a F hF j * u6a F hF i := by
  haveI := cjField_of_equiv (psiOf F hF)
  exact radBasis_comm _ i j

theorem u6_pow (i : Fin u6Mod.basis.length) : u6a F hF i ^ 2 = 1 := by
  haveI := cjField_of_equiv (psiOf F hF)
  exact radBasis_sq _ i

theorem u6_indep (c : Fin u6Mod.basis.length → ZMod 2) :
    ((List.finRange u6Mod.basis.length).map fun k => u6a F hF k ^ (c k).val).prod = 1 →
      c = 0 := by
  haveI := cjField_of_equiv (psiOf F hF)
  exact radBasis_indep _ c

theorem u6_act (j : Fin u6Mod.acts.length) (i : Fin u6Mod.basis.length) :
    u6g F hF j * u6a F hF i * (u6g F hF j)⁻¹ = ((List.finRange u6Mod.basis.length).map fun k =>
      u6a F hF k ^ (actMatN 2 u6Mod.basis.length (u6Mod.acts.get j) k i).val).prod := by
  haveI := cjField_of_equiv (psiOf F hF)
  exact leviElt_act _ (fun j k i => (actMatN 2 u6Mod.basis.length (u6Mod.acts.get j) k i).val)
    act4_u6 j i

@[expose] noncomputable def u6Spec :
    ModuleSpec (LargeEvenProj (LargeEvenSUGroup (Fin 6) F 2)) 2 where
  n := u6Mod.basis.length
  m := u6Mod.acts.length
  a := u6a F hF
  g := u6g F hF
  M := fun j => actMatN 2 u6Mod.basis.length (u6Mod.acts.get j)
  comm := u6_comm F hF
  pow := u6_pow F hF
  indep := u6_indep F hF
  act := u6_act F hF

end Spec

end CFSG.LocalAnalysis.GLTheoremA.U6Herm
