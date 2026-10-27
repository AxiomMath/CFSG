module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Lin3
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.QuasithinUnique.A5.Kc3L3

open Matrix CFSG.Assembly.LowTwoRank

variable {F : Type} [Field F] [CharP F 2]

abbrev S3 (F : Type) [Field F] : Type := ↥(StatedSL 3 F)

abbrev X3 (F : Type) [Field F] : Type := StatedProj (StatedSL 3 F)

@[expose] def mat (g : S3 F) : Matrix (Fin 3) (Fin 3) F :=
  ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)

omit [CharP F 2] in
theorem mat_mul (g h : S3 F) : mat (g * h) = mat g * mat h := rfl

omit [CharP F 2] in
theorem mat_one : mat (1 : S3 F) = 1 := rfl

omit [CharP F 2] in
theorem mat_injective : Function.Injective (mat : S3 F → Matrix (Fin 3) (Fin 3) F) :=
  fun _ _ e => Subtype.ext (Units.ext e)

omit [CharP F 2] in
theorem mat_inv_mul (g : S3 F) : mat g⁻¹ * mat g = 1 := by
  rw [← mat_mul, inv_mul_cancel, mat_one]

omit [CharP F 2] in
theorem mat_mul_inv (g : S3 F) : mat g * mat g⁻¹ = 1 := by
  rw [← mat_mul, mul_inv_cancel, mat_one]

omit [CharP F 2] in
theorem det_mat (g : S3 F) : (mat g).det = 1 := by
  obtain ⟨g, hg⟩ := g
  rw [statedSL_eq_range_toGL] at hg
  obtain ⟨A, rfl⟩ := hg
  exact A.2

omit [CharP F 2] in
theorem mem_statedSL_of_det {A : GL (Fin 3) F} (h : (A : Matrix (Fin 3) (Fin 3) F).det = 1) :
    A ∈ StatedSL 3 F :=
  CFSG.Open.StatedAPI.mem_statedSL_of_det h

omit [CharP F 2] in
theorem scalar_injective :
    Function.Injective (Matrix.GeneralLinearGroup.scalar (Fin 3) : Fˣ →* GL (Fin 3) F) := by
  intro u v h
  have h1 := congrArg (fun A : GL (Fin 3) F => (A : Matrix (Fin 3) (Fin 3) F) 0 0) h
  exact Units.ext (by simpa [Matrix.scalar_apply] using h1)

theorem unit_sq_eq_one {c : Fˣ} (h : c * c = 1) : c = 1 := by
  have h' : (c : F) * c = 1 := by simpa using congrArg Units.val h
  have h2 : (c : F) = 1 := by
    rcases mul_self_eq_one_iff.1 h' with h1 | h1
    · exact h1
    · rw [h1]
      exact CharTwo.neg_eq 1
  exact Units.ext h2

omit [CharP F 2] in
theorem det_scalar (c : Fˣ) :
    (((Matrix.GeneralLinearGroup.scalar (Fin 3) c : GL (Fin 3) F)) :
      Matrix (Fin 3) (Fin 3) F).det = (c : F) ^ 3 := by
  simp [Matrix.scalar_apply, Matrix.det_diagonal, pow_succ, mul_assoc]

omit [CharP F 2] in
theorem mk_eq_one_iff {g : S3 F} :
    (QuotientGroup.mk g : X3 F) = 1 ↔
      ∃ c : Fˣ, Matrix.GeneralLinearGroup.scalar (Fin 3) c = (g : GL (Fin 3) F) := by
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range]

omit [CharP F 2] in
theorem mk_eq_iff {g h : S3 F} :
    (QuotientGroup.mk g : X3 F) = QuotientGroup.mk h ↔
      ∃ c : Fˣ, Matrix.GeneralLinearGroup.scalar (Fin 3) c = ((g⁻¹ * h : S3 F) : GL (Fin 3) F) := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range]

omit [CharP F 2] in
theorem scalar_comm (c : Fˣ) (g : S3 F) :
    Matrix.GeneralLinearGroup.scalar (Fin 3) c * (g : GL (Fin 3) F) =
      (g : GL (Fin 3) F) * Matrix.GeneralLinearGroup.scalar (Fin 3) c :=
  Matrix.GeneralLinearGroup.scalar_commute c _

theorem eq_of_mk_eq {e e' : S3 F} (he : e * e = 1) (he' : e' * e' = 1)
    (h : (QuotientGroup.mk e : X3 F) = QuotientGroup.mk e') : e = e' := by
  obtain ⟨c, hc⟩ := mk_eq_iff.1 h
  have h1 : (e' : GL (Fin 3) F) = (e : GL (Fin 3) F) * Matrix.GeneralLinearGroup.scalar (Fin 3) c := by
    rw [hc]
    simp
  have he2 : (e : GL (Fin 3) F) * e = 1 := congrArg Subtype.val he
  have he2' : (e' : GL (Fin 3) F) * e' = 1 := congrArg Subtype.val he'
  have h2 : Matrix.GeneralLinearGroup.scalar (Fin 3) (c * c) = (1 : GL (Fin 3) F) := by
    have h3 : (e' : GL (Fin 3) F) * e' =
        ((e : GL (Fin 3) F) * e) * (Matrix.GeneralLinearGroup.scalar (Fin 3) c *
          Matrix.GeneralLinearGroup.scalar (Fin 3) c) := by
      rw [h1]
      have hc' := scalar_comm c e
      calc (e : GL (Fin 3) F) * Matrix.GeneralLinearGroup.scalar (Fin 3) c *
            ((e : GL (Fin 3) F) * Matrix.GeneralLinearGroup.scalar (Fin 3) c)
          = (e : GL (Fin 3) F) * (Matrix.GeneralLinearGroup.scalar (Fin 3) c * (e : GL (Fin 3) F)) *
              Matrix.GeneralLinearGroup.scalar (Fin 3) c := by group
        _ = (e : GL (Fin 3) F) * ((e : GL (Fin 3) F) * Matrix.GeneralLinearGroup.scalar (Fin 3) c) *
              Matrix.GeneralLinearGroup.scalar (Fin 3) c := by rw [hc']
        _ = _ := by group
    rw [he2', he2, one_mul, ← map_mul] at h3
    exact h3.symm
  have hcc : c * c = 1 := scalar_injective (by rw [h2, map_one])
  have hc1 : c = 1 := unit_sq_eq_one hcc
  subst hc1
  rw [map_one] at h1
  exact Subtype.ext (by rw [h1, mul_one])

@[expose] def scl (c : Fˣ) (hc : c ^ 3 = 1) : S3 F :=
  ⟨Matrix.GeneralLinearGroup.scalar (Fin 3) c, mem_statedSL_of_det (by
    rw [det_scalar]
    have := congrArg Units.val hc
    simpa using this)⟩

omit [CharP F 2] in
theorem scl_mk (c : Fˣ) (hc : c ^ 3 = 1) : (QuotientGroup.mk (scl c hc) : X3 F) = 1 :=
  mk_eq_one_iff.2 ⟨c, rfl⟩

omit [CharP F 2] in
theorem scl_comm (c : Fˣ) (hc : c ^ 3 = 1) (g : S3 F) : scl c hc * g = g * scl c hc :=
  Subtype.ext (scalar_comm c g)

omit [CharP F 2] in
theorem exists_lift (x : X3 F) (hx : x * x = 1) :
    ∃ e : S3 F, e * e = 1 ∧ (QuotientGroup.mk e : X3 F) = x := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  have h1 : (QuotientGroup.mk (g * g) : X3 F) = 1 := by rw [QuotientGroup.mk_mul]; exact hx
  obtain ⟨c, hc⟩ := mk_eq_one_iff.1 h1
  have hc3 : c ^ 3 = 1 := by
    apply Units.ext
    have h2 : (((g * g : S3 F) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1 := det_mat (g * g)
    rw [← hc, det_scalar] at h2
    simpa using h2
  refine ⟨scl c hc3 * g, ?_, ?_⟩
  · have hcomm := scl_comm c hc3 g
    have h3 : scl c hc3 * scl c hc3 * (g * g) = 1 := by
      have : (scl c hc3 * scl c hc3 * (g * g) : S3 F) =
          ⟨Matrix.GeneralLinearGroup.scalar (Fin 3) (c ^ 3), mem_statedSL_of_det (by
            rw [det_scalar, hc3]; simp)⟩ := by
        apply Subtype.ext
        show Matrix.GeneralLinearGroup.scalar (Fin 3) c * Matrix.GeneralLinearGroup.scalar (Fin 3) c *
          ((g : GL (Fin 3) F) * g) = _
        have hc' : (g : GL (Fin 3) F) * g = Matrix.GeneralLinearGroup.scalar (Fin 3) c := hc.symm
        rw [hc', ← map_mul, ← map_mul]
        congr 1
        rw [pow_succ, pow_two]
      rw [this]
      apply Subtype.ext
      show Matrix.GeneralLinearGroup.scalar (Fin 3) (c ^ 3) = 1
      rw [hc3, map_one]
    calc scl c hc3 * g * (scl c hc3 * g) = scl c hc3 * (g * scl c hc3) * g := by group
      _ = scl c hc3 * (scl c hc3 * g) * g := by rw [hcomm]
      _ = scl c hc3 * scl c hc3 * (g * g) := by group
      _ = 1 := h3
  · rw [QuotientGroup.mk_mul, scl_mk, one_mul]

theorem comm_of_mk_comm {e f : S3 F} (hf : f * f = 1)
    (h : (QuotientGroup.mk e : X3 F) * QuotientGroup.mk f = QuotientGroup.mk f * QuotientGroup.mk e) :
    e * f = f * e := by
  set z : S3 F := e * f * e⁻¹ * f⁻¹ with hz
  have hz1 : (QuotientGroup.mk z : X3 F) = 1 := by
    rw [hz]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [h]
    group
  obtain ⟨c, hc⟩ := mk_eq_one_iff.1 hz1
  have hzf : z * f = e * f * e⁻¹ := by rw [hz]; group
  have hzfz : z * f = f * z := Subtype.ext (by
    show (z : GL (Fin 3) F) * f = (f : GL (Fin 3) F) * z
    rw [← hc]
    exact scalar_comm c f)
  have hsq : (z * f) * (z * f) = 1 := by
    rw [hzf]
    calc e * f * e⁻¹ * (e * f * e⁻¹) = e * (f * f) * e⁻¹ := by group
      _ = 1 := by rw [hf]; group
  have hzz : z * z = 1 := by
    calc z * z = (z * f) * (z * f) := by
          calc z * z = z * (f * f) * z := by rw [hf]; group
            _ = z * f * (f * z) := by group
            _ = z * f * (z * f) := by rw [← hzfz]
      _ = 1 := hsq
  have h2 : Matrix.GeneralLinearGroup.scalar (Fin 3) (c * c) = (1 : GL (Fin 3) F) := by
    have : (z : GL (Fin 3) F) * z = 1 := congrArg Subtype.val hzz
    rw [← hc, ← map_mul] at this
    exact this
  have hcc : c * c = 1 := scalar_injective (by rw [h2, map_one])
  have hc1 : c = 1 := unit_sq_eq_one hcc
  subst hc1
  have hz2 : z = 1 := Subtype.ext (by rw [← hc, map_one]; rfl)
  rw [hz] at hz2
  calc e * f = (e * f * e⁻¹ * f⁻¹) * (f * e) := by group
    _ = f * e := by rw [hz2, one_mul]

open Classical in
@[expose] noncomputable def Nm (x : X3 F) : Matrix (Fin 3) (Fin 3) F :=
  if h : ∃ e : S3 F, e * e = 1 ∧ (QuotientGroup.mk e : X3 F) = x then mat h.choose - 1 else 0

theorem Nm_mk {e : S3 F} (he : e * e = 1) : Nm (QuotientGroup.mk e : X3 F) = mat e - 1 := by
  rw [Nm]
  split_ifs with hh
  · have := eq_of_mk_eq hh.choose_spec.1 he hh.choose_spec.2
    rw [this]
  · exact absurd ⟨e, he, rfl⟩ hh

theorem Nm_one : Nm (1 : X3 F) = 0 := by
  have := Nm_mk (F := F) (e := 1) (mul_one 1)
  rw [QuotientGroup.mk_one, mat_one, sub_self] at this
  exact this

omit [CharP F 2] in
theorem mat_sq {e : S3 F} (he : e * e = 1) : mat e * mat e = 1 := by
  rw [← mat_mul, he, mat_one]

theorem Nmat_sq {e : S3 F} (he : e * e = 1) : (mat e - 1) * (mat e - 1) = 0 := by
  have h1 := mat_sq he
  rw [CharTwo.sub_eq_add]
  have : (mat e + 1) * (mat e + 1) = mat e * mat e + (mat e + mat e) + 1 := by noncomm_ring
  rw [this, h1, CharTwo.add_self_eq_zero, add_zero]
  exact CharTwo.add_self_eq_zero 1

omit [CharP F 2] in
theorem Nmat_comm {e f : S3 F} (h : e * f = f * e) : (mat e - 1) * (mat f - 1) = (mat f - 1) * (mat e - 1) := by
  have hc : mat e * mat f = mat f * mat e := by rw [← mat_mul, ← mat_mul, h]
  have hc' : Commute (mat e) (mat f) := hc
  exact ((hc'.sub_right (Commute.one_right _)).sub_left
    ((Commute.one_left _).sub_right (Commute.one_right _))).eq

omit [CharP F 2] in
theorem mat_prod_zero {A B : Matrix (Fin 3) (Fin 3) F} (hA : A * A = 0) (hB : B * B = 0)
    (hAB : A * B = B * A) : A * B = 0 := by
  have hW : Module.finrank F (Fin 3 → F) = 3 := by simp
  have h1 := Kc3Lin3.prod_zero_of_dim_three hW (N := Matrix.toLin' A) (M := Matrix.toLin' B)
    (by rw [← Matrix.toLin'_mul, hA]; exact map_zero _)
    (by rw [← Matrix.toLin'_mul, hB]; exact map_zero _)
    (by rw [← Matrix.toLin'_mul, ← Matrix.toLin'_mul, hAB])
  rw [← Matrix.toLin'_mul] at h1
  exact (LinearEquiv.map_eq_zero_iff Matrix.toLin').1 h1

theorem Nm_mul_zero {x y : X3 F} (hx : x * x = 1) (hy : y * y = 1) (hxy : x * y = y * x) :
    Nm x * Nm y = 0 := by
  obtain ⟨e, he, rfl⟩ := exists_lift x hx
  obtain ⟨f, hf, rfl⟩ := exists_lift y hy
  have hef : e * f = f * e := comm_of_mk_comm hf hxy
  rw [Nm_mk he, Nm_mk hf]
  exact mat_prod_zero (Nmat_sq he) (Nmat_sq hf) (Nmat_comm hef)

theorem Nm_mul {x y : X3 F} (hx : x * x = 1) (hy : y * y = 1) (hxy : x * y = y * x) :
    Nm (x * y) = Nm x + Nm y := by
  obtain ⟨e, he, rfl⟩ := exists_lift x hx
  obtain ⟨f, hf, rfl⟩ := exists_lift y hy
  have hef : e * f = f * e := comm_of_mk_comm hf hxy
  have hef2 : (e * f) * (e * f) = 1 := by
    calc e * f * (e * f) = e * (f * e) * f := by group
      _ = e * (e * f) * f := by rw [hef]
      _ = (e * e) * (f * f) := by group
      _ = 1 := by rw [he, hf, one_mul]
  rw [← QuotientGroup.mk_mul, Nm_mk hef2, Nm_mk he, Nm_mk hf, mat_mul]
  have h0 := mat_prod_zero (Nmat_sq he) (Nmat_sq hf) (Nmat_comm hef)
  have : mat e * mat f - 1 = (mat e - 1) + (mat f - 1) + (mat e - 1) * (mat f - 1) := by
    noncomm_ring
  rw [this, h0, add_zero]

theorem Nm_conj (g : S3 F) {x : X3 F} (hx : x * x = 1) :
    Nm ((QuotientGroup.mk g : X3 F) * x * (QuotientGroup.mk g : X3 F)⁻¹) = mat g * Nm x * mat g⁻¹ := by
  obtain ⟨e, he, rfl⟩ := exists_lift x hx
  have hge : (g * e * g⁻¹) * (g * e * g⁻¹) = 1 := by
    calc g * e * g⁻¹ * (g * e * g⁻¹) = g * (e * e) * g⁻¹ := by group
      _ = 1 := by rw [he]; group
  have h1 : (QuotientGroup.mk g : X3 F) * QuotientGroup.mk e * (QuotientGroup.mk g : X3 F)⁻¹ =
      QuotientGroup.mk (g * e * g⁻¹) := by
    simp [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  rw [h1, Nm_mk hge, Nm_mk he, mat_mul, mat_mul, mul_sub, sub_mul, mul_one, mat_mul_inv]

theorem eq_one_of_Nm_eq_zero {x : X3 F} (hx : x * x = 1) (h : Nm x = 0) : x = 1 := by
  obtain ⟨e, he, rfl⟩ := exists_lift x hx
  rw [Nm_mk he, sub_eq_zero] at h
  have : e = 1 := mat_injective (by rw [h, mat_one])
  rw [this, QuotientGroup.mk_one]

end CFSG.QuasithinUnique.A5.Kc3L3
