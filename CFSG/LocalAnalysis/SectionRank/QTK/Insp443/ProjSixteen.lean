module

public import CFSG.Open.StatedDefs
public import CFSG.Open.LocalVocabulary
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Open.Defs

public section

namespace CFSG.SectionRank.QTK.Insp443

open CFSG.Open Matrix

@[expose] def liftMats {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    {H : Subgroup (GL ι K)} (E : Subgroup (CFSG.Open.StatedProj H)) : Set (Matrix ι ι K) :=
  {M | ∃ h : H, (QuotientGroup.mk h : CFSG.Open.StatedProj H) ∈ E ∧
    ((h : GL ι K) : Matrix ι ι K) = M}

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] {H : Subgroup (GL ι K)}

private def mat (h : H) : Matrix ι ι K := ((h : GL ι K) : Matrix ι ι K)

private theorem mat_mul (a b : H) : mat (a * b) = mat a * mat b := by
  simp [mat, Subgroup.coe_mul]

private theorem mat_inv (a : H) : mat a⁻¹ = (mat a)⁻¹ := by
  simp [mat, Subgroup.coe_inv]

private theorem mat_one : mat (1 : H) = 1 := by
  simp [mat]

private theorem exists_scalar_of_mk_eq {h₁ h₂ : H}
    (hmk : (QuotientGroup.mk h₁ : CFSG.Open.StatedProj H) = QuotientGroup.mk h₂) :
    ∃ c : Kˣ, mat h₁ = (c : K) • mat h₂ := by
  have hmem : h₁⁻¹ * h₂ ∈ (StatedScalars ι K).subgroupOf H := QuotientGroup.eq.mp hmk
  rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hmem
  obtain ⟨c, hc⟩ := hmem
  have hmat : mat (h₁⁻¹ * h₂) = (c : K) • 1 := by
    rw [mat]
    change ((↑(h₁⁻¹ * h₂) : GL ι K) : Matrix ι ι K) = (c : K) • 1
    rw [← hc, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal]
  have hmul : mat h₂ = (c : K) • mat h₁ := by
    have h1 : mat h₁ * mat (h₁⁻¹ * h₂) = (c : K) • mat h₁ := by
      rw [hmat, Matrix.mul_smul, mul_one]
    have h2 : mat h₁ * mat (h₁⁻¹ * h₂) = mat h₂ := by
      rw [← mat_mul, mul_inv_cancel_left]
    rw [h2] at h1
    exact h1
  refine ⟨c⁻¹, ?_⟩
  have hc0 : (c : K) ≠ 0 := c.ne_zero
  calc mat h₁ = (c : K)⁻¹ • ((c : K) • mat h₁) := by
        rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
    _ = (c : K)⁻¹ • mat h₂ := by rw [hmul]
    _ = ((c⁻¹ : Kˣ) : K) • mat h₂ := by simp

private theorem mk_eq_of_scalar_mul {h₁ h₂ : H} {c : Kˣ}
    (hc : mat h₁ = (c : K) • mat h₂) :
    (QuotientGroup.mk h₁ : CFSG.Open.StatedProj H) = QuotientGroup.mk h₂ := by
  have hmat : mat (h₁ * h₂⁻¹) = (c : K) • 1 := by
    calc mat (h₁ * h₂⁻¹) = mat h₁ * mat h₂⁻¹ := mat_mul h₁ h₂⁻¹
      _ = (c : K) • mat h₂ * (mat h₂)⁻¹ := by rw [hc, mat_inv]
      _ = (c : K) • (mat h₂ * (mat h₂)⁻¹) := Matrix.smul_mul _ _ _
      _ = (c : K) • 1 := by
            rw [← mat_inv, ← mat_mul, mul_inv_cancel, mat_one]
  have hmem : h₁ * h₂⁻¹ ∈ (StatedScalars ι K).subgroupOf H := by
    rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range]
    refine ⟨c, ?_⟩
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]
    exact hmat.symm
  have h1 : (QuotientGroup.mk (h₁ * h₂⁻¹) : CFSG.Open.StatedProj H) = 1 :=
    (QuotientGroup.eq_one_iff (h₁ * h₂⁻¹)).mpr hmem
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h1
  exact mul_inv_eq_one.mp h1

private noncomputable def lift (E : Subgroup (CFSG.Open.StatedProj H)) : E → H :=
  fun e => Quotient.out (e : CFSG.Open.StatedProj H)

private theorem mk_lift (E : Subgroup (CFSG.Open.StatedProj H)) (e : E) :
    (QuotientGroup.mk (lift E e) : CFSG.Open.StatedProj H) = (e : CFSG.Open.StatedProj H) :=
  QuotientGroup.out_eq' (e : CFSG.Open.StatedProj H)

private theorem mem_liftMats_lift (E : Subgroup (CFSG.Open.StatedProj H)) (e : E) :
    mat (lift E e) ∈ liftMats E := by
  refine ⟨lift E e, ?_, rfl⟩
  rw [mk_lift]
  exact e.2

private theorem liftMats_subset_span (E : Subgroup (CFSG.Open.StatedProj H)) :
    liftMats E ⊆ (Submodule.span K (Set.range (fun e : E => mat (lift E e))) :
      Set (Matrix ι ι K)) := by
  rintro M ⟨h, hhE, rfl⟩
  obtain ⟨c, hc⟩ :=
    exists_scalar_of_mk_eq (h₁ := h) (h₂ := lift E ⟨(QuotientGroup.mk h : _), hhE⟩)
      (by rw [mk_lift])
  change mat h ∈ Submodule.span K (Set.range (fun e : E => mat (lift E e)))
  rw [hc]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨(QuotientGroup.mk h : _), hhE⟩, rfl⟩)

private theorem span_liftMats_eq_span_lift (E : Subgroup (CFSG.Open.StatedProj H))
    (hspan : Submodule.span K (liftMats E) = ⊤) :
    Submodule.span K (Set.range (fun e : E => mat (lift E e))) = ⊤ := by
  apply le_antisymm le_top
  rw [← hspan]
  exact Submodule.span_le.mpr (liftMats_subset_span E)

theorem span_liftMats_eq_top_of_trace {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    {H : Subgroup (GL ι K)} {E : Subgroup (CFSG.Open.StatedProj H)}
    (h2 : (2 : K) ≠ 0) (hι : Fintype.card ι = 4) (hcard : Nat.card E = 16)
    (htr : ∀ h : H, (QuotientGroup.mk h : CFSG.Open.StatedProj H) ∈ E →
      (QuotientGroup.mk h : CFSG.Open.StatedProj H) ≠ 1 →
      Matrix.trace ((h : GL ι K) : Matrix ι ι K) = 0) :
    Submodule.span K (liftMats E) = ⊤ := by
  classical
  have hEne : Nat.card E ≠ 0 := by rw [hcard]; norm_num
  haveI : Finite E := Nat.finite_of_card_ne_zero hEne
  letI : Fintype E := Fintype.ofFinite E
  haveI : Nonempty E := ⟨1⟩
  have hcardE : Fintype.card E = Module.finrank K (Matrix ι ι K) := by
    rw [← Nat.card_eq_fintype_card, hcard, Module.finrank_matrix]
    simp [hι, Module.finrank_self]
  have hli : LinearIndependent K (fun e : E => mat (lift E e)) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc e₀
    have hmul : (mat (lift E e₀))⁻¹ * (∑ e : E, c e • mat (lift E e)) = 0 := by
      rw [hc, mul_zero]
    have hsum : (mat (lift E e₀))⁻¹ * (∑ e : E, c e • mat (lift E e))
        = ∑ e : E, c e • ((mat (lift E e₀))⁻¹ * mat (lift E e)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun e _ => Matrix.mul_smul _ _ _
    have htrace : ∑ e : E, c e * Matrix.trace ((mat (lift E e₀))⁻¹ * mat (lift E e)) = 0 := by
      have h := congrArg Matrix.trace hmul
      rw [hsum, Matrix.trace_sum] at h
      simpa [Matrix.trace_smul, smul_eq_mul] using h
    have hsingle : ∑ e : E, c e * Matrix.trace ((mat (lift E e₀))⁻¹ * mat (lift E e))
        = c e₀ * 4 := by
      rw [Finset.sum_eq_single e₀]
      · have h1 : (mat (lift E e₀))⁻¹ * mat (lift E e₀) = 1 := by
          rw [← mat_inv, ← mat_mul, inv_mul_cancel, mat_one]
        rw [h1, Matrix.trace_one, hι]
        norm_num
      · intro e _ hne
        have hzero : Matrix.trace ((mat (lift E e₀))⁻¹ * mat (lift E e)) = 0 := by
          have hmat : (mat (lift E e₀))⁻¹ * mat (lift E e)
              = ((↑((lift E e₀)⁻¹ * lift E e) : GL ι K) : Matrix ι ι K) := by
            rw [← mat_inv, ← mat_mul]
            rfl
          rw [hmat]
          refine htr ((lift E e₀)⁻¹ * lift E e) ?_ ?_
          · rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, mk_lift, mk_lift]
            exact E.mul_mem (E.inv_mem e₀.2) e.2
          · intro h1
            rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, mk_lift, mk_lift] at h1
            apply hne
            have h2 : (e : CFSG.Open.StatedProj H) = (e₀ : CFSG.Open.StatedProj H) := by
              calc (e : CFSG.Open.StatedProj H)
                  = (e₀ : CFSG.Open.StatedProj H) *
                    ((e₀ : CFSG.Open.StatedProj H)⁻¹ * (e : CFSG.Open.StatedProj H)) := by
                    group
                _ = (e₀ : CFSG.Open.StatedProj H) * 1 := by rw [h1]
                _ = (e₀ : CFSG.Open.StatedProj H) := by simp
            exact Subtype.ext h2
        rw [hzero, mul_zero]
      · intro h
        exact absurd (Finset.mem_univ e₀) h
    have hzero : c e₀ * 4 = 0 := by
      rw [← hsingle]
      exact htrace
    have h4 : (4 : K) ≠ 0 := by
      have h44 : (4 : K) = 2 * 2 := by norm_num
      rw [h44]
      exact mul_ne_zero h2 h2
    exact (mul_eq_zero.mp hzero).resolve_right h4
  have hspanm : Submodule.span K (Set.range (fun e : E => mat (lift E e))) = ⊤ := by
    apply top_le_iff.mp
    intro x _
    have hb := (basisOfLinearIndependentOfCardEqFinrank hli hcardE).mem_span x
    rwa [coe_basisOfLinearIndependentOfCardEqFinrank] at hb
  have hrange_le : Submodule.span K (Set.range (fun e : E => mat (lift E e))) ≤
      Submodule.span K (liftMats E) :=
    Submodule.span_mono (by rintro _ ⟨e, rfl⟩; exact mem_liftMats_lift E e)
  apply le_antisymm le_top
  rw [← hspanm]
  exact hrange_le

private theorem mat_mul_inv_cancel (c : H) : mat c * mat c⁻¹ = 1 := by
  rw [← mat_mul, mul_inv_cancel, mat_one]

private theorem mat_inv_mul_cancel (c : H) : mat c⁻¹ * mat c = 1 := by
  rw [← mat_mul, inv_mul_cancel, mat_one]

private theorem smul_conj_mat {a b : H} {s : Kˣ}
    (hc : mat (a * b) = (s : K) • mat (b * a)) :
    mat a * mat b * (mat a)⁻¹ = (s : K) • mat b := by
  calc mat a * mat b * (mat a)⁻¹
      = mat (a * b) * mat a⁻¹ := by rw [← mat_mul, ← mat_inv]
    _ = ((s : K) • mat (b * a)) * mat a⁻¹ := by rw [hc]
    _ = (s : K) • (mat (b * a) * mat a⁻¹) := Matrix.smul_mul _ _ _
    _ = (s : K) • mat ((b * a) * a⁻¹) := by rw [← mat_mul]
    _ = (s : K) • mat b := by rw [mul_inv_cancel_right]

private theorem inv_mul_eq_smul_mul_inv {a c : H} {s : Kˣ}
    (hc : mat (a * c) = (s : K) • mat (c * a)) :
    mat c⁻¹ * mat a = (s : K) • (mat a * mat c⁻¹) := by
  have h1 : mat a * mat c = (s : K) • (mat c * mat a) := by
    rw [← mat_mul, ← mat_mul]
    exact hc
  have h2 := congrArg (fun X => mat c⁻¹ * X * mat c⁻¹) h1
  calc mat c⁻¹ * mat a
      = mat c⁻¹ * (mat a * mat c) * mat c⁻¹ := by
          rw [← mul_assoc (mat c⁻¹) (mat a) (mat c),
            mul_assoc (mat c⁻¹ * mat a) (mat c) (mat c⁻¹), mat_mul_inv_cancel, mul_one]
    _ = mat c⁻¹ * ((s : K) • (mat c * mat a)) * mat c⁻¹ := h2
    _ = (s : K) • (mat a * mat c⁻¹) := by
          rw [Matrix.mul_smul, Matrix.smul_mul]
          congr 1
          rw [← mul_assoc (mat c⁻¹) (mat c) (mat a), mat_inv_mul_cancel, one_mul]

private theorem commute_mul_inv_of_eq {a b c : H} {s : Kˣ}
    (h1 : mat (a * b) = (s : K) • mat (b * a))
    (h2 : mat (a * c) = (s : K) • mat (c * a)) :
    mat a * (mat b * mat c⁻¹) = (mat b * mat c⁻¹) * mat a := by
  have hc := inv_mul_eq_smul_mul_inv h2
  have hc' : mat a * mat c⁻¹ = ((s : K)⁻¹) • (mat c⁻¹ * mat a) := by
    rw [hc, smul_smul, inv_mul_cancel₀ s.ne_zero, one_smul]
  calc mat a * (mat b * mat c⁻¹)
      = (mat a * mat b) * mat c⁻¹ := by rw [mul_assoc]
    _ = ((s : K) • mat (b * a)) * mat c⁻¹ := by rw [← mat_mul, h1]
    _ = (s : K) • (mat (b * a) * mat c⁻¹) := Matrix.smul_mul _ _ _
    _ = (s : K) • (mat b * (mat a * mat c⁻¹)) := by
          congr 1
          rw [mat_mul, mul_assoc]
    _ = (s : K) • (mat b * (((s : K)⁻¹) • (mat c⁻¹ * mat a))) := by rw [hc']
    _ = (s : K) • (((s : K)⁻¹) • (mat b * (mat c⁻¹ * mat a))) := by rw [Matrix.mul_smul]
    _ = ((s : K) * ((s : K)⁻¹)) • (mat b * (mat c⁻¹ * mat a)) := by rw [smul_smul]
    _ = mat b * (mat c⁻¹ * mat a) := by rw [mul_inv_cancel₀ s.ne_zero, one_smul]
    _ = (mat b * mat c⁻¹) * mat a := by rw [← mul_assoc]

private theorem eq_one_of_commute_lift (E : Subgroup (CFSG.Open.StatedProj H))
    (hspan : Submodule.span K (liftMats E) = ⊤) {a : E}
    (ha : ∀ e : E, mat (lift E a) * mat (lift E e) = mat (lift E e) * mat (lift E a)) :
    a = 1 := by
  have hspan' := span_liftMats_eq_span_lift E hspan
  have hall : ∀ x ∈ Submodule.span K (Set.range (fun e : E => mat (lift E e))),
      mat (lift E a) * x = x * mat (lift E a) := by
    intro x hx
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · rintro y ⟨e, rfl⟩
      exact ha e
    · rw [mul_zero, zero_mul]
    · intro x y hx hy ihx ihy
      rw [Matrix.mul_add, Matrix.add_mul, ihx, ihy]
    · intro c x hx ih
      rw [Matrix.mul_smul, Matrix.smul_mul, ih]
  have hcenter : (lift E a : GL ι K) ∈ Subgroup.center (GL ι K) := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Units.ext
    have hg : (↑g : Matrix ι ι K) ∈
        Submodule.span K (Set.range (fun e : E => mat (lift E e))) := by
      rw [hspan']
      exact Submodule.mem_top
    have hcomm := hall (↑g) hg
    show (↑(g * lift E a) : Matrix ι ι K) = (↑(lift E a * g) : Matrix ι ι K)
    rw [Units.val_mul, Units.val_mul]
    exact hcomm.symm
  have hmem : (lift E a : GL ι K) ∈ StatedScalars ι K := by
    rw [StatedScalars, ← Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact hcenter
  have hone : (QuotientGroup.mk (lift E a) : CFSG.Open.StatedProj H) = 1 := by
    rw [QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.mpr hmem
  have h1 : (a : CFSG.Open.StatedProj H) = 1 := by
    rw [← mk_lift E a, hone]
  exact Subtype.ext h1

private theorem fun_eq_of_sum_smul_eq {κ : Type*} [Fintype κ]
    {v : κ → Matrix ι ι K} (hli : LinearIndependent K v) {c d : κ → K}
    (h : ∑ i, c i • v i = ∑ i, d i • v i) : c = d := by
  funext i
  have h0 : ∑ j, (c j - d j) • v j = 0 := by
    have hsub : ∑ j, (c j - d j) • v j = ∑ j, c j • v j - ∑ j, d j • v j := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => sub_smul (c j) (d j) (v j)
    rw [hsub, h, sub_self]
  have hpoint := Fintype.linearIndependent_iff.mp hli (fun j => c j - d j) h0 i
  exact sub_eq_zero.mp hpoint

theorem centralizer_le_of_span_liftMats {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    {H : Subgroup (GL ι K)} {E : Subgroup (CFSG.Open.StatedProj H)}
    (hE : CFSG.Open.IsElemAbelian 2 E) (hcard : Nat.card E = Fintype.card ι ^ 2)
    (hspan : Submodule.span K (liftMats E) = ⊤) :
    Subgroup.centralizer (E : Set (CFSG.Open.StatedProj H)) ≤ E := by
  classical
  by_cases hι0 : Fintype.card ι = 0
  · haveI : IsEmpty ι := Fintype.card_eq_zero_iff.mp hι0
    haveI : Subsingleton (GL ι K) := by
      constructor
      intro u v
      exact Units.ext (by ext i; exact (IsEmpty.false i).elim)
    haveI : Subsingleton (CFSG.Open.StatedProj H) := by
      refine ⟨fun a b => ?_⟩
      induction a using Quotient.inductionOn with
      | h x =>
        induction b using Quotient.inductionOn with
        | h y => rw [Subsingleton.elim x y]
    have h1 : Nat.card E = 1 := Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1⟩⟩
    rw [hcard, hι0] at h1
    omega
  · have hιpos : 0 < Fintype.card ι := Nat.pos_of_ne_zero hι0
    haveI : Nonempty ι := Fintype.card_pos_iff.mp hιpos
    have hEne : Nat.card E ≠ 0 := by rw [hcard]; positivity
    haveI : Finite E := Nat.finite_of_card_ne_zero hEne
    letI : Fintype E := Fintype.ofFinite E
    haveI : Nonempty E := ⟨1⟩
    have hcardE : Fintype.card E = Module.finrank K (Matrix ι ι K) := by
      rw [← Nat.card_eq_fintype_card, hcard, Module.finrank_matrix]
      simp [Module.finrank_self, pow_two]
    have hspan' := span_liftMats_eq_span_lift E hspan
    have hli : LinearIndependent K (fun e : E => mat (lift E e)) :=
      linearIndependent_of_top_le_span_of_card_eq_finrank hspan'.ge hcardE
    let b := basisOfLinearIndependentOfCardEqFinrank hli hcardE
    have hbrepr : ∀ x : Matrix ι ι K, ∑ e : E, (b.repr x) e • mat (lift E e) = x := by
      intro x
      have hb : ⇑b = fun e : E => mat (lift E e) :=
        coe_basisOfLinearIndependentOfCardEqFinrank hli hcardE
      simpa only [hb] using b.sum_repr x
    intro x hx
    let xhat : H := Quotient.out x
    have hxhat : (QuotientGroup.mk xhat : CFSG.Open.StatedProj H) = x := QuotientGroup.out_eq' x
    have hcomm (e : E) : (QuotientGroup.mk (xhat * lift E e) : CFSG.Open.StatedProj H) =
        QuotientGroup.mk (lift E e * xhat) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, hxhat, mk_lift]
      exact ((Subgroup.mem_centralizer_iff.mp hx) (e : CFSG.Open.StatedProj H) e.2).symm
    choose χ hχ using fun e : E => exists_scalar_of_mk_eq (hcomm e)
    have hcommβ (e f : E) : (QuotientGroup.mk (lift E e * lift E f) :
        CFSG.Open.StatedProj H) = QuotientGroup.mk (lift E f * lift E e) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, mk_lift, mk_lift]
      simpa using congrArg Subtype.val (hE.1.is_comm.comm e f)
    choose β hβ using fun e f : E => exists_scalar_of_mk_eq (hcommβ e f)
    let c : E → K := fun f => (b.repr (mat xhat)) f
    have hxsum : ∑ f : E, c f • mat (lift E f) = mat xhat := by
      simpa only [c] using hbrepr (mat xhat)
    have hxhat0 : mat xhat ≠ 0 := by
      intro h0
      have h1 : mat xhat * mat xhat⁻¹ = 1 := mat_mul_inv_cancel xhat
      rw [h0, zero_mul] at h1
      exact zero_ne_one h1
    have hconj (e : E) : mat xhat = (χ e : K) • mat (lift E e * xhat * (lift E e)⁻¹) := by
      calc mat xhat = mat ((xhat * lift E e) * (lift E e)⁻¹) := by
              rw [mul_assoc, mul_inv_cancel, mul_one]
        _ = mat (xhat * lift E e) * mat (lift E e)⁻¹ := by rw [← mat_mul]
        _ = mat (xhat * lift E e) * (mat (lift E e))⁻¹ := by rw [mat_inv]
        _ = ((χ e : K) • mat (lift E e * xhat)) * (mat (lift E e))⁻¹ := by rw [hχ e]
        _ = (χ e : K) • (mat (lift E e * xhat) * (mat (lift E e))⁻¹) := Matrix.smul_mul _ _ _
        _ = (χ e : K) • mat ((lift E e * xhat) * (lift E e)⁻¹) := by rw [← mat_inv, ← mat_mul]
    have hmain (e : E) : ∑ f : E, c f • mat (lift E f)
        = ∑ f : E, (χ e * c f * β e f) • mat (lift E f) := by
      have hstep (f : E) : mat (lift E e) * mat (lift E f) * (mat (lift E e))⁻¹
          = (β e f : K) • mat (lift E f) := smul_conj_mat (hβ e f)
      have hdist : mat (lift E e) * (∑ f : E, c f • mat (lift E f)) *
            (mat (lift E e))⁻¹
          = ∑ f : E, c f • (mat (lift E e) * mat (lift E f) * (mat (lift E e))⁻¹) := by
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun f _ => ?_
        rw [Matrix.mul_smul, Matrix.smul_mul]
      calc ∑ f : E, c f • mat (lift E f)
          = mat xhat := hxsum
        _ = (χ e : K) • mat (lift E e * xhat * (lift E e)⁻¹) := hconj e
        _ = (χ e : K) • (mat (lift E e) * mat xhat * (mat (lift E e))⁻¹) := by
              rw [mat_mul, mat_mul, mat_inv]
        _ = (χ e : K) • (mat (lift E e) * (∑ f : E, c f • mat (lift E f)) *
              (mat (lift E e))⁻¹) := by rw [← hxsum]
        _ = (χ e : K) • ∑ f : E, c f •
              (mat (lift E e) * mat (lift E f) * (mat (lift E e))⁻¹) := by rw [hdist]
        _ = (χ e : K) • ∑ f : E, c f • ((β e f : K) • mat (lift E f)) := by
              congr 1
              exact Finset.sum_congr rfl fun f _ => by rw [hstep f]
        _ = ∑ f : E, (χ e * c f * β e f) • mat (lift E f) := by
              rw [Finset.smul_sum]
              refine Finset.sum_congr rfl fun f _ => ?_
              rw [smul_smul, smul_smul]
    have hcoeff (e : E) : ∀ f : E, c f = χ e * c f * β e f := by
      intro f
      exact congrFun (fun_eq_of_sum_smul_eq hli (hmain e)) f
    have hprod (e f : E) (hf : c f ≠ 0) : (χ e : K) * (β e f : K) = 1 := by
      have h := hcoeff e f
      have h' : c f = c f * ((χ e : K) * (β e f : K)) := by
        calc c f = (χ e : K) * c f * (β e f : K) := h
          _ = c f * ((χ e : K) * (β e f : K)) := by ring
      have h1 : c f * ((χ e : K) * (β e f : K)) = c f * 1 := by
        rw [mul_one]
        exact h'.symm
      exact mul_left_cancel₀ hf h1
    obtain ⟨g, hg⟩ : ∃ g : E, c g ≠ 0 := by
      by_contra h
      have h' : ∀ g : E, c g = 0 := by
        intro g
        by_contra hg
        exact h ⟨g, hg⟩
      apply hxhat0
      rw [← hxsum]
      simp [h']
    have hβ_eq (e : E) {f : E} (hf : c f ≠ 0) : (β e f : K) = (β e g : K) := by
      have h1 := hprod e f hf
      have h2 := hprod e g hg
      have hχ0 : (χ e : K) ≠ 0 := by
        intro h0
        rw [h0, zero_mul] at h1
        exact zero_ne_one h1
      exact mul_left_cancel₀ hχ0 (h1.trans h2.symm)
    have hfg (f : E) (hf : c f ≠ 0) : f = g := by
      have hcommfg : ∀ e : E, mat (lift E (f * g⁻¹)) * mat (lift E e) =
          mat (lift E e) * mat (lift E (f * g⁻¹)) := by
        intro e
        have hmk : (QuotientGroup.mk (lift E (f * g⁻¹)) : CFSG.Open.StatedProj H) =
            QuotientGroup.mk (lift E f * (lift E g)⁻¹) := by
          rw [mk_lift, QuotientGroup.mk_mul, QuotientGroup.mk_inv, mk_lift, mk_lift,
            Subgroup.coe_mul, Subgroup.coe_inv]
        obtain ⟨μ, hμ⟩ := exists_scalar_of_mk_eq hmk
        have hbase : mat (lift E f * (lift E g)⁻¹) =
            mat (lift E f) * (mat (lift E g))⁻¹ := by rw [mat_mul, mat_inv]
        have hcommA : (mat (lift E f) * (mat (lift E g))⁻¹) * mat (lift E e) =
            mat (lift E e) * (mat (lift E f) * (mat (lift E g))⁻¹) := by
          have h2' : mat (lift E e * lift E g) =
              (β e f : K) • mat (lift E g * lift E e) := by
            rw [hβ_eq e hf]
            exact hβ e g
          have h := commute_mul_inv_of_eq (hβ e f) h2'
          rw [mat_inv] at h
          exact h.symm
        have hcommA' : mat (lift E f * (lift E g)⁻¹) * mat (lift E e) =
            mat (lift E e) * mat (lift E f * (lift E g)⁻¹) := by
          rw [hbase]
          exact hcommA
        calc mat (lift E (f * g⁻¹)) * mat (lift E e)
            = ((μ : K) • mat (lift E f * (lift E g)⁻¹)) * mat (lift E e) := by rw [hμ]
          _ = (μ : K) • (mat (lift E f * (lift E g)⁻¹) * mat (lift E e)) :=
                Matrix.smul_mul (μ : K) _ _
          _ = (μ : K) • (mat (lift E e) * mat (lift E f * (lift E g)⁻¹)) := by rw [hcommA']
          _ = mat (lift E e) * ((μ : K) • mat (lift E f * (lift E g)⁻¹)) :=
                (Matrix.mul_smul _ (μ : K) _).symm
          _ = mat (lift E e) * mat (lift E (f * g⁻¹)) := by rw [hμ]
      have h1 : f * g⁻¹ = 1 := eq_one_of_commute_lift E hspan hcommfg
      exact mul_inv_eq_one.mp h1
    have hsupp (f : E) (hf : f ≠ g) : c f = 0 := by
      by_contra hc0
      exact hf (hfg f hc0)
    have hxsumg : ∑ f : E, c f • mat (lift E f) = c g • mat (lift E g) := by
      rw [Finset.sum_eq_single g]
      · intro b _ hb
        rw [hsupp b hb, zero_smul]
      · intro h
        exact absurd (Finset.mem_univ g) h
    have hxg : mat xhat = (c g : K) • mat (lift E g) := by
      rw [← hxsum, hxsumg]
    have hx_eq : (QuotientGroup.mk xhat : CFSG.Open.StatedProj H) =
        QuotientGroup.mk (lift E g) :=
      mk_eq_of_scalar_mul (c := Units.mk0 (c g) hg) (by simpa using hxg)
    rw [← hxhat, hx_eq, mk_lift]
    exact g.2

private theorem scalar_injective [Nonempty ι] :
    Function.Injective (Matrix.GeneralLinearGroup.scalar ι : Kˣ →* GL ι K) := by
  intro c d hcd
  obtain ⟨i⟩ := ‹Nonempty ι›
  apply Units.ext
  have hentry := congrArg (fun M : GL ι K => (M : Matrix ι ι K) i i) hcd
  simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] using hentry

private theorem commute_of_mem_scalars {x : H}
    (hx : (x : GL ι K) ∈ StatedScalars ι K) (h : H) : x * h = h * x := by
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp hx
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul]
  apply Units.ext
  change ((x : GL ι K) : Matrix ι ι K) * ((h : GL ι K) : Matrix ι ι K) =
    ((h : GL ι K) : Matrix ι ι K) * ((x : GL ι K) : Matrix ι ι K)
  rw [← hc, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, one_mul, Matrix.mul_smul, mul_one]

private theorem commutator_mul_central (G : Type*) [Group G] {z : G}
    (hz : z ∈ Subgroup.center G) (a x : G) :
    a * (z * x) * a⁻¹ * (z * x)⁻¹ = a * x * a⁻¹ * x⁻¹ := by
  have hz' : ∀ y : G, y * z = z * y := fun y => Subgroup.mem_center_iff.mp hz y
  calc a * (z * x) * a⁻¹ * (z * x)⁻¹
      = a * z * x * a⁻¹ * (x⁻¹ * z⁻¹) := by rw [_root_.mul_inv_rev]; group
    _ = z * (a * x * a⁻¹ * x⁻¹) * z⁻¹ := by rw [hz' a]; group
    _ = a * x * a⁻¹ * x⁻¹ := by rw [← hz' (a * x * a⁻¹ * x⁻¹)]; group

private theorem commutator_mul_eq (G : Type*) [Group G] {x y z : G}
    (hz : x * z * x⁻¹ * z⁻¹ ∈ Subgroup.center G) :
    x * (y * z) * x⁻¹ * (y * z)⁻¹ =
      (x * y * x⁻¹ * y⁻¹) * (x * z * x⁻¹ * z⁻¹) := by
  have hcy : y * (x * z * x⁻¹ * z⁻¹) * y⁻¹ = x * z * x⁻¹ * z⁻¹ := by
    have hcomm := Subgroup.mem_center_iff.mp hz y
    rw [hcomm]
    group
  calc x * (y * z) * x⁻¹ * (y * z)⁻¹
      = (x * y * x⁻¹ * y⁻¹) * (y * (x * z * x⁻¹ * z⁻¹) * y⁻¹) := by group
    _ = (x * y * x⁻¹ * y⁻¹) * (x * z * x⁻¹ * z⁻¹) := by rw [hcy]

private lemma zpow_smul_eq_self {G α : Type*} [Group G] [MulAction G α]
    {g : G} {a : α} (h : g • a = a) : ∀ k : ℤ, (g ^ k) • a = a := by
  have h1 : g⁻¹ • a = a := by
    have := congrArg (fun y => g⁻¹ • y) h
    simpa [← mul_smul] using this.symm
  intro k
  induction k using Int.induction_on with
  | zero => simp
  | succ n ih =>
      rw [_root_.zpow_add, zpow_natCast, zpow_one, mul_smul, h]
      simpa using ih
  | pred n ih =>
      have hk : (-(n : ℤ) - 1) = -(n : ℤ) + (-1) := by ring
      rw [hk, _root_.zpow_add, _root_.zpow_neg_one, mul_smul, h1, ih]

theorem conj_eq_of_pow_seven_of_span_liftMats {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    {H : Subgroup (GL ι K)} {E : Subgroup (CFSG.Open.StatedProj H)}
    (hE : CFSG.Open.IsElemAbelian 2 E) (hcard : Nat.card E = 16)
    (hspan : Submodule.span K (liftMats E) = ⊤) :
    ∀ n ∈ Subgroup.normalizer (E : Set (CFSG.Open.StatedProj H)),
      (∀ e ∈ E, n ^ 7 * e * (n ^ 7)⁻¹ = e) → ∀ e ∈ E, n * e * n⁻¹ = e := by
  classical
  intro n hn hn7 e he
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  haveI hne : Nonempty ι := by
    by_contra hι
    rw [not_nonempty_iff] at hι
    haveI : IsEmpty ι := hι
    haveI : Subsingleton (GL ι K) := by
      constructor
      intro u v
      exact Units.ext (by ext i; exact (IsEmpty.false i).elim)
    haveI : Subsingleton (CFSG.Open.StatedProj H) := by
      refine ⟨fun a b => ?_⟩
      induction a using Quotient.inductionOn with
      | h x =>
        induction b using Quotient.inductionOn with
        | h y => rw [Subsingleton.elim x y]
    have h1 : Nat.card E = 1 := Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1⟩⟩
    omega
  have hEne : Nat.card E ≠ 0 := by rw [hcard]; norm_num
  haveI : Finite E := Nat.finite_of_card_ne_zero hEne
  letI : Fintype E := Fintype.ofFinite E
  have hmap : E.map (MulAut.conj n).toMonoidHom = E :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hn
  let σ : MulAut E :=
    (Subgroup.equivMapOfInjective E (MulAut.conj n).toMonoidHom
      (MulAut.conj n).injective).trans (MulEquiv.subgroupCongr hmap)
  have hσ_apply : ∀ x : E, (σ x : CFSG.Open.StatedProj H) =
      n * (x : CFSG.Open.StatedProj H) * n⁻¹ := by
    intro x
    rfl
  have hpow : ∀ (k : ℕ) (x : E), ((σ ^ k) x : CFSG.Open.StatedProj H) =
      n ^ k * (x : CFSG.Open.StatedProj H) * (n ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
        intro x
        rw [pow_succ']
        change ((σ : MulAut E) ((σ ^ k) x) : CFSG.Open.StatedProj H) = _
        rw [hσ_apply, ih, pow_succ']
        group
  have hσ7 : σ ^ 7 = 1 := by
    ext x
    rw [hpow 7 x]
    exact hn7 (x : CFSG.Open.StatedProj H) x.2
  by_cases hσ1 : σ = 1
  · have hx : σ ⟨e, he⟩ = ⟨e, he⟩ := by rw [hσ1]; rfl
    have hval := congrArg Subtype.val hx
    rw [hσ_apply ⟨e, he⟩] at hval
    exact hval
  · exfalso
    let P : Subgroup (MulAut E) := Subgroup.zpowers σ
    letI : MulAction P E := MulAction.compHom E P.subtype
    have hPcard : Nat.card P = 7 := by
      have horder : orderOf σ = 7 := orderOf_eq_prime hσ7 hσ1
      rw [show P = Subgroup.zpowers σ from rfl, Nat.card_zpowers, horder]
    have hPis : IsPGroup 7 P := IsPGroup.of_card (n := 1) (by rw [hPcard]; norm_num)
    have hfix_iff : ∀ x : E, x ∈ MulAction.fixedPoints P E ↔ σ x = x := by
      intro x
      rw [MulAction.mem_fixedPoints]
      constructor
      · intro h
        have h1 := h ⟨σ, Subgroup.mem_zpowers σ⟩
        have h2 : (σ : MulAut E) • x = x := h1
        rwa [MulAut.smul_def] at h2
      · intro h g
        have hg : (g : MulAut E) ∈ Subgroup.zpowers σ := g.2
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hg
        change ((g : MulAut E) • x) = x
        rw [← hk]
        exact zpow_smul_eq_self (g := (σ : MulAut E)) (a := x)
          (by rwa [MulAut.smul_def]) k
    let C : Subgroup E :=
      (Subgroup.centralizer ({n} : Set (CFSG.Open.StatedProj H))).comap E.subtype
    have hC_fix : ∀ x : E, x ∈ C ↔ σ x = x := by
      intro x
      rw [show C = _ from rfl, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
      constructor
      · intro h
        have h' : (x : CFSG.Open.StatedProj H) * n = n * (x : CFSG.Open.StatedProj H) := h
        apply Subtype.ext
        rw [hσ_apply x, ← h']
        group
      · intro h
        have h' := congrArg Subtype.val h
        rw [hσ_apply x] at h'
        have h'' : n * (x : CFSG.Open.StatedProj H) * n⁻¹ = (x : CFSG.Open.StatedProj H) := h'
        have hc := congrArg (fun y => y * n) h''
        simpa [mul_assoc] using hc.symm
    have hset : (MulAction.fixedPoints P E : Set E) = (C : Set E) := by
      ext x
      exact (hfix_iff x).trans (hC_fix x).symm
    have hcardFix : Nat.card (MulAction.fixedPoints P E) = Nat.card C := by
      rw [hset]
      rfl
    have hmod : Nat.card E ≡ Nat.card (MulAction.fixedPoints P E) [MOD 7] :=
      hPis.card_modEq_card_fixedPoints E
    have hmodC : Nat.card C ≡ 2 [MOD 7] := by
      rw [hcardFix, hcard] at hmod
      exact hmod.symm.trans (by decide)
    have hCdvd : Nat.card C ∣ 16 := by
      have h := Subgroup.card_eq_card_quotient_mul_card_subgroup C
      rw [hcard] at h
      exact ⟨_, by rw [mul_comm]; exact h⟩
    have h16 : (16 : ℕ) = 2 ^ 4 := by norm_num
    obtain ⟨k, hk4, hk⟩ :=
      (Nat.dvd_prime_pow Nat.prime_two (m := 4) (i := Nat.card C)).mp (by
        rw [← h16]; exact hCdvd)
    have hkmod : 2 ^ k ≡ 2 [MOD 7] := by rw [← hk]; exact hmodC
    have hkcases : k = 1 ∨ k = 4 := by
      interval_cases k
      · norm_num at hkmod
      · left; rfl
      · norm_num at hkmod
      · norm_num at hkmod
      · right; rfl
    rcases hkcases with rfl | rfl
    ·
      have hCcard : Nat.card C = 2 := by simpa using hk
      have hCne : C ≠ ⊥ := by
        intro hbot
        have h1 : Nat.card C = 1 := by rw [hbot, Subgroup.card_bot]
        omega
      obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hCne
      have haC : (a : E) ∈ C := a.2
      have hafix : σ (a : E) = (a : E) := (hC_fix (a : E)).mp haC
      have ha_ne_one : (a : E) ≠ 1 := by
        intro h
        exact ha1 (Subtype.ext h)
      have ha2 : ((a : E) : CFSG.Open.StatedProj H) ^ 2 = 1 := hE.2 (a : E) (a : E).2
      obtain ⟨x, y, hxy, huniv⟩ := Nat.card_eq_two_iff.mp hCcard
      have h1mem : (1 : C) ∈ ({x, y} : Set C) := by rw [huniv]; exact Set.mem_univ _
      have hamem : a ∈ ({x, y} : Set C) := by rw [huniv]; exact Set.mem_univ _
      have hpair : ({1, a} : Set C) = Set.univ := by
        have hsub : ({1, a} : Set C) ⊆ ({x, y} : Set C) := by
          intro z hz
          rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
          rcases hz with rfl | rfl
          · exact h1mem
          · exact hamem
        have heq : ({1, a} : Set C) = ({x, y} : Set C) := by
          apply Set.eq_of_subset_of_ncard_le hsub
          rw [Set.ncard_pair hxy, Set.ncard_pair (Ne.symm ha1)]
        rw [heq, huniv]
      have hCmem : ∀ z : E, z ∈ C → z = 1 ∨ z = (a : E) := by
        intro z hz
        have hzC : (⟨z, hz⟩ : C) ∈ ({1, a} : Set C) := by
          rw [hpair]; exact Set.mem_univ _
        rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hzC
        rcases hzC with h | h
        · left; simpa using congrArg Subtype.val h
        · right; simpa using congrArg Subtype.val h
      let cfun : E → H := fun e =>
        lift E (a : E) * lift E e * (lift E (a : E))⁻¹ * (lift E e)⁻¹
      have hcfun_mem (e : E) : (cfun e : GL ι K) ∈ StatedScalars ι K := by
        have h1 : (QuotientGroup.mk (cfun e) : CFSG.Open.StatedProj H) = 1 := by
          simp only [cfun]
          rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
            QuotientGroup.mk_inv, QuotientGroup.mk_inv, mk_lift, mk_lift]
          have hcomm : (e : CFSG.Open.StatedProj H) * ((a : E) : CFSG.Open.StatedProj H) =
              ((a : E) : CFSG.Open.StatedProj H) * (e : CFSG.Open.StatedProj H) :=
            congrArg Subtype.val (hE.1.is_comm.comm e (a : E))
          rw [← hcomm]
          group
        rw [QuotientGroup.eq_one_iff] at h1
        exact Subgroup.mem_subgroupOf.mp h1
      have hcfun_one : cfun 1 = 1 := by
        have hmem1 : ((lift E (1 : E) : H) : GL ι K) ∈ StatedScalars ι K := by
          have h1 : (QuotientGroup.mk (lift E (1 : E)) : CFSG.Open.StatedProj H) = 1 := by
            rw [mk_lift]; rfl
          rw [QuotientGroup.eq_one_iff] at h1
          exact Subgroup.mem_subgroupOf.mp h1
        have hcomm : lift E (a : E) * lift E (1 : E) = lift E (1 : E) * lift E (a : E) :=
          (commute_of_mem_scalars hmem1 _).symm
        simp only [cfun]
        rw [hcomm]
        group
      have hcfun_mul (e f : E) : cfun (e * f) = cfun e * cfun f := by
        let u : H := lift E (e * f) * (lift E e * lift E f)⁻¹
        have hu_scalar : (u : GL ι K) ∈ StatedScalars ι K := by
          have h1 : (QuotientGroup.mk u : CFSG.Open.StatedProj H) = 1 := by
            simp only [u]
            rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_mul,
              mk_lift, mk_lift, mk_lift]
            rw [Subgroup.coe_mul]
            group
          rw [QuotientGroup.eq_one_iff] at h1
          exact Subgroup.mem_subgroupOf.mp h1
        have hu_center : u ∈ Subgroup.center H := by
          rw [Subgroup.mem_center_iff]
          intro h
          exact (commute_of_mem_scalars hu_scalar h).symm
        have hs : lift E (e * f) = u * (lift E e * lift E f) := by
          simp only [u]; group
        have hcentral : cfun f ∈ Subgroup.center H := by
          rw [Subgroup.mem_center_iff]
          intro h
          exact (commute_of_mem_scalars (hcfun_mem f) h).symm
        simp only [cfun]
        rw [hs]
        calc lift E (a : E) * (u * (lift E e * lift E f)) * (lift E (a : E))⁻¹ *
              (u * (lift E e * lift E f))⁻¹
            = lift E (a : E) * (lift E e * lift E f) * (lift E (a : E))⁻¹ *
                (lift E e * lift E f)⁻¹ := commutator_mul_central H hu_center _ _
          _ = (lift E (a : E) * lift E e * (lift E (a : E))⁻¹ * (lift E e)⁻¹) *
                (lift E (a : E) * lift E f * (lift E (a : E))⁻¹ * (lift E f)⁻¹) :=
                commutator_mul_eq H hcentral
          _ = cfun e * cfun f := by simp only [cfun]
      let D : Subgroup E :=
        { carrier := {e | cfun e = 1}
          one_mem' := hcfun_one
          mul_mem' := fun {a b} ha hb => by
            change cfun (a * b) = 1
            rw [hcfun_mul, show cfun a = 1 from ha, show cfun b = 1 from hb, mul_one]
          inv_mem' := fun {e} he => by
            change cfun e⁻¹ = 1
            have h := hcfun_mul e e⁻¹
            rw [mul_inv_cancel, hcfun_one] at h
            rw [show cfun e = 1 from he, one_mul] at h
            exact h.symm }
      have hDmem : ∀ e : E, e ∈ D ↔ cfun e = 1 := fun e => Iff.rfl
      let γ : E → Kˣ := fun e => Classical.choose (hcfun_mem e)
      have hγ : ∀ e : E, (cfun e : GL ι K) = Matrix.GeneralLinearGroup.scalar ι (γ e) :=
        fun e => (Classical.choose_spec (hcfun_mem e)).symm
      have hγ_one : γ 1 = 1 := by
        apply scalar_injective (ι := ι)
        rw [← hγ 1, hcfun_one, Subgroup.coe_one, map_one]
      have hγ_mul : ∀ e f : E, γ (e * f) = γ e * γ f := by
        intro e f
        apply scalar_injective (ι := ι)
        rw [← hγ (e * f)]
        change (cfun (e * f) : GL ι K) = Matrix.GeneralLinearGroup.scalar ι (γ e * γ f)
        rw [show (cfun (e * f) : GL ι K) = (cfun e : GL ι K) * (cfun f : GL ι K) by
          rw [hcfun_mul, Subgroup.coe_mul]]
        rw [hγ e, hγ f, ← map_mul]
      let φ : E →* Kˣ := MonoidHom.mk' γ hγ_mul
      have hφ_apply : ∀ e : E, φ e = γ e := fun e => rfl
      have hDker : D = φ.ker := by
        ext e
        rw [hDmem, MonoidHom.mem_ker, hφ_apply]
        constructor
        · intro h
          apply scalar_injective (ι := ι)
          rw [← hγ e, show ((cfun e : H) : GL ι K) = 1 by rw [h]; rfl, map_one]
        · intro h
          apply Subtype.ext
          rw [hγ e, h, map_one]
          rfl
      have hφ_ne_one : φ ≠ 1 := by
        intro hφ1
        have hall : ∀ e : E, cfun e = 1 := by
          intro e
          have h1 : γ e = 1 := by
            have := congrArg (fun f : E →* Kˣ => f e) hφ1
            simpa [hφ_apply] using this
          apply Subtype.ext
          rw [hγ e, h1, map_one]
          rfl
        have haeq : (a : E) = 1 := by
          apply eq_one_of_commute_lift E hspan (a := (a : E))
          intro e
          have h1 : cfun e = 1 := hall e
          have h2 : lift E (a : E) * lift E e = lift E e * lift E (a : E) := by
            have h := h1
            simp only [cfun] at h
            calc lift E (a : E) * lift E e
                = (lift E (a : E) * lift E e * (lift E (a : E))⁻¹ * (lift E e)⁻¹) *
                    (lift E e * lift E (a : E)) := by group
              _ = lift E e * lift E (a : E) := by rw [h, one_mul]
          rw [← mat_mul, ← mat_mul, h2]
        exact ha_ne_one haeq
      have hφ_pow_two (e : E) : (φ e) ^ 2 = 1 := by
        have he2 : e ^ 2 = 1 := by
          apply Subtype.ext
          rw [Subgroup.coe_pow, Subgroup.coe_one]
          exact hE.2 e e.2
        rw [← map_pow, he2, map_one]
      have hφ_range_le : φ.range ≤ Subgroup.zpowers (-1 : Kˣ) := by
        rintro z ⟨e, rfl⟩
        have hval : ((φ e : Kˣ) : K) ^ 2 = 1 := by
          simpa using congrArg (fun u : Kˣ => (u : K)) (hφ_pow_two e)
        rcases sq_eq_one_iff.mp hval with h | h
        · have hφe : φ e = 1 := Units.ext (by simpa using h)
          rw [hφe]
          exact Subgroup.mem_zpowers_iff.mpr ⟨0, by simp⟩
        · have hφe : φ e = -1 := Units.ext (by simpa using h)
          rw [hφe]
          exact Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩
      have hrange_ne_bot : φ.range ≠ ⊥ := by
        intro hbot
        apply hφ_ne_one
        ext e
        have hmem : φ e ∈ φ.range := MonoidHom.mem_range.mpr ⟨e, rfl⟩
        rw [hbot, Subgroup.mem_bot] at hmem
        simpa using hmem
      have hzpowers_finite : Finite ↥(Subgroup.zpowers (-1 : Kˣ)) := by
        have hdvd : orderOf (-1 : Kˣ) ∣ 2 :=
          orderOf_dvd_iff_pow_eq_one.mpr (by simp)
        have hpos : 0 < orderOf (-1 : Kˣ) := Nat.pos_of_dvd_of_pos hdvd (by norm_num)
        exact Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers]; omega)
      have hrange_finite : Finite φ.range :=
        Finite.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
      have hrange_card : Nat.card φ.range = 2 := by
        haveI : Finite φ.range := hrange_finite
        haveI : Finite ↥(Subgroup.zpowers (-1 : Kˣ)) := hzpowers_finite
        have hle : Nat.card φ.range ≤ 2 := by
          calc Nat.card φ.range ≤ Nat.card ↥(Subgroup.zpowers (-1 : Kˣ)) :=
                Subgroup.card_le_of_le hφ_range_le
            _ ≤ 2 := by
                rw [Nat.card_zpowers]
                exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_iff_pow_eq_one.mpr (by simp))
        have hgt : 1 < Nat.card φ.range :=
          (Subgroup.one_lt_card_iff_ne_bot φ.range).mpr hrange_ne_bot
        omega
      have hDcard : Nat.card D = 8 := by
        have h1 : Nat.card E = Nat.card (E ⧸ φ.ker) * Nat.card φ.ker :=
          Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
        have h2 : Nat.card (E ⧸ φ.ker) = Nat.card φ.range :=
          Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
        have h3 : Nat.card φ.ker = Nat.card D := by rw [hDker]
        rw [hcard, h2, hrange_card, h3] at h1
        omega
      have haX : n * ((a : E) : CFSG.Open.StatedProj H) * n⁻¹ =
          ((a : E) : CFSG.Open.StatedProj H) := by
        have := congrArg Subtype.val hafix
        rwa [hσ_apply (a : E)] at this
      have hCD : C ≤ D := by
        intro z hz
        rcases hCmem z hz with rfl | rfl
        · exact D.one_mem
        · rw [hDmem]
          simp only [cfun]
          group
      have hDinv : ∀ d : D, σ (d : E) ∈ D := by
        intro d
        let nhat : H := Quotient.out n
        have hnhat : (QuotientGroup.mk nhat : CFSG.Open.StatedProj H) = n :=
          QuotientGroup.out_eq' n
        let wd : H := nhat * lift E (d : E) * nhat⁻¹
        let wa : H := nhat * lift E (a : E) * nhat⁻¹
        have hwd_mk : (QuotientGroup.mk wd : CFSG.Open.StatedProj H) =
            ((σ (d : E) : E) : CFSG.Open.StatedProj H) := by
          simp only [wd]
          rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hnhat,
            mk_lift, hσ_apply (d : E)]
        have hwa_mk : (QuotientGroup.mk wa : CFSG.Open.StatedProj H) =
            ((a : E) : CFSG.Open.StatedProj H) := by
          simp only [wa]
          rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hnhat,
            mk_lift, haX]
        have hcomm_d : lift E (a : E) * lift E (d : E) = lift E (d : E) * lift E (a : E) := by
          have h := (hDmem (d : E)).mp d.2
          simp only [cfun] at h
          calc lift E (a : E) * lift E (d : E)
              = (lift E (a : E) * lift E (d : E) * (lift E (a : E))⁻¹ *
                  (lift E (d : E))⁻¹) * (lift E (d : E) * lift E (a : E)) := by group
            _ = lift E (d : E) * lift E (a : E) := by rw [h, one_mul]
        have hw : wd * wa = wa * wd := by
          simp only [wd, wa]
          calc (nhat * lift E (d : E) * nhat⁻¹) * (nhat * lift E (a : E) * nhat⁻¹)
              = nhat * (lift E (d : E) * lift E (a : E)) * nhat⁻¹ := by group
            _ = nhat * (lift E (a : E) * lift E (d : E)) * nhat⁻¹ := by rw [← hcomm_d]
            _ = (nhat * lift E (a : E) * nhat⁻¹) * (nhat * lift E (d : E) * nhat⁻¹) := by group
        obtain ⟨μd, hμd⟩ := exists_scalar_of_mk_eq
          (h₁ := wd) (h₂ := lift E (σ (d : E))) (by rw [hwd_mk, mk_lift])
        obtain ⟨μa, hμa⟩ := exists_scalar_of_mk_eq
          (h₁ := wa) (h₂ := lift E (a : E)) (by rw [hwa_mk, mk_lift])
        have hmatw : mat wd * mat wa = mat wa * mat wd := by
          rw [← mat_mul, ← mat_mul, hw]
        rw [hμd, hμa, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
          smul_smul, smul_smul] at hmatw
        have hμ0 : ((μd : K) * (μa : K)) ≠ 0 := mul_ne_zero μd.ne_zero μa.ne_zero
        have hcommσ : mat (lift E (a : E)) * mat (lift E (σ (d : E))) =
            mat (lift E (σ (d : E))) * mat (lift E (a : E)) := by
          have h := hmatw
          rw [mul_comm (μa : K) (μd : K)] at h
          exact ((smul_right_inj hμ0).mp h).symm
        have hcommH : lift E (a : E) * lift E (σ (d : E)) =
            lift E (σ (d : E)) * lift E (a : E) := by
          apply Subtype.ext
          apply Units.ext
          rw [show ((↑(lift E (a : E) * lift E (σ (d : E))) : GL ι K) : Matrix ι ι K) =
              mat (lift E (a : E)) * mat (lift E (σ (d : E))) from mat_mul _ _]
          rw [show ((↑(lift E (σ (d : E)) * lift E (a : E)) : GL ι K) : Matrix ι ι K) =
              mat (lift E (σ (d : E))) * mat (lift E (a : E)) from mat_mul _ _]
          exact hcommσ
        rw [hDmem]
        change cfun (σ (d : E)) = 1
        simp only [cfun]
        rw [hcommH]
        group
      have hDmap : D.map σ.toMonoidHom = D := by
        apply Subgroup.eq_of_le_of_card_ge
        · rintro _ ⟨d, hd, rfl⟩
          exact hDinv ⟨d, hd⟩
        · rw [Nat.card_congr (Subgroup.equivMapOfInjective D σ.toMonoidHom σ.injective).toEquiv]
      let σD : MulAut D :=
        (Subgroup.equivMapOfInjective D σ.toMonoidHom σ.injective).trans
          (MulEquiv.subgroupCongr hDmap)
      have hσD_apply : ∀ d : D, (σD d : E) = σ (d : E) := fun d => rfl
      have hσDpow : ∀ (k : ℕ) (d : D), ((σD ^ k) d : E) = (σ ^ k) (d : E) := by
        intro k
        induction k with
        | zero => intro d; simp
        | succ k ih =>
            intro d
            rw [pow_succ, MulAut.mul_apply, ih (σD d), pow_succ, MulAut.mul_apply, hσD_apply]
      have hσD7 : σD ^ 7 = 1 := by
        ext d
        rw [hσDpow 7 d]
        have := congrArg (fun f : MulAut E => f (d : E)) hσ7
        simpa using this
      have hσD_ne_one : σD ≠ 1 := by
        intro h1
        have hDC : D ≤ C := by
          intro d hd
          rw [hC_fix]
          have h2 := congrArg (fun f : MulAut D => (f ⟨d, hd⟩ : D)) h1
          have h3 : (σD ⟨d, hd⟩ : E) = (⟨d, hd⟩ : D) := by
            simpa using congrArg Subtype.val h2
          rw [hσD_apply] at h3
          exact h3
        have hle := Subgroup.card_le_of_le hDC
        rw [hDcard, hCcard] at hle
        omega
      have horderD : orderOf σD = 7 := orderOf_eq_prime hσD7 hσD_ne_one
      let PD : Subgroup (MulAut D) := Subgroup.zpowers σD
      letI : MulAction PD D := MulAction.compHom D PD.subtype
      have hPDcard : Nat.card PD = 7 := by
        rw [show PD = Subgroup.zpowers σD from rfl, Nat.card_zpowers, horderD]
      have hPDis : IsPGroup 7 PD := IsPGroup.of_card (n := 1) (by rw [hPDcard]; norm_num)
      have hfixD_iff : ∀ d : D, d ∈ MulAction.fixedPoints PD D ↔ σD d = d := by
        intro d
        rw [MulAction.mem_fixedPoints]
        constructor
        · intro h
          have h1 := h ⟨σD, Subgroup.mem_zpowers σD⟩
          have h2 : (σD : MulAut D) • d = d := h1
          rwa [MulAut.smul_def] at h2
        · intro h g
          have hg : (g : MulAut D) ∈ Subgroup.zpowers σD := g.2
          obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hg
          change ((g : MulAut D) • d) = d
          rw [← hk]
          exact zpow_smul_eq_self (g := (σD : MulAut D)) (a := d)
            (by rwa [MulAut.smul_def]) k
      have hfixedCard : Nat.card (MulAction.fixedPoints PD D) = Nat.card C := by
        have hset : (MulAction.fixedPoints PD D : Set D) = {d : D | (d : E) ∈ C} := by
          ext d
          rw [hfixD_iff d]
          change σD d = d ↔ (d : E) ∈ C
          rw [hC_fix]
          constructor
          · intro h
            rw [← hσD_apply d]
            exact congrArg Subtype.val h
          · intro h
            apply Subtype.ext
            rw [hσD_apply d]
            exact h
        rw [hset]
        exact Nat.card_congr
          { toFun := fun d => ⟨(d.1 : E), d.2⟩
            invFun := fun c => ⟨⟨(c : E), hCD c.2⟩, c.2⟩
            left_inv := fun d => Subtype.ext rfl
            right_inv := fun c => Subtype.ext rfl }
      have hmodD : Nat.card D ≡ Nat.card (MulAction.fixedPoints PD D) [MOD 7] :=
        hPDis.card_modEq_card_fixedPoints D
      rw [hDcard, hfixedCard, hCcard] at hmodD
      norm_num at hmodD
    ·
      have hCtop : C = ⊤ := by
        refine Subgroup.eq_of_le_of_card_ge le_top ?_
        rw [Subgroup.card_top, hcard, hk]
        norm_num
      have hσeq : σ = 1 := by
        ext x
        have hx : x ∈ C := by rw [hCtop]; exact Subgroup.mem_top x
        simpa using (hC_fix x).mp hx
      exact hσ1 hσeq

end CFSG.SectionRank.QTK.Insp443

end
