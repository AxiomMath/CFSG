module

public import CFSG.LinearAlgebra.LinearGroups.Elations
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

public section

namespace CFSG.QuasithinUnique.Setup.Campbell

open Matrix Module CFSG.SL2MinimalFaithful
open scoped LinearAlgebra.Projectivization Pointwise

section SL2

variable {k : Type*} [Field k]

@[expose] def rootGrp (p : ℙ k (Fin 2 → k)) : Subgroup (SpecialLinearGroup (Fin 2) k) :=
  SpecialLinearGroup.lineStab p.submodule

theorem mem_rootGrp {p : ℙ k (Fin 2 → k)} {g : SpecialLinearGroup (Fin 2) k} :
    g ∈ rootGrp p ↔ ∀ w : Fin 2 → k, g • w - w ∈ p.submodule := Iff.rfl

theorem rootGrp_smul (g : SpecialLinearGroup (Fin 2) k) (p : ℙ k (Fin 2 → k)) :
    rootGrp (g • p) = MulAut.conj g • rootGrp p := by
  unfold rootGrp
  rw [PSL.smul_submodule, SpecialLinearGroup.lineStab_smul]

theorem mem_rootGrp_smul_iff {g h : SpecialLinearGroup (Fin 2) k} {p : ℙ k (Fin 2 → k)} :
    h ∈ rootGrp (g • p) ↔ g⁻¹ * h * g ∈ rootGrp p := by
  rw [rootGrp_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp [MulAut.inv_apply]

@[expose] def pt0 : ℙ k (Fin 2 → k) :=
  Projectivization.mk k (Pi.single 0 1) (by simp [Pi.single_eq_zero_iff])

@[expose] def pt1 : ℙ k (Fin 2 → k) :=
  Projectivization.mk k (Pi.single 1 1) (by simp [Pi.single_eq_zero_iff])

theorem mem_span_e0_iff (v : Fin 2 → k) :
    v ∈ (pt0 : ℙ k (Fin 2 → k)).submodule ↔ v 1 = 0 := by
  rw [pt0, Projectivization.submodule_mk, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, rfl⟩
    simp
  · intro h
    refine ⟨v 0, ?_⟩
    ext i
    fin_cases i <;> simp [h]

theorem mem_span_e1_iff (v : Fin 2 → k) :
    v ∈ (pt1 : ℙ k (Fin 2 → k)).submodule ↔ v 0 = 0 := by
  rw [pt1, Projectivization.submodule_mk, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, rfl⟩
    simp
  · intro h
    refine ⟨v 1, ?_⟩
    ext i
    fin_cases i <;> simp [h]

theorem smul_unipotent_vec (t : k) (v : Fin 2 → k) :
    (unipotent t : SpecialLinearGroup (Fin 2) k) • v = ![v 0 + t * v 1, v 1] := by
  rw [Matrix.SpecialLinearGroup.smul_def]
  ext i
  fin_cases i <;> simp [coe_unipotent, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem rootGrp_pt0 : rootGrp (pt0 : ℙ k (Fin 2 → k)) = (unipotentHom (F := k)).range := by
  ext A
  constructor
  · intro hA
    have h0 := (mem_rootGrp.mp hA) (Pi.single 0 1)
    have h1 := (mem_rootGrp.mp hA) (Pi.single 1 1)
    rw [mem_span_e0_iff] at h0 h1
    rw [Matrix.SpecialLinearGroup.smul_def] at h0 h1
    simp at h0 h1
    have hdet := A.2
    rw [Matrix.det_fin_two] at hdet
    have hc : (A : Matrix (Fin 2) (Fin 2) k) 1 0 = 0 := h0
    have hd : (A : Matrix (Fin 2) (Fin 2) k) 1 1 = 1 := by linear_combination h1
    have ha : (A : Matrix (Fin 2) (Fin 2) k) 0 0 = 1 := by
      rw [hc, hd] at hdet; linear_combination hdet
    refine ⟨Multiplicative.ofAdd ((A : Matrix (Fin 2) (Fin 2) k) 0 1), ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [unipotentHom, coe_unipotent, ha, hc, hd]
  · rintro ⟨t, rfl⟩ w
    rw [mem_span_e0_iff]
    simp [unipotentHom, smul_unipotent_vec]

theorem exists_smul_pt0 (p : ℙ k (Fin 2 → k)) :
    ∃ g : SpecialLinearGroup (Fin 2) k, g • (pt0 : ℙ k (Fin 2 → k)) = p :=
  MulAction.exists_smul_eq _ _ _

theorem eq_of_smul_eq_of_mem_rootGrp {p q : ℙ k (Fin 2 → k)} {u : SpecialLinearGroup (Fin 2) k}
    (hu : u ∈ rootGrp p) (hne : u ≠ 1) (hq : u • q = q) : q = p := by
  obtain ⟨g, rfl⟩ := exists_smul_pt0 p
  have hu' : g⁻¹ * u * g ∈ rootGrp (pt0 : ℙ k (Fin 2 → k)) := mem_rootGrp_smul_iff.mp hu
  rw [rootGrp_pt0] at hu'
  obtain ⟨t, ht⟩ := hu'
  have ht0 : t.toAdd ≠ 0 := by
    intro h0
    apply hne
    have hconj : g⁻¹ * u * g = 1 := by
      rw [← ht]; simp [unipotentHom, h0, unipotent_zero]
    calc u = g * (g⁻¹ * u * g) * g⁻¹ := by group
      _ = 1 := by rw [hconj]; group
  have hfix : (unipotent t.toAdd : SpecialLinearGroup (Fin 2) k) • (g⁻¹ • q) = g⁻¹ • q := by
    have : (g⁻¹ * u * g : SpecialLinearGroup (Fin 2) k) • (g⁻¹ • q) = g⁻¹ • q := by
      simp [mul_smul, hq]
    have hut : (unipotent t.toAdd : SpecialLinearGroup (Fin 2) k) = g⁻¹ * u * g := ht
    rw [hut]
    exact this
  obtain ⟨v, hv, hqv⟩ : ∃ v : Fin 2 → k, ∃ hv : v ≠ 0, g⁻¹ • q = Projectivization.mk k v hv :=
    ⟨(g⁻¹ • q).rep, (g⁻¹ • q).rep_nonzero, (Projectivization.mk_rep _).symm⟩
  rw [hqv, Projectivization.smul_mk, Projectivization.mk_eq_mk_iff] at hfix
  obtain ⟨a, ha⟩ := hfix
  have h1 : (a : k) * v 1 = v 1 := by
    have := congrFun ha 1
    simpa [Units.smul_def, smul_eq_mul, smul_unipotent_vec] using this
  have hv1 : v 1 = 0 := by
    by_contra hv1
    have ha1 : (a : k) = 1 := mul_right_cancel₀ hv1 (by simpa using h1)
    have h0 := congrFun ha 0
    simp only [Units.smul_def, smul_eq_mul, smul_unipotent_vec, Pi.smul_apply] at h0
    simp only [Matrix.cons_val_zero, ha1, one_mul] at h0
    have : Multiplicative.toAdd t * v 1 = 0 := by linear_combination -h0
    exact hv1 ((mul_eq_zero.mp this).resolve_left ht0)
  have hqp : g⁻¹ • q = (pt0 : ℙ k (Fin 2 → k)) := by
    rw [hqv, pt0, Projectivization.mk_eq_mk_iff]
    have hv0 : v 0 ≠ 0 := by
      intro h0
      apply hv
      ext i; fin_cases i <;> simp [h0, hv1]
    refine ⟨Units.mk0 (v 0) hv0, ?_⟩
    ext i
    fin_cases i <;> simp [hv1]
  rw [inv_smul_eq_iff] at hqp
  exact hqp

theorem smul_self_of_mem_rootGrp {p : ℙ k (Fin 2 → k)} {u : SpecialLinearGroup (Fin 2) k}
    (hu : u ∈ rootGrp p) : u • p = p := by
  obtain ⟨v, hv, rfl⟩ : ∃ v : Fin 2 → k, ∃ hv : v ≠ 0, p = Projectivization.mk k v hv :=
    ⟨p.rep, p.rep_nonzero, (Projectivization.mk_rep _).symm⟩
  rw [Projectivization.smul_mk]
  have : u • v = v := by
    refine Matrix.SpecialLinearGroup.lineStab_fix_of_span v hv u ?_
    unfold rootGrp at hu
    rwa [Projectivization.submodule_mk] at hu
  simp [this]


theorem rootGrp_smul_eq_map (g : SpecialLinearGroup (Fin 2) k) (p : ℙ k (Fin 2 → k)) :
    rootGrp (g • p) = (rootGrp p).map (MulAut.conj g).toMonoidHom := by
  rw [rootGrp_smul, Subgroup.pointwise_smul_def]
  rfl

theorem card_rootGrp [Finite k] (p : ℙ k (Fin 2 → k)) : Nat.card (rootGrp p) = Nat.card k := by
  obtain ⟨g, rfl⟩ := exists_smul_pt0 p
  rw [rootGrp_smul_eq_map, rootGrp_pt0]
  rw [Nat.card_congr ((unipotentHom (F := k)).range.equivMapOfInjective _
    (MulAut.conj g).injective).toEquiv.symm]
  exact (Nat.card_congr (MonoidHom.ofInjective unipotentHom_injective).toEquiv).symm.trans
    (Nat.card_congr Multiplicative.toAdd)

theorem rootGrp_inf_rootGrp {p q : ℙ k (Fin 2 → k)} (h : p ≠ q) :
    rootGrp p ⊓ rootGrp q = ⊥ := by
  rw [eq_bot_iff]
  rintro u ⟨hp, hq⟩
  by_contra hne
  rw [Subgroup.mem_bot] at hne
  exact h (eq_of_smul_eq_of_mem_rootGrp hp hne (smul_self_of_mem_rootGrp hq)).symm

theorem exists_ne_one_mem_rootGrp [Finite k] (p : ℙ k (Fin 2 → k)) :
    ∃ u ∈ rootGrp p, u ≠ 1 := by
  by_contra hall
  push Not at hall
  have h1 : Nat.card (rootGrp p) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => Subtype.ext ?_⟩, ⟨1⟩⟩
    rw [hall a a.2, hall b b.2]
  rw [card_rootGrp] at h1
  exact (Finite.one_lt_card (α := k)).ne' (by simpa using h1)

theorem rootGrp_sup_rootGrp_pt0_pt1 :
    rootGrp (pt0 : ℙ k (Fin 2 → k)) ⊔ rootGrp (pt1 : ℙ k (Fin 2 → k)) = ⊤ := by
  rw [eq_top_iff, ← CFSG.LinearGroups.special_linear_elementary_generation, Subgroup.closure_le]
  rintro _ ⟨i, j, hij, c, rfl⟩
  have h0 := CFSG.LinearGroups.linear_elation_elementary_containment (K := k) (n := 2)
    (i := 0) (j := 1) (by decide) c
  have h1 := CFSG.LinearGroups.linear_elation_elementary_containment (K := k) (n := 2)
    (i := 1) (j := 0) (by decide) c
  have e0 : CFSG.LinearGroups.elationSubgroup
      (k ∙ (Pi.single 0 1 : Fin 2 → k)) = rootGrp (pt0 : ℙ k (Fin 2 → k)) := by
    rw [CFSG.LinearGroups.elationSubgroup_eq_lineStab, rootGrp, pt0, Projectivization.submodule_mk]
    rw [finrank_span_singleton]
    simp [Pi.single_eq_zero_iff]
  have e1 : CFSG.LinearGroups.elationSubgroup
      (k ∙ (Pi.single 1 1 : Fin 2 → k)) = rootGrp (pt1 : ℙ k (Fin 2 → k)) := by
    rw [CFSG.LinearGroups.elationSubgroup_eq_lineStab, rootGrp, pt1, Projectivization.submodule_mk]
    rw [finrank_span_singleton]
    simp [Pi.single_eq_zero_iff]
  rw [e0] at h0
  rw [e1] at h1
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact Subgroup.mem_sup_left h0
  · exact Subgroup.mem_sup_right h1
  · exact absurd rfl hij

theorem rootGrp_sup_rootGrp {p q : ℙ k (Fin 2 → k)} (h : p ≠ q) :
    rootGrp p ⊔ rootGrp q = ⊤ := by
  have hpt : (pt0 : ℙ k (Fin 2 → k)) ≠ pt1 := by
    intro h01
    have := (Projectivization.mk_eq_mk_iff k _ _ (by simp [Pi.single_eq_zero_iff])
      (by simp [Pi.single_eq_zero_iff])).mp h01
    obtain ⟨a, ha⟩ := this
    have := congrFun ha 0
    simp at this
  obtain ⟨g, hg1, hg2⟩ := CFSG.LinearGroups.special_linear_projective_double_transitivity
    p.finrank_submodule q.finrank_submodule (pt0 : ℙ k (Fin 2 → k)).finrank_submodule
    (pt1 : ℙ k (Fin 2 → k)).finrank_submodule
    (fun hpq => h (Projectivization.submodule_injective hpq))
    (fun hpq => hpt (Projectivization.submodule_injective hpq))
  have hgp : g • p = pt0 := by
    apply Projectivization.submodule_injective
    rw [PSL.smul_submodule, hg1]
  have hgq : g • q = pt1 := by
    apply Projectivization.submodule_injective
    rw [PSL.smul_submodule, hg2]
  have key := rootGrp_sup_rootGrp_pt0_pt1 (k := k)
  rw [← hgp, ← hgq, rootGrp_smul_eq_map, rootGrp_smul_eq_map, ← Subgroup.map_sup] at key
  have := Subgroup.map_injective (MulAut.conj g).injective (key.trans
    (Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective).symm)
  exact this

theorem mem_normalizer_rootGrp_iff [Finite k] {g : SpecialLinearGroup (Fin 2) k}
    {p : ℙ k (Fin 2 → k)} :
    g ∈ Subgroup.normalizer (rootGrp p : Set (SpecialLinearGroup (Fin 2) k)) ↔ g • p = p := by
  constructor
  · intro hg
    by_contra hne
    obtain ⟨u, hu, hu1⟩ := exists_ne_one_mem_rootGrp p
    have hu2 : u ∈ rootGrp (g • p) := by
      rw [mem_rootGrp_smul_iff]
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) u).mp hu
      simpa using this
    have := rootGrp_inf_rootGrp (p := p) (q := g • p) (Ne.symm hne)
    have hmem : u ∈ rootGrp p ⊓ rootGrp (g • p) := ⟨hu, hu2⟩
    rw [this, Subgroup.mem_bot] at hmem
    exact hu1 hmem
  · intro hg
    have key : ∀ g : SpecialLinearGroup (Fin 2) k, g • p = p →
        ∀ h, h ∈ rootGrp p → g * h * g⁻¹ ∈ rootGrp p := by
      intro g hg h hh
      have hg' : g⁻¹ • p = p := by rw [inv_smul_eq_iff, hg]
      have : g * h * g⁻¹ ∈ rootGrp (g • p) := by
        rw [mem_rootGrp_smul_iff]
        have e : g⁻¹ * (g * h * g⁻¹) * g = h := by group
        rw [e]; exact hh
      rwa [hg] at this
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨key g hg h, fun hh => ?_⟩
    have hg' : g⁻¹ • p = p := by rw [inv_smul_eq_iff, hg]
    have := key g⁻¹ hg' _ hh
    simpa [mul_assoc] using this

theorem exists_point_eq_rootGrp [Finite k] {p f : ℕ} (hp : p.Prime) (hcard : Nat.card k = p ^ f)
    {P : Subgroup (SpecialLinearGroup (Fin 2) k)} (hP : Nat.card P = Nat.card k) :
    ∃ x : ℙ k (Fin 2 → k), P = rootGrp x := by
  obtain ⟨g, hg⟩ := exists_conj_unipotent_mem hp hcard hP
  refine ⟨g • pt0, ?_⟩
  have hle : rootGrp (g • (pt0 : ℙ k (Fin 2 → k))) ≤ P := by
    intro h hh
    rw [mem_rootGrp_smul_iff, rootGrp_pt0] at hh
    obtain ⟨t, ht⟩ := hh
    have : h = g * unipotent t.toAdd * g⁻¹ := by
      have ht' : unipotent t.toAdd = g⁻¹ * h * g := ht
      rw [ht']; group
    rw [this]
    exact hg _
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [card_rootGrp, hP])).symm

theorem mem_span_iff_cross {v : Fin 2 → k} (hv : v ≠ 0) (u : Fin 2 → k) :
    u ∈ k ∙ v ↔ u 0 * v 1 - u 1 * v 0 = 0 := by
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, rfl⟩
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  · intro h
    by_cases h0 : v 0 = 0
    · have h1 : v 1 ≠ 0 := by
        intro h1; apply hv; ext i; fin_cases i <;> simp [h0, h1]
      refine ⟨u 1 / v 1, ?_⟩
      have hu0 : u 0 = 0 := by
        rw [h0] at h
        have : u 0 * v 1 = 0 := by linear_combination h
        exact (mul_eq_zero.mp this).resolve_right h1
      ext i; fin_cases i
      · simp [h0, hu0]
      · simp; field_simp
    · refine ⟨u 0 / v 0, ?_⟩
      ext i; fin_cases i
      · simp; field_simp
      · simp
        field_simp
        linear_combination h

theorem mem_rootGrp_mk_of_smul_eq {v : Fin 2 → k} (hv : v ≠ 0) {g : SpecialLinearGroup (Fin 2) k}
    (h : g • v = v) : g ∈ rootGrp (Projectivization.mk k v hv) := by
  unfold rootGrp
  rw [Projectivization.submodule_mk, Matrix.SpecialLinearGroup.mem_lineStab_iff]
  intro w
  rw [mem_span_iff_cross hv]
  have hdet := g.2
  rw [Matrix.det_fin_two] at hdet
  have hv' := h
  rw [Matrix.SpecialLinearGroup.smul_def] at hv'
  have hx := congrFun hv' 0
  have hy := congrFun hv' 1
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hx hy
  simp [Matrix.SpecialLinearGroup.smul_def]
  set a := (g : Matrix (Fin 2) (Fin 2) k) 0 0
  set b := (g : Matrix (Fin 2) (Fin 2) k) 0 1
  set c := (g : Matrix (Fin 2) (Fin 2) k) 1 0
  set d := (g : Matrix (Fin 2) (Fin 2) k) 1 1
  have hx' : (a - 1) * v 0 + b * v 1 = 0 := by linear_combination hx
  have hy' : c * v 0 + (d - 1) * v 1 = 0 := by linear_combination hy
  have hdetN : ((a - 1) * (d - 1) - b * c) = 0 := by
    have h1 : ((a - 1) * (d - 1) - b * c) * v 0 = 0 := by
      linear_combination (d - 1) * hx' - b * hy'
    have h2 : ((a - 1) * (d - 1) - b * c) * v 1 = 0 := by
      linear_combination (a - 1) * hy' - c * hx'
    by_contra hne
    apply hv
    ext i; fin_cases i
    · exact (mul_eq_zero.mp h1).resolve_left hne
    · exact (mul_eq_zero.mp h2).resolve_left hne
  have htr : (a - 1) + (d - 1) = 0 := by linear_combination hdet - hdetN
  have hd1 : d - 1 = -(a - 1) := by linear_combination htr
  rw [hd1] at hy'
  linear_combination (-(w 0)) * hy' + (w 1) * hx' - (w 1 * v 0) * htr


@[expose] def lowerElt (t : k) : SpecialLinearGroup (Fin 2) k :=
  ⟨!![1, 0; t, 1], by simp [Matrix.det_fin_two]⟩

theorem smul_lowerElt_vec (t : k) (v : Fin 2 → k) :
    (lowerElt t : SpecialLinearGroup (Fin 2) k) • v = ![v 0, t * v 0 + v 1] := by
  rw [Matrix.SpecialLinearGroup.smul_def]
  ext i
  fin_cases i <;> simp [lowerElt, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem eq_zero_of_forall_smul_eq {w : Fin 2 → k} (h : ∀ g : SpecialLinearGroup (Fin 2) k, g • w = w) :
    w = 0 := by
  have h1 := congrFun (h (unipotent 1)) 0
  have h2 := congrFun (h (lowerElt 1)) 1
  simp [smul_unipotent_vec] at h1
  simp [smul_lowerElt_vec] at h2
  ext i
  fin_cases i
  · exact h2
  · exact h1

theorem smul_eq_self_iff_mem_of_mem_rootGrp {p : ℙ k (Fin 2 → k)} {t : SpecialLinearGroup (Fin 2) k}
    (ht : t ∈ rootGrp p) (ht1 : t ≠ 1) (w : Fin 2 → k) : t • w = w ↔ w ∈ p.submodule := by
  constructor
  · intro hw
    by_cases hw0 : w = 0
    · rw [hw0]; exact p.submodule.zero_mem
    · have hmem : t ∈ rootGrp (Projectivization.mk k w hw0) := mem_rootGrp_mk_of_smul_eq hw0 hw
      by_contra hwp
      have hne : Projectivization.mk k w hw0 ≠ p := by
        intro heq
        apply hwp
        rw [← heq, Projectivization.submodule_mk]
        exact Submodule.mem_span_singleton_self w
      have : t ∈ rootGrp (Projectivization.mk k w hw0) ⊓ rootGrp p := ⟨hmem, ht⟩
      rw [rootGrp_inf_rootGrp hne, Subgroup.mem_bot] at this
      exact ht1 this
  · intro hw
    obtain ⟨v, hv, rfl⟩ : ∃ v : Fin 2 → k, ∃ hv : v ≠ 0, p = Projectivization.mk k v hv :=
      ⟨p.rep, p.rep_nonzero, (Projectivization.mk_rep _).symm⟩
    rw [Projectivization.submodule_mk, Submodule.mem_span_singleton] at hw
    obtain ⟨c, rfl⟩ := hw
    have hfix : t • v = v := by
      refine Matrix.SpecialLinearGroup.lineStab_fix_of_span v hv t ?_
      unfold rootGrp at ht
      rwa [Projectivization.submodule_mk] at ht
    rw [smul_comm, hfix]

theorem exists_smul_sub_eq {p : ℙ k (Fin 2 → k)} {t : SpecialLinearGroup (Fin 2) k}
    (ht : t ∈ rootGrp p) (ht1 : t ≠ 1) {u : Fin 2 → k} (hu : u ∈ p.submodule) :
    ∃ w : Fin 2 → k, t • w - w = u := by
  obtain ⟨w₀, hw₀⟩ : ∃ w₀ : Fin 2 → k, t • w₀ ≠ w₀ := by
    by_contra hall
    push Not at hall
    apply ht1
    have hall' : ∀ w : Fin 2 → k, t • w = w := hall
    ext i j
    have := congrFun (hall' (Pi.single j 1)) i
    rw [Matrix.SpecialLinearGroup.smul_def] at this
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.one_apply] using this
  obtain ⟨v, hv, rfl⟩ : ∃ v : Fin 2 → k, ∃ hv : v ≠ 0, p = Projectivization.mk k v hv :=
    ⟨p.rep, p.rep_nonzero, (Projectivization.mk_rep _).symm⟩
  have hmem : t • w₀ - w₀ ∈ (Projectivization.mk k v hv).submodule := (mem_rootGrp.mp ht) w₀
  rw [Projectivization.submodule_mk, Submodule.mem_span_singleton] at hmem hu
  obtain ⟨a, ha⟩ := hmem
  obtain ⟨b, hb⟩ := hu
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply hw₀
    simpa [sub_eq_zero] using ha.symm
  refine ⟨(b / a) • w₀, ?_⟩
  rw [smul_comm, ← smul_sub, ← ha, smul_smul, div_mul_cancel₀ _ ha0, hb]

theorem mul_self_eq_one_of_mem_rootGrp [CharP k 2] {p : ℙ k (Fin 2 → k)}
    {t : SpecialLinearGroup (Fin 2) k} (ht : t ∈ rootGrp p) : t * t = 1 := by
  obtain ⟨g, rfl⟩ := exists_smul_pt0 p
  have ht' : g⁻¹ * t * g ∈ rootGrp (pt0 : ℙ k (Fin 2 → k)) := mem_rootGrp_smul_iff.mp ht
  rw [rootGrp_pt0] at ht'
  obtain ⟨s, hs⟩ := ht'
  have h2 : (unipotent s.toAdd : SpecialLinearGroup (Fin 2) k) * unipotent s.toAdd = 1 := by
    rw [← unipotent_add]
    have : s.toAdd + s.toAdd = 0 := by
      rw [← two_mul]
      have h2 : (2 : k) = 0 := by exact_mod_cast CharP.cast_eq_zero k 2
      rw [h2, zero_mul]
    rw [this, unipotent_zero]
  have hs' : (unipotent s.toAdd : SpecialLinearGroup (Fin 2) k) = g⁻¹ * t * g := hs
  have : (g⁻¹ * t * g) * (g⁻¹ * t * g) = 1 := by rw [← hs']; exact h2
  calc t * t = g * ((g⁻¹ * t * g) * (g⁻¹ * t * g)) * g⁻¹ := by group
    _ = 1 := by rw [this]; group

theorem card_submodule_line (p : ℙ k (Fin 2 → k)) :
    Nat.card p.submodule = Nat.card k := by
  rw [Module.natCard_eq_pow_finrank (K := k), p.finrank_submodule, pow_one]

omit [Field k] in
theorem card_fin_two_pi : Nat.card (Fin 2 → k) = Nat.card k ^ 2 := by
  rw [Nat.card_pi]
  simp [Finset.prod_const, sq]


theorem pt0_ne_pt1 : (pt0 : ℙ k (Fin 2 → k)) ≠ pt1 := by
  intro h01
  have := (Projectivization.mk_eq_mk_iff k _ _ (by simp [Pi.single_eq_zero_iff])
    (by simp [Pi.single_eq_zero_iff])).mp h01
  obtain ⟨a, ha⟩ := this
  have := congrFun ha 0
  simp at this

theorem exists_ne_point (p : ℙ k (Fin 2 → k)) : ∃ m : ℙ k (Fin 2 → k), m ≠ p := by
  by_cases h : p = pt0
  · exact ⟨pt1, fun h' => pt0_ne_pt1 (h.symm.trans h'.symm)⟩
  · exact ⟨pt0, fun h' => h h'.symm⟩

theorem eq_mk_of_mem_submodule {p : ℙ k (Fin 2 → k)} {w : Fin 2 → k} (hw0 : w ≠ 0)
    (hw : w ∈ p.submodule) : p = Projectivization.mk k w hw0 := by
  obtain ⟨v, hv, rfl⟩ : ∃ v : Fin 2 → k, ∃ hv : v ≠ 0, p = Projectivization.mk k v hv :=
    ⟨p.rep, p.rep_nonzero, (Projectivization.mk_rep _).symm⟩
  rw [Projectivization.submodule_mk, Submodule.mem_span_singleton] at hw
  obtain ⟨c, rfl⟩ := hw
  have hc : c ≠ 0 := by rintro rfl; simp at hw0
  rw [Projectivization.mk_eq_mk_iff]
  refine ⟨(Units.mk0 c hc)⁻¹, ?_⟩
  rw [Units.smul_def, smul_smul]
  simp [hc]

theorem submodule_inf_eq_bot {p m : ℙ k (Fin 2 → k)} (h : p ≠ m) {w : Fin 2 → k}
    (hp : w ∈ p.submodule) (hm : w ∈ m.submodule) : w = 0 := by
  by_contra hw0
  exact h ((eq_mk_of_mem_submodule hw0 hp).trans (eq_mk_of_mem_submodule hw0 hm).symm)

end SL2

end CFSG.QuasithinUnique.Setup.Campbell
