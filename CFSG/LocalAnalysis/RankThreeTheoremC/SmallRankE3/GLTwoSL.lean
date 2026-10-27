module

public import Mathlib.LinearAlgebra.Determinant

import Mathlib.LinearAlgebra.Center

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

private theorem r10h3_det_coe {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (c : V ≃ₗ[K] V) (h : LinearEquiv.det c = 1) : LinearMap.det (c : V →ₗ[K] V) = 1 := by
  have h' := congrArg Units.val h
  rwa [LinearEquiv.coe_det, Units.val_one] at h'

private theorem r10h3_exists_smul_of_finrank_le_one {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (hV : Module.finrank K V ≤ 1) (f : V →ₗ[K] V) :
    ∃ r : K, f = r • (1 : V →ₗ[K] V) := by
  refine LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent (fun v hv => ?_)
  have h := hv.fintype_card_le_finrank
  simp only [Fintype.card_fin] at h
  omega

private theorem r10h3_eq_one_of_finrank_le_one {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (hV : Module.finrank K V ≤ 1) (e : V ≃ₗ[K] V)
    (hdet : LinearEquiv.det e = 1) : e = 1 := by
  by_cases h0 : Module.finrank K V = 0
  · refine LinearEquiv.ext fun x => ?_
    rw [finrank_zero_iff_forall_zero.1 h0 x]
    simp
  · obtain ⟨r, hr⟩ := r10h3_exists_smul_of_finrank_le_one hV (e : V →ₗ[K] V)
    have h1 : Module.finrank K V = 1 := by omega
    have hd := r10h3_det_coe e hdet
    rw [hr, LinearMap.det_smul, h1, map_one, mul_one, pow_one] at hd
    refine LinearEquiv.ext fun x => ?_
    have hx := LinearMap.congr_fun hr x
    rw [hd, LinearMap.smul_apply, Module.End.one_apply, one_smul] at hx
    simpa using hx

private theorem r10h3_sq_eq_one_of_smul {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (hV : Module.finrank K V = 2) (c : V ≃ₗ[K] V) (hdet : LinearEquiv.det c = 1) (r : K)
    (hr : (c : V →ₗ[K] V) = r • (1 : V →ₗ[K] V)) : c ^ 2 = 1 := by
  have h1 : r ^ 2 = 1 := by
    have h := congrArg Units.val hdet
    rw [LinearEquiv.coe_det, hr, LinearMap.det_smul, hV, map_one, mul_one] at h
    simpa using h
  have hc : ∀ x, c x = r • x := fun x => by simpa using LinearMap.congr_fun hr x
  ext x
  rw [pow_two, LinearEquiv.mul_apply, hc, hc, ← mul_smul, ← pow_two, h1, one_smul]
  rfl

private theorem r10h3_eq_one_of_smul {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (hV : Module.finrank K V = 2) (c : V ≃ₗ[K] V) (hc3 : c ^ 3 = 1)
    (hdet : LinearEquiv.det c = 1) (r : K) (hr : (c : V →ₗ[K] V) = r • (1 : V →ₗ[K] V)) :
    c = 1 := by
  have h2 := r10h3_sq_eq_one_of_smul hV c hdet r hr
  have h3 : c ^ 3 = c := by rw [pow_succ, h2, one_mul]
  exact h3.symm.trans hc3

private theorem r10h3_not_smul {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (hV : Module.finrank K V = 2) (c : V ≃ₗ[K] V) (hc3 : c ^ 3 = 1)
    (hdet : LinearEquiv.det c = 1) (hc1 : c ≠ 1) :
    ¬∃ r : K, (c : V →ₗ[K] V) = r • (1 : V →ₗ[K] V) := by
  rintro ⟨r, hr⟩
  exact hc1 (r10h3_eq_one_of_smul hV c hc3 hdet r hr)

private theorem r10h3_exists_span {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (hV : Module.finrank K V = 2) (c : V ≃ₗ[K] V)
    (hns : ¬∃ r : K, (c : V →ₗ[K] V) = r • (1 : V →ₗ[K] V)) :
    ∃ v : V, LinearIndependent K ![v, (c : V →ₗ[K] V) v] ∧
      Submodule.span K {v, (c : V →ₗ[K] V) v} = ⊤ := by
  by_contra hex
  apply hns
  refine LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent (fun v hv => ?_)
  apply hex
  refine ⟨v, hv, ?_⟩
  have := hv.span_eq_top_of_card_eq_finrank' (by simp [hV])
  rwa [Matrix.range_cons_cons_empty] at this

private theorem r10h3_det_eq_neg {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (c : V ≃ₗ[K] V) (v : V) (a b : K) (hli : LinearIndependent K ![v, (c : V →ₗ[K] V) v])
    (hsp : Submodule.span K {v, (c : V →ₗ[K] V) v} = ⊤)
    (hcv : (c : V →ₗ[K] V) ((c : V →ₗ[K] V) v) = a • v + b • (c : V →ₗ[K] V) v) :
    LinearMap.det (c : V →ₗ[K] V) = -a := by
  have hle : ⊤ ≤ Submodule.span K (Set.range ![v, (c : V →ₗ[K] V) v]) := by
    rw [Matrix.range_cons_cons_empty, hsp]
  obtain ⟨B, hB0, hB1⟩ : ∃ B : Module.Basis (Fin 2) K V, B 0 = v ∧ B 1 = (c : V →ₗ[K] V) v :=
    ⟨Module.Basis.mk hli hle, by simp, by simp⟩
  have hc0 : (c : V →ₗ[K] V) (B 0) = B 1 := by rw [hB0, hB1]
  have hc1 : (c : V →ₗ[K] V) (B 1) = a • B 0 + b • B 1 := by rw [hB0, hB1, hcv]
  rw [← LinearMap.det_toMatrix B, Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply, hc0, hc1, map_add, map_smul, Module.Basis.repr_self,
    Finsupp.add_apply, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
  norm_num

private theorem r10h3_eq_of_span {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {v w : V} (hspan : Submodule.span K {v, w} = ⊤) (f g : V →ₗ[K] V) (hv : f v = g v)
    (hw : f w = g w) (x : V) : f x = g x := by
  have hle : Submodule.span K {v, w} ≤ LinearMap.eqLocus f g := by
    rw [Submodule.span_le]
    intro y hy
    rcases hy with rfl | rfl
    · exact hv
    · exact hw
  have hx : x ∈ Submodule.span K {v, w} := by
    rw [hspan]
    exact Submodule.mem_top
  exact hle hx

private theorem r10h3_lin_zero {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (f : V →ₗ[K] V) (hns : ¬∃ r : K, f = r • (1 : V →ₗ[K] V)) (v : V) (hv : v ≠ 0)
    (p q : K) (h : ∀ x, p • x + q • f x = 0) : p = 0 ∧ q = 0 := by
  by_cases hq : q = 0
  · refine ⟨?_, hq⟩
    have hp : p • v = 0 := by simpa [hq] using h v
    exact (smul_eq_zero.1 hp).resolve_right hv
  · exfalso
    apply hns
    refine ⟨-(q⁻¹ * p), LinearMap.ext fun x => ?_⟩
    have h1 : q • f x = -(p • x) := by linear_combination (norm := module) h x
    rw [LinearMap.smul_apply, Module.End.one_apply]
    calc f x = q⁻¹ • (q • f x) := (inv_smul_smul₀ hq (f x)).symm
      _ = q⁻¹ • (-(p • x)) := by rw [h1]
      _ = (-(q⁻¹ * p)) • x := by rw [smul_neg, smul_smul, neg_smul]

private theorem r10h3_quad {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (hV : Module.finrank K V = 2) (c : V ≃ₗ[K] V)
    (hc3 : c ^ 3 = 1) (hdet : LinearEquiv.det c = 1) (hc1 : c ≠ 1) :
    ∃ v : V, v ≠ 0 ∧ Submodule.span K {v, (c : V →ₗ[K] V) v} = ⊤ ∧
      ∀ x, c (c x) = -(c x) - x := by
  have hns := r10h3_not_smul hV c hc3 hdet hc1
  obtain ⟨v, hli, hsp⟩ := r10h3_exists_span hV c hns
  have hv0 : v ≠ 0 := by simpa using hli.ne_zero 0
  have hmem : (c : V →ₗ[K] V) ((c : V →ₗ[K] V) v) ∈
      Submodule.span K {v, (c : V →ₗ[K] V) v} := by
    rw [hsp]
    exact Submodule.mem_top
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.1 hmem
  have hdm : -a = 1 :=
    (r10h3_det_eq_neg c v a b hli hsp hab.symm).symm.trans (r10h3_det_coe c hdet)
  have ha : a = -1 := by linear_combination -hdm
  rw [ha, neg_one_smul] at hab
  have hv' : ((c : V →ₗ[K] V) ∘ₗ (c : V →ₗ[K] V)) v =
      ((b • (c : V →ₗ[K] V) - LinearMap.id : V →ₗ[K] V)) v := by
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply]
    rw [← hab]
    abel
  have hw' : ((c : V →ₗ[K] V) ∘ₗ (c : V →ₗ[K] V)) ((c : V →ₗ[K] V) v) =
      ((b • (c : V →ₗ[K] V) - LinearMap.id : V →ₗ[K] V)) ((c : V →ₗ[K] V) v) := by
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, ← hab, map_add, map_neg, map_smul]
    module
  have hq : ∀ x, (c : V →ₗ[K] V) ((c : V →ₗ[K] V) x) = b • (c : V →ₗ[K] V) x - x := by
    intro x
    have h := r10h3_eq_of_span hsp _ _ hv' hw' x
    simpa using h
  have hc3x : ∀ x, (c : V →ₗ[K] V) ((c : V →ₗ[K] V) ((c : V →ₗ[K] V) x)) = x := by
    intro x
    have h := LinearEquiv.congr_fun hc3 x
    simpa [pow_succ, LinearEquiv.mul_apply] using h
  have hcube : ∀ x, (-(1 + b)) • x + (b ^ 2 - 1) • (c : V →ₗ[K] V) x = 0 := by
    intro x
    linear_combination (norm := module) hc3x x - hq ((c : V →ₗ[K] V) x) - b • hq x
  have hb : b = -1 := by
    obtain ⟨hp, -⟩ := r10h3_lin_zero (c : V →ₗ[K] V) hns v hv0 (-(1 + b)) (b ^ 2 - 1) hcube
    linear_combination -hp
  refine ⟨v, hv0, hsp, fun x => ?_⟩
  have h := hq x
  rw [hb, neg_one_smul] at h
  exact h

private theorem r10h3_mem_three {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (hK : (3 : K) ≠ 0) (m e : V ≃ₗ[K] V) (v : V) (hv0 : v ≠ 0)
    (hspan : Submodule.span K {v, (m : V →ₗ[K] V) v} = ⊤)
    (hqm : ∀ x, m (m x) = -(m x) - x) (hqe : ∀ x, e (e x) = -(e x) - x)
    (hcomm : ∀ x, e (m x) = m (e x)) (hnsm : ¬∃ r : K, (m : V →ₗ[K] V) = r • (1 : V →ₗ[K] V))
    (hnse : ¬∃ r : K, (e : V →ₗ[K] V) = r • (1 : V →ₗ[K] V)) :
    e = m ∨ e = m ^ 2 := by
  have hmem : (e : V →ₗ[K] V) v ∈ Submodule.span K {v, (m : V →ₗ[K] V) v} := by
    rw [hspan]
    exact Submodule.mem_top
  obtain ⟨α, β, hab⟩ := Submodule.mem_span_pair.1 hmem
  have hex : ∀ x, e x = α • x + β • m x := by
    intro x
    refine r10h3_eq_of_span hspan (e : V →ₗ[K] V) (α • LinearMap.id + β • (m : V →ₗ[K] V))
      ?_ ?_ x
    · exact hab.symm
    · show (e : V →ₗ[K] V) ((m : V →ₗ[K] V) v) =
        α • (m : V →ₗ[K] V) v + β • (m : V →ₗ[K] V) ((m : V →ₗ[K] V) v)
      calc (e : V →ₗ[K] V) ((m : V →ₗ[K] V) v) = (m : V →ₗ[K] V) ((e : V →ₗ[K] V) v) :=
            hcomm v
        _ = (m : V →ₗ[K] V) (α • v + β • (m : V →ₗ[K] V) v) := by rw [hab]
        _ = α • (m : V →ₗ[K] V) v + β • (m : V →ₗ[K] V) ((m : V →ₗ[K] V) v) := by
          rw [map_add, map_smul, map_smul]
  have hkey : ∀ x, (α ^ 2 - β ^ 2 + α + 1) • x + (2 * α * β - β ^ 2 + β) • m x = 0 := by
    intro x
    have h4 := hqe x
    simp only [map_add, map_smul, hex x, hex (m x), hqm x] at h4
    linear_combination (norm := module) h4
  obtain ⟨hp, hq⟩ := r10h3_lin_zero (m : V →ₗ[K] V) hnsm v hv0 (α ^ 2 - β ^ 2 + α + 1)
    (2 * α * β - β ^ 2 + β) hkey
  by_cases hβ : β = 0
  · exfalso
    apply hnse
    refine ⟨α, LinearMap.ext fun x => ?_⟩
    have h := hex x
    rw [hβ, zero_smul, add_zero] at h
    rw [LinearMap.smul_apply, Module.End.one_apply]
    exact h
  · have hβ2 : 2 * α - β + 1 = 0 := by
      have h5 : β * (2 * α - β + 1) = 0 := by linear_combination hq
      exact (mul_eq_zero.1 h5).resolve_left hβ
    have h6 : 3 * (α * (α + 1)) = 0 := by
      linear_combination (-1 : K) * hp + (2 * α + 1 + β) * hβ2
    have h7 : α * (α + 1) = 0 := (mul_eq_zero.1 h6).resolve_left hK
    rcases mul_eq_zero.1 h7 with hα | hα
    · left
      have hβ1 : β = 1 := by linear_combination (-1 : K) * hβ2 + 2 * hα
      apply LinearEquiv.ext
      intro x
      rw [hex x, hα, hβ1, zero_smul, one_smul, zero_add]
    · right
      have hα' : α = -1 := eq_neg_of_add_eq_zero_left hα
      have hβ' : β = -1 := by linear_combination (-1 : K) * hβ2 + 2 * hα
      apply LinearEquiv.ext
      intro x
      rw [pow_two, LinearEquiv.mul_apply, hqm x, hex x, hα', hβ', neg_one_smul, neg_one_smul]
      abel

theorem card_le_three_of_det_eq_one {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (hK : (3 : K) ≠ 0) (hV : Module.finrank K V ≤ 2)
    (E : Subgroup (V ≃ₗ[K] V)) (hE3 : ∀ e ∈ E, e ^ 3 = 1)
    (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hdet : ∀ e ∈ E, LinearEquiv.det e = 1) :
    Nat.card E ≤ 3 := by
  obtain ⟨m, hm⟩ : ∃ m : V ≃ₗ[K] V, ∀ e ∈ E, e = 1 ∨ e = m ∨ e = m ^ 2 := by
    by_cases hfin : Module.finrank K V ≤ 1
    · exact ⟨1, fun e he => Or.inl (r10h3_eq_one_of_finrank_le_one hfin e (hdet e he))⟩
    have h2 : Module.finrank K V = 2 := by omega
    by_cases hE : ∃ m ∈ E, m ≠ 1
    · obtain ⟨m, hmE, hm1⟩ := hE
      obtain ⟨v, hv0, hspan, hqm⟩ := r10h3_quad h2 m (hE3 m hmE) (hdet m hmE) hm1
      refine ⟨m, fun e he => ?_⟩
      by_cases he1 : e = 1
      · exact Or.inl he1
      · obtain ⟨_, _, _, hqe⟩ := r10h3_quad h2 e (hE3 e he) (hdet e he) he1
        have hnse := r10h3_not_smul h2 e (hE3 e he) (hdet e he) he1
        have hnsm := r10h3_not_smul h2 m (hE3 m hmE) (hdet m hmE) hm1
        have hcomm : ∀ x, e (m x) = m (e x) := fun x => by
          simpa only [LinearEquiv.mul_apply] using LinearEquiv.congr_fun (hEc e he m hmE) x
        rcases r10h3_mem_three hK m e v hv0 hspan hqm hqe hcomm hnsm hnse with h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
    · have hE' : ∀ e ∈ E, e = 1 := fun e he => Classical.byContradiction fun h => hE ⟨e, he, h⟩
      exact ⟨1, fun e he => Or.inl (hE' e he)⟩
  have hsub : (E : Set (V ≃ₗ[K] V)) ⊆ ({1, m, m ^ 2} : Set (V ≃ₗ[K] V)) := by
    intro e he
    rcases hm e he with h | h | h <;> simp [h]
  have h3 : ({1, m, m ^ 2} : Set (V ≃ₗ[K] V)).ncard ≤ 3 := by
    have a1 := Set.ncard_insert_le m ({m ^ 2} : Set (V ≃ₗ[K] V))
    have a2 := Set.ncard_insert_le (1 : V ≃ₗ[K] V) ({m, m ^ 2} : Set (V ≃ₗ[K] V))
    rw [Set.ncard_singleton] at a1
    omega
  calc Nat.card E = (E : Set (V ≃ₗ[K] V)).ncard := Nat.card_coe_set_eq _
    _ ≤ ({1, m, m ^ 2} : Set (V ≃ₗ[K] V)).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ 3 := h3


private lemma surj_zmod3_aux (Q : Type*) [Group Q] [IsCyclic Q] (h : 3 ∣ Nat.card Q) :
    ∃ φ : Q →* Multiplicative (ZMod 3), Function.Surjective φ := by
  have hc : Function.Surjective
      (AddMonoidHom.toMultiplicative (ZMod.castHom h (ZMod 3)).toAddMonoidHom) := by
    intro y
    obtain ⟨x, hx⟩ := ZMod.castHom_surjective h (Multiplicative.toAdd y)
    exact ⟨Multiplicative.ofAdd x, congrArg Multiplicative.ofAdd hx⟩
  exact ⟨(AddMonoidHom.toMultiplicative (ZMod.castHom h (ZMod 3)).toAddMonoidHom).comp
    (zmodCyclicMulEquiv (inferInstance : IsCyclic Q)).symm.toMonoidHom,
    hc.comp (zmodCyclicMulEquiv (inferInstance : IsCyclic Q)).symm.surjective⟩

private lemma not_three_dvd_aux {Γ : Type*} [Group Γ] [Finite Γ] {G' : Type*} [Group G']
    (hΓ : ∀ N : Subgroup Γ, N.Normal → N.index ≠ 3) (δ : Γ →* G')
    [Finite δ.range] [IsCyclic δ.range] : ¬ 3 ∣ Nat.card δ.range := by
  intro h
  obtain ⟨φ, hφ⟩ := surj_zmod3_aux δ.range h
  have hψ : Function.Surjective (φ.comp δ.rangeRestrict) :=
    hφ.comp (MonoidHom.rangeRestrict_surjective δ)
  have hidx : (φ.comp δ.rangeRestrict).ker.index = 3 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top_of_surjective (φ.comp δ.rangeRestrict) hψ,
      Subgroup.card_top, ← Nat.card_congr Multiplicative.ofAdd, Nat.card_zmod]
  exact hΓ (φ.comp δ.rangeRestrict).ker (MonoidHom.normal_ker _) hidx

theorem elemAbelian_image_card_le_three {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (hK : (3 : K) ≠ 0) (hV : Module.finrank K V ≤ 2)
    {Γ : Type*} [Group Γ] [Finite Γ] (ρ : Γ →* (V ≃ₗ[K] V))
    (hΓ : ∀ N : Subgroup Γ, N.Normal → N.index ≠ 3)
    (E : Subgroup Γ) (hE3 : ∀ e ∈ E, e ^ 3 = 1) (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) :
    Nat.card (E.map ρ) ≤ 3 := by
  obtain ⟨δ, hδ⟩ : ∃ δ : Γ →* Kˣ, δ = LinearEquiv.det.comp ρ := ⟨_, rfl⟩
  have hδe : ∀ e : Γ, δ e = LinearEquiv.det (ρ e) := fun e => by
    subst hδ
    rfl
  haveI : Finite δ.range :=
    Finite.of_surjective δ.rangeRestrict (MonoidHom.rangeRestrict_surjective δ)
  haveI : IsCyclic δ.range := inferInstance
  have hnd : ¬ 3 ∣ Nat.card δ.range := not_three_dvd_aux hΓ δ
  have hdet : ∀ e ∈ E, LinearEquiv.det (ρ e) = 1 := by
    intro e he
    have h3 : δ e ^ 3 = 1 := by
      rw [← map_pow, hE3 e he, map_one]
    have hmem : δ e ∈ δ.range := MonoidHom.mem_range.mpr ⟨e, rfl⟩
    have hd1 : orderOf (δ e) ∣ 3 := orderOf_dvd_of_pow_eq_one h3
    have hd2 : orderOf (δ e) ∣ Nat.card δ.range := Subgroup.orderOf_dvd_natCard δ.range hmem
    have hone : orderOf (δ e) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hd1 with h | h
      · exact h
      · exfalso
        rw [h] at hd2
        exact hnd hd2
    rw [← hδe e]
    exact orderOf_eq_one_iff.mp hone
  have hE3' : ∀ e' ∈ E.map ρ, e' ^ 3 = 1 := by
    intro e' he'
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp he'
    rw [← map_pow, hE3 e he, map_one]
  have hEc' : ∀ a ∈ E.map ρ, ∀ b ∈ E.map ρ, a * b = b * a := by
    intro a ha b hb
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hb
    rw [← map_mul, ← map_mul, hEc x hx y hy]
  have hdet' : ∀ e' ∈ E.map ρ, LinearEquiv.det e' = 1 := by
    intro e' he'
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp he'
    exact hdet e he
  exact card_le_three_of_det_eq_one hK hV (E.map ρ) hE3' hEc' hdet'

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
