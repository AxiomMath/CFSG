module

public import CFSG.HardMathSupport.Timmesfeld.DFour.CodimTwo
public import CFSG.HardMathSupport.Malle.E27Lie.Cross.OrthOddPairs

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open Module QuadraticMap
open CFSG.LieType.Universal.Spin CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open CFSG.HardMathSupport.Timmesfeld.DFour
open CFSG.HardMathSupport.Malle.E27Lie

section Zero

variable {K : Type} [Field K] [Finite K]
  {g : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)}

theorem sum_eq_zero_of_fixed_zero (h3 : (3 : K) ≠ 0)
    (hg3 : ∀ v, g (g (g v)) = v)
    (hd : finrank K (LinearMap.ker ((g : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] _) - LinearMap.id)) = 0)
    (v : Fin 4 ⊕ Fin 4 → K) : v + g v + g (g v) = 0 := by
  have hfix : fixSp g = ⊥ := by
    have := Submodule.finrank_eq_zero.1 hd
    exact this
  have hsup := movSp_sup_fixSp h3 hg3
  rw [hfix, sup_bot_eq] at hsup
  have : v ∈ movSp g := by rw [hsup]; trivial
  exact mem_movSp.1 this


section CaseB

variable (h2 : (2 : K) ≠ 0)
  (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K))
  (hsum : ∀ v, v + g v + g (g v) = 0) (hg3 : ∀ v, g (g (g v)) = v)
  (hroot : ¬ ∃ ω : K, ω ^ 2 + ω + 1 = 0)

omit [Finite K] in
include hsum hroot in
theorem indep_of_noRoot {v : Fin 4 ⊕ Fin 4 → K} (hv : v ≠ 0) {a b : K}
    (hab : a • v + b • g v = 0) : a = 0 ∧ b = 0 := by
  by_cases hb : b = 0
  · subst hb
    simp only [zero_smul, add_zero] at hab
    exact ⟨(smul_eq_zero.mp hab).resolve_right hv, rfl⟩
  · exfalso
    apply hroot
    refine ⟨-(a / b), ?_⟩
    have h1 : g v = -(a / b) • v := by
      have : b • g v = -(a • v) := eq_neg_of_add_eq_zero_right hab
      calc g v = b⁻¹ • (b • g v) := by rw [smul_smul, inv_mul_cancel₀ hb, one_smul]
        _ = b⁻¹ • -(a • v) := by rw [this]
        _ = -(a / b) • v := by rw [smul_neg, smul_smul, div_eq_inv_mul, neg_smul]
    have h2' : g (g v) = (-(a / b)) ^ 2 • v := by
      rw [h1, map_smul, h1, smul_smul, _root_.sq]
    have := hsum v
    rw [h2', h1] at this
    have h3 : (1 + (-(a / b)) + (-(a / b)) ^ 2) • v = 0 := by
      rw [add_smul, add_smul, one_smul]
      exact this
    have h4 := (smul_eq_zero.mp h3).resolve_right hv
    linear_combination h4

omit [Finite K] in
include hg in
theorem polar_isometry (x y : Fin 4 ⊕ Fin 4 → K) :
    polar (quadPlus 4 K) (g x) (g y) = polar (quadPlus 4 K) x y := by
  have hQg : ∀ v, quadPlus 4 K (g v) = quadPlus 4 K v :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hg
  simp only [polar, ← map_add, hQg]

omit [Finite K] in
include h2 hg hsum hg3 in
theorem polar_apply_eq_zero_of_singular {v : Fin 4 ⊕ Fin 4 → K} (hv : quadPlus 4 K v = 0) :
    polar (quadPlus 4 K) v (g v) = 0 := by
  have e : polar (quadPlus 4 K) v (v + g v + g (g v)) = 0 := by rw [hsum, polar_zero_right]
  rw [polar_add_right, polar_add_right] at e
  have h1 : polar (quadPlus 4 K) v v = 0 := by rw [QuadraticMap.polar_self, hv, smul_zero]
  have h2' : polar (quadPlus 4 K) v (g (g v)) = polar (quadPlus 4 K) v (g v) := by
    have := polar_isometry hg v (g (g v))
    rw [hg3 v] at this
    rw [← this, polar_comm]
  rw [h1, h2'] at e
  have h3 : (2 : K) * polar (quadPlus 4 K) v (g v) = 0 := by linear_combination e
  exact (mul_eq_zero.mp h3).resolve_left h2

@[expose] def planeSp (g : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K))
    (v : Fin 4 ⊕ Fin 4 → K) : Submodule K (Fin 4 ⊕ Fin 4 → K) := Submodule.span K {v, g v}

omit [Finite K] in
include hsum in
theorem planeSp_invariant {v x : Fin 4 ⊕ Fin 4 → K} (hx : x ∈ planeSp g v) :
    g x ∈ planeSp g v := by
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hx
  have h1 : g (g v) = -v - g v := by
    have h := hsum v
    calc g (g v) = (v + g v + g (g v)) - v - g v := by abel
      _ = -v - g v := by rw [h]; abel
  rw [map_add, map_smul, map_smul, h1]
  refine Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))) ?_
  refine Submodule.smul_mem _ _ ?_
  exact Submodule.sub_mem _ (Submodule.neg_mem _ (Submodule.subset_span (by simp)))
    (Submodule.subset_span (by simp))

omit [Finite K] in
include h2 hg hsum hg3 in
theorem planeSp_singular {v : Fin 4 ⊕ Fin 4 → K} (hv : quadPlus 4 K v = 0) :
    ∀ x ∈ planeSp g v, quadPlus 4 K x = 0 := by
  intro x hx
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hx
  have hQg : ∀ v, quadPlus 4 K (g v) = quadPlus 4 K v :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hg
  rw [QuadraticMap.map_add (quadPlus 4 K) (a • v) (b • g v), QuadraticMap.map_smul,
    QuadraticMap.map_smul, hQg, hv,
    QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right,
    polar_apply_eq_zero_of_singular h2 hg hsum hg3 hv]
  simp

omit [Finite K] in
include hsum hroot in
theorem finrank_planeSp {v : Fin 4 ⊕ Fin 4 → K} (hv : v ≠ 0) : finrank K (planeSp g v) = 2 := by
  have hli : LinearIndependent K ![v, g v] := by
    rw [LinearIndependent.pair_iff]
    exact fun a b hab => indep_of_noRoot hsum hroot hv hab
  have := finrank_span_eq_card hli
  rw [Fintype.card_fin] at this
  have hset : Set.range ![v, g v] = {v, g v} := by
    ext x
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff, Fin.exists_fin_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    tauto
  rw [hset] at this
  exact this

omit [Finite K] in
theorem mem_orth_iff {S : Submodule K (Fin 4 ⊕ Fin 4 → K)} {w : Fin 4 ⊕ Fin 4 → K} :
    w ∈ LinearMap.BilinForm.orthogonal (polarBilin (quadPlus 4 K)) S ↔
      ∀ n ∈ S, polar (quadPlus 4 K) n w = 0 := by
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  rfl

omit [Finite K] in
include hg hg3 in
theorem orth_invariant {S : Submodule K (Fin 4 ⊕ Fin 4 → K)} (hS : ∀ x ∈ S, g x ∈ S)
    {w : Fin 4 ⊕ Fin 4 → K} (hw : w ∈ LinearMap.BilinForm.orthogonal (polarBilin (quadPlus 4 K)) S) :
    g w ∈ LinearMap.BilinForm.orthogonal (polarBilin (quadPlus 4 K)) S := by
  rw [mem_orth_iff] at hw ⊢
  intro n hn
  have h := polar_isometry hg (g (g n)) w
  rw [hg3 n] at h
  rw [h]
  exact hw _ (hS _ (hS _ hn))

omit [Finite K] in
include hg3 in
theorem map_eq_of_invariant {M : Submodule K (Fin 4 ⊕ Fin 4 → K)} (hM : ∀ x ∈ M, g x ∈ M) :
    M.map (g : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) = M := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact hM x hx
  · intro x hx
    exact ⟨g (g x), hM _ (hM _ hx), hg3 x⟩

include h2 hg hsum hg3 hroot in
theorem exists_invariant_maximal_of_noRoot :
    ∃ M : Submodule K (Fin 4 ⊕ Fin 4 → K), M ∈ singularSubspaces (quadPlus 4 K) 4 ∧
      M.map (g : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) = M := by
  classical
  obtain ⟨v₁, -, hv₁0, hv₁⟩ := exists_singular_of_three_le_odd h2 (quadPlus 4 K)
    (S := (⊤ : Submodule K (Fin 4 ⊕ Fin 4 → K))) (by rw [finrank_top, finrank_V8]; norm_num)
  have hP₁s := planeSp_singular h2 hg hsum hg3 hv₁
  have hP₁i : ∀ x ∈ planeSp g v₁, g x ∈ planeSp g v₁ := fun x hx => planeSp_invariant hsum hx
  have hP₁r : finrank K (planeSp g v₁) = 2 := finrank_planeSp hsum hroot hv₁0
  set P₁ := planeSp g v₁ with hP₁
  set U := LinearMap.BilinForm.orthogonal (polarBilin (quadPlus 4 K)) P₁ with hU
  have hP₁U : P₁ ≤ U := fun x hx =>
    mem_orth_iff.2 fun n hn => CFSG.HardMathSupport.Timmesfeld.DFour.polar_eq_zero_of_singular hP₁s hn hx
  have hUi : ∀ w ∈ U, g w ∈ U := fun w hw => orth_invariant hg hg3 hP₁i hw
  have hUr : finrank K U = 6 := by
    have h := LinearMap.BilinForm.finrank_orthogonal (nondegenerate_polarBilin_quadPlus 4 K) P₁
    rw [finrank_V8, hP₁r] at h
    exact h
  obtain ⟨C', hC'⟩ := Submodule.exists_isCompl (P₁.comap U.subtype)
  set C : Submodule K (Fin 4 ⊕ Fin 4 → K) := C'.map U.subtype with hC
  have hCU : C ≤ U := by
    rintro _ ⟨c, -, rfl⟩
    exact c.2
  have hCP : C ⊓ P₁ = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨c, hc, rfl⟩, hxP⟩
    have hc1 : c ∈ P₁.comap U.subtype ⊓ C' := ⟨hxP, hc⟩
    rw [hC'.1.eq_bot, Submodule.mem_bot] at hc1
    rw [hc1, map_zero]
    exact Submodule.zero_mem _
  have hCr : finrank K C = 4 := by
    have h1 := Submodule.finrank_add_eq_of_isCompl hC'
    have h2' : finrank K (P₁.comap U.subtype) = 2 := by
      rw [← Submodule.finrank_map_subtype_eq U (P₁.comap U.subtype), Submodule.map_comap_subtype,
        inf_of_le_right hP₁U, hP₁r]
    have h3' : finrank K C = finrank K C' := Submodule.finrank_map_subtype_eq U C'
    omega
  obtain ⟨w, hwC, hw0, hw⟩ := exists_singular_of_three_le_odd h2 (quadPlus 4 K) (S := C)
    (by rw [hCr]; norm_num)
  have hP₂s := planeSp_singular h2 hg hsum hg3 hw
  have hP₂i : ∀ x ∈ planeSp g w, g x ∈ planeSp g w := fun x hx => planeSp_invariant hsum hx
  have hP₂r : finrank K (planeSp g w) = 2 := finrank_planeSp hsum hroot hw0
  have hwU : w ∈ U := hCU hwC
  have hP₂U : planeSp g w ≤ U := by
    refine Submodule.span_le.2 ?_
    intro x hx
    rcases hx with rfl | rfl
    · exact hwU
    · exact hUi _ hwU
  have hP₁P₂ : ∀ x ∈ P₁, ∀ y ∈ planeSp g w, polar (quadPlus 4 K) x y = 0 := fun x hx y hy =>
    mem_orth_iff.1 (hP₂U hy) x hx
  have hdisj : P₁ ⊓ planeSp g w = ⊥ := by
    by_contra hne
    obtain ⟨s, hs, hs0⟩ := (Submodule.ne_bot_iff _).1 hne
    have hsi : ∀ x ∈ P₁ ⊓ planeSp g w, g x ∈ P₁ ⊓ planeSp g w := fun x hx =>
      ⟨hP₁i x hx.1, hP₂i x hx.2⟩
    have hle : planeSp g s ≤ P₁ ⊓ planeSp g w := by
      refine Submodule.span_le.2 ?_
      intro x hx
      rcases hx with rfl | rfl
      · exact hs
      · exact hsi _ hs
    have hs2 : finrank K (planeSp g s) = 2 := finrank_planeSp hsum hroot hs0
    have heq : planeSp g s = planeSp g w :=
      Submodule.eq_of_le_of_finrank_eq (hle.trans inf_le_right) (by rw [hs2, hP₂r])
    have hwP₂ : w ∈ planeSp g w := Submodule.subset_span (by simp)
    have hwP₁ : w ∈ P₁ := by
      have : w ∈ planeSp g s := by rw [heq]; exact hwP₂
      exact (hle this).1
    have : w ∈ C ⊓ P₁ := ⟨hwC, hwP₁⟩
    rw [hCP, Submodule.mem_bot] at this
    exact hw0 this
  have hMi : ∀ x ∈ P₁ ⊔ planeSp g w, g x ∈ P₁ ⊔ planeSp g w := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add]
    exact Submodule.add_mem_sup (hP₁i a ha) (hP₂i b hb)
  refine ⟨P₁ ⊔ planeSp g w, ⟨?_, ?_⟩, map_eq_of_invariant hg3 hMi⟩
  · have := Submodule.finrank_sup_add_finrank_inf_eq P₁ (planeSp g w)
    rw [hdisj, finrank_bot, hP₁r, hP₂r] at this
    omega
  · intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
    rw [QuadraticMap.map_add (quadPlus 4 K) a b, hP₁s a ha, hP₂s b hb, hP₁P₂ a ha b hb]
    simp

include hsum hroot in
theorem no_invariant_line_of_noRoot :
    IsEmpty {L : Submodule K (Fin 4 ⊕ Fin 4 → K) // L ∈ singularSubspaces (quadPlus 4 K) 1 ∧
      L.map (g : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) = L} := by
  refine ⟨fun ⟨L, ⟨hL1, _⟩, hLi⟩ => ?_⟩
  obtain ⟨v, hv0, hv⟩ := finrank_eq_one_iff'.1 hL1
  have hgv : g (v : Fin 4 ⊕ Fin 4 → K) ∈ L := by
    have : g (v : Fin 4 ⊕ Fin 4 → K) ∈ L.map (g : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) :=
      Submodule.mem_map_of_mem v.2
    rwa [hLi] at this
  obtain ⟨c, hc⟩ := hv ⟨g (v : Fin 4 ⊕ Fin 4 → K), hgv⟩
  have hc' : c • (v : Fin 4 ⊕ Fin 4 → K) = g v := congrArg Subtype.val hc
  have hv0' : (v : Fin 4 ⊕ Fin 4 → K) ≠ 0 := fun h => hv0 (Subtype.ext h)
  have := indep_of_noRoot hsum hroot hv0' (a := -c) (b := 1) (by
    rw [one_smul, neg_smul, ← hc']; abel)
  exact one_ne_zero this.2

include h2 hg hsum hg3 hroot in
theorem ne_two_mul_of_noRoot :
    Nat.card {M : Submodule K (Fin 4 ⊕ Fin 4 → K) // M ∈ singularSubspaces (quadPlus 4 K) 4 ∧
        M.map (g : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) = M} ≠
      2 * Nat.card {L : Submodule K (Fin 4 ⊕ Fin 4 → K) // L ∈ singularSubspaces (quadPlus 4 K) 1 ∧
        L.map (g : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) = L} := by
  haveI := no_invariant_line_of_noRoot hsum hroot (g := g)
  have h0 : Nat.card {L : Submodule K (Fin 4 ⊕ Fin 4 → K) //
      L ∈ singularSubspaces (quadPlus 4 K) 1 ∧
        L.map (g : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) = L} = 0 := Nat.card_of_isEmpty
  rw [h0, mul_zero]
  obtain ⟨M, hM⟩ := exists_invariant_maximal_of_noRoot h2 hg hsum hg3 hroot
  have hfin : Finite {M : Submodule K (Fin 4 ⊕ Fin 4 → K) //
      M ∈ singularSubspaces (quadPlus 4 K) 4 ∧
        M.map (g : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) = M} :=
    Finite.of_injective (fun M => ((M.1 : Set (Fin 4 ⊕ Fin 4 → K)))) fun a b h =>
      Subtype.ext (SetLike.coe_injective h)
  exact (Nat.card_pos_iff.2 ⟨⟨⟨M, hM⟩⟩, hfin⟩).ne'

end CaseB
end Zero

end CFSG.LocalAnalysis.GLTheoremA
