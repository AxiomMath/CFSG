module

public import CFSG.ClassicalGroups.Alternating.I4SpQuadDefs
public import CFSG.ClassicalGroups.Alternating.I4SpPlaneConj

public section

namespace CFSG.ClassicalGroups.Alternating

open LinearMap (BilinForm)
open Module

variable {K : Type*} [Field K] {N : Type*} [AddCommGroup N] [Module K N] {BN : BilinForm K N}

theorem exists_planeFrame_of_basis [FiniteDimensional K N] (hBN : BN.IsAlt)
    (hBNnd : BN.Nondegenerate) {σ σ' : Submodule K N} (hσ : IsPlane BN σ) (hσ' : IsPlane BN σ')
    (hc : IsCompl σ σ') (f : Fin 3 → N) (hf : LinearIndependent K f) (hfσ' : ∀ i, f i ∈ σ') :
    ∃ F : PlaneFrame BN σ, F.f = f := by
  have hy : ∀ j : Fin 3, ∃ y : N, ∀ i : Fin 3, BN (f i) y = if i = j then 1 else 0 := by
    intro j
    obtain ⟨y, hy⟩ := exists_apply_eq_of_linearIndependent hBNnd hf
      (fun i => -(if i = j then 1 else 0))
    refine ⟨y, fun i => neg_inj.mp ?_⟩
    rw [hBN.neg_eq (f i) y, hy i]
  choose y hy using hy
  have hsplit : ∀ j : Fin 3, ∃ e ∈ σ, ∃ z ∈ σ', e + z = y j := by
    intro j
    have hmem : y j ∈ σ ⊔ σ' := by
      rw [hc.sup_eq_top]
      exact Submodule.mem_top
    exact Submodule.mem_sup.mp hmem
  choose e he z hz hez using hsplit
  have hdual : ∀ i j : Fin 3, BN (f i) (e j) = if i = j then 1 else 0 := by
    intro i j
    have h1 : BN (f i) (y j) = BN (f i) (e j) + BN (f i) (z j) := by
      rw [← hez j, map_add]
    have h2 : BN (f i) (z j) = 0 := hσ'.1 _ (hfσ' i) _ (hz j)
    have h3 := hy j i
    rw [h1, h2, add_zero] at h3
    exact h3
  have hli : LinearIndependent K e := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have h := congrArg (BN (f j)) hg
    simpa [map_sum, map_smul, hdual, mul_ite] using h
  have hspan : Submodule.span K (Set.range e) = σ := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rw [Submodule.span_le, Set.range_subset_iff]
      exact he
    · rw [finrank_span_eq_card hli, hσ.2, Fintype.card_fin]
  refine ⟨⟨e, f, he, fun w hw => ?_, hdual⟩, rfl⟩
  have hw' : w ∈ Submodule.span K (Set.range e) := by
    rw [hspan]
    exact hw
  obtain ⟨c, hc'⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hw'
  refine ⟨c 0, c 1, c 2, ?_⟩
  rw [← hc', Fin.sum_univ_three]

theorem exists_isLine_le_singular [Finite K] [CharP K 2] [FiniteDimensional K N]
    (hBN : BN.IsAlt) {π₀ π₀' : Submodule K N} (h : IsCompl π₀ π₀') (hπ₀ : IsPlane BN π₀)
    (hπ₀' : IsPlane BN π₀') {π : Submodule K N} (hπ : IsPlane BN π) :
    ∃ ℓ ≤ π, IsLine BN ℓ ∧ ∀ x ∈ ℓ, quadPlus BN h x = 0 := by
  have hsq : ∀ a : K, ∃ r : K, r ^ 2 = a := fun a => by
    obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) a
    exact ⟨r, by rw [pow_two, ← hr]⟩
  choose s hs using hsq
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hsqinj : ∀ a b : K, a ^ 2 = b ^ 2 → a = b := fun a b hab => CharTwo.sq_inj.mp hab
  have hsadd : ∀ a b : K, s (a + b) = s a + s b := fun a b => by
    apply hsqinj
    linear_combination hs (a + b) - hs a - hs b - (s a * s b) * h2
  have hsmul : ∀ c a : K, s (c ^ 2 * a) = c * s a := fun c a => by
    apply hsqinj
    linear_combination hs (c ^ 2 * a) - c ^ 2 * hs a
  have hs0 : ∀ a : K, s a = 0 → a = 0 := fun a ha => by
    linear_combination -hs a + s a * ha
  have hadd : ∀ x ∈ π, ∀ y ∈ π, quadPlus BN h (x + y) = quadPlus BN h x + quadPlus BN h y := by
    intro x hx y hy
    rw [quadPlus_add h hBN hπ₀.1 hπ₀'.1 x y, hπ.1 x hx y hy, add_zero]
  let ψ : π →ₗ[K] K :=
    { toFun := fun x => s (quadPlus BN h (x : N))
      map_add' := fun x y => by
        simp only [Submodule.coe_add]
        rw [hadd (x : N) x.2 (y : N) y.2, hsadd]
      map_smul' := fun c x => by
        simp only [Submodule.coe_smul, quadPlus_smul, RingHom.id_apply, smul_eq_mul]
        exact hsmul c _ }
  have hrange : finrank K (LinearMap.range ψ) ≤ 1 := by
    calc finrank K (LinearMap.range ψ) ≤ finrank K K := Submodule.finrank_le _
      _ = 1 := by simp
  have hrank := LinearMap.finrank_range_add_finrank_ker ψ
  rw [hπ.2] at hrank
  have hker : 2 ≤ finrank K (LinearMap.ker ψ) := by omega
  have hZ : 2 ≤ finrank K ((LinearMap.ker ψ).map π.subtype) := by
    rw [Submodule.finrank_map_subtype_eq]
    exact hker
  obtain ⟨ℓ, -, hℓZ, hℓ2⟩ := CFSG.Monster.B.TwoA.exists_submodule_between
    (bot_le : (⊥ : Submodule K N) ≤ (LinearMap.ker ψ).map π.subtype) (k := 2) (by simp) hZ
  have hℓπ : ℓ ≤ π := hℓZ.trans (Submodule.map_subtype_le π _)
  refine ⟨ℓ, hℓπ, ⟨fun x hx y hy => hπ.1 x (hℓπ hx) y (hℓπ hy), hℓ2⟩, fun x hx => ?_⟩
  obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.mp (hℓZ hx)
  have hy0 : s (quadPlus BN h (y : N)) = 0 := LinearMap.mem_ker.mp hy
  have hyx' : (y : N) = x := hyx
  rw [← hyx']
  exact hs0 _ hy0

section Graph

variable [CharP K 2] [FiniteDimensional K N] (hBN : BN.IsAlt) (hBNnd : BN.Nondegenerate)

include hBN hBNnd in
theorem exists_mem_planeGroup_map_le {σ σ' ℓ : Submodule K N} (hσ : IsPlane BN σ)
    (hσ' : IsPlane BN σ') (hc : IsCompl σ σ') (hℓ : IsLine BN ℓ) (hdisj : ℓ ⊓ σ = ⊥)
    (hs : ∀ x ∈ σ', ∀ y ∈ σ, x + y ∈ ℓ → BN x y = 0) :
    ∃ g ∈ planeGroup hBN σ, ℓ.map g.lin ≤ σ' := by
  obtain ⟨s₀, s₁, hs01, hind, rfl⟩ := hℓ.exists_pair
  have hs₀ : s₀ ∈ Submodule.span K {s₀, s₁} := Submodule.subset_span (by simp)
  have hs₁ : s₁ ∈ Submodule.span K {s₀, s₁} := Submodule.subset_span (by simp)
  obtain ⟨x₀, hx₀, y₀, hy₀, hxy₀⟩ := exists_add_eq_of_isCompl hc.symm s₀
  obtain ⟨x₁, hx₁, y₁, hy₁, hxy₁⟩ := exists_add_eq_of_isCompl hc.symm s₁
  have hq₀ : BN x₀ y₀ = 0 := hs x₀ hx₀ y₀ hy₀ (hxy₀ ▸ hs₀)
  have hq₁ : BN x₁ y₁ = 0 := hs x₁ hx₁ y₁ hy₁ (hxy₁ ▸ hs₁)
  have hx01 : LinearIndependent K ![x₀, x₁] := by
    rw [LinearIndependent.pair_iff]
    intro α β hαβ
    have h1 : α • s₀ + β • s₁ ∈ Submodule.span K {s₀, s₁} ⊓ σ := by
      refine ⟨Submodule.add_mem _ (Submodule.smul_mem _ _ hs₀) (Submodule.smul_mem _ _ hs₁), ?_⟩
      have : α • s₀ + β • s₁ = α • y₀ + β • y₁ := by
        rw [← hxy₀, ← hxy₁]
        have : α • (x₀ + y₀) + β • (x₁ + y₁) = (α • x₀ + β • x₁) + (α • y₀ + β • y₁) := by module
        rw [this, hαβ, zero_add]
      rw [this]
      exact σ.add_mem (σ.smul_mem _ hy₀) (σ.smul_mem _ hy₁)
    rw [hdisj] at h1
    exact LinearIndependent.pair_iff.mp hind α β ((Submodule.mem_bot K).mp h1)
  obtain ⟨u, huσ', hu⟩ : ∃ u ∈ σ', u ∉ Submodule.span K {x₀, x₁} := by
    by_contra hcon
    push Not at hcon
    have hle : σ' ≤ Submodule.span K {x₀, x₁} := hcon
    have h2 : finrank K ↥(Submodule.span K {x₀, x₁}) = 2 := by
      rw [← Matrix.range_cons_cons_empty x₀ x₁ ![], finrank_span_eq_card hx01, Fintype.card_fin]
    have := Submodule.finrank_mono hle
    rw [hσ'.2, h2] at this
    omega
  have hli : LinearIndependent K ![u, x₀, x₁] := by
    have : LinearIndependent K (Fin.cons u ![x₀, x₁] : Fin 3 → N) := by
      rw [linearIndependent_fin_cons]
      refine ⟨hx01, ?_⟩
      rwa [Matrix.range_cons_cons_empty]
    exact this
  have hfσ' : ∀ i, (![u, x₀, x₁] : Fin 3 → N) i ∈ σ' := by
    intro i
    fin_cases i
    · exact huσ'
    · exact hx₀
    · exact hx₁
  obtain ⟨F, hF⟩ := exists_planeFrame_of_basis hBN hBNnd hσ hσ' hc ![u, x₀, x₁] hli hfσ'
  have hF0 : F.f 0 = u := by rw [hF]; rfl
  have hF1 : F.f 1 = x₀ := by rw [hF]; rfl
  have hF2 : F.f 2 = x₁ := by rw [hF]; rfl
  have hcy₀ := F.coord hy₀
  have hcy₁ := F.coord hy₁
  rw [hF0, hF1, hF2, hq₀] at hcy₀
  rw [hF0, hF1, hF2, hq₁] at hcy₁
  have hc01 : BN x₀ y₁ = BN x₁ y₀ := by
    have h := hs01
    rw [← hxy₀, ← hxy₁] at h
    simp only [map_add, LinearMap.add_apply, hσ'.1 x₀ hx₀ x₁ hx₁, hσ.1 y₀ hy₀ y₁ hy₁, zero_add,
      add_zero] at h
    have := hBN.neg_eq x₁ y₀
    linear_combination h + this
  rw [hc01] at hcy₁
  have d0 : ∀ j, BN x₀ (F.e j) = if (1 : Fin 3) = j then 1 else 0 := fun j => by
    rw [← hF1]; exact F.dual 1 j
  have d1 : ∀ j, BN x₁ (F.e j) = if (2 : Fin 3) = j then 1 else 0 := fun j => by
    rw [← hF2]; exact F.dual 2 j
  have hgx₀ : (F.phi hBN (BN u y₀) (BN u y₁) (BN x₁ y₀)).app x₀ = x₀ + y₀ := by
    rw [PlaneFrame.phi_app F hBN hσ.1, d0 0, d0 1, d0 2]
    conv_rhs => rw [hcy₀]
    simp only [Fin.isValue, one_ne_zero, ↓reduceIte, zero_smul, add_zero, zero_add, one_smul,
      smul_zero, Fin.reduceEq]
    abel
  have hgx₁ : (F.phi hBN (BN u y₀) (BN u y₁) (BN x₁ y₀)).app x₁ = x₁ + y₁ := by
    rw [PlaneFrame.phi_app F hBN hσ.1, d1 0, d1 1, d1 2]
    conv_rhs => rw [hcy₁]
    simp only [Fin.isValue, ↓reduceIte, zero_smul, add_zero, zero_add, one_smul,
      smul_zero, Fin.reduceEq]
    abel
  have hgy : ∀ y ∈ σ, (F.phi hBN (BN u y₀) (BN u y₁) (BN x₁ y₀)).app y = y := by
    intro y hy
    rw [PlaneFrame.phi_app F hBN hσ.1]
    simp [hσ.1 y hy _ (F.mem 0), hσ.1 y hy _ (F.mem 1), hσ.1 y hy _ (F.mem 2)]
  refine ⟨F.phi hBN (BN u y₀) (BN u y₁) (BN x₁ y₀),
    F.phi_mem_planeGroup hBN _ _ _, ?_⟩
  rintro _ ⟨s, hs, rfl⟩
  obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hs
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have e₀ : (F.phi hBN (BN u y₀) (BN u y₁) (BN x₁ y₀)).app s₀ = x₀ := by
    rw [← hxy₀, Gsp.map_add, hgx₀, hgy y₀ hy₀]
    linear_combination (norm := module) h2 • y₀
  have e₁ : (F.phi hBN (BN u y₀) (BN u y₁) (BN x₁ y₀)).app s₁ = x₁ := by
    rw [← hxy₁, Gsp.map_add, hgx₁, hgy y₁ hy₁]
    linear_combination (norm := module) h2 • y₁
  rw [Gsp.lin_apply, Gsp.map_add, Gsp.map_smul, Gsp.map_smul, e₀, e₁]
  exact σ'.add_mem (σ'.smul_mem _ hx₀) (σ'.smul_mem _ hx₁)

end Graph

section Meet

variable [CharP K 2] [FiniteDimensional K N] (hBN : BN.IsAlt) (hBNnd : BN.Nondegenerate)
  {π₀ π₀' : Submodule K N} (h : IsCompl π₀ π₀') (hπ₀ : IsPlane BN π₀) (hπ₀' : IsPlane BN π₀')

omit [FiniteDimensional K N] in
include hBN hπ₀ hπ₀' in
theorem quadPlus_app_lineElt {a c : N} (hac : BN a c = 0) (ha : quadPlus BN h a = 0)
    (hc : quadPlus BN h c = 0) (v : N) :
    quadPlus BN h ((lineElt hBN a c).app v) = quadPlus BN h v := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hca : BN c a = 0 := hBN.eq_iff.mp hac
  rw [lineElt_app hBN hac, quadPlus_add h hBN hπ₀.1 hπ₀'.1, quadPlus_add h hBN hπ₀.1 hπ₀'.1,
    quadPlus_smul, quadPlus_smul, ha, hc]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hca]
  linear_combination (BN v a * BN v c) * h2


include hBN hBNnd h hπ₀ hπ₀' in
theorem exists_mem_planeGroup_of_meet_both {ℓ : Submodule K N} (hℓ : IsLine BN ℓ)
    (hs : ∀ x ∈ ℓ, quadPlus BN h x = 0) (hA : ℓ ⊓ π₀ ≠ ⊥) (hB : ℓ ⊓ π₀' ≠ ⊥) :
    ∃ g ∈ planeGroup hBN π₀', ℓ.map g.lin ⊓ π₀ = ⊥ ∧ IsLine BN (ℓ.map g.lin) ∧
      ∀ x ∈ ℓ.map g.lin, quadPlus BN h x = 0 := by
  obtain ⟨a, haℓ, haπ, ha0⟩ : ∃ a, a ∈ ℓ ∧ a ∈ π₀ ∧ a ≠ 0 := by
    obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hA
    exact ⟨a, ha.1, ha.2, ha0⟩
  obtain ⟨c, hcℓ, hcπ, hc0⟩ : ∃ c, c ∈ ℓ ∧ c ∈ π₀' ∧ c ≠ 0 := by
    obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hB
    exact ⟨c, hc.1, hc.2, hc0⟩
  have hac : BN a c = 0 := hℓ.1 a haℓ c hcℓ
  have hindep : LinearIndependent K ![a, c] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have hst' : s • a = -(t • c) := eq_neg_of_add_eq_zero_left hst
    have hmem : s • a ∈ π₀ ⊓ π₀' :=
      ⟨π₀.smul_mem _ haπ, by rw [hst']; exact π₀'.neg_mem (π₀'.smul_mem _ hcπ)⟩
    have h0 : s • a = 0 := (Submodule.mem_bot K).mp (h.inf_eq_bot ▸ hmem)
    have hs0 : s = 0 := (smul_eq_zero.mp h0).resolve_right ha0
    rw [hs0, zero_smul, zero_add] at hst
    exact ⟨hs0, (smul_eq_zero.mp hst).resolve_right hc0⟩
  have hℓspan : ℓ = Submodule.span K {a, c} := by
    refine (Submodule.eq_of_le_of_finrank_eq ?_ ?_).symm
    · rw [Submodule.span_le]
      rintro _ (rfl | rfl)
      · exact haℓ
      · exact hcℓ
    · rw [← Matrix.range_cons_cons_empty a c ![], finrank_span_eq_card hindep, Fintype.card_fin,
        hℓ.2]
  obtain ⟨y, hy⟩ : ∃ y, BN a y ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact ha0 (hBNnd.1 a hcon)
  obtain ⟨y₀, hy₀, y₁, hy₁, rfl⟩ := exists_add_eq_of_isCompl h y
  have hay₁ : BN a y₁ ≠ 0 := by
    have : BN a (y₀ + y₁) = BN a y₁ := by rw [map_add, hπ₀.1 a haπ y₀ hy₀, zero_add]
    rwa [this] at hy
  have ha'π : (BN a y₁)⁻¹ • y₁ ∈ π₀' := π₀'.smul_mem _ hy₁
  have haa' : BN a ((BN a y₁)⁻¹ • y₁) = 1 := by
    rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hay₁]
  let φ : ↥π₀' →ₗ[K] K := (BN a).comp π₀'.subtype
  let Z : Submodule K N := (LinearMap.ker φ).map π₀'.subtype
  have hZdim : 2 ≤ finrank K Z := by
    have h3 := hπ₀'.2
    have h1 := LinearMap.finrank_range_add_finrank_ker φ
    have h2 : finrank K (LinearMap.range φ) ≤ 1 := by
      have := Submodule.finrank_le (LinearMap.range φ)
      rwa [Module.finrank_self] at this
    rw [Submodule.finrank_map_subtype_eq]
    omega
  have hZmem : ∀ z ∈ Z, z ∈ π₀' ∧ BN a z = 0 := by
    rintro _ ⟨⟨z, hz⟩, hzk, rfl⟩
    exact ⟨hz, hzk⟩
  have hcZ : c ∈ Z := ⟨⟨c, hcπ⟩, hac, rfl⟩
  obtain ⟨c', hc'Z, hind'⟩ := exists_mem_linearIndependent_pair hZdim hcZ hc0
  obtain ⟨hc'π, hac'⟩ := hZmem c' hc'Z
  have hgm : lineElt hBN ((BN a y₁)⁻¹ • y₁) c' ∈ planeGroup hBN π₀' :=
    lineElt_mem_planeGroup hBN ha'π hc'π
  have hxy : BN ((BN a y₁)⁻¹ • y₁) c' = 0 := hπ₀'.1 _ ha'π _ hc'π
  have hga : (lineElt hBN ((BN a y₁)⁻¹ • y₁) c').app a = a + c' := by
    rw [lineElt_app hBN hxy, haa', hac']
    simp
  have hgc : (lineElt hBN ((BN a y₁)⁻¹ • y₁) c').app c = c := by
    rw [lineElt_app hBN hxy, hπ₀'.1 c hcπ _ ha'π, hπ₀'.1 c hcπ c' hc'π]
    simp
  have hmap : ℓ.map (lineElt hBN ((BN a y₁)⁻¹ • y₁) c').lin = Submodule.span K {a + c', c} := by
    rw [hℓspan, Submodule.map_span, Set.image_pair, Gsp.lin_apply, Gsp.lin_apply, hga, hgc]
  refine ⟨_, hgm, ?_, hℓ.map _, ?_⟩
  · rw [hmap, eq_bot_iff]
    rintro v ⟨hvℓ, hvπ⟩
    obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hvℓ
    have h1 : β • c + α • c' ∈ π₀ := by
      have := π₀.sub_mem hvπ (π₀.smul_mem α haπ)
      convert this using 1
      module
    have h2 : β • c + α • c' ∈ π₀' := π₀'.add_mem (π₀'.smul_mem _ hcπ) (π₀'.smul_mem _ hc'π)
    have h0 : β • c + α • c' = 0 :=
      (Submodule.mem_bot K).mp (h.inf_eq_bot ▸ (⟨h1, h2⟩ : _ ∈ π₀ ⊓ π₀'))
    obtain ⟨hβ, hα⟩ := LinearIndependent.pair_iff.mp hind' β α h0
    rw [hα, hβ]
    simp
  · intro x hx
    obtain ⟨v, hv, rfl⟩ := hx
    rw [Gsp.lin_apply, quadPlus_app_lineElt hBN h hπ₀ hπ₀' hxy
      (quadPlus_of_mem_right h ha'π) (quadPlus_of_mem_right h hc'π)]
    exact hs v hv


omit [CharP K 2] [FiniteDimensional K N] in
theorem map_lin_mul (g g' : Gsp BN) (S : Submodule K N) :
    S.map (g * g').lin = (S.map g'.lin).map g.lin := by
  ext x
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨g'.app s, ⟨s, hs, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    exact ⟨s, hs, rfl⟩

include hBN hBNnd h hπ₀ hπ₀' in
theorem planeGroup_le_sup_of_singular {ℓ : Submodule K N} (hℓ : IsLine BN ℓ)
    (hs : ∀ x ∈ ℓ, quadPlus BN h x = 0) :
    planeGroup hBN ℓ ≤ planeGroup hBN π₀ ⊔ planeGroup hBN π₀' := by
  have hπ0le : planeGroup hBN π₀ ≤ planeGroup hBN π₀ ⊔ planeGroup hBN π₀' := le_sup_left
  have hπ0'le : planeGroup hBN π₀' ≤ planeGroup hBN π₀ ⊔ planeGroup hBN π₀' := le_sup_right
  have hsA : ∀ {ℓ' : Submodule K N}, (∀ x ∈ ℓ', quadPlus BN h x = 0) →
      ∀ x ∈ π₀, ∀ y ∈ π₀', x + y ∈ ℓ' → BN x y = 0 := by
    intro ℓ' hs' x hx y hy hxy
    rw [← quadPlus_add_of_mem h hx hy]
    exact hs' _ hxy
  have hsB : ∀ {ℓ' : Submodule K N}, (∀ x ∈ ℓ', quadPlus BN h x = 0) →
      ∀ x ∈ π₀', ∀ y ∈ π₀, x + y ∈ ℓ' → BN x y = 0 := by
    intro ℓ' hs' x hx y hy hxy
    have h0 := hs' _ hxy
    rw [add_comm, quadPlus_add_of_mem h hy hx] at h0
    exact (form_comm_charTwo hBN x y).trans h0
  have claim : ∃ g ∈ planeGroup hBN π₀ ⊔ planeGroup hBN π₀',
      ℓ.map g.lin ≤ π₀ ∨ ℓ.map g.lin ≤ π₀' := by
    by_cases hA : ℓ ⊓ π₀' = ⊥
    · obtain ⟨g, hg, hle⟩ := exists_mem_planeGroup_map_le hBN hBNnd hπ₀' hπ₀ h.symm hℓ hA (hsA hs)
      exact ⟨g, hπ0'le hg, Or.inl hle⟩
    by_cases hB : ℓ ⊓ π₀ = ⊥
    · obtain ⟨g, hg, hle⟩ := exists_mem_planeGroup_map_le hBN hBNnd hπ₀ hπ₀' h hℓ hB (hsB hs)
      exact ⟨g, hπ0le hg, Or.inr hle⟩
    obtain ⟨g₀, hg₀, hdisj, hℓ₁, hs₁⟩ :=
      exists_mem_planeGroup_of_meet_both hBN hBNnd h hπ₀ hπ₀' hℓ hs hB hA
    obtain ⟨g₁, hg₁, hle₁⟩ := exists_mem_planeGroup_map_le hBN hBNnd hπ₀ hπ₀' h hℓ₁ hdisj (hsB hs₁)
    refine ⟨g₁ * g₀, mul_mem (hπ0le hg₁) (hπ0'le hg₀), Or.inr ?_⟩
    rw [map_lin_mul]
    exact hle₁
  obtain ⟨g, hgS, hle | hle⟩ := claim
  · intro x hx
    have h1 : g * x * g⁻¹ ∈ planeGroup hBN (ℓ.map g.lin) :=
      (conj_mem_planeGroup_map_iff hBN g x ℓ).mpr hx
    have h2 := hπ0le (planeGroup_mono hBN hle h1)
    have := mul_mem (mul_mem (inv_mem hgS) h2) hgS
    simpa [mul_assoc] using this
  · intro x hx
    have h1 : g * x * g⁻¹ ∈ planeGroup hBN (ℓ.map g.lin) :=
      (conj_mem_planeGroup_map_iff hBN g x ℓ).mpr hx
    have h2 := hπ0'le (planeGroup_mono hBN hle h1)
    have := mul_mem (mul_mem (inv_mem hgS) h2) hgS
    simpa [mul_assoc] using this

end Meet

end CFSG.ClassicalGroups.Alternating
