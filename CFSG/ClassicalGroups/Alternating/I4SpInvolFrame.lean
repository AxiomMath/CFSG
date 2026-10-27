module

public import CFSG.ClassicalGroups.Alternating.I4SpInvolBasic
public import CFSG.ClassicalGroups.Alternating.I4SpLineElt

public section

namespace CFSG.ClassicalGroups.Alternating

open LinearMap (BilinForm)

variable {K N : Type*} [Field K] [AddCommGroup N] [Module K N] {BN : BilinForm K N}

theorem exists_hyperbolic_frame [CharP K 2] (hBN : BN.IsAlt) (hBNnd : BN.Nondegenerate)
    {t : Gsp BN} (ht : t * t = 1) (ht1 : t ≠ 1) (hf : ∀ x, t.ft x = 0) :
    ∃ a c w v : N, BN a c = 0 ∧ BN w v = 0 ∧ BN a w = 1 ∧ BN c v = 1 ∧ BN a v = 0 ∧
      BN c w = 0 ∧ t.app v = v + a ∧ t.app w = w + c ∧ t.app a = a ∧ t.app c = c := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have happ : ∀ x, t.app x = x + t.phi x := fun x => by
    rw [Gsp.phi_apply]
    abel
  have hφφ : ∀ x, t.phi (t.phi x) = 0 := fun x => Gsp.phi_phi ht x
  have hPP : ∀ x y, BN (t.phi x) (t.phi y) = 0 := fun x y => Gsp.form_phi_phi ht x y
  have hL : ∀ x y, BN (t.phi x) y = BN x (t.phi y) := fun x y => Gsp.form_phi_left ht x y
  have hsymm : ∀ x y, BN x y = BN y x := fun x y => form_comm_charTwo hBN x y
  have hself : ∀ x, BN x (t.phi x) = 0 := fun x => by
    rw [← Gsp.ft_eq_form_phi hBN t x]
    exact hf x
  obtain ⟨v, hv⟩ : ∃ v : N, t.phi v ≠ 0 := by
    by_contra h
    push Not at h
    refine ht1 (Gsp.ext' fun x => ?_)
    rw [Gsp.app_one, happ x, h x, add_zero]
  obtain ⟨w₀, hw₀⟩ : ∃ w₀ : N, BN (t.phi v) w₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (hBNnd.1 _ h)
  obtain ⟨w₁, haw₁⟩ : ∃ w₁ : N, BN (t.phi v) w₁ = 1 :=
    ⟨(BN (t.phi v) w₀)⁻¹ • w₀, by rw [_root_.map_smul, smul_eq_mul, inv_mul_cancel₀ hw₀]⟩
  have hcv : BN (t.phi w₁) v = 1 := by
    rw [hL w₁ v, hsymm w₁ (t.phi v), haw₁]
  have hφw : t.phi (w₁ + BN v w₁ • t.phi w₁) = t.phi w₁ := by
    simp only [_root_.map_add, _root_.map_smul, hφφ, smul_zero, add_zero]
  refine ⟨t.phi v, t.phi w₁, w₁ + BN v w₁ • t.phi w₁, v, ?_, ?_, ?_, hcv, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hPP v w₁
  · simp only [_root_.map_add, _root_.map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      smul_eq_mul]
    rw [hcv, mul_one, hsymm w₁ v, ← two_mul, h2, zero_mul]
  · simp only [_root_.map_add, _root_.map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      smul_eq_mul]
    rw [haw₁, hPP v w₁, mul_zero, add_zero]
  · rw [hsymm (t.phi v) v]
    exact hself v
  · simp only [_root_.map_add, _root_.map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      smul_eq_mul]
    rw [hsymm (t.phi w₁) w₁, hself w₁, hBN.self_eq_zero (t.phi w₁), mul_zero, add_zero]
  · exact happ v
  · rw [happ, hφw]
  · rw [happ, hφφ, add_zero]
  · rw [happ, hφφ, add_zero]

theorem mem_orthogonal_span_four {a c w v x : N} :
    x ∈ BN.orthogonal (Submodule.span K ({a, c, w, v} : Set N)) ↔
      BN a x = 0 ∧ BN c x = 0 ∧ BN w x = 0 ∧ BN v x = 0 := by
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · intro h
    exact ⟨h a (Submodule.subset_span (by simp)), h c (Submodule.subset_span (by simp)),
      h w (Submodule.subset_span (by simp)), h v (Submodule.subset_span (by simp))⟩
  · rintro ⟨ha, hc, hw, hv⟩ n hn
    induction hn using Submodule.span_induction with
    | mem m hm =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
      rcases hm with rfl | rfl | rfl | rfl <;> assumption
    | zero => simp
    | add m₁ m₂ _ _ h₁ h₂ => simp [h₁, h₂]
    | smul r m _ h => simp [h]

theorem isCompl_span_four_orthogonal [CharP K 2] (hBN : BN.IsAlt) {a c w v : N}
    (hac : BN a c = 0) (hwv : BN w v = 0) (haw : BN a w = 1) (hcv : BN c v = 1)
    (hav : BN a v = 0) (hcw : BN c w = 0) :
    IsCompl (Submodule.span K ({a, c, w, v} : Set N))
      (BN.orthogonal (Submodule.span K ({a, c, w, v} : Set N))) := by
  have hca : BN c a = 0 := (form_comm_charTwo hBN a c).symm.trans hac
  have hvw : BN v w = 0 := (form_comm_charTwo hBN w v).symm.trans hwv
  have hwa : BN w a = 1 := (form_comm_charTwo hBN a w).symm.trans haw
  have hvc : BN v c = 1 := (form_comm_charTwo hBN c v).symm.trans hcv
  have hva : BN v a = 0 := (form_comm_charTwo hBN a v).symm.trans hav
  have hwc : BN w c = 0 := (form_comm_charTwo hBN c w).symm.trans hcw
  have haa : BN a a = 0 := hBN.self_eq_zero a
  have hcc : BN c c = 0 := hBN.self_eq_zero c
  have hww : BN w w = 0 := hBN.self_eq_zero w
  have hvv : BN v v = 0 := hBN.self_eq_zero v
  refine ⟨?_, ?_⟩
  ·
    rw [disjoint_iff, Submodule.eq_bot_iff]
    intro x hx
    rw [Submodule.mem_inf, mem_orthogonal_span_four] at hx
    obtain ⟨hxX, hBa, hBc, hBw, hBv⟩ := hx
    obtain ⟨α, z₁, hz₁, rfl⟩ := Submodule.mem_span_insert.1 hxX
    obtain ⟨β, z₂, hz₂, rfl⟩ := Submodule.mem_span_insert.1 hz₁
    obtain ⟨γ, z₃, hz₃, rfl⟩ := Submodule.mem_span_insert.1 hz₂
    obtain ⟨δ, rfl⟩ := Submodule.mem_span_singleton.1 hz₃
    simp only [map_add, map_smul, smul_eq_mul, haa, hac, haw, hav, hca, hcc, hcw, hcv, hwa,
      hwc, hww, hwv, hva, hvc, hvw, hvv, mul_zero, zero_mul, mul_one, add_zero, zero_add]
      at hBa hBc hBw hBv
    have hγ : γ = 0 := by linear_combination hBa
    have hδ : δ = 0 := by linear_combination hBc
    have hα : α = 0 := by linear_combination hBw
    have hβ : β = 0 := by linear_combination hBv
    subst hα hβ hγ hδ
    simp
  ·
    rw [codisjoint_iff, Submodule.eq_top_iff']
    intro x
    rw [Submodule.mem_sup]
    refine ⟨BN x w • a + BN x v • c + BN x a • w + BN x c • v, ?_,
      x - (BN x w • a + BN x v • c + BN x a • w + BN x c • v), ?_, by abel⟩
    · exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    · rw [mem_orthogonal_span_four]
      simp only [map_sub, map_add, map_smul, smul_eq_mul, haa, hac, haw, hav, hca, hcc, hcw,
        hcv, hwa, hwc, hww, hwv, hva, hvc, hvw, hvv, mul_zero, zero_mul, mul_one, add_zero,
        zero_add]
      refine ⟨?_, ?_, ?_, ?_⟩
      · linear_combination form_comm_charTwo hBN a x
      · linear_combination form_comm_charTwo hBN c x
      · linear_combination form_comm_charTwo hBN w x
      · linear_combination form_comm_charTwo hBN v x

theorem mem_orthogonal_span_pair {a b x : N} :
    x ∈ BN.orthogonal (Submodule.span K ({a, b} : Set N)) ↔ BN a x = 0 ∧ BN b x = 0 := by
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · intro h
    exact ⟨h a (Submodule.mem_span_pair.mpr ⟨1, 0, by simp⟩),
      h b (Submodule.mem_span_pair.mpr ⟨0, 1, by simp⟩)⟩
  · rintro ⟨ha, hb⟩ n hn
    obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hn
    simp [map_add, map_smul, ha, hb]

theorem isCompl_span_pair_orthogonal (hBN : BN.IsAlt) {a b : N} (hab : BN a b ≠ 0) :
    IsCompl (Submodule.span K ({a, b} : Set N))
      (BN.orthogonal (Submodule.span K ({a, b} : Set N))) := by
  have haa : BN a a = 0 := hBN.self_eq_zero a
  have hbb : BN b b = 0 := hBN.self_eq_zero b
  have hba : BN b a = -BN a b := (hBN.neg_eq a b).symm
  have hxa : ∀ x, BN x a = -BN a x := fun x => (hBN.neg_eq a x).symm
  have hxb : ∀ x, BN x b = -BN b x := fun x => (hBN.neg_eq b x).symm
  have ha : a ∈ Submodule.span K ({a, b} : Set N) := Submodule.mem_span_pair.mpr ⟨1, 0, by simp⟩
  have hb : b ∈ Submodule.span K ({a, b} : Set N) := Submodule.mem_span_pair.mpr ⟨0, 1, by simp⟩
  refine ⟨?_, ?_⟩
  · rw [Submodule.disjoint_def]
    intro x hxX hxY
    obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hxX
    obtain ⟨h1, h2⟩ := mem_orthogonal_span_pair.mp hxY
    simp only [map_add, map_smul, haa, hbb, hba, smul_eq_mul, mul_zero, zero_add,
      add_zero] at h1 h2
    have hβ : β = 0 := (mul_eq_zero.mp h1).resolve_right hab
    have hα : α = 0 := by
      have h3 : α * BN a b = 0 := by linear_combination (-1 : K) * h2
      exact (mul_eq_zero.mp h3).resolve_right hab
    simp [hα, hβ]
  · rw [codisjoint_iff, Submodule.eq_top_iff']
    intro x
    obtain ⟨p, hp⟩ : ∃ p : N, p = (BN a b)⁻¹ • (BN x b • a - BN x a • b) := ⟨_, rfl⟩
    have hpX : p ∈ Submodule.span K ({a, b} : Set N) := by
      rw [hp]
      exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.smul_mem _ _ ha)
        (Submodule.smul_mem _ _ hb))
    have hinv : (BN a b)⁻¹ * BN a b = 1 := inv_mul_cancel₀ hab
    have hpa : BN a p = -BN x a := by
      simp only [hp, map_smul, map_sub, haa, smul_eq_mul]
      linear_combination (-(BN x a)) * hinv
    have hpb : BN b p = -BN x b := by
      simp only [hp, map_smul, map_sub, hbb, hba, smul_eq_mul]
      linear_combination (-(BN x b)) * hinv
    have hza : BN a (x - p) = 0 := by
      rw [map_sub, hpa, hxa x]
      ring
    have hzb : BN b (x - p) = 0 := by
      rw [map_sub, hpb, hxb x]
      ring
    rw [Submodule.mem_sup]
    exact ⟨p, hpX, x - p, mem_orthogonal_span_pair.mpr ⟨hza, hzb⟩, by abel⟩

theorem lineElt_mul_lineElt_app_of_dual (hBN : BN.IsAlt) {a c w v : N} (hac : BN a c = 0)
    (hwv : BN w v = 0) (hva : BN v a = 0) (hwa : BN w a = 1) (hvc : BN v c = 1)
    (hwc : BN w c = 0) (x : N) :
    (lineElt hBN a c * lineElt hBN w v : Gsp BN).app x =
      x + (BN x c + BN x w) • a + (BN x a + BN x v) • c + BN x v • w + BN x w • v := by
  rw [Gsp.app_mul, lineElt_app hBN hac, lineElt_app hBN hwv]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    hva, hwa, hvc, hwc]
  module

theorem orderOf_lineElt_mul_lineElt [CharP K 2] (hBN : BN.IsAlt) {a c w v : N}
    (hac : BN a c = 0) (hwv : BN w v = 0) (haw : BN a w = 1) (hcv : BN c v = 1)
    (hav : BN a v = 0) (hcw : BN c w = 0) :
    orderOf (lineElt hBN a c * lineElt hBN w v) = 3 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hca : BN c a = 0 := (form_comm_charTwo hBN c a).trans hac
  have hvw : BN v w = 0 := (form_comm_charTwo hBN v w).trans hwv
  have hwa : BN w a = 1 := (form_comm_charTwo hBN w a).trans haw
  have hvc : BN v c = 1 := (form_comm_charTwo hBN v c).trans hcv
  have hva : BN v a = 0 := (form_comm_charTwo hBN v a).trans hav
  have hwc : BN w c = 0 := (form_comm_charTwo hBN w c).trans hcw
  obtain ⟨P, hPdef⟩ : ∃ P : Gsp BN, P = lineElt hBN a c * lineElt hBN w v := ⟨_, rfl⟩
  rw [← hPdef]
  have hP : ∀ x : N, P.app x = x + (BN x c + BN x w) • a + (BN x a + BN x v) • c +
      BN x v • w + BN x w • v := fun x => by
    rw [hPdef]
    exact lineElt_mul_lineElt_app_of_dual hBN hac hwv hva hwa hvc hwc x
  have hA : ∀ y : N, BN (P.app y) a = BN y a + BN y v := by
    intro y
    rw [hP y]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      hBN.self_eq_zero, hca, hwa, hva]
    ring
  have hC : ∀ y : N, BN (P.app y) c = BN y c + BN y w := by
    intro y
    rw [hP y]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      hBN.self_eq_zero, hac, hvc, hwc]
    ring
  have hW : ∀ y : N, BN (P.app y) w = BN y c := by
    intro y
    rw [hP y]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      hBN.self_eq_zero, haw, hcw, hvw]
    linear_combination (BN y w) * h2
  have hV : ∀ y : N, BN (P.app y) v = BN y a := by
    intro y
    rw [hP y]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      hBN.self_eq_zero, hav, hcv, hwv]
    linear_combination (BN y v) * h2
  have hcube : ∀ x : N, P.app (P.app (P.app x)) = x := by
    intro x
    rw [hP (P.app (P.app x)), hC (P.app x), hW (P.app x), hA (P.app x), hV (P.app x),
      hP (P.app x), hC x, hW x, hA x, hV x, hP x]
    linear_combination (norm := module) h2 •
      ((3 * BN x c + 2 * BN x w) • a + (3 * BN x a + 2 * BN x v) • c +
        (BN x a + BN x v) • w + (BN x c + BN x w) • v)
  have hP3 : P ^ 3 = 1 := by
    refine Gsp.ext' fun x => ?_
    rw [pow_three, Gsp.app_mul, Gsp.app_mul, Gsp.app_one]
    exact hcube x
  have hPa : P.app a = v := by
    rw [hP a, hac, haw, hav, hBN.self_eq_zero a]
    linear_combination (norm := module) h2 • a
  have hne : P ≠ 1 := by
    intro h
    have h1 : P.app a = a := by rw [h, Gsp.app_one]
    have hva' : v = a := hPa.symm.trans h1
    have h01 : BN v w = BN a w := by rw [hva']
    rw [hvw, haw] at h01
    exact zero_ne_one h01
  exact orderOf_eq_prime hP3 hne

end CFSG.ClassicalGroups.Alternating
