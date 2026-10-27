module

public import CFSG.ClassicalGroups.Alternating.I4SpInvolFrame

public section

namespace CFSG.ClassicalGroups.Alternating

open LinearMap (BilinForm)
open Module

variable {K N : Type*} [Field K] [AddCommGroup N] [Module K N] {BN : BilinForm K N}

structure Gsp.Block (t : Gsp BN) (X : Submodule K N) (τ h : Gsp BN) : Prop where
  isCompl : IsCompl X (BN.orthogonal X)
  maps : ∀ x ∈ X, t.app x ∈ X
  tau_mul_self : τ * τ = 1
  tau_eq : ∀ x ∈ X, τ.app x = t.app x
  tau_orth : ∀ x ∈ BN.orthogonal X, τ.app x = x
  commute : ∀ g : Gsp BN, (∀ x ∈ X, g.app x = x) → Commute g τ ∧ Commute g h
  order_three : orderOf (τ * (h * τ * h⁻¹)) = 3

theorem Gsp.Block.fixes {t X τ h} (hb : Gsp.Block (BN := BN) t X τ h) :
    ∀ x ∈ X, (τ * t).app x = x := by
  intro x hx
  rw [Gsp.app_mul, ← hb.tau_eq x hx, ← Gsp.app_mul, hb.tau_mul_self, Gsp.app_one]

theorem Tsp_mul_Tsp_app_left [CharP K 2] (hBN : BN.IsAlt) {a b : N} (hab : BN a b ≠ 0) :
    (Tsp hBN a (BN a b)⁻¹ * Tsp hBN b (BN a b)⁻¹).app a = b := by
  have hcζ : (BN a b)⁻¹ * BN a b = 1 := inv_mul_cancel₀ hab
  have hba : BN b a = BN a b := form_comm_charTwo hBN b a
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [Gsp.app_mul, Tsp_app, Tsp_app, hcζ, one_smul]
  simp only [map_add, LinearMap.add_apply, hBN.self_eq_zero, hba, zero_add, hcζ, one_smul]
  have : a + b + a = b + (2 : K) • a := by module
  rw [this, h2, zero_smul, add_zero]

theorem pow_three_eq_one_of_conj_eq {G : Type*} [Group G] {X Y : G} (hXX : X * X = 1)
    (hYY : Y * Y = 1) (hw : (X * Y * X) * X * (X * Y * X)⁻¹ = Y) : (X * Y) ^ 3 = 1 := by
  have hXi : X⁻¹ = X := inv_eq_of_mul_eq_one_right hXX
  have hYi : Y⁻¹ = Y := inv_eq_of_mul_eq_one_right hYY
  rw [mul_inv_rev, mul_inv_rev, hXi, hYi] at hw
  have h1 : X * Y * X * Y * X = Y := by
    calc X * Y * X * Y * X = X * Y * (X * X) * X * Y * X := by rw [hXX]; group
      _ = X * Y * X * X * (X * (Y * X)) := by group
      _ = Y := hw
  calc (X * Y) ^ 3 = (X * Y * X * Y * X) * Y := by rw [pow_succ, pow_succ, pow_one]; group
    _ = Y * Y := by rw [h1]
    _ = 1 := hYY

theorem orderOf_Tsp_mul_Tsp [CharP K 2] (hBN : BN.IsAlt) {a b : N} (hab : BN a b ≠ 0) :
    orderOf (Tsp hBN a (BN a b)⁻¹ * Tsp hBN b (BN a b)⁻¹) = 3 := by
  have hcζ : (BN a b)⁻¹ * BN a b = 1 := inv_mul_cancel₀ hab
  have hrel : (BN a b)⁻¹ * (BN a b)⁻¹ * BN a b ^ 2 = 1 := by
    linear_combination ((BN a b)⁻¹ * BN a b + 1) * hcζ
  have hw := Tsp_mul_Tsp_mul_Tsp_conj hBN hrel (BN a b)⁻¹
  rw [hcζ, one_pow, one_mul] at hw
  have h3 := pow_three_eq_one_of_conj_eq (Tsp_mul_self hBN a (BN a b)⁻¹)
    (Tsp_mul_self hBN b (BN a b)⁻¹) hw
  have hne : Tsp hBN a (BN a b)⁻¹ * Tsp hBN b (BN a b)⁻¹ ≠ 1 := by
    intro h
    have hXY : Tsp hBN a (BN a b)⁻¹ = Tsp hBN b (BN a b)⁻¹ := by
      have : Tsp hBN a (BN a b)⁻¹ = (Tsp hBN b (BN a b)⁻¹)⁻¹ := eq_inv_of_mul_eq_one_left h
      rw [this]
      exact inv_eq_of_mul_eq_one_right (Tsp_mul_self hBN b _)
    have hb := congrArg (fun g : Gsp BN => g.app b) hXY
    simp only [Tsp_app, hBN.self_eq_zero, mul_zero, zero_smul, add_zero] at hb
    have hba : BN b a = BN a b := form_comm_charTwo hBN b a
    rw [hba, hcζ, one_smul, add_eq_left] at hb
    exact hab (by rw [hb, map_zero, LinearMap.zero_apply])
  exact orderOf_eq_prime h3 hne

theorem finrank_span_pair_of_form_ne_zero (hBN : BN.IsAlt) {a b : N} (hab : BN a b ≠ 0) :
    finrank K (Submodule.span K ({a, b} : Set N)) = 2 := by
  have hli : LinearIndependent K ![a, b] := by
    rw [LinearIndependent.pair_iff]
    intro s u hsu
    have h1 := congrArg (fun x => BN x b) hsu
    have h2 := congrArg (fun x => BN a x) hsu
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      hBN.self_eq_zero, mul_zero, add_zero, zero_add, map_zero, LinearMap.zero_apply] at h1 h2
    exact ⟨(mul_eq_zero.mp h1).resolve_right hab, (mul_eq_zero.mp h2).resolve_right hab⟩
  have h := finrank_span_eq_card hli
  rw [Fintype.card_fin] at h
  rwa [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
    Set.singleton_union] at h

theorem exists_block_of_ft_ne_zero [CharP K 2] (hBN : BN.IsAlt) {t : Gsp BN} (ht : t * t = 1)
    {v : N} (hv : t.ft v ≠ 0) :
    ∃ (X : Submodule K N) (τ h : Gsp BN), t.Block X τ h ∧ finrank K X = 2 ∧
      (τ * t = 1 → finrank K (LinearMap.range t.phi) = 1) := by
  set a := t.phi v with ha
  have hva : BN v a = t.ft v := (Gsp.ft_eq_form_phi hBN t v).symm
  have hav : BN a v = t.ft v := (form_comm_charTwo hBN a v).trans hva
  have hab : BN a v ≠ 0 := hav ▸ hv
  have hta : t.app a = a := by
    have h0 := Gsp.phi_phi ht v
    rw [← ha, Gsp.phi_apply, sub_eq_zero] at h0
    exact h0
  have htv : t.app v = v + a := by
    rw [ha, Gsp.phi_apply]
    abel
  set c : K := (BN a v)⁻¹ with hc
  have hcζ : c * BN a v = 1 := inv_mul_cancel₀ hab
  have haX : a ∈ Submodule.span K ({a, v} : Set N) := Submodule.subset_span (by simp)
  have hvX : v ∈ Submodule.span K ({a, v} : Set N) := Submodule.subset_span (by simp)
  have ha0 : a ≠ 0 := by
    rintro h0
    apply hab
    rw [h0, map_zero, LinearMap.zero_apply]
  refine ⟨Submodule.span K {a, v}, Tsp hBN a c, Tsp hBN a c * Tsp hBN v c, ⟨?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩, finrank_span_pair_of_form_ne_zero hBN hab, ?_⟩
  · exact isCompl_span_pair_orthogonal hBN hab
  · intro x hx
    obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hx
    rw [Gsp.map_add, Gsp.map_smul, Gsp.map_smul, hta, htv]
    exact Submodule.mem_span_pair.mpr ⟨α + β, β, by module⟩
  · exact Tsp_mul_self hBN a c
  · intro x hx
    obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hx
    rw [Tsp_app, Gsp.map_add, Gsp.map_smul, Gsp.map_smul, hta, htv]
    have hxa : BN (α • a + β • v) a = β * BN a v := by
      rw [map_add, map_smul, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
        LinearMap.smul_apply, hBN.self_eq_zero, hva, hav, smul_eq_mul, smul_eq_mul, mul_zero,
        zero_add]
    rw [hxa]
    have : (c * (β * BN a v)) = β := by linear_combination β * hcζ
    rw [this]
    module
  · intro x hx
    have h1 := (mem_orthogonal_span_pair.mp hx).1
    exact Tsp_app_of_form_eq_zero hBN c ((form_comm_charTwo hBN x a).trans h1)
  · intro g hg
    have hga : g.app a = a := hg a haX
    have hgv : g.app v = v := hg v hvX
    exact ⟨commute_Tsp_of_app_eq hBN c hga,
      (commute_Tsp_of_app_eq hBN c hga).mul_right (commute_Tsp_of_app_eq hBN c hgv)⟩
  · have hconj := Tsp_conj hBN (Tsp hBN a c * Tsp hBN v c) a c
    rw [Tsp_mul_Tsp_app_left hBN hab] at hconj
    rw [hconj]
    exact orderOf_Tsp_mul_Tsp hBN hab
  · intro h1
    have htτ : t = Tsp hBN a c := by
      have h2 : t = (Tsp hBN a c)⁻¹ := eq_inv_of_mul_eq_one_right h1
      rw [h2]
      exact inv_eq_of_mul_eq_one_right (Tsp_mul_self hBN a c)
    have hrange : LinearMap.range t.phi = Submodule.span K {a} := by
      apply le_antisymm
      · rintro _ ⟨x, rfl⟩
        rw [Gsp.phi_apply, htτ, Tsp_app, add_sub_cancel_left]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self a)
      · rw [Submodule.span_singleton_le_iff_mem]
        exact ⟨v, rfl⟩
    rw [hrange]
    exact finrank_span_singleton ha0

theorem exists_block_of_ft_eq_zero [CharP K 2] (hBN : BN.IsAlt) (hBNnd : BN.Nondegenerate)
    {t : Gsp BN} (ht : t * t = 1) (ht1 : t ≠ 1) (hf : ∀ x, t.ft x = 0) :
    ∃ (X : Submodule K N) (τ h : Gsp BN), t.Block X τ h ∧
      (τ * t = 1 → ∃ a c, BN a c = 0 ∧ LinearIndependent K ![a, c] ∧ t = lineElt hBN a c) := by
  obtain ⟨a, c, w, v, hac, hwv, haw, hcv, hav, hcw, htv, htw, hta, htc⟩ :=
    exists_hyperbolic_frame hBN hBNnd ht ht1 hf
  have hca : BN c a = 0 := (form_comm_charTwo hBN c a).trans hac
  have hvw : BN v w = 0 := (form_comm_charTwo hBN v w).trans hwv
  have hwa : BN w a = 1 := (form_comm_charTwo hBN w a).trans haw
  have hvc : BN v c = 1 := (form_comm_charTwo hBN v c).trans hcv
  have hva : BN v a = 0 := (form_comm_charTwo hBN v a).trans hav
  have hwc : BN w c = 0 := (form_comm_charTwo hBN w c).trans hcw
  have haX : a ∈ Submodule.span K ({a, c, w, v} : Set N) := Submodule.subset_span (by simp)
  have hcX : c ∈ Submodule.span K ({a, c, w, v} : Set N) := Submodule.subset_span (by simp)
  have hwX : w ∈ Submodule.span K ({a, c, w, v} : Set N) := Submodule.subset_span (by simp)
  have hvX : v ∈ Submodule.span K ({a, c, w, v} : Set N) := Submodule.subset_span (by simp)
  have hτa : (lineElt hBN a c).app a = t.app a := by
    rw [lineElt_app hBN hac, hta, hBN.self_eq_zero, hac]
    simp
  have hτc : (lineElt hBN a c).app c = t.app c := by
    rw [lineElt_app hBN hac, htc, hca, hBN.self_eq_zero]
    simp
  have hτw : (lineElt hBN a c).app w = t.app w := by
    rw [lineElt_app hBN hac, htw, hwa, hwc]
    simp
  have hτv : (lineElt hBN a c).app v = t.app v := by
    rw [lineElt_app hBN hac, htv, hva, hvc]
    simp
  have hli : LinearIndependent K ![a, c] := by
    rw [LinearIndependent.pair_iff]
    intro α β hαβ
    have e1 := congrArg (fun x => BN x v) hαβ
    have e2 := congrArg (fun x => BN x w) hαβ
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hav,
      hcv, haw, hcw, map_zero, LinearMap.zero_apply, mul_zero, zero_add, add_zero, mul_one]
      at e1 e2
    exact ⟨e2, e1⟩
  refine ⟨Submodule.span K {a, c, w, v}, lineElt hBN a c, lineElt hBN w v,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact isCompl_span_four_orthogonal hBN hac hwv haw hcv hav hcw
  · intro x hx
    induction hx using Submodule.span_induction with
    | mem m hm =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
      rcases hm with h | h | h | h <;> rw [h]
      · rw [hta]; exact haX
      · rw [htc]; exact hcX
      · rw [htw]; exact Submodule.add_mem _ hwX hcX
      · rw [htv]; exact Submodule.add_mem _ hvX haX
    | zero => rw [Gsp.map_zero']; exact Submodule.zero_mem _
    | add m₁ m₂ _ _ h₁ h₂ => rw [Gsp.map_add]; exact Submodule.add_mem _ h₁ h₂
    | smul r m _ h => rw [Gsp.map_smul]; exact Submodule.smul_mem _ _ h
  · exact lineElt_mul_self hBN hac
  · intro x hx
    have hEq : Set.EqOn (((lineElt hBN a c : Gsp BN) : LinearMap.GeneralLinearGroup K N) :
        N →ₗ[K] N) (((t : Gsp BN) : LinearMap.GeneralLinearGroup K N) : N →ₗ[K] N)
        ({a, c, w, v} : Set N) := by
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with h | h | h | h <;> rw [h]
      exacts [hτa, hτc, hτw, hτv]
    exact LinearMap.eqOn_span hEq hx
  · intro x hx
    obtain ⟨h1, h2, -, -⟩ := mem_orthogonal_span_four.mp hx
    rw [lineElt_app hBN hac, (form_comm_charTwo hBN x a).trans h1,
      (form_comm_charTwo hBN x c).trans h2]
    simp
  · intro g hg
    have hga : g.app a = a := hg a haX
    have hgc : g.app c = c := hg c hcX
    have hgw : g.app w = w := hg w hwX
    have hgv : g.app v = v := hg v hvX
    exact ⟨commute_lineElt_of_app_eq hBN hga hgc, commute_lineElt_of_app_eq hBN hgw hgv⟩
  · have hord := orderOf_lineElt_mul_lineElt hBN hac hwv haw hcv hav hcw
    have hL₂ : lineElt hBN w v * lineElt hBN w v = 1 := lineElt_mul_self hBN hwv
    have hL₂i : (lineElt hBN w v)⁻¹ = lineElt hBN w v := inv_eq_of_mul_eq_one_right hL₂
    have e : lineElt hBN a c * (lineElt hBN w v * lineElt hBN a c * (lineElt hBN w v)⁻¹) =
        (lineElt hBN a c * lineElt hBN w v) ^ 2 := by
      rw [hL₂i, sq]
      group
    rw [e, orderOf_pow' _ two_ne_zero, hord]
    norm_num
  · intro h1
    refine ⟨a, c, hac, hli, ?_⟩
    have h2 : t = (lineElt hBN a c)⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [h2]
    exact inv_eq_of_mul_eq_one_right (lineElt_mul_self hBN hac)

theorem exists_block [CharP K 2] (hBN : BN.IsAlt) (hBNnd : BN.Nondegenerate) {t : Gsp BN}
    (ht : t * t = 1) (ht1 : t ≠ 1) :
    ∃ (X : Submodule K N) (τ h : Gsp BN), t.Block X τ h ∧
      (τ * t = 1 → finrank K (LinearMap.range t.phi) = 1 ∨
        ∃ a c, BN a c = 0 ∧ LinearIndependent K ![a, c] ∧ t = lineElt hBN a c) := by
  by_cases hf : ∀ x, t.ft x = 0
  · obtain ⟨X, τ, h, hb, hty⟩ := exists_block_of_ft_eq_zero hBN hBNnd ht ht1 hf
    exact ⟨X, τ, h, hb, fun h1 => Or.inr (hty h1)⟩
  · push Not at hf
    obtain ⟨v, hv⟩ := hf
    obtain ⟨X, τ, h, hb, -, hty⟩ := exists_block_of_ft_ne_zero hBN ht hv
    exact ⟨X, τ, h, hb, fun h1 => Or.inl (hty h1)⟩

end CFSG.ClassicalGroups.Alternating
