module

public import CFSG.ClassicalGroups.Alternating.RT1SpBasic
public import CFSG.ClassicalGroups.Alternating.RT1SpWitt

public section

namespace CFSG.ClassicalGroups.Alternating

open LinearMap (BilinForm)
open Module
open CFSG.LocalAnalysis.ComponentInitial

variable {K : Type*} [Field K] {N : Type*} [AddCommGroup N] [Module K N] {BN : BilinForm K N}

theorem Tsp_app_of_apply_eq_zero (hBN : BN.IsAlt) {v z : N} (hz : BN v z = 0) (l : K) :
    (Tsp hBN v l).app z = z := by
  rw [Tsp_app, ← hBN.neg_eq v z, hz, neg_zero, mul_zero, zero_smul, add_zero]

theorem eq_top_of_forall_Tsp_mem [FiniteDimensional K N] (hBN : BN.IsAlt)
    (hBNnd : BN.Nondegenerate) {H : Subgroup (Gsp BN)} (hT : ∀ (x : N) (c : K), Tsp hBN x c ∈ H) :
    H = ⊤ := by
  rw [eq_top_iff]
  intro g _
  have hg : (g : LinearMap.GeneralLinearGroup K N) ∈ bilinIsometryGroup BN := g.2
  have hle : bilinIsometryGroup BN ≤ H.map (bilinIsometryGroup BN).subtype := by
    conv_lhs => rw [alternating_transvection_generation hBN hBNnd]
    rw [Subgroup.closure_le]
    rintro _ ⟨a, c, rfl⟩
    exact ⟨Tsp hBN a c, hT a c, rfl⟩
  obtain ⟨h, hh, hval⟩ := hle hg
  have hgh : h = g := Subtype.ext hval
  rwa [hgh] at hh

theorem mem_closure_Tsp_of_coe_mem_closure (hBN : BN.IsAlt) (P : N → Prop) {k : Gsp BN}
    (hk : (k : LinearMap.GeneralLinearGroup K N) ∈
      Subgroup.closure {t | ∃ x, P x ∧ ∃ c : K, t = symplecticTransvection BN hBN x c}) :
    k ∈ Subgroup.closure {t : Gsp BN | ∃ x, P x ∧ ∃ c : K, t = Tsp hBN x c} := by
  have hmap : Subgroup.map (bilinIsometryGroup BN).subtype
      (Subgroup.closure {t : Gsp BN | ∃ x, P x ∧ ∃ c : K, t = Tsp hBN x c}) =
      Subgroup.closure {t | ∃ x, P x ∧ ∃ c : K, t = symplecticTransvection BN hBN x c} := by
    rw [MonoidHom.map_closure]
    congr 1
    ext t
    constructor
    · rintro ⟨_, ⟨x, hx, c, rfl⟩, rfl⟩
      exact ⟨x, hx, c, rfl⟩
    · rintro ⟨x, hx, c, rfl⟩
      exact ⟨Tsp hBN x c, ⟨x, hx, c, rfl⟩, rfl⟩
  rw [← hmap] at hk
  obtain ⟨k', hk', hkk'⟩ := hk
  have : k' = k := Subtype.ext hkk'
  rwa [this] at hk'

theorem mem_closure_Tsp_of_app_eq [FiniteDimensional K N] (hBN : BN.IsAlt)
    (hBNnd : BN.Nondegenerate) {a : N} {g : Gsp BN} (hg : g.app a = a) :
    g ∈ Subgroup.closure {t : Gsp BN | ∃ (x : N) (c : K), BN a x = 0 ∧ t = Tsp hBN x c} := by
  set C := Subgroup.closure {t : Gsp BN | ∃ (x : N) (c : K), BN a x = 0 ∧ t = Tsp hBN x c}
    with hC
  by_cases ha : a = 0
  · have : C = ⊤ := eq_top_of_forall_Tsp_mem hBN hBNnd fun x c =>
      Subgroup.subset_closure ⟨x, c, by rw [ha, map_zero, LinearMap.zero_apply], rfl⟩
    rw [this]
    exact Subgroup.mem_top g
  obtain ⟨b, hab⟩ := (alternating_hyperbolic_splitting hBN hBNnd ha).1
  have hb' : BN a (g.app b) = 1 := by
    have := Gsp.form_app g a b
    rw [hg] at this
    exact this.trans hab
  obtain ⟨l, -, hl0, hla, hlb⟩ := alternating_fixed_vector_pair_adjustment hBN hb' hab
  set h : Gsp BN := listProdTsp hBN l with hh
  have hha : h.app a = a := by rw [hh, listProdTsp_app]; exact hla
  have hhb : h.app (g.app b) = b := by rw [hh, listProdTsp_app]; exact hlb
  have hhC : h ∈ C := by
    refine Subgroup.list_prod_mem _ fun t ht => ?_
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ht
    exact Subgroup.subset_closure ⟨p.1, p.2, hl0 p hp, rfl⟩
  have hkC : h * g ∈ C := by
    have hk := mem_closure_symplecticTransvection_of_apply_eq_of_apply_eq hBN hBNnd hab
      (g := ((h * g : Gsp BN) : LinearMap.GeneralLinearGroup K N)) (h * g).2
      (by rw [← Gsp.app, Gsp.app_mul, hg, hha]) (by rw [← Gsp.app, Gsp.app_mul, hhb])
    refine Subgroup.closure_mono ?_ (mem_closure_Tsp_of_coe_mem_closure hBN
      (fun x => x ∈ BN.orthogonal (Submodule.span K {a, b})) hk)
    rintro _ ⟨x, hx, c, rfl⟩
    exact ⟨x, c, ((LinearMap.BilinForm.mem_orthogonal_span_pair_iff BN).mp hx).1, rfl⟩
  have : g = h⁻¹ * (h * g) := by group
  rw [this]
  exact mul_mem (inv_mem hhC) hkC

theorem eq_top_of_stabilizer_le_of_Tsp_mem [FiniteDimensional K N] (hBN : BN.IsAlt)
    (hBNnd : BN.Nondegenerate) {a b : N} (hab : BN a b ≠ 0) {H : Subgroup (Gsp BN)}
    (hstab : ∀ g : Gsp BN, g.app a = a → g ∈ H) (hT : ∀ c : K, Tsp hBN b c ∈ H) : H = ⊤ := by
  refine eq_top_of_forall_Tsp_mem hBN hBNnd fun x c => ?_
  by_cases hxa : BN a x = 0
  · refine hstab _ ?_
    exact Tsp_app_of_apply_eq_zero hBN (v := x) (z := a)
      (by rw [← hBN.neg_eq a x, hxa, neg_zero]) c
  ·
    set lam : K := BN a b / BN a x with hlam
    have hlam0 : lam ≠ 0 := div_ne_zero hab hxa
    have h1 : BN a (lam • x) = BN a b := by
      rw [map_smul, smul_eq_mul, hlam, div_mul_cancel₀ _ hxa]
    obtain ⟨g, hga, hgb⟩ := exists_gsp_apply_eq_of_form_eq hBN hBNnd hab rfl h1
    have hgH : g ∈ H := hstab g hga
    have hc : lam ^ 2 * (c / lam ^ 2) = c := by field_simp
    have hconj : g * Tsp hBN b (c / lam ^ 2) * g⁻¹ = Tsp hBN x c := by
      rw [Tsp_conj hBN g b, hgb, Tsp_smul, hc]
    rw [← hconj]
    exact mul_mem (mul_mem hgH (hT _)) (inv_mem hgH)

theorem exists_mem_app_eq_of_Tsp_mem (hBN : BN.IsAlt) {e f : N} (hef : BN e f = 1)
    {H : Subgroup (Gsp BN)} (he : ∀ l : K, Tsp hBN e l ∈ H) (hf : ∀ l : K, Tsp hBN f l ∈ H)
    {p q : K} (hpq : p ≠ 0 ∨ q ≠ 0) :
    ∃ g ∈ H, g.app f = p • e + q • f ∧ ∀ z, BN e z = 0 → BN f z = 0 → g.app z = z := by
  have hfe : BN f e = -1 := by rw [← hBN.neg_eq e f, hef]
  by_cases hp : p = 0
  ·
    have hq : q ≠ 0 := hpq.resolve_left (not_not.mpr hp)
    refine ⟨Tsp hBN e q⁻¹ * Tsp hBN f (q - 1) * Tsp hBN e (-1),
      mul_mem (mul_mem (he _) (hf _)) (he _), ?_, ?_⟩
    · rw [Gsp.app_mul, Gsp.app_mul, Tsp_app hBN e (-1) f, Tsp_app hBN f (q - 1),
        Tsp_app hBN e q⁻¹]
      simp only [hfe, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        hBN.self_eq_zero, hef, hp, zero_smul, zero_add]
      match_scalars <;> field_simp <;> ring
    · intro z hez hfz
      rw [Gsp.app_mul, Gsp.app_mul, Tsp_app_of_apply_eq_zero hBN hez,
        Tsp_app_of_apply_eq_zero hBN hfz, Tsp_app_of_apply_eq_zero hBN hez]
  ·
    refine ⟨Tsp hBN f ((q - 1) / p) * Tsp hBN e (-p), mul_mem (hf _) (he _), ?_, ?_⟩
    · rw [Gsp.app_mul, Tsp_app hBN e (-p) f, Tsp_app hBN f ((q - 1) / p)]
      simp only [hfe, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        hBN.self_eq_zero, hef]
      match_scalars
      · field_simp
        ring
      · field_simp
    · intro z hez hfz
      rw [Gsp.app_mul, Tsp_app_of_apply_eq_zero hBN hez, Tsp_app_of_apply_eq_zero hBN hfz]

theorem linearIndependent_of_hyperbolic_pairs (hBN : BN.IsAlt) {a b c c' : N} (hab : BN a b = 1)
    (hcc : BN c c' = 1) (hac : BN a c = 0) (hac' : BN a c' = 0) (hbc : BN b c = 0)
    (hbc' : BN b c' = 0) : LinearIndependent K ![a, b, c, c'] := by
  have hba : BN b a = -1 := by rw [← hBN.neg_eq a b, hab]
  have hc'c : BN c' c = -1 := by rw [← hBN.neg_eq c c', hcc]
  have hca : BN c a = 0 := by rw [← hBN.neg_eq a c, hac, neg_zero]
  have hc'a : BN c' a = 0 := by rw [← hBN.neg_eq a c', hac', neg_zero]
  have hcb : BN c b = 0 := by rw [← hBN.neg_eq b c, hbc, neg_zero]
  have hc'b : BN c' b = 0 := by rw [← hBN.neg_eq b c', hbc', neg_zero]
  rw [Fintype.linearIndependent_iff]
  intro g hg
  simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at hg
  have e0 := congrArg (fun z => BN z b) hg
  have e1 := congrArg (fun z => BN z a) hg
  have e2 := congrArg (fun z => BN z c') hg
  have e3 := congrArg (fun z => BN z c) hg
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, map_zero,
    LinearMap.zero_apply, hBN.self_eq_zero, hab, hba, hcc, hc'c, hac, hac', hbc, hbc', hca, hc'a,
    hcb, hc'b] at e0 e1 e2 e3
  intro i
  fin_cases i
  · simpa using e0
  · simpa using e1
  · simpa using e2
  · simpa using e3

theorem closure_Tsp_five_eq_top [FiniteDimensional K N] (hBN : BN.IsAlt)
    (hBNnd : BN.Nondegenerate) (hdim : finrank K N = 4) {a b c c' : N} (hab : BN a b = 1)
    (hcc : BN c c' = 1) (hac : BN a c = 0) (hac' : BN a c' = 0) (hbc : BN b c = 0)
    (hbc' : BN b c' = 0) :
    Subgroup.closure {t : Gsp BN | ∃ x ∈ ({a, b, c, c', b + c} : Set N), ∃ l : K,
      t = Tsp hBN x l} = ⊤ := by
  set H := Subgroup.closure {t : Gsp BN | ∃ x ∈ ({a, b, c, c', b + c} : Set N), ∃ l : K,
    t = Tsp hBN x l} with hH
  have hmem : ∀ x ∈ ({a, b, c, c', b + c} : Set N), ∀ l : K, Tsp hBN x l ∈ H := fun x hx l =>
    Subgroup.subset_closure ⟨x, hx, l, rfl⟩
  have hsmul : ∀ (μ : K) (x : N), (∀ l : K, Tsp hBN x l ∈ H) →
      ∀ l : K, Tsp hBN (μ • x) l ∈ H := fun μ x hx l => by
    rw [Tsp_smul]
    exact hx _
  have hconj : ∀ (g : Gsp BN) (x : N), g ∈ H → (∀ l : K, Tsp hBN x l ∈ H) →
      ∀ l : K, Tsp hBN (g.app x) l ∈ H := fun g x hg hx l => by
    rw [← Tsp_conj hBN g x l]
    exact mul_mem (mul_mem hg (hx l)) (inv_mem hg)
  have hc'c : BN c' c = -1 := by rw [← hBN.neg_eq c c', hcc]
  have hca : BN c a = 0 := by rw [← hBN.neg_eq a c, hac, neg_zero]
  have hc'a : BN c' a = 0 := by rw [← hBN.neg_eq a c', hac', neg_zero]
  have hcb : BN c b = 0 := by rw [← hBN.neg_eq b c, hbc, neg_zero]
  have hc'b : BN c' b = 0 := by rw [← hBN.neg_eq b c', hbc', neg_zero]
  have hnc' : ∀ l : K, Tsp hBN (-c') l ∈ H := fun l => by
    have := hsmul (-1) c' (hmem c' (by simp)) l
    rwa [neg_one_smul] at this
  have hef' : BN (-c') c = 1 := by rw [map_neg, LinearMap.neg_apply, hc'c, neg_neg]
  have hP : ∀ p q : K, p ≠ 0 ∨ q ≠ 0 → ∃ g ∈ H, g.app b = p • a + q • b ∧
      ∀ z, BN a z = 0 → BN b z = 0 → g.app z = z := fun p q hpq =>
    exists_mem_app_eq_of_Tsp_mem hBN hab (hmem a (by simp)) (hmem b (by simp)) hpq
  have hQ : ∀ p q : K, p ≠ 0 ∨ q ≠ 0 → ∃ g ∈ H, g.app c = p • (-c') + q • c ∧
      ∀ z, BN (-c') z = 0 → BN c z = 0 → g.app z = z := fun p q hpq =>
    exists_mem_app_eq_of_Tsp_mem hBN hef' hnc' (hmem c (by simp)) hpq
  have hQ' : ∀ u v : K, u ≠ 0 ∨ v ≠ 0 → ∃ g ∈ H, g.app c = u • c + v • c' ∧
      ∀ z, BN (-c') z = 0 → BN c z = 0 → g.app z = z := by
    intro u v hk
    obtain ⟨g, hgH, hg1, hg2⟩ := hQ (-v) u (by
      rcases hk with hk | hk
      · exact Or.inr hk
      · exact Or.inl (neg_ne_zero.mpr hk))
    refine ⟨g, hgH, ?_, hg2⟩
    rw [hg1]
    module
  have hli := linearIndependent_of_hyperbolic_pairs hBN hab hcc hac hac' hbc hbc'
  have htop : Submodule.span K (Set.range ![a, b, c, c']) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank (by simp [hdim])
  have hall : ∀ (x : N) (l : K), Tsp hBN x l ∈ H := by
    intro x
    obtain ⟨gs, hgs⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp
      (htop ▸ Submodule.mem_top : x ∈ Submodule.span K (Set.range ![a, b, c, c']))
    simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at hgs
    obtain ⟨s, t, u, v, hx⟩ : ∃ s t u v : K, s • a + t • b + u • c + v • c' = x :=
      ⟨gs 0, gs 1, gs 2, gs 3, hgs⟩
    subst hx
    by_cases hh : s ≠ 0 ∨ t ≠ 0
    · obtain ⟨g₁, hg₁H, hg₁b, hg₁z⟩ := hP s t hh
      by_cases hk : u ≠ 0 ∨ v ≠ 0
      · obtain ⟨g₂, hg₂H, hg₂c, hg₂z⟩ := hQ' u v hk
        have ha' : g₂.app a = a :=
          hg₂z a (by rw [map_neg, LinearMap.neg_apply, hc'a, neg_zero]) hca
        have hb' : g₂.app b = b :=
          hg₂z b (by rw [map_neg, LinearMap.neg_apply, hc'b, neg_zero]) hcb
        have e1 : g₁.app (b + c) = s • a + t • b + c := by
          rw [Gsp.map_add, hg₁b, hg₁z c hac hbc]
        have hxeq : s • a + t • b + u • c + v • c' = (g₂ * g₁).app (b + c) := by
          rw [Gsp.app_mul, e1, Gsp.map_add, Gsp.map_add, Gsp.map_smul, Gsp.map_smul, ha', hb',
            hg₂c]
          module
        rw [hxeq]
        exact hconj (g₂ * g₁) (b + c) (mul_mem hg₂H hg₁H) (hmem (b + c) (by simp))
      · push Not at hk
        obtain ⟨rfl, rfl⟩ := hk
        have hxeq : s • a + t • b + (0 : K) • c + (0 : K) • c' = g₁.app b := by
          rw [hg₁b]
          module
        rw [hxeq]
        exact hconj g₁ b hg₁H (hmem b (by simp))
    · push Not at hh
      obtain ⟨rfl, rfl⟩ := hh
      by_cases hk : u ≠ 0 ∨ v ≠ 0
      · obtain ⟨g₂, hg₂H, hg₂c, -⟩ := hQ' u v hk
        have hxeq : (0 : K) • a + (0 : K) • b + u • c + v • c' = g₂.app c := by
          rw [hg₂c]
          module
        rw [hxeq]
        exact hconj g₂ c hg₂H (hmem c (by simp))
      · push Not at hk
        obtain ⟨rfl, rfl⟩ := hk
        intro l
        have h0 : (0 : K) • a + (0 : K) • b + (0 : K) • c + (0 : K) • c' = 0 := by module
        rw [h0, (Tsp_eq_one_iff hBN hBNnd 0 l).mpr (Or.inl rfl)]
        exact one_mem H
  exact eq_top_of_forall_Tsp_mem hBN hBNnd hall

end CFSG.ClassicalGroups.Alternating
