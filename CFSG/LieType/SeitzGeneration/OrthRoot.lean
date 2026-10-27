module

public import CFSG.LieType.SeitzGeneration.OrthFixed

public section

namespace CFSG.LieType.SeitzGeneration

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

section EichlerOn

variable (Q) in
@[expose] def eichlerGroupOn (U : Submodule K V) : Subgroup (V ≃ₗ[K] V) :=
  Subgroup.closure {g | ∃ e ∈ U, ∃ w ∈ U, g = eichler Q e w}

theorem eichler_mem_eichlerGroupOn {U : Submodule K V} {e w : V} (he : e ∈ U) (hw : w ∈ U) :
    eichler Q e w ∈ eichlerGroupOn Q U :=
  Subgroup.subset_closure ⟨e, he, w, hw, rfl⟩

theorem eichlerGroupOn_le {U : Submodule K V} {H : Subgroup (V ≃ₗ[K] V)}
    (h : ∀ e ∈ U, ∀ w ∈ U, eichler Q e w ∈ H) : eichlerGroupOn Q U ≤ H := by
  refine (Subgroup.closure_le _).2 ?_
  rintro g ⟨e, he, w, hw, rfl⟩
  exact h e he w hw

theorem eichlerGroupOn_apply_of_orth {U : Submodule K V} {g : V ≃ₗ[K] V}
    (hg : g ∈ eichlerGroupOn Q U) {v : V} (hv : ∀ u ∈ U, polar Q v u = 0) : g v = v := by
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨e, he, w, hw, rfl⟩ := hg
    exact eichler_apply_of_polar_eq_zero (hv e he) (hv w hw)
  | one => rfl
  | mul g h _ _ ihg ihh => rw [LinearEquiv.mul_apply, ihh, ihg]
  | inv g _ ih => exact (LinearEquiv.symm_apply_eq _).mpr ih.symm

theorem eichlerGroupOn_apply_mem {U : Submodule K V} {g : V ≃ₗ[K] V}
    (hg : g ∈ eichlerGroupOn Q U) {u : V} (hu : u ∈ U) : g u ∈ U ∧ g⁻¹ u ∈ U := by
  induction hg using Subgroup.closure_induction generalizing u with
  | mem g hg =>
    obtain ⟨e, he, w, hw, rfl⟩ := hg
    by_cases h : Q e = 0 ∧ polar Q e w = 0
    · have h1 : ∀ w' ∈ U, polar Q e w' = 0 → eichler Q e w' u ∈ U := fun w' hw' hw'0 => by
        rw [eichler_apply h.1 hw'0]
        exact U.sub_mem (U.add_mem hu (U.smul_mem _ hw'))
          (U.smul_mem _ he)
      refine ⟨h1 w hw h.2, ?_⟩
      rw [eichler_inv h.2]
      exact h1 (-w) (U.neg_mem hw) (by rw [polar_neg_right, h.2, neg_zero])
    · rw [eichler_of_not h]
      exact ⟨hu, hu⟩
  | one => exact ⟨hu, hu⟩
  | mul g h _ _ ihg ihh =>
    refine ⟨(ihg (ihh hu).1).1, ?_⟩
    rw [mul_inv_rev, LinearEquiv.mul_apply]
    exact (ihh (ihg hu).2).2
  | inv g _ ih => exact ⟨(ih hu).2, by simpa using (ih hu).1⟩

end EichlerOn

section Transitive

theorem polarBilin_comp_subtype (U : Submodule K V) :
    polarBilin (Q.comp U.subtype) = LinearMap.BilinForm.restrict (polarBilin Q) U := by
  refine LinearMap.ext₂ fun u w => ?_
  rw [polarBilin_apply_apply]
  simp only [QuadraticMap.polar, QuadraticMap.comp_apply, map_add]
  rfl

theorem polar_comp_subtype' (U : Submodule K V) (u w : U) :
    polar (Q.comp U.subtype) u w = polar Q (u : V) (w : V) := by
  simp only [QuadraticMap.polar, QuadraticMap.comp_apply, map_add]
  rfl

theorem exists_mem_eichlerGroupOn_of_mem_elementaryGroup {U : Submodule K V}
    {g' : U ≃ₗ[K] U} (hg' : g' ∈ elementaryGroup (Q.comp U.subtype)) :
    ∃ g ∈ eichlerGroupOn Q U, ∀ u : U, g (u : V) = (g' u : V) := by
  induction hg' using Subgroup.closure_induction with
  | mem g' hg' =>
    obtain ⟨e, w, hQe, hew, rfl⟩ := hg'
    have hQe' : Q (e : V) = 0 := hQe
    have hew' : polar Q (e : V) (w : V) = 0 := by rw [← polar_comp_subtype']; exact hew
    refine ⟨eichler Q (e : V) (w : V), eichler_mem_eichlerGroupOn e.2 w.2, fun u => ?_⟩
    rw [eichler_apply hQe' hew', eichler_apply hQe hew]
    simp only [polar_comp_subtype', QuadraticMap.comp_apply, Submodule.coe_sub,
      Submodule.coe_add, Submodule.coe_smul, Submodule.subtype_apply]
  | one => exact ⟨1, Subgroup.one_mem _, fun u => rfl⟩
  | mul g h _ _ ihg ihh =>
    obtain ⟨a, ha, ha'⟩ := ihg
    obtain ⟨b, hb, hb'⟩ := ihh
    refine ⟨a * b, Subgroup.mul_mem _ ha hb, fun u => ?_⟩
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hb' u]
    exact ha' (h u)
  | inv g _ ih =>
    obtain ⟨a, ha, ha'⟩ := ih
    refine ⟨a⁻¹, Subgroup.inv_mem _ ha, fun u => ?_⟩
    have h1 : a ((g⁻¹ u : U) : V) = (u : V) := by
      rw [ha' (g⁻¹ u)]
      simp
    exact (LinearEquiv.symm_apply_eq a).mpr h1.symm

theorem exists_mem_eichlerGroupOn_apply_eq {U : Submodule K V}
    (hU : (LinearMap.BilinForm.restrict (polarBilin Q) U).Nondegenerate)
    {P P' : HypPair (Q.comp U.subtype)} (h : P.Orth P') {x y : V} (hxU : x ∈ U) (hyU : y ∈ U)
    (hx : x ≠ 0) (hy : y ≠ 0) (hxy : Q x = Q y) : ∃ g ∈ eichlerGroupOn Q U, g x = y := by
  have hU' : (polarBilin (Q.comp U.subtype)).Nondegenerate := by
    rw [polarBilin_comp_subtype]
    exact hU
  obtain ⟨g', hg', hg'x⟩ := exists_mem_elementaryGroup_apply_eq hU' h
    (x := (⟨x, hxU⟩ : U)) (y := (⟨y, hyU⟩ : U)) (fun h0 => hx (congrArg Subtype.val h0))
    (fun h0 => hy (congrArg Subtype.val h0)) hxy
  obtain ⟨g, hg, hgg'⟩ := exists_mem_eichlerGroupOn_of_mem_elementaryGroup hg'
  refine ⟨g, hg, ?_⟩
  have := hgg' ⟨x, hxU⟩
  rw [hg'x] at this
  exact this

@[expose] def HasOrthPairs (Q : QuadraticForm K V) (U : Submodule K V) : Prop :=
  ∃ a₁ f₁ a₂ f₂ : V, a₁ ∈ U ∧ f₁ ∈ U ∧ a₂ ∈ U ∧ f₂ ∈ U ∧ Q a₁ = 0 ∧ Q f₁ = 0 ∧ Q a₂ = 0 ∧
    Q f₂ = 0 ∧ polar Q a₁ f₁ = 1 ∧ polar Q a₂ f₂ = 1 ∧ polar Q a₁ a₂ = 0 ∧
    polar Q a₁ f₂ = 0 ∧ polar Q f₁ a₂ = 0 ∧ polar Q f₁ f₂ = 0

theorem exists_mem_eichlerGroupOn_apply_eq_of_pairs {U : Submodule K V}
    (hU : (LinearMap.BilinForm.restrict (polarBilin Q) U).Nondegenerate)
    (hP : HasOrthPairs Q U) {x y : V} (hxU : x ∈ U) (hyU : y ∈ U) (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : Q x = Q y) : ∃ g ∈ eichlerGroupOn Q U, g x = y := by
  obtain ⟨a₁, f₁, a₂, f₂, ha₁, hf₁, ha₂, hf₂, hQa₁, hQf₁, hQa₂, hQf₂, h11, h22, h12, h1f2, hf1a2,
    hf1f2⟩ := hP
  obtain ⟨P, hPe, hPf⟩ : ∃ P : HypPair (Q.comp U.subtype), P.e = ⟨a₁, ha₁⟩ ∧ P.f = ⟨f₁, hf₁⟩ :=
    ⟨⟨⟨a₁, ha₁⟩, ⟨f₁, hf₁⟩, hQa₁, hQf₁, by rw [polar_comp_subtype']; exact h11⟩, rfl, rfl⟩
  obtain ⟨P', hPe', hPf'⟩ : ∃ P' : HypPair (Q.comp U.subtype), P'.e = ⟨a₂, ha₂⟩ ∧
      P'.f = ⟨f₂, hf₂⟩ :=
    ⟨⟨⟨a₂, ha₂⟩, ⟨f₂, hf₂⟩, hQa₂, hQf₂, by rw [polar_comp_subtype']; exact h22⟩, rfl, rfl⟩
  have hOrth : P.Orth P' := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [polar_comp_subtype'] <;> simp [hPe, hPf, hPe', hPf'] <;>
      assumption
  exact exists_mem_eichlerGroupOn_apply_eq hU hOrth hxU hyU hx hy hxy

end Transitive

section Root

variable (Q) in
@[expose] def rootSet (H : Subgroup (V ≃ₗ[K] V)) (s : V) : AddSubgroup V where
  carrier := {w | polar Q s w = 0 ∧ eichler Q s w ∈ H}
  zero_mem' := ⟨polar_zero_right Q s, by rw [eichler_zero_right]; exact H.one_mem⟩
  add_mem' := fun {a b} ha hb =>
    ⟨by rw [polar_add_right, ha.1, hb.1, add_zero],
      by rw [← eichler_mul ha.1 hb.1]; exact H.mul_mem ha.2 hb.2⟩
  neg_mem' := fun {a} ha =>
    ⟨by rw [polar_neg_right, ha.1, neg_zero], by rw [← eichler_inv ha.1]; exact H.inv_mem ha.2⟩

theorem mem_rootSet {H : Subgroup (V ≃ₗ[K] V)} {s w : V} :
    w ∈ rootSet Q H s ↔ polar Q s w = 0 ∧ eichler Q s w ∈ H := Iff.rfl

theorem rootSet_map {H : Subgroup (V ≃ₗ[K] V)} (hH : H ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    {g : V ≃ₗ[K] V} (hg : g ∈ H) {s w : V} (hw : w ∈ rootSet Q H s) :
    g w ∈ rootSet Q H (g s) := by
  refine ⟨by rw [polar_map_of_mem (hH hg)]; exact hw.1, ?_⟩
  rw [← eichler_conj (hH hg)]
  exact H.mul_mem (H.mul_mem hg hw.2) (H.inv_mem hg)

end Root

section Pairs

theorem map_sub_smul' (x y : V) (c : K) :
    Q (x - c • y) = Q x + c ^ 2 * Q y - c * polar Q x y := by
  rw [sub_eq_add_neg, QuadraticMap.map_add Q x (-(c • y)), QuadraticMap.map_neg, map_smul_eq_sq,
    polar_neg_right, polar_smul_right_eq]
  ring

theorem exists_orthPairs {U : Submodule K V}
    (hU : (LinearMap.BilinForm.restrict (polarBilin Q) U).Nondegenerate) {e₁ e₂ : V}
    (h₁ : e₁ ∈ U) (h₂ : e₂ ∈ U) (hQ₁ : Q e₁ = 0) (hQ₂ : Q e₂ = 0) (h12 : polar Q e₁ e₂ = 0)
    (he₁ : e₁ ≠ 0) (hind : ∀ c : K, e₂ ≠ c • e₁) :
    ∃ a₁ f₁ a₂ f₂ : V, a₁ ∈ U ∧ f₁ ∈ U ∧ a₂ ∈ U ∧ f₂ ∈ U ∧ Q a₁ = 0 ∧ Q f₁ = 0 ∧ Q a₂ = 0 ∧
      Q f₂ = 0 ∧ polar Q a₁ f₁ = 1 ∧ polar Q a₂ f₂ = 1 ∧ polar Q a₁ a₂ = 0 ∧
      polar Q a₁ f₂ = 0 ∧ polar Q f₁ a₂ = 0 ∧ polar Q f₁ f₂ = 0 := by
  obtain ⟨f₁, hf₁U, hf₁Q, hef₁⟩ := exists_hypPair_of_regular hU h₁ he₁ hQ₁
  have hf₁e : polar Q f₁ e₁ = 1 := by rw [polar_comm, hef₁]
  have he₁e₁ : polar Q e₁ e₁ = 0 := polar_self_eq_zero hQ₁
  have hf₁f₁ : polar Q f₁ f₁ = 0 := polar_self_eq_zero hf₁Q
  have he₂e₁ : polar Q e₂ e₁ = 0 := by rw [polar_comm, h12]
  obtain ⟨a₂, ha₂U, ha₂ne, ha₂Q, ha₁a₂, hf₁a₂⟩ : ∃ a₂ ∈ U, a₂ ≠ 0 ∧ Q a₂ = 0 ∧
      polar Q e₁ a₂ = 0 ∧ polar Q f₁ a₂ = 0 := by
    refine ⟨e₂ - polar Q e₂ f₁ • e₁, U.sub_mem h₂ (U.smul_mem _ h₁), fun h0 =>
      hind _ (sub_eq_zero.mp h0), ?_, ?_, ?_⟩
    · rw [map_sub_smul', hQ₁, hQ₂, he₂e₁]
      ring
    · rw [polar_sub_right, polar_smul_right_eq, he₁e₁, h12]
      ring
    · rw [polar_sub_right, polar_smul_right_eq, hf₁e, polar_comm Q f₁ e₂]
      ring
  have h1 : polar Q a₂ e₁ = 0 := by rw [polar_comm, ha₁a₂]
  have h2 : polar Q a₂ f₁ = 0 := by rw [polar_comm, hf₁a₂]
  have ha₂a₂ : polar Q a₂ a₂ = 0 := polar_self_eq_zero ha₂Q
  obtain ⟨g, hgU, hg⟩ : ∃ g ∈ U, polar Q a₂ g ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact ha₂ne (congrArg Subtype.val (hU.1 ⟨a₂, ha₂U⟩ fun z => hcon z z.2))
  obtain ⟨f'', hf''U, hf''a, hf''e, hf''f⟩ : ∃ f'' ∈ U, polar Q a₂ f'' = 1 ∧ polar Q e₁ f'' = 0 ∧
      polar Q f₁ f'' = 0 := by
    refine ⟨(polar Q a₂ g)⁻¹ • (g - polar Q g f₁ • e₁ - polar Q g e₁ • f₁),
      U.smul_mem _ (U.sub_mem (U.sub_mem hgU (U.smul_mem _ h₁)) (U.smul_mem _ hf₁U)), ?_, ?_, ?_⟩
    · rw [polar_smul_right_eq, polar_sub_right, polar_sub_right, polar_smul_right_eq,
        polar_smul_right_eq, h1, h2]
      simp [hg]
    · rw [polar_smul_right_eq, polar_sub_right, polar_sub_right, polar_smul_right_eq,
        polar_smul_right_eq, he₁e₁, hef₁, polar_comm Q e₁ g]
      ring
    · rw [polar_smul_right_eq, polar_sub_right, polar_sub_right, polar_smul_right_eq,
        polar_smul_right_eq, hf₁e, hf₁f₁, polar_comm Q f₁ g]
      ring
  refine ⟨e₁, f₁, a₂, f'' - Q f'' • a₂, h₁, hf₁U, ha₂U, U.sub_mem hf''U (U.smul_mem _ ha₂U), hQ₁,
    hf₁Q, ha₂Q, ?_, hef₁, ?_, ha₁a₂, ?_, hf₁a₂, ?_⟩
  · rw [map_sub_smul', ha₂Q, polar_comm Q f'' a₂, hf''a]
    ring
  · rw [polar_sub_right, polar_smul_right_eq, ha₂a₂, hf''a]
    ring
  · rw [polar_sub_right, polar_smul_right_eq, ha₁a₂, hf''e]
    ring
  · rw [polar_sub_right, polar_smul_right_eq, hf₁a₂, hf''f]
    ring

end Pairs

section Inv

theorem mem_of_invariant {U : Submodule K V}
    (hU : (LinearMap.BilinForm.restrict (polarBilin Q) U).Nondegenerate)
    (hP : HasOrthPairs Q U) (A : AddSubgroup V)
    (hA : ∀ e ∈ U, ∀ w ∈ U, ∀ a ∈ A, a ∈ U → eichler Q e w a ∈ A)
    {a : V} (haA : a ∈ A) (haU : a ∈ U) (ha0 : a ≠ 0) : ∀ y ∈ U, y ∈ A := by
  obtain ⟨a₁, f₁, a₂, f₂, ha₁, hf₁, ha₂, hf₂, hQa₁, hQf₁, hQa₂, hQf₂, h11, h22, h12, h1f2, hf1a2,
    hf1f2⟩ := hP
  have hAinv : ∀ g ∈ eichlerGroupOn Q U, (∀ b ∈ A, b ∈ U → g b ∈ A) ∧
      (∀ b ∈ A, b ∈ U → g⁻¹ b ∈ A) := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨e, he, w, hw, rfl⟩ := hg
      by_cases h : Q e = 0 ∧ polar Q e w = 0
      · refine ⟨fun b hb hbU => hA e he w hw b hb hbU, fun b hb hbU => ?_⟩
        rw [eichler_inv h.2]
        exact hA e he (-w) (U.neg_mem hw) b hb hbU
      · rw [eichler_of_not h]
        exact ⟨fun b hb _ => hb, fun b hb _ => hb⟩
    | one => exact ⟨fun b hb _ => hb, fun b hb _ => hb⟩
    | mul g h hg hh ihg ihh =>
      refine ⟨fun b hb hbU => ?_, fun b hb hbU => ?_⟩
      · rw [LinearEquiv.mul_apply]
        exact ihg.1 _ (ihh.1 b hb hbU) ((eichlerGroupOn_apply_mem hh hbU).1)
      · rw [mul_inv_rev, LinearEquiv.mul_apply]
        exact ihh.2 _ (ihg.2 b hb hbU) ((eichlerGroupOn_apply_mem hg hbU).2)
    | inv g hg ih => exact ⟨ih.2, fun b hb hbU => by simpa using ih.1 b hb hbU⟩
  have hAorb : ∀ b ∈ A, b ∈ U → b ≠ 0 → ∀ c ∈ U, c ≠ 0 → Q c = Q b → c ∈ A := by
    intro b hb hbU hb0 c hcU hc0 hcb
    obtain ⟨g, hg, hgb⟩ := exists_mem_eichlerGroupOn_apply_eq_of_pairs hU
      ⟨a₁, f₁, a₂, f₂, ha₁, hf₁, ha₂, hf₂, hQa₁, hQf₁, hQa₂, hQf₂, h11, h22, h12, h1f2, hf1a2,
        hf1f2⟩ hbU hcU hb0 hc0 hcb.symm
    rw [← hgb]
    exact (hAinv g hg).1 b hb hbU
  obtain ⟨s, hsA, hsU, hs0, hsQ⟩ : ∃ s ∈ A, s ∈ U ∧ s ≠ 0 ∧ Q s = 0 := by
    by_cases hQ : Q a = 0
    · exact ⟨a, haA, haU, ha0, hQ⟩
    set α := polar Q a a₂ with hα
    set β := -polar Q a a₁ with hβ
    obtain ⟨e', he'U, he'0, he'Q, he'a⟩ : ∃ e' ∈ U, e' ≠ 0 ∧ Q e' = 0 ∧ polar Q a e' = 0 := by
      by_cases hαβ : α = 0 ∧ β = 0
      · refine ⟨a₁, ha₁, fun h0 => ?_, hQa₁, ?_⟩
        · rw [h0] at h11
          simp at h11
        · have h2 := hαβ.2
          rw [hβ] at h2
          exact neg_eq_zero.mp h2
      · refine ⟨α • a₁ + β • a₂, U.add_mem (U.smul_mem _ ha₁) (U.smul_mem _ ha₂), fun h0 => ?_,
          ?_, ?_⟩
        · apply hαβ
          have h1 : polar Q (α • a₁ + β • a₂) f₁ = 0 := by rw [h0]; exact polar_zero_left Q f₁
          have h2 : polar Q (α • a₁ + β • a₂) f₂ = 0 := by rw [h0]; exact polar_zero_left Q f₂
          rw [polar_add_left, polar_smul_left_eq, polar_smul_left_eq, h11,
            show polar Q a₂ f₁ = 0 by rw [polar_comm]; exact hf1a2] at h1
          rw [polar_add_left, polar_smul_left_eq, polar_smul_left_eq, h1f2, h22] at h2
          constructor
          · linear_combination h1
          · linear_combination h2
        · rw [QuadraticMap.map_add Q (α • a₁) (β • a₂), map_smul_eq_sq, map_smul_eq_sq, hQa₁, hQa₂,
            polar_smul_left_eq, polar_smul_right_eq, h12]
          ring
        · rw [polar_add_right, polar_smul_right_eq, polar_smul_right_eq, hα, hβ]
          rw [polar_comm Q a a₁, polar_comm Q a a₂]
          ring
    have hxQ : Q (a + e') = Q a := by
      rw [QuadraticMap.map_add Q a e', he'Q, he'a]
      ring
    have hx0 : a + e' ≠ 0 := by
      intro h0
      have : e' = -a := eq_neg_of_add_eq_zero_right h0
      apply hQ
      rw [this, QuadraticMap.map_neg] at he'Q
      exact he'Q
    have hxA : a + e' ∈ A := hAorb a haA haU ha0 _ (U.add_mem haU he'U) hx0 hxQ
    exact ⟨e', by simpa using A.sub_mem hxA haA, he'U, he'0, he'Q⟩
  have hsing : ∀ u ∈ U, Q u = 0 → u ∈ A := by
    intro u huU huQ
    by_cases hu0 : u = 0
    · rw [hu0]; exact A.zero_mem
    · exact hAorb s hsA hsU hs0 u huU hu0 (by rw [hsQ, huQ])
  intro y hyU
  set c₁ := polar Q y f₁ with hc₁
  set c₂ := polar Q y a₁ with hc₂
  have ha₁f₁ : polar Q f₁ a₁ = 1 := by rw [polar_comm, h11]
  have ha₁a₁ : polar Q a₁ a₁ = 0 := polar_self_eq_zero hQa₁
  have hf₁f₁ : polar Q f₁ f₁ = 0 := polar_self_eq_zero hQf₁
  set y₁ := y - c₁ • a₁ - c₂ • f₁ with hy₁
  have hy₁U : y₁ ∈ U := U.sub_mem (U.sub_mem hyU (U.smul_mem _ ha₁)) (U.smul_mem _ hf₁)
  have hy₁a : polar Q y₁ a₁ = 0 := by
    rw [hy₁, polar_sub_left, polar_sub_left, polar_smul_left_eq, polar_smul_left_eq, ha₁a₁,
      ha₁f₁]
    ring
  have hy₁f : polar Q y₁ f₁ = 0 := by
    rw [hy₁, polar_sub_left, polar_sub_left, polar_smul_left_eq, polar_smul_left_eq, h11,
      hf₁f₁]
    ring
  have hy₁a' : polar Q a₁ y₁ = 0 := by rw [polar_comm, hy₁a]
  have hmul : ∀ (c : K) (u : V), u ∈ U → Q u = 0 → c • u ∈ A := fun c u hu hQu =>
    hsing _ (U.smul_mem _ hu) (by rw [map_smul_eq_sq, hQu, mul_zero])
  have hs'Q : Q (y₁ + a₁ - Q y₁ • f₁) = 0 := by
    rw [map_sub_smul', QuadraticMap.map_add Q y₁ a₁, hQa₁, hQf₁, hy₁a, polar_add_left, hy₁f, h11]
    ring
  have hs'U : y₁ + a₁ - Q y₁ • f₁ ∈ U := U.sub_mem (U.add_mem hy₁U ha₁) (U.smul_mem _ hf₁)
  have hs'A : y₁ + a₁ - Q y₁ • f₁ ∈ A := hsing _ hs'U hs'Q
  have ha₁A : a₁ ∈ A := hsing _ ha₁ hQa₁
  have hy₁A : y₁ ∈ A := by
    have : y₁ = (y₁ + a₁ - Q y₁ • f₁) - a₁ + Q y₁ • f₁ := by abel
    rw [this]
    exact A.add_mem (A.sub_mem hs'A ha₁A) (hmul _ f₁ hf₁ hQf₁)
  have : y = y₁ + c₁ • a₁ + c₂ • f₁ := by rw [hy₁]; abel
  rw [this]
  exact A.add_mem (A.add_mem hy₁A (hmul _ a₁ ha₁ hQa₁)) (hmul _ f₁ hf₁ hQf₁)

end Inv

end CFSG.LieType.SeitzGeneration
