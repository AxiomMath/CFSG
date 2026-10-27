module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotSwapBoundsLagrangian

public section

namespace CFSG.SeitzReduction.OmegaPilot

open CFSG Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.RankThree.OrthogonalInvolutions (commSpace mem_commSpace polar_commSpace_eq_zero
  polar_sub_eq_polar_sub)

section LeviPair

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem exists_levi_pair_of_four_le [CharP K 2] {Q : QuadraticForm K V}
    (hQ : (polarBilin Q).Nondegenerate) {t : V ≃ₗ[K] V}
    (ht : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (htt : t * t = 1) {n : ℕ} (hn : 4 ≤ n)
    (hV : Module.finrank K V = 2 * n) (hW : Module.finrank K (commSpace t) = n)
    {W₀ : Submodule K V} (hW₀W : W₀ ≤ commSpace t) (hW₀sing : ∀ x ∈ W₀, Q x = 0)
    (hW₀ : n - 1 ≤ Module.finrank K W₀) :
    ∃ v₁ v₂ : V, t v₁ - v₁ ∈ W₀ ∧ t v₂ - v₂ ∈ W₀ ∧
      v₁ ∉ LinearMap.BilinForm.orthogonal (polarBilin Q) W₀ ∧
      v₂ ∉ LinearMap.BilinForm.orthogonal (polarBilin Q) W₀ ∧
      (∀ a b : K, a • (t v₁ - v₁) + b • (t v₂ - v₂) = 0 → a = 0 ∧ b = 0) ∧
      polar Q v₁ v₂ = 0 ∧ polar Q (t v₁ - v₁) v₂ = 0 := by
  set W := commSpace t with hWdef
  set f : V →ₗ[K] V := (t : V →ₗ[K] V) - 1 with hfdef
  have hWiso : ∀ x ∈ W, ∀ y ∈ W, polar Q x y = 0 := fun x hx y hy =>
    polar_commSpace_eq_zero ht htt hx hy
  have hfix : CFSG.RankThree.OrthogonalInvolutions.fixSpace t = W := by
    have h1 : Module.finrank K W +
        Module.finrank K (CFSG.RankThree.OrthogonalInvolutions.fixSpace t) =
          Module.finrank K V :=
      CFSG.RankThree.OrthogonalInvolutions.finrank_commSpace_add_finrank_fixSpace t
    have h2 : W ≤ CFSG.RankThree.OrthogonalInvolutions.fixSpace t :=
      CFSG.RankThree.OrthogonalInvolutions.commSpace_le_fixSpace htt
    exact (Submodule.eq_of_le_of_finrank_eq h2 (by omega)).symm
  have hWfix : ∀ w ∈ W, t w = w := fun w hw =>
    CFSG.RankThree.OrthogonalInvolutions.mem_fixSpace.mp (hfix ▸ hw)
  have hfixW : ∀ x, t x = x → x ∈ W := fun x hx =>
    hfix ▸ CFSG.RankThree.OrthogonalInvolutions.mem_fixSpace.mpr hx
  set O₀ := LinearMap.BilinForm.orthogonal (polarBilin Q) W₀ with hO₀
  have hmemO : ∀ {x}, x ∈ O₀ ↔ ∀ w ∈ W₀, polar Q w x = 0 := fun {x} => by
    rw [hO₀, LinearMap.BilinForm.mem_orthogonal_iff]
    rfl
  have hO₀dim : Module.finrank K O₀ = 2 * n - Module.finrank K W₀ := by
    rw [hO₀, LinearMap.BilinForm.finrank_orthogonal hQ, hV]
  have hWO₀ : W ≤ O₀ := fun x hx => hmemO.mpr fun w hw => hWiso w (hW₀W hw) x hx
  set Y₀ := W₀.comap f with hY₀
  have hY₀dim : Module.finrank K Y₀ = Module.finrank K W₀ + n := by
    rw [hY₀, finrank_comap_eq_of_le_range f hW₀W]
    congr 1
    have := hfix ▸ hW
    exact this
  have hWY₀ : W ≤ Y₀ := fun x hx => by
    change t x - x ∈ W₀
    rw [hWfix x hx, sub_self]
    exact W₀.zero_mem
  have hpol_self : ∀ v, polar Q (t v - v) v = Q (t v - v) := fun v => by
    rw [polar_sub_left, CFSG.RankThree.OrthogonalInvolutions.polar_self_eq_zero Q v, sub_zero,
      CFSG.RankThree.OrthogonalInvolutions.map_sub_eq_polar ht v]
  obtain ⟨v₁, hv₁Y, hv₁O⟩ := exists_mem_not_mem_of_finrank_lt (A := Y₀) (B := O₀) (by omega)
  have he₁ : t v₁ - v₁ ∈ W₀ := hv₁Y
  have he₁0 : t v₁ - v₁ ≠ 0 := fun h => hv₁O (hWO₀ (hfixW v₁ (sub_eq_zero.mp h)))
  set Z := Y₀ ⊓ LinearMap.BilinForm.orthogonal (polarBilin Q) (K ∙ (t v₁ - v₁)) with hZ
  have hmemZ : ∀ {x}, x ∈ Z ↔ x ∈ Y₀ ∧ polar Q (t v₁ - v₁) x = 0 := fun {x} => by
    rw [hZ, Submodule.mem_inf, LinearMap.BilinForm.mem_orthogonal_iff]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      have := h2 _ (Submodule.mem_span_singleton_self _)
      rwa [polarBilin_apply_apply] at this
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun w hw => ?_⟩
      obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hw
      rw [polarBilin_apply_apply, polar_smul_left, h2, smul_zero]
  have hZdim : 2 * n - 2 ≤ Module.finrank K Z := by
    have h1 : Module.finrank K Y₀ + Module.finrank K
        (LinearMap.BilinForm.orthogonal (polarBilin Q) (K ∙ (t v₁ - v₁))) - Module.finrank K V ≤
          Module.finrank K Z := finrank_inf_ge _ _
    have h3 : Module.finrank K
        (LinearMap.BilinForm.orthogonal (polarBilin Q) (K ∙ (t v₁ - v₁))) =
          Module.finrank K V - Module.finrank K (K ∙ (t v₁ - v₁)) :=
      LinearMap.BilinForm.finrank_orthogonal hQ _
    rw [finrank_span_singleton he₁0] at h3
    omega
  have hv₁Z : v₁ ∈ Z := hmemZ.mpr ⟨hv₁Y, by rw [hpol_self]; exact hW₀sing _ he₁⟩
  set B₁ := W ⊔ K ∙ v₁ with hB₁
  have hB₁dim : Module.finrank K B₁ ≤ n + 1 := by
    have h1 : Module.finrank K B₁ ≤ Module.finrank K W + Module.finrank K (K ∙ v₁) :=
      Submodule.finrank_add_le_finrank_add_finrank W (K ∙ v₁)
    have h2 : Module.finrank K (K ∙ v₁) ≤ 1 := by
      by_cases h0 : v₁ = 0
      · rw [h0, Submodule.span_singleton_eq_bot.mpr rfl, finrank_bot]; omega
      · rw [finrank_span_singleton h0]
    omega
  obtain ⟨y, hyZ, hyB⟩ := exists_mem_not_mem_of_finrank_lt (A := Z) (B := B₁) (by omega)
  have hv₁B : v₁ ∈ B₁ := Submodule.mem_sup_right (Submodule.mem_span_singleton_self v₁)
  obtain ⟨x, hxZ, hxO, hxB⟩ : ∃ x ∈ Z, x ∉ O₀ ∧ x ∉ B₁ := by
    by_cases hyO : y ∈ O₀
    · refine ⟨y + v₁, Z.add_mem hyZ hv₁Z, fun h => hv₁O ?_, fun h => hyB ?_⟩
      · have := O₀.sub_mem h hyO
        rwa [add_sub_cancel_left] at this
      · have := B₁.sub_mem h hv₁B
        rwa [add_sub_cancel_right] at this
    · exact ⟨y, hyZ, hyO, hyB⟩
  obtain ⟨hxY, hxe₁⟩ := hmemZ.mp hxZ
  have hv₁W : v₁ ∉ LinearMap.BilinForm.orthogonal (polarBilin Q) W := fun h =>
    hv₁O (LinearMap.BilinForm.orthogonal_le hW₀W h)
  obtain ⟨w₀, hw₀W, hw₀⟩ : ∃ w₀ ∈ W, polar Q v₁ w₀ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hv₁W
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro w hw
    rw [polarBilin_apply_apply, polar_comm]
    exact hcon w hw
  set c₀ := -(polar Q v₁ x / polar Q v₁ w₀) with hc₀
  have he₃ : t (x + c₀ • w₀) - (x + c₀ • w₀) = t x - x := by
    rw [map_add, map_smul, hWfix w₀ hw₀W]
    abel
  refine ⟨v₁, x + c₀ • w₀, he₁, by rw [he₃]; exact hxY, hv₁O, fun h => hxO ?_, ?_, ?_, ?_⟩
  · have := O₀.sub_mem h (O₀.smul_mem c₀ (hWO₀ hw₀W))
    rwa [add_sub_cancel_right] at this
  · rw [he₃]
    intro a b hab
    by_cases hb : b = 0
    · subst hb
      rw [zero_smul, add_zero, smul_eq_zero] at hab
      exact ⟨hab.resolve_right he₁0, rfl⟩
    · exfalso
      apply hxB
      have hfx : t (x + (b⁻¹ * a) • v₁) = x + (b⁻¹ * a) • v₁ := by
        have h1 : t (x + (b⁻¹ * a) • v₁) - (x + (b⁻¹ * a) • v₁) =
            b⁻¹ • (a • (t v₁ - v₁) + b • (t x - x)) := by
          rw [map_add, map_smul, smul_add, smul_smul, smul_smul, inv_mul_cancel₀ hb, one_smul,
            smul_sub]
          abel
        rw [hab, smul_zero] at h1
        exact sub_eq_zero.mp h1
      have hmem := hfixW _ hfx
      have : x = (x + (b⁻¹ * a) • v₁) - (b⁻¹ * a) • v₁ := by abel
      rw [this]
      exact B₁.sub_mem (Submodule.mem_sup_left hmem) (B₁.smul_mem _ hv₁B)
  · rw [polar_add_right, polar_smul_right, smul_eq_mul, hc₀, neg_mul,
      div_mul_cancel₀ _ hw₀, add_neg_cancel]
  · rw [polar_add_right, polar_smul_right, hxe₁,
      hWiso _ (hW₀W he₁) _ hw₀W, smul_zero, add_zero]

end LeviPair

section Lagrangian

open CFSG.ComponentClassification.UnbalancedCatalog.OmegaRadical (flagRadical mem_flagRadical_iff)

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_twoSubgroup_centralizer_of_lagrangian_of_four_le {n : ℕ} (hn : 4 ≤ n)
    {Q : QuadraticForm K (Fin (2 * n) → K)} (hQ : (polarBilin Q).Nondegenerate)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q)
    {s : GL (Fin (2 * n)) K} (hs : s ∈ matrixIsometries Q) (hss : s * s = 1)
    (hl : Module.finrank K (commSpace (matrixLinearIso s)) = n) :
    ∃ R : Subgroup (GL (Fin (2 * n)) K), IsPGroup 2 R ∧
      R ≤ matrixDerived Q ⊓ Subgroup.centralizer {s} ∧
      Nat.card K ^ (n * (n - 1) / 2 + 2) ≤ Nat.card R := by
  set t := matrixLinearIso s with htdef
  have ht : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q := hs
  have htt : t * t = 1 := by rw [htdef, ← map_mul, hss, map_one]
  set W := commSpace t with hWdef
  have hWiso : ∀ x ∈ W, ∀ y ∈ W, polar Q x y = 0 := fun x hx y hy =>
    polar_commSpace_eq_zero ht htt hx hy
  have hdimV : Module.finrank K (Fin (2 * n) → K) = 2 * n := Module.finrank_fin_fun K
  have hfix : CFSG.RankThree.OrthogonalInvolutions.fixSpace t = W := by
    have h1 : Module.finrank K W +
        Module.finrank K (CFSG.RankThree.OrthogonalInvolutions.fixSpace t) =
          Module.finrank K (Fin (2 * n) → K) :=
      CFSG.RankThree.OrthogonalInvolutions.finrank_commSpace_add_finrank_fixSpace t
    have h2 : W ≤ CFSG.RankThree.OrthogonalInvolutions.fixSpace t :=
      CFSG.RankThree.OrthogonalInvolutions.commSpace_le_fixSpace htt
    exact (Submodule.eq_of_le_of_finrank_eq h2 (by omega)).symm
  have hWfix : ∀ w ∈ W, t w = w := fun w hw =>
    CFSG.RankThree.OrthogonalInvolutions.mem_fixSpace.mp (hfix ▸ hw)
  obtain ⟨a, haW, hWa⟩ := exists_le_singularPart_sup W hWiso
  set W₀ := singularPart Q W hWiso with hW₀def
  have hW₀W : W₀ ≤ W := fun x hx => hx.1
  have hW₀sing : ∀ x ∈ W₀, Q x = 0 := fun x hx => hx.2
  have hm2 : Module.finrank K W₀ ≤ n := by
    have := Submodule.finrank_mono hW₀W
    omega
  have hm1 : n - 1 ≤ Module.finrank K W₀ := by
    have h1 := Submodule.finrank_mono hWa
    have h2 := Submodule.finrank_add_le_finrank_add_finrank W₀ (K ∙ a)
    have h3 : Module.finrank K (K ∙ a) ≤ 1 := by
      by_cases h0 : a = 0
      · rw [h0, Submodule.span_singleton_eq_bot.mpr rfl, finrank_bot]; omega
      · rw [finrank_span_singleton h0]
    omega
  obtain ⟨R₀, -, hR₀le, hR₀rad, hR₀card⟩ := exists_twoSubgroup_of_totallySingular hQ hE hs hss
    (T := W₀) rfl hW₀sing (fun x hx => hWiso x hx.1 a haW)
    (fun v => hWa (mem_commSpace.mpr ⟨v, rfl⟩))
    (c := 2 * n - (2 * Module.finrank K W₀ + 1))
    (Or.inl le_rfl)
  obtain ⟨v₁, v₂, he₁, he₃, hv₁O, hv₂O, hind, hv₁₂, he₁v₂⟩ :=
    exists_levi_pair_of_four_le hQ ht htt hn hdimV hl hW₀W hW₀sing hm1
  set O₀ := LinearMap.BilinForm.orthogonal (polarBilin Q) W₀ with hO₀
  set e₁ := t v₁ - v₁ with he₁def
  set e₃ := t v₂ - v₂ with he₃def
  have hmemO : ∀ {x}, x ∈ O₀ ↔ ∀ w ∈ W₀, polar Q w x = 0 := fun {x} => by
    rw [hO₀, LinearMap.BilinForm.mem_orthogonal_iff]
    rfl
  have hW₀O : W₀ ≤ O₀ := fun x hx => hmemO.mpr fun w hw => hWiso w hw.1 x hx.1
  have hQe₁ : Q e₁ = 0 := hW₀sing e₁ he₁
  have hQe₃ : Q e₃ = 0 := hW₀sing e₃ he₃
  have hpol_self : ∀ v, polar Q (t v - v) v = Q (t v - v) := fun v => by
    rw [polar_sub_left, CFSG.RankThree.OrthogonalInvolutions.polar_self_eq_zero Q v, sub_zero,
      CFSG.RankThree.OrthogonalInvolutions.map_sub_eq_polar ht v]
  have he₁v₁ : polar Q e₁ v₁ = 0 := by rw [he₁def, hpol_self, ← he₁def, hQe₁]
  have he₃v₂ : polar Q e₃ v₂ = 0 := by rw [he₃def, hpol_self, ← he₃def, hQe₃]
  have he₃v₁ : polar Q e₃ v₁ = 0 := by
    rw [he₃def, polar_sub_eq_polar_sub ht htt, ← he₁def, polar_comm]
    exact he₁v₂
  have he₁₃ : polar Q e₁ e₃ = 0 := hWiso _ he₁.1 _ he₃.1
  have hc₁ : ∀ c : K, polar Q e₁ (c • v₁) = 0 := fun c => by
    rw [polar_smul_right, he₁v₁, smul_zero]
  have hc₃ : ∀ c : K, polar Q e₃ (c • v₂) = 0 := fun c => by
    rw [polar_smul_right, he₃v₂, smul_zero]
  have hE₁fix : ∀ c : K, ∀ x, polar Q x e₁ = 0 → polar Q x v₁ = 0 →
      eichler Q e₁ (c • v₁) x = x :=
    fun c x h1 h2 => eichler_apply_of_polar_eq_zero h1 (by rw [polar_smul_right, h2, smul_zero])
  have hcomm : ∀ c c' : K, eichler Q e₁ (c • v₁) * eichler Q e₃ (c' • v₂) =
      eichler Q e₃ (c' • v₂) * eichler Q e₁ (c • v₁) := by
    intro c c'
    have h := eichler_conj (eichler_mem_orthogonalGroup Q e₁ (c • v₁)) e₃ (c' • v₂)
    rw [hE₁fix c e₃ (by rw [polar_comm]; exact he₁₃) he₃v₁, map_smul,
      hE₁fix c v₂ (by rw [polar_comm]; exact he₁v₂) (by rw [polar_comm]; exact hv₁₂)] at h
    calc eichler Q e₁ (c • v₁) * eichler Q e₃ (c' • v₂)
        = eichler Q e₁ (c • v₁) * eichler Q e₃ (c' • v₂) * (eichler Q e₁ (c • v₁))⁻¹ *
          eichler Q e₁ (c • v₁) := by group
      _ = eichler Q e₃ (c' • v₂) * eichler Q e₁ (c • v₁) := by rw [h]
  have hact : ∀ c c' : K, ∀ x ∈ O₀, eichler Q e₁ (c • v₁) (eichler Q e₃ (c' • v₂) x) =
      x - (c * polar Q x v₁) • e₁ - (c' * polar Q x v₂) • e₃ := by
    intro c c' x hx
    have hx₁ : polar Q x e₁ = 0 := by rw [polar_comm]; exact hmemO.mp hx e₁ he₁
    have hx₃ : polar Q x e₃ = 0 := by rw [polar_comm]; exact hmemO.mp hx e₃ he₃
    rw [eichler_apply_of_polar_left hQe₃ (hc₃ c') hx₃, map_sub, map_smul,
      eichler_apply_of_polar_left hQe₁ (hc₁ c) hx₁,
      hE₁fix c e₃ (by rw [polar_comm]; exact he₁₃) he₃v₁, polar_smul_right, polar_smul_right,
      smul_eq_mul, smul_eq_mul]
  have hkey : ∀ c c' : K, (∀ x ∈ W₀, eichler Q e₁ (c • v₁) (eichler Q e₃ (c' • v₂) x) = x) →
      c = 0 ∧ c' = 0 := by
    intro c c' hfixW
    have hrel : ∀ x ∈ W₀, c * polar Q x v₁ = 0 ∧ c' * polar Q x v₂ = 0 := by
      intro x hx
      have h1 := hact c c' x (hW₀O hx)
      rw [hfixW x hx] at h1
      have h2 : (c * polar Q x v₁) • e₁ + (c' * polar Q x v₂) • e₃ = 0 := by
        have := congrArg (fun y => x - y) h1
        simp only [sub_self] at this
        rw [show x - (x - (c * polar Q x v₁) • e₁ - (c' * polar Q x v₂) • e₃) =
          (c * polar Q x v₁) • e₁ + (c' * polar Q x v₂) • e₃ by abel] at this
        exact this.symm
      exact hind _ _ h2
    have hpick : ∀ v, v ∉ O₀ → ∃ x ∈ W₀, polar Q x v ≠ 0 := fun v hv => by
      by_contra hcon
      push Not at hcon
      exact hv (hmemO.mpr hcon)
    obtain ⟨x₁, hx₁, hx₁v⟩ := hpick v₁ hv₁O
    obtain ⟨x₂, hx₂, hx₂v⟩ := hpick v₂ hv₂O
    exact ⟨(mul_eq_zero.mp (hrel x₁ hx₁).1).resolve_right hx₁v,
      (mul_eq_zero.mp (hrel x₂ hx₂).2).resolve_right hx₂v⟩
  have hspan_pol : ∀ (S : Set (Fin (2 * n) → K)) (v : Fin (2 * n) → K),
      (∀ y ∈ S, polar Q y v = 0) → ∀ x ∈ Submodule.span K S, polar Q x v = 0 := by
    intro S v hS x hx
    have hle : Submodule.span K S ≤ LinearMap.ker (polarBilin Q v) :=
      Submodule.span_le.mpr fun y hy => by
        change polarBilin Q v y = 0
        rw [polarBilin_apply_apply, polar_comm]
        exact hS y hy
    have h := hle hx
    rw [LinearMap.mem_ker, polarBilin_apply_apply, polar_comm] at h
    exact h
  let E : K × K → ((Fin (2 * n) → K) ≃ₗ[K] (Fin (2 * n) → K)) := fun p =>
    eichler Q e₁ (p.1 • v₁) * eichler Q e₃ (p.2 • v₂)
  have hEmul : ∀ p p' : K × K, E (p + p') = E p * E p' := by
    intro p p'
    simp only [E, Prod.fst_add, Prod.snd_add, add_smul]
    rw [← eichler_mul (hc₁ _) (hc₁ _), ← eichler_mul (hc₃ _) (hc₃ _)]
    calc eichler Q e₁ (p.1 • v₁) * eichler Q e₁ (p'.1 • v₁) *
          (eichler Q e₃ (p.2 • v₂) * eichler Q e₃ (p'.2 • v₂))
        = eichler Q e₁ (p.1 • v₁) * (eichler Q e₁ (p'.1 • v₁) * eichler Q e₃ (p.2 • v₂)) *
          eichler Q e₃ (p'.2 • v₂) := by group
      _ = eichler Q e₁ (p.1 • v₁) * (eichler Q e₃ (p.2 • v₂) * eichler Q e₁ (p'.1 • v₁)) *
          eichler Q e₃ (p'.2 • v₂) := by rw [hcomm]
      _ = eichler Q e₁ (p.1 • v₁) * eichler Q e₃ (p.2 • v₂) *
          (eichler Q e₁ (p'.1 • v₁) * eichler Q e₃ (p'.2 • v₂)) := by group
  let ψ : Multiplicative (K × K) →* GL (Fin (2 * n)) K :=
    { toFun := fun p => matrixLinearIso.symm (E (Multiplicative.toAdd p))
      map_one' := by
        simp only [toAdd_one, E, Prod.fst_zero, Prod.snd_zero, zero_smul, eichler_zero_right,
          mul_one, map_one]
      map_mul' := fun p p' => by rw [toAdd_mul, hEmul, map_mul] }
  have hψ : ∀ p, matrixLinearIso (ψ p) = E (Multiplicative.toAdd p) := fun p =>
    MulEquiv.apply_symm_apply _ _
  have hfixW₀ : ∀ p, (∀ x ∈ W₀, matrixLinearIso (ψ p) x = x) → p = 1 := by
    intro p hp
    obtain ⟨h1, h2⟩ := hkey (Multiplicative.toAdd p).1 (Multiplicative.toAdd p).2 fun x hx => by
      have := hp x hx
      rwa [hψ] at this
    have : Multiplicative.toAdd p = 0 := Prod.ext h1 h2
    exact toAdd_eq_zero.mp this
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro p hp
    exact hfixW₀ p fun x _ => by rw [hp, map_one]; rfl
  set F₁ := Submodule.span K ({e₁, e₃} : Set (Fin (2 * n) → K)) with hF₁
  set F₄ := O₀ ⊔ Submodule.span K ({v₁, v₂} : Set (Fin (2 * n) → K)) with hF₄
  have h12 : F₁ ≤ W₀ := Submodule.span_le.mpr (by
    rintro x (rfl | rfl)
    · exact he₁
    · exact he₃)
  have h34 : O₀ ≤ F₄ := le_sup_left
  set R := flagGroup F₁ W₀ O₀ F₄ h12 hW₀O h34 ⊓ (matrixDerived Q ⊓ Subgroup.centralizer {s})
    with hRdef
  have hR2 : IsPGroup 2 R :=
    (isPGroup_flagGroup F₁ W₀ O₀ F₄ h12 hW₀O h34).to_le inf_le_left
  have hR₀R : R₀ ≤ R := by
    intro g hg
    refine ⟨?_, hR₀le hg⟩
    obtain ⟨g', hg', rfl⟩ := hR₀rad hg
    obtain ⟨g1, g2, g3⟩ := mem_flagRadical_iff.mp hg'
    refine ⟨fun x hx => g1 x (h12 hx), fun x hx => ?_, fun x hx => g2 x hx, fun x _ => g3 x,
      fun x => h34 (g3 x)⟩
    change matrixLinearEquiv g'.val x - x ∈ F₁
    rw [g1 x hx, sub_self]
    exact F₁.zero_mem
  have hfactor : ∀ (e v : Fin (2 * n) → K), e ∈ F₁ → e = t v - v → v ∈ F₄ →
      polar Q e₁ v = 0 → polar Q e₃ v = 0 → polar Q v₁ e = 0 → polar Q v₂ e = 0 →
      ∀ c : K, matrixLinearIso.symm (eichler Q e (c • v)) ∈ R := by
    intro e v heF hev hvF h1 h3 hv1 hv2 c
    have he : e ∈ W₀ := h12 heF
    have hQe : Q e = 0 := hW₀sing e he
    have hpe : polar Q e (c • v) = 0 := by
      rw [polar_smul_right, hev, hpol_self, ← hev, hQe, smul_zero]
    have happ : ∀ x, matrixLinearIso (matrixLinearIso.symm (eichler Q e (c • v))) x =
        eichler Q e (c • v) x := fun x => by rw [MulEquiv.apply_symm_apply]
    have hO₀e : ∀ x ∈ O₀, polar Q x e = 0 := fun x hx => by
      rw [polar_comm]; exact hmemO.mp hx e he
    have hF₄e : ∀ x ∈ F₄, polar Q x e = 0 := by
      intro x hx
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
      rw [polar_add_left, hO₀e y hy, zero_add]
      refine hspan_pol _ e ?_ z hz
      rintro w (rfl | rfl)
      · exact hv1
      · exact hv2
    have hgen : ∀ x, polar Q x e = 0 → eichler Q e (c • v) x - x = -(polar Q x (c • v)) • e :=
      fun x hx => by
        rw [eichler_apply_of_polar_left hQe hpe hx, sub_sub_cancel_left, neg_smul]
    refine ⟨⟨fun x hx => ?_, fun x hx => ?_, fun x hx => ?_, fun x hx => ?_, fun x => ?_⟩, ?_, ?_⟩
    · rw [happ]
      refine eichler_apply_of_polar_eq_zero (hspan_pol _ e ?_ x hx) ?_
      · rintro w (rfl | rfl)
        · exact hWiso _ he₁.1 _ he.1
        · exact hWiso _ he₃.1 _ he.1
      · rw [polar_smul_right, hspan_pol _ v ?_ x hx, smul_zero]
        rintro w (rfl | rfl)
        · exact h1
        · exact h3
    · rw [happ, hgen x (hWiso x hx.1 e he.1)]
      exact F₁.smul_mem _ heF
    · rw [happ, hgen x (hO₀e x hx)]
      exact W₀.smul_mem _ he
    · rw [happ, hgen x (hF₄e x hx)]
      exact O₀.smul_mem _ (hW₀O he)
    · rw [happ, eichler_apply hQe hpe, add_sub_assoc, add_sub_cancel_left]
      refine sub_mem ?_ ?_
      · refine Submodule.smul_mem _ _ (Submodule.smul_mem _ _ ?_)
        exact hvF
      · exact Submodule.smul_mem _ _ (h34 (hW₀O he))
    · show _ ∈ matrixDerived Q
      rw [CFSG.ComponentClassification.CatalogueBOrthogonalFixedTransfer.mem_matrixDerived_iff,
        MulEquiv.apply_symm_apply, hE]
      exact eichler_mem_elementaryGroup Q e (c • v)
    · show _ ∈ Subgroup.centralizer {s}
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply matrixLinearIso.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, ← htdef]
      have hte : t e = e := hWfix e he.1
      have htv : t (c • v) = c • v + c • e := by
        rw [map_smul, hev, ← smul_add, add_sub_cancel]
      have h := eichler_conj ht e (c • v)
      rw [hte, htv, eichler_add_smul_self hQe] at h
      calc eichler Q e (c • v) * t = t * eichler Q e (c • v) * t⁻¹ * t := by rw [h]
        _ = t * eichler Q e (c • v) := by group
  have he₁F : e₁ ∈ F₁ := Submodule.subset_span (Set.mem_insert _ _)
  have he₃F : e₃ ∈ F₁ := Submodule.subset_span (Set.mem_insert_of_mem _ rfl)
  have hv₁F : v₁ ∈ F₄ := Submodule.mem_sup_right (Submodule.subset_span (Set.mem_insert _ _))
  have hv₂F : v₂ ∈ F₄ :=
    Submodule.mem_sup_right (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))
  set H := ψ.range with hHdef
  have hHR : H ≤ R := by
    rintro _ ⟨p, rfl⟩
    have hsplit : ψ p = matrixLinearIso.symm (eichler Q e₁ ((Multiplicative.toAdd p).1 • v₁)) *
        matrixLinearIso.symm (eichler Q e₃ ((Multiplicative.toAdd p).2 • v₂)) := by
      change matrixLinearIso.symm (E (Multiplicative.toAdd p)) = _
      rw [← map_mul]
    rw [hsplit]
    refine R.mul_mem ?_ ?_
    · exact hfactor e₁ v₁ he₁F rfl hv₁F he₁v₁ he₃v₁ (by rw [polar_comm]; exact he₁v₁)
        (by rw [polar_comm]; exact he₁v₂) _
    · exact hfactor e₃ v₂ he₃F rfl hv₂F he₁v₂ he₃v₂ (by rw [polar_comm]; exact he₃v₁)
        (by rw [polar_comm]; exact he₃v₂) _
  have hR₀H : R₀ ⊓ H = ⊥ := by
    rw [eq_bot_iff]
    rintro g ⟨hg, p, rfl⟩
    obtain ⟨g', hg', hgg'⟩ := hR₀rad hg
    have hg1 := (mem_flagRadical_iff.mp hg').1
    rw [hfixW₀ p fun x hx => by
      have := hg1 x hx
      rw [← hgg']
      exact this, map_one]
    exact Subgroup.one_mem _
  have hHcard : Nat.card H = Nat.card K ^ 2 := by
    rw [hHdef, ← Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (K × K) ≃ _), Nat.card_prod,
      _root_.sq]
  have hcount := card_mul_card_le_card_of_inf_eq_bot hR₀R hHR hR₀H
  have hq : 1 ≤ Nat.card K := Nat.card_pos
  have hR₀' : Nat.card K ^ (n * (n - 1) / 2) ≤ Nat.card R₀ :=
    le_trans (Nat.pow_le_pow_right hq (lagrangian_exponent_le hm1 hm2 (by omega))) hR₀card
  refine ⟨R, hR2, inf_le_right, ?_⟩
  calc Nat.card K ^ (n * (n - 1) / 2 + 2) = Nat.card K ^ (n * (n - 1) / 2) * Nat.card K ^ 2 :=
        pow_add _ _ _
    _ ≤ Nat.card R₀ * Nat.card H := by rw [hHcard]; exact Nat.mul_le_mul_right _ hR₀'
    _ ≤ Nat.card R := hcount

end Lagrangian

end CFSG.SeitzReduction.OmegaPilot
