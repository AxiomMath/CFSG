module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotSwapBoundsLagrangian

public section

namespace CFSG.SeitzReduction.OmegaPilot

open CFSG Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

section Fix

open CFSG.RankThree.OrthogonalInvolutions (commSpace mem_commSpace)

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem apply_eq_of_le_sup_span (hQ : (polarBilin Q).Nondegenerate) {t : V ≃ₗ[K] V}
    (ht : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (htt : t * t = 1) {T : Submodule K V}
    (hTsing : ∀ x ∈ T, Q x = 0) {a : V} (hTa : ∀ x ∈ T, polar Q x a = 0)
    (hW : ∀ v, t v - v ∈ T ⊔ K ∙ a) {x : V} (hx : x ∈ T) : t x = x := by
  have hmem : x ∈ CFSG.RankThree.OrthogonalInvolutions.fixSpace t := by
    rw [CFSG.RankThree.OrthogonalInvolutions.fixSpace_eq_orthogonal_commSpace hQ ht htt,
      LinearMap.BilinForm.mem_orthogonal_iff]
    intro w hw
    obtain ⟨v, rfl⟩ := mem_commSpace.mp hw
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp (hW v)
    obtain ⟨c', rfl⟩ := Submodule.mem_span_singleton.mp hz
    change polarBilin Q (t v - v) x = 0
    rw [polarBilin_apply_apply, ← hyz, polar_add_left, polar_smul_left,
      polar_eq_zero_of_totallySingular hTsing hy hx, polar_comm, hTa x hx, smul_zero, add_zero]
  exact CFSG.RankThree.OrthogonalInvolutions.mem_fixSpace.mp hmem

end Fix

section LeviOne

open CFSG.ComponentClassification.UnbalancedCatalog.OmegaRadical (flagRadical mem_flagRadical_iff)

variable {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

omit [Finite K] [CharP K 2] in
theorem eichler_mem_flagGroup_levi_one
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q)
    {s : GL (Fin d) K} (hs : s ∈ matrixIsometries Q) {T : Submodule K (Fin d → K)}
    (hTsing : ∀ x ∈ T, Q x = 0) (hTfix : ∀ x ∈ T, matrixLinearIso s x = x)
    {e v : Fin d → K} (heT : e ∈ T) (hv : matrixLinearIso s v - v ∈ K ∙ e)
    (hev : polar Q e v = 0)
    (h12 : K ∙ e ≤ T) (h23 : T ≤ LinearMap.BilinForm.orthogonal (polarBilin Q) T)
    (h34 : LinearMap.BilinForm.orthogonal (polarBilin Q) T ≤
      LinearMap.BilinForm.orthogonal (polarBilin Q) T ⊔ K ∙ v) (c : K) :
    matrixLinearIso.symm (eichler Q e (c • v)) ∈
      flagGroup (K ∙ e) T (LinearMap.BilinForm.orthogonal (polarBilin Q) T)
          (LinearMap.BilinForm.orthogonal (polarBilin Q) T ⊔ K ∙ v) h12 h23 h34 ⊓
        (matrixDerived Q ⊓ Subgroup.centralizer {s}) := by
  set t := matrixLinearIso s with htdef
  have ht : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q := hs
  set O := LinearMap.BilinForm.orthogonal (polarBilin Q) T with hO
  have hmemO : ∀ {x}, x ∈ O ↔ ∀ w ∈ T, polar Q w x = 0 := fun {x} => by
    rw [hO, LinearMap.BilinForm.mem_orthogonal_iff]
    rfl
  have hQe : Q e = 0 := hTsing e heT
  have hpe : polar Q e (c • v) = 0 := by rw [polar_smul_right, hev, smul_zero]
  have happ : ∀ x, matrixLinearIso (matrixLinearIso.symm (eichler Q e (c • v))) x =
      eichler Q e (c • v) x := fun x => by rw [MulEquiv.apply_symm_apply]
  have hOe : ∀ x ∈ O, polar Q x e = 0 := fun x hx => by
    rw [polar_comm]
    exact hmemO.mp hx e heT
  have hF₄e : ∀ x ∈ O ⊔ K ∙ v, polar Q x e = 0 := by
    intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hz
    rw [polar_add_left, hOe y hy, zero_add, polar_smul_left, polar_comm, hev, smul_zero]
  have hgen : ∀ x, polar Q x e = 0 → eichler Q e (c • v) x - x = -(polar Q x (c • v)) • e :=
    fun x hx => by
      rw [eichler_apply_of_polar_left hQe hpe hx, sub_sub_cancel_left, neg_smul]
  refine ⟨⟨fun x hx => ?_, fun x hx => ?_, fun x hx => ?_, fun x hx => ?_, fun x => ?_⟩, ?_, ?_⟩
  · obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [happ, eichler_apply_smul_self]
  · rw [happ, hgen x (hOe x (h23 hx))]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self e)
  · rw [happ, hgen x (hOe x hx)]
    exact T.smul_mem _ heT
  · rw [happ, hgen x (hF₄e x hx)]
    exact O.smul_mem _ (h23 heT)
  · rw [happ, eichler_apply hQe hpe, add_sub_assoc, add_sub_cancel_left]
    refine sub_mem ?_ ?_
    · exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _
        (Submodule.mem_sup_right (Submodule.mem_span_singleton_self v)))
    · exact Submodule.smul_mem _ _ (Submodule.mem_sup_left (h23 heT))
  · show _ ∈ matrixDerived Q
    rw [CFSG.ComponentClassification.CatalogueBOrthogonalFixedTransfer.mem_matrixDerived_iff,
      MulEquiv.apply_symm_apply, hE]
    exact eichler_mem_elementaryGroup Q e (c • v)
  · show _ ∈ Subgroup.centralizer {s}
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply matrixLinearIso.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, ← htdef]
    obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp hv
    have hte : t e = e := hTfix e heT
    have htv : t (c • v) = c • v + (c * μ) • e := by
      rw [map_smul, mul_smul, hμ, smul_sub, add_sub_cancel]
    have h := eichler_conj ht e (c • v)
    rw [hte, htv, eichler_add_smul_self hQe] at h
    calc eichler Q e (c • v) * t = t * eichler Q e (c • v) * t⁻¹ * t := by rw [h]
      _ = t * eichler Q e (c • v) := by group

theorem exists_twoSubgroup_of_levi_one (hQ : (polarBilin Q).Nondegenerate)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q)
    {s : GL (Fin d) K} (hs : s ∈ matrixIsometries Q) (hss : s * s = 1)
    {T : Submodule K (Fin d → K)} {m : ℕ} (hTm : Module.finrank K T = m)
    (hTsing : ∀ x ∈ T, Q x = 0) {a : Fin d → K} (hTa : ∀ x ∈ T, polar Q x a = 0)
    (hW : ∀ v, matrixLinearIso s v - v ∈ T ⊔ K ∙ a) {c : ℕ}
    (hc : c ≤ d - (2 * m + 1) ∨ (a ∈ T ∧ c ≤ d - 2 * m))
    {e v e' : Fin d → K} (heT : e ∈ T) (he0 : e ≠ 0) (hv : matrixLinearIso s v - v ∈ K ∙ e)
    (hev : polar Q e v = 0) (he'T : e' ∈ T) (he'v : polar Q e' v ≠ 0) :
    ∃ R : Subgroup (GL (Fin d) K), IsPGroup 2 R ∧
      R ≤ matrixDerived Q ⊓ Subgroup.centralizer {s} ∧
      Nat.card K ^ (m * c + m * (m - 1) / 2 + 1) ≤ Nat.card R := by
  set t := matrixLinearIso s with htdef
  have ht : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q := hs
  have htt : t * t = 1 := by rw [htdef, ← map_mul, hss, map_one]
  obtain ⟨R₀, -, hR₀le, hR₀rad, hR₀card⟩ :=
    exists_twoSubgroup_of_totallySingular hQ hE hs hss hTm hTsing hTa hW hc
  have hTfix : ∀ x ∈ T, t x = x := fun x hx =>
    apply_eq_of_le_sup_span hQ ht htt hTsing hTa hW hx
  set O := LinearMap.BilinForm.orthogonal (polarBilin Q) T with hO
  have hmemO : ∀ {x}, x ∈ O ↔ ∀ w ∈ T, polar Q w x = 0 := fun {x} => by
    rw [hO, LinearMap.BilinForm.mem_orthogonal_iff]
    rfl
  have hTO : T ≤ O := fun x hx => hmemO.mpr fun w hw =>
    polar_eq_zero_of_totallySingular hTsing hw hx
  have h12 : K ∙ e ≤ T := (Submodule.span_singleton_le_iff_mem e T).mpr heT
  have h34 : O ≤ O ⊔ K ∙ v := le_sup_left
  set R := flagGroup (K ∙ e) T O (O ⊔ K ∙ v) h12 hTO h34 ⊓
    (matrixDerived Q ⊓ Subgroup.centralizer {s}) with hRdef
  have hR2 : IsPGroup 2 R :=
    (isPGroup_flagGroup (K ∙ e) T O (O ⊔ K ∙ v) h12 hTO h34).to_le inf_le_left
  have hR₀R : R₀ ≤ R := by
    intro g hg
    refine ⟨?_, hR₀le hg⟩
    obtain ⟨g', hg', rfl⟩ := hR₀rad hg
    obtain ⟨g1, g2, g3⟩ := mem_flagRadical_iff.mp hg'
    refine ⟨fun x hx => g1 x (h12 hx), fun x hx => ?_, fun x hx => g2 x hx, fun x _ => g3 x,
      fun x => h34 (g3 x)⟩
    change matrixLinearEquiv g'.val x - x ∈ K ∙ e
    rw [g1 x hx, sub_self]
    exact Submodule.zero_mem _
  have hpe : ∀ b : K, polar Q e (b • v) = 0 := fun b => by
    rw [polar_smul_right, hev, smul_zero]
  let ψ : Multiplicative K →* GL (Fin d) K :=
    { toFun := fun b => matrixLinearIso.symm (eichler Q e (Multiplicative.toAdd b • v))
      map_one' := by rw [toAdd_one, zero_smul, eichler_zero_right, map_one]
      map_mul' := fun b b' => by
        rw [← map_mul, eichler_mul (hpe _) (hpe _), toAdd_mul, add_smul] }
  have hψ : ∀ b, matrixLinearIso (ψ b) = eichler Q e (Multiplicative.toAdd b • v) := fun b =>
    MulEquiv.apply_symm_apply _ _
  have hQe : Q e = 0 := hTsing e heT
  have hψe' : ∀ b, matrixLinearIso (ψ b) e' = e' → b = 1 := by
    intro b hb
    rw [hψ, eichler_apply_of_polar_left hQe (hpe _)
      (polar_eq_zero_of_totallySingular hTsing he'T heT)] at hb
    have h0 : polar Q e' (Multiplicative.toAdd b • v) • e = 0 := by
      have := congrArg (fun y => e' - y) hb
      simpa using this
    rw [smul_eq_zero, polar_smul_right, smul_eq_mul, mul_eq_zero] at h0
    rcases h0 with (h0 | h0) | h0
    · exact toAdd_eq_zero.mp h0
    · exact absurd h0 he'v
    · exact absurd h0 he0
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro b hb
    exact hψe' b (by rw [hb, map_one]; rfl)
  have hHR : ψ.range ≤ R := by
    rintro _ ⟨b, rfl⟩
    exact eichler_mem_flagGroup_levi_one hE hs hTsing hTfix heT hv hev h12 hTO h34 _
  have hR₀H : R₀ ⊓ ψ.range = ⊥ := by
    rw [eq_bot_iff]
    rintro g ⟨hg, b, rfl⟩
    obtain ⟨g', hg', hgg'⟩ := hR₀rad hg
    have hg1 := (mem_flagRadical_iff.mp hg').1 e' he'T
    rw [hψe' b (by rw [← hgg']; exact hg1), map_one]
    exact Subgroup.one_mem _
  have hHcard : Nat.card ψ.range = Nat.card K := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv]
    exact Nat.card_congr Multiplicative.toAdd
  have hcount := card_mul_card_le_card_of_inf_eq_bot hR₀R hHR hR₀H
  refine ⟨R, hR2, inf_le_right, ?_⟩
  calc Nat.card K ^ (m * c + m * (m - 1) / 2 + 1) =
        Nat.card K ^ (m * c + m * (m - 1) / 2) * Nat.card K := pow_succ _ _
    _ ≤ Nat.card R₀ * Nat.card ψ.range := by rw [hHcard]; exact Nat.mul_le_mul_right _ hR₀card
    _ ≤ Nat.card R := hcount

end LeviOne

end CFSG.SeitzReduction.OmegaPilot
