module

public import CFSG.ClassicalInvolution.RouteD.TWEB3QAut
public import CFSG.ClassicalInvolution.ModelFacts.Orth15TwinStd

public section

namespace CFSG.ClassicalInvolution.RouteD.TWE.B3

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.ModelFacts.Orth15
  CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.ModelFacts.OrthAut CFSG.ClassicalInvolution.Balance.StrongBalance.Orth
open scoped MatrixGroups

set_option linter.unusedSectionVars false

section Det

variable {p f : ℕ} [Fact p.Prime]



theorem exists_isometry_sqrt_b3 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {X : Type} [Group X]
    (ψ : spinGroup (quadOdd 3 (GaloisField p f)) →* X)
    (hψ : ψ.ker ≤ Subgroup.center (spinGroup (quadOdd 3 (GaloisField p f))))
    (σ σd : X ≃* X) (hσ2 : ∀ y, σ (σ y) = y) (hσdd : ∀ y, σd (σd y) = σ y)
    (hσr : ∀ k, σ (ψ k) ∈ ψ.range) (hσdr : ∀ k, σd (ψ k) ∈ ψ.range)
    {RM RM' : Subgroup (spinGroup (quadOdd 3 (GaloisField p f)))}
    (FM : OFrame (quadOdd 3 (GaloisField p f)))
    (hFM : RM.map (spinAction (quadOdd 3 (GaloisField p f))) = FM.La.range)
    (hFM' : RM'.map (spinAction (quadOdd 3 (GaloisField p f))) = FM.swap.La.range)
    (hfixM : ∀ y ∈ RM, σd (ψ y) = ψ y) (hfixM' : ∀ y ∈ RM', σd (ψ y) = ψ y) :
    ∃ (h : (Fin 3 ⊕ Fin 3 ⊕ Unit → GaloisField p f) ≃ₗ[GaloisField p f]
        (Fin 3 ⊕ Fin 3 ⊕ Unit → GaloisField p f))
      (αd : spinGroup (quadOdd 3 (GaloisField p f)) ≃* spinGroup (quadOdd 3 (GaloisField p f))),
      h ∈ TauCeti.QuadraticMap.orthogonalGroup (quadOdd 3 (GaloisField p f)) ∧
      (∀ x ∈ FM.span, h x = x) ∧ (∀ y, ψ (αd y) = σd (ψ y)) ∧
      ∀ y z, spinAction (quadOdd 3 (GaloisField p f)) (αd y) (h z) =
        h (spinAction (quadOdd 3 (GaloisField p f)) y z) := by
  classical
  obtain ⟨hf0, hK⟩ := RouteD.card_galoisField_of_four_le (p := p) (f := f) (by omega)
  have he : 1 ≤ f := Nat.one_le_iff_ne_zero.mpr hf0
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2
  have hodd : Odd (Nat.card (GaloisField p f)) := by
    rw [hK]
    exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  have hn3 : 3 ≤ 3 := le_rfl
  have : Group.IsPerfect (spinGroup (quadOdd 3 (GaloisField p f))) :=
    isPerfect_spinGroup_quadOdd h2 hn3
  have hrange := range_spinAction_quadOdd h2 hn3
  have h5 : 5 ≤ Nat.card (GaloisField p f) := five_le_card_galoisField hq
  obtain ⟨σR, hσR⟩ := exists_rangeAut_of_sq ψ σ σd hσ2 hσdd hσr hσdr
  have hfixT : ∀ t ∈ RM ⊔ RM', σR (ψ.rangeRestrict t) = ψ.rangeRestrict t := by
    have hle : RM ⊔ RM' ≤ MonoidHom.eqLocus ((σR : ↥ψ.range →* ↥ψ.range).comp ψ.rangeRestrict)
        ψ.rangeRestrict := by
      refine sup_le (fun r hr => ?_) (fun r hr => ?_)
      · exact Subtype.ext ((hσR (ψ.rangeRestrict r)).trans (hfixM r hr))
      · exact Subtype.ext ((hσR (ψ.rangeRestrict r)).trans (hfixM' r hr))
    exact fun t ht => hle ht
  have hσ : ∀ s : spinGroup (quadOdd 3 (GaloisField p f)),
      spinAction (quadOdd 3 (GaloisField p f)) s ∈ FM.La.range ⊔ FM.swap.La.range →
      ∀ ℓ : ↥ψ.range, σR (ψ.rangeRestrict s * ℓ * (ψ.rangeRestrict s)⁻¹) =
        ψ.rangeRestrict s * σR ℓ * (ψ.rangeRestrict s)⁻¹ := by
    intro s hs
    have hmem : spinAction (quadOdd 3 (GaloisField p f)) s ∈
        (RM ⊔ RM').map (spinAction (quadOdd 3 (GaloisField p f))) := by
      rw [Subgroup.map_sup, hFM, hFM']
      exact hs
    obtain ⟨s₁, hs₁, hs₁s⟩ := hmem
    have hzS : s₁⁻¹ * s ∈ Subgroup.center (spinGroup (quadOdd 3 (GaloisField p f))) :=
      ker_spinAction_le_center (quadOdd 3 (GaloisField p f)) (by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hs₁s, inv_mul_cancel])
    have hsS : s ∈ (RM ⊔ RM') ⊔ Subgroup.center (spinGroup (quadOdd 3 (GaloisField p f))) := by
      have : s = s₁ * (s₁⁻¹ * s) := by group
      rw [this]
      exact Subgroup.mul_mem_sup (show s₁ ∈ RM ⊔ RM' from hs₁) hzS
    exact conj_comm_of_fix ψ σR (RM ⊔ RM') hfixT s hsS
  obtain ⟨αd, a, c, hαdψ, hαdθ, hac, μ, hμ, hQa⟩ := exists_aut_of_centralizing hodd h5 hrange FM
    hψ (liftSim_quadOdd hp2 hn3 he ψ hψ) σR hσ
  have hc0 : c ≠ 0 := by
    intro h0
    apply μ.ne_zero
    rw [hμ, h0]
    ring
  let c₀ : (GaloisField p f)ˣ := Units.mk0 c hc0
  have hc₀ : ((c₀⁻¹ : (GaloisField p f)ˣ) : GaloisField p f) = c⁻¹ := by
    simp [c₀]
  let h : (Fin 3 ⊕ Fin 3 ⊕ Unit → GaloisField p f) ≃ₗ[GaloisField p f]
      (Fin 3 ⊕ Fin 3 ⊕ Unit → GaloisField p f) := a.trans (LinearEquiv.smulOfUnit c₀⁻¹)
  have hh : ∀ v, h v = c⁻¹ • a v := fun v => by rw [← hc₀]; rfl
  have ea : ∀ y z, spinAction (quadOdd 3 (GaloisField p f)) (αd y) (a z) =
      a (spinAction (quadOdd 3 (GaloisField p f)) y z) := by
    intro y z
    have := LinearEquiv.congr_fun (hαdθ y) (a z)
    simpa [LinearEquiv.mul_apply] using this
  refine ⟨h, αd, ?_, fun x hx => ?_, fun x => congrArg Subtype.val (hαdψ x) |>.trans (hσR _),
    fun y z => ?_⟩
  · refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => ?_
    rw [hh, QuadraticMap.map_smul, hQa, hμ, smul_eq_mul]
    field_simp
  · rw [hh, hac x hx, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  · rw [hh, hh, map_smul, ea]

theorem det_of_sq_b3 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {X : Type} [Group X]
    (ψ : spinGroup (quadOdd 3 (GaloisField p f)) →* X)
    (hψ : ψ.ker ≤ Subgroup.center (spinGroup (quadOdd 3 (GaloisField p f))))
    (σ σd : X ≃* X) (hσdd : ∀ y, σd (σd y) = σ y) (FM : OFrame (quadOdd 3 (GaloisField p f)))
    {h : (Fin 3 ⊕ Fin 3 ⊕ Unit → GaloisField p f) ≃ₗ[GaloisField p f]
      (Fin 3 ⊕ Fin 3 ⊕ Unit → GaloisField p f)}
    {αd : spinGroup (quadOdd 3 (GaloisField p f)) ≃* spinGroup (quadOdd 3 (GaloisField p f))}
    (hhO : h ∈ TauCeti.QuadraticMap.orthogonalGroup (quadOdd 3 (GaloisField p f)))
    (hhspan : ∀ x ∈ FM.span, h x = x) (hαdψ' : ∀ y, ψ (αd y) = σd (ψ y))
    (hhconj : ∀ y z, spinAction (quadOdd 3 (GaloisField p f)) (αd y) (h z) =
      h (spinAction (quadOdd 3 (GaloisField p f)) y z))
    (α : spinGroup (quadOdd 3 (GaloisField p f)) ≃* spinGroup (quadOdd 3 (GaloisField p f)))
    (hαψ : ∀ y, ψ (α y) = σ (ψ y))
    {g₀ : (Fin 3 ⊕ Fin 3 ⊕ Unit → GaloisField p f) ≃ₗ[GaloisField p f]
      (Fin 3 ⊕ Fin 3 ⊕ Unit → GaloisField p f)}
    (hgO : g₀ ∈ TauCeti.QuadraticMap.orthogonalGroup (quadOdd 3 (GaloisField p f)))
    (hconj : ∀ y z, spinAction (quadOdd 3 (GaloisField p f)) (α y) (g₀ z) =
      g₀ (spinAction (quadOdd 3 (GaloisField p f)) y z))
    {ε : GaloisField p f} (hε : ε = 1 ∨ ε = -1) (hgε : ∀ x ∈ FM.span, g₀ x = ε • x) :
    ((LinearEquiv.det g₀ : (GaloisField p f)ˣ) : GaloisField p f) = ε := by
  classical
  obtain ⟨hf0, hK⟩ := RouteD.card_galoisField_of_four_le (p := p) (f := f) (by omega)
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2
  have hodd : Odd (Nat.card (GaloisField p f)) := by
    rw [hK]
    exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  have hn3 : 3 ≤ 3 := le_rfl
  have : Group.IsPerfect (spinGroup (quadOdd 3 (GaloisField p f))) :=
    isPerfect_spinGroup_quadOdd h2 hn3
  have hrange := range_spinAction_quadOdd h2 hn3
  have hQ' : (polarBilin (quadOdd 3 (GaloisField p f))).Nondegenerate :=
    nondegenerate_polarBilin_quadOdd 3 _ h2
  have hdim7 : Module.finrank (GaloisField p f) (Fin 3 ⊕ Fin 3 ⊕ Unit → GaloisField p f) = 7 := by
    rw [finrank_odd]
  have hαα : ∀ y, αd (αd y) = α y := by
    have key := eq_of_inv_mul_mem_center (α.toMonoidHom) ((αd.toMonoidHom).comp αd.toMonoidHom)
      (fun x => by
        apply hψ
        rw [MonoidHom.mem_ker]
        change ψ ((αd (αd x))⁻¹ * α x) = 1
        rw [map_mul, map_inv, hαdψ', hαdψ', hσdd, hαψ, inv_mul_cancel])
    exact fun y => DFunLike.congr_fun key y
  have hg₁O : h * h ∈ TauCeti.QuadraticMap.orthogonalGroup (quadOdd 3 (GaloisField p f)) :=
    Subgroup.mul_mem _ hhO hhO
  have hg₁conj : ∀ y z, spinAction (quadOdd 3 (GaloisField p f)) (α y) ((h * h) z) =
      (h * h) (spinAction (quadOdd 3 (GaloisField p f)) y z) := by
    intro y z
    rw [← hαα y]
    show spinAction (quadOdd 3 (GaloisField p f)) (αd (αd y)) (h (h z)) =
      h (h (spinAction (quadOdd 3 (GaloisField p f)) y z))
    rw [hhconj, hhconj]
  have hEO : (h * h)⁻¹ * g₀ ∈ TauCeti.QuadraticMap.orthogonalGroup (quadOdd 3 (GaloisField p f)) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hg₁O) hgO
  have hEcomm : ∀ y z, ((h * h)⁻¹ * g₀) (spinAction (quadOdd 3 (GaloisField p f)) y z) =
      spinAction (quadOdd 3 (GaloisField p f)) y (((h * h)⁻¹ * g₀) z) := by
    intro y z
    have e2 : ∀ w, (h * h)⁻¹ (spinAction (quadOdd 3 (GaloisField p f)) (α y) w) =
        spinAction (quadOdd 3 (GaloisField p f)) y ((h * h)⁻¹ w) := by
      intro w
      have := hg₁conj y ((h * h)⁻¹ w)
      rw [show (h * h) ((h * h)⁻¹ w) = w from (h * h).apply_symm_apply w] at this
      rw [this]
      exact (h * h).symm_apply_apply _
    show (h * h)⁻¹ (g₀ (spinAction (quadOdd 3 (GaloisField p f)) y z)) =
      spinAction (quadOdd 3 (GaloisField p f)) y ((h * h)⁻¹ (g₀ z))
    rw [← hconj y z, e2]
  have hcommE : ∀ h' ∈ elemOn (quadOdd 3 (GaloisField p f)) ⊤,
      ((h * h)⁻¹ * g₀) * h' = h' * ((h * h)⁻¹ * g₀) := by
    intro h' hh'
    have hh'' : h' ∈ (spinAction (quadOdd 3 (GaloisField p f))).range := by
      rw [hrange]
      exact elemOn_le_elementaryGroup hh'
    obtain ⟨y, rfl⟩ := hh''
    exact LinearEquiv.ext fun z => hEcomm y z
  have h3 : 3 ≤ Module.finrank (GaloisField p f)
      ↥(⊤ : Submodule (GaloisField p f) (Fin 3 ⊕ Fin 3 ⊕ Unit → GaloisField p f)) := by
    rw [finrank_top, hdim7]
    norm_num
  obtain ⟨c', hc'⟩ := exists_smul_of_commute_elemOn hodd (polarNondegOn_top hQ') h3 hEO
    (fun x => by simp) hcommE
  obtain ⟨⟨x, hx⟩, hx0⟩ := Module.finrank_pos_iff_exists_ne_zero.mp
    (by rw [FM.finrank_span]; norm_num : 0 < Module.finrank (GaloisField p f) FM.span)
  have hx0' : x ≠ 0 := fun h0 => hx0 (Subtype.ext h0)
  have hg₁x : (h * h) x = x := by
    show h (h x) = x
    rw [hhspan x hx, hhspan x hx]
  have hEx : ((h * h)⁻¹ * g₀) x = ε • x := by
    show (h * h)⁻¹ (g₀ x) = ε • x
    rw [hgε x hx, map_smul]
    congr 1
    exact ((h * h).symm_apply_eq.mpr hg₁x.symm)
  have hcε : c' = ε := by
    have := hc' x Submodule.mem_top
    rw [hEx] at this
    exact (smul_left_injective (GaloisField p f) hx0' this).symm
  have hg₀eq : ∀ v, g₀ v = ε • (h * h) v := by
    intro v
    have h1 := hc' v Submodule.mem_top
    rw [hcε] at h1
    have h4 : g₀ v = (h * h) (ε • v) := by
      have h5' : (h * h)⁻¹ (g₀ v) = ε • v := h1
      rw [← h5']
      exact ((h * h).apply_symm_apply _).symm
    rw [h4, map_smul]
  have hsq : LinearEquiv.det h ^ 2 = 1 := by
    have := TauCeti.QuadraticMap.orthogonalDet_sq hQ'.1 ⟨h, hhO⟩
    simpa [QuadraticMap.orthogonalDet_apply] using this
  have hdet1 : ((LinearEquiv.det (h * h) : (GaloisField p f)ˣ) : GaloisField p f) = 1 := by
    rw [map_mul, ← _root_.sq, hsq, Units.val_one]
  have hlin : (g₀ : (Fin 3 ⊕ Fin 3 ⊕ Unit → GaloisField p f) →ₗ[GaloisField p f]
      (Fin 3 ⊕ Fin 3 ⊕ Unit → GaloisField p f)) =
      ε • ((h * h : (Fin 3 ⊕ Fin 3 ⊕ Unit → GaloisField p f) ≃ₗ[GaloisField p f]
        (Fin 3 ⊕ Fin 3 ⊕ Unit → GaloisField p f)) :
        (Fin 3 ⊕ Fin 3 ⊕ Unit → GaloisField p f) →ₗ[GaloisField p f]
          (Fin 3 ⊕ Fin 3 ⊕ Unit → GaloisField p f)) :=
    LinearMap.ext hg₀eq
  rw [LinearEquiv.coe_det, hlin, LinearMap.det_smul, hdim7, ← LinearEquiv.coe_det, hdet1]
  rcases hε with rfl | rfl <;> norm_num

end Det

end CFSG.ClassicalInvolution.RouteD.TWE.B3
