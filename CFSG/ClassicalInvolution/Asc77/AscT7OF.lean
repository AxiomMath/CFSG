module

public import CFSG.ClassicalInvolution.Asc77.AscT7OE
public import CFSG.ClassicalInvolution.Asc77.AscT7MJ
public import CFSG.ClassicalInvolution.ModelFacts.Orth15D4Lift

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15

namespace T7O

set_option linter.unusedSectionVars false

open CFSG.ClassicalInvolution.G2D4Models.Twin CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalInvolution.Balance.StrongBalance.Orth QuadraticMap CFSG.Assembly.Dichotomy
open scoped MatrixGroups

section Rigid

variable {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F] [Finite F]
  {Q : QuadraticForm F (ι → F)} {H : Type} [Group H] [Finite H]

theorem commute_of_fix_span {fr : Frame Q} {w : (ι → F) ≃ₗ[F] (ι → F)}
    (hwspan : ∀ x ∈ fr.span, w x = x) (hspan_ne : fr.span ≠ ⊥)
    {g : (ι → F) ≃ₗ[F] (ι → F)} (hg : g ∈ elemOn Q fr.perp) {c₀ : F}
    (hc : ∀ x, (w * g * w⁻¹ * g⁻¹) x = c₀ • x) : w * g = g * w := by
  obtain ⟨z₀, hz₀, hz₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hspan_ne
  have hperp : ∀ y ∈ fr.perp, polar Q z₀ y = 0 := fun y hy => polar_perp_of_mem_span fr hz₀ hy
  have hfix : ∀ k ∈ elemOn Q fr.perp, k z₀ = z₀ := fun k hk =>
    (support_of_mem_elemOn hk).2 z₀ hperp
  have hgz : g z₀ = z₀ := hfix g hg
  have hgiz : g⁻¹ z₀ = z₀ := hfix g⁻¹ (inv_mem hg)
  have hwz : w z₀ = z₀ := hwspan z₀ hz₀
  have hwiz : w⁻¹ z₀ = z₀ := by
    apply w.injective
    rw [LinearEquiv.apply_inv_apply', hwz]
  have h1 := hc z₀
  simp only [LinearEquiv.mul_apply] at h1
  rw [hgiz, hwiz, hgz, hwz] at h1
  have hc1 : c₀ = 1 := by
    have : (c₀ - 1) • z₀ = 0 := by rw [sub_smul, ← h1, one_smul, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp this).resolve_right hz₀0)
  have hone : w * g * w⁻¹ * g⁻¹ = 1 := LinearEquiv.ext fun x => by
    rw [hc x, hc1, one_smul]; rfl
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hone
  exact hone

theorem mem_perp_iff_of_fix {fr : Frame Q} {w : (ι → F) ≃ₗ[F] (ι → F)}
    (hwO : w ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hwspan : ∀ x ∈ fr.span, w x = x)
    (x : ι → F) : x ∈ fr.perp ↔ w x ∈ fr.perp := by
  refine ⟨fun hx => map_mem_perp_of_fix fr hwO hwspan hx, fun hx => ?_⟩
  have hwiO : w⁻¹ ∈ TauCeti.QuadraticMap.orthogonalGroup Q := inv_mem hwO
  have hwispan : ∀ y ∈ fr.span, w⁻¹ y = y := fun y hy => by
    apply w.injective
    rw [LinearEquiv.apply_inv_apply', hwspan y hy]
  have := map_mem_perp_of_fix fr hwiO hwispan hx
  rwa [show (w⁻¹ : (ι → F) ≃ₗ[F] (ι → F)) (w x) = x from LinearEquiv.symm_apply_apply w x] at this

theorem oddCore_frame_eq_one (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    (hQ : (polarBilin Q).Nondegenerate) (hrange : (spinAction Q).range = elementaryGroup Q)
    [Group.IsPerfect (spinGroup Q)] (fr : Frame Q) (hV : 7 ≤ Module.finrank F (ι → F))
    {ψ : spinGroup Q →* H} (hψ : ψ.ker ≤ Subgroup.center (spinGroup Q))
    (hlift : LiftSimFr Q ψ) {s₂ : spinGroup Q} (hs₂ : spinAction Q s₂ = fr.La (-1)) :
    ∀ n ∈ involutionOddCore (toInducedAutOn ψ.range ⟨ψ s₂, mem_normalizer_range ψ s₂⟩),
      n = 1 := by
  classical
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card hodd
  have h3 : 3 ≤ Module.finrank F (ι → F) := by omega
  obtain ⟨e, he, hker, hnorm, hcent⟩ := exists_hom_spin hodd hQ h3 hrange ψ hψ
  have : Finite ↥(inducedAutOn ψ.range) := inferInstance
  have := hnorm
  have hzmem : fr.La (-1) ∈ elementaryGroup Q := fr.La_mem_elementaryGroup (-1)
  have hez : e ⟨fr.La (-1), hzmem⟩ =
      toInducedAutOn ψ.range ⟨ψ s₂, mem_normalizer_range ψ s₂⟩ := by
    have := he s₂ (by rw [hs₂]; exact hzmem)
    rw [← this]
    congr 1
    exact Subtype.ext hs₂.symm
  rw [← hez]
  intro n hn
  have hnodd : Odd (orderOf n) := Odd.of_dvd_nat (odd_natCard_involutionOddCore _)
    (Subgroup.orderOf_dvd_natCard _ hn)
  have Dz := layerData_frame hodd h5 hQ fr (by omega) e hker
  have hnP : ∀ p ∈ img e (elemOn Q fr.span ⊔ elemOn Q fr.perp), n * p = p * n :=
    fun p hp => Dz.commutes_of_oddCore hn hp
  have hnE : ∀ g : ↥(elementaryGroup Q),
      (g : (ι → F) ≃ₗ[F] (ι → F)) ∈ elemOn Q fr.span ⊔ elemOn Q fr.perp →
        n * e g = e g * n := fun g hg => hnP (e g) ((mem_img_iff e).mpr ⟨g, hg, rfl⟩)
  set σ : MulAut ↥ψ.range := (n : MulAut ↥ψ.range) with hσdef
  have hLspan : fr.La.range ⊔ fr.swap.La.range ≤ elemOn Q fr.span ⊔ elemOn Q fr.perp := by
    refine sup_le (fun g hg => ?_) (fun g hg => ?_)
    · obtain ⟨A, rfl⟩ := hg
      exact Subgroup.mem_sup_left (La_mem_elemOn fr A)
    · obtain ⟨A, rfl⟩ := hg
      exact Subgroup.mem_sup_left (swap_La_mem_elemOn fr A)
  have hσ : ∀ s : spinGroup Q, spinAction Q s ∈ fr.La.range ⊔ fr.swap.La.range →
      ∀ ℓ : ↥ψ.range, σ (ψ.rangeRestrict s * ℓ * (ψ.rangeRestrict s)⁻¹) =
        ψ.rangeRestrict s * σ ℓ * (ψ.rangeRestrict s)⁻¹ := by
    intro s hs ℓ
    have hm : spinAction Q s ∈ elementaryGroup Q := by rw [← hrange]; exact ⟨s, rfl⟩
    have hc := hnE ⟨spinAction Q s, hm⟩ (hLspan hs)
    rw [he s hm] at hc
    have h := congrArg (fun g : ↥(inducedAutOn ψ.range) => ((g : MulAut ↥ψ.range) ℓ : ↥ψ.range))
      hc
    exact Subtype.ext (congrArg Subtype.val h)
  obtain ⟨α, w, hαψ, hwO, hwspan, hθw⟩ := exists_isometry_of_centralizing_at hodd h5 hrange fr
    hψ σ (hlift fr σ hσ) hσ
  have hconj := conj_e_of_lift e he hrange n α w hαψ hθw
  have hwcomm : ∀ h ∈ elemOn Q fr.perp, w * h = h * w := by
    intro h hh
    have hhE : h ∈ elementaryGroup Q := elemOn_le_elementaryGroup hh
    have hwg : w * h * w⁻¹ ∈ elementaryGroup Q := conj_mem_elementaryGroup hwO hhE
    have h1 := hconj ⟨h, hhE⟩ ⟨w * h * w⁻¹, hwg⟩ rfl
    have hgc : n * e ⟨h, hhE⟩ = e ⟨h, hhE⟩ * n := hnE ⟨h, hhE⟩ (Subgroup.mem_sup_right hh)
    have h2 : e ⟨w * h * w⁻¹, hwg⟩ = e ⟨h, hhE⟩ := by rw [← h1, hgc]; group
    have h3 : e (⟨w * h * w⁻¹, hwg⟩ * (⟨h, hhE⟩ : ↥(elementaryGroup Q))⁻¹) = 1 := by
      rw [map_mul, map_inv, h2, mul_inv_cancel]
    obtain ⟨c₀, hc₀⟩ := mem_scalars.mp (hker _ h3)
    exact commute_of_fix_span hwspan (span_ne_bot fr) hh (c₀ := c₀) (fun x => hc₀ x)
  have hperp3 : 3 ≤ Module.finrank F fr.perp := by
    have := finrank_perp_add_four fr
    omega
  obtain ⟨c, hc⟩ := exists_smul_of_commute_elemOn hodd (polarNondegOn_perp hQ fr) hperp3 hwO
    (mem_perp_iff_of_fix hwO hwspan) hwcomm
  obtain ⟨x₁, hx₁, hQx₁⟩ : ∃ x ∈ fr.perp, Q x ≠ 0 := by
    by_contra hall
    push Not at hall
    obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (perp_ne_bot fr (by omega))
    apply hy0
    refine polarNondegOn_perp hQ fr y hy fun z hz => ?_
    have h1 := hall (y + z) (Submodule.add_mem _ hy hz)
    simp only [QuadraticMap.polar, h1, hall y hy, hall z hz]
    simp
  have hcc : c * c = 1 := by
    have h1 : Q (w x₁) = Q x₁ := (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hwO) x₁
    rw [hc x₁ hx₁, QuadraticMap.map_smul] at h1
    have h2 : (c * c - 1) * Q x₁ = 0 := by
      simp only [smul_eq_mul] at h1
      linear_combination h1
    exact sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_right hQx₁)
  have hwdec : ∀ x : ι → F, w x = fr.incl (fr.coords x) + c • (x - fr.incl (fr.coords x)) := by
    intro x
    obtain ⟨hdec, hr⟩ := decomp_span_perp fr x
    have hs_span : fr.incl (fr.coords x) ∈ fr.span := ⟨_, rfl⟩
    conv_lhs => rw [hdec]
    rw [map_add, hwspan _ hs_span, hc _ hr]
  rcases mul_self_eq_one_iff.mp hcc with hc1 | hc1
  ·
    have hw1 : w = 1 := LinearEquiv.ext fun x => by
      rw [hwdec x, hc1, one_smul]
      change _ = x
      abel
    have hα : (α : spinGroup Q →* spinGroup Q) = MonoidHom.id _ := by
      refine hom_eq_of_central_diff _ _ fun x => ?_
      apply ker_spinAction_le_center Q
      rw [MonoidHom.mem_ker, map_mul, map_inv]
      show (spinAction Q x)⁻¹ * spinAction Q (α x) = 1
      rw [hθw, hw1]
      group
    apply Subtype.ext
    apply MulEquiv.ext
    intro ℓ
    obtain ⟨x, rfl⟩ := ψ.rangeRestrict_surjective ℓ
    have h1 := hαψ x
    have hαx : α x = x := DFunLike.congr_fun hα x
    rw [hαx] at h1
    exact h1.symm
  ·
    have hneg : (LinearEquiv.neg F : (ι → F) ≃ₗ[F] (ι → F)) ∈ scalars F (ι → F) :=
      mem_scalars.mpr ⟨-1, fun v => by simp⟩
    have hw : w = LinearEquiv.neg F * fr.La (-1) := LinearEquiv.ext fun x => by
      rw [hwdec x, hc1, LinearEquiv.mul_apply, LinearEquiv.neg_apply]
      obtain ⟨hdec, hr⟩ := decomp_span_perp fr x
      have hs_span : fr.incl (fr.coords x) ∈ fr.span := ⟨_, rfl⟩
      conv_rhs => rw [hdec]
      rw [map_add, La_neg_one_of_mem_span fr hs_span, La_neg_one_of_mem_perp fr hr]
      simp
      abel
    have hwconj : ∀ g : (ι → F) ≃ₗ[F] (ι → F),
        w * g * w⁻¹ = fr.La (-1) * g * (fr.La (-1))⁻¹ := by
      intro g
      have hcm : ∀ u : (ι → F) ≃ₗ[F] (ι → F), (LinearEquiv.neg F) * u = u * (LinearEquiv.neg F) :=
        fun u => commute_of_mem_scalars hneg u
      rw [hw, mul_inv_rev]
      calc LinearEquiv.neg F * fr.La (-1) * g * ((fr.La (-1))⁻¹ * (LinearEquiv.neg F)⁻¹)
          = LinearEquiv.neg F * (fr.La (-1) * g * (fr.La (-1))⁻¹) * (LinearEquiv.neg F)⁻¹ := by
            group
        _ = (fr.La (-1) * g * (fr.La (-1))⁻¹) * LinearEquiv.neg F * (LinearEquiv.neg F)⁻¹ := by
            rw [hcm]
        _ = fr.La (-1) * g * (fr.La (-1))⁻¹ := by group
    have hα : (α : spinGroup Q →* spinGroup Q) = (MulAut.conj s₂).toMonoidHom := by
      refine hom_eq_of_central_diff _ _ fun x => ?_
      apply ker_spinAction_le_center Q
      rw [MonoidHom.mem_ker, map_mul, map_inv]
      show (spinAction Q (s₂ * x * s₂⁻¹))⁻¹ * spinAction Q (α x) = 1
      rw [hθw, hwconj, map_mul, map_mul, map_inv, hs₂]
      group
    have hnz : n = e ⟨fr.La (-1), hzmem⟩ := by
      rw [hez]
      apply Subtype.ext
      rw [toInducedAutOn_eq_conj]
      apply MulEquiv.ext
      intro ℓ
      obtain ⟨x, rfl⟩ := ψ.rangeRestrict_surjective ℓ
      have hαx : α x = s₂ * x * s₂⁻¹ := DFunLike.congr_fun hα x
      have h2 : (n : MulAut ↥ψ.range) (ψ.rangeRestrict x) =
          ψ.rangeRestrict (s₂ * x * s₂⁻¹) := by
        rw [← hαx]; exact (hαψ x).symm
      change (n : MulAut ↥ψ.range) (ψ.rangeRestrict x) =
        (MulAut.conj (ψ.rangeRestrict s₂)) (ψ.rangeRestrict x)
      rw [h2, MulAut.conj_apply]
      simp
    have hzz : e ⟨fr.La (-1), hzmem⟩ * e ⟨fr.La (-1), hzmem⟩ = 1 := by
      rw [← map_mul]
      have : (⟨fr.La (-1), hzmem⟩ * ⟨fr.La (-1), hzmem⟩ : ↥(elementaryGroup Q)) = 1 :=
        Subtype.ext fr.La_neg_one_mul_self
      rw [this, map_one]
    have hn2 : n * n = 1 := by rw [hnz]; exact hzz
    have hdvd : orderOf n ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hn2)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact orderOf_eq_one_iff.mp h
    · exact absurd (h ▸ hnodd) (Nat.not_odd_iff_even.mpr even_two)

end Rigid

end T7O

end CFSG.ClassicalInvolution.ModelFacts.Orth15
