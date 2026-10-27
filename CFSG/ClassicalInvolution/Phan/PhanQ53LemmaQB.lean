module

public import CFSG.ClassicalInvolution.Phan.PhanQ51Conj

public section

namespace CFSG.ClassicalInvolution.PhanQ

open QuadraticMap CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.PhanP
  CFSG.ClassicalInvolution.PhanD4 CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary CFSG.ClassicalInvolution.Phan

section QB

variable {F K : Type} [Field F] [Field K] [Algebra F K] {ε : F} (D : KData F K ε)

theorem quadPlusForm_β (u v : V8 K) : (quadPlusForm 4 K).polar.β u v = B8 u v := by
  rw [B8_eq_sum]
  rfl

theorem phanSolid_of_lagrangian [Finite K] {W : Submodule K (V8 K)}
    (hL : (quadPlusForm 4 K).IsLagrangian W) (hinf : ∀ v ∈ W, conj D v ∈ W → v = 0) :
    PhanSolid D W := by
  have hW4 : Module.finrank K W = 4 := by
    have : 2 * Module.finrank K W = 8 := hL.2.trans finrank_V8
    omega
  refine ⟨fun u hu v hv => ?_, hinf, ?_⟩
  · have := hL.1.isTotallyIsotropic hv u hu
    rwa [quadPlusForm_β] at this
  · have hc4 : Module.finrank K (conjSub D W) = 4 := by rw [finrank_conjSub, hW4]
    have hdisj : W ⊓ conjSub D W = ⊥ := by
      rw [eq_bot_iff]
      rintro v ⟨hv, hcv⟩
      exact (Submodule.mem_bot K).2 (hinf v hv hcv)
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq W (conjSub D W)
    rw [hdisj, finrank_bot, hW4, hc4] at h1
    have hsup : W ⊔ conjSub D W = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      have h8 : Module.finrank K ↥(W ⊔ conjSub D W) = 8 := by omega
      exact h8.trans finrank_V8.symm
    intro v
    have hv : v ∈ W ⊔ conjSub D W := by rw [hsup]; exact Submodule.mem_top
    obtain ⟨w₁, hw₁, w', hw', rfl⟩ := Submodule.mem_sup.1 hv
    exact ⟨w₁, hw₁, conj D w', hw', by rw [conj_conj]⟩

theorem conj_sub' (v w : V8 K) : conj D (v - w) = conj D v - conj D w := by
  ext i
  simp [conj]

theorem exists_fixed_of_stable (h2 : (2 : K) ≠ 0) (hε : ε ≠ 0) {Z : Submodule K (V8 K)}
    (hZ : ∀ v ∈ Z, conj D v ∈ Z) {v : V8 K} (hv : v ∈ Z) (hv0 : v ≠ 0) :
    ∃ ρ ∈ Z, ρ ≠ 0 ∧ conj D ρ = ρ := by
  have hθ := theta_ne_zero D hε
  by_cases h : v + conj D v = 0
  · refine ⟨D.θ • (v - conj D v), Z.smul_mem _ (Z.sub_mem hv (hZ v hv)), ?_, ?_⟩
    · intro h0
      rcases smul_eq_zero.1 h0 with h1 | h1
      · exact hθ h1
      · apply hv0
        have h3 : v = conj D v := sub_eq_zero.1 h1
        have h4 : (2 : K) • v = 0 := by
          rw [two_smul]
          nth_rewrite 2 [h3]
          exact h
        exact (smul_eq_zero.1 h4).resolve_left h2
    · rw [conj_smul, D.tau_theta, conj_sub', conj_conj, neg_smul, ← smul_neg, neg_sub]
  · refine ⟨v + conj D v, Z.add_mem hv (hZ v hv), h, ?_⟩
    rw [conj_add, conj_conj, add_comm]

theorem exists_phanSolid_of_rad [Finite K] (h2 : (2 : K) ≠ 0) (hε : ε ≠ 0)
    {H : Submodule K (V8 K)} (hts : ∀ u ∈ H, ∀ v ∈ H, B8 u v = 0)
    (hdim : Module.finrank K H = 3) (hinf : ∀ v ∈ H, conj D v ∈ H → v = 0) {r : V8 K}
    (hr : r ∈ H) (hr0 : r ≠ 0) (hrad : ∀ h ∈ H, her D r h = 0) :
    ∃ W, PhanSolid D W ∧ H ≤ W := by
  have hQ8 := quadPlusForm_Q (K := K)
  have hQ : ∀ v ∈ H, Q8 v = 0 := fun v hv => by
    have h1 := hts v hv v hv
    rw [B8_self] at h1
    exact (mul_eq_zero.1 h1).resolve_left h2
  have hQr : Q8 r = 0 := hQ r hr
  have hQcr : Q8 (conj D r) = 0 := by rw [Q8_conj, hQr, map_zero]
  have hcr0 : conj D r ≠ 0 := by
    intro h
    apply hr0
    have := congrArg (conj D) h
    rw [conj_conj] at this
    rw [this]
    ext i
    simp [conj]
  have hind : ∀ α β : K, α • r + β • conj D r = 0 → α = 0 ∧ β = 0 := by
    intro α β h
    have hβ : β = 0 := by
      by_contra hβ
      have h1 : conj D r = (-(α / β)) • r := by
        have : β • conj D r = -(α • r) := eq_neg_of_add_eq_zero_right h
        have h3 : conj D r = β⁻¹ • (β • conj D r) := by rw [smul_smul, inv_mul_cancel₀ hβ, one_smul]
        rw [h3, this, smul_neg, smul_smul, ← neg_smul]
        congr 1
        field_simp
      apply hr0
      exact hinf r hr (by rw [h1]; exact H.smul_mem _ hr)
    refine ⟨?_, hβ⟩
    rw [hβ, zero_smul, add_zero] at h
    exact (smul_eq_zero.1 h).resolve_right hr0
  have hHc3 : Module.finrank K (conjSub D H) = 3 := by rw [finrank_conjSub, hdim]
  have hdisj : H ⊓ conjSub D H = ⊥ := by
    rw [eq_bot_iff]
    rintro v ⟨hv, hcv⟩
    exact (Submodule.mem_bot K).2 (hinf v hv hcv)
  have hN6 : Module.finrank K ↥(H ⊔ conjSub D H) = 6 := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq H (conjSub D H)
    rw [hdisj, finrank_bot, hdim, hHc3] at h1
    omega
  have hperp2 : Module.finrank K ↥((quadPlusForm 4 K).polar.perp (H ⊔ conjSub D H)) = 2 := by
    have h1 : Module.finrank K ↥((quadPlusForm 4 K).polar.perp (H ⊔ conjSub D H)) +
        Module.finrank K ↥(H ⊔ conjSub D H) = 8 :=
      ((quadPlusForm 4 K).polar.finrank_perp (H ⊔ conjSub D H)).trans finrank_V8
    omega
  have e1 : ∀ w ∈ H, B8 w r = 0 := fun w hw => hts w hw r hr
  have e2 : ∀ w ∈ conjSub D H, B8 w r = 0 := by
    intro w hw
    have h1 := B8_conj D (conj D w) (conj D r)
    rw [conj_conj, conj_conj] at h1
    have h3 : B8 (conj D w) (conj D r) = her D (conj D w) r := rfl
    rw [h1, h3, her_conj_symm, hrad _ hw, map_zero, map_zero]
  have e3 : ∀ w ∈ H, B8 w (conj D r) = 0 := by
    intro w hw
    have h3 : B8 w (conj D r) = her D w r := rfl
    rw [h3, her_conj_symm, hrad w hw, map_zero]
  have e4 : ∀ w ∈ conjSub D H, B8 w (conj D r) = 0 := by
    intro w hw
    have h1 := B8_conj D (conj D w) r
    rw [conj_conj] at h1
    rw [h1, hts _ hw r hr, map_zero]
  have hr_perp : r ∈ (quadPlusForm 4 K).polar.perp (H ⊔ conjSub D H) := by
    rw [ReflForm.perp_sup]
    refine ⟨fun w hw => ?_, fun w hw => ?_⟩
    · rw [quadPlusForm_β]; exact e1 w hw
    · rw [quadPlusForm_β]; exact e2 w hw
  have hcr_perp : conj D r ∈ (quadPlusForm 4 K).polar.perp (H ⊔ conjSub D H) := by
    rw [ReflForm.perp_sup]
    refine ⟨fun w hw => ?_, fun w hw => ?_⟩
    · rw [quadPlusForm_β]; exact e3 w hw
    · rw [quadPlusForm_β]; exact e4 w hw
  have hli : LinearIndependent K ![r, conj D r] := LinearIndependent.pair_iff.2 hind
  have hspan2 : Module.finrank K ↥(Submodule.span K {r, conj D r}) = 2 := by
    have h := finrank_span_eq_card hli
    rw [Matrix.range_cons_cons_empty] at h
    simpa using h
  have hspan_le : Submodule.span K {r, conj D r} ≤
      (quadPlusForm 4 K).polar.perp (H ⊔ conjSub D H) := by
    rw [Submodule.span_le]
    intro x hx
    rcases hx with rfl | hx
    · exact hr_perp
    · rw [Set.mem_singleton_iff.1 hx]
      exact hcr_perp
  have hperp_eq : (quadPlusForm 4 K).polar.perp (H ⊔ conjSub D H) =
      Submodule.span K {r, conj D r} :=
    (Submodule.eq_of_le_of_finrank_eq hspan_le (by rw [hspan2, hperp2])).symm
  have hHts : (quadPlusForm 4 K).IsTotallySingular H := fun w hw => by
    rw [hQ8 w]
    exact hQ w hw
  have hcr_perpH : conj D r ∈ (quadPlusForm 4 K).polar.perp H := fun w hw => by
    rw [quadPlusForm_β]
    exact e3 w hw
  have hQcr' : (quadPlusForm 4 K).Q (conj D r) = 0 := by rw [hQ8]; exact hQcr
  have htsP := hHts.sup_span hcr_perpH hQcr'
  have hcr_notin : conj D r ∉ H := fun h => hr0 (hinf r hr h)
  have hWP4 : Module.finrank K ↥(H ⊔ K ∙ conj D r) = 4 := by
    have hd : Disjoint H (K ∙ conj D r) := (Submodule.disjoint_span_singleton' hcr0).2 hcr_notin
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq H (K ∙ conj D r)
    rw [disjoint_iff.1 hd, finrank_bot, hdim, finrank_span_singleton hcr0] at h1
    omega
  have hLP : (quadPlusForm 4 K).IsLagrangian (H ⊔ K ∙ conj D r) :=
    ⟨htsP, by rw [hWP4, finrank_V8]⟩
  obtain ⟨Y, Y', hYY', hY, hY', hHY, hHY', -⟩ := QuadForm.exists_isLagrangian_pair
    (Φ := quadPlusForm 4 K) (n := 4) (by rw [finrank_V8]) (isLagrangian_quadPlusForm 4 K) hHts
    (by rw [hdim])
  have hle_eq : ∀ X : Submodule K (V8 K), (quadPlusForm 4 K).IsLagrangian X → H ≤ X →
      conj D r ∈ X → X = H ⊔ K ∙ conj D r := by
    intro X hX hHX hcX
    have hle : H ⊔ K ∙ conj D r ≤ X :=
      sup_le hHX ((Submodule.span_singleton_le_iff_mem _ _).2 hcX)
    exact (hLP.eq_of_le hX.1 hle).symm
  have hkey : ∀ X : Submodule K (V8 K), (quadPlusForm 4 K).IsLagrangian X → H ≤ X →
      conj D r ∉ X → ∀ v ∈ X, conj D v ∈ X → v = 0 := by
    intro X hX hHX hcrX v hv hcv
    by_contra hv0
    have hXts : ∀ u ∈ X, ∀ w ∈ X, B8 u w = 0 := fun u hu w hw => by
      have := hX.1.isTotallyIsotropic hw u hu
      rwa [quadPlusForm_β] at this
    have hstab : ∀ w ∈ X ⊓ conjSub D X, conj D w ∈ X ⊓ conjSub D X := fun w hw => by
      obtain ⟨hw1, hw2⟩ := Submodule.mem_inf.1 hw
      refine Submodule.mem_inf.2 ⟨(mem_conjSub (D := D)).1 hw2, ?_⟩
      rw [mem_conjSub, conj_conj]
      exact hw1
    obtain ⟨ρ, hρZ, hρ0, hρc⟩ := exists_fixed_of_stable D h2 hε hstab
      (Submodule.mem_inf.2 ⟨hv, (mem_conjSub (D := D)).2 hcv⟩) hv0
    have hρX : ρ ∈ X := (Submodule.mem_inf.1 hρZ).1
    have hρperp : ρ ∈ (quadPlusForm 4 K).polar.perp (H ⊔ conjSub D H) := by
      rw [ReflForm.perp_sup]
      refine ⟨fun w hw => ?_, fun w hw => ?_⟩
      · rw [quadPlusForm_β]
        exact hXts w (hHX hw) ρ hρX
      · have hw' : conj D w ∈ H := hw
        rw [quadPlusForm_β]
        have h1 := B8_conj D (conj D w) (conj D ρ)
        rw [conj_conj, conj_conj, hρc] at h1
        rw [h1, hXts (conj D w) (hHX hw') ρ hρX, map_zero]
    rw [hperp_eq] at hρperp
    obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.1 hρperp
    have hc : conj D (α • r + β • conj D r) = α • r + β • conj D r := by
      rw [hαβ]
      exact hρc
    rw [conj_add, conj_smul, conj_smul, conj_conj] at hc
    have hab := hind (D.τ β - α) (D.τ α - β) (by linear_combination (norm := module) hc)
    have hαβ' : α = D.τ β := by linear_combination -hab.1
    have hβ0 : β ≠ 0 := by
      rintro rfl
      apply hρ0
      rw [← hαβ, hαβ', map_zero, zero_smul, zero_smul, add_zero]
    apply hcrX
    have h3 : conj D r = β⁻¹ • (ρ - α • r) := by
      rw [← hαβ, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hβ0, one_smul]
    rw [h3]
    exact X.smul_mem _ (X.sub_mem hρX (X.smul_mem _ (hHX hr)))
  by_cases hcY : conj D r ∈ Y
  · have hcY' : conj D r ∉ Y' := fun h =>
      hYY' ((hle_eq Y hY hHY hcY).trans (hle_eq Y' hY' hHY' h).symm)
    exact ⟨Y', phanSolid_of_lagrangian D hY' (hkey Y' hY' hHY' hcY'), hHY'⟩
  · exact ⟨Y, phanSolid_of_lagrangian D hY (hkey Y hY hHY hcY), hHY⟩

end QB

end CFSG.ClassicalInvolution.PhanQ
