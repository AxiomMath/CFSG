module

public import CFSG.RankThree.PartOne.KC.UnitaryRigidityMixing

public section

namespace CFSG.LieType.SeitzGeneration.Mixing

open Polynomial Module CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary

variable {ℓ f : ℕ} {K : Type*} [Field K] {hK : UnitaryFieldData ℓ f K} {V : Type*}
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] {B : V →ₛₗ[hK.bar] V →ₗ[K] K}
  {x : LinearMap.GeneralLinearGroup K V}

theorem exists_mixing_element_of_paired (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    (hx : x ∈ sesqUnitaryGroup B) (hsq : Squarefree (minpoly K (x : Module.End K V)))
    {a : primaryFactors (x : Module.End K V)} (hne : (a : K[X]) ≠ dualPoly hK.bar (a : K[X]))
    {u w : V} (hu : u ∈ primaryComponent (x : Module.End K V) (a : K[X]))
    (hw : w ∈ primaryComponent (x : Module.End K V) (a : K[X]))
    (hind : LinearIndependent (AdjoinRoot (a : K[X]))
      ![(⟨u, hu⟩ : primaryComponent (x : Module.End K V) (a : K[X])), ⟨w, hw⟩]) :
    ∃ g : LinearMap.GeneralLinearGroup K V, g ∈ unitaryCentralizer B x ∧
      LinearMap.det (g : Module.End K V) = 1 ∧ (g : Module.End K V) w = w + u := by
  have H : UnitaryPrimaryData hK.bar B x := ⟨hK.bar_bar, hB, hBl, hx, hsq⟩
  obtain ⟨φ, -, hφ1, -, -, hdet⟩ := (pairedPrimaryBlock H a hne).factor
  set W := primaryComponent (x : Module.End K V) (a : K[X]) with hWdef
  set E := AdjoinRoot (a : K[X]) with hEdef
  set u₀ : W := ⟨u, hu⟩ with hu₀
  set w₀ : W := ⟨w, hw⟩ with hw₀
  have hwnot : w₀ ∉ Submodule.span E {u₀} := by
    intro hmem
    obtain ⟨e, he⟩ := Submodule.mem_span_singleton.mp hmem
    have h1 := (LinearIndependent.pair_iff.mp hind) e (-1) (by
      simp only [neg_smul, one_smul]
      rw [he]
      exact add_neg_cancel _)
    exact one_ne_zero (neg_eq_zero.mp h1.2)
  obtain ⟨φ₀, hφ₀w, hφ₀u⟩ := Submodule.exists_le_ker_of_notMem hwnot
  set ψ : Module.Dual E W := (φ₀ w₀)⁻¹ • φ₀ with hψ
  have hψw : ψ w₀ = 1 := by
    rw [hψ, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hφ₀w]
  have hψu : ψ u₀ = 0 := by
    have h1 : φ₀ u₀ = 0 := hφ₀u (Submodule.mem_span_singleton_self u₀)
    rw [hψ, LinearMap.smul_apply, h1, smul_zero]
  let γ₀ : blockGL (x : Module.End K V) (a : K[X]) :=
    LinearMap.GeneralLinearGroup.ofLinearEquiv (LinearEquiv.transvection hψu)
  have hγdet : LinearMap.det ((γ₀ : blockGL (x : Module.End K V) (a : K[X])) :
      Module.End E W) = 1 := by
    have h1 := LinearEquiv.transvection.det_eq_one hψu
    rw [← Units.val_inj, LinearEquiv.coe_det, Units.val_one] at h1
    exact h1
  refine ⟨(φ.symm γ₀ : LinearMap.GeneralLinearGroup K V), (φ.symm γ₀).2.1, ?_, ?_⟩
  · refine hdet (φ.symm γ₀) ?_
    rw [MulEquiv.apply_symm_apply]
    exact hγdet
  · have hg := hφ1 (φ.symm γ₀) w hw
    rw [MulEquiv.apply_symm_apply] at hg
    rw [← hg]
    have hγ : blockApply γ₀ w hw = w + ((ψ w₀ • u₀ : W) : V) := rfl
    rw [hγ, hψw, one_smul]


section Generic

variable {E : Type*} [Field E] {W : Type*} [AddCommGroup W] [Module E W] {bar : E →+* E}

theorem transvection_isometry (Hf : W →ₛₗ[bar] W →ₗ[E] E) (hsymm : ∀ a b, bar (Hf a b) = Hf b a)
    {e : W} {c : E} (he : Hf e e = 0) (hc : bar c = -c) (y z : W) :
    Hf (y + (c * Hf e y) • e) (z + (c * Hf e z) • e) = Hf y z := by
  simp only [map_add, LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, he,
    mul_zero, add_zero, map_mul, hc, ← hsymm e y, RingHom.id_apply]
  ring

theorem exists_anisotropic_of_pairing (Hf : W →ₛₗ[bar] W →ₗ[E] E)
    (hsymm : ∀ a b, bar (Hf a b) = Hf b a) (hbar : ∃ s, bar s ≠ s) (R : Submodule E W)
    {w₀ w₁ : W} (h₀ : w₀ ∈ R) (h₁ : w₁ ∈ R) (hz : Hf w₀ w₁ ≠ 0) :
    ∃ w ∈ R, Hf w w ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have key : ∀ t : E, t + bar t = 0 := by
    intro t
    set z := Hf w₀ w₁ with hzdef
    have h00 := hcon w₀ h₀
    have h11 := hcon w₁ h₁
    have h10 : Hf w₁ w₀ = bar z := (hsymm w₀ w₁).symm
    have hc := hcon (w₀ + (t * z⁻¹) • w₁) (R.add_mem h₀ (R.smul_mem _ h₁))
    have hexp : Hf (w₀ + (t * z⁻¹) • w₁) (w₀ + (t * z⁻¹) • w₁) =
        t * z⁻¹ * z + bar (t * z⁻¹) * bar z := by
      simp only [map_add, LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
        RingHom.id_apply, h00, h11, h10]
      ring
    rw [hexp, ← map_mul, inv_mul_cancel_right₀ hz] at hc
    exact hc
  obtain ⟨s, hs⟩ := hbar
  have h2 : (1 : E) + 1 = 0 := by simpa using key 1
  apply hs
  linear_combination (key s) - s * h2

theorem eq_zero_of_trace_mul_eq_zero {K : Type*} [Field K] [Finite K] (h : K[X])
    [Fact (Irreducible h)] (z : AdjoinRoot h)
    (hz : ∀ c : AdjoinRoot h, Algebra.trace K (AdjoinRoot h) (c * z) = 0) : z = 0 := by
  have : FiniteDimensional K (AdjoinRoot h) :=
    (AdjoinRoot.powerBasis (Fact.out : Irreducible h).ne_zero).finite
  have hnd := traceForm_nondegenerate K (AdjoinRoot h)
  refine hnd.2 z fun c => ?_
  rw [Algebra.traceForm_apply]
  exact hz c

end Generic

section SelfDual

omit [FiniteDimensional K V] in
theorem coe_smul_mem_of_stable {T : Module.End K V} {a : K[X]} {Sub : Submodule K V}
    (hstab : ∀ s ∈ Sub, T s ∈ Sub) (c : AdjoinRoot a) (v : primaryComponent T a)
    (hv : (v : V) ∈ Sub) : ((c • v : primaryComponent T a) : V) ∈ Sub := by
  obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective c
  rw [coe_mk_smul_primaryComponent]
  exact KCUnitaryMixing.aeval_apply_mem hstab g hv

theorem apply_of_supported (hsq : Squarefree (minpoly K (x : Module.End K V)))
    {g : LinearMap.GeneralLinearGroup K V} {a : K[X]}
    (ha : a ∈ primaryFactors (x : Module.End K V)) (hg : g ∈ supportedUnitary B x {a}) (v : V) :
    (g : Module.End K V) v = v +
      ((g : Module.End K V) (primaryProjection (x : Module.End K V) a v) -
        primaryProjection (x : Module.End K V) a v) := by
  classical
  have hsum := LinearMap.congr_fun (sum_primaryProjection hsq) v
  rw [LinearMap.sum_apply, ← Finset.add_sum_erase _ _ ha] at hsum
  simp only [Module.End.one_apply] at hsum
  have hrest : ∑ b ∈ (primaryFactors (x : Module.End K V)).erase a,
      primaryProjection (x : Module.End K V) b v =
        v - primaryProjection (x : Module.End K V) a v := by
    rw [eq_sub_iff_add_eq, add_comm]
    exact hsum
  have hgv : (g : Module.End K V) v =
      (g : Module.End K V) (primaryProjection (x : Module.End K V) a v) +
      ∑ b ∈ (primaryFactors (x : Module.End K V)).erase a,
        (g : Module.End K V) (primaryProjection (x : Module.End K V) b v) := by
    conv_lhs => rw [← hsum]
    rw [map_add, map_sum]
  have hfix : ∀ b ∈ (primaryFactors (x : Module.End K V)).erase a,
      (g : Module.End K V) (primaryProjection (x : Module.End K V) b v) =
        primaryProjection (x : Module.End K V) b v := by
    intro b hb
    obtain ⟨hba, hbm⟩ := Finset.mem_erase.mp hb
    exact hg.2 b hbm (by simpa using hba) _ (primaryProjection_mem hsq hbm v)
  rw [hgv, Finset.sum_congr rfl hfix, hrest]
  abel

theorem exists_mixing_element_of_selfDual (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    (hx : x ∈ sesqUnitaryGroup B) (hsq : Squarefree (minpoly K (x : Module.End K V)))
    {a : primaryFactors (x : Module.End K V)} (hself : dualPoly hK.bar (a : K[X]) = a)
    (hdeg : 2 ≤ (a : K[X]).natDegree) {S₁ S₂ : Submodule K V}
    (hS₁ : ∀ s ∈ S₁, (x : Module.End K V) s ∈ S₁) (hS₂ : ∀ s ∈ S₂, (x : Module.End K V) s ∈ S₂)
    (horth : ∀ s ∈ S₁, ∀ t ∈ S₂, B s t = 0) (hnd₁ : (B.domRestrict₁₂ S₁ S₁).SeparatingLeft)
    (hnd₂ : (B.domRestrict₁₂ S₂ S₂).SeparatingLeft)
    (hKI : ∀ w ∈ S₂, w ≠ 0 → ∃ w₀ ∈ S₂, B w₀ w₀ = 0 ∧ B w w₀ ≠ 0)
    {u w : V} (hu : u ∈ S₁) (hua : u ∈ primaryComponent (x : Module.End K V) (a : K[X]))
    (hu0 : u ≠ 0) (hw : w ∈ S₂) (hwa : w ∈ primaryComponent (x : Module.End K V) (a : K[X]))
    (hw0 : w ≠ 0) :
    ∃ g : LinearMap.GeneralLinearGroup K V, g ∈ unitaryCentralizer B x ∧
      LinearMap.det (g : Module.End K V) = 1 ∧ ∃ w₀ ∈ S₂, w₀ ≠ 0 ∧ B w₀ w₀ = 0 ∧
        ∃ u'' ∈ S₁, ∃ w'' ∈ S₂, u'' ≠ 0 ∧ w'' ≠ 0 ∧ (g : Module.End K V) w₀ = u'' + w'' := by
  classical
  have := hK.finite
  have H : UnitaryPrimaryData hK.bar B x := ⟨hK.bar_bar, hB, hBl, hx, hsq⟩
  obtain ⟨hodd, hE, hbarE, hadj, Hf, hsymmF, hsep, htrace, -, φ, hφ1, hφdet⟩ :=
    selfDualPrimaryBlock H a hself
  have haX : (a : K[X]) ∈ primaryFactors (x : Module.End K V) := a.2
  have hsymm : ∀ s t : primaryComponent (x : Module.End K V) (a : K[X]),
      hE.bar (Hf s t) = Hf t s := fun s t => hsymmF.eq s t
  have hbarne : ∃ s : AdjoinRoot (a : K[X]), hE.bar s ≠ s := hE.exists_bar_ne
  have hεa : primaryProjection (x : Module.End K V) (a : K[X]) =
      primaryProjection (x : Module.End K V) (dualPoly hK.bar (a : K[X])) := by
    rw [hself]
  have hεadj : ∀ v t : V, B (primaryProjection (x : Module.End K V) (a : K[X]) v) t =
      B v (primaryProjection (x : Module.End K V) (a : K[X]) t) := by
    intro v t
    rw [H.adj_spec, adj_primaryProjection H haX, ← hεa]
  have hBtr : ∀ s t : primaryComponent (x : Module.End K V) (a : K[X]),
      B (s : V) (t : V) = Algebra.trace K (AdjoinRoot (a : K[X])) (Hf s t) := fun s t => by
    simpa using (htrace s t 1).symm
  have hHorth : ∀ s t : primaryComponent (x : Module.End K V) (a : K[X]), (s : V) ∈ S₁ →
      (t : V) ∈ S₂ → Hf s t = 0 := by
    intro s t hs ht
    refine eq_zero_of_trace_mul_eq_zero (a : K[X]) (Hf s t) fun c => ?_
    rw [htrace s t c]
    exact horth _ hs _ (coe_smul_mem_of_stable hS₂ c t ht)
  have hex : ∀ S : Submodule K V, (∀ s ∈ S, (x : Module.End K V) s ∈ S) →
      (B.domRestrict₁₂ S S).SeparatingLeft →
      ∀ v : primaryComponent (x : Module.End K V) (a : K[X]), (v : V) ∈ S → v ≠ 0 →
        ∃ z : primaryComponent (x : Module.End K V) (a : K[X]), (z : V) ∈ S ∧ Hf z z ≠ 0 := by
    intro S hS hnd v hvS hv0
    obtain ⟨s, hs, hBs⟩ : ∃ s ∈ S, B (v : V) s ≠ 0 := by
      by_contra hcon
      push Not at hcon
      refine hv0 (Subtype.ext ?_)
      have := hnd ⟨(v : V), hvS⟩ (fun y => by
        rw [LinearMap.domRestrict₁₂_apply]
        exact hcon y y.2)
      have h0 : ((⟨(v : V), hvS⟩ : S) : V) = ((0 : S) : V) := congrArg Subtype.val this
      simpa using h0
    set y₁ : primaryComponent (x : Module.End K V) (a : K[X]) :=
      ⟨primaryProjection (x : Module.End K V) (a : K[X]) s,
        primaryProjection_mem hsq haX s⟩ with hy₁
    have hy₁S : (y₁ : V) ∈ S := KCUnitaryMixing.aeval_apply_mem hS _ hs
    have h1 : B (y₁ : V) (v : V) = B s (v : V) := by
      rw [hy₁]
      change B (primaryProjection (x : Module.End K V) (a : K[X]) s) (v : V) = _
      rw [hεadj, primaryProjection_of_mem hsq haX v.2]
    have h2 : B (v : V) (y₁ : V) = B (v : V) s := by
      rw [← hB.eq, h1, hB.eq]
    have hz : Hf v y₁ ≠ 0 := by
      intro h0
      apply hBs
      rw [← h2, hBtr, h0, map_zero]
    exact exists_anisotropic_of_pairing Hf hsymm hbarne
      { carrier := {z | (z : V) ∈ S}
        add_mem' := fun {a b} ha hb => S.add_mem ha hb
        zero_mem' := S.zero_mem
        smul_mem' := fun c z hz => coe_smul_mem_of_stable hS c z hz } hvS hy₁S hz
  obtain ⟨z₁, hz₁S, hz₁⟩ := hex S₁ hS₁ hnd₁ ⟨u, hua⟩ hu
    (fun h => hu0 (by simpa using congrArg Subtype.val h))
  obtain ⟨z₂, hz₂S, hz₂⟩ := hex S₂ hS₂ hnd₂ ⟨w, hwa⟩ hw
    (fun h => hw0 (by simpa using congrArg Subtype.val h))
  have hz₁0 : z₁ ≠ 0 := fun h => hz₁ (by rw [h]; simp)
  have hz₂0 : z₂ ≠ 0 := fun h => hz₂ (by rw [h]; simp)
  have ht₁ : hE.bar (Hf z₁ z₁) = Hf z₁ z₁ := hsymm z₁ z₁
  have ht₂ : hE.bar (Hf z₂ z₂) = Hf z₂ z₂ := hsymm z₂ z₂
  have hmem : (-(Hf z₂ z₂) / Hf z₁ z₁ : AdjoinRoot (a : K[X])) ∈ hE.fixedField := by
    rw [hE.mem_fixedField, map_div₀, map_neg, ht₁, ht₂]
  obtain ⟨lam, hlam⟩ := hE.normHom_surjective ⟨_, hmem⟩
  have hlam' : lam * hE.bar lam = -(Hf z₂ z₂) / Hf z₁ z₁ := by
    have := congrArg Subtype.val hlam
    simpa [UnitaryFieldData.norm] using this
  have hlam0 : lam ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hlam'
    exact (div_ne_zero (neg_ne_zero.mpr hz₂) hz₁) hlam'.symm
  have hnorm : Hf (lam • z₁) (lam • z₁) = -(Hf z₂ z₂) := by
    simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
    calc lam * (hE.bar lam * Hf z₁ z₁) = (lam * hE.bar lam) * Hf z₁ z₁ := by ring
      _ = -(Hf z₂ z₂) := by rw [hlam']; field_simp
  have hlz₁S : ((lam • z₁ : primaryComponent (x : Module.End K V) (a : K[X])) : V) ∈ S₁ :=
    coe_smul_mem_of_stable hS₁ lam z₁ hz₁S
  have hH12 : Hf (lam • z₁) z₂ = 0 := hHorth _ _ hlz₁S hz₂S
  have hH21 : Hf z₂ (lam • z₁) = 0 := by
    rw [← hsymm, hH12, map_zero]
  have hee : Hf (lam • z₁ + z₂) (lam • z₁ + z₂) = 0 := by
    simp only [map_add, LinearMap.add_apply, hnorm, hH12, hH21]
    ring
  have hz₂V : (z₂ : V) ≠ 0 := fun h => hz₂0 (Subtype.ext h)
  obtain ⟨w₀, hw₀S, hw₀i, hBw₀⟩ := hKI (z₂ : V) hz₂S hz₂V
  set ω : primaryComponent (x : Module.End K V) (a : K[X]) :=
    ⟨primaryProjection (x : Module.End K V) (a : K[X]) w₀, primaryProjection_mem hsq haX w₀⟩
    with hω
  have hωS : (ω : V) ∈ S₂ := KCUnitaryMixing.aeval_apply_mem hS₂ _ hw₀S
  have hBω : B (z₂ : V) (ω : V) = B (z₂ : V) w₀ := by
    rw [hω]
    change B (z₂ : V) (primaryProjection (x : Module.End K V) (a : K[X]) w₀) = _
    rw [← hεadj, primaryProjection_of_mem hsq haX z₂.2]
  have hh₀ : Hf z₂ ω ≠ 0 := by
    intro h0
    apply hBw₀
    rw [← hBω, hBtr, h0, map_zero]
  have hH1ω : Hf (lam • z₁) ω = 0 := hHorth _ _ hlz₁S hωS
  have hHeω : Hf (lam • z₁ + z₂) ω = Hf z₂ ω := by
    rw [map_add, LinearMap.add_apply, hH1ω, zero_add]
  have hc : ∃ c₁ c₂ : AdjoinRoot (a : K[X]), hE.bar c₁ = -c₁ ∧ hE.bar c₂ = -c₂ ∧ c₁ ≠ 0 ∧
      c₂ ≠ 0 ∧ c₁ ≠ c₂ := by
    have := hE.finite
    have hq : 3 ≤ ℓ ^ (f * (a : K[X]).natDegree) := by
      have hℓ2 := hK.prime.two_le
      have hf1 := hK.one_le
      calc 3 ≤ 2 ^ 2 := by norm_num
        _ ≤ ℓ ^ 2 := Nat.pow_le_pow_left hℓ2 2
        _ ≤ ℓ ^ (f * (a : K[X]).natDegree) :=
          Nat.pow_le_pow_right (by omega) (by nlinarith)
    have hcard : 2 < (hE.traceZero : Set (AdjoinRoot (a : K[X]))).ncard := by
      rw [← Nat.card_coe_set_eq]
      change 2 < Nat.card hE.traceZero
      rw [hE.card_traceZero]
      omega
    obtain ⟨c₁, c₂, c₃, h₁, h₂, h₃, h12, h13, h23⟩ :=
      (Set.two_lt_ncard_iff (Set.toFinite _)).1 hcard
    have hbar : ∀ c ∈ hE.traceZero, hE.bar c = -c := fun c hc => by
      have := hE.mem_traceZero.mp hc
      rw [UnitaryFieldData.trace] at this
      linear_combination this
    by_cases h0₁ : c₁ = 0
    · exact ⟨c₂, c₃, hbar _ h₂, hbar _ h₃, fun h => h12 (h0₁.trans h.symm),
        fun h => h13 (h0₁.trans h.symm), h23⟩
    · by_cases h0₂ : c₂ = 0
      · exact ⟨c₁, c₃, hbar _ h₁, hbar _ h₃, h0₁, fun h => h23 (h0₂.trans h.symm), h13⟩
      · exact ⟨c₁, c₂, hbar _ h₁, hbar _ h₂, h0₁, h0₂, h12⟩
  obtain ⟨c₁, c₂, hc₁, hc₂, hc₁0, hc₂0, hc12⟩ := hc
  have hw₀0 : w₀ ≠ 0 := by
    rintro rfl
    exact hBw₀ (by simp)
  have hmain : ∀ c : AdjoinRoot (a : K[X]), hE.bar c = -c → ∃ g : LinearMap.GeneralLinearGroup K V,
      g ∈ unitaryCentralizer B x ∧ LinearMap.det (g : Module.End K V) = 1 ∧
        (g : Module.End K V) w₀ = w₀ +
          (((c * Hf z₂ ω) • (lam • z₁ + z₂) : primaryComponent (x : Module.End K V) (a : K[X])) :
            V) := by
    intro c hc
    have hfv : (c • Hf (lam • z₁ + z₂)) (lam • z₁ + z₂) = 0 := by
      rw [LinearMap.smul_apply, hee, smul_zero]
    let γ : primaryComponent (x : Module.End K V) (a : K[X]) ≃ₗ[AdjoinRoot (a : K[X])]
        primaryComponent (x : Module.End K V) (a : K[X]) := LinearEquiv.transvection hfv
    have hγapply : ∀ y, γ y = y + (c * Hf (lam • z₁ + z₂) y) • (lam • z₁ + z₂) := fun y => rfl
    have hγiso : ∀ y z, Hf (γ y) (γ z) = Hf y z := fun y z => by
      rw [hγapply, hγapply]
      exact transvection_isometry Hf hsymm hee hc y z
    let γg : blockGL (x : Module.End K V) (a : K[X]) :=
      LinearMap.GeneralLinearGroup.ofLinearEquiv γ
    have hγmem : γg ∈ sesqUnitaryGroup Hf := fun y z => hγiso y z
    have hγdet : LinearMap.det ((γg : blockGL (x : Module.End K V) (a : K[X])) :
        Module.End (AdjoinRoot (a : K[X])) (primaryComponent (x : Module.End K V) (a : K[X]))) =
        1 := by
      have h1 := LinearEquiv.transvection.det_eq_one hfv
      rw [← Units.val_inj, LinearEquiv.coe_det, Units.val_one] at h1
      exact h1
    have hγspec : γg ∈ sesqSpecialUnitaryGroup Hf := mem_sesqSpecialUnitaryGroup.mpr ⟨hγmem, hγdet⟩
    set g := φ.symm ⟨γg, hγmem⟩ with hg
    refine ⟨(g : LinearMap.GeneralLinearGroup K V), g.2.1, hφdet g ?_, ?_⟩
    · rw [hg, MulEquiv.apply_symm_apply]
      exact hγspec
    · have h1 := apply_of_supported hsq haX g.2 w₀
      have h3 := hφ1 g (primaryProjection (x : Module.End K V) (a : K[X]) w₀)
        (primaryProjection_mem hsq haX w₀)
      have h4 : φ g = ⟨γg, hγmem⟩ := by rw [hg, MulEquiv.apply_symm_apply]
      rw [h4] at h3
      have h5 : ((γ ω : primaryComponent (x : Module.End K V) (a : K[X])) : V) =
          ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V)
            (primaryProjection (x : Module.End K V) (a : K[X]) w₀) := h3
      rw [h1, ← h5, hγapply, hHeω]
      change w₀ + (((ω + (c * Hf z₂ ω) • (lam • z₁ + z₂) :
        primaryComponent (x : Module.End K V) (a : K[X])) : V) - (ω : V)) = _
      rw [Submodule.coe_add]
      abel
  have hpart : ∀ c : AdjoinRoot (a : K[X]), c ≠ 0 →
      (((c * Hf z₂ ω) • (lam • z₁) : primaryComponent (x : Module.End K V) (a : K[X])) : V) ∈ S₁ ∧
      (((c * Hf z₂ ω) • (lam • z₁) : primaryComponent (x : Module.End K V) (a : K[X])) : V) ≠ 0 ∧
      (((c * Hf z₂ ω) • z₂ : primaryComponent (x : Module.End K V) (a : K[X])) : V) ∈ S₂ := by
    intro c hc0
    refine ⟨coe_smul_mem_of_stable hS₁ _ _ hlz₁S, fun h => ?_,
      coe_smul_mem_of_stable hS₂ _ _ hz₂S⟩
    exact smul_ne_zero (mul_ne_zero hc0 hh₀) (smul_ne_zero hlam0 hz₁0) (Subtype.ext h)
  have hsplit : ∀ c : AdjoinRoot (a : K[X]),
      (((c * Hf z₂ ω) • (lam • z₁ + z₂) : primaryComponent (x : Module.End K V) (a : K[X])) : V) =
        (((c * Hf z₂ ω) • (lam • z₁) : primaryComponent (x : Module.End K V) (a : K[X])) : V) +
        (((c * Hf z₂ ω) • z₂ : primaryComponent (x : Module.End K V) (a : K[X])) : V) := by
    intro c
    rw [smul_add, Submodule.coe_add]
  have hfin : ∀ c : AdjoinRoot (a : K[X]), hE.bar c = -c → c ≠ 0 →
      w₀ + (((c * Hf z₂ ω) • z₂ : primaryComponent (x : Module.End K V) (a : K[X])) : V) ≠ 0 →
      ∃ g : LinearMap.GeneralLinearGroup K V, g ∈ unitaryCentralizer B x ∧
        LinearMap.det (g : Module.End K V) = 1 ∧ ∃ w₀ ∈ S₂, w₀ ≠ 0 ∧ B w₀ w₀ = 0 ∧
          ∃ u'' ∈ S₁, ∃ w'' ∈ S₂, u'' ≠ 0 ∧ w'' ≠ 0 ∧
            (g : Module.End K V) w₀ = u'' + w'' := by
    intro c hc hc0 hne
    obtain ⟨g, hg1, hg2, hg3⟩ := hmain c hc
    obtain ⟨hp1, hp2, hp3⟩ := hpart c hc0
    refine ⟨g, hg1, hg2, w₀, hw₀S, hw₀0, hw₀i, _, hp1, w₀ + _, S₂.add_mem hw₀S hp3, hp2, hne, ?_⟩
    rw [hg3, hsplit]
    abel
  by_cases h1 : w₀ + (((c₁ * Hf z₂ ω) • z₂ : primaryComponent (x : Module.End K V) (a : K[X])) :
      V) = 0
  · by_cases h2 : w₀ + (((c₂ * Hf z₂ ω) • z₂ : primaryComponent (x : Module.End K V) (a : K[X])) :
        V) = 0
    · exfalso
      have e1 := eq_neg_of_add_eq_zero_right h1
      have e2 := eq_neg_of_add_eq_zero_right h2
      have h0 : (((c₁ - c₂) * Hf z₂ ω) • z₂ : primaryComponent (x : Module.End K V) (a : K[X])) =
          0 := by
        apply Subtype.ext
        rw [sub_mul, sub_smul, Submodule.coe_sub, e1, e2, sub_self]
        rfl
      exact smul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hc12) hh₀) hz₂0 h0
    · exact hfin c₂ hc₂ hc₂0 h2
  · exact hfin c₁ hc₁ hc₁0 h1

theorem exists_mixing_element (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    (hx : x ∈ sesqUnitaryGroup B) (hsq : Squarefree (minpoly K (x : Module.End K V)))
    {a : primaryFactors (x : Module.End K V)}
    (hdeg : dualPoly hK.bar (a : K[X]) = a → 2 ≤ (a : K[X]).natDegree) {S₁ S₂ : Submodule K V}
    (hS₁ : ∀ s ∈ S₁, (x : Module.End K V) s ∈ S₁) (hS₂ : ∀ s ∈ S₂, (x : Module.End K V) s ∈ S₂)
    (hdisj : Disjoint S₁ S₂) (horth : ∀ s ∈ S₁, ∀ t ∈ S₂, B s t = 0)
    (hnd₁ : (B.domRestrict₁₂ S₁ S₁).SeparatingLeft)
    (hnd₂ : (B.domRestrict₁₂ S₂ S₂).SeparatingLeft)
    (hKI : ∀ w ∈ S₂, w ≠ 0 → ∃ w₀ ∈ S₂, B w₀ w₀ = 0 ∧ B w w₀ ≠ 0)
    {u w : V} (hu : u ∈ S₁) (hua : u ∈ primaryComponent (x : Module.End K V) (a : K[X]))
    (hu0 : u ≠ 0) (hw : w ∈ S₂) (hwa : w ∈ primaryComponent (x : Module.End K V) (a : K[X]))
    (hw0 : w ≠ 0) :
    ∃ g : LinearMap.GeneralLinearGroup K V, g ∈ unitaryCentralizer B x ∧
      LinearMap.det (g : Module.End K V) = 1 ∧ ∃ w₀ ∈ S₂, w₀ ≠ 0 ∧ B w₀ w₀ = 0 ∧
        ∃ u'' ∈ S₁, ∃ w'' ∈ S₂, u'' ≠ 0 ∧ w'' ≠ 0 ∧ (g : Module.End K V) w₀ = u'' + w'' := by
  by_cases hself : dualPoly hK.bar (a : K[X]) = a
  · exact exists_mixing_element_of_selfDual hB hBl hx hsq hself (hdeg hself) hS₁ hS₂ horth hnd₁
      hnd₂ hKI hu hua hu0 hw hwa hw0
  · have H : UnitaryPrimaryData hK.bar B x := ⟨hK.bar_bar, hB, hBl, hx, hsq⟩
    have hne : (a : K[X]) ≠ dualPoly hK.bar (a : K[X]) := fun h => hself h.symm
    have : Fact (Irreducible (a : K[X])) := ⟨irreducible_of_mem_primaryFactors a.2⟩
    have hind := KCUnitaryMixing.linearIndependent_pair_of_disjoint (a := (a : K[X]))
      hS₁ hS₂ hdisj hu hw hua hwa hu0 hw0
    obtain ⟨g, hg1, hg2, hg3⟩ := exists_mixing_element_of_paired hB hBl hx hsq hne hua hwa hind
    have hwi : B w w = 0 := (pairedPrimaryBlock H a hne).isotropic_left w hwa w hwa
    exact ⟨g, hg1, hg2, w, hw, hw0, hwi, u, hu, w, hw, hu0, hw0, hg3.trans (add_comm w u)⟩

end SelfDual

end CFSG.LieType.SeitzGeneration.Mixing
