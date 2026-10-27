module

public import CFSG.LieType.BorelTits.FormFlag

public section

namespace CFSG.LieType.BorelTits

namespace ReflForm

variable {K : Type*} {V : Type*} [Field K] [AddCommGroup V] [Module K V] (F : ReflForm K V)

theorem absolute_of_σ_eq_one (hσ : F.σ = RingEquiv.refl K) {u w : V} (hu : F.β u u = 0)
    (hw : F.β w w = 0) :
    (∀ a : K, F.β (a • u + w) (a • u + w) = 0) ∨
      ∀ a : K, a ≠ 0 → F.β (a • u + w) (a • u + w) ≠ 0 := by
  have hcalc : ∀ a : K, F.β (a • u + w) (a • u + w) =
      a * (F.β u w + F.β w u) := by
    intro a
    calc
      F.β (a • u + w) (a • u + w) =
          F.β (a • u) (a • u + w) + F.β w (a • u + w) := F.add_left _ _ _
      _ = F.σ a * F.β u (a • u + w) + F.β w (a • u + w) := by
        rw [F.smul_left]
      _ = F.σ a * F.β u (a • u + w) + F.σ 1 * F.β w (a • u + w) := by
        conv_lhs => rw [show F.β w (a • u + w) = F.σ 1 * F.β w (a • u + w) by
          simpa using F.smul_left (1 : K) w (a • u + w)]
      _ = F.σ a * (F.β u (a • u) + F.β u w) +
            F.σ 1 * (F.β w (a • u) + F.β w w) := by rw [F.add_right, F.add_right]
      _ = F.σ a * (a * F.β u u + F.β u w) +
            F.σ 1 * (a * F.β w u + F.β w w) := by rw [F.smul_right, F.smul_right]
      _ = a * (F.β u w + F.β w u) := by
        rw [hσ, hu, hw]
        simp
        ring
  by_cases hc : F.β u w + F.β w u = 0
  · left
    intro a
    rw [hcalc a, hc, mul_zero]
  · right
    intro a ha
    rw [hcalc a]
    exact mul_ne_zero ha hc

@[expose] def revDual (u : V) : Module.Dual K V where
  toFun v := F.σ.symm (F.β v u)
  map_add' v v' := by simp [F.add_left]
  map_smul' c v := by
    rw [F.smul_left]
    simp [map_mul, smul_eq_mul]

theorem ker_revDual (u : V) : LinearMap.ker (revDual F u) = LinearMap.ker (F.toDual u) := by
  ext v
  change F.σ.symm (F.β v u) = 0 ↔ F.β u v = 0
  constructor
  · intro h
    exact F.refl v u (by simpa using congrArg F.σ h)
  · intro h
    rw [F.refl u v h, map_zero]

theorem revDual_add (u u' : V) : revDual F (u + u') = revDual F u + revDual F u' := by
  ext v
  simp [revDual, F.add_right]

section FiniteDimensional

variable [FiniteDimensional K V]

theorem exists_lam {u : V} (hu : u ≠ 0) :
    ∃ l : K, revDual F u = F.σ.symm l • F.toDual u := by
  have hspan : revDual F u ∈ Submodule.span K (Set.range (fun _ : Unit => F.toDual u)) := by
    refine _root_.mem_span_of_iInf_ker_le_ker (L := fun _ : Unit => F.toDual u) ?_
    simpa using (ker_revDual F u).ge
  have hspan' : revDual F u ∈ K ∙ F.toDual u := by simpa using hspan
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hspan'
  exact ⟨F.σ c, by simpa using hc.symm⟩

@[expose] noncomputable def lam (u : V) (hu : u ≠ 0) : K :=
  Classical.choose (exists_lam F hu)

theorem revDual_eq_smul_lam {u : V} (hu : u ≠ 0) :
    revDual F u = F.σ.symm (lam F u hu) • F.toDual u :=
  Classical.choose_spec (exists_lam F hu)

theorem β_eq_lam {u : V} (hu : u ≠ 0) (v : V) :
    F.β v u = lam F u hu * F.σ (F.β u v) := by
  have h := congrArg (fun φ : Module.Dual K V => φ v) (revDual_eq_smul_lam F hu)
  simp only [revDual, LinearMap.smul_apply, smul_eq_mul, F.toDual_apply] at h
  have h' := congrArg F.σ h
  simpa [map_mul] using h'

theorem lam_ne_zero {u : V} (hu : u ≠ 0) : lam F u hu ≠ 0 := by
  intro h0
  apply hu
  apply F.nondeg u
  intro v
  have h := β_eq_lam F hu v
  rw [h0, zero_mul] at h
  exact F.refl v u h

theorem lam_eq_of_independent {u u' : V} (hu : u ≠ 0) (hu' : u' ≠ 0)
    (hind : ∀ c : K, c • u ≠ u') : lam F u hu = lam F u' hu' := by
  have hfu : F.toDual u ≠ 0 := by
    intro h
    apply hu
    apply F.nondeg u
    intro v
    have := congrArg (fun φ : Module.Dual K V => φ v) h
    simpa using this
  have hpair : LinearIndependent K ![F.toDual u, F.toDual u'] := by
    rw [LinearIndependent.pair_iff' hfu]
    intro c hc
    refine hind (F.σ.symm c) ?_
    have hc' : F.toDual (F.σ.symm c • u) = F.toDual u' := by
      rw [map_smulₛₗ]
      simpa using hc
    exact F.toDual_injective hc'
  have hsum : u + u' ≠ 0 := by
    intro h
    apply hind (-1)
    rw [neg_one_smul]
    have hcomm : u' + u = 0 := by rwa [add_comm] at h
    exact (eq_neg_of_add_eq_zero_left hcomm).symm
  let a := F.σ.symm (lam F (u + u') hsum)
  let b := F.σ.symm (lam F u hu)
  let c := F.σ.symm (lam F u' hu')
  have hEq : a • (F.toDual u + F.toDual u') = b • F.toDual u + c • F.toDual u' := by
    calc
      a • (F.toDual u + F.toDual u') = a • F.toDual (u + u') := by
        rw [F.toDual.map_add]
      _ = revDual F (u + u') := (revDual_eq_smul_lam F hsum).symm
      _ = revDual F u + revDual F u' := revDual_add F u u'
      _ = b • F.toDual u + c • F.toDual u' := by
        rw [revDual_eq_smul_lam F hu, revDual_eq_smul_lam F hu']
  have hEq' : a • F.toDual u + a • F.toDual u' = b • F.toDual u + c • F.toDual u' := by
    simpa only [smul_add] using hEq
  have hzero : (a - b) • F.toDual u + (a - c) • F.toDual u' = 0 := by
    ext v
    have hval := congrArg (fun φ : Module.Dual K V => φ v) hEq'
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at hval ⊢
    calc
      (a - b) * F.toDual u v + (a - c) * F.toDual u' v =
          (a * F.toDual u v + a * F.toDual u' v) -
            (b * F.toDual u v + c * F.toDual u' v) := by ring
      _ = 0 := by rw [hval, sub_self]
  obtain ⟨h1, h2⟩ := LinearIndependent.pair_iff.mp hpair (a - b) (a - c) hzero
  have hab : a = b := sub_eq_zero.mp h1
  have hac : a = c := sub_eq_zero.mp h2
  have hbc : b = c := hab.symm.trans hac
  have := congrArg F.σ hbc
  simpa [b, c] using this

private theorem exists_notMem_span_singleton {u : V} (hu : u ≠ 0)
    (hdim : 2 ≤ Module.finrank K V) : ∃ w : V, ∀ c : K, c • u ≠ w := by
  have h1 : Module.finrank K (K ∙ u) = 1 := finrank_span_singleton hu
  have hlt : K ∙ u < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    have h2 : Module.finrank K (K ∙ u) = Module.finrank K (⊤ : Submodule K V) := by rw [h]
    rw [h1, finrank_top] at h2
    omega
  obtain ⟨w, -, hw⟩ := IsConcreteLE.exists_of_lt hlt
  refine ⟨w, fun c hc => hw ?_⟩
  exact Submodule.mem_span_singleton.mpr ⟨c, hc⟩

theorem lam_eq_of_dependent {u u' : V} (hdim : 2 ≤ Module.finrank K V) (hu : u ≠ 0)
    (hu' : u' ≠ 0) (hdep : ∃ c : K, c • u = u') : lam F u hu = lam F u' hu' := by
  obtain ⟨c, hc⟩ := hdep
  obtain ⟨w, hw⟩ := exists_notMem_span_singleton hu hdim
  have hw0 : w ≠ 0 := by
    intro h
    apply hw 0
    rw [h, zero_smul]
  have h1 : lam F u hu = lam F w hw0 := lam_eq_of_independent F hu hw0 hw
  have h2 : lam F u' hu' = lam F w hw0 := by
    refine lam_eq_of_independent F hu' hw0 ?_
    intro d hd
    exact hw (d * c) (by rw [mul_smul, hc, hd])
  exact h1.trans h2.symm

theorem lam_eq (hdim : 2 ≤ Module.finrank K V) {u u' : V} (hu : u ≠ 0) (hu' : u' ≠ 0) :
    lam F u hu = lam F u' hu' := by
  by_cases hdep : ∃ c : K, c • u = u'
  · exact lam_eq_of_dependent F hdim hu hu' hdep
  · exact lam_eq_of_independent F hu hu' fun c hc => hdep ⟨c, hc⟩

theorem exists_hermitian_multiple [FiniteDimensional K V] (hdim : 2 ≤ Module.finrank K V)
    (hσ : F.σ ≠ RingEquiv.refl K) :
    (∀ a : K, F.σ (F.σ a) = a) ∧ ∃ μ : K, μ ≠ 0 ∧ ∀ u v, μ * F.β v u = F.σ (μ * F.β u v) := by
  haveI : Nontrivial V :=
    Module.nontrivial_of_finrank_pos (Nat.lt_of_lt_of_le (by norm_num) hdim)
  obtain ⟨u, hu⟩ := exists_ne (0 : V)
  have hex : ∃ v : V, F.β u v ≠ 0 := by
    by_contra h
    have h' : ∀ v : V, F.β u v = 0 := by
      intro v
      by_contra hv
      exact h ⟨v, hv⟩
    exact hu (F.nondeg u h')
  obtain ⟨v0, hv0⟩ := hex
  have hv0' : v0 ≠ 0 := by
    intro h
    apply hv0
    rw [h, F.β_zero_right]
  have hfun : ∀ a : K, F.σ (F.σ a) = a := by
    intro a
    rcases eq_or_ne a 0 with rfl | ha
    · simp
    · have hau : a • u ≠ 0 := smul_ne_zero ha hu
      have hlam : lam F (a • u) hau = lam F u hu := lam_eq F hdim hau hu
      have hs : F.σ (F.β u v0) ≠ 0 := (map_ne_zero F.σ).mpr hv0
      have hl : lam F u hu ≠ 0 := lam_ne_zero F hu
      have hmain : a * F.β v0 u =
          lam F u hu * (F.σ (F.σ a) * F.σ (F.β u v0)) := by
        calc
          a * F.β v0 u = F.β v0 (a • u) := by rw [F.smul_right]
          _ = lam F (a • u) hau * F.σ (F.β (a • u) v0) := β_eq_lam F hau v0
          _ = lam F u hu * F.σ (F.β (a • u) v0) := by rw [hlam]
          _ = lam F u hu * F.σ (F.σ a * F.β u v0) := by rw [F.smul_left]
          _ = lam F u hu * (F.σ (F.σ a) * F.σ (F.β u v0)) := by rw [map_mul]
      have heq : a * (lam F u hu * F.σ (F.β u v0)) =
          F.σ (F.σ a) * (lam F u hu * F.σ (F.β u v0)) := by
        calc
          a * (lam F u hu * F.σ (F.β u v0)) = a * F.β v0 u := by
            rw [β_eq_lam F hu v0]
          _ = lam F u hu * (F.σ (F.σ a) * F.σ (F.β u v0)) := hmain
          _ = F.σ (F.σ a) * (lam F u hu * F.σ (F.β u v0)) := by ring
      exact (mul_right_cancel₀ (mul_ne_zero hl hs) heq).symm
  have hlam_sigma : lam F u hu * F.σ (lam F u hu) = 1 := by
    have h1 : F.β u v0 = lam F v0 hv0' * F.σ (F.β v0 u) := β_eq_lam F hv0' u
    have h2 : F.β v0 u = lam F u hu * F.σ (F.β u v0) := β_eq_lam F hu v0
    have hlam : lam F v0 hv0' = lam F u hu := lam_eq F hdim hv0' hu
    have hb : F.β u v0 = (lam F u hu * F.σ (lam F u hu)) * F.β u v0 := by
      calc
        F.β u v0 = lam F v0 hv0' * F.σ (F.β v0 u) := h1
        _ = lam F u hu * F.σ (F.β v0 u) := by rw [hlam]
        _ = lam F u hu * F.σ (lam F u hu * F.σ (F.β u v0)) := by rw [h2]
        _ = lam F u hu * (F.σ (lam F u hu) * F.σ (F.σ (F.β u v0))) := by rw [map_mul]
        _ = lam F u hu * (F.σ (lam F u hu) * F.β u v0) := by rw [hfun]
        _ = (lam F u hu * F.σ (lam F u hu)) * F.β u v0 := by ring
    have h1b : (1 : K) * F.β u v0 = (lam F u hu * F.σ (lam F u hu)) * F.β u v0 := by
      rw [one_mul]
      exact hb
    exact (mul_right_cancel₀ hv0 h1b).symm
  have hexμ : ∃ x : K, x + F.σ (lam F u hu) * F.σ x ≠ 0 := by
    by_contra h
    have h' : ∀ x : K, x + F.σ (lam F u hu) * F.σ x = 0 := by
      intro x
      by_contra hx
      exact h ⟨x, hx⟩
    have h1 : F.σ (lam F u hu) = -1 := by
      have h := h' 1
      rw [map_one, mul_one] at h
      exact eq_neg_of_add_eq_zero_left (by rwa [add_comm] at h)
    have h2 : ∀ x : K, F.σ x = x := by
      intro x
      have hx := h' x
      rw [h1] at hx
      have hx' : x - F.σ x = 0 := by simpa [sub_eq_add_neg] using hx
      exact (sub_eq_zero.mp hx').symm
    exact hσ (RingEquiv.ext fun x => by simpa using h2 x)
  obtain ⟨x, hx⟩ := hexμ
  let μ : K := x + F.σ (lam F u hu) * F.σ x
  have hμ : μ ≠ 0 := hx
  have hσμ : F.σ μ = lam F u hu * μ := by
    dsimp only [μ]
    calc
      F.σ (x + F.σ (lam F u hu) * F.σ x) =
          F.σ x + F.σ (F.σ (lam F u hu)) * F.σ (F.σ x) := by rw [map_add, map_mul]
      _ = F.σ x + lam F u hu * x := by rw [hfun (lam F u hu), hfun x]
      _ = lam F u hu * (x + F.σ (lam F u hu) * F.σ x) := by
        rw [mul_add, ← mul_assoc, hlam_sigma, one_mul]
        ring
  refine ⟨hfun, μ, hμ, ?_⟩
  intro u₁ v
  rcases eq_or_ne u₁ 0 with rfl | hu₁
  · rw [F.β_zero_right, F.β_zero_left]
    simp
  · have hlam : lam F u₁ hu₁ = lam F u hu := lam_eq F hdim hu₁ hu
    calc
      μ * F.β v u₁ = μ * (lam F u₁ hu₁ * F.σ (F.β u₁ v)) := by
        rw [β_eq_lam F hu₁ v]
      _ = (μ * lam F u₁ hu₁) * F.σ (F.β u₁ v) := by ring
      _ = (lam F u hu * μ) * F.σ (F.β u₁ v) := by rw [hlam]; ring
      _ = F.σ μ * F.σ (F.β u₁ v) := by rw [← hσμ]
      _ = F.σ (μ * F.β u₁ v) := by rw [map_mul]

end FiniteDimensional

theorem exists_sesq {μ : K} (hμ : μ ≠ 0)
    (hherm : ∀ u v, μ * F.β v u = F.σ (μ * F.β u v)) :
    ∃ h : V →ₛₗ[F.σ.toRingHom] V →ₗ[K] K, (∀ u v, h u v = μ * F.β u v) ∧ h.IsSymm ∧
      h.Nondegenerate := by
  let h : V →ₛₗ[F.σ.toRingHom] V →ₗ[K] K :=
    LinearMap.mk₂'ₛₗ F.σ.toRingHom (RingHom.id K) (fun u v => μ * F.β u v)
      (fun u u' v => by rw [F.add_left, mul_add])
      (fun c u v => by
        rw [F.smul_left]
        show μ * (F.σ c * F.β u v) = F.σ c * (μ * F.β u v)
        ring)
      (fun u v v' => by rw [F.add_right, mul_add])
      (fun c u v => by
        rw [F.smul_right]
        show μ * (c * F.β u v) = c * (μ * F.β u v)
        ring)
  refine ⟨h, ?_, ?_, ?_⟩
  · intro u v
    rfl
  · refine ⟨fun u v => ?_⟩
    show F.σ (μ * F.β u v) = μ * F.β v u
    exact (hherm u v).symm
  · refine ⟨?_, ?_⟩
    · intro u hu
      apply F.nondeg u
      intro v
      have hv : μ * F.β u v = 0 := hu v
      exact (mul_eq_zero.mp hv).resolve_left hμ
    · intro v hv
      apply F.nondeg v
      intro u
      have hzero : μ * F.β u v = 0 := hv u
      exact F.refl u v ((mul_eq_zero.mp hzero).resolve_left hμ)

end ReflForm

end CFSG.LieType.BorelTits
