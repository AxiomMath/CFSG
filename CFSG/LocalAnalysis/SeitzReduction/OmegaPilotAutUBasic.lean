module

public import CFSG.ClassicalGroups.Orthogonal.Eichler
public import CFSG.ClassicalGroups.Orthogonal.Hyperbolic

public section

namespace CFSG.SeitzReduction.OmegaPilot

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

section Semilinear

variable {φ : V ≃+ V} {σ : K ≃+* K} {μ : K}

theorem polar_map_of_semisim (hφQ : ∀ x, Q (φ x) = μ * σ (Q x)) (x y : V) :
    polar Q (φ x) (φ y) = μ * σ (polar Q x y) := by
  have h : φ x + φ y = φ (x + y) := (map_add φ x y).symm
  rw [polar, polar, h, hφQ, hφQ, hφQ, map_sub, map_sub]
  ring

end Semilinear

section Fixed

@[expose] def flipPair (P : HypPair Q) : HypPair Q := ⟨P.f, P.e, P.Q_f, P.Q_e, P.polar_fe⟩

@[simp] theorem flipPair_e (P : HypPair Q) : (flipPair P).e = P.f := rfl

@[simp] theorem flipPair_f (P : HypPair Q) : (flipPair P).f = P.e := rfl

theorem orth_flipPair {P P' : HypPair Q} (h : P.Orth P') : (flipPair P).Orth P' :=
  ⟨h.fe, h.ff, h.ee, h.ef⟩

theorem eichler_apply_eq_self_iff {u w x : V} (hu : Q u = 0) (hw : polar Q u w = 0) :
    eichler Q u w x = x ↔ polar Q x u • w = (polar Q x w + Q w * polar Q x u) • u := by
  rw [eichler_apply hu hw, add_sub_assoc, add_eq_left, sub_eq_zero]

theorem polar_eq_zero_of_forall_eichler_apply_eq {U : Submodule K V} {P P' : HypPair Q}
    (hPP' : P.Orth P') (he' : P'.e ∈ U) {x : V}
    (hx : ∀ w ∈ U, polar Q P.e w = 0 → eichler Q P.e w x = x) :
    polar Q x P.e = 0 ∧ ∀ w ∈ U, polar Q P.e w = 0 → polar Q x w = 0 := by
  have key : ∀ w ∈ U, polar Q P.e w = 0 →
      polar Q x P.e • w = (polar Q x w + Q w * polar Q x P.e) • P.e := fun w hw hew =>
    (eichler_apply_eq_self_iff P.Q_e hew).mp (hx w hw hew)
  have h1 : polar Q x P.e = 0 := by
    have h := congrArg (fun z => polar Q z P'.f) (key P'.e he' hPP'.ee)
    simp only [polar_smul_left_eq, P'.polar_ef, hPP'.ef, mul_zero, mul_one] at h
    exact h
  refine ⟨h1, fun w hw hew => ?_⟩
  have h := key w hw hew
  rw [h1, zero_smul, mul_zero, add_zero] at h
  exact (smul_eq_zero.mp h.symm).resolve_right P.e_ne_zero

theorem polar_eq_zero_of_forall_eichler_apply_eq_two {U : Submodule K V} {P P' : HypPair Q}
    (hPP' : P.Orth P') (hf : P.f ∈ U) (he' : P'.e ∈ U) {x : V}
    (hxe : ∀ w ∈ U, polar Q P.e w = 0 → eichler Q P.e w x = x)
    (hxf : ∀ w ∈ U, polar Q P.f w = 0 → eichler Q P.f w x = x) :
    ∀ y ∈ U, polar Q x y = 0 := by
  obtain ⟨-, hwe⟩ := polar_eq_zero_of_forall_eichler_apply_eq hPP' he' hxe
  obtain ⟨hxf0, -⟩ := polar_eq_zero_of_forall_eichler_apply_eq (P := flipPair P) (orth_flipPair hPP') he'
    hxf
  intro y hy
  have hy' : y - polar Q y P.e • P.f ∈ U := U.sub_mem hy (U.smul_mem _ hf)
  have hye : polar Q P.e (y - polar Q y P.e • P.f) = 0 := by
    rw [polar_sub_right, polar_smul_right_eq, P.polar_ef, polar_comm Q P.e y]
    ring
  have h := hwe _ hy' hye
  rw [polar_sub_right, polar_smul_right_eq] at h
  rw [flipPair_e] at hxf0
  rw [hxf0, mul_zero, sub_zero] at h
  exact h

end Fixed

section Rigidity

variable {U : Submodule K V} {P P' : HypPair Q} {φ : V ≃+ V} {σ : K ≃+* K} {μ : K}

theorem eq_smul_eichler_of_commute (hU : PolarNondegOn Q U) (hPP' : P.Orth P') (he : P.e ∈ U)
    (hf : P.f ∈ U) (he' : P'.e ∈ U) (hf' : P'.f ∈ U) (hμ : μ ≠ 0)
    (hφs : ∀ (c : K) x, φ (c • x) = σ c • φ x) (hφQ : ∀ x, Q (φ x) = μ * σ (Q x))
    (hφU : ∀ x ∈ U, φ x ∈ U)
    (hcomm : ∀ w ∈ U, polar Q P.e w = 0 → ∀ x ∈ U,
      φ (eichler Q P.e w x) = eichler Q P.e w (φ x)) :
    (∀ c, σ c = c) ∧ ∃ γ : K, γ ≠ 0 ∧ ∃ x₀ ∈ U, x₀ ∈ P.perp ∧
      ∀ x ∈ U, φ x = γ • eichler Q P.e x₀ x := by
  have hpol := polar_map_of_semisim (φ := φ) hφQ
  obtain ⟨-, hyw⟩ := polar_eq_zero_of_forall_eichler_apply_eq (U := U) hPP' he' (x := φ P.e)
    (fun w hw hew => by rw [← hcomm w hw hew P.e he, eichler_apply_self])
  set α := polar Q (φ P.e) P.f with hα
  have hφe : φ P.e = α • P.e := by
    have h0 : φ P.e - α • P.e = 0 := by
      refine hU _ (U.sub_mem (hφU _ he) (U.smul_mem _ he)) fun x hx => ?_
      have hx' : x - polar Q x P.e • P.f ∈ U := U.sub_mem hx (U.smul_mem _ hf)
      have hxe : polar Q P.e (x - polar Q x P.e • P.f) = 0 := by
        rw [polar_sub_right, polar_smul_right_eq, P.polar_ef, polar_comm Q P.e x]
        ring
      have h1 := hyw _ hx' hxe
      rw [polar_sub_right, polar_smul_right_eq] at h1
      rw [polar_sub_left, polar_smul_left_eq, polar_comm Q P.e x]
      linear_combination h1
    exact sub_eq_zero.mp h0
  have hα0 : α ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hφe
    exact P.e_ne_zero (φ.injective (hφe.trans (map_zero φ).symm))
  set γ := polar Q (φ P.f) P.e with hγ
  have hαγ : α * γ = μ := by
    have h := hpol P.f P.e
    rw [hφe, polar_smul_right_eq, P.polar_fe, map_one, mul_one] at h
    exact h
  have hγ0 : γ ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hαγ
    exact hμ hαγ.symm
  have hφw : ∀ w ∈ U, polar Q P.e w = 0 → ∃ t : K, φ w = γ • w + t • P.e := by
    intro w hw hew
    have h := hcomm w hw hew P.f hf
    rw [eichler_apply P.Q_e hew, eichler_apply P.Q_e hew, P.polar_fe, one_smul, mul_one,
      map_sub, map_add, hφs, hφe, smul_smul] at h
    refine ⟨σ (polar Q P.f w + Q w) * α - (polar Q (φ P.f) w + Q w * γ), ?_⟩
    calc φ w = (φ P.f + φ w - (σ (polar Q P.f w + Q w) * α) • P.e) - φ P.f +
          (σ (polar Q P.f w + Q w) * α) • P.e := by abel
      _ = (φ P.f + γ • w - (polar Q (φ P.f) w + Q w * γ) • P.e) - φ P.f +
          (σ (polar Q P.f w + Q w) * α) • P.e := by rw [h]
      _ = γ • w + (σ (polar Q P.f w + Q w) * α - (polar Q (φ P.f) w + Q w * γ)) • P.e := by
        rw [sub_smul]
        abel
  have hσ : ∀ c, σ c = c := by
    intro c
    obtain ⟨t₁, ht₁⟩ := hφw P'.e he' hPP'.ee
    obtain ⟨t₂, ht₂⟩ := hφw (c • P'.e) (U.smul_mem c he')
      (by rw [polar_smul_right_eq, hPP'.ee, mul_zero])
    rw [hφs, ht₁] at ht₂
    have h := congrArg (fun z => polar Q z P'.f) ht₂
    simp only [smul_add, polar_add_left, polar_smul_left_eq, P'.polar_ef, hPP'.ef, mul_zero,
      mul_one, add_zero] at h
    have h' : (σ c - c) * γ = 0 := by linear_combination h
    exact sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_right hγ0)
  have hμγ : μ = γ * γ := by
    obtain ⟨t, ht⟩ := hφw (P'.e + P'.f) (U.add_mem he' hf')
      (by rw [polar_add_right, hPP'.ee, hPP'.ef, add_zero])
    have hQx : Q (P'.e + P'.f) = 1 := by
      rw [QuadraticMap.map_add Q, P'.Q_e, P'.Q_f, P'.polar_ef]
      ring
    have h := hφQ (P'.e + P'.f)
    rw [ht, hQx, map_one, mul_one, QuadraticMap.map_add Q, map_smul_eq_sq, map_smul_eq_sq, hQx,
      P.Q_e, polar_smul_left_eq, polar_smul_right_eq, polar_add_left, polar_comm Q P'.e P.e,
      polar_comm Q P'.f P.e, hPP'.ee, hPP'.ef] at h
    linear_combination -h
  have hαeq : α = γ := by
    have h : (α - γ) * γ = 0 := by linear_combination hαγ + hμγ
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hγ0)
  rw [hαeq] at hφe
  obtain ⟨y, hy⟩ : ∃ y, y = γ⁻¹ • φ P.f := ⟨_, rfl⟩
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, x₀ = P.proj y := ⟨_, rfl⟩
  have hx₀U : x₀ ∈ U := by
    rw [hx₀, hy, HypPair.proj]
    exact U.sub_mem (U.sub_mem (U.smul_mem _ (hφU _ hf)) (U.smul_mem _ he)) (U.smul_mem _ hf)
  have hx₀P : x₀ ∈ P.perp := hx₀ ▸ P.proj_mem_perp _
  obtain ⟨hex₀, hfx₀⟩ := HypPair.mem_perp.mp hx₀P
  have hφf : φ P.f = γ • (P.f + x₀ - Q x₀ • P.e) := by
    have hyf : φ P.f = γ • y := by rw [hy, smul_smul, mul_inv_cancel₀ hγ0, one_smul]
    have hye : polar Q y P.e = 1 := by
      rw [hy, polar_smul_left_eq, ← hγ, inv_mul_cancel₀ hγ0]
    have hQy : Q y = 0 := by
      rw [hy, map_smul_eq_sq, hφQ, P.Q_f, map_zero, mul_zero, mul_zero]
    have hdec := P.eq_add_proj y
    rw [hye, one_smul, ← hx₀] at hdec
    have hcoef : polar Q y P.f = -Q x₀ := by
      have h := hQy
      rw [hdec, QuadraticMap.map_add Q, QuadraticMap.map_add Q, map_smul_eq_sq, P.Q_e, P.Q_f,
        polar_smul_left_eq, P.polar_ef, polar_add_left, polar_smul_left_eq, hex₀, hfx₀] at h
      linear_combination h
    rw [hyf, hdec, hcoef]
    module
  have hφp : ∀ p ∈ U, p ∈ P.perp → φ p = γ • (p - polar Q p x₀ • P.e) := by
    intro p hpU hpP
    obtain ⟨hep, hfp⟩ := HypPair.mem_perp.mp hpP
    have hpe : polar Q p P.e = 0 := by rw [polar_comm]; exact hep
    have hpf : polar Q p P.f = 0 := by rw [polar_comm]; exact hfp
    obtain ⟨t, ht⟩ := hφw p hpU hep
    have h := hpol p P.f
    rw [hpf, map_zero, mul_zero, ht, hφf] at h
    simp only [polar_add_left, polar_add_right, polar_sub_right, polar_smul_left_eq,
      polar_smul_right_eq, hpf, hpe, P.polar_ef, hex₀, P.polar_ee] at h
    have h' : γ * (t + γ * polar Q p x₀) = 0 := by linear_combination h
    have ht' : t = -(γ * polar Q p x₀) := by
      linear_combination (mul_eq_zero.mp h').resolve_left hγ0
    rw [ht, ht']
    module
  refine ⟨hσ, γ, hγ0, x₀, hx₀U, hx₀P, fun x hx => ?_⟩
  have hφl : ∀ (c : K) v, φ (c • v) = c • φ v := fun c v => by rw [hφs, hσ]
  have hpU : P.proj x ∈ U := by
    rw [HypPair.proj]
    exact U.sub_mem (U.sub_mem hx (U.smul_mem _ he)) (U.smul_mem _ hf)
  have hEe : eichler Q P.e x₀ P.e = P.e := eichler_apply_self _ _
  have hEf : eichler Q P.e x₀ P.f = P.f + x₀ - Q x₀ • P.e := by
    rw [eichler_apply P.Q_e hex₀, P.polar_fe, hfx₀]
    module
  have hEp : eichler Q P.e x₀ (P.proj x) = P.proj x - polar Q (P.proj x) x₀ • P.e := by
    obtain ⟨hep, -⟩ := HypPair.mem_perp.mp (P.proj_mem_perp x)
    rw [eichler_apply P.Q_e hex₀, polar_comm Q (P.proj x) P.e, hep]
    module
  rw [P.eq_add_proj x]
  simp only [map_add, hφl, LinearEquiv.map_smul]
  rw [hφe, hφf, hφp _ hpU (P.proj_mem_perp x), hEe, hEf, hEp]
  module

theorem eq_smul_of_commute_of_commute (hU : PolarNondegOn Q U) (hPP' : P.Orth P') (he : P.e ∈ U)
    (hf : P.f ∈ U) (he' : P'.e ∈ U) (hf' : P'.f ∈ U) (hμ : μ ≠ 0)
    (hφs : ∀ (c : K) x, φ (c • x) = σ c • φ x) (hφQ : ∀ x, Q (φ x) = μ * σ (Q x))
    (hφU : ∀ x ∈ U, φ x ∈ U)
    (hcomme : ∀ w ∈ U, polar Q P.e w = 0 → ∀ x ∈ U,
      φ (eichler Q P.e w x) = eichler Q P.e w (φ x))
    (hcommf : ∀ w ∈ U, polar Q P.f w = 0 → ∀ x ∈ U,
      φ (eichler Q P.f w x) = eichler Q P.f w (φ x)) :
    (∀ c, σ c = c) ∧ ∃ γ : K, γ ≠ 0 ∧ ∀ x ∈ U, φ x = γ • x := by
  obtain ⟨hσ, γ, hγ0, x₀, -, -, hφ⟩ :=
    eq_smul_eichler_of_commute hU hPP' he hf he' hf' hμ hφs hφQ hφU hcomme
  obtain ⟨-, γ', hγ'0, x₁, -, hx₁, hφ'⟩ := eq_smul_eichler_of_commute (P := flipPair P) hU
    (orth_flipPair hPP') hf he he' hf' hμ hφs hφQ hφU hcommf
  simp only [HypPair.mem_perp, flipPair_e, flipPair_f] at hx₁
  simp only [flipPair_e] at hφ'
  obtain ⟨hfx₁, hex₁⟩ := hx₁
  have hx₁e : polar Q x₁ P.e = 0 := by rw [polar_comm]; exact hex₁
  have hx₁f : polar Q x₁ P.f = 0 := by rw [polar_comm]; exact hfx₁
  have hEe : eichler Q P.f x₁ P.e = P.e + x₁ - Q x₁ • P.f := by
    rw [eichler_apply P.Q_f hfx₁, P.polar_ef, hex₁]
    module
  have h := (hφ P.e he).symm.trans (hφ' P.e he)
  rw [eichler_apply_self, hEe] at h
  have hγγ : γ = γ' := by
    have h2 := congrArg (fun z => polar Q z P.f) h
    simp only [polar_smul_left_eq, polar_add_left, polar_sub_left, P.polar_ef, hx₁f,
      P.polar_ff] at h2
    linear_combination h2
  rw [← hγγ] at h hφ'
  have h3 : γ • (x₁ - Q x₁ • P.f) = 0 := by
    calc γ • (x₁ - Q x₁ • P.f) = γ • (P.e + x₁ - Q x₁ • P.f) - γ • P.e := by module
      _ = 0 := by rw [← h, sub_self]
  have h4 := (smul_eq_zero.mp h3).resolve_left hγ0
  have h5 := congrArg (fun z => polar Q z P.e) h4
  simp only [polar_sub_left, polar_smul_left_eq, P.polar_fe, polar_zero_left, hx₁e] at h5
  have hQ0 : Q x₁ = 0 := by linear_combination -h5
  rw [hQ0, zero_smul, sub_zero] at h4
  refine ⟨hσ, γ, hγ0, fun x hx => ?_⟩
  rw [hφ' x hx, h4, eichler_zero_right]
  rfl

end Rigidity

section LongRoot

theorem exists_sub_eq_smul_of_eichler_eq (P : HypPair Q) {y y' : V} (hy : polar Q P.e y = 0)
    (hy' : polar Q P.e y' = 0) (h : eichler Q P.e y = eichler Q P.e y') :
    ∃ c : K, y - y' = c • P.e := by
  have h1 := LinearEquiv.congr_fun h P.f
  rw [eichler_apply P.Q_e hy, eichler_apply P.Q_e hy', P.polar_fe, one_smul, one_smul, mul_one,
    mul_one] at h1
  refine ⟨(polar Q P.f y + Q y) - (polar Q P.f y' + Q y'), ?_⟩
  rw [sub_smul]
  calc y - y' = (P.f + y - (polar Q P.f y + Q y) • P.e) -
        (P.f + y' - (polar Q P.f y' + Q y') • P.e) +
        ((polar Q P.f y + Q y) • P.e - (polar Q P.f y' + Q y') • P.e) := by abel
    _ = (polar Q P.f y + Q y) • P.e - (polar Q P.f y' + Q y') • P.e := by
      rw [h1, sub_self, zero_add]

theorem eq_smul_of_forall_commute_eichler (hQ : (polarBilin Q).Nondegenerate)
    {P₁ P₂ P₃ : HypPair Q} (h₁₂ : P₁.Orth P₂) (h₁₃ : P₁.Orth P₃) (h₂₃ : P₂.Orth P₃) {x₀ : V}
    (hx₀ : x₀ ∈ P₁.perp)
    (hc : ∀ w, polar Q P₂.e w = 0 → polar Q P₁.e w = 0 →
      eichler Q P₂.e w * eichler Q P₁.e x₀ = eichler Q P₁.e x₀ * eichler Q P₂.e w) :
    x₀ = polar Q x₀ P₂.f • P₂.e := by
  obtain ⟨hex₀, hfx₀⟩ := HypPair.mem_perp.mp hx₀
  have key : ∀ w, polar Q P₂.e w = 0 → polar Q P₁.e w = 0 →
      ∃ c : K, eichler Q P₂.e w x₀ - x₀ = c • P₁.e := by
    intro w h2w h1w
    have hgO := eichler_mem_orthogonalGroup Q P₂.e w
    have hge : eichler Q P₂.e w P₁.e = P₁.e := eichler_apply_of_polar_eq_zero h₁₂.ee h1w
    have hconj := eichler_conj hgO P₁.e x₀
    rw [hge, hc w h2w h1w, mul_inv_cancel_right] at hconj
    refine exists_sub_eq_smul_of_eichler_eq P₁ ?_ hex₀ hconj.symm
    rw [← hge, polar_map_of_mem hgO, hex₀]
  have hdisp : ∀ w, polar Q P₂.e w = 0 → eichler Q P₂.e w x₀ - x₀ =
      polar Q x₀ P₂.e • w - (polar Q x₀ w + Q w * polar Q x₀ P₂.e) • P₂.e := by
    intro w h2w
    rw [eichler_apply P₂.Q_e h2w]
    abel
  have hx₀e₂ : polar Q x₀ P₂.e = 0 := by
    obtain ⟨c, hc'⟩ := key P₃.e h₂₃.ee h₁₃.ee
    rw [hdisp P₃.e h₂₃.ee] at hc'
    have h := congrArg (fun z => polar Q z P₃.f) hc'
    simp only [polar_sub_left, polar_smul_left_eq, P₃.polar_ef, h₂₃.ef, h₁₃.ef] at h
    linear_combination h
  have hx₀w : ∀ w, polar Q P₂.e w = 0 → polar Q P₁.e w = 0 → polar Q x₀ w = 0 := by
    intro w h2w h1w
    obtain ⟨c, hc'⟩ := key w h2w h1w
    rw [hdisp w h2w, hx₀e₂, zero_smul, mul_zero, add_zero, zero_sub] at hc'
    have h := congrArg (fun z => polar Q z P₂.f) hc'
    simp only [polar_neg_left, polar_smul_left_eq, P₂.polar_ef, h₁₂.ef] at h
    linear_combination -h
  have hx₀f₁ : polar Q x₀ P₁.f = 0 := by rw [polar_comm]; exact hfx₀
  apply sub_eq_zero.mp
  apply eq_zero_of_polar_eq_zero hQ
  intro z
  set z' := z - polar Q z P₁.e • P₁.f - polar Q z P₂.e • P₂.f with hz'
  have h2z' : polar Q P₂.e z' = 0 := by
    rw [hz', polar_sub_right, polar_sub_right, polar_smul_right_eq, polar_smul_right_eq,
      P₂.polar_ef, polar_comm Q P₂.e P₁.f, h₁₂.fe, polar_comm Q P₂.e z]
    ring
  have h1z' : polar Q P₁.e z' = 0 := by
    rw [hz', polar_sub_right, polar_sub_right, polar_smul_right_eq, polar_smul_right_eq,
      P₁.polar_ef, h₁₂.ef, polar_comm Q P₁.e z]
    ring
  have h := hx₀w z' h2z' h1z'
  rw [hz', polar_sub_right, polar_sub_right, polar_smul_right_eq, polar_smul_right_eq,
    hx₀f₁] at h
  rw [polar_sub_left, polar_smul_left_eq, polar_comm Q P₂.e z]
  linear_combination h

end LongRoot

end CFSG.SeitzReduction.OmegaPilot
