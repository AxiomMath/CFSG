module

public import CFSG.GF2Type.Smith1979W3.Cert690.Tab

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979W3.Cert690

open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.O62

variable {K : Subgroup (V₀ ≃ₗ[ZMod 2] V₀)} {σ : (Q0 ≃* Q0) → Q0}

theorem v_mul_apply_of {φ ψ : Q0 ≃* Q0} {g h : V₀ ≃ₗ[ZMod 2] V₀}
    (hφ : ∀ x, (φ x).v = g x.v) (hψ : ∀ x, (ψ x).v = h x.v) (x : Q0) :
    ((φ * ψ) x).v = (g * h) x.v := by
  rw [MulAut.mul_apply, hφ, hψ, LinearEquiv.mul_apply]

theorem v_inv_apply_of {φ : Q0 ≃* Q0} {g : V₀ ≃ₗ[ZMod 2] V₀}
    (hφ : ∀ x, (φ x).v = g x.v) (x : Q0) : (φ⁻¹ x).v = g⁻¹ x.v := by
  have h := hφ (φ⁻¹ x)
  rw [MulAut.apply_inv_self] at h
  rw [h]
  simp

theorem v_inn_apply (e x : Q0) : (inn e x).v = x.v := by
  rw [inn, MulAut.conj_apply, inv_inv]
  show e.v + x.v + e.v = x.v
  rw [add_comm e.v x.v, add_assoc, CharTwo.add_self_eq_zero, add_zero]

theorem one_mem_thetaOver : (1 : Q0 ≃* Q0) ∈ ThetaOver K :=
  ⟨1, K.one_mem, by simp, fun _ => by simp⟩

theorem inn_mul_mem_thetaOver {θ : Q0 ≃* Q0} (hθ : θ ∈ ThetaOver K) (e : Q0) :
    inn e * θ ∈ ThetaOver K := by
  obtain ⟨g, hgK, hgg, hg⟩ := hθ
  exact ⟨g, hgK, hgg, fun x => by
    rw [v_mul_apply_of (g := 1) (h := g) (fun y => by rw [v_inn_apply]; simp) hg x,
      one_mul]⟩

theorem conj_mem_thetaOver {θ ψ : Q0 ≃* Q0} (hθ : θ ∈ ThetaOver K) (hψ : ψ ∈ XOver K) :
    ψ * θ * ψ⁻¹ ∈ ThetaOver K := by
  obtain ⟨g, hgK, hgg, hg⟩ := hθ
  obtain ⟨h, hhK, hh⟩ := hψ
  refine ⟨h * g * h⁻¹, K.mul_mem (K.mul_mem hhK hgK) (K.inv_mem hhK), ?_, fun x => ?_⟩
  · calc
      (h * g * h⁻¹) * (h * g * h⁻¹) = h * (g * g) * h⁻¹ := by group
      _ = h * 1 * h⁻¹ := by rw [hgg]
      _ = 1 := by group
  · exact v_mul_apply_of (g := h * g) (h := h⁻¹) (fun y => v_mul_apply_of hh hg y)
      (v_inv_apply_of hh) x

theorem IsSquareData.sigma_inn (h : IsSquareData K σ) (e : Q0) : σ (inn e) = e * e := by
  have h4 := h.2.2.2 (1 : Q0 ≃* Q0) one_mem_thetaOver e
  simpa [h.1] using h4

theorem IsSquareData.sigma_eq_or (h : IsSquareData K σ) {θ : Q0 ≃* Q0} (hθ : θ ∈ ThetaOver K)
    {r : Q0} (hr : ∀ e, inn e = θ * θ → e = r ∨ e = r * z0) :
    σ θ = r ∨ σ θ = r * z0 :=
  hr (σ θ) (h.2.1 θ hθ).symm

theorem IsSquareData.sigma_inn_mul_conj (h : IsSquareData K σ) {θ ψ : Q0 ≃* Q0}
    (hθ : θ ∈ ThetaOver K) (hψ : ψ ∈ XOver K) (e : Q0) :
    σ (inn e * (ψ * θ * ψ⁻¹)) = ψ (σ θ) * (ψ * θ * ψ⁻¹) e * e := by
  have h4 := h.2.2.2 (ψ * θ * ψ⁻¹) (conj_mem_thetaOver hθ hψ) e
  rw [h.2.2.1 θ hθ ψ hψ] at h4
  exact h4

theorem IsSquareData.sigma_eq_of_mul_inv_eq_inn (h : IsSquareData K σ) {θ θ₀ ψ : Q0 ≃* Q0}
    (hθ₀ : θ₀ ∈ ThetaOver K) (hψ : ψ ∈ XOver K) {e : Q0}
    (he : θ * (ψ * θ₀ * ψ⁻¹)⁻¹ = inn e) :
    σ θ = ψ (σ θ₀) * (ψ * θ₀ * ψ⁻¹) e * e := by
  have h' : θ = inn e * (ψ * θ₀ * ψ⁻¹) := by
    rw [← he, mul_assoc, inv_mul_cancel, mul_one]
  rw [h']
  exact h.sigma_inn_mul_conj hθ₀ hψ e

theorem ofTab_liftTab_mem_xOver {u : V₀ ≃ₗ[ZMod 2] V₀} (hu : u ∈ K) {g f : ℕ}
    (hg : Code.HasCode (u : V₀ →ₗ[ZMod 2] V₀) g) (h : isHomTab (liftTab g f) = true) :
    ofTab (liftTab g f) h ∈ XOver K :=
  ⟨u, hu, v_ofTab_liftTab hg h⟩

theorem ofTab_liftTab_mem_thetaOver {u : V₀ ≃ₗ[ZMod 2] V₀} (hu : u ∈ K) (hu2 : u * u = 1)
    {g f : ℕ} (hg : Code.HasCode (u : V₀ →ₗ[ZMod 2] V₀) g)
    (h : isHomTab (liftTab g f) = true) :
    ofTab (liftTab g f) h ∈ ThetaOver K :=
  ⟨u, hu, hu2, v_ofTab_liftTab hg h⟩

private theorem candValOne_eq_some_iff {IT : Array (Array ℕ)} {theta : Array ℕ} {v : ℕ} :
    candValOne IT theta = some v ↔ ∃ e, findInn IT theta = some e ∧ e < 128 ∧ v = qmulN e e := by
  unfold candValOne
  cases h : findInn IT theta with
  | none => simp [h]
  | some e => by_cases he : e < 128 <;> simp [h, he, eq_comm]

private theorem candVal_eq_some_iff {IT : Array (Array ℕ)} {theta psi tp itp : Array ℕ}
    {s v : ℕ} :
    candVal IT theta psi tp itp s = some v ↔ ∃ e, findInn IT (compTab theta itp) = some e ∧
      e < 128 ∧ v = qmulN (qmulN (psi[s]!) (tp[e]!)) e := by
  unfold candVal
  cases h : findInn IT (compTab theta itp) with
  | none => simp [h]
  | some e => by_cases he : e < 128 <;> simp [h, he, eq_comm]

theorem IsSquareData.candValOne_eq (h : IsSquareData K σ) {θ : Q0 ≃* Q0} {v : ℕ}
    (hv : candValOne (innTabs ()) (tabOf θ) = some v) : v = enc (σ θ) := by
  obtain ⟨e, hfind, he, hv'⟩ := candValOne_eq_some_iff.mp hv
  obtain ⟨-, heinn⟩ := findInn_spec hfind
  have hθ : θ = inn (dec e) := by
    apply tabOf_injective
    rw [tabOf_inn, enc_dec he]
    exact heinn.symm
  rw [hv', hθ]
  calc
    qmulN e e = qmulN (enc (dec e)) (enc (dec e)) := by rw [enc_dec he]
    _ = enc ((dec e) * (dec e)) := qmulN_enc _ _
    _ = enc (σ (inn (dec e))) := by rw [h.sigma_inn]

theorem IsSquareData.candVal_eq (h : IsSquareData K σ) {θ θ₀ ψ : Q0 ≃* Q0}
    (hθ₀ : θ₀ ∈ ThetaOver K) (hψ : ψ ∈ XOver K) {s v : ℕ} (hs : s < 128)
    (hσ : σ θ₀ = dec s)
    (hv : candVal (innTabs ()) (tabOf θ) (tabOf ψ) (tabOf (ψ * θ₀ * ψ⁻¹))
      (tabOf (ψ * θ₀ * ψ⁻¹)⁻¹) s = some v) : v = enc (σ θ) := by
  let tp : Q0 ≃* Q0 := ψ * θ₀ * ψ⁻¹
  change candVal (innTabs ()) (tabOf θ) (tabOf ψ) (tabOf tp) (tabOf tp⁻¹) s = some v at hv
  obtain ⟨e, hfind, he, hv'⟩ := candVal_eq_some_iff.mp hv
  have htabpsi : (tabOf ψ)[s]! = enc (ψ (dec s)) := by
    have h := tabOf_getElem! ψ (dec s)
    rwa [enc_dec hs] at h
  have htabtp : (tabOf tp)[e]! = enc (tp (dec e)) := by
    have h := tabOf_getElem! tp (dec e)
    rwa [enc_dec he] at h
  have heinn : innTab e = compTab (tabOf θ) (tabOf tp⁻¹) := (findInn_spec hfind).2
  have h1 : tabOf (inn (dec e)) = tabOf (θ * tp⁻¹) := by
    rw [tabOf_mul, tabOf_inn, enc_dec he]
    exact heinn
  have hθeq : θ * tp⁻¹ = inn (dec e) := (tabOf_injective h1).symm
  have hsq : σ θ = ψ (σ θ₀) * tp (dec e) * dec e :=
    h.sigma_eq_of_mul_inv_eq_inn hθ₀ hψ hθeq
  calc
    v = qmulN (qmulN ((tabOf ψ)[s]!) ((tabOf tp)[e]!)) e := hv'
    _ = qmulN (qmulN (enc (ψ (dec s))) (enc (tp (dec e)))) e := by rw [htabpsi, htabtp]
    _ = qmulN (enc (ψ (dec s) * tp (dec e))) e := by rw [qmulN_enc]
    _ = qmulN (enc (ψ (dec s) * tp (dec e))) (enc (dec e)) := by rw [enc_dec he]
    _ = enc (ψ (dec s) * tp (dec e) * (dec e)) := qmulN_enc _ _
    _ = enc (σ θ) := by rw [hsq, hσ]

theorem IsSquareData.sigma_eq_dec_or (h : IsSquareData K σ) {θ₀ : Q0 ≃* Q0}
    (hθ₀ : θ₀ ∈ ThetaOver K) {r : ℕ}
    (hr : ∀ e, e ∈ innRoots (innTabs ()) (compTab (tabOf θ₀) (tabOf θ₀)) ↔
      e = r ∨ e = qmulN r z0N) :
    σ θ₀ = dec r ∨ σ θ₀ = dec (qmulN r z0N) := by
  have hr_lt : r < 128 := (mem_innRoots_iff.mp ((hr r).mpr (Or.inl rfl))).1
  have hrz_lt : qmulN r z0N < 128 :=
    (mem_innRoots_iff.mp ((hr (qmulN r z0N)).mpr (Or.inr rfl))).1
  have hz : dec r * z0 = dec (qmulN r z0N) := by
    apply enc_injective
    rw [← qmulN_enc, enc_z0, enc_dec hr_lt, enc_dec hrz_lt]
  have hr' : ∀ e, inn e = θ₀ * θ₀ → e = dec r ∨ e = dec (qmulN r z0N) := by
    intro e he
    have hmem : enc e ∈ innRoots (innTabs ()) (compTab (tabOf θ₀) (tabOf θ₀)) := by
      rw [mem_innRoots_iff]
      refine ⟨enc_lt e, ?_⟩
      rw [← tabOf_inn e, he, tabOf_mul]
    rcases (hr (enc e)).mp hmem with h | h
    · left
      rw [← h, dec_enc]
    · right
      rw [← h, dec_enc]
  have hr'' : ∀ e, inn e = θ₀ * θ₀ → e = dec r ∨ e = dec r * z0 := by
    intro e he
    rcases hr' e he with h | h
    · exact Or.inl h
    · exact Or.inr (h.trans hz.symm)
  rcases h.sigma_eq_or hθ₀ hr'' with h1 | h1
  · exact Or.inl h1
  · exact Or.inr (h1.trans hz)

theorem IsSquareData.candVal_liftTab_eq (h : IsSquareData K σ) {kc rc s v : ℕ}
    (hk : ∃ k ∈ K, Code.HasCode (k : V₀ →ₗ[ZMod 2] V₀) kc)
    (hr : ∃ r ∈ K, r * r = 1 ∧ Code.HasCode (r : V₀ →ₗ[ZMod 2] V₀) rc)
    (hkt : isHomTab (liftTab kc 0) = true) (hrt : isHomTab (liftTab rc 0) = true)
    (hs : s < 128) (hσ : σ (ofTab (liftTab rc 0) hrt) = dec s) {θ : Q0 ≃* Q0}
    (hv : candVal (innTabs ()) (tabOf θ) (liftTab kc 0)
      (compTab (compTab (liftTab kc 0) (liftTab rc 0)) (invTab (liftTab kc 0)))
      (invTab (compTab (compTab (liftTab kc 0) (liftTab rc 0))
        (invTab (liftTab kc 0)))) s = some v) :
    v = enc (σ θ) := by
  obtain ⟨k, hkK, hkc⟩ := hk
  obtain ⟨r, hrK, hr2, hrc⟩ := hr
  let ψ : Q0 ≃* Q0 := ofTab (liftTab kc 0) hkt
  let θ₀ : Q0 ≃* Q0 := ofTab (liftTab rc 0) hrt
  have hψ : ψ ∈ XOver K := ofTab_liftTab_mem_xOver hkK hkc hkt
  have hθ₀ : θ₀ ∈ ThetaOver K := ofTab_liftTab_mem_thetaOver hrK hr2 hrc hrt
  have htabψ : tabOf ψ = liftTab kc 0 := tabOf_ofTab _ hkt
  have htabθ₀ : tabOf θ₀ = liftTab rc 0 := tabOf_ofTab _ hrt
  have htp : tabOf (ψ * θ₀ * ψ⁻¹) =
      compTab (compTab (liftTab kc 0) (liftTab rc 0)) (invTab (liftTab kc 0)) := by
    rw [tabOf_mul, tabOf_mul, tabOf_inv, htabψ, htabθ₀]
  have hitp : tabOf (ψ * θ₀ * ψ⁻¹)⁻¹ =
      invTab (compTab (compTab (liftTab kc 0) (liftTab rc 0)) (invTab (liftTab kc 0))) := by
    rw [tabOf_inv, htp]
  have hσ' : σ θ₀ = dec s := hσ
  rw [← hitp, ← htp, ← htabψ] at hv
  exact h.candVal_eq hθ₀ hψ hs hσ' hv

end CFSG.GF2Type.Smith1979W3.Cert690

end
