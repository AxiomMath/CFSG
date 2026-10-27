module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticCoverFourModel
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverDiagonal

public section

namespace CFSG.LocalAnalysis.ComponentInitial.SymplecticCoverFour

open CFSG.Assembly.LowTwoRank SymplecticFlag SymplecticFour
open scoped commutatorElement

section Weight

variable {F E : Type*} [Field F] [Group E]

theorem eq_one_of_add_of_mul_invariant {ψ : F → E} (hadd : ∀ s s', ψ (s + s') = ψ s * ψ s')
    {r : F} (hr : r ≠ 1) (hinv : ∀ s, ψ (r * s) = ψ s) (s : F) : ψ s = 1 := by
  have hr' : r - 1 ≠ 0 := sub_ne_zero.mpr hr
  have h := hinv ((r - 1)⁻¹ * s)
  rw [show r * ((r - 1)⁻¹ * s) = (r - 1)⁻¹ * s + s by field_simp; ring, hadd] at h
  exact mul_eq_left.mp h

variable {X : Type*} [Group X] {θ : E →* X} (hθ : Function.Surjective θ)
  (hC : θ.ker ≤ Subgroup.center E)

include hθ hC in
theorem commutatorElement_eq_one_of_weight {ψ : F → X} (hψ : ∀ s s', ψ (s + s') = ψ s * ψ s')
    {x g : E} {r : F} (hr : r ≠ 1) (hcen : ∀ e s, θ e = ψ s → ⁅e, x⁆ ∈ Subgroup.center E)
    (hg : ∀ s, θ g * ψ s * (θ g)⁻¹ = ψ (r * s)) (hgx : θ g * θ x * (θ g)⁻¹ = θ x)
    {e : E} {s : F} (he : θ e = ψ s) : ⁅e, x⁆ = 1 := by
  have comm_eq : ∀ {x x' y y' : E}, θ x = θ x' → θ y = θ y' → ⁅x, y⁆ = ⁅x', y'⁆ :=
    fun hx hy => LinearCover.HeisenbergRoots.commutatorElement_eq_of_map_eq θ (fun z hz => hC hz)
      hx hy
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : F → E, ∀ s, θ (ℓ s) = ψ s :=
    ⟨fun s => Function.surjInv hθ (ψ s), fun s => Function.surjInv_eq hθ _⟩
  have hF := eq_one_of_add_of_mul_invariant (ψ := fun s => ⁅ℓ s, x⁆)
    (fun s s' => by
      rw [comm_eq (x' := ℓ s * ℓ s') (by rw [hℓ, map_mul, hℓ, hℓ, hψ]) rfl,
        commutatorElement_mul_left_of_mem_center (hcen _ _ (hℓ s'))])
    hr
    (fun s => by
      have hc := hcen _ _ (hℓ s)
      have h1 : g * ⁅ℓ s, x⁆ * g⁻¹ = ⁅ℓ s, x⁆ := by
        rw [Subgroup.mem_center_iff.mp hc g, mul_inv_cancel_right]
      have h2 : g * ⁅ℓ s, x⁆ * g⁻¹ = ⁅g * ℓ s * g⁻¹, g * x * g⁻¹⁆ := by
        simp only [commutatorElement_def]
        group
      change ⁅ℓ (r * s), x⁆ = ⁅ℓ s, x⁆
      rw [← h1, h2]
      exact comm_eq (by rw [hℓ, map_mul, map_mul, map_inv, hℓ, hg])
        (by rw [map_mul, map_mul, map_inv, hgx]))
  rw [comm_eq (x' := ℓ s) (by rw [he, hℓ]) rfl]
  exact hF s

end Weight

section Cover

variable {K : Type} [Field K] [CharP K 2] {E : Type*} [Group E] {θ : E →* StatedSp 2 K}
  (hθ : Function.Surjective θ) (hC : θ.ker ≤ Subgroup.center E)

include hC in
theorem commutatorElement_mem_center_of_tauS {z g : E} (hz : ∃ b c, θ z = tauS b c 0)
    (hg : θ g ∈ unipotent 2 K) : ⁅z, g⁆ ∈ Subgroup.center E := hC (by
  obtain ⟨b, c, hbc⟩ := hz
  rw [MonoidHom.mem_ker, map_commutatorElement, hbc, commutatorElement_eq_one_iff_mul_comm]
  exact tauS_zero_mul_comm hg b c)

include hθ hC in
theorem mul_comm_of_tauS {t : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1) {z₁ z₂ : E}
    (h₁ : ∃ b c, θ z₁ = tauS b c 0) (h₂ : ∃ b c, θ z₂ = tauS b c 0) : z₁ * z₂ = z₂ * z₁ := by
  obtain ⟨b, c, hbc⟩ := h₂
  have htt := sq_add_self_ne_zero_of_charTwo ht0 ht1
  set d₂ := (b + c) / (t ^ 2 + t) with hd₂
  set d₁ := c + t * d₂ with hd₁
  have hd : (t ^ 2 + t) * d₂ = b + c := by
    rw [hd₂]
    exact mul_div_cancel₀ _ htt
  have hb : 1 ^ 2 * d₁ + t ^ 2 * d₂ = b := by
    rw [hd₁]
    linear_combination hd + c * (CharP.cast_eq_zero K 2)
  have hc : 1 * d₁ + t * d₂ = c := by
    rw [hd₁]
    linear_combination t * d₂ * (CharP.cast_eq_zero K 2)
  obtain ⟨x₁, hx₁⟩ := hθ (lam 1)
  obtain ⟨y₁, hy₁⟩ := hθ (tauS 0 0 d₁)
  obtain ⟨x₂, hx₂⟩ := hθ (lam t)
  obtain ⟨y₂, hy₂⟩ := hθ (tauS 0 0 d₂)
  have hP : θ (⁅x₁, y₁⁆ * ⁅x₂, y₂⁆) = θ z₂ := by
    rw [map_mul, map_commutatorElement, map_commutatorElement, hx₁, hy₁, hx₂, hy₂,
      commutatorElement_lam_tauS, commutatorElement_lam_tauS, tauS_mul_tauS, hb, hc, add_zero,
      hbc]
  have hk₀ : (⁅x₁, y₁⁆ * ⁅x₂, y₂⁆)⁻¹ * z₂ ∈ Subgroup.center E := hC (by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hP, inv_mul_cancel])
  have hU : ∀ {g : E} {y : StatedSp 2 K}, θ g = y → y ∈ unipotent 2 K → θ g ∈ unipotent 2 K :=
    fun h hy => h ▸ hy
  have hc₁ := LinearFieldFour.commute_commutatorElement_of_mem_center
    (commutatorElement_mem_center_of_tauS hC h₁ (hU hx₁ (lam_mem_unipotent 1)))
    (commutatorElement_mem_center_of_tauS hC h₁ (hU hy₁ (tauS_mem_unipotent 0 0 d₁)))
  have hc₂ := LinearFieldFour.commute_commutatorElement_of_mem_center
    (commutatorElement_mem_center_of_tauS hC h₁ (hU hx₂ (lam_mem_unipotent t)))
    (commutatorElement_mem_center_of_tauS hC h₁ (hU hy₂ (tauS_mem_unipotent 0 0 d₂)))
  obtain ⟨k, hk, rfl⟩ : ∃ k ∈ Subgroup.center E, z₂ = ⁅x₁, y₁⁆ * ⁅x₂, y₂⁆ * k :=
    ⟨_, hk₀, by group⟩
  calc z₁ * (⁅x₁, y₁⁆ * ⁅x₂, y₂⁆ * k) = z₁ * ⁅x₁, y₁⁆ * ⁅x₂, y₂⁆ * k := by group
    _ = ⁅x₁, y₁⁆ * (z₁ * ⁅x₂, y₂⁆) * k := by rw [hc₁]; group
    _ = ⁅x₁, y₁⁆ * ⁅x₂, y₂⁆ * (z₁ * k) := by rw [hc₂]; group
    _ = ⁅x₁, y₁⁆ * ⁅x₂, y₂⁆ * k * z₁ := by rw [Subgroup.mem_center_iff.mp hk z₁]; group

include hθ hC in
theorem commutatorElement_eq_one_of_weights {x g g' : E} (hx : θ x ∈ unipotent 2 K)
    {r r' : K} (hr : r ≠ 1) (hr' : r' ≠ 1)
    (hg : ∀ s, θ g * tauS s 0 0 * (θ g)⁻¹ = tauS (r * s) 0 0)
    (hgx : θ g * θ x * (θ g)⁻¹ = θ x)
    (hg' : ∀ s, θ g' * tauS 0 s 0 * (θ g')⁻¹ = tauS 0 (r' * s) 0)
    (hg'x : θ g' * θ x * (θ g')⁻¹ = θ x) {z : E} (hz : ∃ b c, θ z = tauS b c 0) :
    ⁅z, x⁆ = 1 := by
  have hcen : ∀ e (b c : K), θ e = tauS b c 0 → ⁅e, x⁆ ∈ Subgroup.center E := fun e b c he =>
    commutatorElement_mem_center_of_tauS hC ⟨b, c, he⟩ hx
  obtain ⟨b, c, hbc⟩ := hz
  obtain ⟨eb, heb⟩ := hθ (tauS b 0 0)
  obtain ⟨ec, hec⟩ := hθ (tauS 0 c 0)
  have h₁ : ⁅eb, x⁆ = 1 := commutatorElement_eq_one_of_weight hθ hC (ψ := fun s => tauS s 0 0)
    (fun s s' => by rw [tauS_mul_tauS, add_zero]) hr (fun e s he => hcen e s 0 he)
    hg hgx heb
  have h₂ : ⁅ec, x⁆ = 1 := commutatorElement_eq_one_of_weight hθ hC (ψ := fun s => tauS 0 s 0)
    (fun s s' => by rw [tauS_mul_tauS, add_zero]) hr' (fun e s he => hcen e 0 s he)
    hg' hg'x hec
  rw [LinearCover.HeisenbergRoots.commutatorElement_eq_of_map_eq θ (fun z hz => hC hz)
      (x' := eb * ec) (by rw [hbc, map_mul, heb, hec, tauS_mul_tauS, add_zero, zero_add,
        add_zero]) rfl,
    commutatorElement_mul_left_of_mem_center (hcen ec 0 c hec), h₁, h₂, mul_one]

include hθ hC in
theorem commutatorElement_tauS_lam {t : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1) {z x : E}
    (hz : ∃ b c, θ z = tauS b c 0) {a : K} (hx : θ x = lam a) : ⁅z, x⁆ = 1 := by
  obtain ⟨g, hg⟩ := hθ (SymplecticTorusWeyl.torusHom (fun _ => Units.mk0 t ht0))
  have hgx : θ g * θ x * (θ g)⁻¹ = θ x := by rw [hg, hx, torusHom_const_conj_lam]
  have hgs : ∀ s, θ g * tauS s 0 0 * (θ g)⁻¹ = tauS (t ^ 2 * s) 0 0 := fun s => by
    rw [hg, torusHom_const_conj_tauS, Units.val_mk0, mul_zero]
  have hgs' : ∀ s, θ g * tauS 0 s 0 * (θ g)⁻¹ = tauS 0 (t ^ 2 * s) 0 := fun s => by
    rw [hg, torusHom_const_conj_tauS, Units.val_mk0, mul_zero]
  exact commutatorElement_eq_one_of_weights hθ hC (hx ▸ lam_mem_unipotent a)
    (sq_ne_one_of_charTwo ht1) (sq_ne_one_of_charTwo ht1) hgs hgx hgs' hgx hz

include hθ hC in
theorem commutatorElement_tauS_tauS {t : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1) {z y : E}
    (hz : ∃ b c, θ z = tauS b c 0) {d : K} (hy : θ y = tauS 0 0 d) : ⁅z, y⁆ = 1 := by
  obtain ⟨g, hg⟩ := hθ (SymplecticTorusWeyl.torusHom ![Units.mk0 t ht0, 1])
  have hgy : θ g * θ y * (θ g)⁻¹ = θ y := by
    rw [hg, hy, torusHom_first_conj_tauS, mul_zero, mul_zero]
  have hgs : ∀ s, θ g * tauS s 0 0 * (θ g)⁻¹ = tauS (t ^ 2 * s) 0 0 := fun s => by
    rw [hg, torusHom_first_conj_tauS, Units.val_mk0, mul_zero]
  have hgs' : ∀ s, θ g * tauS 0 s 0 * (θ g)⁻¹ = tauS 0 (t * s) 0 := fun s => by
    rw [hg, torusHom_first_conj_tauS, Units.val_mk0, mul_zero]
  exact commutatorElement_eq_one_of_weights hθ hC (hy ▸ tauS_mem_unipotent 0 0 d)
    (sq_ne_one_of_charTwo ht1) ht1 hgs hgy hgs' hgy hz

include hθ hC in
theorem mul_comm_of_tauS_of_mem_unipotent {t : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1) {z g : E}
    (hz : ∃ b c, θ z = tauS b c 0) (hg : θ g ∈ unipotent 2 K) : z * g = g * z := by
  obtain ⟨C, hC', a, hga⟩ := mem_unipotent_iff.mp hg
  rw [tau_eq_tauS] at hga
  obtain ⟨w, hw⟩ := hθ (tauS (C 0 0) (C 0 1) 0)
  obtain ⟨y, hy⟩ := hθ (tauS 0 0 (C 1 1))
  obtain ⟨x, hx⟩ := hθ (lam a)
  have hθg : θ g = θ (w * y * x) := by
    rw [hga, map_mul, map_mul, hw, hy, hx, tauS_mul_tauS, add_zero, add_zero, zero_add]
  have h₁ : ⁅z, w⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm_of_tauS hθ hC ht0 ht1 hz ⟨_, _, hw⟩)
  have h₂ : ⁅z, y⁆ = 1 := commutatorElement_tauS_tauS hθ hC ht0 ht1 hz hy
  have h₃ : ⁅z, x⁆ = 1 := commutatorElement_tauS_lam hθ hC ht0 ht1 hz hx
  refine commutatorElement_eq_one_iff_mul_comm.mp ?_
  rw [LinearCover.HeisenbergRoots.commutatorElement_eq_of_map_eq θ (fun z hz => hC hz) rfl hθg,
    commutatorElement_mul_right_of_mem_center' (h₃ ▸ one_mem _),
    commutatorElement_mul_right_of_mem_center' (h₂ ▸ one_mem _), h₁, h₂, h₃, mul_one, mul_one]

include hθ hC in
theorem mul_comm_of_lam {t : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1) {x₁ x₂ : E} {a₁ a₂ : K}
    (h₁ : θ x₁ = lam a₁) (h₂ : θ x₂ = lam a₂) : x₁ * x₂ = x₂ * x₁ := by
  obtain ⟨g, hg⟩ := hθ (weylA K)
  have hconj : ∀ {x : E} {a : K}, θ x = lam a → θ (g * x * g⁻¹) = tauS 0 a 0 := fun hx => by
    rw [map_mul, map_mul, map_inv, hg, hx, mul_inv_eq_iff_eq_mul, weylA_mul_lam]
  have h := mul_comm_of_tauS hθ hC ht0 ht1 ⟨0, a₁, hconj h₁⟩ ⟨0, a₂, hconj h₂⟩
  have h' : g * (x₁ * x₂) * g⁻¹ = g * (x₂ * x₁) * g⁻¹ := by
    calc g * (x₁ * x₂) * g⁻¹ = (g * x₁ * g⁻¹) * (g * x₂ * g⁻¹) := by group
      _ = (g * x₂ * g⁻¹) * (g * x₁ * g⁻¹) := h
      _ = g * (x₂ * x₁) * g⁻¹ := by group
  simpa using h'

include hθ hC in
theorem mul_comm_of_tauS_d {t : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1) {y₁ y₂ : E} {d₁ d₂ : K}
    (h₁ : θ y₁ = tauS 0 0 d₁) (h₂ : θ y₂ = tauS 0 0 d₂) : y₁ * y₂ = y₂ * y₁ := by
  obtain ⟨g, hg⟩ := hθ (weylD K)
  have hconj : ∀ {y : E} {d : K}, θ y = tauS 0 0 d → θ (g * y * g⁻¹) = tauS d 0 0 := fun hy => by
    rw [map_mul, map_mul, map_inv, hg, hy, mul_inv_eq_iff_eq_mul, weylD_mul_tauS]
  have h := mul_comm_of_tauS hθ hC ht0 ht1 ⟨d₁, 0, hconj h₁⟩ ⟨d₂, 0, hconj h₂⟩
  have h' : g * (y₁ * y₂) * g⁻¹ = g * (y₂ * y₁) * g⁻¹ := by
    calc g * (y₁ * y₂) * g⁻¹ = (g * y₁ * g⁻¹) * (g * y₂ * g⁻¹) := by group
      _ = (g * y₂ * g⁻¹) * (g * y₁ * g⁻¹) := h
      _ = g * (y₂ * y₁) * g⁻¹ := by group
  simpa using h'

include hθ hC in
theorem ker_eq_bot_of_statedSp [Finite K] (hK : 3 ≤ Nat.card K) [Finite E] [Group.IsPerfect E]
    (h2 : IsPGroup 2 θ.ker) : θ.ker = ⊥ := by
  obtain ⟨t, ht0, ht1⟩ := LinearCover.exists_ne_zero_ne_one_of_three_le (K := K) hK
  have comm_eq : ∀ {x x' y y' : E}, θ x = θ x' → θ y = θ y' → ⁅x, y⁆ = ⁅x', y'⁆ :=
    fun hx hy => LinearCover.HeisenbergRoots.commutatorElement_eq_of_map_eq θ (fun z hz => hC hz)
      hx hy
  have hWcomm : ∀ {z₁ z₂ : E}, (∃ b c, θ z₁ = tauS b c 0) → (∃ b c, θ z₂ = tauS b c 0) →
      z₁ * z₂ = z₂ * z₁ := fun h₁ h₂ => mul_comm_of_tauS hθ hC ht0 ht1 h₁ h₂
  have hWU : ∀ {z g : E}, (∃ b c, θ z = tauS b c 0) → θ g ∈ unipotent 2 K → z * g = g * z :=
    fun hz hg => mul_comm_of_tauS_of_mem_unipotent hθ hC ht0 ht1 hz hg
  obtain ⟨la, hla⟩ : ∃ la : K → E, ∀ a, θ (la a) = lam a :=
    ⟨fun a => Function.surjInv hθ (lam a), fun a => Function.surjInv_eq hθ _⟩
  obtain ⟨ld, hld⟩ : ∃ ld : K → E, ∀ d, θ (ld d) = tauS 0 0 d :=
    ⟨fun d => Function.surjInv hθ (tauS 0 0 d), fun d => Function.surjInv_eq hθ _⟩
  have hlaU : ∀ a, θ (la a) ∈ unipotent 2 K := fun a => (hla a) ▸ lam_mem_unipotent a
  have hldU : ∀ d, θ (ld d) ∈ unipotent 2 K := fun d => (hld d) ▸ tauS_mem_unipotent 0 0 d
  obtain ⟨γ, hγdef⟩ : ∃ γ : K → K → E, ∀ a d, γ a d = ⁅la a, ld d⁆ :=
    ⟨fun a d => ⁅la a, ld d⁆, fun _ _ => rfl⟩
  have hγW : ∀ a d, ∃ b c, θ (γ a d) = tauS b c 0 := fun a d =>
    ⟨_, _, by rw [hγdef, map_commutatorElement, hla, hld, commutatorElement_lam_tauS]⟩
  have hγ_add : ∀ a a' d, γ (a + a') d = γ a d * γ a' d := fun a a' d => by
    rw [hγdef, hγdef, hγdef, comm_eq (x' := la a * la a') (by rw [hla, map_mul, hla, hla, lam_mul])
      rfl, LinearCover.commutatorElement_mul_left_eq, ← hγdef a' d, ← hWU (hγW a' d) (hlaU a),
      mul_inv_cancel_right, ← hγdef a d]
    exact hWcomm (hγW a' d) (hγW a d)
  obtain ⟨g, hg⟩ := hθ (SymplecticTorusWeyl.torusHom ![Units.mk0 t ht0, 1])
  set φ := MulAut.conj g with hφdef
  have hφC : ∀ z ∈ θ.ker, φ z = z := fun z hz => by
    rw [hφdef, MulAut.conj_apply, Subgroup.mem_center_iff.mp (hC hz) g, mul_inv_cancel_right]
  have hφγ : ∀ a d, φ (γ a d) = γ (t * a) d := fun a d => by
    rw [hγdef, hγdef, hφdef, MulAut.conj_apply]
    have h : g * ⁅la a, ld d⁆ * g⁻¹ = ⁅g * la a * g⁻¹, g * ld d * g⁻¹⁆ := by
      simp only [commutatorElement_def]
      group
    rw [h]
    exact comm_eq (by rw [map_mul, map_mul, map_inv, hg, hla, torusHom_first_conj_lam,
      Units.val_mk0, hla]) (by rw [map_mul, map_mul, map_inv, hg, hld, torusHom_first_conj_tauS,
      mul_zero, mul_zero])
  have := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  rw [← Nat.card_eq_fintype_card] at hn
  have hm : Odd (Nat.card K - 1) := by
    rw [hn]
    exact Nat.Even.sub_odd Nat.one_le_two_pow ((Nat.even_pow' n.ne_zero).mpr even_two) odd_one
  have hφm : φ ^ (Nat.card K - 1) = 1 := by
    have ht : (![Units.mk0 t ht0, 1] : Fin 2 → Kˣ) ^ (Nat.card K - 1) = 1 := by
      funext i
      rw [Pi.pow_apply, Pi.one_apply, ← Nat.card_units]
      exact pow_card_eq_one'
    have hz : g ^ (Nat.card K - 1) ∈ Subgroup.center E := hC (by
      rw [MonoidHom.mem_ker, map_pow, hg, ← map_pow, ht, map_one])
    rw [hφdef, ← map_pow]
    ext x
    rw [MulAut.conj_apply, ← Subgroup.mem_center_iff.mp hz x, mul_inv_cancel_right,
      MulAut.one_apply]
  set D : Subgroup E := Subgroup.closure (Set.range fun p : K × K => γ p.1 p.2)
  have hDW : ∀ r ∈ D, ∃ b c, θ r = tauS b c 0 := by
    intro r hr
    induction hr using Subgroup.closure_induction with
    | mem s hs =>
      obtain ⟨p, rfl⟩ := hs
      exact hγW p.1 p.2
    | one => exact ⟨0, 0, by rw [map_one, tauS_zero]⟩
    | mul r₁ r₂ _ _ ih₁ ih₂ =>
      obtain ⟨b₁, c₁, h₁⟩ := ih₁
      obtain ⟨b₂, c₂, h₂⟩ := ih₂
      exact ⟨b₁ + b₂, c₁ + c₂, by rw [map_mul, h₁, h₂, tauS_mul_tauS, add_zero]⟩
    | inv r _ ih =>
      obtain ⟨b, c, h⟩ := ih
      exact ⟨-b, -c, by rw [map_inv, h, tauS_inv, neg_zero]⟩
  have hDcomm : ∀ r₁ ∈ D, ∀ r₂ ∈ D, r₁ * r₂ = r₂ * r₁ := fun r₁ h₁ r₂ h₂ =>
    hWcomm (hDW r₁ h₁) (hDW r₂ h₂)
  have hψ : ∀ z ∈ D, ∃ y ∈ D, z = φ y * y⁻¹ := by
    have hr : t - 1 ≠ 0 := sub_ne_zero.mpr ht1
    intro z hz
    induction hz using Subgroup.closure_induction with
    | mem s hs =>
      obtain ⟨⟨a, d⟩, rfl⟩ := hs
      refine ⟨γ ((t - 1)⁻¹ * a) d, Subgroup.subset_closure ⟨((t - 1)⁻¹ * a, d), rfl⟩, ?_⟩
      rw [hφγ, show t * ((t - 1)⁻¹ * a) = a + (t - 1)⁻¹ * a by field_simp; ring, hγ_add,
        mul_inv_cancel_right]
    | one => exact ⟨1, one_mem _, by rw [map_one, inv_one, mul_one]⟩
    | mul z₁ z₂ hz₁ hz₂ ih₁ ih₂ =>
      obtain ⟨y₁, hy₁, rfl⟩ := ih₁
      obtain ⟨y₂, hy₂, rfl⟩ := ih₂
      refine ⟨y₁ * y₂, mul_mem hy₁ hy₂, ?_⟩
      have hc : y₁⁻¹ * (φ y₂ * y₂⁻¹) = (φ y₂ * y₂⁻¹) * y₁⁻¹ :=
        hDcomm _ (inv_mem hy₁) _ hz₂
      rw [map_mul, _root_.mul_inv_rev]
      calc φ y₁ * y₁⁻¹ * (φ y₂ * y₂⁻¹) = φ y₁ * (y₁⁻¹ * (φ y₂ * y₂⁻¹)) := by group
        _ = φ y₁ * ((φ y₂ * y₂⁻¹) * y₁⁻¹) := by rw [hc]
        _ = φ y₁ * φ y₂ * (y₂⁻¹ * y₁⁻¹) := by group
    | inv z hz ih =>
      obtain ⟨y, hy, rfl⟩ := ih
      refine ⟨y⁻¹, inv_mem hy, ?_⟩
      rw [map_inv, inv_inv, _root_.mul_inv_rev, inv_inv]
      exact hDcomm _ hy _ (inv_mem (show φ y ∈ D from by
        have := mul_mem hz hy
        rwa [inv_mul_cancel_right] at this))
  set X : Set E := {z | ∃ b c, θ z = tauS b c 0} ∪ Set.range la ∪ Set.range ld
  have hXU : ∀ s ∈ Subgroup.closure X, θ s ∈ unipotent 2 K := by
    intro s hs
    have hle : Subgroup.closure X ≤ (unipotent 2 K).comap θ := by
      rw [Subgroup.closure_le]
      rintro x ((⟨b, c, hx⟩ | ⟨a, rfl⟩) | ⟨d, rfl⟩)
      · exact show θ x ∈ unipotent 2 K from hx ▸ tauS_mem_unipotent b c 0
      · exact hlaU a
      · exact hldU d
    exact hle hs
  have hUX : ∀ x, θ x ∈ unipotent 2 K → x ∈ Subgroup.closure X := by
    intro x hx
    obtain ⟨C, hC', a, hxa⟩ := mem_unipotent_iff.mp hx
    rw [tau_eq_tauS] at hxa
    have hw : θ (x * (ld (C 1 1) * la a)⁻¹) = tauS (C 0 0) (C 0 1) 0 := by
      rw [map_mul, map_inv, mul_inv_eq_iff_eq_mul, map_mul, hld, hla, hxa, ← mul_assoc,
        tauS_mul_tauS]
      simp only [add_zero, zero_add]
    have hx' : x = x * (ld (C 1 1) * la a)⁻¹ * ld (C 1 1) * la a := by group
    rw [hx']
    exact mul_mem (mul_mem (Subgroup.subset_closure (Or.inl (Or.inl ⟨_, _, hw⟩)))
      (Subgroup.subset_closure (Or.inr ⟨_, rfl⟩)))
      (Subgroup.subset_closure (Or.inl (Or.inr ⟨_, rfl⟩)))
  have hnorm : ∀ x ∈ Subgroup.closure X, ∀ r ∈ D, x * r * x⁻¹ ∈ D := fun x hx r hr => by
    rw [← hWU (hDW r hr) (hXU x hx), mul_inv_cancel_right]
    exact hr
  have hX : ∀ s ∈ X, ∀ s' ∈ X, ⁅s, s'⁆ ∈ D := by
    intro s hs s' hs'
    have hsU := hXU s (Subgroup.subset_closure hs)
    have hs'U := hXU s' (Subgroup.subset_closure hs')
    rcases hs' with (hs'W | ⟨a', rfl⟩) | ⟨d', rfl⟩
    · rw [commutatorElement_eq_one_iff_mul_comm.mpr (hWU hs'W hsU).symm]
      exact one_mem _
    · rcases hs with (hsW | ⟨a, rfl⟩) | ⟨d, rfl⟩
      · rw [commutatorElement_eq_one_iff_mul_comm.mpr (hWU hsW hs'U)]
        exact one_mem _
      · rw [commutatorElement_eq_one_iff_mul_comm.mpr
          (mul_comm_of_lam hθ hC ht0 ht1 (hla a) (hla a'))]
        exact one_mem _
      · rw [← commutatorElement_inv, ← hγdef]
        exact inv_mem (Subgroup.subset_closure ⟨(a', d), rfl⟩)
    · rcases hs with (hsW | ⟨a, rfl⟩) | ⟨d, rfl⟩
      · rw [commutatorElement_eq_one_iff_mul_comm.mpr (hWU hsW hs'U)]
        exact one_mem _
      · rw [← hγdef]
        exact Subgroup.subset_closure ⟨(a, d'), rfl⟩
      · rw [commutatorElement_eq_one_iff_mul_comm.mpr
          (mul_comm_of_tauS_d hθ hC ht0 ht1 (hld d) (hld d'))]
        exact one_mem _
  obtain ⟨S, hS⟩ := SymplecticFlag.exists_sylow_unipotent (K := K) 2 2
  obtain ⟨P, hP, hzP⟩ := LinearCover.exists_sylow_map_eq_twoPart_le θ hθ hC S
  have hPX : ∀ x ∈ (P : Subgroup E), x ∈ Subgroup.closure X := fun x hx =>
    hUX x (by rw [← hS, ← hP]; exact Subgroup.mem_map_of_mem _ hx)
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  obtain ⟨k, hk⟩ := h2 ⟨z, hz⟩
  have hk' : z ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hzD : z ∈ D := (Subgroup.commutator_le.mpr fun g₁ hg₁ g₂ hg₂ =>
    LinearCover.commutatorElement_mem_of_mem_closure hnorm hX (hPX g₁ hg₁) (hPX g₂ hg₂))
    (hzP z hz ⟨k, hk'⟩)
  obtain ⟨y, -, hzy⟩ := hψ z hzD
  have hm1 := LinearCover.pow_apply_eq_of_conj_fixed (hφC z hz) hzy (Nat.card K - 1)
  rw [hφm, MulAut.one_apply] at hm1
  have hzm : z ^ (Nat.card K - 1) = 1 := mul_eq_right.mp hm1.symm
  have hcop : Nat.Coprime (Nat.card K - 1) (2 ^ k) := Nat.Coprime.pow_right k hm.coprime_two_right
  have h := pow_gcd_eq_one.mpr ⟨hzm, hk'⟩
  rwa [hcop.gcd_eq_one, pow_one] at h

end Cover

end CFSG.LocalAnalysis.ComponentInitial.SymplecticCoverFour
