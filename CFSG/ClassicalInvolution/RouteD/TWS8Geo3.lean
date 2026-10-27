module

public import CFSG.ClassicalInvolution.RouteD.TWS8Geo2

public section

namespace CFSG.ClassicalInvolution.RouteD.TWS8

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.ClassicalGroups.Orthogonal.Small (stabSub)
open scoped MatrixGroups

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

section Proj

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

@[expose] def pA (fr : OFrame Q) : V →ₗ[F] V := LinearMap.id - fr.incl ∘ₗ fr.coords

@[expose] def pW (fr : OFrame Q) : V →ₗ[F] V := fr.incl ∘ₗ fr.coords

theorem pA_apply (fr : OFrame Q) (x : V) : pA fr x = x - fr.incl (fr.coords x) := rfl

theorem pW_apply (fr : OFrame Q) (x : V) : pW fr x = fr.incl (fr.coords x) := rfl

theorem pW_add_pA (fr : OFrame Q) (x : V) : pW fr x + pA fr x = x := by
  rw [pA_apply, pW_apply]
  abel

theorem pA_mem_perp (fr : OFrame Q) (x : V) : pA fr x ∈ fr.perp := sub_incl_mem_perp fr x

theorem pW_mem (fr : OFrame Q) (x : V) : pW fr x ∈ wPlane fr := incl_mem_wPlane fr _

theorem pW_of_mem {fr : OFrame Q} {x : V} (hx : x ∈ wPlane fr) : pW fr x = x := by
  rw [pW_apply]
  exact (mem_wPlane.mp hx).symm

theorem pA_of_mem {fr : OFrame Q} {x : V} (hx : x ∈ wPlane fr) : pA fr x = 0 := by
  rw [pA_apply, ← mem_wPlane.mp hx, sub_self]

theorem mem_wPlane_of_pA_eq_zero {fr : OFrame Q} {x : V} (hx : pA fr x = 0) : x ∈ wPlane fr := by
  rw [pA_apply, sub_eq_zero] at hx
  exact mem_wPlane.mpr hx

theorem pA_eq_zero_iff (fr : OFrame Q) {x : V} : pA fr x = 0 ↔ x ∈ wPlane fr :=
  ⟨mem_wPlane_of_pA_eq_zero, pA_of_mem⟩

theorem polar_eq_pW {fr : OFrame Q} {x : V} (hx : x ∈ wPlane fr) (y : V) :
    polar Q x y = polar Q x (pW fr y) := by
  have h1 : polar Q x (pA fr y) = 0 := polar_wPlane_perp (pA_mem_perp fr y) hx
  have h2 := pW_add_pA fr y
  calc polar Q x y = polar Q x (pW fr y + pA fr y) := by rw [h2]
    _ = polar Q x (pW fr y) := by rw [polar_add_right, h1, add_zero]

theorem e₁_ne_zero (fr : OFrame Q) : fr.e₁ ≠ 0 := fun h => by
  have := fr.polar_e₁_f₁
  rw [h] at this
  simp at this

theorem e₂_ne_zero (fr : OFrame Q) : fr.e₂ ≠ 0 := fun h => by
  have := fr.polar_e₂_f₂
  rw [h] at this
  simp at this

theorem e₂_mem_wPlane (fr : OFrame Q) : fr.e₂ ∈ wPlane fr :=
  ⟨!![0, -1; 0, 0], by simp [Frame.incl_apply]⟩

theorem incl_ne_zero (fr : OFrame Q) {X : Matrix (Fin 2) (Fin 2) F} (hX : X ≠ 0) :
    fr.incl X ≠ 0 := fun h => hX (by rw [← Frame.coords_incl fr X, h, map_zero])

theorem exists_singular_orth (fr : OFrame Q) (v : V) :
    ∃ s ∈ wPlane fr, Q s = 0 ∧ s ≠ 0 ∧ polar Q s v = 0 := by
  by_cases h1 : polar Q v fr.e₁ = 0
  · refine ⟨fr.e₁, e₁_mem_wPlane fr, fr.Q_e₁, e₁_ne_zero fr, ?_⟩
    rw [polar_comm]
    exact h1
  · set b₁ := polar Q v fr.e₁ with hb₁
    set b₂ := polar Q v fr.e₂ with hb₂
    refine ⟨fr.incl !![-b₂, -b₁; 0, 0], incl_mem_wPlane fr _, ?_, ?_, ?_⟩
    · rw [Frame.Q_incl]
      simp [Matrix.det_fin_two]
    · refine incl_ne_zero fr fun h => h1 ?_
      have := congrFun (congrFun h 0) 1
      simpa using this
    · rw [polar_comm, Frame.polar_incl_right]
      simp [Frame.coords_apply, hb₁, hb₂]
      ring

end Proj

section Conj

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

theorem pA_conj_eichler (fr : OFrame Q) {h : V ≃ₗ[F] V}
    (hO : h ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {s w x : V} (hs : Q s = 0)
    (hsw : polar Q s w = 0) (hx : x ∈ wPlane fr) :
    pA fr ((h * eichler Q s w * h⁻¹) x) =
      polar Q x (h s) • pA fr (h w) -
        (polar Q x (h w) + Q w * polar Q x (h s)) • pA fr (h s) := by
  have hhs : Q (h s) = 0 := by rw [map_of_mem hO, hs]
  have hhsw : polar Q (h s) (h w) = 0 := by rw [polar_map_of_mem hO, hsw]
  rw [eichler_conj hO, eichler_apply hhs hhsw, map_sub, map_add, map_smul, map_smul,
    map_of_mem hO, pA_of_mem hx, zero_add]

@[expose] def NoTotSing (Q : QuadraticForm F V) (A : Submodule F V) : Prop :=
  ∀ u ∈ A, ∀ v ∈ A, Q u = 0 → Q v = 0 → polar Q u v = 0 → u = 0 ∨ ∃ c : F, v = c • u

end Conj

section Fix2

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}
  [FiniteDimensional F V]

omit [FiniteDimensional F V] in
theorem exists_ne_zero_orth_two (fr : OFrame Q) (u₁ u₂ : V) :
    ∃ y ∈ wPlane fr, y ≠ 0 ∧ polar Q y u₁ = 0 ∧ polar Q y u₂ = 0 := by
  let f : Matrix (Fin 2) (Fin 2) F →ₗ[F] F × F :=
    LinearMap.prod ((polarBilin Q).flip u₁ ∘ₗ fr.incl) ((polarBilin Q).flip u₂ ∘ₗ fr.incl)
  have hlt : Module.finrank F (F × F) < Module.finrank F (Matrix (Fin 2) (Fin 2) F) := by
    simp [Module.finrank_prod, Module.finrank_matrix]
  obtain ⟨X, hX, hX0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (LinearMap.ker_ne_bot_of_finrank_lt hlt (f := f))
  have hX' := LinearMap.mem_ker.mp hX
  refine ⟨fr.incl X, incl_mem_wPlane fr X, incl_ne_zero fr hX0, ?_, ?_⟩
  · have := congrArg Prod.fst hX'
    simpa [f] using this
  · have := congrArg Prod.snd hX'
    simpa [f] using this

theorem exists_kernel_of_finrank (fr : OFrame Q) (h : V ≃ₗ[F] V)
    (hA : Module.finrank F fr.perp < 4) : ∃ w ∈ wPlane fr, w ≠ 0 ∧ h w ∈ wPlane fr := by
  let φ : Matrix (Fin 2) (Fin 2) F →ₗ[F] fr.perp :=
    ((pA fr) ∘ₗ (h : V →ₗ[F] V) ∘ₗ fr.incl).codRestrict fr.perp (fun X => pA_mem_perp fr _)
  have hlt : Module.finrank F fr.perp < Module.finrank F (Matrix (Fin 2) (Fin 2) F) := by
    simpa [Module.finrank_matrix] using hA
  obtain ⟨X, hX, hX0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (LinearMap.ker_ne_bot_of_finrank_lt hlt (f := φ))
  refine ⟨fr.incl X, incl_mem_wPlane fr X, incl_ne_zero fr hX0, ?_⟩
  have := congrArg Subtype.val (LinearMap.mem_ker.mp hX)
  exact mem_wPlane_of_pA_eq_zero (by simpa [φ] using this)

theorem exists_fix_of_singular_kernel (hQ : (polarBilin Q).Nondegenerate) (fr : OFrame Q)
    {H : Subgroup (V ≃ₗ[F] V)} (hH : stabE fr ≤ H) (hHE : H ≤ elementaryGroup Q)
    {h : V ≃ₗ[F] V} (hh : h ∈ H) (hhW : ¬ ∀ x ∈ wPlane fr, h x ∈ wPlane fr) {s₀ : V}
    (hs₀W : s₀ ∈ wPlane fr) (hs₀Q : Q s₀ = 0) (hs₀ : s₀ ≠ 0) (hhs₀ : h s₀ ∈ wPlane fr) :
    ∃ k ∈ H, k fr.e₁ = fr.e₁ ∧ ¬ ∀ x ∈ wPlane fr, k x ∈ wPlane fr := by
  have hO : h ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    elementaryGroup_le_orthogonalGroup Q (hHE hh)
  obtain ⟨g₀, hg₀, hg₀e⟩ := exists_stabE_apply_eq hQ fr (e₁_mem_wPlane fr) hs₀W (e₁_ne_zero fr)
    hs₀ (by rw [fr.Q_e₁, hs₀Q])
  have hx₁0 : h s₀ ≠ 0 := fun h0 => hs₀ (h.injective (by rw [h0, map_zero]))
  obtain ⟨g₁, hg₁, hg₁e⟩ := exists_stabE_apply_eq hQ fr hhs₀ (e₁_mem_wPlane fr) hx₁0
    (e₁_ne_zero fr) (by rw [map_of_mem hO, hs₀Q, fr.Q_e₁])
  refine ⟨g₁ * h * g₀, H.mul_mem (H.mul_mem (hH hg₁) hh) (hH hg₀), ?_, ?_⟩
  · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hg₀e, hg₁e]
  · intro hall
    apply hhW
    intro y hy
    have hy' : g₀⁻¹ y ∈ wPlane fr := by
      have := (mem_stabE.mp hg₀).2 (g₀⁻¹ y)
      rw [LinearEquiv.apply_inv_apply'] at this
      exact this.mpr hy
    have h2 := hall _ hy'
    simp only [LinearEquiv.mul_apply, LinearEquiv.apply_inv_apply'] at h2
    exact ((mem_stabE.mp hg₁).2 (h y)).mpr h2

omit [FiniteDimensional F V] in
theorem exists_singular_kernel (hQ : (polarBilin Q).Nondegenerate) (fr : OFrame Q)
    {H : Subgroup (V ≃ₗ[F] V)} (hH : stabE fr ≤ H) (hHE : H ≤ elementaryGroup Q)
    (h2 : (2 : F) ≠ 0) {h : V ≃ₗ[F] V} (hh : h ∈ H)
    (hhW : ¬ ∀ x ∈ wPlane fr, h x ∈ wPlane fr) {w₀ : V} (hw₀ : w₀ ∈ wPlane fr) (hw₀0 : w₀ ≠ 0)
    (hhw₀ : h w₀ ∈ wPlane fr) :
    ∃ h' ∈ H, (¬ ∀ x ∈ wPlane fr, h' x ∈ wPlane fr) ∧
      ∃ s ∈ wPlane fr, Q s = 0 ∧ s ≠ 0 ∧ h' s ∈ wPlane fr := by
  have hO : h ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    elementaryGroup_le_orthogonalGroup Q (hHE hh)
  by_cases hq : Q w₀ = 0
  · exact ⟨h, hh, hhW, w₀, hw₀, hq, hw₀0, hhw₀⟩
  obtain ⟨s, hsW, hsQ, hs0, hsw⟩ := exists_singular_orth fr w₀
  by_cases hhs : h s ∈ wPlane fr
  · exact ⟨h, hh, hhW, s, hsW, hsQ, hs0, hhs⟩
  have hpA_hs : pA fr (h s) ≠ 0 := fun h0 => hhs (mem_wPlane_of_pA_eq_zero h0)
  have hpA_w₀ : pA fr (h w₀) = 0 := pA_of_mem hhw₀
  have hne : h w₀ ≠ 0 := fun h0 => hw₀0 (h.injective (by rw [h0, map_zero]))
  have ht : ∃ t : F, t ≠ 0 ∧ pW fr (h w₀ + (t * Q w₀) • h s) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h1 := hcon 1 one_ne_zero
    have h2' := hcon 2 h2
    rw [map_add, map_smul, pW_of_mem hhw₀] at h1 h2'
    have h3 : (Q w₀) • pW fr (h s) = 0 := by
      calc (Q w₀) • pW fr (h s) = (h w₀ + (2 * Q w₀) • pW fr (h s)) -
          (h w₀ + (1 * Q w₀) • pW fr (h s)) := by module
        _ = 0 := sub_eq_zero.mpr (h2'.trans h1.symm)
    have h4 : pW fr (h s) = 0 := (smul_eq_zero.mp h3).resolve_left hq
    rw [h4, smul_zero, add_zero] at h1
    exact hne h1
  obtain ⟨t, ht0, htW⟩ := ht
  have hh' : h * eichler Q s (t • w₀) * h⁻¹ ∈ H :=
    H.mul_mem (H.mul_mem hh (hH (eichler_mem_stabE fr hsW ((wPlane fr).smul_mem t hw₀))))
      (H.inv_mem hh)
  have hformula : ∀ x ∈ wPlane fr, pA fr ((h * eichler Q s (t • w₀) * h⁻¹) x) =
      (-(t * polar Q x (h w₀ + (t * Q w₀) • h s))) • pA fr (h s) := by
    intro x hx
    have hsw' : polar Q s (t • w₀) = 0 := by rw [polar_smul_right_eq, hsw, mul_zero]
    rw [pA_conj_eichler fr hO hsQ hsw' hx]
    have e1 : pA fr (h (t • w₀)) = 0 := by rw [map_smul, map_smul, hpA_w₀, smul_zero]
    have e2 : polar Q x (h (t • w₀)) = t * polar Q x (h w₀) := by
      rw [map_smul, polar_smul_right_eq]
    have e3 : Q (t • w₀) = t * t * Q w₀ := by rw [QuadraticMap.map_smul, smul_eq_mul]
    have e4 : polar Q x (h w₀ + (t * Q w₀) • h s) =
        polar Q x (h w₀) + t * Q w₀ * polar Q x (h s) := by
      rw [polar_add_right, polar_smul_right_eq]
    rw [e1, e2, e3, e4, smul_zero, zero_sub, ← neg_smul]
    congr 1
    ring
  obtain ⟨x₁, hx₁, hx₁v⟩ : ∃ x ∈ wPlane fr, polar Q x (h w₀ + (t * Q w₀) • h s) ≠ 0 := by
    obtain ⟨y, hy, hy1⟩ := (polarNondegOn_wPlane hQ fr).exists_polar_ne_zero (pW_mem fr _) htW
    refine ⟨y, hy, ?_⟩
    rw [polar_eq_pW hy, polar_comm]
    exact hy1
  refine ⟨_, hh', ?_, ?_⟩
  · intro hall
    have h0 := (pA_eq_zero_iff fr).mpr (hall x₁ hx₁)
    rw [hformula x₁ hx₁] at h0
    exact smul_ne_zero (neg_ne_zero.mpr (mul_ne_zero ht0 hx₁v)) hpA_hs h0
  · obtain ⟨y, hyW, hyQ, hy0, hyv⟩ := exists_singular_orth fr (h w₀ + (t * Q w₀) • h s)
    refine ⟨y, hyW, hyQ, hy0, mem_wPlane_of_pA_eq_zero ?_⟩
    rw [hformula y hyW, hyv, mul_zero, neg_zero, zero_smul]

omit [FiniteDimensional F V] in
theorem core_c (hQ : (polarBilin Q).Nondegenerate) (fr : OFrame Q) {H : Subgroup (V ≃ₗ[F] V)}
    (hH : stabE fr ≤ H) (hHE : H ≤ elementaryGroup Q) {h : V ≃ₗ[F] V} (hh : h ∈ H)
    (hker : ∀ x ∈ wPlane fr, h x ∈ wPlane fr → x = 0) {s w : V} (hsW : s ∈ wPlane fr)
    (hwW : w ∈ wPlane fr) (hs : Q s = 0) (hw : Q w = 0) (hsw : polar Q s w = 0)
    (hind : ∀ a b : F, a • s + b • w = 0 → a = 0 ∧ b = 0)
    (hα : pW fr (h s) ≠ 0 ∨ pW fr (h w) ≠ 0) :
    ∃ h' ∈ H, (¬ ∀ x ∈ wPlane fr, h' x ∈ wPlane fr) ∧
      ∃ y ∈ wPlane fr, y ≠ 0 ∧ h' y ∈ wPlane fr := by
  have hO : h ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    elementaryGroup_le_orthogonalGroup Q (hHE hh)
  have hp : eichler Q s w ∈ H := hH (eichler_mem_stabE fr hsW hwW)
  have hh' : h * eichler Q s w * h⁻¹ ∈ H := H.mul_mem (H.mul_mem hh hp) (H.inv_mem hh)
  have key : ∀ x ∈ wPlane fr, pA fr ((h * eichler Q s w * h⁻¹) x) =
      pA fr (h (polar Q x (h s) • w - polar Q x (h w) • s)) := by
    intro x hx
    rw [pA_conj_eichler fr hO hs hsw hx]
    simp [hw]
  have hex : ∃ x ∈ wPlane fr, polar Q x (h s) ≠ 0 ∨ polar Q x (h w) ≠ 0 := by
    rcases hα with h1 | h1
    · obtain ⟨y, hy, hy1⟩ := (polarNondegOn_wPlane hQ fr).exists_polar_ne_zero (pW_mem fr _) h1
      refine ⟨y, hy, Or.inl ?_⟩
      rw [polar_eq_pW hy, polar_comm]
      exact hy1
    · obtain ⟨y, hy, hy1⟩ := (polarNondegOn_wPlane hQ fr).exists_polar_ne_zero (pW_mem fr _) h1
      refine ⟨y, hy, Or.inr ?_⟩
      rw [polar_eq_pW hy, polar_comm]
      exact hy1
  refine ⟨_, hh', ?_, ?_⟩
  · obtain ⟨x, hx, hx1⟩ := hex
    intro hall
    have h0 := (pA_eq_zero_iff fr).mpr (hall x hx)
    rw [key x hx] at h0
    have hW : polar Q x (h s) • w - polar Q x (h w) • s ∈ wPlane fr :=
      (wPlane fr).sub_mem ((wPlane fr).smul_mem _ hwW) ((wPlane fr).smul_mem _ hsW)
    have h00 := hker _ hW (mem_wPlane_of_pA_eq_zero h0)
    have h01 := hind (-polar Q x (h w)) (polar Q x (h s)) (by
      calc (-polar Q x (h w)) • s + polar Q x (h s) • w =
          polar Q x (h s) • w - polar Q x (h w) • s := by module
        _ = 0 := h00)
    rcases hx1 with hx1 | hx1
    · exact hx1 h01.2
    · exact hx1 (neg_eq_zero.mp h01.1)
  · obtain ⟨y, hyW, hy0, hy1, hy2⟩ := exists_ne_zero_orth_two fr (h s) (h w)
    refine ⟨y, hyW, hy0, mem_wPlane_of_pA_eq_zero ?_⟩
    rw [key y hyW, hy1, hy2, zero_smul, zero_smul, sub_zero, map_zero, map_zero]

omit [FiniteDimensional F V] in
theorem exists_kernel_of_inj (hQ : (polarBilin Q).Nondegenerate) (fr : OFrame Q)
    {H : Subgroup (V ≃ₗ[F] V)} (hH : stabE fr ≤ H) (hHE : H ≤ elementaryGroup Q)
    (hNo : NoTotSing Q fr.perp) {h : V ≃ₗ[F] V} (hh : h ∈ H)
    (hker : ∀ x ∈ wPlane fr, h x ∈ wPlane fr → x = 0) :
    ∃ h' ∈ H, (¬ ∀ x ∈ wPlane fr, h' x ∈ wPlane fr) ∧
      ∃ y ∈ wPlane fr, y ≠ 0 ∧ h' y ∈ wPlane fr := by
  have hO : h ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    elementaryGroup_le_orthogonalGroup Q (hHE hh)
  have hind12 : ∀ a b : F, a • fr.e₁ + b • fr.e₂ = 0 → a = 0 ∧ b = 0 := by
    intro a b hab
    have h1 := congrArg (fun y => polar Q y fr.f₁) hab
    have h2 := congrArg (fun y => polar Q y fr.f₂) hab
    simp only [polar_add_left, polar_smul_left, fr.polar_e₁_f₁, fr.polar_e₂_f₁, fr.polar_e₁_f₂,
      fr.polar_e₂_f₂, polar_zero_left, smul_eq_mul] at h1 h2
    constructor
    · simpa using h1
    · simpa using h2
  have hind21 : ∀ a b : F, a • fr.e₂ + b • fr.e₁ = 0 → a = 0 ∧ b = 0 := fun a b hab =>
    (hind12 b a (by rw [add_comm]; exact hab)).symm
  by_cases h1 : pW fr (h fr.e₁) = 0
  · by_cases h2 : pW fr (h fr.e₂) = 0
    · exfalso
      have hA1 : h fr.e₁ ∈ fr.perp := by
        have := pW_add_pA fr (h fr.e₁)
        rw [h1, zero_add] at this
        rw [← this]
        exact pA_mem_perp fr _
      have hA2 : h fr.e₂ ∈ fr.perp := by
        have := pW_add_pA fr (h fr.e₂)
        rw [h2, zero_add] at this
        rw [← this]
        exact pA_mem_perp fr _
      rcases hNo _ hA1 _ hA2 (by rw [map_of_mem hO, fr.Q_e₁]) (by rw [map_of_mem hO, fr.Q_e₂])
        (by rw [polar_map_of_mem hO, fr.polar_e₁_e₂]) with h0 | ⟨c, hc⟩
      · exact e₁_ne_zero fr (h.injective (by rw [h0, map_zero]))
      · have h3 : fr.e₂ = c • fr.e₁ := h.injective (by rw [map_smul]; exact hc)
        have h4 := hind12 (-c) 1 (by rw [one_smul, neg_smul, h3]; abel)
        exact one_ne_zero h4.2
    · exact core_c hQ fr hH hHE hh hker (s := fr.e₂) (w := fr.e₁) (e₂_mem_wPlane fr)
        (e₁_mem_wPlane fr) fr.Q_e₂ fr.Q_e₁ fr.polar_e₂_e₁ hind21 (Or.inl h2)
  · exact core_c hQ fr hH hHE hh hker (s := fr.e₁) (w := fr.e₂) (e₁_mem_wPlane fr)
      (e₂_mem_wPlane fr) fr.Q_e₁ fr.Q_e₂ fr.polar_e₁_e₂ hind12 (Or.inl h1)

theorem exists_fix [Finite F] (hodd : Odd (Nat.card F)) (hQ : (polarBilin Q).Nondegenerate)
    (fr : OFrame Q) {H : Subgroup (V ≃ₗ[F] V)} (hH : stabE fr ≤ H) (hHE : H ≤ elementaryGroup Q)
    (hA : Module.finrank F fr.perp < 4 ∨ NoTotSing Q fr.perp) {h : V ≃ₗ[F] V} (hh : h ∈ H)
    (hhW : ¬ ∀ x ∈ wPlane fr, h x ∈ wPlane fr) :
    ∃ k ∈ H, k fr.e₁ = fr.e₁ ∧ ¬ ∀ x ∈ wPlane fr, k x ∈ wPlane fr := by
  have h2 : (2 : F) ≠ 0 := CFSG.ClassicalInvolution.ModelFacts.Orth15.two_ne_zero_of_odd_card hodd
  have step1 : ∃ h₁ ∈ H, (¬ ∀ x ∈ wPlane fr, h₁ x ∈ wPlane fr) ∧
      ∃ w ∈ wPlane fr, w ≠ 0 ∧ h₁ w ∈ wPlane fr := by
    by_cases hker : ∃ w ∈ wPlane fr, w ≠ 0 ∧ h w ∈ wPlane fr
    · exact ⟨h, hh, hhW, hker⟩
    · push Not at hker
      rcases hA with hA | hA
      · obtain ⟨w, hw, hw0, hhw⟩ := exists_kernel_of_finrank fr h hA
        exact absurd hhw (hker w hw hw0)
      · exact exists_kernel_of_inj hQ fr hH hHE hA hh fun x hx hhx =>
          by_contra fun hx0 => hker x hx hx0 hhx
  obtain ⟨h₁, hh₁, hh₁W, w₀, hw₀, hw₀0, hhw₀⟩ := step1
  obtain ⟨h₂, hh₂, hh₂W, s₀, hs₀W, hs₀Q, hs₀0, hhs₀⟩ :=
    exists_singular_kernel hQ fr hH hHE h2 hh₁ hh₁W hw₀ hw₀0 hhw₀
  exact exists_fix_of_singular_kernel hQ fr hH hHE hh₂ hh₂W hs₀W hs₀Q hs₀0 hhs₀

end Fix2

section Max

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}
  [FiniteDimensional F V] [Finite F]

theorem elementaryGroup_le_of_not_maps (hodd : Odd (Nat.card F))
    (hQ : (polarBilin Q).Nondegenerate) (fr : OFrame Q) {H : Subgroup (V ≃ₗ[F] V)}
    (hH : stabE fr ≤ H) (hHE : H ≤ elementaryGroup Q) (h3 : 3 ≤ Module.finrank F fr.perp)
    (hA : Module.finrank F fr.perp < 4 ∨ NoTotSing Q fr.perp) {h : V ≃ₗ[F] V} (hh : h ∈ H)
    (hhW : ¬ ∀ x ∈ wPlane fr, h x ∈ wPlane fr) : elementaryGroup Q ≤ H := by
  obtain ⟨k, hk, hke, hkW⟩ := exists_fix hodd hQ fr hH hHE hA hh hhW
  obtain ⟨a, ha, ha0, haH⟩ := exists_mixed_of_fix fr hH hk (hHE hk) hke hkW
  exact elementaryGroup_le_of_mixed hodd hQ fr hH
    (hHE.trans (elementaryGroup_le_orthogonalGroup Q)) h3 ha ha0 haH

end Max

end CFSG.ClassicalInvolution.RouteD.TWS8
