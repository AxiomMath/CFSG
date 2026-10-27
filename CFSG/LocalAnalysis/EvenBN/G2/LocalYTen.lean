module

public import CFSG.LocalAnalysis.EvenBN.G2.LocalYNine

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.LocalAnalysis.EvenBN.Common (CosetData)
open scoped commutatorElement Pointwise

section AutImage

variable {G : Type*} [Group G] {H : Subgroup G}

theorem card_autImage (φ : H ≃* H) {E : Subgroup G} (hE : E ≤ H) :
    Nat.card (autImage φ E) = Nat.card E := by
  rw [autImage, Subgroup.card_map_of_injective (fun a b hab => φ.injective (Subtype.ext hab))]
  exact Nat.card_congr (subgroupOfEquivOfLe hE).toEquiv

theorem autImage_sup (φ : H ≃* H) {E E' : Subgroup G} (hE : E ≤ H) (hE' : E' ≤ H) :
    autImage φ (E ⊔ E') = autImage φ E ⊔ autImage φ E' := by
  rw [autImage, autImage, autImage, Subgroup.subgroupOf_sup hE hE', Subgroup.map_sup]

theorem autImage_le_iff (φ : H ≃* H) {E E' : Subgroup G} (hE : E ≤ H) (hE' : E' ≤ H) :
    autImage φ E ≤ E' ↔ E ≤ autImage φ.symm E' := by
  constructor
  · intro hle
    calc E = autImage φ.symm (autImage φ E) := (autImage_symm φ hE).symm
      _ ≤ autImage φ.symm E' := autImage_mono _ hle
  · intro hle
    calc autImage φ E ≤ autImage φ (autImage φ.symm E') := autImage_mono _ hle
      _ = E' := by
          have := autImage_symm φ.symm hE'
          rwa [MulEquiv.symm_symm] at this

theorem autImage_map_subtype (φ : H ≃* H) (K : Subgroup H) [hK : K.Characteristic] :
    autImage φ (K.map H.subtype) = K.map H.subtype := by
  ext x
  rw [mem_autImage]
  constructor
  · rintro ⟨y, ⟨z, hz, hzy⟩, rfl⟩
    have hzy' : z = y := Subtype.ext hzy
    subst hzy'
    refine ⟨φ z, ?_, rfl⟩
    rw [← Subgroup.characteristic_iff_map_eq.mp hK φ]
    exact ⟨z, hz, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    refine ⟨φ.symm y, ⟨φ.symm y, ?_, rfl⟩, by simp⟩
    rw [← Subgroup.characteristic_iff_map_eq.mp hK φ.symm]
    exact ⟨y, hy, rfl⟩

theorem mul_comm_of_mem_autImage (φ : H ≃* H) {A : Subgroup G}
    (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) :
    ∀ x ∈ autImage φ A, ∀ y ∈ autImage φ A, x * y = y * x := by
  intro x hx y hy
  obtain ⟨a, ha, rfl⟩ := mem_autImage.1 hx
  obtain ⟨b, hb, rfl⟩ := mem_autImage.1 hy
  have hab : a * b = b * a := Subtype.ext (hA _ ha _ hb)
  rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hab]

theorem thompsonSubgroup_le (E : Subgroup G) : CFSG.Open.thompsonSubgroup E ≤ E :=
  CFSG.ambientMaxCardThompson_le E

theorem autImage_thompsonSubgroup_le (φ : H ≃* H) {E : Subgroup G} (hE : E ≤ H) :
    autImage φ (CFSG.Open.thompsonSubgroup E) ≤
      CFSG.Open.thompsonSubgroup (autImage φ E) := by
  have hJH : CFSG.Open.thompsonSubgroup (autImage φ E) ≤ H :=
    (thompsonSubgroup_le _).trans (autImage_le φ E)
  rw [autImage_le_iff φ ((thompsonSubgroup_le E).trans hE) hJH]
  conv_lhs => rw [CFSG.Open.thompsonSubgroup_eq_iSup]
  refine iSup_le fun A => iSup_le fun hAE => iSup_le fun hAc => iSup_le fun hAm => ?_
  have hAH : A ≤ H := hAE.trans hE
  rw [← autImage_le_iff φ hAH hJH]
  have hc := mul_comm_of_mem_autImage φ (A := A) fun x hx y hy =>
    congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : A) ⟨y, hy⟩)
  have hc' : IsMulCommutative (autImage φ A) := ⟨⟨fun a b => Subtype.ext (hc a a.2 b b.2)⟩⟩
  have hm : ∀ B : Subgroup G, B ≤ autImage φ E → IsMulCommutative B →
      Nat.card B ≤ Nat.card (autImage φ A) := by
    intro B hB hBc
    rw [card_autImage φ hAH]
    have hBH : B ≤ H := hB.trans (autImage_le φ E)
    have hBc' := mul_comm_of_mem_autImage φ.symm (A := B) fun x hx y hy =>
      congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : B) ⟨y, hy⟩)
    have h1 := hAm (autImage φ.symm B) ((autImage_mono φ.symm hB).trans (autImage_symm φ hE).le)
      ⟨⟨fun a b => Subtype.ext (hBc' a a.2 b b.2)⟩⟩
    rwa [card_autImage φ.symm hBH] at h1
  rw [CFSG.Open.thompsonSubgroup_eq_iSup]
  exact le_iSup_of_le (autImage φ A) (le_iSup_of_le (autImage_mono φ hAE)
    (le_iSup_of_le hc' (le_iSup_of_le hm le_rfl)))

theorem autImage_thompsonSubgroup (φ : H ≃* H) {E : Subgroup G} (hE : E ≤ H) :
    autImage φ (CFSG.Open.thompsonSubgroup E) = CFSG.Open.thompsonSubgroup (autImage φ E) := by
  refine le_antisymm (autImage_thompsonSubgroup_le φ hE) ?_
  have h1 := autImage_thompsonSubgroup_le φ.symm (autImage_le φ E)
  rw [autImage_symm φ hE, autImage_le_iff φ.symm ((thompsonSubgroup_le _).trans
    (autImage_le φ E)) ((thompsonSubgroup_le E).trans hE), MulEquiv.symm_symm] at h1
  exact h1

theorem maximal_autImage (φ : H ≃* H) {N Q : Subgroup G} (hN : autImage φ N = N)
    (hQ : autImage φ Q = Q) (hQH : Q ≤ H) {E : Subgroup G}
    (hE : Maximal (fun E' : Subgroup G => N ≤ E' ∧ E' ≤ Q ∧ ElemModulo N E') E) :
    Maximal (fun E' : Subgroup G => N ≤ E' ∧ E' ≤ Q ∧ ElemModulo N E') (autImage φ E) := by
  have hP : ∀ ψ : H ≃* H, autImage ψ N = N → autImage ψ Q = Q → ∀ {E : Subgroup G},
      (N ≤ E ∧ E ≤ Q ∧ ElemModulo N E) →
        (N ≤ autImage ψ E ∧ autImage ψ E ≤ Q ∧ ElemModulo N (autImage ψ E)) := by
    rintro ψ hψN hψQ E ⟨hNE, hEQ, hEm⟩
    refine ⟨hψN.symm.le.trans (autImage_mono ψ hNE), hψQ ▸ autImage_mono ψ hEQ, ?_⟩
    have := elemModulo_autImage ψ hEm
    rwa [hψN] at this
  have hNH : N ≤ H := hE.1.1.trans (hE.1.2.1.trans hQH)
  have hsN : autImage φ.symm N = N := by
    have := autImage_symm φ hNH
    rwa [hN] at this
  have hsQ : autImage φ.symm Q = Q := by
    have := autImage_symm φ hQH
    rwa [hQ] at this
  refine ⟨hP φ hN hQ hE.1, fun E'' hE'' hle => ?_⟩
  have h1 : E ≤ autImage φ.symm E'' := by
    rw [← autImage_symm φ (hE.1.2.1.trans hQH)]
    exact autImage_mono φ.symm hle
  have h2 := hE.2 (hP φ.symm hsN hsQ hE'') h1
  have h3 := autImage_symm φ.symm (hE''.2.1.trans hQH)
  rw [MulEquiv.symm_symm] at h3
  rw [← h3]
  exact autImage_mono φ h2

end AutImage

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section Local

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem mem_M_of_mem_yamadaL₂ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    {x : G} (hx : x ∈ yamadaL₂ d t) (hxL : x ∈ L) : x ∈ d.M := by
  obtain ⟨-, hL₂t, -, -⟩ := h.two_core_L₂ d hK
  have hxtM : x ∈ d.M ⊔ zpowers t := by
    rw [← hL₂t]
    exact ⟨hx, h.L_le_centralizer hxL⟩
  rcases (h.mem_sup_zpowers_iff (d.image_le _)).1 hxtM with h1 | h1
  · exact h1
  · exfalso
    refine h.t_not_mem_L ?_
    have := mul_mem (d.image_le _ h1) (inv_mem hxL)
    rwa [mul_inv_cancel_right] at this

theorem exists_decomp_yamadaC₂ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) {x : G} (hx : x ∈ yamadaC₂ d t) :
    ∃ δ ∈ d.D, ∃ y ∈ yamadaY₂ d t, ∃ τ ∈ zpowers t, x = δ * y * τ := by
  obtain ⟨-, -, -, -, -, -, -, hDS, -, -⟩ := d.inclusions
  have htL₂ : t ∈ yamadaL₂ d t := h.tM_le_yamadaL₂ d hK (mem_sup_right (mem_zpowers t))
  have htN : zpowers t ≤ normalizer (yamadaD₂ d t : Set G) := (zpowers_le).2
    (mem_normalizer_sup (Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun _ hy =>
      mem_centralizer_singleton_iff.1 (h.L_le_centralizer (d.image_le _ hy))))
      (h.yamadaL₂_le_normalizer_yamadaY₂ d hK hD htL₂))
  obtain ⟨a, ha, τ, hτ, rfl⟩ := Common.exists_mul_of_le_normalizer htN x hx
  obtain ⟨δ, hδ, y, hy, rfl⟩ := Common.exists_mul_of_le_normalizer'
    (hDS.trans (h.S_le_normalizer_yamadaY₂ d hK hD)) a ha
  exact ⟨δ, hδ, y, hy, τ, hτ, rfl⟩

theorem mem_D_of_mem_yamadaC₂ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) {x : G} (hx : x ∈ yamadaC₂ d t) (hxL : x ∈ L) : x ∈ d.D := by
  obtain ⟨-, hYX, -, hXF, -, hFD, -⟩ := d.inclusions
  obtain ⟨δ, hδ, y, hy, τ, hτ, rfl⟩ := h.exists_decomp_yamadaC₂ d hK hD hx
  have hτC : τ ∈ centralizer ({t} : Set G) := (zpowers_le.2 h.t_mem_centralizer) hτ
  have hδC : δ ∈ centralizer ({t} : Set G) := h.L_le_centralizer (d.image_le _ hδ)
  have hyY : y ∈ d.Y := by
    rw [← h.yamadaY₂_inf_centralizer d hK hD]
    refine ⟨hy, ?_⟩
    have := mul_mem (mul_mem (inv_mem hδC) (h.L_le_centralizer hxL)) (inv_mem hτC)
    rwa [show δ⁻¹ * (δ * y * τ) * τ⁻¹ = y by group] at this
  have hδy : δ * y ∈ d.D := mul_mem hδ ((hYX.trans (hXF.trans hFD)) hyY)
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hτ
  rcases h.zpow_eq_one_or_eq k with hk | hk
  · rw [hk, mul_one]
    exact hδy
  · exfalso
    rw [hk] at hxL
    refine h.t_not_mem_L ?_
    have := mul_mem (inv_mem (d.image_le _ hδy)) hxL
    rwa [inv_mul_cancel_left] at this

theorem mem_or_mem_of_mul_self_mem_yamadaY₂ (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) {x : G} (hx : x ∈ yamadaR₂ d t)
    (hxx : x * x ∈ yamadaY₂ d t) : x ∈ yamadaL₂ d t ∨ x ∈ yamadaC₂ d t := by
  obtain ⟨hR₂, hRN⟩ := h.yamadaR₂_eq_sup_yamadaY₂ d hK hD
  have htL₂ : t ∈ yamadaL₂ d t := h.tM_le_yamadaL₂ d hK (mem_sup_right (mem_zpowers t))
  rw [hR₂] at hx
  obtain ⟨r, hr, y, hy, rfl⟩ := Common.exists_mul_of_le_normalizer' hRN x hx
  have htS : zpowers t ≤ normalizer (d.S : Set G) := (zpowers_le).2
    (Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun s hs =>
      mem_centralizer_singleton_iff.1 (h.S_le_centralizer d hs)))
  obtain ⟨s, hs, τ, hτ, rfl⟩ := Common.exists_mul_of_le_normalizer htS r hr
  have hτs : τ * s = s * τ := (commute_of_mem_zpowers hτ (h.S_le_centralizer d hs)).symm
  have hττ : τ * τ = 1 := by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hτ
    rcases h.zpow_eq_one_or_eq k with hk | hk <;> rw [hk]
    · rw [mul_one]
    · exact h.t_mul_t
  have hy' : (s * τ)⁻¹ * y * (s * τ) ∈ yamadaY₂ d t := by
    have := (mem_normalizer_iff.1 (inv_mem (hRN hr)) y).1 hy
    rwa [inv_inv] at this
  have hss : s * s ∈ d.Y := by
    rw [← h.yamadaY₂_inf_centralizer d hK hD]
    refine Subgroup.mem_inf.2
      ⟨?_, mul_mem (h.S_le_centralizer d hs) (h.S_le_centralizer d hs)⟩
    have e : s * s = (s * τ * y * (s * τ * y)) * (((s * τ)⁻¹ * y * (s * τ)) * y)⁻¹ := by
      calc s * s = s * s * (τ * τ) := by rw [hττ, mul_one]
        _ = s * (s * τ) * τ := by group
        _ = s * (τ * s) * τ := by rw [hτs]
        _ = (s * τ * y * (s * τ * y)) * (((s * τ)⁻¹ * y * (s * τ)) * y)⁻¹ := by group
    rw [e]
    exact mul_mem hxx (inv_mem (mul_mem hy' hy))
  have hτL₂ : τ ∈ yamadaL₂ d t := (zpowers_le.2 htL₂) hτ
  have hτC₂ : τ ∈ yamadaC₂ d t := (zpowers_le.2 (mem_sup_right (mem_zpowers t))) hτ
  rcases d.mem_D_or_M_of_mul_self_mem hs hss with hsD | hsM
  · right
    exact mul_mem (mul_mem (le_sup_left.trans le_sup_left |> fun hle =>
      (hle : d.D ≤ yamadaC₂ d t) hsD) hτC₂) ((le_sup_right.trans le_sup_left :
        yamadaY₂ d t ≤ yamadaC₂ d t) hy)
  · left
    exact mul_mem (mul_mem (h.tM_le_yamadaL₂ d hK (mem_sup_left hsM)) hτL₂)
      (h.yamadaY₂_le_yamadaL₂ d hK hD hy)

theorem yamadaL₂_inf_yamadaC₂ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : yamadaL₂ d t ⊓ yamadaC₂ d t = yamadaE₂ d t := by
  obtain ⟨-, -, -, -, -, hFD, -⟩ := d.inclusions
  have htL₂ : t ∈ yamadaL₂ d t := h.tM_le_yamadaL₂ d hK (mem_sup_right (mem_zpowers t))
  refine le_antisymm (fun x hx => ?_) (le_inf (h.yamadaE₂_le_yamadaL₂ d hK hD).2
    (sup_le_sup_right (sup_le_sup_right hFD _) _))
  obtain ⟨hx₁, hx₂⟩ := Subgroup.mem_inf.1 hx
  obtain ⟨δ, hδ, y, hy, τ, hτ, rfl⟩ := h.exists_decomp_yamadaC₂ d hK hD hx₂
  have hτL₂ : τ ∈ yamadaL₂ d t := (zpowers_le.2 htL₂) hτ
  have hδL₂ : δ ∈ yamadaL₂ d t := by
    have := mul_mem (mul_mem hx₁ (inv_mem hτL₂)) (inv_mem (h.yamadaY₂_le_yamadaL₂ d hK hD hy))
    rwa [show δ * y * τ * τ⁻¹ * y⁻¹ = δ by group] at this
  have hδF : δ ∈ d.F := by
    rw [← (d.yamada_defs).2.2.2.2.2.2.2.1]
    exact ⟨hδ, h.mem_M_of_mem_yamadaL₂ d hK hδL₂ (d.image_le _ hδ)⟩
  exact mul_mem (mul_mem (mem_sup_left (mem_sup_left hδF)) (mem_sup_left (mem_sup_right hy)))
    (mem_sup_right hτ)

theorem yamadaR₁_inf_yamadaC₂ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : yamadaR₁ d t ⊓ yamadaC₂ d t = yamadaC₁ d t := by
  obtain ⟨-, hYX, -, hXF, -, hFD, -⟩ := d.inclusions
  obtain ⟨hC₂, hC₁N⟩ := h.yamadaC₂_eq_sup d hK hD
  have hY₁C₁ : yamadaY₁ d t ≤ yamadaC₁ d t :=
    sup_le ((hYX.trans (hXF.trans hFD)).trans (le_sup_left.trans (h.tD_le_yamadaC₁ d hK)))
      (h.yamadaU₁_le_yamadaC₁ d hK hD)
  refine le_antisymm (fun x hx => ?_) (le_inf le_sup_left (hC₂ ▸ le_sup_left))
  obtain ⟨hx₁, hx₂⟩ := Subgroup.mem_inf.1 hx
  rw [hC₂] at hx₂
  obtain ⟨c, hc, y, hy, rfl⟩ := Common.exists_mul_of_le_normalizer' hC₁N x hx₂
  have hyY₁ : y ∈ yamadaY₁ d t := by
    rw [← h.yamadaY₂_inf_yamadaR₁ d hK hD]
    refine ⟨hy, ?_⟩
    have := mul_mem (inv_mem ((le_sup_left : yamadaC₁ d t ≤ yamadaR₁ d t) hc)) hx₁
    rwa [inv_mul_cancel_left] at this
  exact mul_mem hc (hY₁C₁ hyY₁)

theorem elemModulo_yamadaL₂_yamadaC₂ (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    ElemModulo d.Y (yamadaL₂ d t) ∧ ElemModulo (yamadaY₁ d t) (yamadaC₂ d t) := by
  obtain ⟨hL₂Y, -, -, -⟩ := h.two_core_L₂ d hK
  obtain ⟨hC₂, -⟩ := h.yamadaC₂_eq_sup d hK hD
  have hC₂R₂ : yamadaC₂ d t ≤ yamadaR₂ d t := by
    rw [hC₂]
    exact sup_le (h.yamadaC₁_le_yamadaR₂ d hK) (h.yamadaY₂_le_yamadaR₂ d hK hD)
  refine ⟨elemModulo_of_mul_self_mem (hL₂Y.trans (Subgroup.centralizer_le_normalizer _))
    fun x hx => h.mul_self_mem_Y_of_mem_yamadaL₂ d hK hD hx,
    elemModulo_of_mul_self_mem (hC₂R₂.trans (h.yamadaR₂_le_normalizer_yamadaY₁ d hK hD))
      fun x hx => ?_⟩
  have : x ^ 2 ∈ closure {z | ∃ g ∈ yamadaC₂ d t, z = g ^ 2} := subset_closure ⟨x, hx, rfl⟩
  rwa [h.closure_sq_yamadaC₂ d hK hD, sq] at this

theorem yamada_5_15_5 (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) (E : Subgroup G) :
    (Maximal (fun E' : Subgroup G => yamadaY₁ d t ≤ E' ∧ E' ≤ yamadaR₂ d t ∧
        ElemModulo (yamadaY₁ d t) E') E ↔ E = yamadaL₂ d t ∨ E = yamadaC₂ d t) ∧
      (Maximal (fun E' : Subgroup G => d.Y ≤ E' ∧ E' ≤ yamadaC₂ d t ∧ ElemModulo d.Y E') E ↔
        E = yamadaE₂ d t ∨ E = yamadaC₁ d t) := by
  obtain ⟨hUY, hYX, -, hXF, -, hFD, hFM, hDS, -, -⟩ := d.inclusions
  obtain ⟨hC₂, -⟩ := h.yamadaC₂_eq_sup d hK hD
  obtain ⟨hEY, hEC⟩ := h.elemModulo_yamadaL₂_yamadaC₂ d hK hD
  have hY₁Y₂ := h.yamadaY₁_le_yamadaY₂ d hK hD
  have hY₂L₂ := h.yamadaY₂_le_yamadaL₂ d hK hD
  have hY₂C₂ : yamadaY₂ d t ≤ yamadaC₂ d t := le_sup_right.trans le_sup_left
  have hL₂R₂ : yamadaL₂ d t ≤ yamadaR₂ d t := le_sup_left
  have hC₂R₂ : yamadaC₂ d t ≤ yamadaR₂ d t := by
    rw [hC₂]
    exact sup_le (h.yamadaC₁_le_yamadaR₂ d hK) (h.yamadaY₂_le_yamadaR₂ d hK hD)
  have hDC₂ : d.D ≤ yamadaC₂ d t := le_sup_left.trans le_sup_left
  have hDL₂ : ¬ d.D ≤ yamadaL₂ d t := fun hle => d.not_D_le_M fun x hx =>
    h.mem_M_of_mem_yamadaL₂ d hK (hle hx) (d.image_le _ hx)
  have hEY₁ : ElemModulo (yamadaY₁ d t) (yamadaL₂ d t) := fun x hx y hy =>
    ⟨mem_sup_left (hEY x hx y hy).1, mem_sup_left (hEY x hx y hy).2⟩
  constructor
  · have key : ∀ E' : Subgroup G, E' ≤ yamadaR₂ d t → ElemModulo (yamadaY₁ d t) E' →
        E' ≤ yamadaL₂ d t ∨ E' ≤ yamadaC₂ d t := fun E' hE'R hE' =>
      le_or_le_of_subset_union fun x hx => h.mem_or_mem_of_mul_self_mem_yamadaY₂ d hK hD
        (hE'R hx) (hY₁Y₂ (hE' x hx x hx).1)
    have hL : yamadaY₁ d t ≤ yamadaL₂ d t ∧ yamadaL₂ d t ≤ yamadaR₂ d t ∧
        ElemModulo (yamadaY₁ d t) (yamadaL₂ d t) := ⟨hY₁Y₂.trans hY₂L₂, hL₂R₂, hEY₁⟩
    have hC : yamadaY₁ d t ≤ yamadaC₂ d t ∧ yamadaC₂ d t ≤ yamadaR₂ d t ∧
        ElemModulo (yamadaY₁ d t) (yamadaC₂ d t) := ⟨hY₁Y₂.trans hY₂C₂, hC₂R₂, hEC⟩
    have hne1 : ¬ yamadaL₂ d t ≤ yamadaC₂ d t := fun hle => d.not_M_le_D fun x hx =>
      h.mem_D_of_mem_yamadaC₂ d hK hD (hle (h.tM_le_yamadaL₂ d hK (mem_sup_left hx)))
        (d.image_le _ hx)
    have hne2 : ¬ yamadaC₂ d t ≤ yamadaL₂ d t := fun hle => hDL₂ (hDC₂.trans hle)
    constructor
    · rintro ⟨⟨-, hER, hE⟩, hmax⟩
      rcases key E hER hE with h' | h'
      · exact Or.inl (le_antisymm h' (hmax hL h'))
      · exact Or.inr (le_antisymm h' (hmax hC h'))
    · rintro (rfl | rfl)
      · refine ⟨hL, fun E' hE' hLE' => ?_⟩
        rcases key E' hE'.2.1 hE'.2.2 with h' | h'
        · exact h'
        · exact absurd (hLE'.trans h') hne1
      · refine ⟨hC, fun E' hE' hCE' => ?_⟩
        rcases key E' hE'.2.1 hE'.2.2 with h' | h'
        · exact absurd (hCE'.trans h') hne2
        · exact h'
  · have hYtM : d.Y ≤ d.M ⊔ zpowers t := (hYX.trans (hXF.trans hFM)).trans le_sup_left
    have key : ∀ E' : Subgroup G, E' ≤ yamadaC₂ d t → ElemModulo d.Y E' →
        E' ≤ yamadaE₂ d t ∨ E' ≤ yamadaC₁ d t := fun E' hE'C hE' =>
      le_or_le_of_subset_union fun x hx => by
        rcases (h.mul_self_mem_tM_iff d hK (hC₂R₂ (hE'C hx))).1 (hYtM (hE' x hx x hx).1)
          with h' | h'
        · left
          rw [← h.yamadaL₂_inf_yamadaC₂ d hK hD]
          exact ⟨h', hE'C hx⟩
        · right
          rw [← h.yamadaR₁_inf_yamadaC₂ d hK hD]
          exact ⟨h', hE'C hx⟩
    have hE₂L₂ := (h.yamadaE₂_le_yamadaL₂ d hK hD).2
    have hE₂C₂ : yamadaE₂ d t ≤ yamadaC₂ d t := by
      rw [← h.yamadaL₂_inf_yamadaC₂ d hK hD]
      exact inf_le_right
    have hC₁C₂ : yamadaC₁ d t ≤ yamadaC₂ d t := hC₂ ▸ le_sup_left
    have hE : d.Y ≤ yamadaE₂ d t ∧ yamadaE₂ d t ≤ yamadaC₂ d t ∧ ElemModulo d.Y (yamadaE₂ d t) :=
      ⟨(hYX.trans hXF).trans (le_sup_left.trans le_sup_left), hE₂C₂,
        fun x hx y hy => hEY x (hE₂L₂ hx) y (hE₂L₂ hy)⟩
    have hC : d.Y ≤ yamadaC₁ d t ∧ yamadaC₁ d t ≤ yamadaC₂ d t ∧ ElemModulo d.Y (yamadaC₁ d t) :=
      ⟨(hYX.trans (hXF.trans hFD)).trans (le_sup_left.trans (h.tD_le_yamadaC₁ d hK)), hC₁C₂,
        (h.elemModulo_Y d hK hD).2⟩
    have hne1 : ¬ yamadaE₂ d t ≤ yamadaC₁ d t := by
      intro hle
      obtain ⟨y, hy, hyR₁⟩ := h.exists_mem_yamadaY₂_not_mem_yamadaR₁ d hK hD
      exact hyR₁ ((le_sup_left : yamadaC₁ d t ≤ yamadaR₁ d t)
        (hle (mem_sup_left (mem_sup_right hy))))
    have hne2 : ¬ yamadaC₁ d t ≤ yamadaE₂ d t := fun hle =>
      hDL₂ (((le_sup_left.trans (h.tD_le_yamadaC₁ d hK)).trans hle).trans hE₂L₂)
    constructor
    · rintro ⟨⟨-, hEC', hE'⟩, hmax⟩
      rcases key E hEC' hE' with h' | h'
      · exact Or.inl (le_antisymm h' (hmax hE h'))
      · exact Or.inr (le_antisymm h' (hmax hC h'))
    · rintro (rfl | rfl)
      · refine ⟨hE, fun E' hE' hEE' => ?_⟩
        rcases key E' hE'.2.1 hE'.2.2 with h' | h'
        · exact h'
        · exact absurd (hEE'.trans h') hne1
      · refine ⟨hC, fun E' hE' hCE' => ?_⟩
        rcases key E' hE'.2.1 hE'.2.2 with h' | h'
        · exact absurd (hCE'.trans h') hne2
        · exact h'

theorem yamadaS₂_eq_sup (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) :
    yamadaS₂ d t = CFSG.Open.thompsonSubgroup (yamadaL₂ d t) ⊔
      CFSG.Open.thompsonSubgroup (yamadaC₁ d t) := by
  obtain ⟨-, -, -, -, -, -, -, hDS, hMS, -⟩ := d.inclusions
  rw [h.yamada_5_13_2 d hK hD, h.yamada_5_11_2 d hK hD, hD.D₁_eq]
  have hU₁Y₂ := yamadaU₁_le_yamadaY₂ d t
  apply le_antisymm
  · refine sup_le ?_ (le_sup_right.trans le_sup_left)
    rw [← (d.yamada_defs).2.2.2.2.2.2.2.2]
    exact sup_le (le_sup_left.trans le_sup_right) (le_sup_left.trans le_sup_left)
  · exact sup_le (sup_le (hMS.trans le_sup_left) le_sup_right)
      (sup_le (hDS.trans le_sup_left) (hU₁Y₂.trans le_sup_right))

theorem yamada_5_15_6 (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) :
    ((yamadaL₂ d t).subgroupOf (yamadaR₂ d t)).Characteristic ∧
      ((yamadaC₂ d t).subgroupOf (yamadaR₂ d t)).Characteristic ∧
      ((yamadaC₁ d t).subgroupOf (yamadaR₂ d t)).Characteristic ∧
      ((yamadaS₂ d t).subgroupOf (yamadaR₂ d t)).Characteristic := by
  obtain ⟨hUY, hYX, -, hXF, -, hFD, hFM, hDS, -, -⟩ := d.inclusions
  obtain ⟨hC₂, -⟩ := h.yamadaC₂_eq_sup d hK hD
  have hL₂R₂ : yamadaL₂ d t ≤ yamadaR₂ d t := le_sup_left
  have hC₁R₂ := h.yamadaC₁_le_yamadaR₂ d hK
  have hC₂R₂ : yamadaC₂ d t ≤ yamadaR₂ d t := by
    rw [hC₂]
    exact sup_le hC₁R₂ (h.yamadaY₂_le_yamadaR₂ d hK hD)
  have hE₂L₂ := (h.yamadaE₂_le_yamadaL₂ d hK hD).2
  have hE₂R₂ : yamadaE₂ d t ≤ yamadaR₂ d t := hE₂L₂.trans hL₂R₂
  have hYL₂ : d.Y ≤ yamadaL₂ d t := ((hYX.trans (hXF.trans hFM)).trans le_sup_left).trans
    (h.tM_le_yamadaL₂ d hK)
  have hDC₁ : d.D ≤ yamadaC₁ d t := le_sup_left.trans (h.tD_le_yamadaC₁ d hK)
  have hDL₂ : ¬ d.D ≤ yamadaL₂ d t := fun hle => d.not_D_le_M fun x hx =>
    h.mem_M_of_mem_yamadaL₂ d hK (hle hx) (d.image_le _ hx)
  obtain ⟨y₀, hy₀, hy₀R₁⟩ := h.exists_mem_yamadaY₂_not_mem_yamadaR₁ d hK hD
  have hY₁ : ∀ φ : yamadaR₂ d t ≃* yamadaR₂ d t, autImage φ (yamadaY₁ d t) = yamadaY₁ d t :=
    fun φ => by
      rw [← (h.yamada_5_15_2 d hK hD).2.1]
      exact autImage_map_subtype φ _
  have h5 := h.yamada_5_15_5 d hK hD
  have hL₂ : ∀ φ : yamadaR₂ d t ≃* yamadaR₂ d t, autImage φ (yamadaL₂ d t) = yamadaL₂ d t := by
    intro φ
    rcases (h5 _).1.1 (maximal_autImage φ (hY₁ φ) (autImage_self φ) le_rfl
      ((h5 _).1.2 (Or.inl rfl))) with e | e
    · exact e
    · exfalso
      have h1 : autImage φ d.Y = yamadaY₁ d t := by
        rw [← (h.yamada_5_13_4 d hK hD).1, autImage_closure_sq φ hL₂R₂, e,
          h.closure_sq_yamadaC₂ d hK hD]
      have h2 := card_autImage φ (hYL₂.trans hL₂R₂)
      rw [h1] at h2
      have h3 : d.Y = yamadaY₁ d t := Subgroup.eq_of_le_of_card_ge le_sup_left h2.le
      obtain ⟨u, hu, huU⟩ := h.exists_mem_yamadaU₁_not_mem_U d hK hD
      refine huU ?_
      rw [← hD.inf_centralizer]
      refine ⟨hu, h.L_le_centralizer (d.image_le (Model.Y K) ?_)⟩
      rw [← G2Data.Y, h3]
      exact mem_sup_right hu
  have hC₂φ : ∀ φ : yamadaR₂ d t ≃* yamadaR₂ d t, autImage φ (yamadaC₂ d t) = yamadaC₂ d t := by
    intro φ
    rcases (h5 _).1.1 (maximal_autImage φ (hY₁ φ) (autImage_self φ) le_rfl
      ((h5 _).1.2 (Or.inr rfl))) with e | e
    · exfalso
      have := autImage_injective φ hL₂R₂ hC₂R₂ ((hL₂ φ).trans e.symm)
      exact hDL₂ (this ▸ (le_sup_left.trans le_sup_left : d.D ≤ yamadaC₂ d t))
    · exact e
  have hY : ∀ φ : yamadaR₂ d t ≃* yamadaR₂ d t, autImage φ d.Y = d.Y := fun φ => by
    rw [← (h.yamada_5_13_4 d hK hD).1, autImage_closure_sq φ hL₂R₂, hL₂ φ]
  have hE₂ : ∀ φ : yamadaR₂ d t ≃* yamadaR₂ d t, autImage φ (yamadaE₂ d t) = yamadaE₂ d t := by
    intro φ
    rcases (h5 _).2.1 (maximal_autImage φ (hY φ) (hC₂φ φ) hC₂R₂
      ((h5 _).2.2 (Or.inl rfl))) with e | e
    · exact e
    · exfalso
      have : yamadaC₁ d t ≤ yamadaL₂ d t := by
        rw [← e, ← hL₂ φ]
        exact autImage_mono φ hE₂L₂
      exact hDL₂ (hDC₁.trans this)
  have hC₁ : ∀ φ : yamadaR₂ d t ≃* yamadaR₂ d t, autImage φ (yamadaC₁ d t) = yamadaC₁ d t := by
    intro φ
    rcases (h5 _).2.1 (maximal_autImage φ (hY φ) (hC₂φ φ) hC₂R₂
      ((h5 _).2.2 (Or.inr rfl))) with e | e
    · exfalso
      have := autImage_injective φ hE₂R₂ hC₁R₂ ((hE₂ φ).trans e.symm)
      exact hy₀R₁ ((le_sup_left : yamadaC₁ d t ≤ yamadaR₁ d t)
        (this ▸ (mem_sup_left (mem_sup_right hy₀) : y₀ ∈ yamadaE₂ d t)))
    · exact e
  have hS₂ : ∀ φ : yamadaR₂ d t ≃* yamadaR₂ d t, autImage φ (yamadaS₂ d t) = yamadaS₂ d t := by
    intro φ
    rw [h.yamadaS₂_eq_sup d hK hD, autImage_sup φ ((thompsonSubgroup_le _).trans hL₂R₂)
      ((thompsonSubgroup_le _).trans hC₁R₂), autImage_thompsonSubgroup φ hL₂R₂,
      autImage_thompsonSubgroup φ hC₁R₂, hL₂ φ, hC₁ φ]
  exact ⟨characteristic_of_autImage hL₂, characteristic_of_autImage hC₂φ,
    characteristic_of_autImage hC₁, characteristic_of_autImage hS₂⟩

end Local

end Setup

end CFSG.LocalAnalysis.EvenBN.G2
