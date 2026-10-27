module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8abAP

public noncomputable section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup
open scoped Pointwise

namespace KD8ab

open KD7 Sec8

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : L2Data t L}
  {C : A.CaseKD} {S : KDBase A C} {T₁ : Subgroup X}

namespace AD

variable {H : AD S T₁}

theorem mem_zk_of_comm_R {s : MA}
    (hs : ∀ a : MA, MA.inT1 a = true → H.ι s * H.ι a = H.ι a * H.ι s) : s ∈ MA.ZList := by
  have hc : ∀ g ∈ [MA.u, MA.w₁, MA.v, MA.z, MA.y, MA.t, MA.k], g * s = s * g := by
    intro g hg
    apply H.ι_injective
    rw [map_mul, map_mul]
    exact (hs g (gens7_T1 g hg)).symm
  rcases MA.cent_T1 s hc with h | h | h | h <;> rw [h] <;> simp [MA.ZList]

theorem zk_central : ∀ s ∈ MA.ZList, ∀ a : MA, s * a = a * s := by decide +kernel

theorem ι_comm_of_zk {s : MA} (hs : s ∈ MA.ZList) (a : MA) : H.ι s * H.ι a = H.ι a * H.ι s := by
  rw [← map_mul, ← map_mul, zk_central s hs a]

namespace DC

variable {D : H.DC}

namespace PD

variable (P : D.PD)

@[expose] noncomputable def R₂ : Subgroup X := H.G.D₁.S₁ ⊔ zpowers P.p

theorem S₁_le_R₂ : H.G.D₁.S₁ ≤ P.R₂ := le_sup_left

theorem p_mem_R₂ : P.p ∈ P.R₂ := mem_sup_right (mem_zpowers _)

theorem isPGroup_R₂ : IsPGroup 2 P.R₂ :=
  IsPGroup.to_sup_of_normal_left' H.G.D₁.isPGroup_S₁ (isPGroup_zpowers_of_pow P.hpow)
    (zpowers_le.mpr P.hN)

theorem p_conj_ι {a : MA} (ha : MA.inT1 a = true) :
    P.p * H.ι a * P.p⁻¹ = H.ι (pAct D.e D.c₂ a) := by
  rw [P.hact _ (H.ι_mem_R ha), D.g₁_conj ha]

theorem p_conj_R {τ : X} (hτ : τ ∈ H.R) : P.p * τ * P.p⁻¹ ∈ H.R := by
  rw [P.hact τ hτ]; exact D.g₁_conj_mem_R hτ

theorem p_conj_t : P.p * t * P.p⁻¹ = H.ι (MA.t * MA.u) := by
  have h := P.p_conj_ι (a := MA.t) (by decide +kernel)
  rwa [H.ι_t, (actsW_pAct D.e D.c₂ D.hc₂).1] at h

theorem p_sq_mem_S₁ : P.p * P.p ∈ H.G.D₁.S₁ := by
  have hC : P.p * P.p ∈ centralizer (H.R : Set X) := by
    rw [mem_centralizer_iff]
    intro τ hτ
    have h1 := P.hact τ hτ
    have h2 := P.hact _ (P.p_conj_R hτ)
    have h3 : (P.p * P.p) * τ * (P.p * P.p)⁻¹ = τ := by
      calc (P.p * P.p) * τ * (P.p * P.p)⁻¹ = P.p * (P.p * τ * P.p⁻¹) * P.p⁻¹ := by group
        _ = D.g₁ * (D.g₁ * τ * D.g₁⁻¹) * D.g₁⁻¹ := by rw [h2, h1]
        _ = (D.g₁ * D.g₁) * τ * (D.g₁ * D.g₁)⁻¹ := by group
        _ = τ := by rw [D.g₁_mul_g₁]; group
    calc τ * (P.p * P.p) = ((P.p * P.p) * τ * (P.p * P.p)⁻¹) * (P.p * P.p) := by rw [h3]
      _ = (P.p * P.p) * τ := by group
  have hle : H.G.D₁.S₁ ⊔ zpowers (P.p * P.p) ≤ P.R₂ :=
    sup_le P.S₁_le_R₂ (zpowers_le.mpr (mul_mem P.p_mem_R₂ P.p_mem_R₂))
  have hmax := H.S₁_max_K₁ _ (P.isPGroup_R₂.to_le hle) le_sup_left
    (sup_le le_sup_right (zpowers_le.mpr (mem_sup_left hC)))
  rw [← hmax]
  exact mem_sup_right (mem_zpowers _)

theorem mem_R₂ {g : X} (hg : g ∈ P.R₂) : g ∈ H.G.D₁.S₁ ∨ g * P.p⁻¹ ∈ H.G.D₁.S₁ :=
  Sec7.mem_or_of_mem_sup_zpowers P.hN (by rw [pow_two]; exact P.p_sq_mem_S₁) hg

theorem mem_S₁_of_comm_t {g : X} (hg : g ∈ P.R₂) (hgt : g * t = t * g) :
    g ∈ H.G.D₁.S₁ := by
  rcases P.mem_R₂ hg with h | h
  · exact h
  · exfalso
    obtain ⟨s, hs⟩ := H.mem_range_of_mem_S₁ h
    have hg' : g = H.ι s * P.p := by rw [hs]; group
    apply MA.not_conj_t_tu s⁻¹
    apply H.ι_injective
    have h1 : H.ι s * H.ι (MA.t * MA.u) * (H.ι s)⁻¹ = t := by
      rw [← P.p_conj_t, show H.ι s * (P.p * t * P.p⁻¹) * (H.ι s)⁻¹ = g * t * g⁻¹ by
        rw [hg']; group, hgt, mul_inv_cancel_right]
    rw [map_mul, map_mul, map_inv, inv_inv, H.ι_t]
    calc (H.ι s)⁻¹ * t * H.ι s =
        (H.ι s)⁻¹ * (H.ι s * H.ι (MA.t * MA.u) * (H.ι s)⁻¹) * H.ι s := by rw [h1]
      _ = H.ι (MA.t * MA.u) := by group

theorem R₂_le_normalizer_C : P.R₂ ≤ normalizer (centralizer (H.R : Set X) : Set X) := by
  refine sup_le H.S₁_le_normalizer_C (zpowers_le.mpr ?_)
  refine mem_normalizer_of_conj_le fun c hc => conj_mem_centralizer (fun τ hτ => ?_) hc
  obtain ⟨a, ha, rfl⟩ := H.mem_R_iff.mp hτ
  have h1 : P.p⁻¹ * H.ι a * P.p = H.ι (pAct D.e D.c₂ a) := by
    have h2 := P.p_conj_ι (pAct_T1 D.e D.c₂ D.hc₂ a)
    rw [pAct_pAct D.e D.c₂ D.hc₂ a ha] at h2
    rw [← h2]; group
  rw [h1]; exact H.ι_mem_R (pAct_T1 D.e D.c₂ D.hc₂ a)

@[expose] noncomputable def K₂ : Subgroup X := centralizer (H.R : Set X) ⊔ P.R₂

theorem mem_K₂ {k : X} (hk : k ∈ P.K₂) :
    ∃ c ∈ centralizer (H.R : Set X), ∃ r ∈ P.R₂, k = c * r := by
  have h : k ∈ ((centralizer (H.R : Set X) : Set X) * (P.R₂ : Set X)) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _ P.R₂_le_normalizer_C]; exact hk
  obtain ⟨c, hc, r, hr, rfl⟩ := h
  exact ⟨c, hc, r, hr, rfl⟩

theorem R₂_max_K₂ : ∀ Q : Subgroup X, IsPGroup 2 Q → P.R₂ ≤ Q → Q ≤ P.K₂ → Q = P.R₂ := by
  intro Q hQ hle hQK
  have hQ₁ : Q ⊓ H.K₁ = H.G.D₁.S₁ := H.S₁_max_K₁ _ (hQ.to_le inf_le_left)
    (le_inf (P.S₁_le_R₂.trans hle) le_sup_right) inf_le_right
  refine le_antisymm (fun q hq => ?_) hle
  obtain ⟨c, hc, r, hr, rfl⟩ := P.mem_K₂ (hQK hq)
  rcases P.mem_R₂ hr with h | h
  · have : c * r ∈ Q ⊓ H.K₁ :=
      Subgroup.mem_inf.mpr ⟨hq, mul_mem (mem_sup_left hc) (mem_sup_right h)⟩
    rw [hQ₁] at this
    exact P.S₁_le_R₂ this
  · have hpQ : P.p ∈ Q := hle P.p_mem_R₂
    have : c * r * P.p⁻¹ ∈ Q ⊓ H.K₁ := Subgroup.mem_inf.mpr ⟨mul_mem hq (inv_mem hpQ), by
      rw [mul_assoc]; exact mul_mem (mem_sup_left hc) (mem_sup_right h)⟩
    rw [hQ₁] at this
    have := mul_mem (P.S₁_le_R₂ this) P.p_mem_R₂
    rwa [inv_mul_cancel_right] at this

theorem p_inv_mul_g₁ : P.p⁻¹ * D.g₁ ∈ centralizer (H.R : Set X) :=
  inv_mul_mem_centralizer fun τ hτ => (P.hact τ hτ).symm

theorem g₁_mem_K₂ : D.g₁ ∈ P.K₂ := by
  rw [show D.g₁ = P.p * (P.p⁻¹ * D.g₁) by group]
  exact mul_mem (mem_sup_right P.p_mem_R₂) (mem_sup_left P.p_inv_mul_g₁)

theorem d₀_conj_R {τ : X} (hτ : τ ∈ H.R) : D.d₀ * τ * D.d₀⁻¹ ∈ H.R := by
  obtain ⟨a, ha, rfl⟩ := H.mem_R_iff.mp hτ
  rw [← D.conj a ha]; exact H.ι_mem_R (dc_T1 D.e D.c₂ D.hc₂ a)

theorem d₀_inv_conj_R {τ : X} (hτ : τ ∈ H.R) : D.d₀⁻¹ * τ * D.d₀ ∈ H.R := by
  obtain ⟨a, ha, rfl⟩ := H.mem_R_iff.mp hτ
  rw [← D.conj_inv ha]; exact H.ι_mem_R (dci_T1 D.e D.c₂ D.hc₂ a)

theorem conj_R₂_le_K₂ : P.R₂.map (MulAut.conj D.d₀).toMonoidHom ≤ P.K₂ := by
  rw [R₂, Subgroup.map_sup]
  refine sup_le ?_ ?_
  · rw [← H.range_ι, MonoidHom.range_eq_map, map_map, ← MonoidHom.range_eq_map]
    refine MA.range_le _ fun g hg => ?_
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    have hT : ∀ a : MA, MA.inT1 a = true → D.d₀ * H.ι a * D.d₀⁻¹ ∈ P.K₂ := fun a ha => by
      rw [← D.conj a ha]; exact mem_sup_right (P.S₁_le_R₂ (H.ι_mem_S₁ _))
    simp only [MA.gens, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact P.g₁_mem_K₂
    all_goals exact hT _ (by decide +kernel)
  · rw [MonoidHom.map_zpowers, zpowers_le]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    set s₀ := H.ι (tE D.e) * H.ι MA.w₂ * H.ι (tE D.e) with hs₀
    have hs₀S : s₀ ∈ H.G.D₁.S₁ := by
      rw [hs₀, ← map_mul, ← map_mul]; exact H.ι_mem_S₁ _
    have hs₀g : D.d₀ * D.g₁ * D.d₀⁻¹ = s₀ := by
      rw [hs₀, DC.g₁]
      nth_rewrite 2 [← D.ι_tE_inv]
      rw [← D.sq]
      group
    have hC : s₀⁻¹ * (D.d₀ * P.p * D.d₀⁻¹) ∈ centralizer (H.R : Set X) := by
      refine inv_mul_mem_centralizer fun τ hτ => ?_
      have h1 := P.hact _ (d₀_inv_conj_R (D := D) hτ)
      rw [← hs₀g]
      calc D.d₀ * P.p * D.d₀⁻¹ * τ * (D.d₀ * P.p * D.d₀⁻¹)⁻¹ =
          D.d₀ * (P.p * (D.d₀⁻¹ * τ * D.d₀) * P.p⁻¹) * D.d₀⁻¹ := by group
        _ = D.d₀ * (D.g₁ * (D.d₀⁻¹ * τ * D.d₀) * D.g₁⁻¹) * D.d₀⁻¹ := by rw [h1]
        _ = D.d₀ * D.g₁ * D.d₀⁻¹ * τ * (D.d₀ * D.g₁ * D.d₀⁻¹)⁻¹ := by group
    rw [show D.d₀ * P.p * D.d₀⁻¹ = s₀ * (s₀⁻¹ * (D.d₀ * P.p * D.d₀⁻¹)) by group]
    exact mul_mem (mem_sup_right (P.S₁_le_R₂ hs₀S)) (mem_sup_left hC)

theorem conj_inv_of_conj {g : X} (hg : ∀ τ ∈ H.R, g * τ * g⁻¹ = D.d₀ * τ * D.d₀⁻¹) {τ : X}
    (hτ : τ ∈ H.R) : g⁻¹ * τ * g = D.d₀⁻¹ * τ * D.d₀ := by
  have h1 := hg _ (d₀_inv_conj_R (D := D) hτ)
  rw [show D.d₀ * (D.d₀⁻¹ * τ * D.d₀) * D.d₀⁻¹ = τ by group] at h1
  calc g⁻¹ * τ * g = g⁻¹ * (g * (D.d₀⁻¹ * τ * D.d₀) * g⁻¹) * g := by rw [h1]
    _ = D.d₀⁻¹ * τ * D.d₀ := by group

theorem exists_d₃ : ∃ d₃ g : X, d₃ ∈ normalizer (P.R₂ : Set X) ∧
    g ∈ normalizer (P.R₂ : Set X) ∧ (∃ a : ℕ, g ^ 2 ^ a = 1) ∧ d₃ ∈ P.R₂ ⊔ zpowers g ∧
      ∀ τ ∈ H.R, d₃ * τ * d₃⁻¹ = D.d₀ * τ * D.d₀⁻¹ := by
  obtain ⟨c, hc, hN⟩ := exists_centralizer_mul_mem_normalizer P.R₂_le_normalizer_C
    P.isPGroup_R₂ P.R₂_max_K₂ P.conj_R₂_le_K₂
  obtain ⟨m, hm, a, hpow⟩ := exists_odd_pow_two_elt (c * D.d₀)
  have hgR : ∀ τ ∈ H.R, D.d₀ * τ * D.d₀⁻¹ ∈ H.R := fun τ hτ => d₀_conj_R (D := D) hτ
  have hT : ∀ τ ∈ H.R, (c * D.d₀) * τ * (c * D.d₀)⁻¹ = D.d₀ * τ * D.d₀⁻¹ :=
    fun τ hτ => conj_centralizer_mul hc hgR hτ
  have hcR : ∀ τ ∈ H.R, (c * D.d₀) * τ * (c * D.d₀)⁻¹ ∈ H.R := fun τ hτ => by
    rw [hT τ hτ]; exact hgR τ hτ
  obtain ⟨j, rfl⟩ := hm
  set g := (c * D.d₀) ^ (2 * j + 1) with hg
  have hdm : D.d₀ ^ (2 * j + 1) = H.ι (tE D.e ^ j) * D.d₀ := by
    rw [pow_succ, pow_mul, pow_two, D.sq, map_pow]
  have hgN : g ∈ normalizer (P.R₂ : Set X) := pow_mem hN _
  have hι : H.ι (tE D.e ^ j) ∈ P.R₂ := P.S₁_le_R₂ (H.ι_mem_S₁ _)
  have hιN : H.ι (tE D.e ^ j) ∈ normalizer (P.R₂ : Set X) := le_normalizer hι
  refine ⟨(H.ι (tE D.e ^ j))⁻¹ * g, g, mul_mem (inv_mem hιN) hgN, hgN, ⟨a, hpow⟩,
    mul_mem (inv_mem (mem_sup_left hι)) (mem_sup_right (mem_zpowers g)), fun τ hτ => ?_⟩
  have h1 := (conj_pow_eq_of_conj_eq hT hcR (2 * j + 1) τ hτ).1
  rw [show (H.ι (tE D.e ^ j))⁻¹ * g * τ * ((H.ι (tE D.e ^ j))⁻¹ * g)⁻¹ =
    (H.ι (tE D.e ^ j))⁻¹ * (g * τ * g⁻¹) * H.ι (tE D.e ^ j) by group, h1, hdm]
  group

end PD

end DC

structure TD (H : AD S T₁) where
  e : Bool
  c₂ : MA
  hc₂ : c₂ ∈ [1, MA.z]
  d : X
  sq : d * d = H.ι (tE e)
  conj : ∀ a, MA.inT1 a = true → H.ι (dc e c₂ a) = d * H.ι a * d⁻¹
  hp : d * H.ι MA.w₂ * d⁻¹ ∈ normalizer (H.G.D₁.S₁ : Set X)

namespace DC.PD

variable {D : H.DC} (P : D.PD)

theorem nonempty_TD_of {d : X} (hdN : d ∈ normalizer (P.R₂ : Set X))
    (hd : ∀ τ ∈ H.R, d * τ * d⁻¹ = D.d₀ * τ * D.d₀⁻¹) (hsq : d * d = H.ι (tE D.e)) :
    Nonempty H.TD := by
  refine ⟨⟨D.e, D.c₂, D.hc₂, d, hsq, fun a ha => by rw [D.conj a ha, hd _ (H.ι_mem_R ha)], ?_⟩⟩
  have hR₂ : d * H.ι MA.w₂ * d⁻¹ ∈ P.R₂ :=
    Sec7.conj_mem_of_mem_normalizer hdN (P.S₁_le_R₂ (H.ι_mem_S₁ _))
  have hact : ∀ τ ∈ H.R, (d * H.ι MA.w₂ * d⁻¹) * τ * (d * H.ι MA.w₂ * d⁻¹)⁻¹ =
      P.p * τ * P.p⁻¹ := by
    intro τ hτ
    have h1 := conj_inv_of_conj (D := D) hd hτ
    have h2 : H.ι MA.w₂ * (D.d₀⁻¹ * τ * D.d₀) * (H.ι MA.w₂)⁻¹ ∈ H.R :=
      H.conj_mem_R_of_mem_S₁ (H.ι_mem_S₁ _) (d₀_inv_conj_R (D := D) hτ)
    rw [P.hact τ hτ, show (d * H.ι MA.w₂ * d⁻¹) * τ * (d * H.ι MA.w₂ * d⁻¹)⁻¹ =
      d * (H.ι MA.w₂ * (d⁻¹ * τ * d) * (H.ι MA.w₂)⁻¹) * d⁻¹ by group, h1, hd _ h2, DC.g₁]
    group
  have hC : P.p⁻¹ * (d * H.ι MA.w₂ * d⁻¹) ∈ centralizer (H.R : Set X) :=
    inv_mul_mem_centralizer fun τ hτ => hact τ hτ
  have hS : P.p⁻¹ * (d * H.ι MA.w₂ * d⁻¹) ∈ H.G.D₁.S₁ := by
    refine P.mem_S₁_of_comm_t (mul_mem (inv_mem P.p_mem_R₂) hR₂) ?_
    have ht : t ∈ H.R := by
      have h1 := H.ι_mem_R (a := MA.t) (by decide +kernel)
      rwa [H.ι_t] at h1
    exact (mem_centralizer_iff.mp hC t ht).symm
  rw [show d * H.ι MA.w₂ * d⁻¹ = P.p * (P.p⁻¹ * (d * H.ι MA.w₂ * d⁻¹)) by group]
  exact mul_mem P.hN (le_normalizer hS)

theorem dc_k_sq : ∀ e : Bool, ∀ c₂ ∈ [1, MA.z],
    dc e c₂ MA.k * (tE e * MA.z) * MA.k = tE e := by decide +kernel

theorem tE_mul_T1 : ∀ e : Bool, ∀ ζ ∈ MA.ZList, MA.inT1 (tE e * ζ) = true := by decide +kernel

include P in
theorem nonempty_TD : Nonempty H.TD := by
  obtain ⟨d₃, g, hd₃N, hgN, ⟨a, hga⟩, hd₃g, hd₃⟩ := P.exists_d₃
  have hQ : IsPGroup 2 (P.R₂ ⊔ zpowers g : Subgroup X) :=
    IsPGroup.to_sup_of_normal_left' P.isPGroup_R₂ (isPGroup_zpowers_of_pow hga)
      (zpowers_le.mpr hgN)
  have hc₀ : (H.ι (tE D.e))⁻¹ * (d₃ * d₃) ∈ centralizer (H.R : Set X) := by
    refine inv_mul_mem_centralizer fun τ hτ => ?_
    calc (d₃ * d₃) * τ * (d₃ * d₃)⁻¹ = d₃ * (d₃ * τ * d₃⁻¹) * d₃⁻¹ := by group
      _ = D.d₀ * (D.d₀ * τ * D.d₀⁻¹) * D.d₀⁻¹ := by rw [hd₃ τ hτ, hd₃ _ (d₀_conj_R (D := D) hτ)]
      _ = (D.d₀ * D.d₀) * τ * (D.d₀ * D.d₀)⁻¹ := by group
      _ = _ := by rw [D.sq]
  have hιR₂ : H.ι (tE D.e) ∈ P.R₂ := P.S₁_le_R₂ (H.ι_mem_S₁ _)
  have hd₃sq : d₃ * d₃ ∈ P.R₂ := by
    have hle : P.R₂ ⊔ zpowers (d₃ * d₃) ≤ P.K₂ := by
      refine sup_le le_sup_right (zpowers_le.mpr ?_)
      rw [show d₃ * d₃ = H.ι (tE D.e) * ((H.ι (tE D.e))⁻¹ * (d₃ * d₃)) by group]
      exact mul_mem (mem_sup_right hιR₂) (mem_sup_left hc₀)
    have hmax := P.R₂_max_K₂ _
      (hQ.to_le (sup_le le_sup_left (zpowers_le.mpr (mul_mem hd₃g hd₃g)))) le_sup_left hle
    rw [← hmax]; exact mem_sup_right (mem_zpowers _)
  have ht : t ∈ H.R := by
    have h1 := H.ι_mem_R (a := MA.t) (by decide +kernel)
    rwa [H.ι_t] at h1
  have hc₀S : (H.ι (tE D.e))⁻¹ * (d₃ * d₃) ∈ H.G.D₁.S₁ :=
    P.mem_S₁_of_comm_t (mul_mem (inv_mem hιR₂) hd₃sq) (mem_centralizer_iff.mp hc₀ t ht).symm
  obtain ⟨ζ, hζ⟩ := H.mem_range_of_mem_S₁ hc₀S
  have hζZ : ζ ∈ MA.ZList := H.mem_zk_of_comm_R fun a ha => by
    rw [hζ]; exact (mem_centralizer_iff.mp hc₀ _ (H.ι_mem_R ha)).symm
  have hd₃sq' : d₃ * d₃ = H.ι (tE D.e * ζ) := by rw [map_mul, hζ]; group
  have hT1 := tE_mul_T1 D.e ζ hζZ
  have hfix : dc D.e D.c₂ (tE D.e * ζ) = tE D.e * ζ := by
    apply H.ι_injective
    rw [D.conj _ hT1, ← hd₃ _ (H.ι_mem_R hT1), ← hd₃sq']
    group
  rcases dc_tE D.e D.c₂ D.hc₂ ζ hζZ hfix with rfl | rfl
  · exact P.nonempty_TD_of hd₃N hd₃ (by rw [hd₃sq', mul_one])
  · have hk : H.ι MA.k ∈ P.R₂ := P.S₁_le_R₂ (H.ι_mem_S₁ _)
    have hkZ : MA.k ∈ MA.ZList := by simp [MA.ZList]
    refine P.nonempty_TD_of (mul_mem hd₃N (le_normalizer hk)) (fun τ hτ => ?_) ?_
    · obtain ⟨b, hb, rfl⟩ := H.mem_R_iff.mp hτ
      rw [← hd₃ _ (H.ι_mem_R hb), show d₃ * H.ι MA.k * H.ι b * (d₃ * H.ι MA.k)⁻¹ =
        d₃ * (H.ι MA.k * H.ι b * (H.ι MA.k)⁻¹) * d₃⁻¹ by group, H.ι_comm_of_zk hkZ b,
        mul_inv_cancel_right]
    · have hk' : d₃ * H.ι MA.k * d₃⁻¹ = H.ι (dc D.e D.c₂ MA.k) := by
        rw [hd₃ _ (H.ι_mem_R (by decide +kernel)), D.conj _ (by decide +kernel)]
      rw [show d₃ * H.ι MA.k * (d₃ * H.ι MA.k) = (d₃ * H.ι MA.k * d₃⁻¹) * (d₃ * d₃) * H.ι MA.k by
        group, hk', hd₃sq', ← map_mul, ← map_mul, dc_k_sq D.e D.c₂ D.hc₂]

end DC.PD

theorem nonempty_TD (H : AD S T₁) : Nonempty H.TD := by
  obtain ⟨D⟩ := H.nonempty_DC
  obtain ⟨P⟩ := D.nonempty_PD
  exact P.nonempty_TD

end AD

end KD8ab

end CFSG.ComponentClassification.HSFLit
