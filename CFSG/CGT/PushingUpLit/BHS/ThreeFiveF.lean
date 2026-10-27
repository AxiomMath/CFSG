module

public import CFSG.CGT.PushingUpLit.BHS.ThreeFiveE

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin CFSG.CGT.PushingUpLit.BHS.Glauberman CFSG.RankThree.PartOne CFSG.Open
  CFSG.LieType.BorelTits

local macro "comm_group" : tactic =>
  `(tactic| (apply Additive.ofMul.injective
             simp only [ofMul_mul, ofMul_inv, ofMul_div, ofMul_one]
             abel))

variable {V : Type} [CommGroup V] {Γ : Type} [Group Γ]

namespace ThreeFiveHyp

variable {ρ : Γ →* MulAut V} {T M A : Subgroup Γ} (h : ThreeFiveHyp ρ T M A)

include h

variable [Finite V] [Finite Γ]

theorem glHyp_secF : GlHyp ((⊤ : Subgroup Γ).map (secF ρ T)) (M.map (secF ρ T))
    (T.map (secF ρ T)) (A.map (secF ρ T)) where
  hV := sec_sq_eq_one' h.hV _ _
  lt := h.map_maximal_secF.1
  max := h.map_maximal_secF.2
  syl := h.isSylowOf_map_secF
  le := Subgroup.map_mono h.le_T
  ne := h.map_secF_ne_bot
  el := h.isElemAbelian2_map_secF
  o2 := h.pCoreOf_map_secF
  quad := h.isQuadratic_map_secF
  gen := fun _ hg hgM => h.sup_zpowers_map_secF hg hgM
  fix := h.fixV_map_secF
  off := h.card_le_map_secF

theorem ker_eq_bot_of_card_eq
    (hcard : Nat.card (Sec (wMod ρ T) (fixV ρ.range)) =
      Nat.card (A.map (secF ρ T)) * Nat.card (fixV (A.map (secF ρ T)))) :
    A ⊓ (secF ρ T).ker = ⊥ ∧ wMod ρ T ⊔ fixV (A.map ρ) = ⊤ ∧
      Nat.card V = Nat.card A * Nat.card (fixV (A.map ρ)) := by
  set W := wMod ρ T with hW
  set Y := fixV ρ.range with hY
  set F := fixV (A.map ρ) with hF
  set f := secF ρ T with hf
  set K := A ⊓ f.ker with hK
  have hcardW : Nat.card (Sec W Y) * Nat.card Y = Nat.card W :=
    card_sec_mul (fixV_range_le_wMod ρ T)
  have hC := card_wMod_inf_le (ρ := ρ) (T := T) (A := A)
  have hkey := h.card_ker_mul_le
  have hA : Nat.card A = Nat.card (A.map f) * Nat.card K :=
    (B1More.card_map_mul_card_inf_ker A f).symm
  have heq : Nat.card A * Nat.card ↥(W ⊓ F) = Nat.card K * Nat.card W := by
    refine le_antisymm ?_ hkey
    calc Nat.card A * Nat.card ↥(W ⊓ F)
        ≤ Nat.card A * (Nat.card (fixV (A.map f)) * Nat.card Y) := Nat.mul_le_mul_left _ hC
      _ = Nat.card K * (Nat.card (A.map f) * Nat.card (fixV (A.map f)) * Nat.card Y) := by
          rw [hA]; ring
      _ = Nat.card K * (Nat.card (Sec W Y) * Nat.card Y) := by rw [hcard]
      _ = Nat.card K * Nat.card W := by rw [hcardW]
  have hKpos : 0 < Nat.card K := Nat.card_pos
  have hinfpos : 0 < Nat.card ↥(W ⊓ F) := Nat.card_pos
  have hKsup : Nat.card K * Nat.card ↥(W ⊔ F) = Nat.card A * Nat.card F := by
    apply Nat.eq_of_mul_eq_mul_right hinfpos
    calc Nat.card K * Nat.card ↥(W ⊔ F) * Nat.card ↥(W ⊓ F)
        = Nat.card K * (Nat.card ↥(W ⊔ F) * Nat.card ↥(W ⊓ F)) := by ring
      _ = Nat.card K * (Nat.card W * Nat.card F) := by rw [card_sup_mul_card_inf W F]
      _ = (Nat.card K * Nat.card W) * Nat.card F := by ring
      _ = (Nat.card A * Nat.card ↥(W ⊓ F)) * Nat.card F := by rw [heq]
      _ = Nat.card A * Nat.card F * Nat.card ↥(W ⊓ F) := by ring
  have hKle : K.map ρ ≤ A.map ρ := Subgroup.map_mono inf_le_left
  have hwt := h.wt_le hKle
  have hKcard : Nat.card (K.map ρ) = Nat.card K := Subgroup.card_map_of_injective h.faithful
  have hAcard : Nat.card (A.map ρ) = Nat.card A := Subgroup.card_map_of_injective h.faithful
  rw [hKcard, hAcard] at hwt
  have hsup : W ⊔ F ≤ fixV (K.map ρ) := h.sup_le_fixV_ker
  have hcs : Nat.card ↥(W ⊔ F) ≤ Nat.card (fixV (K.map ρ)) := Subgroup.card_le_of_le hsup
  have hfix : Nat.card (fixV (K.map ρ)) = Nat.card ↥(W ⊔ F) := by
    refine Nat.le_antisymm ?_ hcs
    refine Nat.le_of_mul_le_mul_left ?_ hKpos
    rw [hKsup]
    exact hwt
  have hKA : Nat.card K * Nat.card (fixV (K.map ρ)) = Nat.card A * Nat.card F := by
    rw [hfix, hKsup]
  have hK0 : K.map ρ = ⊥ := by
    by_contra hne
    have hneA : K.map ρ ≠ A.map ρ := by
      intro hEq
      have hKA' : K = A := Subgroup.map_injective h.faithful hEq
      apply h.not_le_cenW
      intro a ha
      have : a ∈ K := by rw [hKA']; exact ha
      exact h.ker_secF_le.1 ⟨this.2, Subgroup.mem_top a⟩
    have := h.lt_wt (K.map ρ) hKle hne hneA
    rw [hKcard, hAcard] at this
    exact absurd hKA (Nat.ne_of_lt this)
  have hKbot : K = ⊥ := Subgroup.map_injective h.faithful (by rw [hK0, Subgroup.map_bot])
  have hsupeq : W ⊔ F = ⊤ := by
    have := Subgroup.eq_of_le_of_card_ge hsup hfix.le
    rw [this, hK0]
    exact B1.fixV_bot
  refine ⟨hKbot, hsupeq, ?_⟩
  rw [hKbot, Subgroup.card_bot, hsupeq] at hKsup
  rw [one_mul] at hKsup
  rw [← hKsup]
  exact (Nat.card_congr (Subgroup.topEquiv (G := V)).toEquiv).symm

omit [Finite Γ] in
theorem wMod_eq_top (hsup : wMod ρ T ⊔ fixV (A.map ρ) = ⊤) : wMod ρ T = ⊤ := by
  obtain ⟨x, hx⟩ := h.exists_not_mem
  set W := wMod ρ T with hW
  set F := fixV (A.map ρ) with hF
  set B := A.map (MulAut.conj x).toMonoidHom with hB
  have hYW : fixV ρ.range ≤ W := fixV_range_le_wMod ρ T
  have hFB : fixV (B.map ρ) = F.map (ρ x).toMonoidHom := by
    rw [hB, map_map_conj, fixV_map_conj]
  have hVB : ∀ v : V, ∃ w ∈ W, ∃ c ∈ fixV (B.map ρ), w * c = v := by
    intro v
    have hv : (ρ x)⁻¹ v ∈ W ⊔ F := by rw [hsup]; exact Subgroup.mem_top _
    obtain ⟨w, hw, c, hc, hwc⟩ := Subgroup.mem_sup.1 hv
    refine ⟨ρ x w, wMod_inv ρ T x hw, ρ x c, ?_, ?_⟩
    · rw [hFB]
      exact Subgroup.mem_map_of_mem _ hc
    · calc ρ x w * ρ x c = ρ x (w * c) := (map_mul _ _ _).symm
        _ = v := by rw [hwc]; simp
  rw [eq_top_iff]
  intro v _
  obtain ⟨w₁, hw₁, c₁, hc₁, hv1⟩ := Subgroup.mem_sup.1 (hsup ▸ Subgroup.mem_top v : v ∈ W ⊔ F)
  obtain ⟨w₂, hw₂, c₂, hc₂, hv2⟩ := hVB v
  have hmem : c₁ * c₂⁻¹ ∈ W := by
    have h12 : w₁ * c₁ = w₂ * c₂ := hv1.trans hv2.symm
    have : c₁ * c₂⁻¹ = w₁⁻¹ * w₂ := by
      calc c₁ * c₂⁻¹ = (w₁⁻¹ * (w₁ * c₁)) * c₂⁻¹ := by comm_group
        _ = (w₁⁻¹ * (w₂ * c₂)) * c₂⁻¹ := by rw [h12]
        _ = w₁⁻¹ * w₂ := by comm_group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hw₁) hw₂
  obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.1 (h.wMod_le_sup hx hmem)
  have hcA : c₁ * a⁻¹ ∈ F := Subgroup.mul_mem _ hc₁ (Subgroup.inv_mem _ ha.2)
  have hcB : c₁ * a⁻¹ ∈ fixV (B.map ρ) := by
    have : c₁ * a⁻¹ = b * c₂ := by
      calc c₁ * a⁻¹ = (c₁ * c₂⁻¹) * c₂ * a⁻¹ := by comm_group
        _ = (a * b) * c₂ * a⁻¹ := by rw [← hab]
        _ = b * c₂ := by comm_group
    rw [this]
    exact Subgroup.mul_mem _ hb.2 hc₂
  have hcY : c₁ * a⁻¹ ∈ fixV ρ.range := by
    rw [← h.fixV_inf_fixV hx]
    exact ⟨hcA, hcB⟩
  have : v = (w₁ * a) * (c₁ * a⁻¹) := by rw [← hv1]; comm_group
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hw₁ ha.1) (hYW hcY)

omit [Finite V] in
theorem ker_secF_eq_bot (hW : wMod ρ T = ⊤) : (secF ρ T).ker = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  have h1 := mem_cenMod.1 (h.ker_secF_le.1 ⟨hg, Subgroup.mem_top g⟩)
  rw [Subgroup.mem_bot]
  apply h.faithful
  rw [map_one]
  ext v
  simpa using h1 v (hW ▸ Subgroup.mem_top v)

end ThreeFiveHyp

end CFSG.CGT.PushingUpLit.BHS
