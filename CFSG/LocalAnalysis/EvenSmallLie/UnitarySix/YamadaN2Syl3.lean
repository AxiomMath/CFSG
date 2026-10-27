module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaN2PiSyl
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaN2Syl

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaN2

open Subgroup CFSG.ABGLocalTools CFSG.EvenSmallLie.UnitarySix.YamadaEnd
  CFSG.EvenSmallLie.UnitarySix.YamadaPar
open scoped commutatorElement

section Bar

variable {G : Type} [Group G] {D₂ K₂ D₁ : Subgroup G}
variable [(D₂.subgroupOf (nTwo D₂ K₂ D₁)).Normal]

@[expose] noncomputable def barG2 (D₂ K₂ D₁ : Subgroup G)
    [(D₂.subgroupOf (nTwo D₂ K₂ D₁)).Normal] (Y : Subgroup G) :
    Subgroup (↥(nTwo D₂ K₂ D₁) ⧸ D₂.subgroupOf (nTwo D₂ K₂ D₁)) :=
  (Y.subgroupOf (nTwo D₂ K₂ D₁)).map (mk2 D₂ K₂ D₁)

theorem mk2_mem_barG2_iff {Y : Subgroup G} (hDY : D₂ ≤ Y) (n : nTwo D₂ K₂ D₁) :
    mk2 D₂ K₂ D₁ n ∈ barG2 D₂ K₂ D₁ Y ↔ (n : G) ∈ Y := by
  constructor
  · rintro ⟨y, hy, hyn⟩
    rw [Y14Hyp.mk2_eq_iff] at hyn
    have : (n : G) = y * ((y : G)⁻¹ * n) := by group
    rw [this]
    exact mul_mem hy (hDY hyn)
  · intro hn
    exact ⟨n, hn, rfl⟩

theorem card_eq_mul_card_barG2 {Y : Subgroup G} (hDY : D₂ ≤ Y) (hYN : Y ≤ nTwo D₂ K₂ D₁) :
    Nat.card Y = Nat.card D₂ * Nat.card (barG2 D₂ K₂ D₁ Y) := by
  set f : Y →* (↥(nTwo D₂ K₂ D₁) ⧸ D₂.subgroupOf (nTwo D₂ K₂ D₁)) :=
    (mk2 D₂ K₂ D₁).comp (Subgroup.inclusion hYN)
  have hker : f.ker = D₂.subgroupOf Y := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.comp_apply,
      ← map_one (mk2 D₂ K₂ D₁), Y14Hyp.mk2_eq_iff]
    simp
  have hrange : f.range = barG2 D₂ K₂ D₁ Y := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨Subgroup.inclusion hYN y, y.2, rfl⟩
    · rintro ⟨n, hn, rfl⟩
      exact ⟨⟨n, hn⟩, rfl⟩
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hrange, hker,
    card_subgroupOf_of_le hDY, mul_comm]

theorem barG2_inf_conjR {P : Subgroup G} (hDP : D₂ ≤ P)
    (hN : nTwo D₂ K₂ D₁ ≤ normalizer (D₂ : Set G)) {w : G} (hw : w ∈ nTwo D₂ K₂ D₁) :
    barG2 D₂ K₂ D₁ (P ⊓ conjR P w) =
      barG2 D₂ K₂ D₁ P ⊓ conjR (barG2 D₂ K₂ D₁ P) (mk2 D₂ K₂ D₁ ⟨w, hw⟩) := by
  have hDw : D₂ ≤ conjR P w := fun d hd => by
    rw [mem_conjR]
    exact hDP ((mem_normalizer_iff.mp (hN hw) d).mp hd)
  ext x
  obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective (D₂.subgroupOf (nTwo D₂ K₂ D₁)) x
  change mk2 D₂ K₂ D₁ n ∈ _ ↔ mk2 D₂ K₂ D₁ n ∈ _
  have : mk2 D₂ K₂ D₁ ⟨w, hw⟩ * mk2 D₂ K₂ D₁ n * (mk2 D₂ K₂ D₁ ⟨w, hw⟩)⁻¹ =
      mk2 D₂ K₂ D₁ (⟨w, hw⟩ * n * ⟨w, hw⟩⁻¹) := by simp only [map_mul, map_inv]
  rw [mk2_mem_barG2_iff (le_inf hDP hDw), Subgroup.mem_inf, Subgroup.mem_inf,
    mk2_mem_barG2_iff hDP, mem_conjR, mem_conjR, this, mk2_mem_barG2_iff hDP]
  rfl

end Bar

section W1

variable {G : Type} [Group G] {t : G} {D₁ V₁ D₂ A₂ K₂ : Subgroup G} {θ₂ : SL3 →* G}
  {ιG : (Fin 9 → ZMod 2) → G}

theorem Y14Hyp.card_P_w₁ [Finite G] (h : Y14Hyp t D₁ V₁ D₂ A₂ K₂ θ₂ ιG) {P : Subgroup G}
    (hD₂P : D₂ ≤ P) (hPN : P ≤ nTwo D₂ K₂ D₁) (hP : Nat.card P = 2 ^ 30)
    (hPU : ∀ u ∈ U3, θ₂ u ∈ P) {w₁ : G} {g : SL3} (hg : θ₂ g = w₁)
    (hgU : Nat.card (U3 ⊓ conjR U3 g : Subgroup SL3) = 2 ^ 4) :
    Nat.card (P ⊓ conjR P w₁ : Subgroup G) = 2 ^ 26 := by
  have : Fact (ElemSec D₂ (⊥ : Subgroup G)) := ⟨h.elemSec⟩
  have hN := h.normal_nTwo
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, X, h1, h2, h3, ψ, hψ, hk, hθ⟩ := h.r3bHyp.main
  have hττ := h.pi_ττ
  have hθφ : ∀ u, theta2 h u = phiG (tauG2 h) ψ h2 (u, u) := fun u => by
    rw [phiG_apply, psiG_apply, hθ u]
  have hPb : Nat.card (barG2 D₂ K₂ D₁ P) = 2 ^ 12 := by
    have := card_eq_mul_card_barG2 hD₂P hPN
    rw [hP, h.card_D₂] at this
    have h2' : 2 ^ 18 * Nat.card (barG2 D₂ K₂ D₁ P) = 2 ^ 18 * 2 ^ 12 := by
      rw [← this]; norm_num
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h2'
  have hP2 : IsPGroup 2 (barG2 D₂ K₂ D₁ P) := IsPGroup.of_card hPb
  have hθP : ∀ u ∈ U3, phiG (tauG2 h) ψ h2 (u, u) ∈ barG2 D₂ K₂ D₁ P := fun u hu => by
    rw [← hθφ, h.theta2_apply, mk2_mem_barG2_iff hD₂P]
    exact hPU u hu
  have hle := le_Pi h1 h2 h3 hk hττ hψ hP2 hθP
  have hPPi : barG2 D₂ K₂ D₁ P = (U3.prod U3).map (phiG (tauG2 h) ψ h2) :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [card_Pi h1 h2 h3 hk hττ, hPb])
  have hw : w₁ ∈ nTwo D₂ K₂ D₁ := hg ▸ h.θ_mem g
  have hwb : mk2 D₂ K₂ D₁ ⟨w₁, hw⟩ = phiG (tauG2 h) ψ h2 (g, g) := by
    rw [← hθφ, h.theta2_apply]
    congr 1
    exact Subtype.ext hg.symm
  have hDw : D₂ ≤ conjR P w₁ := fun d hd => by
    rw [mem_conjR]
    exact hD₂P ((mem_normalizer_iff.mp (h.nTwo_le_normalizer hw) d).mp hd)
  rw [card_eq_mul_card_barG2 (le_inf hD₂P hDw) (inf_le_left.trans hPN),
    barG2_inf_conjR hD₂P h.nTwo_le_normalizer hw, hwb, hPPi,
    card_Pi_inf_conjR h1 h2 h3 hk hττ g, hgU, h.card_D₂]
  norm_num

theorem Y14Hyp.P_fields [Finite G] (h : Y14Hyp t D₁ V₁ D₂ A₂ K₂ θ₂ ιG)
    {S P X₁ X₂ : Subgroup G} {w₁ w₂ j : G} {g₁ : SL3}
    (hG1 : ∀ x ∈ normalizer (D₂ : Set G), x⁻¹ * (t * x * t⁻¹) ∈ D₂ →
      ∃ y ∈ normalizer (A₂ : Set G) ⊓ centralizer ({t} : Set G), y⁻¹ * x ∈ D₂)
    (hG2 : normalizer (A₂ : Set G) ⊓ centralizer ({t} : Set G) ≤
      K₂ ⊔ (normalizer (S : Set G) ⊓ centralizer ({t} : Set G)))
    (hNS : normalizer (S : Set G) ⊓ centralizer ({t} : Set G) ≤
      normalizer (D₂ : Set G) ⊓ normalizer ((K₂ ⊔ A₂ : Subgroup G) : Set G) ⊓
        normalizer (D₁ : Set G))
    (hSK : S ≤ K₂ ⊔ A₂) (hK₂ : K₂ = X₁ ⊔ X₂ ⊔ zpowers w₁ ⊔ zpowers w₂) (hX₁ : X₁ ≤ S)
    (hX₂ : X₂ ≤ S) (hU : ∀ u ∈ U3, θ₂ u ∈ S) (hw₁ : θ₂ g₁ = w₁)
    (hgU : Nat.card (U3 ⊓ conjR U3 g₁ : Subgroup SL3) = 2 ^ 4)
    (hP : Nat.card P = 2 ^ 30) (hSP : S ≤ P) (hD₁P : D₁ ≤ P) (hD₂P : D₂ ≤ P)
    (htP : t ∈ normalizer (P : Set G)) (hPD₁ : P ≤ normalizer (D₁ : Set G))
    (hPD₂ : P ≤ normalizer (D₂ : Set G))
    (hab : ∀ x ∈ P, ∀ y ∈ P, x * y * x⁻¹ * y⁻¹ ∈ D₁ ⊔ D₂) (hsq : ∀ x ∈ P, x * x ∈ D₁ ⊔ D₂)
    (hPt : ∀ x ∈ P, x * t * x⁻¹ * t⁻¹ ∈ D₁ ⊔ D₂ → x ∈ S ⊔ D₁ ⊔ D₂)
    (hj : j ∈ K₂) (hjP : j ∈ normalizer (P : Set G)) (hj3 : j ^ 3 = 1)
    (hjfix : ∀ x ∈ P, j * x * j⁻¹ * x⁻¹ ∈ D₁ ⊔ D₂ → x ∈ D₁ ⊔ D₂) :
    P ≤ nTwo D₂ K₂ D₁ ∧ IsSylowOf 2 P (nTwo D₂ K₂ D₁) ∧
      Nat.card (P ⊓ conjR P w₁ : Subgroup G) = 2 ^ 26 ∧
      nTwo D₂ K₂ D₁ = P ⊔ zpowers w₁ ⊔ zpowers w₂ := by
  have hG := normalizer_nTwo_of_global h.A₂_le hG1 hG2 hNS
  have hSN : S ≤ nTwo D₂ K₂ D₁ :=
    hSK.trans (sup_le K₂_le_nTwo (h.A₂_le.trans D₂_le_nTwo))
  have hQN : S ⊔ D₁ ⊔ D₂ ≤ nTwo D₂ K₂ D₁ := sup_le (sup_le hSN D₁_le_nTwo) D₂_le_nTwo
  have hQP : D₁ ⊔ D₂ ≤ P := sup_le hD₁P hD₂P
  have hPQ : P ≤ normalizer ((D₁ ⊔ D₂ : Subgroup G) : Set G) := fun x hx =>
    mem_normalizer_sup' (hPD₁ hx) (hPD₂ hx)
  have hPt' : ∀ p ∈ P, p * t * p⁻¹ * t⁻¹ ∈ nTwo D₂ K₂ D₁ := fun p hp =>
    hQN (comm_t_mem h.t_sq htP hsq hPt p hp)
  have hJ := fix_identity hQP hPQ hab hsq hjP hj3 hjfix
  have hPN : P ≤ nTwo D₂ K₂ D₁ := h.le_nTwo hG hPD₂ hPt' (K₂_le_nTwo hj) hJ
  exact ⟨hPN, h.isSylowOf hPN hP,
    h.card_P_w₁ hD₂P hPN hP (fun u hu => hSP (hU u hu)) hw₁ hgU,
    nTwo_eq_sup_P hK₂ (hX₁.trans hSP) (hX₂.trans hSP) hPN hD₁P hD₂P⟩

end W1

end CFSG.EvenSmallLie.UnitarySix.YamadaN2
