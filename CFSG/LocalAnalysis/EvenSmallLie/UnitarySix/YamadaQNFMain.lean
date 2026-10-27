module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaQNF
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaQConfig
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaBridgeQ

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaD

open Subgroup CFSG.EvenSmallLie.UnitarySix.YamadaQ CFSG.EvenSmallLie.UnitarySix.LemmaQ
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem mem_normalizer_commutator [Finite G] {A B : Subgroup G} {y : G}
    (hA : y ∈ normalizer (A : Set G)) (hB : y ∈ normalizer (B : Set G)) :
    y ∈ normalizer ((⁅A, B⁆ : Subgroup G) : Set G) := by
  apply mem_normalizer_of_conj_mem
  have hle : ⁅A, B⁆ ≤ ⁅A, B⁆.comap (MulAut.conj y).toMonoidHom := by
    rw [commutator_le]
    intro a ha b hb
    change y * ⁅a, b⁆ * y⁻¹ ∈ ⁅A, B⁆
    rw [conjugate_commutatorElement]
    exact commutator_mem_commutator ((mem_normalizer_iff.mp hA a).mp ha)
      ((mem_normalizer_iff.mp hB b).mp hb)
  exact fun c hc => hle hc

theorem mem_normalizer_inf_centralizer [Finite G] {Q W : Subgroup G} {y : G}
    (hQ : y ∈ normalizer (Q : Set G)) (hW : y ∈ normalizer (W : Set G)) :
    y ∈ normalizer ((Q ⊓ centralizer (W : Set G) : Subgroup G) : Set G) :=
  Hyp.mem_normalizer_inf hQ (mem_normalizer_of_conj_mem fun _ hc => conj_mem_centralizer hW hc)

namespace Hyp

variable [Finite G] {d : Data G} (h : Hyp d)
include h

omit [Finite G] in
theorem X₁_le_cent_e (hQ : HypQ d) : d.X₁ ≤ centralizer ({d.e} : Set G) := fun x hx =>
  mem_centralizer_singleton_iff.mpr (h.Λ_comm_Sig x (h.X₁_le_Λ hx) d.e hQ.e_mem_Sig)

omit [Finite G] in
theorem Q₁_le_cent_e (hQ : HypQ d) : d.Q₁ ≤ centralizer ({d.e} : Set G) :=
  sup_le (h.X₁_le_cent_e hQ) D_le_cent_e

theorem isPGroup_Q₁ : IsPGroup 2 d.Q₁ := by
  have hX : IsPGroup 2 d.X₁ := IsPGroup.of_card (n := 2) (by rw [h.card_X₁]; norm_num)
  exact hX.to_sup_of_normal_right' (isPGroup_C₄.to_le D_le_C₄) h.X₁_le_normalizer_D

theorem centInvSup_D₄ : centInvSup d.D₄ d.t = d.withT d.A₄ := by
  rw [centInvSup, Data.withT, ← h.D₄_inf_H]
  rfl

theorem Q₁_le_normalizer : d.Q₁ ≤ normalizer ((centInvSup d.D₄ d.t : Subgroup G) : Set G) := by
  rw [h.centInvSup_D₄]
  exact sup_le (fun x hx => h.Λ_le_X₄ (h.X₁_le_Λ hx)) D_le_X₄

omit [Finite G] in
theorem J_le_cent_e (hQ : HypQ d) : d.J ≤ centralizer ({d.e} : Set G) := by
  rw [h.J_eq, zpowers_le]; exact mem_centralizer_singleton_iff.mpr hQ.j₀_comm_e

omit [Finite G] in
theorem J_comm_t {j : G} (hj : j ∈ d.J) : j * d.t = d.t * j := h.comm_of_mem_L (h.J_le_L hj)

theorem J_le_normalizer_X₁ : d.J ≤ normalizer (d.X₁ : Set G) := by
  rw [h.J_eq, zpowers_le]; exact h.j₀_mem_normalizer_X₁

theorem J_le_normalizer_D₁ : d.J ≤ normalizer (d.D₁ : Set G) := by
  rw [h.J_eq, zpowers_le]
  exact Hyp.XV_le_normalizer_D₁ (h.X_le_XV (CHz_le_X
    ⟨mem_centralizer_singleton_iff.mpr h.j₀_comm_z, h.L_le_H h.j₀_mem_L⟩))

theorem J_le_normalizer_E₁ (hQ : HypQ d) :
    d.J ≤ normalizer ((d.D₁ ⊓ centralizer ({d.e} : Set G) : Subgroup G) : Set G) := fun _ hj =>
  mem_normalizer_inf (h.J_le_normalizer_D₁ hj)
    (mem_normalizer_cent_of_comm (mem_centralizer_singleton_iff.mp (h.J_le_cent_e hQ hj)))

omit [Finite G] in
theorem j₀_conj_u₁u₂ : d.j₀ * (d.u₁ * d.u₂) * d.j₀⁻¹ = d.u₁ := by
  calc d.j₀ * (d.u₁ * d.u₂) * d.j₀⁻¹ = (d.j₀ * d.u₁ * d.j₀⁻¹) * (d.j₀ * d.u₂ * d.j₀⁻¹) := by
        group
    _ = d.u₂ * (d.u₁ * d.u₂) := by rw [h.j₀_u₁, h.j₀_u₂]
    _ = d.u₁ := by rw [← mul_assoc, ← h.u₁_comm_u₂, mul_assoc, h.u₂_sq, mul_one]

omit [Finite G] in
theorem J_trans : ∀ a ∈ d.X₁, ∀ b ∈ d.X₁, a ≠ 1 → b ≠ 1 → ∃ j ∈ d.J, j⁻¹ * a * j = b := by
  have hj : d.j₀ ∈ d.J := by rw [h.J_eq]; exact mem_zpowers _
  have c1 : ∀ x, (d.j₀⁻¹)⁻¹ * x * d.j₀⁻¹ = d.j₀ * x * d.j₀⁻¹ := fun x => by group
  have c2 : ∀ x, (d.j₀⁻¹ * d.j₀⁻¹)⁻¹ * x * (d.j₀⁻¹ * d.j₀⁻¹) =
      d.j₀ * (d.j₀ * x * d.j₀⁻¹) * d.j₀⁻¹ := fun x => by
    rw [mul_inv_rev, inv_inv]; simp only [mul_assoc]
  have m0 : (1 : G) ∈ d.J := one_mem _
  have m1 : d.j₀⁻¹ ∈ d.J := inv_mem hj
  have m2 : d.j₀⁻¹ * d.j₀⁻¹ ∈ d.J := mul_mem (inv_mem hj) (inv_mem hj)
  have e0 : ∀ x : G, (1 : G)⁻¹ * x * 1 = x := fun x => by group
  intro a ha b hb ha1 hb1
  rcases h.X₁_cases ha with rfl | rfl | rfl | rfl
  · exact absurd rfl ha1
  · rcases h.X₁_cases hb with rfl | rfl | rfl | rfl
    · exact absurd rfl hb1
    · exact ⟨1, m0, e0 _⟩
    · exact ⟨d.j₀⁻¹, m1, by rw [c1, h.j₀_u₁]⟩
    · exact ⟨d.j₀⁻¹ * d.j₀⁻¹, m2, by rw [c2, h.j₀_u₁, h.j₀_u₂]⟩
  · rcases h.X₁_cases hb with rfl | rfl | rfl | rfl
    · exact absurd rfl hb1
    · exact ⟨d.j₀⁻¹ * d.j₀⁻¹, m2, by rw [c2, h.j₀_u₂, h.j₀_conj_u₁u₂]⟩
    · exact ⟨1, m0, e0 _⟩
    · exact ⟨d.j₀⁻¹, m1, by rw [c1, h.j₀_u₂]⟩
  · rcases h.X₁_cases hb with rfl | rfl | rfl | rfl
    · exact absurd rfl hb1
    · exact ⟨d.j₀⁻¹, m1, by rw [c1, h.j₀_conj_u₁u₂]⟩
    · exact ⟨d.j₀⁻¹ * d.j₀⁻¹, m2, by rw [c2, h.j₀_conj_u₁u₂, h.j₀_u₁]⟩
    · exact ⟨1, m0, e0 _⟩

section W

variable (hB : HypB d) (hV : ∀ v ∈ d.V₁, v * v = 1) {d₀ : G} (hd₀ : d₀ ∈ d.D₄)
  (hθ : d₀⁻¹ * d.t * d₀ * d.t = d.a₀)
include hB hV hd₀ hθ

theorem W₁_le_D₄ : ⁅⁅d.Q₁, d.Q₁⁆, d.Q₁⁆ ≤ d.D₄ := (h.W₁_le_V₂ hd₀ hB hV hθ).trans h.V₂_le_D₄

theorem D₄_eq_inf_cent :
    d.D₄ = d.Q₁ ⊓ centralizer ((⁅⁅d.Q₁, d.Q₁⁆, d.Q₁⁆ : Subgroup G) : Set G) := by
  refine le_antisymm (le_inf h.D₄_le_Q₁ fun x hx => mem_centralizer_iff.mpr fun w hw =>
    h.D₄_comm (h.W₁_le_D₄ hB hV hd₀ hθ hw) hx) ?_
  rintro q ⟨hq, hc⟩
  refine h.mem_D₄_of_cent hd₀ hB hV hθ hq fun w hw => ?_
  have hw' : w ∈ ⁅⁅d.Q₁, d.Q₁⁆, d.Q₁⁆ :=
    sup_le (h.Z₂S_le_W₁ hd₀ hB hV hθ) (h.V₁_le_W₁ hd₀ hB hV hθ) hw
  exact ((mem_centralizer_iff.mp hc) w hw').symm

theorem inf_H_W₁ : ⁅⁅d.Q₁, d.Q₁⁆, d.Q₁⁆ ⊓ d.H = d.Z₂S := by
  refine le_antisymm (fun x hx => ?_)
    (le_inf (h.Z₂S_le_W₁ hd₀ hB hV hθ) (h.Z₂S_le_A₄.trans (h.A₄_le_L.trans h.L_le_H)))
  rw [← h.V₂_inf_H]
  exact ⟨h.W₁_le_V₂ hd₀ hB hV hθ hx.1, hx.2⟩

theorem D₁_le_normalizer_W₁ (hC : HypC d) :
    d.D₁ ≤ normalizer ((⁅⁅d.Q₁, d.Q₁⁆, d.Q₁⁆ : Subgroup G) : Set G) :=
  h.D₁_le_normalizer_of hB hC hV (h.V₁_le_W₁ hd₀ hB hV hθ)
    ((h.W₁_le_V₂ hd₀ hB hV hθ).trans (h.V₂_le_D₁ hB hV))

end W

theorem configN_nf (hB : HypB d) (hC : HypC d) (hV : ∀ v ∈ d.V₁, v * v = 1) (hQ : HypQ d)
    (hN : HypNF d) {d₀ : G} (hd₀ : d₀ ∈ d.D₄) (hθ : d₀⁻¹ * d.t * d₀ * d.t = d.a₀) :
    ConfigN (centralizer ({d.e} : Set G)) d.D₄ d.X₁ d.Q₁ d.J (⁅⁅d.Q₁, d.Q₁⁆, d.Q₁⁆)
      (d.D₁ ⊓ centralizer ({d.e} : Set G)) d.t := by
  have P := h.configPart hB hV hQ.CA₁e
  have hW : ∀ y : G, y ∈ normalizer (d.Q₁ : Set G) →
      y ∈ normalizer ((⁅⁅d.Q₁, d.Q₁⁆, d.Q₁⁆ : Subgroup G) : Set G) := fun y hy =>
    mem_normalizer_commutator (mem_normalizer_commutator hy hy) hy
  refine
    { t_sq := P.t_sq, D_le := P.D_le, D_comm := P.D_comm, D_sq := P.D_sq, t_normD := P.t_normD,
      D_conj := P.D_conj, normD_of_norm := P.normD_of_norm,
      Q_le := h.Q₁_le_cent_e hQ, t_memQ := h.t_mem_Q₁, Q_pGroup := h.isPGroup_Q₁,
      Q_le_norm := h.Q₁_le_normalizer,
      Q_max := Q_max_of_card_le fun R hR hRY hRN => ?_,
      Q_not_sylow := h.not_sylow_Q₁ hB hC hV hQ hd₀ hθ,
      normD_of_normQ := fun y _ hy => ?_,
      normW_of_normQ := fun y _ hy => hW y hy,
      fusion := fun y _ _ hy => h.fusion_Q₁ hB hV hQ hd₀ hθ hy,
      J_le := h.J_le_cent_e hQ, J_comm := fun j hj => h.J_comm_t hj,
      J_normX := h.J_le_normalizer_X₁, J_normD := h.J_le_normalizer_D₄, J_trans := h.J_trans,
      W_le := h.W₁_le_D₄ hB hV hd₀ hθ,
      E_le := P.E_le, E_t := P.E_t,
      E_normW := fun j hj u hu => ?_,
      normW_cent := fun j hj c hcY hct hcW => ?_ }
  ·
    rw [h.centInvSup_D₄] at hRN
    have h1 := h.card_le_of_normalizer R hRN
    have h2 : R ⊓ centralizer ({d.t} : Set G) ≤
        d.H ⊓ centralizer ({d.e} : Set G) ⊓ normalizer (d.A₄ : Set G) := fun x hx =>
      ⟨⟨hx.2, hRY hx.1⟩, h.X₄_le_normalizer_A₄ (hRN hx.1)⟩
    have h3 := hN.card_le _ h2 (hR.to_le inf_le_left)
    rw [h.card_Q₁ hB hV hd₀ hθ]
    calc Nat.card R ≤ 2 ^ 4 * Nat.card (R ⊓ centralizer ({d.t} : Set G) : Subgroup G) := h1
      _ ≤ 2 ^ 4 * 2 ^ 7 := by gcongr
      _ = 2 ^ 11 := by norm_num
  ·
    rw [h.D₄_eq_inf_cent hB hV hd₀ hθ]
    exact mem_normalizer_inf_centralizer hy (hW y hy)
  ·
    have hju := (mem_normalizer_iff.mp (h.J_le_normalizer_E₁ hQ hj) u).mp hu
    exact h.D₁_le_normalizer_W₁ hB hV hd₀ hθ hC hju.1
  ·
    have hjH : j ∈ d.H := h.L_le_H (h.J_le_L hj)
    have hcH : c ∈ d.H := mem_centralizer_singleton_iff.mpr hct
    have hc'H : j * c * j⁻¹ ∈ d.H := d.H.mul_mem (d.H.mul_mem hjH hcH) (d.H.inv_mem hjH)
    have hc'e : j * c * j⁻¹ ∈ centralizer ({d.e} : Set G) :=
      mul_mem (mul_mem (h.J_le_cent_e hQ hj) hcY) (inv_mem (h.J_le_cent_e hQ hj))
    have hc'Z : j * c * j⁻¹ ∈ normalizer (d.Z₂S : Set G) := by
      rw [← h.inf_H_W₁ hB hV hd₀ hθ]
      exact mem_normalizer_inf hcW (le_normalizer hc'H)
    have hc'A := hQ.NZ₂S _ hc'H (mem_centralizer_singleton_iff.mp hc'e) hc'Z
    have hjA : j ∈ normalizer (d.A₄ : Set G) := h.X₄_le_normalizer_A₄ (h.J_le_X₄ hj)
    have hcA : c ∈ normalizer (d.A₄ : Set G) := by
      have := mul_mem (mul_mem (inv_mem hjA) hc'A) hjA
      simpa [mul_assoc] using this
    rw [h.centInvSup_D₄, Data.withT]
    exact mem_normalizer_sup hcA (mem_normalizer_zpowers hct)

end Hyp

end CFSG.EvenSmallLie.UnitarySix.YamadaD
