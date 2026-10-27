module

public import CFSG.LocalAnalysis.EvenBN.U5.LinSec43TwoGenA
public import CFSG.LocalAnalysis.EvenBN.Common.CoprimeQuotient
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.LocalAnalysis.EvenBN.U5

namespace LinT43

open Subgroup

variable {G : Type*} [Group G]

theorem card_inf_centralizer_le_of_split [Finite G] {F A A' : Subgroup G}
    (hF : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a) (hsup : A ⊔ A' = F) (hinf : A ⊓ A' = ⊥) {x q : G}
    (hAx : ∀ a ∈ A, x * a * x⁻¹ = q * a * q⁻¹) (hqA : ∀ a ∈ A, q * a * q⁻¹ ∈ A)
    (hqA' : ∀ a ∈ A', q * a * q⁻¹ ∈ A')
    (hA'x : ∀ a ∈ A', (q * a * q⁻¹)⁻¹ * (x * a * x⁻¹) ∈ A) :
    Nat.card (F ⊓ centralizer ({x} : Set G) : Subgroup G) ≤
      Nat.card (A ⊓ centralizer ({q} : Set G) : Subgroup G) *
        Nat.card (A' ⊓ centralizer ({q} : Set G) : Subgroup G) := by
  classical
  have hAF : A ≤ F := hsup ▸ le_sup_left
  have hA'F : A' ≤ F := hsup ▸ le_sup_right
  have hcomm : ∀ a ∈ A, ∀ b ∈ A', a * b = b * a := fun a ha b hb => hF a (hAF ha) b (hA'F hb)
  have hdec : ∀ v ∈ F, ∃ u ∈ A, ∃ u' ∈ A', v = u * u' := by
    intro v hv
    have hv' : v ∈ ((A ⊔ A' : Subgroup G) : Set G) := by rw [hsup]; exact hv
    rw [(CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A A' hcomm).2] at hv'
    obtain ⟨u, hu, u', hu', huv⟩ := hv'
    exact ⟨u, hu, u', hu', huv.symm⟩
  have huniq : ∀ a₁ ∈ A, ∀ a₂ ∈ A, ∀ b₁ ∈ A', ∀ b₂ ∈ A', a₁ * b₁ = a₂ * b₂ →
      a₁ = a₂ ∧ b₁ = b₂ := by
    intro a₁ ha₁ a₂ ha₂ b₁ hb₁ b₂ hb₂ h
    have h1 : a₂⁻¹ * a₁ = b₂ * b₁⁻¹ := by
      calc a₂⁻¹ * a₁ = a₂⁻¹ * (a₁ * b₁) * b₁⁻¹ := by group
        _ = a₂⁻¹ * (a₂ * b₂) * b₁⁻¹ := by rw [h]
        _ = b₂ * b₁⁻¹ := by group
    have hmem : a₂⁻¹ * a₁ ∈ A ⊓ A' :=
      Subgroup.mem_inf.2 ⟨mul_mem (inv_mem ha₂) ha₁, h1 ▸ mul_mem hb₂ (inv_mem hb₁)⟩
    rw [hinf, Subgroup.mem_bot] at hmem
    refine ⟨(inv_mul_eq_one.1 hmem).symm, ?_⟩
    rw [hmem] at h1
    exact (mul_inv_eq_one.1 h1.symm).symm
  set H : Subgroup G := F ⊓ centralizer ({x} : Set G) with hH
  have hdec' : ∀ v : H, ∃ u ∈ A, ∃ u' ∈ A', (v : G) = u * u' := fun v =>
    hdec _ (Subgroup.mem_inf.1 v.2).1
  choose uf huf u'f hu'f hvf using hdec'
  have hfix : ∀ v : H, x * (v : G) * x⁻¹ = v := by
    intro v
    have := mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 v.2).2
    rw [mul_inv_eq_iff_eq_mul]
    exact this.symm
  have key : ∀ v : H, q * u'f v * q⁻¹ = u'f v := by
    intro v
    have hu := huf v
    have hu' := hu'f v
    have hc : (q * u'f v * q⁻¹)⁻¹ * (x * u'f v * x⁻¹) ∈ A := hA'x _ hu'
    have hqu : q * uf v * q⁻¹ ∈ A := hqA _ hu
    have hqu' : q * u'f v * q⁻¹ ∈ A' := hqA' _ hu'
    have hxu : x * uf v * x⁻¹ = q * uf v * q⁻¹ := hAx _ hu
    set c := (q * u'f v * q⁻¹)⁻¹ * (x * u'f v * x⁻¹) with hcdef
    have e2 : x * u'f v * x⁻¹ = (q * u'f v * q⁻¹) * c := by rw [hcdef]; group
    have hfv := hfix v
    rw [hvf v] at hfv
    have e3 : x * (uf v * u'f v) * x⁻¹ = (x * uf v * x⁻¹) * (x * u'f v * x⁻¹) := by group
    rw [e3, hxu, e2] at hfv
    have hcc : (q * u'f v * q⁻¹) * c = c * (q * u'f v * q⁻¹) :=
      hF _ (hA'F hqu') _ (hAF hc)
    have e4 : uf v * u'f v = ((q * uf v * q⁻¹) * c) * (q * u'f v * q⁻¹) := by
      rw [← hfv]
      calc (q * uf v * q⁻¹) * ((q * u'f v * q⁻¹) * c)
          = (q * uf v * q⁻¹) * (c * (q * u'f v * q⁻¹)) := by rw [hcc]
        _ = ((q * uf v * q⁻¹) * c) * (q * u'f v * q⁻¹) := by group
    exact ((huniq _ hu _ (mul_mem hqu hc) _ hu' _ hqu' e4).2).symm
  have hρ : ∀ v w : H, u'f v = u'f w → (v : G)⁻¹ * (w : G) ∈ A ⊓ centralizer ({q} : Set G) := by
    intro v w hvw
    have hv := hvf v
    have hw := hvf w
    have hmemA : (uf v)⁻¹ * uf w ∈ A := mul_mem (inv_mem (huf v)) (huf w)
    have e : (v : G)⁻¹ * (w : G) = (uf v)⁻¹ * uf w := by
      have hcomm' : ((uf v)⁻¹ * uf w) * u'f v = u'f v * ((uf v)⁻¹ * uf w) :=
        hF _ (hAF hmemA) _ (hA'F (hu'f v))
      calc (v : G)⁻¹ * (w : G) = (u'f v)⁻¹ * ((uf v)⁻¹ * uf w) * u'f w := by
            rw [hv, hw]; group
        _ = (u'f v)⁻¹ * ((uf v)⁻¹ * uf w) * u'f v := by rw [← hvw]
        _ = (uf v)⁻¹ * uf w := by
          rw [mul_assoc, hcomm', ← mul_assoc, inv_mul_cancel, one_mul]
    have hax : x * ((v : G)⁻¹ * (w : G)) * x⁻¹ = (v : G)⁻¹ * (w : G) := by
      calc x * ((v : G)⁻¹ * (w : G)) * x⁻¹ = (x * (v : G) * x⁻¹)⁻¹ * (x * (w : G) * x⁻¹) := by
            group
        _ = (v : G)⁻¹ * (w : G) := by rw [hfix v, hfix w]
    rw [e] at hax
    have haq : q * ((uf v)⁻¹ * uf w) * q⁻¹ = (uf v)⁻¹ * uf w := by
      rw [← hAx _ hmemA]
      exact hax
    rw [e]
    exact Subgroup.mem_inf.2 ⟨hmemA, mem_centralizer_singleton_iff.2 (mul_inv_eq_iff_eq_mul.1 haq).symm⟩
  have hrange : Set.range (fun v : H => u'f v) ⊆
      ((A' ⊓ centralizer ({q} : Set G) : Subgroup G) : Set G) := by
    rintro _ ⟨v, rfl⟩
    refine Subgroup.mem_inf.2 ⟨hu'f v, mem_centralizer_singleton_iff.2 ?_⟩
    exact (mul_inv_eq_iff_eq_mul.1 (key v)).symm
  have h1 := LinT43.card_le_range_mul (fun v : H => u'f v) hρ
  have h2 : Nat.card (Set.range fun v : H => u'f v) ≤
      Nat.card (A' ⊓ centralizer ({q} : Set G) : Subgroup G) :=
    Nat.card_mono (Set.toFinite _) hrange
  calc Nat.card H ≤ Nat.card (Set.range fun v : H => u'f v) *
        Nat.card (A ⊓ centralizer ({q} : Set G) : Subgroup G) := h1
    _ ≤ Nat.card (A' ⊓ centralizer ({q} : Set G) : Subgroup G) *
        Nat.card (A ⊓ centralizer ({q} : Set G) : Subgroup G) := Nat.mul_le_mul_right _ h2
    _ = Nat.card (A ⊓ centralizer ({q} : Set G) : Subgroup G) *
        Nat.card (A' ⊓ centralizer ({q} : Set G) : Subgroup G) := mul_comm _ _


theorem card_le_mul_card_inf [Finite G] {T D A₀ : Subgroup G} (hA₀T : A₀ ≤ T) (hDT : D ≤ T)
    (hA₀D : A₀ ≤ normalizer (D : Set G)) {m : ℕ} (hT : Nat.card T ≤ m * Nat.card D) :
    Nat.card A₀ ≤ m * Nat.card (A₀ ⊓ D : Subgroup G) := by
  have h1 : Nat.card (D ⊔ A₀ : Subgroup G) * Nat.card (D ⊓ A₀ : Subgroup G) =
      Nat.card D * Nat.card A₀ := by
    exact Common.card_sup_mul_card_inf_eq hA₀D
  have h2 : Nat.card (D ⊔ A₀ : Subgroup G) ≤ Nat.card T :=
    Subgroup.card_le_of_le (sup_le hDT hA₀T)
  have hpos : 0 < Nat.card D := Nat.card_pos
  have h3 : Nat.card D * Nat.card A₀ ≤ Nat.card D * (m * Nat.card (D ⊓ A₀ : Subgroup G)) := by
    rw [← h1]
    calc Nat.card (D ⊔ A₀ : Subgroup G) * Nat.card (D ⊓ A₀ : Subgroup G)
        ≤ Nat.card T * Nat.card (D ⊓ A₀ : Subgroup G) := Nat.mul_le_mul_right _ h2
      _ ≤ (m * Nat.card D) * Nat.card (D ⊓ A₀ : Subgroup G) := Nat.mul_le_mul_right _ hT
      _ = Nat.card D * (m * Nat.card (D ⊓ A₀ : Subgroup G)) := by ring
  rw [inf_comm]
  exact Nat.le_of_mul_le_mul_left h3 hpos

theorem card_inf_le_mul_inf [Finite G] {B' N Z : Subgroup G} (hNB : N ≤ B') {m : ℕ}
    (hm : N.relIndex B' ≤ m) :
    Nat.card (B' ⊓ Z : Subgroup G) ≤ m * Nat.card (N ⊓ Z : Subgroup G) := by
  have h1 : N.relIndex (B' ⊓ Z) * Nat.card (N ⊓ (B' ⊓ Z) : Subgroup G) =
      Nat.card (B' ⊓ Z : Subgroup G) := Subgroup.relIndex_mul_card N (B' ⊓ Z)
  have h2 : N.relIndex (B' ⊓ Z) ≤ N.relIndex B' :=
    Subgroup.relIndex_le_of_le_right inf_le_left (Subgroup.index_ne_zero_of_finite)
  have h3 : N ⊓ (B' ⊓ Z) = N ⊓ Z := by
    rw [← inf_assoc, inf_eq_left.2 hNB]
  rw [h3] at h1
  rw [← h1]
  exact Nat.mul_le_mul (h2.trans hm) le_rfl

end LinT43

end CFSG.LocalAnalysis.EvenBN.U5
