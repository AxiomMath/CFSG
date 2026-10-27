module

public import CFSG.LocalAnalysis.EvenBN.U5.LinSec43TwoCtx
public import CFSG.LocalAnalysis.EvenBN.U5.LinSec43TwoGenB

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.ABGLocalTools (IsSylowOf)
open scoped MatrixGroups

namespace LinT43

open Matrix

theorem conj_mem_of_isNaturalModule {G : Type*} [Group G] {k : Type*} [Field k] {R : Subgroup G}
    {φ : R ≃* SL(2, k)} {θ : (Fin 2 → k) → G}
    (hθ : CFSG.Timmesfeld.ARS.IsNaturalModule φ θ) {A : Subgroup G}
    (hA : Set.range θ = (A : Set G)) {y a : G} (hy : y ∈ R) (ha : a ∈ A) : y * a * y⁻¹ ∈ A := by
  have ha' : a ∈ Set.range θ := by
    rw [hA]
    exact ha
  obtain ⟨v, rfl⟩ := ha'
  have h1 : y * θ v * y⁻¹ = θ (((φ ⟨y, hy⟩ : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) *ᵥ v) :=
    (hθ.map_mulVec ⟨y, hy⟩ v).symm
  rw [h1]
  have h2 : θ (((φ ⟨y, hy⟩ : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) *ᵥ v) ∈ Set.range θ :=
    Set.mem_range_self _
  rw [hA] at h2
  exact h2

end LinT43

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

namespace CaseBData

variable (hl : d.LinCtx) (k : d.Know12) (c : d.CaseBData)
include hl k c

theorem lin43_act_mod_F {d' p q' : G} (hd' : d' ∈ d.D) (hp : p ∈ c.X) (hq' : q' ∈ c.Y) :
    ∀ b ∈ c.Bc, (p * b * p⁻¹)⁻¹ * ((d' * p * q') * b * (d' * p * q')⁻¹) ∈ d.F := by
  intro b hb
  have hL₁F := lin_L₁_le_normalizer_F hl k c
  have hL₁B := lin_L₁_le_normalizer_Bc hl k c
  have hpL : p ∈ d.L₁ := lin_X_le_L₁ hl k c hp
  have hf₁ : q' * b * q'⁻¹ * b⁻¹ ∈ d.F := lin_comm_Bc_Y hl k c hb hq'
  set f₁ := q' * b * q'⁻¹ * b⁻¹ with hf₁def
  have hf₂ : p * f₁ * p⁻¹ ∈ d.F := (mem_normalizer_iff.1 (hL₁F hpL) f₁).1 hf₁
  have hb₂ : p * b * p⁻¹ ∈ c.Bc := (mem_normalizer_iff.1 (hL₁B hpL) b).1 hb
  have hb₂D : p * b * p⁻¹ ∈ d.D := lin_Bc_le_D hl k c hb₂
  have hf₃ : d' * (p * b * p⁻¹) * d'⁻¹ * (p * b * p⁻¹)⁻¹ ∈ d.F :=
    lin_commutator_mem_F hl k c hd' hb₂D
  set f₂ := p * f₁ * p⁻¹ with hf₂def
  set b₂ := p * b * p⁻¹ with hb₂def
  set f₃ := d' * b₂ * d'⁻¹ * b₂⁻¹ with hf₃def
  have hdf₂ : d' * f₂ * d'⁻¹ = f₂ := by
    have := mem_centralizer_iff.1 (lin_D_le_centralizer_F hl k c hd') f₂ hf₂
    rw [mul_inv_eq_iff_eq_mul]
    exact this.symm
  have e1 : (d' * p * q') * b * (d' * p * q')⁻¹ = f₂ * (f₃ * b₂) := by
    calc (d' * p * q') * b * (d' * p * q')⁻¹
        = d' * (p * (f₁ * b) * p⁻¹) * d'⁻¹ := by rw [hf₁def]; group
      _ = (d' * (f₂ * b₂) * d'⁻¹) := by rw [hf₂def, hb₂def]; group
      _ = (d' * f₂ * d'⁻¹) * (d' * b₂ * d'⁻¹) := by group
      _ = f₂ * (f₃ * b₂) := by rw [hdf₂, hf₃def]; group
  have hF₂₃ : f₂ * f₃ ∈ d.F := mul_mem hf₂ hf₃
  have hcomm : (f₂ * f₃) * b₂ = b₂ * (f₂ * f₃) :=
    mem_centralizer_iff.1 (lin_D_le_centralizer_F hl k c hb₂D) _ hF₂₃
  rw [e1]
  have : b₂⁻¹ * (f₂ * (f₃ * b₂)) = f₂ * f₃ := by
    calc b₂⁻¹ * (f₂ * (f₃ * b₂)) = b₂⁻¹ * ((f₂ * f₃) * b₂) := by group
      _ = b₂⁻¹ * (b₂ * (f₂ * f₃)) := by rw [hcomm]
      _ = f₂ * f₃ := by group
  exact this ▸ hF₂₃

theorem lin43_conj_D_F {d' v : G} (hd' : d' ∈ d.D) (hv : v ∈ d.F) : d' * v * d'⁻¹ = v := by
  have h1 : v * d' = d' * v := mem_centralizer_iff.1 (lin_D_le_centralizer_F hl k c hd') v hv
  rw [← h1]
  group

theorem lin43_conj_eq {d' y a : G} (hd' : d' ∈ d.D) (hya : y * a * y⁻¹ ∈ d.F) :
    (d' * y) * a * (d' * y)⁻¹ = y * a * y⁻¹ := by
  have h1 := lin43_conj_D_F hl k c hd' hya
  calc (d' * y) * a * (d' * y)⁻¹ = d' * (y * a * y⁻¹) * d'⁻¹ := by group
    _ = y * a * y⁻¹ := h1

theorem lin43_card_F_cent_le_q (h41 : c.Sec41) {d' q' : G} (hd' : d' ∈ d.D) (hq' : q' ∈ c.Y)
    (hq'1 : q' ≠ 1) :
    Nat.card (d.F ⊓ centralizer ({d' * q'} : Set G) : Subgroup G) ≤ (2 ^ f) ^ 4 := by
  obtain ⟨P', Q', -, -, -, -, ⟨θ₁, hθ₁, hr₁⟩, ⟨θ₂, hθ₂, hr₂⟩, -, -, hsup, hinf, -, -⟩ :=
    lin43_pair_full hl k c h41
  have hFab : ∀ a ∈ d.F, ∀ b ∈ d.F, a * b = b * a := fun a ha b hb =>
    Prelim.mul_comm_of_mem (lin_isElementaryAbelian_F hl k c) ha hb
  have hFY : ∀ a ∈ d.F, q' * a * q'⁻¹ ∈ d.F := fun a ha =>
    (mem_normalizer_iff.1 (lin_L₁_le_normalizer_F hl k c (lin_Y_le_L₁ hl k c hq')) a).1 ha
  have hact : ∀ a ∈ d.F, (d' * q') * a * (d' * q')⁻¹ = q' * a * q'⁻¹ := fun a ha =>
    lin43_conj_eq hl k c hd' (hFY a ha)
  have h1 := LinT43.card_inf_centralizer_le_of_split hFab hsup hinf (x := d' * q') (q := q')
    (fun a ha => hact a (Subgroup.mem_inf.1 ha).1)
    (fun a ha => LinT43.conj_mem_of_isNaturalModule hθ₁ hr₁ hq' ha)
    (fun a ha => LinT43.conj_mem_of_isNaturalModule hθ₂ hr₂ hq' ha)
    (fun a ha => by
      rw [hact a (Subgroup.mem_inf.1 ha).1, inv_mul_cancel]
      exact one_mem _)
  have hA₁ := LinT43.card_inf_centralizer_le_of_isNaturalModule hθ₁ hr₁ hq' hq'1
  have hA₂ := LinT43.card_inf_centralizer_le_of_isNaturalModule hθ₂ hr₂ hq' hq'1
  calc _ ≤ _ := h1
    _ ≤ Nat.card c.k * Nat.card c.k := Nat.mul_le_mul hA₁ hA₂
    _ = (2 ^ f) ^ 4 := by rw [lin43_card_k hl k c, ← pow_add]

theorem lin43_card_F_cent_le_p (h41 : c.Sec41) {d' p q' : G} (hd' : d' ∈ d.D) (hp : p ∈ c.X)
    (hp1 : p ≠ 1) (hq' : q' ∈ c.Y ⊓ c.S) :
    Nat.card (d.F ⊓ centralizer ({d' * p * q'} : Set G) : Subgroup G) ≤ (2 ^ f) ^ 4 := by
  obtain ⟨P', Q', -, -, -, -, ⟨θU, hθU, hrU⟩, ⟨θU', hθU', hrU'⟩, ⟨θW, hθW, hrW⟩,
    ⟨θW', hθW', hrW'⟩, hsupU, -, hsupW, hinfW⟩ := lin43_pair_full hl k c h41
  have hf2 := hl.hyp.two_le
  have hFab : ∀ a ∈ d.F, ∀ b ∈ d.F, a * b = b * a := fun a ha b hb =>
    Prelim.mul_comm_of_mem (lin_isElementaryAbelian_F hl k c) ha hb
  have hFY : ∀ a ∈ d.F, q' * a * q'⁻¹ ∈ d.F := fun a ha =>
    (mem_normalizer_iff.1 (lin_L₁_le_normalizer_F hl k c (lin_Y_le_L₁ hl k c hq'.1)) a).1 ha
  have hFX : ∀ a ∈ d.F, p * a * p⁻¹ ∈ d.F := fun a ha =>
    (mem_normalizer_iff.1 (lin_L₁_le_normalizer_F hl k c (lin_X_le_L₁ hl k c hp)) a).1 ha
  have hQsyl : IsSylowOf 2 (c.Y ⊓ c.S) c.Y :=
    s313a_isSylowOf_Y_inf_S hl.toCaseHyp k c.S_syl c.P_le_S c.ψ
  have hcomm_mem := LinT43.comm_mem_centralizer_of_isSylowOf c.card_k_eq (by omega : 1 ≤ 2 * f)
    c.φY hQsyl hθU hθU' hrU hrU' (by rw [hsupU]; exact hFab)
  have hw : ∀ a ∈ d.F, q' * a * q'⁻¹ * a⁻¹ ∈
      d.F ⊓ centralizer ((c.Y ⊓ c.S : Subgroup G) : Set G) := by
    intro a ha
    refine Subgroup.mem_inf.2 ⟨mul_mem (hFY a ha) (inv_mem ha), ?_⟩
    rw [mem_centralizer_iff]
    intro q'' hq''
    have h1 := hcomm_mem q' hq' q'' hq'' a (by rw [hsupU]; exact ha)
    exact mul_inv_eq_iff_eq_mul.1 h1
  have hact : ∀ a ∈ d.F ⊓ centralizer ((c.Y ⊓ c.S : Subgroup G) : Set G),
      (d' * p * q') * a * (d' * p * q')⁻¹ = p * a * p⁻¹ := by
    intro a ha
    have haF : a ∈ d.F := (Subgroup.mem_inf.1 ha).1
    have hcq : q' * a = a * q' := mem_centralizer_iff.1 (Subgroup.mem_inf.1 ha).2 q' hq'
    have hq'a : q' * a * q'⁻¹ = a := by
      rw [hcq]
      group
    have e1 : (d' * p * q') * a * (d' * p * q')⁻¹ = d' * (p * a * p⁻¹) * d'⁻¹ := by
      calc (d' * p * q') * a * (d' * p * q')⁻¹
          = d' * (p * (q' * a * q'⁻¹) * p⁻¹) * d'⁻¹ := by group
        _ = d' * (p * a * p⁻¹) * d'⁻¹ := by rw [hq'a]
    rw [e1]
    exact lin43_conj_D_F hl k c hd' (hFX a haF)
  have h1 := LinT43.card_inf_centralizer_le_of_split hFab hsupW hinfW (x := d' * p * q') (q := p)
    hact
    (fun a ha => LinT43.conj_mem_of_isNaturalModule hθW hrW hp ha)
    (fun a ha => LinT43.conj_mem_of_isNaturalModule hθW' hrW' hp ha)
    (fun a ha => by
      have haF : a ∈ d.F := (Subgroup.mem_inf.1 ha).1
      have ha'F : q' * a * q'⁻¹ ∈ d.F := hFY a haF
      have hpa'F : p * (q' * a * q'⁻¹) * p⁻¹ ∈ d.F := hFX _ ha'F
      have e1 : (d' * p * q') * a * (d' * p * q')⁻¹ = p * (q' * a * q'⁻¹) * p⁻¹ := by
        have h2 := lin43_conj_D_F hl k c hd' hpa'F
        calc (d' * p * q') * a * (d' * p * q')⁻¹
            = d' * (p * (q' * a * q'⁻¹) * p⁻¹) * d'⁻¹ := by group
          _ = p * (q' * a * q'⁻¹) * p⁻¹ := h2
      have e2 : (p * a * p⁻¹)⁻¹ * (p * (q' * a * q'⁻¹) * p⁻¹) =
          p * (q' * a * q'⁻¹ * a⁻¹) * p⁻¹ := by
        have hc : a⁻¹ * (q' * a * q'⁻¹) = (q' * a * q'⁻¹) * a⁻¹ := hFab _ (inv_mem haF) _ ha'F
        calc (p * a * p⁻¹)⁻¹ * (p * (q' * a * q'⁻¹) * p⁻¹)
            = p * (a⁻¹ * (q' * a * q'⁻¹)) * p⁻¹ := by group
          _ = p * ((q' * a * q'⁻¹) * a⁻¹) * p⁻¹ := by rw [hc]
      rw [e1, e2]
      exact LinT43.conj_mem_of_isNaturalModule hθW hrW hp (hw a haF))
  have hA₁ := LinT43.card_inf_centralizer_le_of_isNaturalModule hθW hrW hp hp1
  have hA₂ := LinT43.card_inf_centralizer_le_of_isNaturalModule hθW' hrW' hp hp1
  calc _ ≤ _ := h1
    _ ≤ Nat.card c.k * Nat.card c.k := Nat.mul_le_mul hA₁ hA₂
    _ = (2 ^ f) ^ 4 := by rw [lin43_card_k hl k c, ← pow_add]

theorem lin43_card_Bc_cent_le_p (h41 : c.Sec41) {d' p q' : G} (hd' : d' ∈ d.D) (hp : p ∈ c.X)
    (hp1 : p ≠ 1) (hq' : q' ∈ c.Y ⊓ c.S) :
    Nat.card (c.Bc ⊓ centralizer ({d' * p * q'} : Set G) : Subgroup G) ≤ (2 ^ f) ^ 6 := by
  have hnat := (lin_s12 hl k c).2.2
  have hpK : p ∈ d.M₁ ⊓ c.Kc := Subgroup.mem_inf.2 ⟨c.X_le_M₁ hp, lin_X_le_Kc hl k c hp⟩
  have h1 := LinT43.card_inf_centralizer_le_of_isNaturalSection hnat (lin_F_le_Bc hl k c) hpK hp1
    (fun b hb => (mem_normalizer_iff.1
      (lin_L₁_le_normalizer_F hl k c (lin_X_le_L₁ hl k c hp)) b).1 hb)
    (lin43_act_mod_F hl k c hd' hp hq'.1)
  have h2 := lin43_card_F_cent_le_p hl k c h41 hd' hp hp1 hq'
  calc _ ≤ _ := h1
    _ ≤ (2 ^ f) ^ 2 * (2 ^ f) ^ 4 :=
        Nat.mul_le_mul (lin43_card_k hl k c).le h2
    _ = (2 ^ f) ^ 6 := by rw [← pow_add]

theorem lin43_card_Bc_cent_le_q (h41 : c.Sec41) {d' q' : G} (hd' : d' ∈ d.D) (hq' : q' ∈ c.Y)
    (hq'1 : q' ≠ 1) :
    Nat.card (c.Bc ⊓ centralizer ({d' * q'} : Set G) : Subgroup G) ≤ (2 ^ f) ^ 8 := by
  have hrel : d.F.relIndex c.Bc ≤ (2 ^ f) ^ 4 := by
    have h := Subgroup.relIndex_mul_card d.F c.Bc
    rw [inf_eq_left.2 (lin_F_le_Bc hl k c), lin_card_F hl k c, lin_card_Bc hl k c] at h
    have hpos : 0 < (2 ^ f) ^ 8 := by positivity
    have : d.F.relIndex c.Bc = (2 ^ f) ^ 4 := by
      refine Nat.eq_of_mul_eq_mul_right hpos ?_
      rw [h]
      ring
    exact this.le
  have h1 := LinT43.card_inf_le_mul_inf (B' := c.Bc) (N := d.F)
    (Z := centralizer ({d' * q'} : Set G)) (lin_F_le_Bc hl k c) hrel
  have h2 := lin43_card_F_cent_le_q hl k c h41 hd' hq' hq'1
  calc _ ≤ _ := h1
    _ ≤ (2 ^ f) ^ 4 * (2 ^ f) ^ 4 := Nat.mul_le_mul_left _ h2
    _ = (2 ^ f) ^ 8 := by rw [← pow_add]

end CaseBData

end Data

end CFSG.LocalAnalysis.EvenBN.U5
