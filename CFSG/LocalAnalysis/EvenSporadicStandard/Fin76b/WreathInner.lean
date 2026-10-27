module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.A6Normalizer
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.A6Dihedral
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Basic

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

variable {Γ : Type*} [Group Γ] {N₁ N₂ : Subgroup Γ} {σ : Γ}

theorem wreath_uniq (hdisj : Disjoint N₁ N₂) {a a' b b' : Γ} (ha : a ∈ N₁) (ha' : a' ∈ N₁)
    (hb : b ∈ N₂) (hb' : b' ∈ N₂) (h : a * b = a' * b') : a = a' ∧ b = b' := by
  have h1 : a'⁻¹ * a = b' * b⁻¹ := by
    calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
      _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [h]
      _ = b' * b⁻¹ := by group
  have h2 : a'⁻¹ * a ∈ N₁ ⊓ N₂ :=
    ⟨N₁.mul_mem (N₁.inv_mem ha') ha, h1 ▸ N₂.mul_mem hb' (N₂.inv_mem hb)⟩
  rw [hdisj.eq_bot, mem_bot] at h2
  have ha_eq : a = a' := by
    calc a = a' * (a'⁻¹ * a) := by group
      _ = a' := by rw [h2, mul_one]
  refine ⟨ha_eq, ?_⟩
  rw [ha_eq] at h
  exact mul_left_cancel h

structure WreathData (N₁ N₂ : Subgroup Γ) (σ : Γ) : Prop where
  comm : ∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a
  disj : Disjoint N₁ N₂
  sq : σ * σ = 1
  swap₁ : ∀ a ∈ N₁, σ * a * σ⁻¹ ∈ N₂
  swap₂ : ∀ b ∈ N₂, σ * b * σ⁻¹ ∈ N₁

namespace WreathData

variable (h : WreathData N₁ N₂ σ)
include h

theorem dec {v : Γ} (hv : v ∈ N₁ ⊔ N₂) : ∃ a ∈ N₁, ∃ b ∈ N₂, v = a * b :=
  exists_mul_of_mem_sup_of_le_centralizer
    (fun b hb => mem_centralizer_iff.2 fun a ha => h.comm a ha b hb) hv

theorem inv_eq : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right h.sq

omit h in
@[expose] def diag (h : WreathData N₁ N₂ σ) : ↥N₁ →* Γ where
  toFun a := (a : Γ) * (σ * (a : Γ) * σ⁻¹)
  map_one' := by simp
  map_mul' a b := by
    have hc := h.comm (b : Γ) b.2 (σ * (a : Γ) * σ⁻¹) (h.swap₁ a a.2)
    simp only [Subgroup.coe_mul]
    calc (a : Γ) * b * (σ * (a * b) * σ⁻¹)
        = a * (b * (σ * a * σ⁻¹)) * (σ * b * σ⁻¹) := by group
      _ = a * ((σ * a * σ⁻¹) * b) * (σ * b * σ⁻¹) := by rw [hc]
      _ = (a * (σ * a * σ⁻¹)) * (b * (σ * b * σ⁻¹)) := by group

theorem diag_apply (a : ↥N₁) : h.diag a = (a : Γ) * (σ * (a : Γ) * σ⁻¹) := rfl

theorem diag_injective : Function.Injective h.diag := by
  rw [injective_iff_map_eq_one]
  intro a ha
  rw [diag_apply] at ha
  have h1 : (a : Γ) ∈ N₂ := by
    have : (a : Γ) = (σ * (a : Γ) * σ⁻¹)⁻¹ := eq_inv_of_mul_eq_one_left ha
    rw [this]
    exact N₂.inv_mem (h.swap₁ a a.2)
  have h2 : (a : Γ) ∈ N₁ ⊓ N₂ := ⟨a.2, h1⟩
  rw [h.disj.eq_bot, mem_bot] at h2
  exact Subtype.ext h2

theorem mem_diag_of_comm {x : Γ} (hx : x ∈ N₁ ⊔ N₂) (hσx : σ * x * σ⁻¹ = x) :
    ∃ a : ↥N₁, h.diag a = x := by
  obtain ⟨a, ha, b, hb, rfl⟩ := h.dec hx
  have h1 : σ * (a * b) * σ⁻¹ = (σ * a * σ⁻¹) * (σ * b * σ⁻¹) := by group
  have h2 : (σ * b * σ⁻¹) * (σ * a * σ⁻¹) = a * b := by
    rw [h.comm _ (h.swap₂ b hb) _ (h.swap₁ a ha), ← h1]
    exact hσx
  obtain ⟨-, h4⟩ := wreath_uniq h.disj (h.swap₂ b hb) ha (h.swap₁ a ha) hb h2
  exact ⟨⟨a, ha⟩, by rw [diag_apply]; simp only; rw [h4]⟩

theorem conj_prod {m₁ a m₂ b : Γ} (hm₁ : m₁ ∈ N₁) (ha : a ∈ N₁) (hm₂ : m₂ ∈ N₂) (hb : b ∈ N₂) :
    (m₁ * m₂) * (a * b) * (m₁ * m₂)⁻¹ = (m₁ * a * m₁⁻¹) * (m₂ * b * m₂⁻¹) := by
  have c1 : m₂ * a = a * m₂ := (h.comm a ha m₂ hm₂).symm
  have c2 : (m₂ * b * m₂⁻¹) * m₁⁻¹ = m₁⁻¹ * (m₂ * b * m₂⁻¹) :=
    (h.comm m₁⁻¹ (N₁.inv_mem hm₁) _ (N₂.mul_mem (N₂.mul_mem hm₂ hb) (N₂.inv_mem hm₂))).symm
  calc (m₁ * m₂) * (a * b) * (m₁ * m₂)⁻¹ = m₁ * (m₂ * a) * b * m₂⁻¹ * m₁⁻¹ := by group
    _ = m₁ * (a * m₂) * b * m₂⁻¹ * m₁⁻¹ := by rw [c1]
    _ = m₁ * a * ((m₂ * b * m₂⁻¹) * m₁⁻¹) := by group
    _ = m₁ * a * (m₁⁻¹ * (m₂ * b * m₂⁻¹)) := by rw [c2]
    _ = (m₁ * a * m₁⁻¹) * (m₂ * b * m₂⁻¹) := by group

theorem normalizing_component {P : Subgroup Γ} (hPN : P ≤ N₁ ⊔ N₂)
    (hPσ : ∀ x ∈ P, σ * x * σ⁻¹ = x) {g m₁ m₂ : Γ} (hm₁ : m₁ ∈ N₁) (hm₂ : m₂ ∈ N₂)
    (hg : g = m₁ * m₂) (hgP : ∀ x ∈ P, g * x * g⁻¹ ∈ P) {a : ↥N₁} (ha : h.diag a ∈ P) :
    h.diag ⟨m₁ * a * m₁⁻¹, N₁.mul_mem (N₁.mul_mem hm₁ a.2) (N₁.inv_mem hm₁)⟩ ∈ P := by
  have hgx := hgP _ ha
  obtain ⟨a', ha'⟩ := h.mem_diag_of_comm (hPN hgx) (hPσ _ hgx)
  have hconj := h.conj_prod hm₁ a.2 hm₂ (h.swap₁ a a.2)
  rw [diag_apply, diag_apply, hg] at ha'
  have ha'' : (a' : Γ) * (σ * (a' : Γ) * σ⁻¹) =
      (m₁ * (a : Γ) * m₁⁻¹) * (m₂ * (σ * (a : Γ) * σ⁻¹) * m₂⁻¹) := by
    rw [ha', ← hconj]
  obtain ⟨h1, -⟩ := wreath_uniq h.disj a'.2 (N₁.mul_mem (N₁.mul_mem hm₁ a.2) (N₁.inv_mem hm₁))
    (h.swap₁ a' a'.2) (N₂.mul_mem (N₂.mul_mem hm₂ (h.swap₁ a a.2)) (N₂.inv_mem hm₂)) ha''
  have : (⟨m₁ * a * m₁⁻¹, N₁.mul_mem (N₁.mul_mem hm₁ a.2) (N₁.inv_mem hm₁)⟩ : ↥N₁) = a' :=
    Subtype.ext h1.symm
  rw [this]
  have := hgx
  rw [← (show h.diag a' = g * h.diag a * g⁻¹ by rw [diag_apply, diag_apply, hg]; exact ha')] at this
  exact this

end WreathData

theorem wreath_inner_on_diag (h : WreathData N₁ N₂ σ) (e₁ : ↥N₁ ≃* alternatingGroup (Fin 6))
    {P : Subgroup Γ} (hP8 : Nat.card P = 8)
    (hPN : P ≤ N₁ ⊔ N₂) (hPσ : ∀ x ∈ P, σ * x * σ⁻¹ = x)
    {t : Γ} (htP : t ∈ P) (htc : ∀ x ∈ P, t * x = x * t)
    {y : Γ} (hyN : y ∈ N₁ ⊔ N₂) (hyP : ∀ x ∈ P, y * x * y⁻¹ ∈ P)
    (hyP' : ∀ x ∈ P, y⁻¹ * x * y ∈ P) (hyσ : y * σ * y⁻¹ = σ * t) :
    ∃ d ∈ P, ∀ x ∈ P, y * x * y⁻¹ = d * x * d⁻¹ := by
  classical
  let P₁ : Subgroup ↥N₁ := P.comap h.diag
  have hmap : P₁.map h.diag = P := by
    apply Subgroup.map_comap_eq_self
    intro x hx
    obtain ⟨a, ha⟩ := h.mem_diag_of_comm (hPN hx) (hPσ x hx)
    exact ⟨a, ha⟩
  have hcard : Nat.card P₁ = 8 := by
    calc Nat.card P₁ = Nat.card (P₁.map h.diag) :=
          (Subgroup.card_map_of_injective h.diag_injective).symm
      _ = 8 := by rw [hmap]; exact hP8
  have hAut₁ : IsPGroup 2 (MulAut ↥P₁) := isPGroup_mulAut_of_card_eight e₁ hcard
  have hnorm := normalizer_le_of_a6 e₁ hcard hAut₁
  obtain ⟨n₁, hn₁, n₂, hn₂, rfl⟩ := h.dec hyN
  have hyinv : (n₁ * n₂)⁻¹ = n₁⁻¹ * n₂⁻¹ := by
    rw [mul_inv_rev, ← h.comm n₁⁻¹ (N₁.inv_mem hn₁) n₂⁻¹ (N₂.inv_mem hn₂)]
  have hn₁N : (⟨n₁, hn₁⟩ : ↥N₁) ∈ normalizer (P₁ : Set ↥N₁) := by
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      exact h.normalizing_component hPN hPσ hn₁ hn₂ rfl hyP ha
    · intro ha
      have := h.normalizing_component hPN hPσ (N₁.inv_mem hn₁) (N₂.inv_mem hn₂) hyinv
        (fun x hx => by simpa using hyP' x hx) ha
      have heq : (⟨n₁⁻¹ * ((⟨n₁, hn₁⟩ * a * ⟨n₁, hn₁⟩⁻¹ : ↥N₁) : Γ) * n₁⁻¹⁻¹, N₁.mul_mem
          (N₁.mul_mem (N₁.inv_mem hn₁) (N₁.mul_mem (N₁.mul_mem hn₁ a.2) (N₁.inv_mem hn₁)))
          (N₁.inv_mem (N₁.inv_mem hn₁))⟩ : ↥N₁) = a := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
        group
      rw [heq] at this
      exact this
  have hn₁P : (⟨n₁, hn₁⟩ : ↥N₁) ∈ P₁ := hnorm hn₁N
  refine ⟨h.diag ⟨n₁, hn₁⟩, hn₁P, ?_⟩
  obtain ⟨t₁, ht₁⟩ := h.mem_diag_of_comm (hPN htP) (hPσ t htP)
  have ht₁' : (t : Γ) = (t₁ : Γ) * (σ * (t₁ : Γ) * σ⁻¹) := by rw [← ht₁, h.diag_apply]
  have hcomm_t : ∀ c : ↥N₁, h.diag c ∈ P → (t₁ : Γ) * c = c * t₁ := by
    intro c hc
    have h1 := htc _ hc
    rw [← ht₁, ← map_mul, ← map_mul] at h1
    exact congrArg Subtype.val (h.diag_injective h1)
  have halg : n₁ * n₂ * σ * (n₁ * n₂)⁻¹ * σ⁻¹ =
      (n₁ * (σ * n₂⁻¹ * σ⁻¹)) * (n₂ * (σ * n₁⁻¹ * σ⁻¹)) := by
    have hc := h.comm (σ * n₂⁻¹ * σ⁻¹) (h.swap₂ _ (N₂.inv_mem hn₂)) n₂ hn₂
    calc n₁ * n₂ * σ * (n₁ * n₂)⁻¹ * σ⁻¹
        = n₁ * (n₂ * (σ * n₂⁻¹ * σ⁻¹)) * (σ * n₁⁻¹ * σ⁻¹) := by group
      _ = n₁ * ((σ * n₂⁻¹ * σ⁻¹) * n₂) * (σ * n₁⁻¹ * σ⁻¹) := by rw [← hc]
      _ = (n₁ * (σ * n₂⁻¹ * σ⁻¹)) * (n₂ * (σ * n₁⁻¹ * σ⁻¹)) := by group
  have hyσ' : n₁ * n₂ * σ * (n₁ * n₂)⁻¹ * σ⁻¹ = t := by
    rw [hyσ]
    exact hPσ t htP
  rw [halg, ht₁'] at hyσ'
  obtain ⟨-, hu₂⟩ := wreath_uniq h.disj
    (N₁.mul_mem hn₁ (h.swap₂ _ (N₂.inv_mem hn₂))) t₁.2
    (N₂.mul_mem hn₂ (h.swap₁ _ (N₁.inv_mem hn₁))) (h.swap₁ _ t₁.2) hyσ'
  have hn₂eq : n₂ = (σ * t₁ * σ⁻¹) * (σ * n₁ * σ⁻¹) := by
    calc n₂ = (n₂ * (σ * n₁⁻¹ * σ⁻¹)) * (σ * n₁ * σ⁻¹) := by group
      _ = (σ * t₁ * σ⁻¹) * (σ * n₁ * σ⁻¹) := by rw [hu₂]
  intro x hx
  obtain ⟨a, rfl⟩ := h.mem_diag_of_comm (hPN hx) (hPσ x hx)
  have haP : a ∈ P₁ := hx
  have hcP : h.diag ⟨n₁ * a * n₁⁻¹, N₁.mul_mem (N₁.mul_mem hn₁ a.2) (N₁.inv_mem hn₁)⟩ ∈ P :=
    h.normalizing_component hPN hPσ hn₁ hn₂ rfl hyP haP
  have hct := hcomm_t _ hcP
  have hconj := h.conj_prod hn₁ a.2 hn₂ (h.swap₁ a a.2)
  have hrhs : h.diag ⟨n₁, hn₁⟩ * h.diag a * (h.diag ⟨n₁, hn₁⟩)⁻¹ =
      (n₁ * (a : Γ) * n₁⁻¹) * (σ * (n₁ * (a : Γ) * n₁⁻¹) * σ⁻¹) := by
    rw [← map_inv, ← map_mul, ← map_mul, h.diag_apply]
    rfl
  show (n₁ * n₂) * h.diag a * (n₁ * n₂)⁻¹ =
    h.diag ⟨n₁, hn₁⟩ * h.diag a * (h.diag ⟨n₁, hn₁⟩)⁻¹
  rw [hrhs, h.diag_apply a, hconj]
  congr 1
  rw [hn₂eq]
  calc σ * t₁ * σ⁻¹ * (σ * n₁ * σ⁻¹) * (σ * a * σ⁻¹) * (σ * t₁ * σ⁻¹ * (σ * n₁ * σ⁻¹))⁻¹
      = σ * ((t₁ : Γ) * (n₁ * a * n₁⁻¹) * (t₁ : Γ)⁻¹) * σ⁻¹ := by group
    _ = σ * (n₁ * a * n₁⁻¹) * σ⁻¹ := by
      rw [hct]
      group

end CFSG.EvenSporadicStandard.Fin76b
