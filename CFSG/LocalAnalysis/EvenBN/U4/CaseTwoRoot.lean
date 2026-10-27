module

public import CFSG.LocalAnalysis.EvenBN.U4.CaseTwoSeven
public import CFSG.LocalAnalysis.EvenBN.Common.Diagonal

public section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Subgroup CFSG.Open CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.EvenBN.Common (prodFactorOne prodFactorTwo mem_normalizer_sup)
open scoped MatrixGroups

section Generic

variable {G : Type*} [Group G]

theorem conj_diagonal_eq {g a t : G} (hgt : g * t = t * g) :
    g⁻¹ * (a * (t⁻¹ * a * t)) * g = g⁻¹ * a * g * (t⁻¹ * (g⁻¹ * a * g) * t) := by
  have h : g⁻¹ * t⁻¹ = t⁻¹ * g⁻¹ := by rw [← mul_inv_rev, ← mul_inv_rev, hgt]
  calc g⁻¹ * (a * (t⁻¹ * a * t)) * g = g⁻¹ * a * g * ((g⁻¹ * t⁻¹) * a * (t * g)) := by group
    _ = g⁻¹ * a * g * ((t⁻¹ * g⁻¹) * a * (g * t)) := by rw [h, ← hgt]
    _ = g⁻¹ * a * g * (t⁻¹ * (g⁻¹ * a * g) * t) := by group

theorem conj_conj_inv_t_eq {c t : G} (hct : c * t = t * c) (v : G) :
    c * (t⁻¹ * v * t) * c⁻¹ = t⁻¹ * (c * v * c⁻¹) * t := by
  have e : t⁻¹ * c = c * t⁻¹ := by
    calc t⁻¹ * c = t⁻¹ * (c * t) * t⁻¹ := by group
      _ = t⁻¹ * (t * c) * t⁻¹ := by rw [hct]
      _ = c * t⁻¹ := by group
  calc c * (t⁻¹ * v * t) * c⁻¹ = (c * t⁻¹) * v * (c * t⁻¹)⁻¹ := by group
    _ = (t⁻¹ * c) * v * (t⁻¹ * c)⁻¹ := by rw [e]
    _ = t⁻¹ * (c * v * c⁻¹) * t := by group

theorem map_conj_inv_le_of_mem_normalizer {A X : Subgroup G} {g : G}
    (hg : g ∈ normalizer (A : Set G)) (hX : X ≤ A) : X.map (MulAut.conj g⁻¹).toMonoidHom ≤ A := by
  rintro _ ⟨x, hx, rfl⟩
  exact (mem_normalizer_iff.1 (inv_mem hg) x).1 (hX hx)

variable {A : Subgroup G} {t : G} (hcomm : ⁅A, A.map (MulAut.conj t⁻¹).toMonoidHom⁆ = ⊥)

theorem mem_map_diagonalHom_iff {X : Subgroup G} {y : G} :
    y ∈ (X.subgroupOf A).map (Common.diagonalHom A t hcomm) ↔
      ∃ a ∈ A, a ∈ X ∧ a * (t⁻¹ * a * t) = y := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, a.2, ha, rfl⟩
  · rintro ⟨a, haA, haX, rfl⟩
    exact ⟨⟨a, haA⟩, haX, rfl⟩

theorem injective_diagonalHom_of_inf_eq_bot
    (hinf : A ⊓ A.map (MulAut.conj t⁻¹).toMonoidHom = ⊥) :
    Function.Injective (Common.diagonalHom A t hcomm) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro a ha
  have := Common.map_ker_diagonalHom_le hcomm ⟨a, ha, rfl⟩
  rw [hinf, mem_bot] at this
  exact mem_bot.2 (Subtype.ext this)

theorem le_of_range_diagonalHom_le (hinf : A ⊓ A.map (MulAut.conj t⁻¹).toMonoidHom = ⊥)
    {X : Subgroup G}
    (hX : (Common.diagonalHom A t hcomm).range ≤
      (X.subgroupOf A).map (Common.diagonalHom A t hcomm)) : A ≤ X := by
  intro a ha
  obtain ⟨b, hb, hba⟩ := hX ⟨⟨a, ha⟩, rfl⟩
  rw [injective_diagonalHom_of_inf_eq_bot hcomm hinf hba] at hb
  exact hb

theorem sup_inf_centralizer_le_map_diagonalHom (ht : t * t = 1)
    (hinf : A ⊓ A.map (MulAut.conj t⁻¹).toMonoidHom = ⊥) {X : Subgroup G} (hXA : X ≤ A) :
    (X ⊔ X.map (MulAut.conj t⁻¹).toMonoidHom) ⊓ centralizer ({t} : Set G) ≤
      (X.subgroupOf A).map (Common.diagonalHom A t hcomm) := by
  intro x hx
  obtain ⟨hxX, hxC⟩ := mem_inf.1 hx
  have hxt : x * t = t * x := mem_centralizer_singleton_iff.1 hxC
  have hc : ∀ a ∈ X, ∀ b ∈ X.map (MulAut.conj t⁻¹).toMonoidHom, a * b = b * a := by
    intro a ha b hb
    exact (mem_centralizer_iff.1 (commutator_eq_bot_iff_le_centralizer.1 hcomm (hXA ha)) b
      (map_mono hXA hb)).symm
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_commute hc hxX
  obtain ⟨c, hcX, rfl⟩ := hb
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hxt ⊢
  have h1 : t⁻¹ * (a * (t⁻¹ * c * t)) * t = a * (t⁻¹ * c * t) := by
    rw [mul_assoc, hxt, inv_mul_cancel_left]
  have htt : t⁻¹ * t⁻¹ = 1 := by rw [← mul_inv_rev, ht, inv_one]
  have h2 : t⁻¹ * (a * (t⁻¹ * c * t)) * t = (t⁻¹ * a * t) * c := by
    calc t⁻¹ * (a * (t⁻¹ * c * t)) * t = (t⁻¹ * a * t) * ((t⁻¹ * t⁻¹) * c * (t * t)) := by
          group
      _ = (t⁻¹ * a * t) * c := by rw [htt, ht, one_mul, mul_one]
  have h3 : c * (t⁻¹ * a * t) = a * (t⁻¹ * c * t) := by
    rw [Common.commute_conj_of_commutator_eq_bot hcomm (hXA ha) (hXA hcX), ← h2, h1]
  have key : c⁻¹ * a = t⁻¹ * (a * c⁻¹) * t := by
    calc c⁻¹ * a = c⁻¹ * (a * (t⁻¹ * c * t)) * (t⁻¹ * c * t)⁻¹ := by group
      _ = c⁻¹ * (c * (t⁻¹ * a * t)) * (t⁻¹ * c * t)⁻¹ := by rw [h3]
      _ = t⁻¹ * (a * c⁻¹) * t := by group
  have hmem : c⁻¹ * a ∈ A ⊓ A.map (MulAut.conj t⁻¹).toMonoidHom :=
    mem_inf.2 ⟨mul_mem (inv_mem (hXA hcX)) (hXA ha),
      key ▸ Common.conj_mem_map_conj_inv t (mul_mem (hXA ha) (inv_mem (hXA hcX)))⟩
  rw [hinf, mem_bot, inv_mul_eq_one] at hmem
  subst hmem
  exact ⟨⟨c, hXA hcX⟩, hcX, rfl⟩

end Generic

namespace Setting

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {L : Subgroup G} {η : L ≃* gramSU h (miyamotoJ4 K)} {t : G}
  {Q T : Subgroup G}

local notation "𝓻₁" => miyamotoR1G h L η

local notation "𝓻₂" => miyamotoR2G h L η

local notation "𝓦" => miyamotoRG h L η t Q ⊓ centralizer (miyamotoI1G h L η : Set G)

variable {k : Type} [Field k] {ψ : miyamotoM1G h L η t ≃* SL(2, k) × SL(2, k)}

local notation "𝓤" => miyamotoF1G h L η t ⊔ (𝓦 ⊓ prodFactorOne ψ)

local notation "𝓨" => CFSG.centerIn 𝓤 ⊓
  Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj (miyamotoR1G h L η))) (CFSG.centerIn 𝓤)

local notation "𝓨t" => Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj t)) 𝓨

local notation "𝓚" => 𝓨t ⊔ prodFactorOne ψ

local notation "𝓦'" => miyamotoRG h L η t Q ⊓ 𝓚

local notation "𝓦₂" => 𝓦' ⊓ miyamotoF2G h L η t Q

local notation "𝓥₂'" => Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj 𝓻₂⁻¹)) 𝓨t ⊓
  Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj (𝓻₂ * 𝓻₁ * 𝓻₂)⁻¹)) 𝓨t

local notation "𝓥₁'" => Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj (𝓻₂ * 𝓻₁)⁻¹)) 𝓨t ⊓
  Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj 𝓻₁⁻¹)) 𝓦₂

theorem R2G_mem_L (_hS : Setting h L η t Q T) : 𝓻₂ ∈ L :=
  (η.symm _).2

theorem R1G_mul_R2G_pow_four (_hS : Setting h L η t Q T) : (𝓻₁ * 𝓻₂) ^ 4 = 1 := by
  have : CharP K 2 := h.charP
  simp only [miyamotoR1G, miyamotoR2G]
  rw [← L.coe_mul, ← map_mul, ← SubgroupClass.coe_pow, ← map_pow]
  have e : ((⟨miyamotoR1 K, miyamotoR1_mem_gramSU h⟩ : gramSU h (miyamotoJ4 K)) *
      ⟨miyamotoR2 K, miyamotoR2_mem_gramSU h⟩) ^ 4 = 1 :=
    Subtype.ext (by simpa using miyamotoR1_mul_R2_pow_four (K := K))
  rw [e, map_one, OneMemClass.coe_one]

theorem R1G_R2G_R1G_eq (hS : Setting h L η t Q T) :
    𝓻₁ * 𝓻₂ * 𝓻₁ = 𝓻₂ * 𝓻₁ * (𝓻₂ * 𝓻₁ * 𝓻₂) := by
  have h1 : 𝓻₁⁻¹ = 𝓻₁ := hS.R1G_inv
  have h2 : 𝓻₂⁻¹ = 𝓻₂ := inv_eq_of_mul_eq_one_right hS.R2G_mul_self
  have h4 := hS.R1G_mul_R2G_pow_four
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq, sq] at h4
  have e : (𝓻₁ * 𝓻₂ * 𝓻₁ * 𝓻₂) * (𝓻₁ * 𝓻₂ * 𝓻₁ * 𝓻₂) = 1 := by
    rw [← h4]; group
  have e2 : 𝓻₁ * 𝓻₂ * 𝓻₁ * 𝓻₂ = 𝓻₂ * 𝓻₁ * 𝓻₂ * 𝓻₁ := by
    rw [eq_inv_of_mul_eq_one_left e]
    simp only [mul_inv_rev, h1, h2, mul_assoc]
  calc 𝓻₁ * 𝓻₂ * 𝓻₁ = 𝓻₁ * 𝓻₂ * 𝓻₁ * 𝓻₂ * 𝓻₂⁻¹ := by group
    _ = 𝓻₂ * 𝓻₁ * 𝓻₂ * 𝓻₁ * 𝓻₂⁻¹ := by rw [e2]
    _ = 𝓻₂ * 𝓻₁ * (𝓻₂ * 𝓻₁ * 𝓻₂) := by rw [h2]; group

theorem conj_R1G_mem_Yt (hS : Setting h L η t Q T) {y : G} (hy : y ∈ 𝓨t) :
    𝓻₁ * y * 𝓻₁⁻¹ ∈ 𝓨t := by
  obtain ⟨y₀, hy₀, rfl⟩ := hy
  have hrt : 𝓻₁ * t = t * 𝓻₁ := hS.comm_t_of_mem_L hS.R1G_mem_L
  refine ⟨𝓻₁ * y₀ * 𝓻₁⁻¹, hS.conj_R1G_mem_Y hy₀, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  calc t * (𝓻₁ * y₀ * 𝓻₁⁻¹) * t⁻¹ = (t * 𝓻₁) * y₀ * (t * 𝓻₁)⁻¹ := by group
    _ = (𝓻₁ * t) * y₀ * (𝓻₁ * t)⁻¹ := by rw [← hrt]
    _ = 𝓻₁ * (t * y₀ * t⁻¹) * 𝓻₁⁻¹ := by group

theorem inv_conj_R1G_mem_Yt (hS : Setting h L η t Q T) {y : G} (hy : y ∈ 𝓨t) :
    𝓻₁⁻¹ * y * 𝓻₁ ∈ 𝓨t := by
  have := hS.conj_R1G_mem_Yt hy
  rw [hS.R1G_inv] at this ⊢
  exact this

theorem Yt_le_W' (hS : Setting h L η t Q T) : 𝓨t ≤ 𝓦' :=
  le_inf (hS.Yt_le_F1.trans (le_sup_left.trans hS.P1_le_miyamotoRG)) le_sup_left

theorem V1'_le_centralizer_V2't (hS : Setting h L η t Q T) {D : Subgroup G} (hWD : 𝓦' ≤ D)
    (hr₂ : 𝓻₂ ∈ normalizer (D : Set G))
    (hcomm : ⁅D, D.map (MulAut.conj t⁻¹).toMonoidHom⁆ = ⊥) :
    𝓥₁' ≤ centralizer (((𝓥₂' : Subgroup G).map (MulAut.conj t⁻¹).toMonoidHom : Subgroup G) :
      Set G) := by
  have hYD : 𝓨t ≤ D := hS.Yt_le_W'.trans hWD
  have hcL : 𝓻₁ * 𝓻₂ * 𝓻₁ ∈ L := mul_mem (mul_mem hS.R1G_mem_L hS.R2G_mem_L) hS.R1G_mem_L
  have hct := hS.comm_t_of_mem_L hcL
  intro y hy
  rw [mem_centralizer_iff]
  rintro _ ⟨v, hv, rfl⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  have hw : 𝓻₂ * 𝓻₁ * 𝓻₂ * v * (𝓻₂ * 𝓻₁ * 𝓻₂)⁻¹ ∈ 𝓨t :=
    Common.mem_map_conj_inv_iff.1 (mem_inf.1 hv).2
  have hw' : 𝓻₂ * 𝓻₁ * y * (𝓻₂ * 𝓻₁)⁻¹ ∈ 𝓨t := Common.mem_map_conj_inv_iff.1 (mem_inf.1 hy).1
  have hcv : 𝓻₁ * 𝓻₂ * 𝓻₁ * v * (𝓻₁ * 𝓻₂ * 𝓻₁)⁻¹ ∈ D := by
    have e : 𝓻₁ * 𝓻₂ * 𝓻₁ * v * (𝓻₁ * 𝓻₂ * 𝓻₁)⁻¹ =
        𝓻₂ * (𝓻₁ * (𝓻₂ * 𝓻₁ * 𝓻₂ * v * (𝓻₂ * 𝓻₁ * 𝓻₂)⁻¹) * 𝓻₁⁻¹) * 𝓻₂⁻¹ := by
      rw [hS.R1G_R2G_R1G_eq]; group
    rw [e]
    exact (mem_normalizer_iff.1 hr₂ _).1 (hYD (hS.conj_R1G_mem_Yt hw))
  have hcy : 𝓻₁ * 𝓻₂ * 𝓻₁ * y * (𝓻₁ * 𝓻₂ * 𝓻₁)⁻¹ ∈ D := by
    have e : 𝓻₁ * 𝓻₂ * 𝓻₁ * y * (𝓻₁ * 𝓻₂ * 𝓻₁)⁻¹ =
        𝓻₁ * (𝓻₂ * 𝓻₁ * y * (𝓻₂ * 𝓻₁)⁻¹) * 𝓻₁⁻¹ := by group
    rw [e]
    exact hYD (hS.conj_R1G_mem_Yt hw')
  have hcx : 𝓻₁ * 𝓻₂ * 𝓻₁ * (t⁻¹ * v * t) * (𝓻₁ * 𝓻₂ * 𝓻₁)⁻¹ ∈
      D.map (MulAut.conj t⁻¹).toMonoidHom := by
    rw [conj_conj_inv_t_eq hct]
    exact Common.conj_mem_map_conj_inv t hcv
  have hc := mem_centralizer_iff.1 (commutator_eq_bot_iff_le_centralizer.1 hcomm hcy) _ hcx
  calc t⁻¹ * v * t * y = (𝓻₁ * 𝓻₂ * 𝓻₁)⁻¹ * ((𝓻₁ * 𝓻₂ * 𝓻₁ * (t⁻¹ * v * t) *
        (𝓻₁ * 𝓻₂ * 𝓻₁)⁻¹) * (𝓻₁ * 𝓻₂ * 𝓻₁ * y * (𝓻₁ * 𝓻₂ * 𝓻₁)⁻¹)) * (𝓻₁ * 𝓻₂ * 𝓻₁) := by
        group
    _ = (𝓻₁ * 𝓻₂ * 𝓻₁)⁻¹ * ((𝓻₁ * 𝓻₂ * 𝓻₁ * y * (𝓻₁ * 𝓻₂ * 𝓻₁)⁻¹) *
        (𝓻₁ * 𝓻₂ * 𝓻₁ * (t⁻¹ * v * t) * (𝓻₁ * 𝓻₂ * 𝓻₁)⁻¹)) * (𝓻₁ * 𝓻₂ * 𝓻₁) := by rw [hc]
    _ = y * (t⁻¹ * v * t) := by group


theorem R1G_mem_normalizer_K1' [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2) {α : miyamotoN1G h L η ≃* SL(2, k)}
    (hψA : ∀ (a : miyamotoN1G h L η) (x : miyamotoM1G h L η t), (x : G) = a →
      ψ x = (α a, α a))
    (hψt : ∀ (x y : miyamotoM1G h L η t) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
      ψ x = (y₁, y₂) → ψ y = (y₂, y₁))
    (hZ : (2 ^ f) ^ 4 < Nat.card (CFSG.centerIn 𝓤)) :
    𝓻₁ ∈ normalizer ((𝓚 : Subgroup G) : Set G) := by
  rw [← hS.commutator_K1 hk hψA hψt hZ]
  have hK := mem_normalizer_sup (hS.M1_le_normalizer_F1 hS.R1G_mem_M1)
    (Common.le_normalizer_prodFactorOne ψ hS.R1G_mem_M1)
  exact mem_normalizer_commutator hK hK

theorem commutator_K1'_map_conj_inv [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2) {α : miyamotoN1G h L η ≃* SL(2, k)}
    (hψA : ∀ (a : miyamotoN1G h L η) (x : miyamotoM1G h L η t), (x : G) = a →
      ψ x = (α a, α a))
    (hψt : ∀ (x y : miyamotoM1G h L η t) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
      ψ x = (y₁, y₂) → ψ y = (y₂, y₁)) :
    ⁅𝓚, (𝓚 : Subgroup G).map (MulAut.conj t⁻¹).toMonoidHom⁆ = ⊥ := by
  rw [hS.t_inv, hS.map_conj_t_K1' hψt]
  exact commutator_eq_bot_iff_le_centralizer.2
    (le_centralizer_iff.1 (hS.K1't_le_centralizer hk hψA hψt))

theorem K1'_inf_map_conj_inv [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2)
    (hψt : ∀ (x y : miyamotoM1G h L η t) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
      ψ x = (y₁, y₂) → ψ y = (y₂, y₁)) :
    𝓚 ⊓ (𝓚 : Subgroup G).map (MulAut.conj t⁻¹).toMonoidHom = ⊥ := by
  rw [hS.t_inv, hS.map_conj_t_K1' hψt]
  exact hS.K1'_inf hk hψt

theorem range_diagonalHom_K1' [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2) {α : miyamotoN1G h L η ≃* SL(2, k)}
    (hψA : ∀ (a : miyamotoN1G h L η) (x : miyamotoM1G h L η t), (x : G) = a →
      ψ x = (α a, α a))
    (hψt : ∀ (x y : miyamotoM1G h L η t) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
      ψ x = (y₁, y₂) → ψ y = (y₂, y₁))
    (hZ : (2 ^ f) ^ 4 < Nat.card (CFSG.centerIn 𝓤))
    (hc : ⁅𝓚, (𝓚 : Subgroup G).map (MulAut.conj t⁻¹).toMonoidHom⁆ = ⊥) :
    (Common.diagonalHom 𝓚 t hc).range = miyamotoA1G h L η ⊔ miyamotoN1G h L η := by
  have hN1M : miyamotoN1G h L η ≤ miyamotoM1G h L η t := hS.sec3_12_one.2.2.1
  refine le_antisymm ?_ ?_
  · have hle : 𝓚 ≤ ((miyamotoA1G h L η ⊔ miyamotoN1G h L η).comap
        (Common.diagonalHom 𝓚 t hc)).map (𝓚 : Subgroup G).subtype := by
      refine sup_le (fun y hy => ⟨⟨y, mem_sup_left hy⟩, mem_sup_left ?_, rfl⟩)
        (fun x hx => ⟨⟨x, mem_sup_right hx⟩, mem_sup_right ?_, rfl⟩)
      · rw [← hS.F1_inf_C]
        refine mem_inf.2 ⟨?_, Common.range_diagonalHom_le hc hS.t_mul_t ⟨_, rfl⟩⟩
        rw [Common.diagonalHom_apply]
        have hyF := hS.Yt_le_F1 hy
        have := (mem_normalizer_iff.1 (inv_mem hS.t_mem_normalizer_F1) y).1 hyF
        rw [inv_inv] at this
        exact mul_mem hyF this
      · rw [Common.diagonalHom_apply]
        have hxM : x ∈ miyamotoM1G h L η t := Common.prodFactorOne_le ψ hx
        have hx'M : t⁻¹ * x * t ∈ miyamotoM1G h L η t :=
          Common.prodFactorTwo_le ψ (hS.t_conj_mem_X2 hψt hx)
        obtain ⟨hxM', hx2⟩ := (Common.mem_prodFactorOne_iff ψ).1 hx
        have hψx : ψ ⟨x, hxM⟩ = ((ψ ⟨x, hxM⟩).1, 1) := Prod.ext rfl hx2
        have hψx' := hψt ⟨x, hxM⟩ ⟨t⁻¹ * x * t, hx'M⟩ _ _ rfl hψx
        have hnM : ((α.symm (ψ ⟨x, hxM⟩).1 : miyamotoN1G h L η) : G) ∈ miyamotoM1G h L η t :=
          hN1M (α.symm (ψ ⟨x, hxM⟩).1).2
        have e : (⟨x * (t⁻¹ * x * t), mul_mem hxM hx'M⟩ : miyamotoM1G h L η t) =
            ⟨_, hnM⟩ := by
          apply ψ.injective
          rw [hψA _ ⟨_, hnM⟩ rfl, MulEquiv.apply_symm_apply]
          change ψ (⟨x, hxM⟩ * ⟨t⁻¹ * x * t, hx'M⟩) = _
          rw [map_mul, hψx, hψx', Prod.mk_mul_mk, mul_one, one_mul]
        rw [show x * (t⁻¹ * x * t) = _ from congrArg Subtype.val e]
        exact (α.symm (ψ ⟨x, hxM⟩).1).2
    rintro _ ⟨a, rfl⟩
    obtain ⟨b, hb, hba⟩ := hle a.2
    rw [show b = a from Subtype.ext hba] at hb
    exact hb
  · have h1 : miyamotoA1G h L η ⊔ miyamotoN1G h L η ≤
        (𝓚 ⊔ (𝓚 : Subgroup G).map (MulAut.conj t⁻¹).toMonoidHom) ⊓
          centralizer ({t} : Set G) := by
      obtain ⟨-, -, hKt, hL1, -, -⟩ := hS.sec5_1_three hk hψA hψt hZ
      rw [hS.t_inv, hKt, hL1]
      exact le_inf (sup_le_sup hS.A1_le_F1 hN1M) (sup_le (hS.A1G_le_PG.trans hS.PG_le_C)
        hS.N1G_le_C)
    refine h1.trans ((sup_inf_centralizer_le_map_diagonalHom hc hS.t_mul_t
      (hS.K1'_inf_map_conj_inv hk hψt) le_rfl).trans ?_)
    rw [subgroupOf_self, ← MonoidHom.range_eq_map]

theorem PG_le_map_diagonalHom [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2) {α : miyamotoN1G h L η ≃* SL(2, k)}
    (hψA : ∀ (a : miyamotoN1G h L η) (x : miyamotoM1G h L η t), (x : G) = a →
      ψ x = (α a, α a))
    (hψt : ∀ (x y : miyamotoM1G h L η t) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
      ψ x = (y₁, y₂) → ψ y = (y₂, y₁))
    (hZ : (2 ^ f) ^ 4 < Nat.card (CFSG.centerIn 𝓤)) {A : Subgroup G} (hWA : 𝓦' ≤ A)
    (hcomm : ⁅A, A.map (MulAut.conj t⁻¹).toMonoidHom⁆ = ⊥)
    (hinf : A ⊓ A.map (MulAut.conj t⁻¹).toMonoidHom = ⊥) :
    miyamotoPG h L η ≤ ((𝓦' : Subgroup G).subgroupOf A).map (Common.diagonalHom A t hcomm) := by
  obtain ⟨-, -, -, hReq, -⟩ := hS.sec5_2_one hk hψA hψt hZ
  have hR : miyamotoRG h L η t Q ≤ 𝓦' ⊔ (𝓦' : Subgroup G).map (MulAut.conj t⁻¹).toMonoidHom := by
    rw [hS.t_inv]
    exact hReq.le
  exact hS.RG_inf_C.symm.le.trans ((inf_le_inf_right _ hR).trans
    (sup_inf_centralizer_le_map_diagonalHom hcomm hS.t_mul_t hinf hWA))

theorem F1_inf_C_le_map_diagonalHom [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2)
    (hψt : ∀ (x y : miyamotoM1G h L η t) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
      ψ x = (y₁, y₂) → ψ y = (y₂, y₁))
    (hZ : (2 ^ f) ^ 4 < Nat.card (CFSG.centerIn 𝓤)) {D : Subgroup G} (hWD : 𝓦' ≤ D)
    (hcomm : ⁅D, D.map (MulAut.conj t⁻¹).toMonoidHom⁆ = ⊥)
    (hinf : D ⊓ D.map (MulAut.conj t⁻¹).toMonoidHom = ⊥) :
    miyamotoF1G h L η t ⊓ centralizer ({t} : Set G) ≤
      ((𝓨t : Subgroup G).subgroupOf D).map (Common.diagonalHom D t hcomm) := by
  have hF : miyamotoF1G h L η t ≤ 𝓨t ⊔ (𝓨t : Subgroup G).map (MulAut.conj t⁻¹).toMonoidHom := by
    rw [hS.t_inv, map_conj_map_conj_of_mul_self hS.t_mul_t]
    exact (hS.sec5_1_one hk hψt hZ).2.1.trans_le (sup_le le_sup_right le_sup_left)
  exact (inf_le_inf_right _ hF).trans
    (sup_inf_centralizer_le_map_diagonalHom hcomm hS.t_mul_t hinf (hS.Yt_le_W'.trans hWD))

theorem F2_inf_C_le_map_diagonalHom [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2) {α : miyamotoN1G h L η ≃* SL(2, k)}
    (hψA : ∀ (a : miyamotoN1G h L η) (x : miyamotoM1G h L η t), (x : G) = a →
      ψ x = (α a, α a))
    (hψt : ∀ (x y : miyamotoM1G h L η t) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
      ψ x = (y₁, y₂) → ψ y = (y₂, y₁))
    (hZ : (2 ^ f) ^ 4 < Nat.card (CFSG.centerIn 𝓤)) {D : Subgroup G} (hWD : 𝓦' ≤ D)
    (hcomm : ⁅D, D.map (MulAut.conj t⁻¹).toMonoidHom⁆ = ⊥)
    (hinf : D ⊓ D.map (MulAut.conj t⁻¹).toMonoidHom = ⊥) :
    miyamotoF2G h L η t Q ⊓ centralizer ({t} : Set G) ≤
      ((𝓦₂ : Subgroup G).subgroupOf D).map (Common.diagonalHom D t hcomm) := by
  obtain ⟨hW2t, hF2, -⟩ := hS.sec5_2_two hk hψA hψt hZ
  have hF : miyamotoF2G h L η t Q ≤ 𝓦₂ ⊔ (𝓦₂ : Subgroup G).map (MulAut.conj t⁻¹).toMonoidHom := by
    rw [hS.t_inv, hW2t]
    exact hF2.le
  exact (inf_le_inf_right _ hF).trans
    (sup_inf_centralizer_le_map_diagonalHom hcomm hS.t_mul_t hinf (inf_le_left.trans hWD))

theorem F1_r2_inf_C_le_map_diagonalHom [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2)
    (hψt : ∀ (x y : miyamotoM1G h L η t) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
      ψ x = (y₁, y₂) → ψ y = (y₂, y₁))
    (hZ : (2 ^ f) ^ 4 < Nat.card (CFSG.centerIn 𝓤)) {D : Subgroup G} (hWD : 𝓦' ≤ D)
    (hr₂ : 𝓻₂ ∈ normalizer (D : Set G))
    (hcomm : ⁅D, D.map (MulAut.conj t⁻¹).toMonoidHom⁆ = ⊥)
    (hinf : D ⊓ D.map (MulAut.conj t⁻¹).toMonoidHom = ⊥) :
    (miyamotoF1G h L η t).map (MulAut.conj 𝓻₂⁻¹).toMonoidHom ⊓ centralizer ({t} : Set G) ≤
      (((𝓨t : Subgroup G).map (MulAut.conj 𝓻₂⁻¹).toMonoidHom).subgroupOf D).map
        (Common.diagonalHom D t hcomm) := by
  intro b hb
  obtain ⟨hbF, hbC⟩ := mem_inf.1 hb
  have hrC : 𝓻₂ ∈ centralizer ({t} : Set G) := hS.L_le_centralizer hS.R2G_mem_L
  have hrt : 𝓻₂ * t = t * 𝓻₂ := mem_centralizer_singleton_iff.1 hrC
  have hb' : 𝓻₂ * b * 𝓻₂⁻¹ ∈ miyamotoF1G h L η t ⊓ centralizer ({t} : Set G) :=
    mem_inf.2 ⟨Common.mem_map_conj_inv_iff.1 hbF, mul_mem (mul_mem hrC hbC) (inv_mem hrC)⟩
  obtain ⟨w, hwD, hwY, hw⟩ := (mem_map_diagonalHom_iff hcomm).1
    (hS.F1_inf_C_le_map_diagonalHom hk hψt hZ hWD hcomm hinf hb')
  refine (mem_map_diagonalHom_iff hcomm).2 ⟨𝓻₂⁻¹ * w * 𝓻₂,
    map_conj_inv_le_of_mem_normalizer hr₂ le_rfl (Common.conj_mem_map_conj_inv 𝓻₂ hwD),
    Common.conj_mem_map_conj_inv _ hwY, ?_⟩
  rw [← conj_diagonal_eq hrt, hw]
  group

theorem inf_le_map_diagonalHom_V2' [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2)
    (hψt : ∀ (x y : miyamotoM1G h L η t) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
      ψ x = (y₁, y₂) → ψ y = (y₂, y₁))
    (hZ : (2 ^ f) ^ 4 < Nat.card (CFSG.centerIn 𝓤)) {D : Subgroup G} (hWD : 𝓦' ≤ D)
    (hr₂ : 𝓻₂ ∈ normalizer (D : Set G))
    (hcomm : ⁅D, D.map (MulAut.conj t⁻¹).toMonoidHom⁆ = ⊥)
    (hinf : D ⊓ D.map (MulAut.conj t⁻¹).toMonoidHom = ⊥) :
    (miyamotoA1G h L η).map (MulAut.conj 𝓻₂⁻¹).toMonoidHom ⊓
        (miyamotoA1G h L η).map (MulAut.conj (𝓻₂ * 𝓻₁ * 𝓻₂)⁻¹).toMonoidHom ≤
      ((𝓥₂' : Subgroup G).subgroupOf D).map (Common.diagonalHom D t hcomm) := by
  intro a ha
  obtain ⟨ha₁, ha₂⟩ := mem_inf.1 ha
  rw [Common.mem_map_conj_inv_iff] at ha₁ ha₂
  have hr₁C : 𝓻₁ ∈ centralizer ({t} : Set G) := hS.L_le_centralizer hS.R1G_mem_L
  have hA₁C : miyamotoA1G h L η ≤ centralizer ({t} : Set G) := hS.A1G_le_PG.trans hS.PG_le_C
  have hr₁F : 𝓻₁ ∈ normalizer (miyamotoF1G h L η t : Set G) :=
    hS.M1_le_normalizer_F1 hS.R1G_mem_M1
  have hbC : 𝓻₁ * (𝓻₂ * a * 𝓻₂⁻¹) * 𝓻₁⁻¹ ∈ centralizer ({t} : Set G) :=
    mul_mem (mul_mem hr₁C (hA₁C ha₁)) (inv_mem hr₁C)
  have hbF : 𝓻₁ * (𝓻₂ * a * 𝓻₂⁻¹) * 𝓻₁⁻¹ ∈ miyamotoF1G h L η t :=
    (mem_normalizer_iff.1 hr₁F _).1 (hS.A1_le_F1 ha₁)
  have hbF' : 𝓻₁ * (𝓻₂ * a * 𝓻₂⁻¹) * 𝓻₁⁻¹ ∈
      (miyamotoF1G h L η t).map (MulAut.conj 𝓻₂⁻¹).toMonoidHom := by
    rw [Common.mem_map_conj_inv_iff]
    have e : 𝓻₂ * (𝓻₁ * (𝓻₂ * a * 𝓻₂⁻¹) * 𝓻₁⁻¹) * 𝓻₂⁻¹ =
        𝓻₂ * 𝓻₁ * 𝓻₂ * a * (𝓻₂ * 𝓻₁ * 𝓻₂)⁻¹ := by group
    rw [e]
    exact hS.A1_le_F1 ha₂
  obtain ⟨w, hwD, hwY, hw⟩ := (mem_map_diagonalHom_iff hcomm).1
    (hS.F1_inf_C_le_map_diagonalHom hk hψt hZ hWD hcomm hinf (mem_inf.2 ⟨hbF, hbC⟩))
  obtain ⟨w', hw'D, hw'Y, hw'⟩ := (mem_map_diagonalHom_iff hcomm).1
    (hS.F1_r2_inf_C_le_map_diagonalHom hk hψt hZ hWD hr₂ hcomm hinf (mem_inf.2 ⟨hbF', hbC⟩))
  have hww : w' = w := congrArg Subtype.val (injective_diagonalHom_of_inf_eq_bot hcomm hinf
    (show Common.diagonalHom D t hcomm ⟨w', hw'D⟩ = Common.diagonalHom D t hcomm ⟨w, hwD⟩ from
      hw'.trans hw.symm))
  subst hww
  have hgt : 𝓻₁ * 𝓻₂ * t = t * (𝓻₁ * 𝓻₂) :=
    hS.comm_t_of_mem_L (mul_mem hS.R1G_mem_L hS.R2G_mem_L)
  have hv₁ : 𝓻₁⁻¹ * w' * 𝓻₁ ∈ 𝓨t := hS.inv_conj_R1G_mem_Yt hwY
  have hYD : 𝓨t ≤ D := hS.Yt_le_W'.trans hWD
  refine (mem_map_diagonalHom_iff hcomm).2 ⟨(𝓻₁ * 𝓻₂)⁻¹ * w' * (𝓻₁ * 𝓻₂), ?_, ?_, ?_⟩
  · have e : (𝓻₁ * 𝓻₂)⁻¹ * w' * (𝓻₁ * 𝓻₂) = 𝓻₂⁻¹ * (𝓻₁⁻¹ * w' * 𝓻₁) * 𝓻₂ := by group
    rw [e]
    exact map_conj_inv_le_of_mem_normalizer hr₂ hYD (Common.conj_mem_map_conj_inv 𝓻₂ hv₁)
  · refine mem_inf.2 ⟨Common.mem_map_conj_inv_iff.2 ?_, Common.mem_map_conj_inv_iff.2 ?_⟩
    · have e : 𝓻₂ * ((𝓻₁ * 𝓻₂)⁻¹ * w' * (𝓻₁ * 𝓻₂)) * 𝓻₂⁻¹ = 𝓻₁⁻¹ * w' * 𝓻₁ := by group
      rw [e]
      exact hv₁
    · have e : 𝓻₂ * 𝓻₁ * 𝓻₂ * ((𝓻₁ * 𝓻₂)⁻¹ * w' * (𝓻₁ * 𝓻₂)) * (𝓻₂ * 𝓻₁ * 𝓻₂)⁻¹ =
          𝓻₂ * w' * 𝓻₂⁻¹ := by group
      rw [e]
      exact Common.mem_map_conj_inv_iff.1 hw'Y
  · rw [← conj_diagonal_eq hgt, hw']
    group

theorem D_le_W'_sup_V2' [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2) {α : miyamotoN1G h L η ≃* SL(2, k)}
    (hψA : ∀ (a : miyamotoN1G h L η) (x : miyamotoM1G h L η t), (x : G) = a →
      ψ x = (α a, α a))
    (hψt : ∀ (x y : miyamotoM1G h L η t) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
      ψ x = (y₁, y₂) → ψ y = (y₂, y₁))
    (hZ : (2 ^ f) ^ 4 < Nat.card (CFSG.centerIn 𝓤)) {D : Subgroup G} (hWD : 𝓦' ≤ D)
    (hr₂ : 𝓻₂ ∈ normalizer (D : Set G))
    (hcomm : ⁅D, D.map (MulAut.conj t⁻¹).toMonoidHom⁆ = ⊥)
    (hinf : D ⊓ D.map (MulAut.conj t⁻¹).toMonoidHom = ⊥)
    (hδ : (Common.diagonalHom D t hcomm).range ≤ miyamotoA2G h L η ⊔ miyamotoN2G h L η) :
    D ≤ 𝓦' ⊔ 𝓥₂' := by
  have : CharP K 2 := h.charP
  refine le_of_range_diagonalHom_le hcomm hinf (hδ.trans ?_)
  rw [miyamotoA2G_sup_N2G_eq]
  refine sup_le ((hS.PG_le_map_diagonalHom hk hψA hψt hZ hWD hcomm hinf).trans ?_)
    ((hS.inf_le_map_diagonalHom_V2' hk hψt hZ hWD hr₂ hcomm hinf).trans ?_)
  · exact map_mono fun x hx => mem_subgroupOf.2 (mem_sup_left (mem_subgroupOf.1 hx))
  · exact map_mono fun x hx => mem_subgroupOf.2 (mem_sup_right (mem_subgroupOf.1 hx))

theorem inf_le_map_diagonalHom_V1' [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2) {α : miyamotoN1G h L η ≃* SL(2, k)}
    (hψA : ∀ (a : miyamotoN1G h L η) (x : miyamotoM1G h L η t), (x : G) = a →
      ψ x = (α a, α a))
    (hψt : ∀ (x y : miyamotoM1G h L η t) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
      ψ x = (y₁, y₂) → ψ y = (y₂, y₁))
    (hZ : (2 ^ f) ^ 4 < Nat.card (CFSG.centerIn 𝓤)) {D : Subgroup G} (hWD : 𝓦' ≤ D)
    (hr₂ : 𝓻₂ ∈ normalizer (D : Set G))
    (hcomm : ⁅D, D.map (MulAut.conj t⁻¹).toMonoidHom⁆ = ⊥)
    (hinf : D ⊓ D.map (MulAut.conj t⁻¹).toMonoidHom = ⊥)
    (hc : ⁅𝓚, (𝓚 : Subgroup G).map (MulAut.conj t⁻¹).toMonoidHom⁆ = ⊥) :
    (miyamotoA1G h L η).map (MulAut.conj (𝓻₂ * 𝓻₁)⁻¹).toMonoidHom ⊓
        (miyamotoA2G h L η).map (MulAut.conj 𝓻₁⁻¹).toMonoidHom ≤
      ((𝓥₁' : Subgroup G).subgroupOf 𝓚).map (Common.diagonalHom 𝓚 t hc) := by
  intro a ha
  obtain ⟨ha₁, ha₂⟩ := mem_inf.1 ha
  rw [Common.mem_map_conj_inv_iff] at ha₁ ha₂
  have hbC : 𝓻₁ * a * 𝓻₁⁻¹ ∈ centralizer ({t} : Set G) :=
    (hS.A2G_le_PG.trans hS.PG_le_C) ha₂
  have hbF2 : 𝓻₁ * a * 𝓻₁⁻¹ ∈ miyamotoF2G h L η t Q := (hS.F2_inf_C.ge.trans inf_le_left) ha₂
  have hbF1 : 𝓻₁ * a * 𝓻₁⁻¹ ∈ (miyamotoF1G h L η t).map (MulAut.conj 𝓻₂⁻¹).toMonoidHom := by
    rw [Common.mem_map_conj_inv_iff]
    have e : 𝓻₂ * (𝓻₁ * a * 𝓻₁⁻¹) * 𝓻₂⁻¹ = 𝓻₂ * 𝓻₁ * a * (𝓻₂ * 𝓻₁)⁻¹ := by group
    rw [e]
    exact hS.A1_le_F1 ha₁
  obtain ⟨w, hwD, hwW, hw⟩ := (mem_map_diagonalHom_iff hcomm).1
    (hS.F2_inf_C_le_map_diagonalHom hk hψA hψt hZ hWD hcomm hinf (mem_inf.2 ⟨hbF2, hbC⟩))
  obtain ⟨w', hw'D, hw'Y, hw'⟩ := (mem_map_diagonalHom_iff hcomm).1
    (hS.F1_r2_inf_C_le_map_diagonalHom hk hψt hZ hWD hr₂ hcomm hinf (mem_inf.2 ⟨hbF1, hbC⟩))
  have hww : w' = w := congrArg Subtype.val (injective_diagonalHom_of_inf_eq_bot hcomm hinf
    (show Common.diagonalHom D t hcomm ⟨w', hw'D⟩ = Common.diagonalHom D t hcomm ⟨w, hwD⟩ from
      hw'.trans hw.symm))
  subst hww
  have hr₁t : 𝓻₁ * t = t * 𝓻₁ := hS.comm_t_of_mem_L hS.R1G_mem_L
  refine (mem_map_diagonalHom_iff hc).2 ⟨𝓻₁⁻¹ * w' * 𝓻₁,
    map_conj_inv_le_of_mem_normalizer (hS.R1G_mem_normalizer_K1' hk hψA hψt hZ)
      (inf_le_left.trans inf_le_right) (Common.conj_mem_map_conj_inv 𝓻₁ hwW),
    mem_inf.2 ⟨Common.mem_map_conj_inv_iff.2 ?_, Common.conj_mem_map_conj_inv 𝓻₁ hwW⟩, ?_⟩
  · have e : 𝓻₂ * 𝓻₁ * (𝓻₁⁻¹ * w' * 𝓻₁) * (𝓻₂ * 𝓻₁)⁻¹ = 𝓻₂ * w' * 𝓻₂⁻¹ := by group
    rw [e]
    exact Common.mem_map_conj_inv_iff.1 hw'Y
  · rw [← conj_diagonal_eq hr₁t, hw']
    group

theorem K1'_le_W'_sup_V1' [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2) {α : miyamotoN1G h L η ≃* SL(2, k)}
    (hψA : ∀ (a : miyamotoN1G h L η) (x : miyamotoM1G h L η t), (x : G) = a →
      ψ x = (α a, α a))
    (hψt : ∀ (x y : miyamotoM1G h L η t) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
      ψ x = (y₁, y₂) → ψ y = (y₂, y₁))
    (hZ : (2 ^ f) ^ 4 < Nat.card (CFSG.centerIn 𝓤)) {D : Subgroup G} (hWD : 𝓦' ≤ D)
    (hr₂ : 𝓻₂ ∈ normalizer (D : Set G))
    (hcomm : ⁅D, D.map (MulAut.conj t⁻¹).toMonoidHom⁆ = ⊥)
    (hinf : D ⊓ D.map (MulAut.conj t⁻¹).toMonoidHom = ⊥) :
    𝓚 ≤ 𝓦' ⊔ 𝓥₁' := by
  have : CharP K 2 := h.charP
  have hc := hS.commutator_K1'_map_conj_inv hk hψA hψt
  have hinfK := hS.K1'_inf_map_conj_inv hk hψt
  refine le_of_range_diagonalHom_le hc hinfK ?_
  rw [hS.range_diagonalHom_K1' hk hψA hψt hZ hc, miyamotoA1G_sup_N1G_eq]
  refine sup_le ((hS.PG_le_map_diagonalHom hk hψA hψt hZ inf_le_right hc hinfK).trans ?_)
    ((hS.inf_le_map_diagonalHom_V1' hk hψA hψt hZ hWD hr₂ hcomm hinf hc).trans ?_)
  · exact map_mono fun x hx => mem_subgroupOf.2 (mem_sup_left (mem_subgroupOf.1 hx))
  · exact map_mono fun x hx => mem_subgroupOf.2 (mem_sup_right (mem_subgroupOf.1 hx))

theorem map_conj_D_le_centralizer_K1' [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2) {α : miyamotoN1G h L η ≃* SL(2, k)}
    (hψA : ∀ (a : miyamotoN1G h L η) (x : miyamotoM1G h L η t), (x : G) = a →
      ψ x = (α a, α a))
    (hψt : ∀ (x y : miyamotoM1G h L η t) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
      ψ x = (y₁, y₂) → ψ y = (y₂, y₁))
    (hZ : (2 ^ f) ^ 4 < Nat.card (CFSG.centerIn 𝓤))
    {D : Subgroup G} (hWD : 𝓦' ≤ D) (hr₂ : 𝓻₂ ∈ normalizer (D : Set G))
    (hcomm : ⁅D, D.map (MulAut.conj t⁻¹).toMonoidHom⁆ = ⊥)
    (hinf : D ⊓ D.map (MulAut.conj t⁻¹).toMonoidHom = ⊥)
    (hδ : (Common.diagonalHom D t hcomm).range ≤ miyamotoA2G h L η ⊔ miyamotoN2G h L η) :
    D.map (MulAut.conj t⁻¹).toMonoidHom ≤ centralizer ((𝓚 : Subgroup G) : Set G) := by
  obtain ⟨-, hC, -, -, -⟩ := hS.sec5_2_one hk hψA hψt hZ
  have hWt : (𝓦' : Subgroup G).map (MulAut.conj t⁻¹).toMonoidHom ≤
      centralizer ((𝓦' : Subgroup G) : Set G) := by
    rw [hS.t_inv]
    exact hC
  have hKt : 𝓚 ≤ centralizer (((𝓚 : Subgroup G).map (MulAut.conj t⁻¹).toMonoidHom :
      Subgroup G) : Set G) :=
    commutator_eq_bot_iff_le_centralizer.1 (hS.commutator_K1'_map_conj_inv hk hψA hψt)
  have hV1K : 𝓥₁' ≤ 𝓚 := inf_le_right.trans (map_conj_inv_le_of_mem_normalizer
    (hS.R1G_mem_normalizer_K1' hk hψA hψt hZ) (inf_le_left.trans inf_le_right))
  have hV2D : 𝓥₂' ≤ D :=
    inf_le_left.trans (map_conj_inv_le_of_mem_normalizer hr₂ (hS.Yt_le_W'.trans hWD))
  refine (map_mono (hS.D_le_W'_sup_V2' hk hψA hψt hZ hWD hr₂ hcomm hinf hδ)).trans ?_
  rw [Subgroup.map_sup]
  refine le_trans ?_ (centralizer_le (SetLike.coe_subset_coe.2
    (hS.K1'_le_W'_sup_V1' hk hψA hψt hZ hWD hr₂ hcomm hinf)))
  refine sup_le (le_centralizer_iff.2 (sup_le (le_centralizer_iff.1 hWt) ?_))
    (le_centralizer_iff.2 (sup_le ?_ (hS.V1'_le_centralizer_V2't hWD hr₂ hcomm)))
  · exact hV1K.trans (hKt.trans (centralizer_le (SetLike.coe_subset_coe.2
      (map_mono inf_le_right))))
  · exact hWD.trans ((commutator_eq_bot_iff_le_centralizer.1 hcomm).trans
      (centralizer_le (SetLike.coe_subset_coe.2 (map_mono hV2D))))

end Setting

end CFSG.LocalAnalysis.EvenBN.U4
