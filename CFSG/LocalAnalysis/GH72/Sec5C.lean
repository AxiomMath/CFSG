module

public import CFSG.LocalAnalysis.GH72.Sec5CTools
public import CFSG.LocalAnalysis.GH72.Sec5Config
public import CFSG.GroupTheory.CyclicSubgroup.NormalizerCommutator

public section

namespace CFSG.GH72

open Subgroup CFSG.ABGLocalTools

theorem normalizer_le_normalizer_centralizer {G : Type} [Group G] [Finite G] (H : Subgroup G) :
    normalizer (H : Set G) ≤ normalizer (centralizer (H : Set G) : Set G) := by
  intro g hg
  apply mem_normalizer_of_forall_conj_mem
  intro c hc
  rw [mem_centralizer_iff] at hc ⊢
  intro h hh
  have hh' : g⁻¹ * h * g ∈ H := by
    have := (mem_normalizer_iff.mp (inv_mem hg) h).mp hh
    simpa using this
  have e := hc _ hh'
  calc h * (g * c * g⁻¹) = g * ((g⁻¹ * h * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * h * g)) * g⁻¹ := by rw [e]
    _ = g * c * g⁻¹ * h := by group

namespace Sec5Roles

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} (ρ : Sec5Roles G A)

include ρ in
theorem mul_self_of_mem_A {a : G} (ha : a ∈ A) : a * a = 1 := by
  have := ρ.hA.1.2 a ha
  rwa [pow_two] at this

include ρ in
theorem A_le_centralizer_of_le {B : Subgroup G} (hB : B ≤ A) : A ≤ centralizer (B : Set G) :=
  fun _ ha => mem_centralizer_iff.mpr fun _ hb => ρ.comm (hB hb) ha

include ρ in
theorem A_le_normalizer_of_le {B : Subgroup G} (hB : B ≤ A) : A ≤ normalizer (B : Set G) :=
  fun a ha => mem_normalizer_of_forall_conj_mem fun b hb => by
    rw [← ρ.comm (hB hb) ha, mul_inv_cancel_right]
    exact hb

theorem isPGroup_two_X : IsPGroup 2 ρ.X := ρ.isPGroup_A.to_le ρ.X_le_A

end Sec5Roles

namespace Sec5KConfig

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {ρ : Sec5Roles G A} {p : ℕ}
  (𝔨 : Sec5KConfig ρ p)

theorem isPGroup_P : IsPGroup p 𝔨.P := 𝔨.hP.2.1

theorem lemma_5_11_of (Q : Subgroup G) (hQP : Q ≤ 𝔨.P) (hPQR : 𝔨.P = Q ⊔ 𝔨.R)
    (h58 : 𝔨.R = 𝔨.U) (W : Subgroup G)
    (hW : Q = (𝔨.R ⊓ Q) ⊔ W ∧ IsCyclic W ∧
      A ≤ normalizer (W : Set G) ∧ W ≤ 𝔨.K₁ ⊓ centralizer (𝔨.V : Set G) ∧ ⁅ρ.X, W⁆ = W) :
    𝔨.P = 𝔨.Pstar ∧ 𝔨.P = 𝔨.U ⊔ W := by
  have hUP : 𝔨.U ≤ 𝔨.Pstar := inf_le_inf_right _ inf_le_left
  have hWQ : W ≤ Q := le_sup_right.trans hW.1.ge
  have hWK : W ≤ 𝔨.K := hW.2.2.2.1.trans (inf_le_left.trans 𝔨.K₁_le_K)
  have hWP : W ≤ 𝔨.Pstar := le_inf (hWQ.trans hQP) hWK
  have hUW : 𝔨.U ⊔ W ≤ 𝔨.Pstar := sup_le hUP hWP
  have hQ : Q ≤ 𝔨.U ⊔ W := hW.1.le.trans (sup_le_sup_right (inf_le_left.trans h58.le) _)
  have hP : 𝔨.P ≤ 𝔨.U ⊔ W := hPQR.le.trans (sup_le hQ (h58.le.trans le_sup_left))
  have hPstar : 𝔨.Pstar ≤ 𝔨.P := inf_le_left
  exact ⟨le_antisymm (hP.trans hUW) hPstar, le_antisymm hP (hUW.trans hPstar)⟩

theorem covers_centralizer_V
    (h48i : QuotIs ρ.N₀ (O ρ.N) (fun L _ => IsL2OrA7 L 5 ∨ IsKleinFour L)) (hXN₀ : ρ.X ≤ ρ.N₀) :
    Covers (centralizer (𝔨.V : Set G)) ρ.N₀ (O ρ.N) := by
  obtain ⟨L, _, f, hf, hker, hL⟩ := h48i
  have hONn := ρ.N₀_le_normalizer_O_N
  have hXV := 𝔨.X_le_centralizer_V
  have hXO : ρ.X ⊓ O ρ.N = ⊥ := inf_eq_bot_of_isKleinFour ρ.isKleinFour_X (card_O_odd _)
  rcases hL with hL | hL
  · have := isSimpleGroup_of_isL2OrA7 le_rfl hL
    obtain ⟨x, hx, hx1⟩ := exists_ne_one_of_isKleinFour ρ.isKleinFour_X
    refine covers_of_isSimpleGroup f hf hker 𝔨.hK₁.2.2.1 hONn ?_
      ⟨⟨hXV hx, 𝔨.X_le_K₁ hx⟩, hXN₀ hx⟩ ?_
    · intro g hg
      have hgK : g ∈ normalizer (𝔨.V : Set G) := 𝔨.K_eq_normalizer_V ▸ 𝔨.K₁_le_K hg.1
      exact normalizer_le_normalizer_centralizer _ hgK
    · intro hxO
      have : x ∈ ρ.X ⊓ O ρ.N := ⟨hx, hxO⟩
      rw [hXO, mem_bot] at this
      exact hx1 this
  · have : Finite L := Finite.of_surjective f hf
    exact covers_of_card_eq f hker (le_inf hXV hXN₀) hXO
      (by rw [ρ.isKleinFour_X.card_four, hL.card_four])

end Sec5KConfig

namespace Sec5ConfigR

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {ρ : Sec5Roles G A} {p : ℕ}
  (𝔠 : Sec5ConfigR ρ p)

theorem Y_not_le_centralizer_Q : ¬ ρ.Y ≤ centralizer (𝔠.Q : Set G) := 𝔠.hH₁.1

theorem covers_H₁ : Covers (𝔠.H₀ ⊓ normalizer (𝔠.Q : Set G)) ρ.M₀ (O ρ.M) := 𝔠.hH₁.2.1

theorem commutator_H₁_X_le :
    ⁅𝔠.H₀ ⊓ normalizer (𝔠.Q : Set G), ρ.X⁆ ≤ O (𝔠.H₀ ⊓ normalizer (𝔠.Q : Set G)) :=
  𝔠.hH₁.2.2.1

theorem exists_covering_W_H₁ : ∃ W : Subgroup G, W ≤ 𝔠.H₀ ⊓ normalizer (𝔠.Q : Set G) ⊓ ρ.M₀ ∧
    ρ.Y ≤ W ∧ Covers W ρ.M₀ (O ρ.M) ∧
    ((W ⊔ O (𝔠.H₀ ⊓ normalizer (𝔠.Q : Set G))).subgroupOf
      (𝔠.H₀ ⊓ normalizer (𝔠.Q : Set G))).Normal ∧
    O (𝔠.H₀ ⊓ normalizer (𝔠.Q : Set G)) ⊓ W = W ⊓ O ρ.M ∧
    IsL2OrA7 (bar (𝔠.H₀ ⊓ normalizer (𝔠.Q : Set G)) W) 5 :=
  𝔠.hH₁.2.2.2

theorem commutator_P_X_le_Q : ⁅𝔠.P, ρ.X⁆ ≤ 𝔠.Q := by
  refine le_inf ?_ ?_
  · rw [commutator_comm]
    exact le_normalizer_iff_commutator_le_right.mp (ρ.X_le_A.trans 𝔠.A_le_normalizer_P)
  · exact (commutator_mono 𝔠.P_le_H₁ le_rfl).trans (𝔠.commutator_H₁_X_le.trans 𝔠.O_H₁_le_O_H₀)

theorem P_le_Q_sup_R : 𝔠.P ≤ 𝔠.Q ⊔ 𝔠.R :=
  (le_commutator_sup_inf_centralizer_of_coprime_pGroup 𝔠.hp 𝔠.hp2 𝔠.isPGroup_P ρ.isPGroup_two_X
    (ρ.X_le_A.trans 𝔠.A_le_normalizer_P)).trans (sup_le_sup_right 𝔠.commutator_P_X_le_Q _)

theorem P_eq_Q_sup_R : 𝔠.P = 𝔠.Q ⊔ 𝔠.R :=
  le_antisymm 𝔠.P_le_Q_sup_R (sup_le 𝔠.Q_le_P inf_le_left)

theorem lemma_5_11_of (h58 : 𝔠.R = 𝔠.U) (W : Subgroup G)
    (hW : 𝔠.Q = (𝔠.R ⊓ 𝔠.Q) ⊔ W ∧ IsCyclic W ∧
      A ≤ normalizer (W : Set G) ∧ W ≤ 𝔠.K₁ ⊓ centralizer (𝔠.V : Set G) ∧ ⁅ρ.X, W⁆ = W) :
    𝔠.P = 𝔠.Pstar ∧ 𝔠.P = 𝔠.U ⊔ W :=
  𝔠.toSec5KConfig.lemma_5_11_of 𝔠.Q 𝔠.Q_le_P 𝔠.P_eq_Q_sup_R h58 W hW

theorem covers_normalizer_inf_centralizer_X :
    Covers (normalizer ((𝔠.Q ⊓ centralizer (ρ.X : Set G) : Subgroup G) : Set G)) ρ.M₀
      (O ρ.M) := by
  refine 𝔠.covers_H₁.mono ?_
  rintro g ⟨⟨-, hgQ⟩, hgM₀⟩
  exact inf_normalizer_le_normalizer_inf ⟨hgQ, le_normalizer (ρ.M₀_le hgM₀)⟩

theorem not_isCyclic_Q
    (h47i : QuotIs ρ.M₀ (O ρ.M) (fun L _ => IsL2OrA7 L 5)) (hYM₀ : ρ.Y ≤ ρ.M₀) :
    ¬ IsCyclic 𝔠.Q := by
  intro hQc
  have : IsCyclic 𝔠.Q := hQc
  obtain ⟨L, _, f, hf, hker, hL⟩ := h47i
  set H₁ : Subgroup G := 𝔠.H₀ ⊓ normalizer (𝔠.Q : Set G) with hH₁def
  have hH₁Q : H₁ ≤ normalizer (𝔠.Q : Set G) := inf_le_right
  have hOMn := ρ.M₀_le_normalizer_O_M
  set D : Subgroup G := ⁅H₁ ⊓ ρ.M₀, H₁ ⊓ ρ.M₀⁆ with hDdef
  have hDC : D ≤ centralizer (𝔠.Q : Set G) :=
    CFSG.GroupTheory.CyclicSubgroup.commutator_le_centralizer 𝔠.Q _ _
      (inf_le_left.trans hH₁Q) (inf_le_left.trans hH₁Q)
  have hDH₁ : D ≤ H₁ := (commutator_le_self _).trans inf_le_left
  have hDM₀ : D ≤ ρ.M₀ := (commutator_le_self _).trans inf_le_right
  have hM₀D : ρ.M₀ ≤ D ⊔ O ρ.M :=
    le_commutator_sup_of_covers f hf hker (commutator_eq_top_of_isL2OrA7 le_rfl hL)
      𝔠.covers_H₁ hOMn
  apply 𝔠.Y_not_le_centralizer_Q
  intro y hy
  have hyA : y ∈ A := ρ.Y_le_A hy
  have hyH₁ : y ∈ H₁ := 𝔠.A_le_H₁ hyA
  have hy' : y ∈ ((D ⊔ O ρ.M : Subgroup G) : Set G) := hM₀D (hYM₀ hy)
  rw [coe_mul_of_left_le_normalizer_right _ _ (hDM₀.trans hOMn)] at hy'
  obtain ⟨d, hd, o, ho, hdo⟩ := hy'
  have hoH₁ : o ∈ H₁ := by
    have : o = d⁻¹ * y := by rw [← hdo]; group
    rw [this]
    exact mul_mem (inv_mem (hDH₁ hd)) hyH₁
  have hoN : o ∈ normalizer (𝔠.Q : Set G) := hH₁Q hoH₁
  have hyo : ∀ q ∈ 𝔠.Q, y * q * y⁻¹ = o * q * o⁻¹ := by
    intro q hq
    have hoq : o * q * o⁻¹ ∈ 𝔠.Q := (mem_normalizer_iff.mp hoN q).mp hq
    have hdc := mem_centralizer_iff.mp (hDC hd) _ hoq
    rw [← hdo]
    calc d * o * q * (d * o)⁻¹ = d * (o * q * o⁻¹) * d⁻¹ := by group
      _ = (o * q * o⁻¹) * d * d⁻¹ := by rw [← hdc]
      _ = o * q * o⁻¹ := by group
  have hyy : y * y = 1 := ρ.mul_self_of_mem_A hyA
  have ho2 : o ^ 2 ∈ centralizer (𝔠.Q : Set G) := by
    rw [mem_centralizer_iff]
    intro q hq
    have hoq : o * q * o⁻¹ ∈ 𝔠.Q := (mem_normalizer_iff.mp hoN q).mp hq
    have e1 := hyo q hq
    have e2 := hyo _ hoq
    have hy1 : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
    have : o ^ 2 * q * (o ^ 2)⁻¹ = q := by
      calc o ^ 2 * q * (o ^ 2)⁻¹ = o * (o * q * o⁻¹) * o⁻¹ := by rw [pow_two]; group
        _ = y * (y * q * y⁻¹) * y⁻¹ := by rw [← e2, ← e1]
        _ = (y * y) * q * (y * y)⁻¹ := by group
        _ = q := by rw [hyy]; group
    calc q * o ^ 2 = o ^ 2 * q * (o ^ 2)⁻¹ * o ^ 2 := by rw [this]
      _ = o ^ 2 * q := by group
  have hoodd : Odd (orderOf o) :=
    (card_O_odd ρ.M).of_dvd_nat (Subgroup.orderOf_dvd_natCard _ ho)
  have hoz : o ∈ zpowers (o ^ 2) := by
    rw [mem_zpowers_pow_iff]
    exact Nat.Coprime.gcd_eq_one ((Nat.coprime_two_left).mpr hoodd)
  have hoC : o ∈ centralizer (𝔠.Q : Set G) := (zpowers_le.mpr ho2) hoz
  rw [← hdo]
  exact mul_mem (hDC hd) hoC

theorem lemma_5_12_of_inf_le (h58 : 𝔠.R = 𝔠.U)
    (h47i : QuotIs ρ.M₀ (O ρ.M) (fun L _ => IsL2OrA7 L 5)) (hYM₀ : ρ.Y ≤ ρ.M₀)
    (h48i : QuotIs ρ.N₀ (O ρ.N) (fun L _ => IsL2OrA7 L 5 ∨ IsKleinFour L))
    (hXN₀ : ρ.X ≤ ρ.N₀) (W : Subgroup G)
    (hW : 𝔠.Q = (𝔠.R ⊓ 𝔠.Q) ⊔ W ∧ IsCyclic W ∧
      A ≤ normalizer (W : Set G) ∧ W ≤ 𝔠.K₁ ⊓ centralizer (𝔠.V : Set G) ∧ ⁅ρ.X, W⁆ = W)
    (hQUV : 𝔠.Q ⊓ 𝔠.U ≤ 𝔠.V) : ∃ H, ρ.IsCovering p H := by
  obtain ⟨hPP, hPUW⟩ := 𝔠.lemma_5_11_of h58 W hW
  have hQK : 𝔠.Q ≤ 𝔠.K := 𝔠.Q_le_P.trans (hPP.le.trans inf_le_right)
  have hQU : 𝔠.Q ⊓ 𝔠.U = 𝔠.Q ⊓ centralizer (ρ.X : Set G) := by
    apply le_antisymm
    · exact le_inf inf_le_left (inf_le_right.trans (inf_le_left.trans inf_le_right))
    · exact le_inf inf_le_left
        (le_inf (le_inf (inf_le_left.trans 𝔠.Q_le_P) inf_le_right) (inf_le_left.trans hQK))
  set D : Subgroup G := 𝔠.Q ⊓ 𝔠.U with hDdef
  have hDne : D ≠ ⊥ := by
    intro hD
    apply 𝔠.not_isCyclic_Q h47i hYM₀
    have hQW : 𝔠.Q = W := by
      refine le_antisymm ?_ (le_sup_right.trans hW.1.ge)
      rw [hW.1, h58, inf_comm, ← hDdef, hD, bot_sup_eq]
    rw [hQW]
    exact hW.2.1
  have hDp : IsPGroup p D := 𝔠.isPGroup_P.to_le (inf_le_left.trans 𝔠.Q_le_P)
  have hAU : A ≤ normalizer (𝔠.U : Set G) := fun a ha =>
    inf_normalizer_le_normalizer_inf
      ⟨inf_normalizer_le_normalizer_inf ⟨𝔠.A_le_normalizer_P ha,
        le_normalizer (ρ.A_le_centralizer_of_le ρ.X_le_A ha)⟩,
        le_normalizer (𝔠.A_le_K ha)⟩
  have hAD : A ≤ normalizer (D : Set G) := fun a ha =>
    inf_normalizer_le_normalizer_inf ⟨𝔠.A_le_normalizer_Q ha, hAU ha⟩
  have hPD : 𝔠.P ≤ normalizer (D : Set G) := by
    rw [hPUW]
    refine sup_le ?_ ?_
    · intro u hu
      have huP : u ∈ 𝔠.P := (inf_le_left.trans inf_le_left : 𝔠.U ≤ 𝔠.P) hu
      exact inf_normalizer_le_normalizer_inf ⟨𝔠.P_le_normalizer_Q huP, le_normalizer hu⟩
    · intro w hw
      apply centralizer_le_normalizer
      rw [mem_centralizer_iff]
      intro d hd
      exact mem_centralizer_iff.mp (hW.2.2.2.1 hw).2 d (hQUV hd)
  refine ⟨normalizer (D : Set G), ⟨⟨D, hDne, hDp, rfl⟩, hAD, 𝔠.P, 𝔠.hP, hPD⟩, ?_, ?_⟩
  · have h := 𝔠.covers_normalizer_inf_centralizer_X
    rw [← hQU] at h
    exact h
  · refine (𝔠.covers_centralizer_V h48i hXN₀).mono ?_
    intro g hg
    apply centralizer_le_normalizer
    exact centralizer_le (fun d hd => hQUV hd) hg.1

end Sec5ConfigR

end CFSG.GH72
