module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaEndSection4
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaEndComponents
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaEndNormalizer

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaEnd

open Subgroup CFSG.ABGLocalTools CFSG.Blueprint
open scoped Pointwise MatrixGroups commutatorElement

section Generic

variable {G : Type} [Group G] {G' : Type*} [Group G']

theorem conjR_H_eq {d : YamadaData G} {g : G} (hg : g ∈ d.H) : conjR d.H g = d.H :=
  conjR_eq_self (le_normalizer hg)

theorem mem_normalizer_conjR {X : Subgroup G'} {t g : G'} (htX : t ∈ normalizer (X : Set G'))
    (hg : t * g = g * t) : t ∈ normalizer (conjR X g : Set G') := by
  rw [mem_normalizer_iff]
  intro x
  rw [mem_conjR, mem_conjR]
  have e : g * (t * x * t⁻¹) * g⁻¹ = t * (g * x * g⁻¹) * t⁻¹ := by
    have hg' : g * t = t * g := hg.symm
    calc g * (t * x * t⁻¹) * g⁻¹ = (g * t) * x * (g * t)⁻¹ := by group
      _ = (t * g) * x * (t * g)⁻¹ := by rw [hg']
      _ = t * (g * x * g⁻¹) * t⁻¹ := by group
  rw [e]
  exact mem_normalizer_iff.mp htX _

theorem t_comm_of_mem_H {d : YamadaData G} {g : G} (hg : g ∈ d.H) : d.t * g = g * d.t :=
  (mem_centralizer_singleton_iff.mp hg).symm

end Generic

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F] [CharP F 2]
  {d : YamadaData G}

namespace YamadaSection4

variable (h : YamadaSection4 F d)
include h

theorem t_sq : d.t * d.t = 1 := by rw [← sq, ← h.order_t]; exact pow_orderOf_eq_one d.t

theorem t_inv : d.t⁻¹ = d.t := inv_eq_of_mul_eq_one_right h.t_sq

theorem L_le_H : d.L ≤ d.H := fun l hl =>
  mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp h.t_mem l hl)

theorem w₁_H : d.w₁ ∈ d.H := h.L_le_H h.w₁_mem
theorem w₂_H : d.w₂ ∈ d.H := h.L_le_H h.w₂_mem
theorem w₃_H : d.w₃ ∈ d.H := h.L_le_H h.w₃_mem

theorem u₁_H : d.u₁ ∈ d.H := by
  unfold YamadaData.u₁
  exact mul_mem (mul_mem (mul_mem (mul_mem h.w₁_H h.w₂_H) h.w₃_H) h.w₂_H) h.w₁_H

theorem u₂_H : d.u₂ ∈ d.H := by
  unfold YamadaData.u₂
  exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem h.w₃_H h.w₂_H) h.w₃_H) h.w₁_H) h.w₂_H) h.w₃_H

theorem w₀_H : d.w₀ ∈ d.H := by
  unfold YamadaData.w₀
  exact pow_mem (mul_mem (mul_mem h.w₁_H h.w₂_H) h.w₃_H) 3

theorem isPGroup_P : IsPGroup 2 d.P := h.sylow_P₁.isPGroup

theorem K₁_le_N₁ : d.K₁ ≤ d.N₁ := (le_sup_left.trans h.N₁_H.ge).trans inf_le_left
theorem K₂_le_N₂ : d.K₂ ≤ d.N₂ := (le_sup_left.trans h.N₂_H.ge).trans inf_le_left

theorem w₂_K₁ : d.w₂ ∈ d.K₁ := by
  rw [h.K₁_gen]; exact mem_sup_left (mem_sup_right (mem_zpowers _))
theorem w₃_K₁ : d.w₃ ∈ d.K₁ := by
  rw [h.K₁_gen]; exact mem_sup_right (mem_zpowers _)
theorem w₁_K₂ : d.w₁ ∈ d.K₂ := by
  rw [h.K₂_gen]; exact mem_sup_left (mem_sup_right (mem_zpowers _))
theorem w₂_K₂ : d.w₂ ∈ d.K₂ := by
  rw [h.K₂_gen]; exact mem_sup_right (mem_zpowers _)

theorem inf_facts {N D K A : Subgroup G} {u : G} (hu : u ∈ d.H) (hNH : N ⊓ d.H = K ⊔ A)
    (hDH : D ⊓ d.H = A) (hKA : (K ⊔ A) ⊓ conjR (K ⊔ A) u = K) (hKA' : K ⊓ A = ⊥)
    (htN : d.t ∈ normalizer (N : Set G)) (htD : d.t ∈ normalizer (D : Set G))
    (hD2 : IsPGroup 2 D) : (N ⊓ conjR N u) ⊓ d.H = K ∧ (N ⊓ conjR N u) ⊓ D = ⊥ := by
  have e : conjR N u ⊓ d.H = conjR (N ⊓ d.H) u := by rw [conjR_inf, conjR_H_eq hu]
  have h1 : (N ⊓ conjR N u) ⊓ d.H = K := by
    rw [inf_inf_distrib_right, e, hNH, hKA]
  refine ⟨h1, ?_⟩
  have htT : d.t ∈ normalizer (((N ⊓ conjR N u) ⊓ D : Subgroup G) : Set G) :=
    YamadaEnd.mem_normalizer_inf (YamadaEnd.mem_normalizer_inf htN
      (mem_normalizer_conjR htN (t_comm_of_mem_H hu))) htD
  refine eq_bot_of_inf_centralizer_eq_bot (hD2.to_le inf_le_right) htT h.t_sq ?_
  rw [eq_bot_iff]
  rintro x ⟨⟨hxL, hxD⟩, hxH⟩
  have hxK : x ∈ K := h1 ▸ ⟨hxL, hxH⟩
  have hxA : x ∈ A := hDH ▸ ⟨hxD, hxH⟩
  have : x ∈ K ⊓ A := ⟨hxK, hxA⟩
  rwa [hKA'] at this

omit h in
theorem chain_step {P Q : Subgroup G} {g s : G} {k : ℕ} (hQ : Q ≤ conjR P g)
    (hk : Nat.card (P ⊓ conjR P s : Subgroup G) * 2 ^ k = Nat.card P) :
    Nat.card Q ≤ Nat.card (Q ⊓ conjR P (s * g) : Subgroup G) * 2 ^ k := by
  have h1 := card_inf_conjR_ge s hQ
  rw [← hk, ← mul_assoc, mul_right_comm] at h1
  exact Nat.le_of_mul_le_mul_right h1 Nat.card_pos

theorem card_P_inf_w₁ : Nat.card (d.P ⊓ conjR d.P d.w₁ : Subgroup G) * 2 ^ 4 = Nat.card d.P := by
  rw [h.card_P_w₁, h.card_P]; norm_num

theorem card_P_inf_w₂ : Nat.card (d.P ⊓ conjR d.P d.w₂ : Subgroup G) * 2 ^ 4 = Nat.card d.P := by
  rw [h.card_P_w₂, h.card_P]; norm_num

theorem card_P_inf_w₃ : Nat.card (d.P ⊓ conjR d.P d.w₃ : Subgroup G) * 2 ^ 2 = Nat.card d.P := by
  rw [h.card_P_w₃, h.card_P]; norm_num

theorem card_P₁_ge : 2 ^ 12 ≤ Nat.card d.P₁ := by
  have s2 := chain_step (s := d.w₂) (inf_le_right : d.P ⊓ conjR d.P d.w₁ ≤ conjR d.P d.w₁)
    h.card_P_inf_w₂
  have s3 := chain_step (s := d.w₃) (inf_le_right : (d.P ⊓ conjR d.P d.w₁) ⊓
    conjR d.P (d.w₂ * d.w₁) ≤ conjR d.P (d.w₂ * d.w₁)) h.card_P_inf_w₃
  have s4 := chain_step (s := d.w₂) (inf_le_right : (d.P ⊓ conjR d.P d.w₁) ⊓
    conjR d.P (d.w₂ * d.w₁) ⊓ conjR d.P (d.w₃ * (d.w₂ * d.w₁)) ≤
      conjR d.P (d.w₃ * (d.w₂ * d.w₁))) h.card_P_inf_w₂
  have s5 := chain_step (s := d.w₁) (inf_le_right : (d.P ⊓ conjR d.P d.w₁) ⊓
    conjR d.P (d.w₂ * d.w₁) ⊓ conjR d.P (d.w₃ * (d.w₂ * d.w₁)) ⊓
      conjR d.P (d.w₂ * (d.w₃ * (d.w₂ * d.w₁))) ≤ conjR d.P (d.w₂ * (d.w₃ * (d.w₂ * d.w₁))))
    h.card_P_inf_w₁
  have hle : (d.P ⊓ conjR d.P d.w₁) ⊓ conjR d.P (d.w₂ * d.w₁) ⊓
      conjR d.P (d.w₃ * (d.w₂ * d.w₁)) ⊓ conjR d.P (d.w₂ * (d.w₃ * (d.w₂ * d.w₁))) ⊓
      conjR d.P (d.w₁ * (d.w₂ * (d.w₃ * (d.w₂ * d.w₁)))) ≤ d.P₁ := by
    refine le_inf (inf_le_left.trans (inf_le_left.trans (inf_le_left.trans
      (inf_le_left.trans inf_le_left)))) ?_
    have : d.w₁ * (d.w₂ * (d.w₃ * (d.w₂ * d.w₁))) = d.u₁ := by
      simp only [YamadaData.u₁, mul_assoc]
    rw [← this]
    exact inf_le_right
  have := card_le_of_le hle
  rw [h.card_P_w₁] at s2
  simp only [Nat.reducePow] at s2 s3 s4 s5 ⊢
  omega

theorem card_P₂_ge : 2 ^ 12 ≤ Nat.card d.P₂ := by
  have s2 := chain_step (s := d.w₂) (inf_le_right : d.P ⊓ conjR d.P d.w₃ ≤ conjR d.P d.w₃)
    h.card_P_inf_w₂
  have s3 := chain_step (s := d.w₁) (inf_le_right : (d.P ⊓ conjR d.P d.w₃) ⊓
    conjR d.P (d.w₂ * d.w₃) ≤ conjR d.P (d.w₂ * d.w₃)) h.card_P_inf_w₁
  have s4 := chain_step (s := d.w₃) (inf_le_right : (d.P ⊓ conjR d.P d.w₃) ⊓
    conjR d.P (d.w₂ * d.w₃) ⊓ conjR d.P (d.w₁ * (d.w₂ * d.w₃)) ≤
      conjR d.P (d.w₁ * (d.w₂ * d.w₃))) h.card_P_inf_w₃
  have s5 := chain_step (s := d.w₂) (inf_le_right : (d.P ⊓ conjR d.P d.w₃) ⊓
    conjR d.P (d.w₂ * d.w₃) ⊓ conjR d.P (d.w₁ * (d.w₂ * d.w₃)) ⊓
      conjR d.P (d.w₃ * (d.w₁ * (d.w₂ * d.w₃))) ≤ conjR d.P (d.w₃ * (d.w₁ * (d.w₂ * d.w₃))))
    h.card_P_inf_w₂
  have s6 := chain_step (s := d.w₃) (inf_le_right : (d.P ⊓ conjR d.P d.w₃) ⊓
    conjR d.P (d.w₂ * d.w₃) ⊓ conjR d.P (d.w₁ * (d.w₂ * d.w₃)) ⊓
      conjR d.P (d.w₃ * (d.w₁ * (d.w₂ * d.w₃))) ⊓
      conjR d.P (d.w₂ * (d.w₃ * (d.w₁ * (d.w₂ * d.w₃)))) ≤
        conjR d.P (d.w₂ * (d.w₃ * (d.w₁ * (d.w₂ * d.w₃))))) h.card_P_inf_w₃
  have hle : (d.P ⊓ conjR d.P d.w₃) ⊓ conjR d.P (d.w₂ * d.w₃) ⊓
      conjR d.P (d.w₁ * (d.w₂ * d.w₃)) ⊓ conjR d.P (d.w₃ * (d.w₁ * (d.w₂ * d.w₃))) ⊓
      conjR d.P (d.w₂ * (d.w₃ * (d.w₁ * (d.w₂ * d.w₃)))) ⊓
      conjR d.P (d.w₃ * (d.w₂ * (d.w₃ * (d.w₁ * (d.w₂ * d.w₃))))) ≤ d.P₂ := by
    refine le_inf (inf_le_left.trans (inf_le_left.trans (inf_le_left.trans
      (inf_le_left.trans (inf_le_left.trans inf_le_left))))) ?_
    have : d.w₃ * (d.w₂ * (d.w₃ * (d.w₁ * (d.w₂ * d.w₃)))) = d.u₂ := by
      simp only [YamadaData.u₂, mul_assoc]
    rw [← this]
    exact inf_le_right
  have := card_le_of_le hle
  rw [h.card_P_w₃] at s2
  simp only [Nat.reducePow] at s2 s3 s4 s5 s6 ⊢
  omega

omit h in
theorem sylow_facts {N D P : Subgroup G} {u : G} (hLD : (N ⊓ conjR N u) ⊓ D = ⊥)
    (hND : N ≤ normalizer (D : Set G)) (hPN : IsSylowOf 2 P N) (hDP : D ≤ P)
    (hcardD : Nat.card D = 2 ^ 18) (hcardP : Nat.card P = 2 ^ 30)
    (hchain : 2 ^ 12 ≤ Nat.card (P ⊓ conjR P u : Subgroup G)) :
    Nat.card (P ⊓ conjR P u : Subgroup G) = 2 ^ 12 ∧ (P ⊓ conjR P u) ⊔ D = P ∧
      IsSylowOf 2 (P ⊓ conjR P u) (N ⊓ conjR N u) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPL : P ⊓ conjR P u ≤ N ⊓ conjR N u := inf_le_inf hPN.le (conjR_mono hPN.le u)
  have hbound : ∀ Q : Subgroup G, Q ≤ N ⊓ conjR N u → IsPGroup 2 Q →
      Nat.card Q * 2 ^ 18 ≤ 2 ^ 30 := by
    intro Q hQ hQ2
    have hQD : Q ⊓ D = ⊥ := le_bot_iff.mp (hLD ▸ inf_le_inf_right D hQ)
    have hQN : Q ≤ normalizer (D : Set G) := hQ.trans (inf_le_left.trans hND)
    have hcard := card_sup_of_inf_eq_bot hQN hQD
    have hp : IsPGroup 2 (Q ⊔ D : Subgroup G) :=
      IsPGroup.to_sup_of_normal_right' hQ2 (hPN.isPGroup.to_le hDP) hQN
    have hle := card_le_of_isSylowOf hPN (sup_le (hQ.trans inf_le_left) (hDP.trans hPN.le)) hp
    rw [hcard, hcardD, hcardP] at hle
    exact hle
  have hle12 := hbound _ hPL (hPN.isPGroup.to_le inf_le_left)
  have h12 : Nat.card (P ⊓ conjR P u : Subgroup G) = 2 ^ 12 := by
    have : Nat.card (P ⊓ conjR P u : Subgroup G) ≤ 2 ^ 12 := by
      simp only [Nat.reducePow] at hle12 ⊢
      omega
    omega
  refine ⟨h12, ?_, ?_⟩
  · have hPD : P ⊓ conjR P u ≤ normalizer (D : Set G) := hPL.trans (inf_le_left.trans hND)
    have hinf : (P ⊓ conjR P u) ⊓ D = ⊥ := le_bot_iff.mp (hLD ▸ inf_le_inf_right D hPL)
    refine eq_of_le_of_card_ge (sup_le inf_le_left hDP) ?_
    rw [card_sup_of_inf_eq_bot hPD hinf, h12, hcardD, hcardP]
    norm_num
  · obtain ⟨Q, hQ, hPQ⟩ := exists_isSylowOf_ge hPL (hPN.isPGroup.to_le inf_le_left)
    have hQle := hbound Q hQ.le hQ.isPGroup
    have hQeq : Q = P ⊓ conjR P u := by
      refine (eq_of_le_of_card_ge hPQ ?_).symm
      rw [h12]
      simp only [Nat.reducePow] at hQle ⊢
      omega
    rwa [← hQeq]

theorem L₁_facts : d.L₁ ⊓ d.H = d.K₁ ∧ d.L₁ ⊓ d.D₁ = ⊥ :=
  h.inf_facts h.u₁_H h.N₁_H h.D₁_H h.KA₁ h.K₁_A₁ h.t_N₁ h.t_D₁ (h.isPGroup_P.to_le h.D₁_le_P)

theorem L₂_facts : d.L₂ ⊓ d.H = d.K₂ ∧ d.L₂ ⊓ d.D₂ = ⊥ :=
  h.inf_facts h.u₂_H h.N₂_H h.D₂_H h.KA₂ h.K₂_A₂ h.t_N₂ h.t_D₂ (h.isPGroup_P.to_le h.D₂_le_P)

theorem P₁_facts : Nat.card d.P₁ = 2 ^ 12 ∧ d.P₁ ⊔ d.D₁ = d.P ∧ IsSylowOf 2 d.P₁ d.L₁ :=
  sylow_facts h.L₁_facts.2 h.N₁_norm h.sylow_P₁ h.D₁_le_P h.card_D₁ h.card_P h.card_P₁_ge

theorem P₂_facts : Nat.card d.P₂ = 2 ^ 12 ∧ d.P₂ ⊔ d.D₂ = d.P ∧ IsSylowOf 2 d.P₂ d.L₂ :=
  sylow_facts h.L₂_facts.2 h.N₂_norm h.sylow_P₂ h.D₂_le_P h.card_D₂ h.card_P h.card_P₂_ge

theorem K₁_le_L₁ : d.K₁ ≤ d.L₁ := h.L₁_facts.1 ▸ inf_le_left
theorem K₂_le_L₂ : d.K₂ ≤ d.L₂ := h.L₂_facts.1 ▸ inf_le_left

theorem N₁_eq : d.N₁ = d.L₁ ⊔ d.D₁ := by
  refine le_antisymm ?_ (sup_le inf_le_left h.D₁_le)
  rw [h.N₁_gen]
  refine sup_le (sup_le ?_ ?_) ?_
  · rw [← h.P₁_facts.2.1]
    exact sup_le_sup_right (h.P₁_facts.2.2.le) _
  · rw [zpowers_le]; exact mem_sup_left (h.K₁_le_L₁ h.w₂_K₁)
  · rw [zpowers_le]; exact mem_sup_left (h.K₁_le_L₁ h.w₃_K₁)

theorem N₂_eq : d.N₂ = d.L₂ ⊔ d.D₂ := by
  refine le_antisymm ?_ (sup_le inf_le_left h.D₂_le)
  rw [h.N₂_gen]
  refine sup_le (sup_le ?_ ?_) ?_
  · rw [← h.P₂_facts.2.1]
    exact sup_le_sup_right (h.P₂_facts.2.2.le) _
  · rw [zpowers_le]; exact mem_sup_left (h.K₂_le_L₂ h.w₁_K₂)
  · rw [zpowers_le]; exact mem_sup_left (h.K₂_le_L₂ h.w₂_K₂)

theorem P_inf_w₀ : d.P ⊓ conjR d.P d.w₀ = ⊥ := by
  have htT : d.t ∈ normalizer ((d.P ⊓ conjR d.P d.w₀ : Subgroup G) : Set G) :=
    YamadaEnd.mem_normalizer_inf h.t_P (mem_normalizer_conjR h.t_P (t_comm_of_mem_H h.w₀_H))
  refine eq_bot_of_inf_centralizer_eq_bot (h.isPGroup_P.to_le inf_le_left) htT h.t_sq ?_
  have e : conjR d.P d.w₀ ⊓ d.H = conjR d.S d.w₀ := by
    rw [← conjR_H_eq h.w₀_H, ← conjR_inf, h.P_H]
  change d.P ⊓ conjR d.P d.w₀ ⊓ d.H = ⊥
  rw [inf_inf_distrib_right, e, h.P_H, h.S_w₀]

theorem card_w₀_mul (s : G) :
    Nat.card (d.P ⊓ conjR d.P (d.w₀ * s) : Subgroup G) *
      Nat.card (d.P ⊓ conjR d.P s : Subgroup G) ≤ Nat.card d.P := by
  have h1 := card_mul_card_le_inf (inf_le_left : d.P ⊓ conjR d.P (d.w₀ * s) ≤ d.P)
    (inf_le_left : d.P ⊓ conjR d.P s ≤ d.P)
  have h2 : (d.P ⊓ conjR d.P (d.w₀ * s)) ⊓ (d.P ⊓ conjR d.P s) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨-, hx₁⟩, -, hx₂⟩
    have : x ∈ conjR (d.P ⊓ conjR d.P d.w₀) s := by
      rw [conjR_inf, ← conjR_mul]
      exact ⟨hx₂, hx₁⟩
    rwa [h.P_inf_w₀, conjR, Subgroup.map_bot] at this
  rwa [h2, card_bot, one_mul] at h1

theorem t_L₂ : d.t ∈ normalizer (d.L₂ : Set G) :=
  YamadaEnd.mem_normalizer_inf h.t_N₂ (mem_normalizer_conjR h.t_N₂ (t_comm_of_mem_H h.u₂_H))

theorem t_L₁ : d.t ∈ normalizer (d.L₁ : Set G) :=
  YamadaEnd.mem_normalizer_inf h.t_N₁ (mem_normalizer_conjR h.t_N₁ (t_comm_of_mem_H h.u₁_H))

omit h [Finite G] in
theorem le_normalizer_of_commutator_le {X Y D : Subgroup G} (hXY : ⁅X, Y⁆ ≤ D) (hDX : D ≤ X) :
    Y ≤ normalizer (X : Set G) := by
  refine le_normalizer_of_conj_mem fun y hy x hx => ?_
  have hc : ⁅y, x⁆ ∈ D :=
    hXY (by rw [commutator_comm]; exact commutator_mem_commutator hy hx)
  have : y * x * y⁻¹ = ⁅y, x⁆ * x := by rw [commutatorElement_def]; group
  rw [this]
  exact mul_mem (hDX hc) hx

omit h [Finite G] in
theorem components_of {N D Mt L : Subgroup G} {t : G} (ht : t * t = 1)
    (hDM : D ≤ Mt) (hMN : Mt ≤ N) (hN : N = Mt ⊔ conjR Mt t) (hcomm : ⁅Mt, conjR Mt t⁆ ≤ D)
    (hLN : L ≤ N) (hNeq : N = L ⊔ D) (hLD : L ⊓ D = ⊥) (hND : N ≤ normalizer (D : Set G))
    (htL : t ∈ normalizer (L : Set G)) (htD : t ∈ normalizer (D : Set G)) :
    L ≤ normalizer ((L ⊓ Mt : Subgroup G) : Set G) ∧ conjR (L ⊓ Mt) t = L ⊓ conjR Mt t ∧
      L ≤ normalizer ((L ⊓ conjR Mt t : Subgroup G) : Set G) ∧
      (L ⊓ Mt) ⊔ (L ⊓ conjR Mt t) = L ∧ ⁅L ⊓ Mt, L ⊓ conjR Mt t⁆ = ⊥ ∧
      ((L ⊓ Mt) ⊓ (L ⊓ conjR Mt t)) ⊔ D ≤ Mt ⊓ conjR Mt t ∧
      ((L ⊓ Mt) ⊓ (L ⊓ conjR Mt t)) ⊓ D = ⊥ := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hDMt : D ≤ conjR Mt t := by
    rw [← conjR_eq_self (show t ∈ normalizer (D : Set G) from htD)]
    exact conjR_mono hDM t
  have hMtN : N ≤ normalizer (Mt : Set G) := by
    rw [hN]
    exact sup_le le_normalizer (le_normalizer_of_commutator_le hcomm hDM)
  have hMtN' : N ≤ normalizer (conjR Mt t : Set G) := by
    rw [hN]
    refine sup_le (le_normalizer_of_commutator_le (by rw [commutator_comm]; exact hcomm) hDMt)
      le_normalizer
  have hLNM : L ≤ normalizer ((L ⊓ Mt : Subgroup G) : Set G) := fun x hx =>
    YamadaEnd.mem_normalizer_inf (le_normalizer hx) (hMtN (hLN hx))
  have hLNM' : L ≤ normalizer ((L ⊓ conjR Mt t : Subgroup G) : Set G) := fun x hx =>
    YamadaEnd.mem_normalizer_inf (le_normalizer hx) (hMtN' (hLN hx))
  have hconj : conjR (L ⊓ Mt) t = L ⊓ conjR Mt t := by
    rw [conjR_inf, conjR_eq_self (show t ∈ normalizer (L : Set G) from htL)]
  refine ⟨hLNM, hconj, hLNM', ?_, ?_, ?_, ?_⟩
  ·
    refine le_antisymm (sup_le inf_le_left inf_le_left) fun x hx => ?_
    have hxN : x ∈ (Mt : Set G) * (conjR Mt t : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left Mt (conjR Mt t)
        (le_sup_right.trans (hN ▸ hMtN)), ← hN]
      exact hLN hx
    obtain ⟨m₁, hm₁, m₂, hm₂, rfl⟩ := hxN
    have hLDmul : (↑N : Set G) = (L : Set G) * (D : Set G) := by
      rw [hNeq]
      exact coe_mul_of_left_le_normalizer_right L D (hLN.trans hND)
    have hm₁N : m₁ ∈ (L : Set G) * (D : Set G) := hLDmul ▸ hMN hm₁
    have hm₂N : m₂ ∈ (L : Set G) * (D : Set G) := by
      rw [← hLDmul, hN]
      exact mem_sup_right hm₂
    obtain ⟨l₁, hl₁, d₁, hd₁, rfl⟩ := hm₁N
    obtain ⟨l₂, hl₂, d₂, hd₂, rfl⟩ := hm₂N
    beta_reduce at hm₁ hm₂ hx ⊢
    have hl₁M : l₁ ∈ Mt := by
      have := Mt.mul_mem hm₁ (Mt.inv_mem (hDM hd₁))
      simpa using this
    have hl₂M : l₂ ∈ conjR Mt t := by
      have := (conjR Mt t).mul_mem hm₂ ((conjR Mt t).inv_mem (hDMt hd₂))
      simpa using this
    have hcD : l₂⁻¹ * d₁ * l₂ * d₂ ∈ D := by
      have h1 : l₂⁻¹ * d₁ * l₂ ∈ D := by
        have := (mem_normalizer_iff.mp (hND (hLN (L.inv_mem hl₂))) d₁).mp hd₁
        simpa using this
      exact D.mul_mem h1 hd₂
    have hcL : l₂⁻¹ * d₁ * l₂ * d₂ ∈ L := by
      have hxL : l₁ * d₁ * (l₂ * d₂) ∈ L := hx
      have : l₂⁻¹ * d₁ * l₂ * d₂ = (l₁ * l₂)⁻¹ * (l₁ * d₁ * (l₂ * d₂)) := by group
      rw [this]
      exact L.mul_mem (L.inv_mem (L.mul_mem hl₁ hl₂)) hxL
    have hc1 : l₂⁻¹ * d₁ * l₂ * d₂ = 1 := by
      have := hLD.le ⟨hcL, hcD⟩
      rwa [mem_bot] at this
    have hx' : l₁ * d₁ * (l₂ * d₂) = l₁ * l₂ := by
      calc l₁ * d₁ * (l₂ * d₂) = l₁ * l₂ * (l₂⁻¹ * d₁ * l₂ * d₂) := by group
        _ = l₁ * l₂ := by rw [hc1, mul_one]
    rw [hx']
    exact mul_mem (mem_sup_left ⟨hl₁, hl₁M⟩) (mem_sup_right ⟨hl₂, hl₂M⟩)
  ·
    rw [eq_bot_iff, ← hLD]
    refine le_inf ((commutator_mono inf_le_left inf_le_left).trans (commutator_le_self L))
      ((commutator_mono inf_le_right inf_le_right).trans hcomm)
  · exact sup_le (inf_le_inf (inf_le_right) (inf_le_right)) (le_inf hDM hDMt)
  · rw [eq_bot_iff, ← hLD]
    exact inf_le_inf_right D (inf_le_left.trans inf_le_left)

omit h [Finite G] in
theorem nonempty_quotientEquiv {L D Mt : Subgroup G} [(D.subgroupOf Mt).Normal] (hDM : D ≤ Mt)
    (hMt : Mt ≤ L ⊔ D) (hLD : L ⊓ D = ⊥) (hLN : L ≤ normalizer (D : Set G)) :
    Nonempty (↥(L ⊓ Mt) ≃* ↥Mt ⧸ D.subgroupOf Mt) := by
  set f : ↥(L ⊓ Mt) →* ↥Mt ⧸ D.subgroupOf Mt :=
    (QuotientGroup.mk' (D.subgroupOf Mt)).comp (inclusion inf_le_right) with hf
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro x hx
    rw [hf, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      mem_subgroupOf, coe_inclusion] at hx
    have : (x : G) ∈ L ⊓ D := ⟨x.2.1, hx⟩
    rw [hLD, mem_bot] at this
    exact Subtype.ext this
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective y
    have hm : (m : G) ∈ (L : Set G) * (D : Set G) := by
      rw [← coe_mul_of_left_le_normalizer_right L D hLN]
      exact hMt m.2
    obtain ⟨l, hl, e, he, hle⟩ := hm
    have hlM : l ∈ Mt := by
      have := Mt.mul_mem m.2 (Mt.inv_mem (hDM he))
      rwa [← hle, mul_inv_cancel_right] at this
    refine ⟨⟨l, hl, hlM⟩, ?_⟩
    rw [hf, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    rw [mem_subgroupOf]
    simp only [coe_mul, coe_inv, coe_inclusion]
    rw [← hle]
    simpa using he
  exact ⟨MulEquiv.ofBijective f ⟨hinj, hsurj⟩⟩

theorem L₂_components : ∃ M : Subgroup G, d.L₂ ≤ normalizer (M : Set G) ∧
    d.L₂ ≤ normalizer (conjR M d.t : Set G) ∧ M ⊔ conjR M d.t = d.L₂ ∧
    ⁅M, conjR M d.t⁆ = ⊥ ∧ Odd (Nat.card (M ⊓ conjR M d.t : Subgroup G)) ∧
    ∃ θ : SL(3, F) →* M, Function.Surjective θ ∧ θ.ker ≤ center SL(3, F) := by
  obtain ⟨Mt, hDM, hMN, hN, hcomm, hidx, hnorm, ψ, hψ, hψker⟩ := h.type₂
  obtain ⟨hn₁, hconj, hn₂, hsup, hc, hXD, hXinf⟩ := components_of (L := d.L₂) h.t_sq hDM hMN hN
    hcomm inf_le_left h.N₂_eq h.L₂_facts.2 h.N₂_norm h.t_L₂ h.t_D₂
  refine ⟨d.L₂ ⊓ Mt, hn₁, hconj ▸ hn₂, hconj ▸ hsup, hconj ▸ hc, ?_, ?_⟩
  · rw [hconj]
    set X := (d.L₂ ⊓ Mt) ⊓ (d.L₂ ⊓ conjR Mt d.t) with hX
    have hXN : X ≤ normalizer (d.D₂ : Set G) :=
      (inf_le_left.trans inf_le_left).trans (inf_le_left.trans h.N₂_norm)
    have h1 := card_sup_of_inf_eq_bot hXN hXinf
    have h2 := card_dvd_of_le hXD
    have h3 := Subgroup.relIndex_mul_card d.D₂ (Mt ⊓ conjR Mt d.t)
    rw [inf_of_le_left (hXD.trans' le_sup_right)] at h3
    rw [h1, ← h3] at h2
    have h4 : Nat.card X ∣ d.D₂.relIndex (Mt ⊓ conjR Mt d.t) :=
      Nat.dvd_of_mul_dvd_mul_right Nat.card_pos h2
    exact Odd.of_dvd_nat (by decide) (h4.trans hidx)
  · obtain ⟨e⟩ := nonempty_quotientEquiv hDM (hMN.trans h.N₂_eq.le) h.L₂_facts.2
      (inf_le_left.trans h.N₂_norm)
    exact ⟨e.symm.toMonoidHom.comp ψ, e.symm.surjective.comp hψ, by
      intro x hx
      apply hψker
      rw [MonoidHom.mem_ker] at hx ⊢
      simpa using hx⟩

omit h [Finite G] in
theorem conjR_inf_H (X : Subgroup G) {g : G} (hg : g ∈ d.H) :
    conjR X g ⊓ d.H = conjR (X ⊓ d.H) g := by
  rw [conjR_inf, conjR_H_eq hg]

theorem P₂_inf_H : d.P₂ ⊓ d.H = d.S ⊓ conjR d.S d.u₂ := by
  change (d.P ⊓ conjR d.P d.u₂) ⊓ d.H = _
  rw [inf_inf_distrib_right, conjR_inf_H _ h.u₂_H, h.P_H]

theorem P₁_inf_H : d.P₁ ⊓ d.H = d.S ⊓ conjR d.S d.u₁ := by
  change (d.P ⊓ conjR d.P d.u₁) ⊓ d.H = _
  rw [inf_inf_distrib_right, conjR_inf_H _ h.u₁_H, h.P_H]

omit h [Finite G] in
theorem inf_conjR_le_sup {P Pi D L : Subgroup G} {g : G} (hP : Pi ⊔ D = P) (hPiL : Pi ≤ L)
    (hLD : L ⊓ D = ⊥) (hPiN : Pi ≤ normalizer (D : Set G)) (hgL : conjR L g = L)
    (hgD : conjR D g = D) : P ⊓ conjR P g ≤ (Pi ⊓ conjR Pi g) ⊔ D := by
  rintro x ⟨hx, hxg⟩
  have hPmul : (↑P : Set G) = (Pi : Set G) * (D : Set G) := by
    rw [← hP]; exact coe_mul_of_left_le_normalizer_right Pi D hPiN
  have hPgmul : (↑(conjR P g) : Set G) = (conjR Pi g : Set G) * (D : Set G) := by
    rw [← hP, conjR_sup, hgD]
    refine coe_mul_of_left_le_normalizer_right _ D ?_
    rw [← hgD]
    intro y hy
    rw [mem_normalizer_iff]
    intro z
    rw [mem_conjR, mem_conjR]
    rw [mem_conjR] at hy
    have := (mem_normalizer_iff.mp (hPiN hy)) (g * z * g⁻¹)
    rw [show g * (y * z * y⁻¹) * g⁻¹ = g * y * g⁻¹ * (g * z * g⁻¹) * (g * y * g⁻¹)⁻¹ by group]
    exact this
  have h1 : x ∈ (Pi : Set G) * (D : Set G) := hPmul ▸ hx
  have h2 : x ∈ (conjR Pi g : Set G) * (D : Set G) := hPgmul ▸ hxg
  obtain ⟨p, hp, e, he, rfl⟩ := h1
  obtain ⟨p', hp', e', he', hpe⟩ := h2
  beta_reduce at hpe ⊢
  have hpL : p ∈ L := hPiL hp
  have hp'L : p' ∈ L := by rw [← hgL]; exact conjR_mono hPiL g hp'
  have hc : p'⁻¹ * p ∈ L ⊓ D := by
    refine ⟨L.mul_mem (L.inv_mem hp'L) hpL, ?_⟩
    have : p'⁻¹ * p = e' * e⁻¹ := by
      calc p'⁻¹ * p = p'⁻¹ * (p * e) * e⁻¹ := by group
        _ = p'⁻¹ * (p' * e') * e⁻¹ := by rw [← hpe]
        _ = e' * e⁻¹ := by group
    rw [this]
    exact D.mul_mem he' (D.inv_mem he)
  rw [hLD, mem_bot, inv_mul_eq_one] at hc
  subst hc
  exact mul_mem (mem_sup_left ⟨hp, hp'⟩) (mem_sup_right he)

theorem card_P₂_inf_sq {g : G} (hgL : g ∈ d.L₂) (hgH : g ∈ d.H) :
    Nat.card (d.P₂ ⊓ conjR d.P₂ g : Subgroup G) =
      Nat.card ((d.P₂ ⊓ conjR d.P₂ g) ⊓ d.H : Subgroup G) ^ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨M, hn, hn', hsup, hc, hodd, -⟩ := h.L₂_components
  set M' := conjR M d.t with hM'
  have hsyl : IsSylowOf 2 d.P₂ (M ⊔ M') := hsup.symm ▸ h.P₂_facts.2.2
  have hP₂ := sylow_eq_sup hc hodd hsyl (hsup.symm ▸ hn) (hsup.symm ▸ hn')
  have hgM : conjR M g = M := conjR_eq_self (hn hgL)
  have hgM' : conjR M' g = M' := conjR_eq_self (hn' hgL)
  have hP₂2 : IsPGroup 2 d.P₂ := h.P₂_facts.2.2.isPGroup
  have hdec : d.P₂ ⊓ conjR d.P₂ g = ((d.P₂ ⊓ M) ⊓ conjR (d.P₂ ⊓ M) g) ⊔
      ((d.P₂ ⊓ M') ⊓ conjR (d.P₂ ⊓ M') g) := by
    conv_lhs => rw [hP₂, conjR_sup]
    exact sup_inf_sup hc hodd inf_le_right
      ((conjR_mono (inf_le_right : d.P₂ ⊓ M ≤ M) g).trans hgM.le) inf_le_right
      ((conjR_mono (inf_le_right : d.P₂ ⊓ M' ≤ M') g).trans hgM'.le) (hP₂2.to_le inf_le_left)
      ((hP₂2.to_le inf_le_left).map _)
  set T := d.P₂ ⊓ conjR d.P₂ g with hT
  have hT2 : IsPGroup 2 T := hP₂2.to_le inf_le_left
  have htT : d.t ∈ normalizer (T : Set G) := by
    have htP₂ : d.t ∈ normalizer (d.P₂ : Set G) :=
      YamadaEnd.mem_normalizer_inf h.t_P (mem_normalizer_conjR h.t_P (t_comm_of_mem_H h.u₂_H))
    exact YamadaEnd.mem_normalizer_inf htP₂ (mem_normalizer_conjR htP₂ (t_comm_of_mem_H hgH))
  have hTeq : T = (T ⊓ M) ⊔ (T ⊓ M') := by
    refine le_antisymm ?_ (sup_le inf_le_left inf_le_left)
    conv_lhs => rw [hdec]
    exact sup_le_sup (le_inf (hdec ▸ le_sup_left) (inf_le_left.trans inf_le_right))
      (le_inf (hdec ▸ le_sup_right) (inf_le_left.trans inf_le_right))
  obtain ⟨h1, h2⟩ := card_inf_centralizer_eq hc hodd h.t_sq rfl hT2 htT hTeq
  rw [h2, ← h1]
  rfl

theorem card_Ub : Nat.card d.Ub = 16 := by
  have hba : d.w₂ * d.w₁ ∈ d.L₂ := mul_mem (h.K₂_le_L₂ h.w₂_K₂) (h.K₂_le_L₂ h.w₁_K₂)
  have h1 := h.card_P₂_inf_sq hba (mul_mem h.w₂_H h.w₁_H)
  have h2 : (d.P₂ ⊓ conjR d.P₂ (d.w₂ * d.w₁)) ⊓ d.H = d.X₂ := by
    rw [inf_inf_distrib_right, conjR_inf_H _ (mul_mem h.w₂_H h.w₁_H), h.P₂_inf_H, h.S_b]
  change Nat.card (d.P₂ ⊓ conjR d.P₂ (d.w₂ * d.w₁) : Subgroup G) = 16
  rw [h1, h2, h.card_X₂]
  norm_num

theorem card_w₀_le {s : G} {k : ℕ}
    (hk : Nat.card (d.P ⊓ conjR d.P s : Subgroup G) * 2 ^ k = Nat.card d.P) :
    Nat.card (d.P ⊓ conjR d.P (d.w₀ * s) : Subgroup G) ≤ 2 ^ k := by
  have h1 := h.card_w₀_mul s
  rw [← hk, mul_comm (Nat.card _) (2 ^ k)] at h1
  exact Nat.le_of_mul_le_mul_right h1 Nat.card_pos

theorem Ub_eq : d.Ub = d.P ⊓ conjR d.P (d.w₀ * d.w₂) := by
  have hle : d.Ub ≤ d.P ⊓ conjR d.P (d.w₀ * d.w₂) := by
    refine le_inf (inf_le_left.trans inf_le_left) ?_
    have e : d.u₂ * (d.w₂ * d.w₁) = d.w₀ * d.w₂ := by
      rw [← h.word_b]; simp only [YamadaData.u₂, mul_assoc]
    rw [← e, conjR_mul]
    exact inf_le_right.trans (conjR_mono inf_le_right _)
  refine eq_of_le_of_card_ge hle ?_
  rw [h.card_Ub]
  exact h.card_w₀_le h.card_P_inf_w₂

theorem w₃w₂w₃_L₁ : d.w₃ * d.w₂ * d.w₃ ∈ d.L₁ :=
  mul_mem (mul_mem (h.K₁_le_L₁ h.w₃_K₁) (h.K₁_le_L₁ h.w₂_K₁)) (h.K₁_le_L₁ h.w₃_K₁)

theorem w₂w₃w₂_L₁ : d.w₂ * d.w₃ * d.w₂ ∈ d.L₁ :=
  mul_mem (mul_mem (h.K₁_le_L₁ h.w₂_K₁) (h.K₁_le_L₁ h.w₃_K₁)) (h.K₁_le_L₁ h.w₂_K₁)

theorem card_inf_le₁ {g : G} (hg : g ∈ d.L₁) :
    Nat.card (d.P ⊓ conjR d.P g : Subgroup G) ≤
      Nat.card (d.P₁ ⊓ conjR d.P₁ g : Subgroup G) * 2 ^ 18 := by
  have hle := inf_conjR_le_sup h.P₁_facts.2.1 h.P₁_facts.2.2.le h.L₁_facts.2
    (h.P₁_facts.2.2.le.trans (inf_le_left.trans h.N₁_norm)) (conjR_eq_self (le_normalizer hg))
    (conjR_eq_self (h.N₁_norm (inf_le_left (a := d.N₁) hg)))
  have hN : d.P₁ ⊓ conjR d.P₁ g ≤ normalizer (d.D₁ : Set G) :=
    (inf_le_left.trans h.P₁_facts.2.2.le).trans (inf_le_left.trans h.N₁_norm)
  rw [← h.card_D₁]
  exact (card_le_of_le hle).trans (card_sup_le hN)

theorem card_P_cbc : 2 ^ 22 ≤ Nat.card (d.P ⊓ conjR d.P (d.w₃ * d.w₂ * d.w₃) : Subgroup G) := by
  have s2 := chain_step (s := d.w₂) (inf_le_right : d.P ⊓ conjR d.P d.w₃ ≤ conjR d.P d.w₃)
    h.card_P_inf_w₂
  have s3 := chain_step (s := d.w₃) (inf_le_right : (d.P ⊓ conjR d.P d.w₃) ⊓
    conjR d.P (d.w₂ * d.w₃) ≤ conjR d.P (d.w₂ * d.w₃)) h.card_P_inf_w₃
  have hle : (d.P ⊓ conjR d.P d.w₃) ⊓ conjR d.P (d.w₂ * d.w₃) ⊓
      conjR d.P (d.w₃ * (d.w₂ * d.w₃)) ≤ d.P ⊓ conjR d.P (d.w₃ * d.w₂ * d.w₃) := by
    refine le_inf (inf_le_left.trans (inf_le_left.trans inf_le_left)) ?_
    rw [mul_assoc]
    exact inf_le_right
  have := card_le_of_le hle
  rw [h.card_P_w₃] at s2
  simp only [Nat.reducePow] at s2 s3 ⊢
  omega

theorem card_P_bcb : 2 ^ 20 ≤ Nat.card (d.P ⊓ conjR d.P (d.w₂ * d.w₃ * d.w₂) : Subgroup G) := by
  have s2 := chain_step (s := d.w₃) (inf_le_right : d.P ⊓ conjR d.P d.w₂ ≤ conjR d.P d.w₂)
    h.card_P_inf_w₃
  have s3 := chain_step (s := d.w₂) (inf_le_right : (d.P ⊓ conjR d.P d.w₂) ⊓
    conjR d.P (d.w₃ * d.w₂) ≤ conjR d.P (d.w₃ * d.w₂)) h.card_P_inf_w₂
  have hle : (d.P ⊓ conjR d.P d.w₂) ⊓ conjR d.P (d.w₃ * d.w₂) ⊓
      conjR d.P (d.w₂ * (d.w₃ * d.w₂)) ≤ d.P ⊓ conjR d.P (d.w₂ * d.w₃ * d.w₂) := by
    refine le_inf (inf_le_left.trans (inf_le_left.trans inf_le_left)) ?_
    rw [mul_assoc]
    exact inf_le_right
  have := card_le_of_le hle
  rw [h.card_P_w₂] at s2
  simp only [Nat.reducePow] at s2 s3 ⊢
  omega

theorem P₁_cbc : d.P₁ ⊓ conjR d.P₁ (d.w₃ * d.w₂ * d.w₃) = d.Ub := by
  have hle : d.P₁ ⊓ conjR d.P₁ (d.w₃ * d.w₂ * d.w₃) ≤ d.Ub := by
    rw [h.Ub_eq]
    refine le_inf (inf_le_left.trans inf_le_left) ?_
    have e : d.u₁ * (d.w₃ * d.w₂ * d.w₃) = d.w₀ * d.w₂ := by
      rw [← h.word_b']; simp only [YamadaData.u₁, mul_assoc]
    rw [← e, conjR_mul d.P d.u₁]
    exact inf_le_right.trans (conjR_mono inf_le_right _)
  refine eq_of_le_of_card_ge hle ?_
  have h1 := h.card_inf_le₁ h.w₃w₂w₃_L₁
  have h2 := h.card_P_cbc
  rw [h.card_Ub]
  simp only [Nat.reducePow] at h1 h2
  omega

theorem Uc_eq : d.Uc = d.P ⊓ conjR d.P (d.w₀ * d.w₃) ∧ Nat.card d.Uc = 4 := by
  have hle : d.Uc ≤ d.P ⊓ conjR d.P (d.w₀ * d.w₃) := by
    refine le_inf (inf_le_left.trans inf_le_left) ?_
    have e : d.u₁ * (d.w₂ * d.w₃ * d.w₂) = d.w₀ * d.w₃ := by
      rw [← h.word_c]; simp only [YamadaData.u₁, mul_assoc]
    rw [← e, conjR_mul d.P d.u₁]
    exact inf_le_right.trans (conjR_mono inf_le_right _)
  have hup := h.card_w₀_le h.card_P_inf_w₃
  have hlow : 4 ≤ Nat.card d.Uc := by
    have h1 := h.card_inf_le₁ h.w₂w₃w₂_L₁
    have h2 := h.card_P_bcb
    change 4 ≤ Nat.card (d.P₁ ⊓ conjR d.P₁ (d.w₂ * d.w₃ * d.w₂) : Subgroup G)
    simp only [Nat.reducePow] at h1 h2
    omega
  have heq := eq_of_le_of_card_ge hle (by simp only [Nat.reducePow] at hup; omega)
  refine ⟨heq, ?_⟩
  have := card_le_of_le hle
  simp only [Nat.reducePow] at hup
  omega

theorem P₂_aba : d.P₂ ⊓ conjR d.P₂ (d.w₁ * d.w₂ * d.w₁) = ⊥ := by
  have haba : d.w₁ * d.w₂ * d.w₁ ∈ d.H := mul_mem (mul_mem h.w₁_H h.w₂_H) h.w₁_H
  have htP₂ : d.t ∈ normalizer (d.P₂ : Set G) :=
    YamadaEnd.mem_normalizer_inf h.t_P (mem_normalizer_conjR h.t_P (t_comm_of_mem_H h.u₂_H))
  have htT := YamadaEnd.mem_normalizer_inf htP₂ (mem_normalizer_conjR htP₂
    (t_comm_of_mem_H haba))
  refine eq_bot_of_inf_centralizer_eq_bot (h.P₂_facts.2.2.isPGroup.to_le inf_le_left) htT
    h.t_sq ?_
  change d.P₂ ⊓ conjR d.P₂ (d.w₁ * d.w₂ * d.w₁) ⊓ d.H = ⊥
  rw [inf_inf_distrib_right, conjR_inf_H _ haba, h.P₂_inf_H, h.S_aba]

theorem P_aba : d.P ⊓ conjR d.P (d.w₁ * d.w₂ * d.w₁) = d.D₂ := by
  have haba : d.w₁ * d.w₂ * d.w₁ ∈ d.L₂ := mul_mem (mul_mem (h.K₂_le_L₂ h.w₁_K₂)
    (h.K₂_le_L₂ h.w₂_K₂)) (h.K₂_le_L₂ h.w₁_K₂)
  have hD : conjR d.D₂ (d.w₁ * d.w₂ * d.w₁) = d.D₂ :=
    conjR_eq_self (h.N₂_norm (inf_le_left (a := d.N₂) haba))
  refine le_antisymm ?_ (le_inf h.D₂_le_P (hD ▸ conjR_mono h.D₂_le_P _))
  have hle := inf_conjR_le_sup h.P₂_facts.2.1 h.P₂_facts.2.2.le h.L₂_facts.2
    (h.P₂_facts.2.2.le.trans (inf_le_left.trans h.N₂_norm)) (conjR_eq_self (le_normalizer haba))
    hD
  rwa [h.P₂_aba, bot_sup_eq] at hle

theorem D₂_cbc : d.D₂ ⊓ conjR d.D₂ (d.w₃ * d.w₂ * d.w₃) = d.V₁ ∧
    conjR d.Uc (d.w₂ * d.w₁) = d.V₁ := by
  set W := d.D₂ ⊓ conjR d.D₂ (d.w₃ * d.w₂ * d.w₃) with hW
  have hab : d.w₁ * d.w₂ ∈ d.N₂ := inf_le_left (a := d.N₂)
    (mul_mem (h.K₂_le_L₂ h.w₁_K₂) (h.K₂_le_L₂ h.w₂_K₂))
  have hDab : conjR d.D₂ (d.w₁ * d.w₂) = d.D₂ := conjR_eq_self (h.N₂_norm hab)
  have hWab : conjR W (d.w₁ * d.w₂) ≤ d.Uc := by
    rw [(h.Uc_eq).1, hW, conjR_inf, hDab, ← conjR_mul]
    refine inf_le_inf h.D₂_le_P ?_
    rw [← h.P_aba]
    refine (conjR_mono inf_le_right _).trans ?_
    rw [← conjR_mul]
    have e : d.w₁ * d.w₂ * d.w₁ * (d.w₃ * d.w₂ * d.w₃ * (d.w₁ * d.w₂)) = d.w₀ * d.w₃ := by
      rw [← h.word_c']; simp only [mul_assoc]
    rw [e]
  have hcbc : d.w₃ * d.w₂ * d.w₃ ∈ normalizer (d.V₁ : Set G) :=
    centralizer_le_normalizer _ (h.K₁_centralizes (mul_mem (mul_mem h.w₃_K₁ h.w₂_K₁) h.w₃_K₁))
  have hVW : d.V₁ ≤ W := le_inf h.V₁_le_D₂
    ((conjR_eq_self hcbc).symm ▸ conjR_mono h.V₁_le_D₂ _)
  have hcard : Nat.card W ≤ 4 := by
    rw [← card_conjR W (d.w₁ * d.w₂), ← (h.Uc_eq).2]
    exact card_le_of_le hWab
  have hWV : W = d.V₁ := (eq_of_le_of_card_ge hVW (by rw [h.card_V₁]; exact hcard)).symm
  refine ⟨hWV, ?_⟩
  have hWU : conjR W (d.w₁ * d.w₂) = d.Uc := eq_of_le_of_card_ge hWab (by
    rw [(h.Uc_eq).2, card_conjR, hWV, h.card_V₁])
  rw [← hWU, ← conjR_mul, ← hWV]
  have e : d.w₁ * d.w₂ * (d.w₂ * d.w₁) = 1 := by
    rw [mul_assoc, ← mul_assoc d.w₂, h.w₂_sq, one_mul, h.w₁_sq]
  rw [e, conjR_one]

theorem N₁_le_centralizer_V₁ : d.N₁ ≤ centralizer (d.V₁ : Set G) := by
  rw [h.N₁_gen]
  refine sup_le (sup_le ?_ ?_) ?_
  · intro x hx
    rw [mem_centralizer_iff]
    intro v hv
    exact (mem_centralizer_iff.mp (h.V₁_center hv) x hx).symm
  · rw [zpowers_le]; exact h.K₁_centralizes h.w₂_K₁
  · rw [zpowers_le]; exact h.K₁_centralizes h.w₃_K₁

theorem u₁_sq : d.u₁ * d.u₁ = 1 := by
  simp only [YamadaData.u₁, mul_assoc]
  rw [← mul_assoc d.w₁ d.w₁, h.w₁_sq, one_mul, ← mul_assoc d.w₂ d.w₂, h.w₂_sq, one_mul,
    ← mul_assoc d.w₃ d.w₃, h.w₃_sq, one_mul, ← mul_assoc d.w₂ d.w₂, h.w₂_sq, one_mul, h.w₁_sq]

theorem conjR_L₁_u₁ : conjR d.L₁ d.u₁ = d.L₁ := by
  change conjR (d.N₁ ⊓ conjR d.N₁ d.u₁) d.u₁ = d.N₁ ⊓ conjR d.N₁ d.u₁
  rw [conjR_inf, ← conjR_mul, h.u₁_sq, conjR_one, inf_comm]

omit h [Finite G] in
theorem le_centralizer_conjR {X V : Subgroup G} {g : G} (hXV : X ≤ centralizer (V : Set G)) :
    conjR X g ≤ centralizer (conjR V g : Set G) := by
  intro x hx
  rw [mem_centralizer_iff]
  intro v hv
  rw [SetLike.mem_coe, mem_conjR] at hv
  rw [mem_conjR] at hx
  have := mem_centralizer_iff.mp (hXV hx) _ hv
  have e : g * (v * x) * g⁻¹ = g * (x * v) * g⁻¹ := by
    calc g * (v * x) * g⁻¹ = g * v * g⁻¹ * (g * x * g⁻¹) := by group
      _ = g * x * g⁻¹ * (g * v * g⁻¹) := this
      _ = g * (x * v) * g⁻¹ := by group
  simpa using e

theorem commutator_Ya_Yc : ⁅d.Ya, d.Yc⁆ = ⊥ := by
  set a := d.w₁
  set b := d.w₂
  set c := d.w₃
  have hL₁V : d.L₁ ≤ centralizer (d.V₁ : Set G) := inf_le_left.trans h.N₁_le_centralizer_V₁
  have hL₁V' : d.L₁ ≤ centralizer (conjR d.V₁ d.u₁ : Set G) := by
    have := le_centralizer_conjR (g := d.u₁) hL₁V
    rwa [h.conjR_L₁_u₁] at this
  have hcba : c * (b * a) = b * a * d.u₁ := by
    simp only [YamadaData.u₁, a, b, c, mul_assoc]
    rw [← mul_assoc d.w₁ d.w₁, h.w₁_sq, one_mul, ← mul_assoc d.w₂ d.w₂, h.w₂_sq, one_mul]
  have hYc : conjR d.Yc (b * a) = d.V₁ ⊔ conjR d.V₁ d.u₁ := by
    change conjR (d.Uc ⊔ conjR d.Uc c) (b * a) = _
    rw [conjR_sup, h.D₂_cbc.2, ← conjR_mul, hcba, conjR_mul, h.D₂_cbc.2]
  have hYb : d.Yb ≤ d.L₁ := by
    have hUb : d.Ub ≤ d.L₁ := h.P₁_cbc ▸ inf_le_left.trans h.P₁_facts.2.2.le
    have hbL : conjR d.L₁ b = d.L₁ := conjR_eq_self (le_normalizer (h.K₁_le_L₁ h.w₂_K₁))
    exact sup_le hUb (hbL ▸ conjR_mono hUb b)
  have hcomm : ⁅d.Yb, conjR d.Yc (b * a)⁆ = ⊥ := by
    rw [commutator_eq_bot_iff_le_centralizer, hYc]
    intro x hx
    exact mem_centralizer_sup (fun v hv => (mem_centralizer_iff.mp (hL₁V (hYb hx)) v hv))
      (fun v hv => (mem_centralizer_iff.mp (hL₁V' (hYb hx)) v hv))
  have hbaab : b * a * (a * b) = 1 := by
    rw [mul_assoc, ← mul_assoc a a, h.w₁_sq, one_mul, h.w₂_sq]
  have habba : a * b * (b * a) = 1 := by
    rw [mul_assoc, ← mul_assoc b b, h.w₂_sq, one_mul, h.w₁_sq]
  have hUa : conjR d.Ub (a * b) = d.Ua := by
    change conjR (d.P₂ ⊓ conjR d.P₂ (b * a)) (a * b) = d.P₂ ⊓ conjR d.P₂ (a * b)
    rw [conjR_inf, ← conjR_mul, hbaab, conjR_one, inf_comm]
  have hYa : conjR d.Yb (a * b) = d.Ya := by
    change conjR (d.Ub ⊔ conjR d.Ub b) (a * b) = d.Ua ⊔ conjR d.Ua a
    rw [conjR_sup, hUa, ← conjR_mul, ← hUa, ← conjR_mul]
    congr 2
    have := h.braid
    simp only [a, b] at this ⊢
    rw [← mul_assoc, ← this]
  have hYc' : conjR (conjR d.Yc (b * a)) (a * b) = d.Yc := by
    rw [← conjR_mul, hbaab, conjR_one]
  rw [← hYa, ← hYc', ← conjR_commutator, hcomm, conjR, Subgroup.map_bot]

theorem Ua_inf_H : d.Ua ⊓ d.H = d.X₁ := by
  change (d.P₂ ⊓ conjR d.P₂ (d.w₁ * d.w₂)) ⊓ d.H = d.X₁
  rw [inf_inf_distrib_right, conjR_inf_H _ (mul_mem h.w₁_H h.w₂_H), h.P₂_inf_H, h.S_a]

theorem Ub_inf_H : d.Ub ⊓ d.H = d.X₂ := by
  change (d.P₂ ⊓ conjR d.P₂ (d.w₂ * d.w₁)) ⊓ d.H = d.X₂
  rw [inf_inf_distrib_right, conjR_inf_H _ (mul_mem h.w₂_H h.w₁_H), h.P₂_inf_H, h.S_b]

theorem Uc_inf_H : d.Uc ⊓ d.H = d.X₃ := by
  have hg : d.w₂ * d.w₃ * d.w₂ ∈ d.H := mul_mem (mul_mem h.w₂_H h.w₃_H) h.w₂_H
  change (d.P₁ ⊓ conjR d.P₁ (d.w₂ * d.w₃ * d.w₂)) ⊓ d.H = d.X₃
  rw [inf_inf_distrib_right, conjR_inf_H _ hg, h.P₁_inf_H, h.S_c]

theorem X₁_le_Ya : d.X₁ ≤ d.Ya := h.Ua_inf_H ▸ inf_le_left.trans le_sup_left
theorem X₂_le_Yb : d.X₂ ≤ d.Yb := h.Ub_inf_H ▸ inf_le_left.trans le_sup_left
theorem X₃_le_Yc : d.X₃ ≤ d.Yc := h.Uc_inf_H ▸ inf_le_left.trans le_sup_left

theorem w₁_Ya : d.w₁ ∈ d.Ya := by
  have h1 : d.X₁ ⊔ conjR d.X₁ d.w₁ ≤ d.Ya :=
    sup_le h.X₁_le_Ya ((conjR_mono (h.Ua_inf_H ▸ inf_le_left) d.w₁).trans le_sup_right)
  exact h1 h.w₁_gen

theorem w₂_Yb : d.w₂ ∈ d.Yb := by
  have h1 : d.X₂ ⊔ conjR d.X₂ d.w₂ ≤ d.Yb :=
    sup_le h.X₂_le_Yb ((conjR_mono (h.Ub_inf_H ▸ inf_le_left) d.w₂).trans le_sup_right)
  exact h1 h.w₂_gen

theorem w₃_Yc : d.w₃ ∈ d.Yc := by
  have h1 : d.X₃ ⊔ conjR d.X₃ d.w₃ ≤ d.Yc :=
    sup_le h.X₃_le_Yc ((conjR_mono (h.Uc_inf_H ▸ inf_le_left) d.w₃).trans le_sup_right)
  exact h1 h.w₃_gen

theorem L_le_G₀ : d.L ≤ d.G₀ := by
  refine h.L_gen.trans (sup_le (sup_le (sup_le (sup_le (sup_le ?_ ?_) ?_) ?_) ?_) ?_)
  · exact h.X₁_le_Ya.trans (le_sup_left.trans le_sup_left)
  · exact h.X₂_le_Yb.trans (le_sup_right.trans le_sup_left)
  · exact h.X₃_le_Yc.trans le_sup_right
  · rw [zpowers_le]; exact le_sup_left (a := d.Ya ⊔ d.Yb) (le_sup_left (a := d.Ya) h.w₁_Ya)
  · rw [zpowers_le]; exact le_sup_left (a := d.Ya ⊔ d.Yb) (le_sup_right (b := d.Yb) h.w₂_Yb)
  · rw [zpowers_le]; exact le_sup_right (b := d.Yc) h.w₃_Yc

theorem Uc_le_D₂ : d.Uc ≤ d.D₂ := by
  have h1 : d.Uc = conjR d.V₁ (d.w₁ * d.w₂) := by
    rw [← h.D₂_cbc.2, ← conjR_mul]
    have : d.w₂ * d.w₁ * (d.w₁ * d.w₂) = 1 := by
      rw [mul_assoc, ← mul_assoc d.w₁ d.w₁, h.w₁_sq, one_mul, h.w₂_sq]
    rw [this, conjR_one]
  have hab : d.w₁ * d.w₂ ∈ d.N₂ := inf_le_left (a := d.N₂)
    (mul_mem (h.K₂_le_L₂ h.w₁_K₂) (h.K₂_le_L₂ h.w₂_K₂))
  rw [h1, ← conjR_eq_self (h.N₂_norm hab)]
  exact conjR_mono h.V₁_le_D₂ _

omit h [Finite G] in
theorem mem_normalizer_sup {A B : Subgroup G} {x : G} (hA : x ∈ normalizer (A : Set G))
    (hB : x ∈ normalizer (B : Set G)) : x ∈ normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  apply mem_normalizer_of_map_conj_eq
  rw [Subgroup.map_sup, map_conj_eq_of_mem_normalizer hA, map_conj_eq_of_mem_normalizer hB]

theorem t_P₂ : d.t ∈ normalizer (d.P₂ : Set G) :=
  YamadaEnd.mem_normalizer_inf h.t_P (mem_normalizer_conjR h.t_P (t_comm_of_mem_H h.u₂_H))

theorem P₂_decomp {M : Subgroup G} (hn : d.L₂ ≤ normalizer (M : Set G))
    (hn' : d.L₂ ≤ normalizer (conjR M d.t : Set G)) (hsup : M ⊔ conjR M d.t = d.L₂)
    (hc : ⁅M, conjR M d.t⁆ = ⊥) (hodd : Odd (Nat.card (M ⊓ conjR M d.t : Subgroup G)))
    {g : G} (hgL : g ∈ d.L₂) :
    d.P₂ ⊓ conjR d.P₂ g = ((d.P₂ ⊓ conjR d.P₂ g) ⊓ M) ⊔ ((d.P₂ ⊓ conjR d.P₂ g) ⊓ conjR M d.t) := by
  set M' := conjR M d.t with hM'
  have hsyl : IsSylowOf 2 d.P₂ (M ⊔ M') := hsup.symm ▸ h.P₂_facts.2.2
  have hP₂ := sylow_eq_sup hc hodd hsyl (hsup.symm ▸ hn) (hsup.symm ▸ hn')
  have hgM : conjR M g = M := conjR_eq_self (hn hgL)
  have hgM' : conjR M' g = M' := conjR_eq_self (hn' hgL)
  have hP₂2 : IsPGroup 2 d.P₂ := h.P₂_facts.2.2.isPGroup
  have hdec : d.P₂ ⊓ conjR d.P₂ g = ((d.P₂ ⊓ M) ⊓ conjR (d.P₂ ⊓ M) g) ⊔
      ((d.P₂ ⊓ M') ⊓ conjR (d.P₂ ⊓ M') g) := by
    conv_lhs => rw [hP₂, conjR_sup]
    exact sup_inf_sup hc hodd inf_le_right
      ((conjR_mono (inf_le_right : d.P₂ ⊓ M ≤ M) g).trans hgM.le) inf_le_right
      ((conjR_mono (inf_le_right : d.P₂ ⊓ M' ≤ M') g).trans hgM'.le) (hP₂2.to_le inf_le_left)
      ((hP₂2.to_le inf_le_left).map _)
  refine le_antisymm ?_ (sup_le inf_le_left inf_le_left)
  conv_lhs => rw [hdec]
  exact sup_le_sup (le_inf (hdec ▸ le_sup_left) (inf_le_left.trans inf_le_right))
    (le_inf (hdec ▸ le_sup_right) (inf_le_left.trans inf_le_right))

omit h [Finite G] in
theorem commutator_sup_le {W Z : Subgroup G} (hWZ : ∀ w ∈ W, ∀ z ∈ Z, w * z = z * w)
    (hZZ : ∀ z ∈ Z, ∀ z' ∈ Z, z * z' = z' * z) : ⁅W ⊔ Z, W ⊔ Z⁆ ≤ W := by
  have hZN : Z ≤ normalizer (W : Set G) := by
    intro z hz
    refine centralizer_le_normalizer _ ?_
    rw [mem_centralizer_iff]
    intro w hw
    exact hWZ w hw z hz
  have hmul : (↑(W ⊔ Z) : Set G) = (W : Set G) * (Z : Set G) := by
    rw [sup_comm, coe_mul_of_left_le_normalizer_right Z W hZN]
    ext x
    constructor
    · rintro ⟨z, hz, w, hw, rfl⟩
      exact ⟨w, hw, z, hz, hWZ w hw z hz⟩
    · rintro ⟨w, hw, z, hz, rfl⟩
      exact ⟨z, hz, w, hw, (hWZ w hw z hz).symm⟩
  rw [commutator_le]
  intro x hx y hy
  rw [← SetLike.mem_coe, hmul] at hx hy
  obtain ⟨w, hw, z, hz, rfl⟩ := hx
  obtain ⟨w', hw', z', hz', rfl⟩ := hy
  have h1 : z * w' = w' * z := (hWZ w' hw' z hz).symm
  have h2 : z * z' = z' * z := hZZ z hz z' hz'
  have h3 : z' * w⁻¹ = w⁻¹ * z' := (hWZ _ (W.inv_mem hw) z' hz').symm
  have e : ⁅w * z, w' * z'⁆ = ⁅w, w'⁆ := by
    rw [commutatorElement_def, commutatorElement_def]
    calc w * z * (w' * z') * (w * z)⁻¹ * (w' * z')⁻¹
        = w * (z * w') * z' * z⁻¹ * w⁻¹ * z'⁻¹ * w'⁻¹ := by group
      _ = w * (w' * z) * z' * z⁻¹ * w⁻¹ * z'⁻¹ * w'⁻¹ := by rw [h1]
      _ = w * w' * (z * z') * z⁻¹ * w⁻¹ * z'⁻¹ * w'⁻¹ := by group
      _ = w * w' * (z' * z) * z⁻¹ * w⁻¹ * z'⁻¹ * w'⁻¹ := by rw [h2]
      _ = w * w' * (z' * w⁻¹) * z'⁻¹ * w'⁻¹ := by group
      _ = w * w' * (w⁻¹ * z') * z'⁻¹ * w'⁻¹ := by rw [h3]
      _ = w * w' * w⁻¹ * w'⁻¹ := by group
  beta_reduce
  rw [e]
  exact commutator_mem_commutator hw hw' |> fun h' => commutator_le_self W h'

theorem t_Ua : d.t ∈ normalizer (d.Ua : Set G) :=
  YamadaEnd.mem_normalizer_inf h.t_P₂ (mem_normalizer_conjR h.t_P₂
    (t_comm_of_mem_H (mul_mem h.w₁_H h.w₂_H)))

theorem t_Ub : d.t ∈ normalizer (d.Ub : Set G) :=
  YamadaEnd.mem_normalizer_inf h.t_P₂ (mem_normalizer_conjR h.t_P₂
    (t_comm_of_mem_H (mul_mem h.w₂_H h.w₁_H)))

theorem t_Ya : d.t ∈ normalizer (d.Ya : Set G) :=
  mem_normalizer_sup h.t_Ua (mem_normalizer_conjR h.t_Ua (t_comm_of_mem_H h.w₁_H))

theorem t_Yb : d.t ∈ normalizer (d.Yb : Set G) :=
  mem_normalizer_sup h.t_Ub (mem_normalizer_conjR h.t_Ub (t_comm_of_mem_H h.w₂_H))

theorem Ya_Yb_eq : d.Ya ⊔ d.Yb = d.L₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨M, hn, hn', hsup, hc, hodd, θ, hθ, -⟩ := h.L₂_components
  set M' := conjR M d.t with hM'
  have haL : d.w₁ ∈ d.L₂ := h.K₂_le_L₂ h.w₁_K₂
  have hbL : d.w₂ ∈ d.L₂ := h.K₂_le_L₂ h.w₂_K₂
  have hUaL : d.Ua ≤ d.L₂ := inf_le_left.trans h.P₂_facts.2.2.le
  have hUbL : d.Ub ≤ d.L₂ := inf_le_left.trans h.P₂_facts.2.2.le
  have hconjL : ∀ x ∈ d.L₂, conjR d.L₂ x = d.L₂ := fun x hx => conjR_eq_self (le_normalizer hx)
  have hle : d.Ya ⊔ d.Yb ≤ d.L₂ :=
    sup_le (sup_le hUaL (hconjL _ haL ▸ conjR_mono hUaL _))
      (sup_le hUbL (hconjL _ hbL ▸ conjR_mono hUbL _))
  refine le_antisymm hle ?_
  have hMC : M ≤ centralizer (M' : Set G) := (commutator_eq_bot_iff_le_centralizer).mp hc
  have hMa : conjR M d.w₁ = M := conjR_eq_self (hn haL)
  have hMb : conjR M d.w₂ = M := conjR_eq_self (hn hbL)
  have hM'a : conjR M' d.w₁ = M' := conjR_eq_self (hn' haL)
  have hM'b : conjR M' d.w₂ = M' := conjR_eq_self (hn' hbL)
  have hUa := h.P₂_decomp hn hn' hsup hc hodd (mul_mem haL hbL)
  have hUb := h.P₂_decomp hn hn' hsup hc hodd (mul_mem hbL haL)
  change d.Ua = (d.Ua ⊓ M) ⊔ (d.Ua ⊓ M') at hUa
  change d.Ub = (d.Ub ⊓ M) ⊔ (d.Ub ⊓ M') at hUb
  set Wa := (d.Ua ⊓ M) ⊔ conjR (d.Ua ⊓ M) d.w₁ with hWa
  set Wb := (d.Ub ⊓ M) ⊔ conjR (d.Ub ⊓ M) d.w₂ with hWb
  have hWaM : Wa ≤ M :=
    sup_le inf_le_right ((conjR_mono (inf_le_right : d.Ua ⊓ M ≤ M) _).trans hMa.le)
  have hWbM : Wb ≤ M :=
    sup_le inf_le_right ((conjR_mono (inf_le_right : d.Ub ⊓ M ≤ M) _).trans hMb.le)
  have hWaY : Wa ≤ d.Ya := sup_le (inf_le_left.trans le_sup_left)
    ((conjR_mono inf_le_left _).trans le_sup_right)
  have hWbY : Wb ≤ d.Yb := sup_le (inf_le_left.trans le_sup_left)
    ((conjR_mono inf_le_left _).trans le_sup_right)
  have hWaa : conjR Wa d.w₁ = Wa := by
    rw [hWa, conjR_sup, ← conjR_mul, h.w₁_sq, conjR_one, sup_comm]
  have hWbb : conjR Wb d.w₂ = Wb := by
    rw [hWb, conjR_sup, ← conjR_mul, h.w₂_sq, conjR_one, sup_comm]
  have hX₁ : d.X₁ ≤ Wa ⊔ M' := by
    rw [← h.Ua_inf_H]
    refine inf_le_left.trans ?_
    rw [hUa]
    exact sup_le_sup le_sup_left inf_le_right
  have hX₂ : d.X₂ ≤ Wb ⊔ M' := by
    rw [← h.Ub_inf_H]
    refine inf_le_left.trans ?_
    rw [hUb]
    exact sup_le_sup le_sup_left inf_le_right
  have ha : d.w₁ ∈ Wa ⊔ M' := by
    have : d.X₁ ⊔ conjR d.X₁ d.w₁ ≤ Wa ⊔ M' := by
      refine sup_le hX₁ ?_
      have := conjR_mono hX₁ d.w₁
      rwa [conjR_sup, hWaa, hM'a] at this
    exact this h.w₁_gen
  have hb : d.w₂ ∈ Wb ⊔ M' := by
    have : d.X₂ ⊔ conjR d.X₂ d.w₂ ≤ Wb ⊔ M' := by
      refine sup_le hX₂ ?_
      have := conjR_mono hX₂ d.w₂
      rwa [conjR_sup, hWbb, hM'b] at this
    exact this h.w₂_gen
  set W := Wa ⊔ Wb with hW
  have hWM : W ≤ M := sup_le hWaM hWbM
  have hK₂ : d.K₂ ≤ W ⊔ M' := by
    rw [h.K₂_gen]
    refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
    · exact hX₁.trans (sup_le_sup_right le_sup_left _)
    · exact hX₂.trans (sup_le_sup_right le_sup_right _)
    · rw [zpowers_le]; exact (sup_le_sup_right le_sup_left M' : Wa ⊔ M' ≤ W ⊔ M') ha
    · rw [zpowers_le]; exact (sup_le_sup_right le_sup_right M' : Wb ⊔ M' ≤ W ⊔ M') hb
  have hML : M ≤ d.L₂ := hsup ▸ le_sup_left
  have hM'L : M' ≤ d.L₂ := hsup ▸ le_sup_right
  have hconjM : ∀ m ∈ M, d.t * m * d.t⁻¹ ∈ M' := fun m hm => by
    rw [hM', mem_conjR, h.t_inv]
    have : d.t * (d.t * m * d.t) * d.t = m := by
      rw [show d.t * (d.t * m * d.t) * d.t = (d.t * d.t) * m * (d.t * d.t) by group, h.t_sq,
        one_mul, mul_one]
    rw [this]
    exact hm
  set Z := M ⊓ M' with hZ
  have hMWZ : M ≤ W ⊔ Z := by
    intro m hm
    set x := m * (d.t * m * d.t⁻¹) with hx
    have hxH : x ∈ d.H := by
      rw [YamadaData.H, mem_centralizer_singleton_iff]
      have hcomm : d.t * m * d.t⁻¹ * m = m * (d.t * m * d.t⁻¹) :=
        mem_centralizer_iff.mp (hMC hm) _ (hconjM m hm)
      calc x * d.t = (d.t * m * d.t⁻¹ * m) * d.t := by rw [hcomm]
        _ = d.t * x := by rw [hx, h.t_inv]; group
    have hxL : x ∈ d.L₂ := mul_mem (hML hm) (hM'L (hconjM m hm))
    have hxK : x ∈ d.K₂ := h.L₂_facts.1 ▸ ⟨hxL, hxH⟩
    have hxWM : x ∈ (W : Set G) * (M' : Set G) := by
      rw [← coe_mul_of_left_le_normalizer_right W M' (hWM.trans (hML.trans hn'))]
      exact hK₂ hxK
    obtain ⟨w, hw, m', hm', hwm⟩ := hxWM
    beta_reduce at hwm
    have hz : w⁻¹ * m ∈ Z := by
      refine ⟨M.mul_mem (M.inv_mem (hWM hw)) hm, ?_⟩
      have : w⁻¹ * m = m' * (d.t * m * d.t⁻¹)⁻¹ := by
        calc w⁻¹ * m = w⁻¹ * x * (d.t * m * d.t⁻¹)⁻¹ := by rw [hx]; group
          _ = w⁻¹ * (w * m') * (d.t * m * d.t⁻¹)⁻¹ := by rw [← hwm]
          _ = m' * (d.t * m * d.t⁻¹)⁻¹ := by group
      rw [this]
      exact M'.mul_mem hm' (M'.inv_mem (hconjM m hm))
    have : m = w * (w⁻¹ * m) := by group
    rw [this]
    exact mul_mem (mem_sup_left hw) (mem_sup_right hz)
  have hMperf : ⁅M, M⁆ = M := by
    have : Group.IsPerfect SL(3, F) := CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le
      (by norm_num)
    have : Group.IsPerfect M := Group.IsPerfect.ofSurjective hθ
    exact YamadaEnd.commutator_eq_self_of_isPerfect this
  have hWZcomm : ∀ w ∈ W, ∀ z ∈ Z, w * z = z * w := fun w hw z hz =>
    (mem_centralizer_iff.mp (hMC (hWM hw)) z hz.2).symm
  have hZZ : ∀ z ∈ Z, ∀ z' ∈ Z, z * z' = z' * z := fun z hz z' hz' =>
    (mem_centralizer_iff.mp (hMC hz.1) z' hz'.2).symm
  have hMW : M ≤ W := by
    have hMeq : M = W ⊔ Z := le_antisymm hMWZ (sup_le hWM inf_le_left)
    rw [← hMperf]
    conv_lhs => rw [hMeq]
    exact commutator_sup_le hWZcomm hZZ
  have hMY : M ≤ d.Ya ⊔ d.Yb := hMW.trans (sup_le_sup hWaY hWbY)
  have htY : d.t ∈ normalizer ((d.Ya ⊔ d.Yb : Subgroup G) : Set G) :=
    mem_normalizer_sup h.t_Ya h.t_Yb
  have hM'Y : M' ≤ d.Ya ⊔ d.Yb := by
    rw [hM', ← conjR_eq_self htY]
    exact conjR_mono hMY _
  rw [← hsup]
  exact sup_le hMY hM'Y

theorem D₂_le_G₀ : d.D₂ ≤ d.G₀ := by
  have hLG := h.L_le_G₀
  have hA₂ : d.A₂ ≤ d.D₂ ⊓ d.G₀ := le_inf (h.D₂_H ▸ inf_le_left)
    ((h.A₂_le.trans h.sylow.le).trans hLG)
  have hK₂N : d.K₂ ≤ normalizer ((d.D₂ ⊓ d.G₀ : Subgroup G) : Set G) := fun k hk =>
    YamadaEnd.mem_normalizer_inf (h.N₂_norm (h.K₂_le_N₂ hk)) (le_normalizer (hLG (h.K₂_le hk)))
  rcases h.D₂_irred _ hA₂ inf_le_left hK₂N with heq | heq
  · exfalso
    have hUc : d.Uc ≤ d.D₂ ⊓ d.G₀ := le_inf h.Uc_le_D₂ (le_sup_left.trans le_sup_right)
    rw [heq] at hUc
    have hUcH : d.Uc ≤ d.H := hUc.trans (h.D₂_H ▸ inf_le_right)
    have : d.Uc ⊓ d.H = d.Uc := inf_of_le_left hUcH
    rw [h.Uc_inf_H] at this
    have hc := congrArg (fun X : Subgroup G => Nat.card X) this
    simp only [h.card_X₃, (h.Uc_eq).2] at hc
    omega
  · exact heq ▸ inf_le_right

theorem G₀_eq : d.G₀ = d.N₁ ⊔ d.N₂ := by
  have hLG := h.L_le_G₀
  have hN₂ : d.N₂ ≤ d.G₀ := by
    rw [h.N₂_eq, ← h.Ya_Yb_eq]
    exact sup_le le_sup_left h.D₂_le_G₀
  have hP : d.P ≤ d.G₀ := h.P_le₂.trans hN₂
  have hN₁ : d.N₁ ≤ d.G₀ := by
    rw [h.N₁_gen]
    refine sup_le (sup_le hP ?_) ?_
    · rw [zpowers_le]; exact hLG h.w₂_mem
    · rw [zpowers_le]; exact hLG h.w₃_mem
  refine le_antisymm ?_ (sup_le hN₁ hN₂)
  refine sup_le (sup_le ?_ ?_) ?_
  · exact le_sup_left.trans (h.Ya_Yb_eq.le.trans (inf_le_left.trans le_sup_right))
  · exact le_sup_right.trans (h.Ya_Yb_eq.le.trans (inf_le_left.trans le_sup_right))
  · have hUc : d.Uc ≤ d.N₁ := (inf_le_left.trans h.P₁_facts.2.2.le).trans inf_le_left
    have hcN : conjR d.N₁ d.w₃ = d.N₁ := conjR_eq_self (le_normalizer (h.K₁_le_N₁ h.w₃_K₁))
    exact (sup_le hUc (hcN ▸ conjR_mono hUc _)).trans le_sup_left

omit h [Finite G] in
theorem zpowers_eq_of_mem {t z : G} (ht : orderOf t = 2) (hz : z ∈ zpowers t) (hz1 : z ≠ 1) :
    zpowers z = zpowers t := by
  have hle : zpowers z ≤ zpowers t := by rw [zpowers_le]; exact hz
  have : Finite (zpowers t) := by
    have : 0 < orderOf t := by rw [ht]; norm_num
    exact Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers]; omega)
  refine eq_of_le_of_card_ge hle ?_
  rw [Nat.card_zpowers, Nat.card_zpowers, ht]
  have h1 : orderOf z ∣ 2 := ht ▸ (orderOf_dvd_of_mem_zpowers hz)
  have h2 : orderOf z ≠ 1 := fun h' => hz1 (orderOf_eq_one_iff.mp h')
  rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h3 | h3
  · exact absurd h3 h2
  · omega

theorem eq_zpowers_of_isPGroup {Q : Subgroup G} (hQL : Q ≤ centralizer (d.L : Set G))
    (hQ2 : IsPGroup 2 Q) (htQ : d.t ∈ Q) : Q = zpowers d.t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht1 : d.t ≠ 1 := fun h1 => by
    have := h.order_t
    rw [h1, orderOf_one] at this
    omega
  have : Nontrivial Q := ⟨⟨⟨d.t, htQ⟩, 1, fun h' => ht1 (congrArg Subtype.val h')⟩⟩
  have := hQ2.center_nontrivial
  obtain ⟨z, hz1⟩ := exists_ne (1 : center Q)
  have hzt : ((z : Q) : G) ∈ zpowers d.t := by
    rw [← h.kernel]
    refine ⟨hQL (z : Q).2, ?_⟩
    change ((z : Q) : G) ∈ centralizer ({d.t} : Set G)
    rw [mem_centralizer_singleton_iff]
    have := (mem_center_iff.mp z.2) ⟨d.t, htQ⟩
    exact (congrArg Subtype.val this).symm
  have hz1' : ((z : Q) : G) ≠ 1 := fun h' => hz1 (Subtype.ext (Subtype.ext h'))
  have heq := zpowers_eq_of_mem h.order_t hzt hz1'
  have htz : d.t ∈ zpowers ((z : Q) : G) := heq ▸ mem_zpowers d.t
  have hQH : Q ≤ d.H := by
    intro q hq
    rw [YamadaData.H, mem_centralizer_singleton_iff]
    obtain ⟨k, hk⟩ := htz
    rw [← hk]
    have hzq : ((z : Q) : G) * q = q * (z : Q) :=
      (congrArg Subtype.val ((mem_center_iff.mp z.2) ⟨q, hq⟩)).symm
    exact ((Commute.zpow_left hzq k).eq).symm
  refine le_antisymm ?_ (by rw [zpowers_le]; exact htQ)
  rw [← h.kernel]
  exact le_inf hQL hQH

theorem t_G₀ : d.t ∈ normalizer (d.G₀ : Set G) := by
  rw [h.G₀_eq]
  exact mem_normalizer_sup h.t_N₁ h.t_N₂

theorem odd_centralizer_G₀ : Odd (Nat.card (centralizer (d.G₀ : Set G))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer (d.G₀ : Set G) with hC
  have hCL : C ≤ centralizer (d.L : Set G) := centralizer_le h.L_le_G₀
  have htC : d.t ∈ normalizer (C : Set G) := by
    apply mem_normalizer_of_map_conj_eq
    rw [hC, ← centralizer_map_conj, map_conj_eq_of_mem_normalizer h.t_G₀]
  have htnot : d.t ∉ C := by
    intro ht
    have hUcH : d.Uc ≤ d.H := fun x hx => by
      rw [YamadaData.H, mem_centralizer_singleton_iff]
      exact (mem_centralizer_iff.mp ht x
        (((le_sup_left : d.Uc ≤ d.Yc).trans (le_sup_right : d.Yc ≤ d.G₀)) hx))
    have : d.Uc ⊓ d.H = d.Uc := inf_of_le_left hUcH
    rw [h.Uc_inf_H] at this
    have hc := congrArg (fun X : Subgroup G => Nat.card X) this
    simp only [h.card_X₃, (h.Uc_eq).2] at hc
    omega
  have hz : IsPGroup 2 (zpowers d.t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h.order_t, pow_one])
  obtain ⟨T, hT, htT⟩ := exists_isSylowOf_ge (le_sup_right : zpowers d.t ≤ C ⊔ zpowers d.t) hz
  have hTL : T ≤ centralizer (d.L : Set G) :=
    hT.le.trans (sup_le hCL (by rw [zpowers_le]; exact h.t_mem))
  have hTeq := h.eq_zpowers_of_isPGroup hTL hT.isPGroup (htT (mem_zpowers _))
  have hN : C ⊔ zpowers d.t ≤ normalizer (C : Set G) :=
    sup_le le_normalizer (by rw [zpowers_le]; exact htC)
  have hT₀ : IsSylowOf 2 (T ⊓ C) C := hT.inf_of_le_normalizer le_sup_left hN
  have hbot : T ⊓ C = ⊥ := by
    rw [eq_bot_iff, hTeq]
    rintro x ⟨hxt, hxC⟩
    by_contra hx1
    have h1 : d.t ∈ zpowers x := by
      rw [zpowers_eq_of_mem h.order_t hxt hx1]; exact mem_zpowers _
    exact htnot ((zpowers_le.mpr hxC) h1)
  rw [hbot] at hT₀
  have := (isSylowOf_iff.mp hT₀).2.2
  rw [Subgroup.relIndex_bot_left] at this
  exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp this)

end YamadaSection4

end CFSG.EvenSmallLie.UnitarySix.YamadaEnd
