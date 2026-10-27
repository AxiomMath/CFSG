module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6SKY
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6SY
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6SOrd6
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6SNZ
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6STr
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6Act6
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6Idx
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6Count

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private theorem y6_mem_C_iff (c : Ctx6 G L) (hH : F33Hyp c.s c.e) {x : G} (hx : x ∈ y6X c) :
    x ∈ y6C c ↔ c.s.t⁻¹ * (x * c.s.t * x⁻¹) ∈ V1 c.e := by
  have hxV : x ∈ normalizer (V1 c.e : Set G) := (Subgroup.mem_inf.mp hx).2
  rw [← y6_mem_NC0_iff (c.y6cfg hH) hxV]
  exact ⟨fun h => (Subgroup.mem_inf.mp h).2, fun h => Subgroup.mem_inf.mpr ⟨hx, h⟩⟩

private theorem y6_mem_Y_iff (c : Ctx6 G L) (hH : F33Hyp c.s c.e) {x : G} (hx : x ∈ y6X c) :
    x ∈ y6Y c ↔ (x * c.s.t * x⁻¹ = c.s.t ∨ x * c.s.t * x⁻¹ = c.s.fr.z * c.s.t) :=
  y6_mem_NAt_iff (c.y6cfg hH) (Subgroup.mem_inf.mp hx).1 (Subgroup.mem_inf.mp hx).2

private theorem y6_card_NC0_le (c : Ctx6 G L) (hH : F33Hyp c.s c.e) :
    Nat.card ↥(normalizer (C0 c.e : Set G)) ≤ 2 * Nat.card ↥(y6Y c) := by
  have hYN : y6Y c ≤ normalizer (C0 c.e : Set G) := s6_Y_le_NC0 c hH
  have hiff : ∀ x ∈ normalizer (C0 c.e : Set G),
      x ∈ y6Y c ↔ (x * c.s.t * x⁻¹ = c.s.t ∨ x * c.s.t * x⁻¹ = c.s.fr.z * c.s.t) := by
    intro x hx
    constructor
    · intro hxY
      exact (y6_mem_Y_iff c hH (s6_Y_le_X c hH hxY)).mp hxY
    · intro hxt
      exact y6_NZ_le_Y c hH (s6_NC0_le_NV c hH hx) hxt
  exact y6_card_le_two_mul hYN
    (y6_three_way (c.y6cfg hH) (s6_NC0_le_NV c hH) le_rfl hiff)

theorem y6_main (c : Ctx6 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5) :
    ∃ ψ : ↥(y6X c) →* Equiv.Perm (Fin 6),
      ψ.ker = (y6K c).subgroupOf (y6X c) ∧ y6K c = C1 c.e ∧
      Nat.card ↥(y6C c) = 2 * Nat.card ↥(y6Y c) ∧
      Nat.card ↥(y6X c) = 10 * Nat.card ↥(y6C c) ∧
      alternatingGroup (Fin 6) ≤ ψ.range ∧
      (c.s.R = c.s.T → Nat.card ↥ψ.range = 360) ∧
      (c.s.R ≠ c.s.T → Nat.card ↥ψ.range = 720) := by
  have cfg := c.y6cfg hH
  have hX1 : y6X c ≤ normalizer ((c.s.fr.A ⊔ C0 c.e : Subgroup G) : Set G) := inf_le_left
  have hX2 : y6X c ≤ normalizer (V1 c.e : Set G) := inf_le_right
  obtain ⟨ψ, hker⟩ := y6_psi6 cfg hX1 hX2
  have hker' : ψ.ker = (y6K c).subgroupOf (y6X c) := hker
  have hXC : Nat.card ↥(y6X c) = 10 * Nat.card ↥(y6C c) :=
    y6_orbit10 cfg inf_le_left hX1 hX2 (fun x hx => y6_mem_C_iff c hH hx) (y6_trans_Up c hH hF)
  have hYC : y6Y c ≤ y6C c := le_inf (s6_Y_le_X c hH) (s6_Y_le_NC0 c hH)
  have hCY : Nat.card ↥(y6C c) ≤ 2 * Nat.card ↥(y6Y c) :=
    y6_card_le_two_mul hYC (y6_three_way cfg (inf_le_left.trans inf_le_right) inf_le_right
      (fun x hx => y6_mem_Y_iff c hH (Subgroup.mem_inf.mp hx).1))
  have hKX : y6K c ≤ y6X c := fun x hx => Subgroup.mem_inf.mpr ⟨hx.1, hx.2.1⟩
  have hKC : y6K c ≤ y6C c := le_inf hKX (y6_K_le_NC0 cfg)
  have hC1K : C1 c.e ≤ y6K c := y6_C1_le_K cfg
  have hC1Y : C1 c.e ≤ y6Y c := y6_C1_le_NAt cfg
  have hKY : y6K c ⊓ y6Y c = C1 c.e := y6_K_inf_Y c hH
  have hYm := y6_card_Y_m c.toCtx5 hH
  by_cases hRT : c.s.R = c.s.T
  · have hY18 : Nat.card ↥(y6Y c) = 18 * Nat.card ↥(C1 c.e) := hYm.1 hRT
    obtain ⟨hCeq, hKeq, hA6, hcard⟩ :=
      y6_count (y6X c) (y6C c) (y6Y c) (y6K c) (C1 c.e) ψ hker' inf_le_left hYC hKC hC1K hC1Y
        hKY hXC hCY (m := 18) (Or.inl rfl) hY18 (fun h => absurd h (by norm_num))
    exact ⟨ψ, hker', hKeq, hCeq, hXC, hA6, fun _ => by rw [hcard], fun h => absurd hRT h⟩
  · have hY36 : Nat.card ↥(y6Y c) = 36 * Nat.card ↥(C1 c.e) := hYm.2 hRT
    obtain ⟨y, hyY, hy6, hy2, hy3⟩ := y6_exists_order6 c.toCtx5 hH hRT
    have h6 : (36 : ℕ) = 36 → ∃ x : ↥(y6X c), (x : G) ∈ y6Y c ∧ orderOf (ψ x) = 6 := fun _ =>
      y6_order_six ψ hker' hKY (s6_Y_le_X c hH) hyY hy6 hy2 hy3
    obtain ⟨hCeq, hKeq, hA6, hcard⟩ :=
      y6_count (y6X c) (y6C c) (y6Y c) (y6K c) (C1 c.e) ψ hker' inf_le_left hYC hKC hC1K hC1Y
        hKY hXC hCY (m := 36) (Or.inr rfl) hY36 h6
    exact ⟨ψ, hker', hKeq, hCeq, hXC, hA6, fun h => absurd h hRT, fun _ => by rw [hcard]⟩

theorem y6_card_X (c : Ctx6 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5) :
    Nat.card ↥(y6X c) = 360 * Nat.card ↥c.s.T := by
  obtain ⟨ψ, -, -, hCY, hXC, -⟩ := y6_main c hH hF
  have hY : Nat.card ↥(y6Y c) = 2 * Nat.card ↥(normIn c.s.H c.s.fr.A) := y6_card_Y c.toCtx5 hH
  have hN : Nat.card ↥(normIn c.s.H c.s.fr.A) = 9 * Nat.card ↥c.s.T := y6_card_NHA hH
  rw [hXC, hCY, hY, hN]
  ring

theorem y6_NC0_eq (c : Ctx6 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5) :
    normalizer (C0 c.e : Set G) = y6C c := by
  obtain ⟨ψ, -, -, hCY, -⟩ := y6_main c hH hF
  have hle : y6C c ≤ normalizer (C0 c.e : Set G) := inf_le_right
  have hcard : Nat.card ↥(normalizer (C0 c.e : Set G)) ≤ Nat.card ↥(y6C c) := by
    rw [hCY]
    exact y6_card_NC0_le c hH
  exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm

private theorem y6_NC1_cent_le_Y (c : Ctx6 G L) (hH : F33Hyp c.s c.e) {x : G}
    (hx1 : x ∈ normalizer (C1 c.e : Set G)) (hxt : x ∈ centralizer ({c.s.t} : Set G)) :
    x ∈ y6Y c := by
  have hxt' : x * c.s.t * x⁻¹ = c.s.t := by
    have h := Subgroup.mem_centralizer_iff.mp hxt c.s.t (Set.mem_singleton _)
    calc x * c.s.t * x⁻¹ = (c.s.t * x) * x⁻¹ := by rw [h]
      _ = c.s.t := by group
  exact y6_mem_NAt_of_cent (c.y6cfg hH) hx1 hxt'

theorem y6_NC1_eq (c : Ctx6 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5) :
    normalizer (C1 c.e : Set G) = y6X c := by
  obtain ⟨ψ, -, -, hCY, hXC, -⟩ := y6_main c hH hF
  have cfg := c.y6cfg hH
  have hH0 : normalizer (C1 c.e : Set G) ⊓ centralizer ({c.s.t} : Set G) =
      normIn c.s.H c.s.fr.A := by
    refine le_antisymm ?_ ?_
    · intro x hx
      obtain ⟨hx1, hxt⟩ := Subgroup.mem_inf.mp hx
      have hxY := y6_NC1_cent_le_Y c hH hx1 hxt
      exact Subgroup.mem_inf.mpr ⟨hxt, s6_Y_le_NA c hH hxY⟩
    · intro x hx
      obtain ⟨hxH, hxA⟩ := Subgroup.mem_inf.mp hx
      have hxY : x ∈ y6Y c := s6_NHA_le_Y c hH hx
      exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp (s6_Y_le_X c hH hxY)).1, hxH⟩
  have hY : Nat.card ↥(y6Y c) = 2 * Nat.card ↥(normIn c.s.H c.s.fr.A) := y6_card_Y c.toCtx5 hH
  have hX40 : Nat.card ↥(y6X c) =
      40 * Nat.card ↥(normalizer (C1 c.e : Set G) ⊓ centralizer ({c.s.t} : Set G)) := by
    rw [hH0, hXC, hCY, hY]
    ring
  refine (y6_normal_eq (N := normalizer (C1 c.e : Set G)) (X := y6X c)
    (H0 := normalizer (C1 c.e : Set G) ⊓ centralizer ({c.s.t} : Set G)) (t := c.s.t)
    (S := {w : G | w ∈ c.s.fr.A ⊔ C0 c.e ∧ w ∉ c.s.fr.A ∧ w ^ 2 = 1})
    inf_le_left ?_ rfl hX40 ?_ (y6_card_invol cfg)).symm
  · intro x hx
    obtain ⟨hx1, hxt⟩ := Subgroup.mem_inf.mp hx
    exact s6_Y_le_X c hH (y6_NC1_cent_le_Y c hH hx1 hxt)
  · intro n hn
    have htC1 : c.s.t ∈ c.s.fr.A ⊔ C0 c.e := Subgroup.mem_sup_right (y6_t_mem_C0 cfg)
    refine ⟨(Subgroup.mem_normalizer_iff.mp hn c.s.t).mp htC1, ?_, ?_⟩
    · intro hA
      exact hH.h31.2.2.1 n ((s3_A_le_L c.s) hA)
    · have ht2 : c.s.t ^ 2 = 1 := by
        have h := pow_orderOf_eq_one c.s.t
        rwa [c.s.t_order] at h
      calc (n * c.s.t * n⁻¹) ^ 2 = n * c.s.t ^ 2 * n⁻¹ := conj_pow
        _ = 1 := by rw [ht2]; group

end CFSG.OddStandard.HigherRank.YamadaG23
