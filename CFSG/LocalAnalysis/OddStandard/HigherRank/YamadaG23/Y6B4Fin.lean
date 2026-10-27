module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6B4K
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6F64
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6B4F2
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6B4F5

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y6b_le_of_index_two {P T N : Subgroup G} {a : G} (hTP : T ≤ P)
    (hcard : Nat.card ↥P = 2 * Nat.card ↥T) (haP : a ∈ P) (haT : a ∉ T) (hTN : T ≤ N)
    (haN : a ∈ N) : P ≤ N := by
  let Q : Subgroup G := T ⊔ zpowers a
  have haQ : a ∈ Q := Subgroup.mem_sup_right (Subgroup.mem_zpowers a)
  have hTQ : T ≤ Q := le_sup_left
  have hQN : Q ≤ N := sup_le hTN (Subgroup.zpowers_le.mpr haN)
  have hQP : Q ≤ P := sup_le hTP (Subgroup.zpowers_le.mpr haP)
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hTQ
  have hk_dvd : k ∣ 2 := by
    have hdvd : Nat.card ↥T * k ∣ 2 * Nat.card ↥T := by
      rw [← hcard, ← hk]
      exact Subgroup.card_dvd_of_le hQP
    rw [Nat.mul_comm 2 (Nat.card ↥T)] at hdvd
    exact Nat.dvd_of_mul_dvd_mul_left (Nat.card_pos) hdvd
  rcases (Nat.dvd_prime Nat.prime_two).mp hk_dvd with hk1 | hk2
  · exfalso
    have hQT : Nat.card ↥Q = Nat.card ↥T := by rw [hk, hk1, mul_one]
    have hT_eq_Q : T = Q := Subgroup.eq_of_le_of_card_ge hTQ (le_of_eq hQT)
    exact haT (hT_eq_Q.symm ▸ haQ)
  · have hQP' : Nat.card ↥Q = Nat.card ↥P := by
      rw [hk, hk2, hcard]
      ring
    have hQ_eq_P : Q = P := Subgroup.eq_of_le_of_card_ge hQP (le_of_eq hQP'.symm)
    rw [← hQ_eq_P]
    exact hQN

theorem y6b_card_T3 (c : Ctx6 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5)
    (hRT : c.s.R ≠ c.s.T) : Nat.card ↥(y6bT3 c.toCtx5) = 2 ^ 11 := by
  have h1 := y6_card_TM3 c hH hF
  have h2 := (y6_card_T hH).2 hRT
  show Nat.card ↥(c.s.T ⊔ M3 c.s) = 2 ^ 11
  rw [h1, h2]
  norm_num

theorem y6b_conj_mem_centSec {K M : Subgroup G} {c x : G}
    (hcK : c ∈ normalizer (K : Set G)) (hcM : c ∈ normalizer (M : Set G))
    (hx : x ∈ CFSG.GH74.GLS.centralizerSection K M) :
    c * x * c⁻¹ ∈ CFSG.GH74.GLS.centralizerSection K M := by
  obtain ⟨hxK, hxM, hx⟩ := hx
  refine ⟨?_, ?_, fun k hk => ?_⟩
  · exact mul_mem (mul_mem hcK hxK) (inv_mem hcK)
  · exact mul_mem (mul_mem hcM hxM) (inv_mem hcM)
  · have hk' : c⁻¹ * k * c ∈ K := (Subgroup.mem_normalizer_iff''.mp hcK k).mp hk
    have hcomm : ⁅c⁻¹ * k * c, x⁆ ∈ M := hx (c⁻¹ * k * c) hk'
    have hconj : c * ⁅c⁻¹ * k * c, x⁆ * c⁻¹ ∈ M :=
      (Subgroup.mem_normalizer_iff.mp hcM (⁅c⁻¹ * k * c, x⁆)).mp hcomm
    rw [show ⁅k, c * x * c⁻¹⁆ = c * ⁅c⁻¹ * k * c, x⁆ * c⁻¹ by
      rw [conjugate_commutatorElement]
      congr 1
      group]
    exact hconj

theorem y6b_le_normalizer_centSec {K M N : Subgroup G} (hNK : N ≤ normalizer (K : Set G))
    (hNM : N ≤ normalizer (M : Set G)) :
    N ≤ normalizer (CFSG.GH74.GLS.centralizerSection K M : Set G) := by
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => y6b_conj_mem_centSec (hNK hn) (hNM hn) hx, fun hx => ?_⟩
  have h := y6b_conj_mem_centSec (hNK (N.inv_mem hn)) (hNM (N.inv_mem hn)) hx
  simpa [mul_assoc] using h

theorem y6b_sylow_sup {N₁ K C T : Subgroup G} (hN : N₁ ≤ normalizer (K : Set G))
    (hCN : C ≤ N₁) (hCK : IsSylowIn 2 K C) (hT : IsSylowIn 2 N₁ T) :
    IsSylowIn 2 (N₁ ⊔ K) T := by
  obtain ⟨hCK', hCp, hCodd⟩ := hCK
  obtain ⟨hTN, hTp, hTodd⟩ := hT
  refine ⟨hTN.trans le_sup_left, hTp, ?_⟩
  have hCI : C ≤ N₁ ⊓ K := le_inf hCN hCK'
  obtain ⟨r, hr⟩ := Subgroup.card_dvd_of_le hCI
  have hK : Nat.card ↥K = C.relIndex K * Nat.card ↥C := by
    have h := Subgroup.relIndex_mul_card (H := C) (K := K)
    rw [inf_of_le_left hCK'] at h
    exact h.symm
  have hCodd' : Odd (C.relIndex K) := by
    rw [← Nat.not_even_iff_odd]
    intro h
    exact hCodd (even_iff_two_dvd.mp h)
  have hTodd' : Odd (T.relIndex N₁) := by
    rw [← Nat.not_even_iff_odd]
    intro h
    exact hTodd (even_iff_two_dvd.mp h)
  have hab_odd : Odd (T.relIndex N₁ * C.relIndex K) := Nat.odd_mul.mpr ⟨hTodd', hCodd'⟩
  have hN1 : T.relIndex N₁ * Nat.card ↥T = Nat.card ↥N₁ := by
    have h := Subgroup.relIndex_mul_card (H := T) (K := N₁)
    rwa [inf_of_le_left hTN] at h
  have hsup : T.relIndex (N₁ ⊔ K) * Nat.card ↥T = Nat.card ↥(N₁ ⊔ K) := by
    have h := Subgroup.relIndex_mul_card (H := T) (K := N₁ ⊔ K)
    rwa [inf_of_le_left (hTN.trans le_sup_left)] at h
  have hprod := y6_card_sup_mul_inf (H := N₁) (N := K) hN
  have hkey : (T.relIndex (N₁ ⊔ K) * r) * (Nat.card ↥T * Nat.card ↥C) =
      (T.relIndex N₁ * C.relIndex K) * (Nat.card ↥T * Nat.card ↥C) := by
    calc (T.relIndex (N₁ ⊔ K) * r) * (Nat.card ↥T * Nat.card ↥C)
        = (T.relIndex (N₁ ⊔ K) * Nat.card ↥T) * (Nat.card ↥C * r) := by ring
      _ = Nat.card ↥(N₁ ⊔ K) * Nat.card ↥(N₁ ⊓ K) := by rw [hsup, ← hr]
      _ = Nat.card ↥N₁ * Nat.card ↥K := hprod
      _ = (T.relIndex N₁ * Nat.card ↥T) * (C.relIndex K * Nat.card ↥C) := by
            rw [← hN1, ← hK]
      _ = (T.relIndex N₁ * C.relIndex K) * (Nat.card ↥T * Nat.card ↥C) := by ring
  have hqr : T.relIndex (N₁ ⊔ K) * r = T.relIndex N₁ * C.relIndex K :=
    Nat.mul_right_cancel (Nat.mul_pos Nat.card_pos Nat.card_pos) hkey
  have hq_odd : Odd (T.relIndex (N₁ ⊔ K)) := by
    have h : Odd (T.relIndex (N₁ ⊔ K) * r) := by rw [hqr]; exact hab_odd
    exact (Nat.odd_mul.mp h).1
  exact hq_odd.not_two_dvd_nat

theorem y6b_T3_sylow_NAV (c : Ctx6 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5)
    (hRT : c.s.R ≠ c.s.T) (h61 : c.Fact61) :
    IsSylowIn 2 (normalizer (AV1 c.e : Set G)) (c.s.T ⊔ M3 c.s) := by
  obtain ⟨-, hFour2, -⟩ := y6_four123 c hH hF hRT
  have hNV : normalizer (C1 c.e : Set G) ≤ normalizer (V1 c.e : Set G) := h61.2.1.trans h61.2.2.1
  rw [hFour2.2]
  exact y6b_sylow_sup (y6b_le_normalizer_centSec h61.2.1 hNV) Subgroup.le_normalizer hFour2.1
    h61.2.2.2.2.2.2

theorem y6b_four4 (c : Ctx6 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5)
    (hRT : c.s.R ≠ c.s.T) (h61 : c.Fact61)
    (hN : ¬ (centralizer ({c.g} : Set G) ⊓
      normalizer ((zpowers c.g ⊔ zpowers c.s.t : Subgroup G) : Set G) ≤ c.s.H)) :
    c.Four4 := by
  have h1 : Y6bHasX1 c.toCtx5 := y6b_exists_x1 c.toCtx5 hH hRT hN
  have hT3c : Nat.card ↥(y6bT3 c.toCtx5) = 2 ^ 11 := y6b_card_T3 c hH hF hRT
  obtain ⟨P, hP⟩ := y6b_exists_P c.toCtx5 hH hF hRT h1 hT3c
  have hTP : y6bT3 c.toCtx5 ≤ P := hP.1
  have hPX : P ≤ y6bX c.toCtx5 := hP.2.1
  have hPcard : Nat.card ↥P = 2 * Nat.card ↥(y6bT3 c.toCtx5) := hP.2.2.1
  obtain ⟨a, haP, haF, haW⟩ := y6b_exists_a c.toCtx5 hH hF hRT h1 hP
  have haT3 : a ∉ y6bT3 c.toCtx5 := fun ha =>
    haW (y6b_T3_cent_F_le_W c.toCtx5 hH hF hRT a ha haF)
  have hconj : ∀ w ∈ M3 c.s, ∃ f ∈ c.s.fr.F, a * w * a⁻¹ = f * w :=
    y6b_a_conj_M3 c hH hF hRT h1 hP haP haF haW
  have haN : a ∈ normalizer (V1 c.e : Set G) :=
    y6b_a_normalizes_V1 c hH hF hRT h1 (hPX haP) haF haW hconj
  have hT3N : y6bT3 c.toCtx5 ≤ normalizer (V1 c.e : Set G) :=
    (y6_TM3_le_X c hH hF).trans inf_le_right
  have hPN : P ≤ normalizer (V1 c.e : Set G) :=
    y6b_le_of_index_two hTP hPcard haP haT3 hT3N haN
  rw [Ctx6.Four4]
  by_contra hodd
  let N1 : Subgroup G := normalizer (AV1 c.e : Set G)
  let N2 : Subgroup G := normalizer (V1 c.e : Set G)
  let T3 : Subgroup G := c.s.T ⊔ M3 c.s
  let r : ℕ := N1.relIndex N2
  have hNV : N1 ≤ N2 := h61.2.2.1
  have hsyl : IsSylowIn 2 N1 T3 := y6b_T3_sylow_NAV c hH hF hRT h61
  obtain ⟨hsyl_le, -, hsyl_odd⟩ := hsyl
  have hrodd : Odd r := Nat.not_even_iff_odd.mp hodd
  have hsmul : T3.relIndex N1 * Nat.card ↥T3 = Nat.card ↥N1 := by
    have h := Subgroup.relIndex_mul_card (H := T3) (K := N1)
    rw [inf_of_le_left hsyl_le] at h
    exact h
  have hs_odd : Odd (T3.relIndex N1) := by
    rw [← Nat.not_even_iff_odd]
    intro h
    exact hsyl_odd (even_iff_two_dvd.mp h)
  have hrmul : r * Nat.card ↥N1 = Nat.card ↥N2 := by
    have h := Subgroup.relIndex_mul_card (H := N1) (K := N2)
    rw [inf_of_le_left hNV] at h
    exact h
  have hcardP : Nat.card ↥P = 2 * Nat.card ↥T3 := hPcard
  have hdvd : 2 * Nat.card ↥T3 ∣ N1.relIndex N2 * (T3.relIndex N1 * Nat.card ↥T3) := by
    have hPdvd : Nat.card ↥P ∣ Nat.card ↥N2 := Subgroup.card_dvd_of_le hPN
    rw [hcardP, ← hrmul, ← hsmul] at hPdvd
    exact hPdvd
  have hdvd' : 2 * Nat.card ↥T3 ∣ (N1.relIndex N2 * T3.relIndex N1) * Nat.card ↥T3 := by
    simpa [mul_assoc] using hdvd
  have h2dvd : 2 ∣ N1.relIndex N2 * T3.relIndex N1 :=
    Nat.dvd_of_mul_dvd_mul_right Nat.card_pos hdvd'
  exact (Nat.odd_mul.mpr ⟨hrodd, hs_odd⟩).not_two_dvd_nat h2dvd

end CFSG.OddStandard.HigherRank.YamadaG23
