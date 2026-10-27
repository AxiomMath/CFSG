module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4Defs

public section

namespace CFSG.OddStandard.AltStdSmall4

open Subgroup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ}
  {θ : L ≃* alternatingGroup (Fin n)} {hn : 8 ≤ n} {z : G} {T : Subgroup G}

theorem N0Data.card_eq (h : N0Data θ hn z T) : Nat.card T = 64 := by
  rcases h.homo with h1 | h1
  · obtain ⟨e⟩ := h1
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
    rfl
  · obtain ⟨e⟩ := h1
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
    rfl

theorem coprime_card_oddCoreOf (H : Subgroup G) :
    Nat.Coprime 2 (Nat.card (AltStdSec.oddCoreOf H)) := by
  unfold AltStdSec.oddCoreOf CFSG.oddCore
  rw [card_map_of_injective H.subtype_injective]
  have : CFSG.oddCore H = pPrimeCore 2 H := by
    unfold CFSG.oddCore pPrimeCore
    congr 1
    ext N
    exact and_congr_right fun _ => Nat.coprime_two_left.symm
  rw [← CFSG.oddCore, this]
  exact pPrimeCore_coprime_card

theorem card_centralizer_eq (h : HData θ hn z T) :
    Nat.card (centralizer (T : Set G)) =
      64 * Nat.card (AltStdSec.oddCoreOf (normalizer (T : Set G))) := by
  set O := AltStdSec.oddCoreOf (normalizer (T : Set G)) with hO
  have hOC : O ≤ centralizer (T : Set G) := by rw [h.cent]; exact le_sup_right
  have hcomm : ∀ (a : T) (b : O), Commute (T.subtype a) (O.subtype b) := by
    intro a b
    exact mem_centralizer_iff.1 (hOC b.2) a a.2
  let φ : T × O →* G := MonoidHom.noncommCoprod T.subtype O.subtype hcomm
  have hrange : φ.range = T ⊔ O := by
    rw [MonoidHom.noncommCoprod_range, range_subtype, range_subtype]
  have hT64 := h.n0.card_eq
  have hinf : T ⊓ O = ⊥ :=
    inf_eq_bot_of_coprime (by rw [hT64]; exact Nat.Coprime.pow_left 6 (coprime_card_oddCoreOf _))
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨a, b⟩ hab
    have h1 : (a : G) * b = 1 := hab
    have ha : (a : G) = (b : G)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have haO : (a : G) ∈ O := by rw [ha]; exact inv_mem b.2
    have hmem : (a : G) ∈ T ⊓ O := ⟨a.2, haO⟩
    rw [hinf, mem_bot] at hmem
    have hb : (b : G) = 1 := by
      have := ha.symm
      rw [hmem, inv_eq_one] at this
      exact this
    exact (Prod.ext (Subtype.ext hmem) (Subtype.ext hb) : (a, b) = 1) ▸ one_mem _
  rw [h.cent, ← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_prod,
    hT64]

theorem mem_ker_normAct_iff (g : normalizer (T : Set G)) :
    g ∈ (AltStdBal.normAct T).ker ↔ (g : G) ∈ centralizer (T : Set G) := by
  rw [MonoidHom.mem_ker, mem_centralizer_iff]
  constructor
  · intro h1 x hx
    have := congrArg (fun φ : MulAut T => ((φ ⟨x, hx⟩ : T) : G)) h1
    simp only [AltStdBal.coe_normAct_apply, MulAut.one_apply] at this
    calc x * (g : G) = ((g : G) * x * (g : G)⁻¹) * g := by rw [this]
      _ = g * x := by group
  · intro h1
    ext w
    rw [AltStdBal.coe_normAct_apply, MulAut.one_apply, ← h1 w w.2, mul_inv_cancel_right]

theorem card_normalizer_eq (h : HData θ hn z T) :
    Nat.card (normalizer (T : Set G)) =
      Nat.card (Hbar T) * (64 * Nat.card (AltStdSec.oddCoreOf (normalizer (T : Set G)))) := by
  have hker : Nat.card (AltStdBal.normAct T).ker = Nat.card (centralizer (T : Set G)) := by
    have hle : centralizer (T : Set G) ≤ normalizer (T : Set G) :=
      Subgroup.centralizer_le_normalizer (T : Set G)
    have : (AltStdBal.normAct T).ker = (centralizer (T : Set G)).subgroupOf
        (normalizer (T : Set G)) := by
      ext g
      rw [mem_ker_normAct_iff, mem_subgroupOf]
    rw [this, Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv]
  rw [← Subgroup.card_ker_mul_card_range (AltStdBal.normAct T), hker, card_centralizer_eq h,
    mul_comm]
  rfl

theorem sec4HbarNotSmall_of_twoPart (hP : Sec4HTwoPart) : Sec4HbarNotSmall := by
  intro G _ _ L Q n θ z c T hH
  have h11 := hP G L Q n θ z c T hH
  rw [card_normalizer_eq hH] at h11
  have hodd := coprime_card_oddCoreOf (normalizer (T : Set G))
  have h32 : 2 ^ 5 ∣ Nat.card (Hbar T) := by
    set a := Nat.card (Hbar T)
    set b := Nat.card (AltStdSec.oddCoreOf (normalizer (T : Set G)))
    have h1 : 2 ^ 11 ∣ (a * 2 ^ 6) * b := by
      have : a * (64 * b) = (a * 2 ^ 6) * b := by ring
      rw [← this]
      exact h11
    have h2 : 2 ^ 11 ∣ a * 2 ^ 6 := (Nat.Coprime.pow_left 11 hodd).dvd_of_dvd_mul_right h1
    have h3 : 2 ^ 5 * 2 ^ 6 ∣ a * 2 ^ 6 := by rw [← pow_add]; exact h2
    exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) h3
  constructor
  · intro h336
    rw [h336] at h32
    norm_num at h32
  · intro h1008
    rw [h1008] at h32
    norm_num at h32

end CFSG.OddStandard.AltStdSmall4
