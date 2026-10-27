module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.UKhatZ
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.UHSFacts

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup Equiv Equiv.Perm CFSG.OddStandard.AltStdSec.SwapPattern
  CFSG.Blueprint.NativeSporadic

open scoped commutatorElement

variable {G : Type} [Group G] {z : G} {ι ιd : Perm (Fin 10) →* G}

structure HSKhat (z : G) (ι : Perm (Fin 10) →* G) (Kh : Subgroup G) : Prop where
  le : Kh ≤ centralizer ({z * ι τ₀} : Set G)
  normal : (Kh.subgroupOf (centralizer ({z * ι τ₀} : Set G))).Normal
  perfect : ⁅Kh, Kh⁆ = Kh
  quasisimple : CFSG.Open.IsQuasisimple ↥Kh
  agrp_le : Agrp ι ≤ Kh
  hs : IsSporadic (↥Kh ⧸ center ↥Kh) .HS

structure HSCtx (z : G) (ι ιd : Perm (Fin 10) →* G) (Kh : Subgroup G) : Prop where
  frame : UFrame z ι ιd
  khat : HSKhat z ι Kh
  facts : HSFacts
  h8 : ∀ Q : Subgroup G, IsPGroup 2 Q → Q ≤ centralizer (Agrp ι : Set G) →
    Q ≤ centralizer ({z * ι τ₀} : Set G) → Nat.card Q ≤ 8

namespace HSCtx

variable {Kh : Subgroup G}

theorem conj_mem (C : HSCtx z ι ιd Kh) {c k : G}
    (hc : c ∈ centralizer ({z * ι τ₀} : Set G)) (hk : k ∈ Kh) : c * k * c⁻¹ ∈ Kh := by
  let Cc := centralizer ({z * ι τ₀} : Set G)
  have hk' : (⟨k, C.khat.le hk⟩ : ↥Cc) ∈ Kh.subgroupOf Cc := by
    rw [Subgroup.mem_subgroupOf]
    exact hk
  have hmem := C.khat.normal.conj_mem ⟨k, C.khat.le hk⟩ hk' ⟨c, hc⟩
  rw [Subgroup.mem_subgroupOf] at hmem
  simpa using hmem

theorem card_quotient (C : HSCtx z ι ιd Kh) :
    Nat.card (↥Kh ⧸ center ↥Kh) = 44352000 := by
  exact C.facts.1 C.khat.hs

theorem two_pow_nine_dvd_card (C : HSCtx z ι ιd Kh) : 2 ^ 9 ∣ Nat.card ↥Kh := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center ↥Kh), C.card_quotient]
  exact dvd_mul_of_dvd_left (by norm_num) _

theorem card_gt (C : HSCtx z ι ιd Kh) [Finite G] : 20160 < Nat.card ↥Kh := by
  have hle : Nat.card (↥Kh ⧸ center ↥Kh) ≤ Nat.card ↥Kh :=
    Nat.card_le_card_of_surjective (QuotientGroup.mk (s := center ↥Kh))
      QuotientGroup.mk_surjective
  rw [C.card_quotient] at hle
  omega

theorem isQuasisimple (C : HSCtx z ι ιd Kh) : CFSG.IsQuasisimple ↥Kh := by
  refine ⟨?_, C.khat.quasisimple.2, ?_⟩
  · exact Group.isPerfect_def.mpr C.khat.quasisimple.1
  · by_contra h
    push_neg at h
    haveI : IsMulCommutative (↥Kh ⧸ center ↥Kh) := isMulCommutative_iff.mpr h
    have hp : (Nat.card (↥Kh ⧸ center ↥Kh)).Prime :=
      Group.is_simple_iff_prime_card.mp C.khat.quasisimple.2
    have h2 : 2 ∣ Nat.card (↥Kh ⧸ center ↥Kh) := by
      rw [C.card_quotient]; norm_num
    rcases hp.eq_one_or_self_of_dvd 2 h2 with h1 | h1
    · omega
    · rw [C.card_quotient] at h1; norm_num at h1

theorem card_center_le_two (C : HSCtx z ι ιd Kh) [Finite G] : Nat.card ↥(center ↥Kh) ≤ 2 := by
  exact C.facts.2.2.2 (E := ↥Kh) (Subgroup.isPerfect_iff.mpr C.khat.perfect) C.khat.hs

theorem isPGroup_center (C : HSCtx z ι ιd Kh) [Finite G] : IsPGroup 2 ↥(center ↥Kh) := by
  haveI : Nonempty ↥(center ↥Kh) := ⟨1⟩
  have hpos : 0 < Nat.card ↥(center ↥Kh) := Nat.card_pos
  have hle := C.card_center_le_two
  obtain h1 | h1 : Nat.card ↥(center ↥Kh) = 1 ∨ Nat.card ↥(center ↥Kh) = 2 := by omega
  · exact IsPGroup.of_card (n := 0) (by simpa using h1)
  · exact IsPGroup.of_card (n := 1) (by simpa using h1)

theorem not_centralizes_z (C : HSCtx z ι ιd Kh) [Finite G] : ¬ ∀ k ∈ Kh, z * k = k * z := by
  exact not_centralizes_z_of_card_gt C.frame C.khat.le C.khat.perfect C.khat.agrp_le
    C.card_gt

end HSCtx

end CFSG.OddStandard.AltStdSec.SwapPartner
