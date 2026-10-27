module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBL3U3Z

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd
open Standing.Setup42

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ}

structure EndB.L2Ctx (hs : Setting46e t L p f S w z V i j) (W : Subgroup X) : Prop where
  h412 : IsLemma412 L p f (w ^ (orderOf w / 2) * t ^ i * z ^ j) (hs.setup.tBar i j)
  simple : IsSimpleGroup ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))
  lie : Blueprint.LieModel ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) .PSL 2 p
    (2 * (f / 2))
  out : conjOn (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) (hs.setup.tBar i j) ∉
    innAut ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))
  sylow : IsSylowOf 2 W (centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X))
  le : V ⊓ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) ≤ W

namespace Setting46e

theorem card_S_le (hs : Setting46e t L p f S w z V i j) :
    Nat.card S ≤ 2 * Nat.card (zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) :=
  (hs.standing.lemma41_of_lift hs.sylow hs.setup.lift hs.setup.gen3).2.2.2.2.1

theorem two_mul_card_T_le (hs : Setting46e t L p f S w z V i j) :
    2 * Nat.card (zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) ≤
      Nat.card ↥(V ⊓ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hlt := hs.beta.lt
  have hP : IsPGroup 2 ↥(V ⊓ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)) :=
    hs.sylow_V.isPGroup.to_le inf_le_left
  have hdvd := Subgroup.card_dvd_of_le hlt.le
  have hne : Nat.card (zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) ≠
      Nat.card ↥(V ⊓ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)) :=
    fun h => hlt.ne (Subgroup.eq_of_le_of_card_ge hlt.le h.symm.le)
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  obtain ⟨c, hc⟩ := hdvd
  have hc1 : c ≠ 1 := fun h => hne (by rw [hc, h, mul_one])
  have hc2 : 2 ∣ c := by
    have hcd : c ∣ 2 ^ k := ⟨Nat.card (zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X), by
      rw [← hk, hc, mul_comm]⟩
    obtain ⟨m, hm, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hcd
    rcases m with _ | m
    · exact absurd (pow_zero 2) hc1
    · exact dvd_pow_self 2 (Nat.succ_ne_zero m)
  obtain ⟨d, rfl⟩ := hc2
  have hd : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · rw [h0, mul_zero, mul_zero] at hc
      exact absurd hc (Nat.card_pos).ne'
    · exact h0
  rw [hc]
  nlinarith

end Setting46e

namespace EndB.L2Ctx

variable {hs : Setting46e t L p f S w z V i j} {W : Subgroup X}

theorem T_le (hc : L2Ctx hs W) : zpowers t ⊔ (S ⊓ L) ⊔ zpowers w ≤ W :=
  hs.beta.lt.le.trans hc.le

theorem card_U_le (hc : L2Ctx hs W) :
    Nat.card ↥(V ⊓ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)) ≤
      Nat.card W :=
  Subgroup.card_le_of_le hc.le

theorem inf_centralizer_t (hc : L2Ctx hs W) :
    W ⊓ centralizer ({t} : Set X) = zpowers t ⊔ (S ⊓ L) ⊔ zpowers w := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT1 := hs.lemma45.isSylowOf_T
  refine hT1.eq_of_le (le_inf hc.T_le (hT1.le.trans inf_le_left)) ?_
    (hc.sylow.isPGroup.to_le inf_le_left)
  exact le_inf inf_le_right (inf_le_left.trans hc.sylow.le)

theorem center_eq (hKC : AutPSL2CentralizerInput) (hc : L2Ctx hs W) :
    W ⊓ centralizer (W : Set X) =
      closure ({w ^ (orderOf w / 2) * t ^ i * z ^ j, z} : Set X) := by
  have := hc.simple
  obtain ⟨hβZ, hZle⟩ := Standing.Setup42.center_W hKC hs.setup hs.sylow_V hs.le_V hs.beta
    hc.sylow hc.le
  have hzZ := hs.z_mem_center_W hKC hc.h412 hc.sylow hc.le
  refine le_antisymm hZle ((closure_le _).mpr ?_)
  rintro x (rfl | rfl)
  · exact hβZ
  · exact hzZ

theorem eq_U_of_le_normalizer (hc : L2Ctx hs W)
    (hWN : W ≤ normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X)) :
    W = V ⊓ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (hs.beta.isSylowOf.eq_of_le hc.le (le_inf hc.sylow.le hWN) hc.sylow.isPGroup)

theorem card_eq (hc : L2Ctx hs W) :
    Nat.card W = twoPart (centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)) :=
  hc.sylow.card_eq

end EndB.L2Ctx

end CFSG.ComponentClassification.HarrisLit
