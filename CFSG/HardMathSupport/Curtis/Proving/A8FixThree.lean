module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusDefs
public import CFSG.HardMathSupport.Curtis.Proving.FixThreeAltEight
public import CFSG.HardMathSupport.Curtis.Proving.NineDvdCentralizer
public import CFSG.HardMathSupport.Curtis.Proving.PerfectTwoNine
import CFSG.Alternating.Multipliers.OddKernel
import CFSG.Fischer.Classification.Recognition.PSU6
import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.HardMathSupport.Curtis.Proving

open CFSG.AGLEmbedding
open CFSG.AGLEmbedding.ParabPrime (perfectJoin perfectJoin_le perfectJoin_perfect)

@[expose] def IsAlternatingEight (X : Type) [Group X] : Prop :=
  Nonempty (X ≃* alternatingGroup (Fin 8))

theorem center_eq_bot_of_altEight {Y : Type} [Group Y] [Finite Y] {L J : Subgroup Y}
    (h : CompParab L J) (e : ↥L ⧸ Subgroup.center ↥L ≃* alternatingGroup (Fin 8)) :
    Subgroup.center ↥L = ⊥ := by
  have : Group.IsPerfect ↥L := ⟨h.comp.2.2.1⟩
  set η : ↥L →* alternatingGroup (Fin 8) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L)) with hη
  have hηs : Function.Surjective η := by
    intro y
    obtain ⟨q, rfl⟩ := e.surjective y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥L) q
    exact ⟨x, rfl⟩
  have hker : η.ker = Subgroup.center ↥L := by
    ext x
    rw [MonoidHom.mem_ker]
    change e (QuotientGroup.mk' (Subgroup.center ↥L) x) = 1 ↔ x ∈ Subgroup.center ↥L
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hodd : Odd (Nat.card η.ker) := by
    rw [hker]
    exact h.odd
  have h1 := CFSG.Alternating.Multipliers.card_ker_eq_one_of_odd (m := 6) le_rfl η hηs
    hker.le hodd
  rw [hker] at h1
  exact Subgroup.eq_bot_of_card_eq _ h1

theorem fixThreeVoid_altEight :
    FixThreeVoid IsAlternatingEight := by
  intro Y _ _ L J u h hX
  obtain ⟨e⟩ := hX
  have hcen : Subgroup.center ↥L = ⊥ := center_eq_bot_of_altEight h.parab e
  set π : ↥L →* ↥L ⧸ Subgroup.center ↥L := QuotientGroup.mk' (Subgroup.center ↥L) with hπ
  set η : ↥L →* alternatingGroup (Fin 8) := e.toMonoidHom.comp π with hη
  have hinj : Function.Injective η := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : π x = 1 := (MulEquiv.map_eq_one_iff e).1 hx
    have h2 : x ∈ Subgroup.center ↥L := (QuotientGroup.eq_one_iff x).1 h1
    rw [hcen, Subgroup.mem_bot] at h2
    exact h2
  have hηs : Function.Surjective η := by
    intro y
    obtain ⟨q, rfl⟩ := e.surjective y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥L) q
    exact ⟨x, rfl⟩
  have hA8 : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  have hLcard : Nat.card ↥L = 20160 := by
    rw [Nat.card_congr (MulEquiv.ofBijective η ⟨hinj, hηs⟩).toEquiv, hA8]
  set φ : ↥L →* Equiv.Perm (Fin 8) := (alternatingGroup (Fin 8)).subtype.comp η with hφ
  have hφinj : Function.Injective φ := Subtype.val_injective.comp hinj
  have hpar := h.parab.parab
  obtain ⟨hJL, T, hT, hTN⟩ := hpar
  have hTJ : T ≤ J := fun x hx => hTN ⟨hT.1 hx, Subgroup.le_normalizer hx⟩
  have hTL : T ≤ L := hT.1
  have hJc : Nat.card (J.subgroupOf L) = Nat.card J :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJL).toEquiv
  have hTc : Nat.card (T.subgroupOf L) = Nat.card T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTL).toEquiv
  have hTJb : T.subgroupOf L ≤ J.subgroupOf L := fun x hx =>
    Subgroup.mem_subgroupOf.2 (hTJ (Subgroup.mem_subgroupOf.1 hx))
  have hPA : (J.subgroupOf L).map φ ≤ alternatingGroup (Fin 8) := by
    rintro _ ⟨x, _, rfl⟩
    exact (η x).2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hT.2.1
  have hodd2 := hT.2.2
  have hidx := Subgroup.card_mul_index (H := T.subgroupOf L)
  rw [hTc, hn, hLcard] at hidx
  have hn6 : n = 6 := by
    have hdvd : 2 ^ n ∣ 20160 := ⟨(T.subgroupOf L).index, hidx.symm⟩
    have hle : 2 ^ n ≤ 20160 := Nat.le_of_dvd (by norm_num) hdvd
    have hn15 : n < 15 := by
      by_contra hc
      rw [not_lt] at hc
      have := le_trans (Nat.pow_le_pow_right (by norm_num : 0 < 2) hc) hle
      norm_num at this
    interval_cases n <;> first | rfl | (norm_num at hidx; omega)
  have hPT : Nat.card ((T.subgroupOf L).map φ) = 64 := by
    rw [Subgroup.card_map_of_injective hφinj, hTc, hn, hn6]
    norm_num
  have hPTle : (T.subgroupOf L).map φ ≤ (J.subgroupOf L).map φ :=
    Subgroup.map_mono hTJb
  have hP2 : IsPGroup 2 ((T.subgroupOf L).map φ) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact (IsPGroup.iff_card).2 ⟨6, by rw [hPT]; norm_num⟩
  have hJopts := card_of_two_group_le hPA hPTle hP2 hPT
  rw [Subgroup.card_map_of_injective hφinj, hJc] at hJopts
  have hu1 : (⟨u, h.mem⟩ : ↥L) ≠ 1 := by
    intro h1
    apply h.not_mem
    have hu : u = 1 := congrArg Subtype.val h1
    rw [hu]
    exact Subgroup.one_mem _
  have hpow3 : (⟨u, h.mem⟩ : ↥L) ^ 3 = 1 := Subtype.ext (by simpa using h.pow)
  have hord : orderOf (⟨u, h.mem⟩ : ↥L) = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime hpow3 hu1
  have h9L : 9 ∣ Nat.card ↥L := by
    rw [hLcard]
    norm_num
  have hC := nine_dvd_card_centralizer_of_orderOf_eq_three h9L hord
  have hCJ : (Subgroup.centralizer ({(⟨u, h.mem⟩ : ↥L)} : Set ↥L)).map L.subtype ≤ J := by
    rintro _ ⟨x, hx, rfl⟩
    have hc := Subgroup.mem_centralizer_iff.1 hx _ (Set.mem_singleton _)
    have hc' : u * (x : Y) = (x : Y) * u := by
      have := congrArg Subtype.val hc
      simpa using this
    apply h.fix (x : Y) x.2
    rw [hc', mul_inv_cancel_right]
  have hcardC :
      Nat.card ((Subgroup.centralizer ({(⟨u, h.mem⟩ : ↥L)} : Set ↥L)).map L.subtype) =
        Nat.card (Subgroup.centralizer ({(⟨u, h.mem⟩ : ↥L)} : Set ↥L)) :=
    Subgroup.card_map_of_injective (f := L.subtype) Subtype.val_injective
  have h9J : 9 ∣ Nat.card J := by
    rw [← hcardC] at hC
    exact hC.trans (Subgroup.card_dvd_of_le hCJ)
  rcases hJopts with hJ | hJ | hJ | hJ | hJ
  · rw [hJ] at h9J
    norm_num at h9J
  · rw [hJ] at h9J
    norm_num at h9J
  ·
    have hVJ : perfectJoin J ≤ J := perfectJoin_le J
    have hVperf : ⁅perfectJoin J, perfectJoin J⁆ = perfectJoin J := perfectJoin_perfect J
    have hdvd : Nat.card (perfectJoin J) ∣ 2 ^ 6 * 9 := by
      have hd := Subgroup.card_dvd_of_le hVJ
      rw [hJ] at hd
      exact hd.trans (by norm_num)
    have hV0 : perfectJoin J = ⊥ :=
      perfect_eq_bot_of_card_dvd_two_pow_mul_nine (a := 6) (perfectJoin J) hVperf hdvd
    have hj := h.join
    rw [hV0, bot_sup_eq] at hj
    exact h.not_mem hj
  · rw [hJ] at h9J
    norm_num at h9J
  ·
    exact h.parab.ne_top (Subgroup.eq_of_le_of_card_ge hJL (le_of_eq (by rw [hLcard, hJ])))

end CFSG.HardMathSupport.Curtis.Proving

end
