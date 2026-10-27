module

public import CFSG.CGT.PushingUpLit.LIT.FooteSimple
public import CFSG.CGT.PushingUpLit.LIT.FooteSplit
public import CFSG.CGT.PushingUpLit.T2K.FourFiveD

public section

namespace CFSG.CGT.PushingUpLit.T2K

open CFSG CFSG.RankThree.PartOne CFSG.Open CFSG.Assembly CFSG.CGT.PushingUpLit.BHS
open scoped commutatorElement

structure T2Hyp (G : Type) [Group G] [Finite G] (L M : Subgroup G) (n : ℕ) : Prop where
  kproper : KProper InCatalog G
  simple : IsSimpleGroup G
  charTwo : CFSG.Assembly.IsCharTwoType G
  inX : InClassX ↥L
  maxLocal : IsMaximalTwoLocal M
  le : L ≤ M
  subnormal : (L.subgroupOf M).IsSubnormal
  unique : maximalTwoLocalsContaining (L : Set G) = {M}
  two_le : 2 ≤ n
  nat : IsNaturalSLTwoModule ↥L n

theorem isPGroup_blockU' {G : Type} [Group G] (L : Subgroup G) : IsPGroup 2 (blockU L) :=
  (isPGroup_oTwoIn L).to_le (blockU_le_oTwoIn L)

namespace NatBlock

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ}

theorem not_isPGroup (h : NatBlock L n) : ¬ IsPGroup 2 ↥L := by
  intro hL
  have hn : 1 ≤ n := by have := h.two_le; omega
  have hS : IsPGroup 2 (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) :=
    hL.of_surjective h.natData.φ h.natData.φ_surj
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).1 hS
  rw [card_sl2_field, GaloisField.card 2 n (by omega)] at hk
  have hdvd : (2 ^ n) ^ 2 - 1 ∣ 2 ^ k := ⟨2 ^ n, by rw [← hk]; ring⟩
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hodd := odd_sq_two_pow_sub_one hn
  have hi0 : i = 0 := by
    by_contra hne
    have : Even ((2 ^ n) ^ 2 - 1) := by
      rw [hi]
      exact (Nat.even_pow.2 ⟨even_two, hne⟩)
    exact (Nat.not_even_iff_odd.2 hodd) this
  rw [hi0, pow_zero] at hi
  have h4 : 4 ≤ (2 ^ n) ^ 2 := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ (2 ^ n) ^ 2 :=
        Nat.pow_le_pow_left (Nat.le_self_pow (by omega) 2 |>.trans' (by norm_num)) 2
  omega

theorem sixty_le_card (h : NatBlock L n) : 60 ≤ Nat.card ↥L := by
  have hn : 2 ≤ n := h.two_le
  have hle : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) ≤ Nat.card ↥L :=
    Nat.card_le_card_of_surjective _ h.natData.φ_surj
  rw [card_sl2_field, GaloisField.card 2 n (by omega)] at hle
  have hq : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hq2 : 16 ≤ (2 ^ n) ^ 2 := by nlinarith
  have : 4 * 15 ≤ 2 ^ n * ((2 ^ n) ^ 2 - 1) := Nat.mul_le_mul hq (by omega)
  omega

end NatBlock

namespace T2Hyp

variable {G : Type} [Group G] [Finite G] {L M : Subgroup G} {n : ℕ}
variable (h : T2Hyp G L M n)
include h

theorem natBlock : NatBlock L n := ⟨h.inX.1, h.nat, h.two_le⟩

theorem blockU_ne_bot : blockU L ≠ ⊥ := by
  intro hbot
  obtain ⟨v, hv⟩ := h.natBlock.natData.ψ_surj
    (Multiplicative.ofAdd (Pi.single (0 : Fin 2) (1 : GaloisField 2 n)))
  have hv1 : v = 1 :=
    Subtype.ext ((Subgroup.eq_bot_iff_forall _).1 hbot (v : G) v.2)
  rw [hv1, map_one] at hv
  have h0 := congrArg Multiplicative.toAdd hv
  simp only [toAdd_one, toAdd_ofAdd] at h0
  have := congrFun h0.symm 0
  simp at this

theorem M_ne_top : M ≠ ⊤ := by
  intro hM
  obtain ⟨P, hP, hP2, hMP⟩ := h.maxLocal.1
  have hPn : P.Normal := Subgroup.normalizer_eq_top_iff.1 (hMP ▸ hM)
  have hPtop : P = ⊤ := by
    rcases h.simple.eq_bot_or_eq_top_of_normal P with h0 | h0
    · exact absurd h0 hP
    · exact h0
  rw [hPtop] at hP2
  exact h.natBlock.not_isPGroup (hP2.to_le le_top)

theorem normal (hE1 : FooteNonsolvableSimple) : M ≤ Subgroup.normalizer (L : Set G) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer h.le).1
    (hE1 G h.simple h.kproper h.charTwo M L h.maxLocal h.le h.subnormal h.inX.1
      (isQuasisimple_top_of_natSL h.inX.1 (by have := h.two_le; omega) h.nat) h.unique)

theorem normalizer_blockU_eq (hE1 : FooteNonsolvableSimple) :
    Subgroup.normalizer (blockU L : Set G) = M := by
  have hMV : M ≤ Subgroup.normalizer (blockU L : Set G) :=
    NatBlock.le_normalizer_blockU_of_le (h.normal hE1)
  by_contra hne
  exact h.maxLocal.2 _ (lt_of_le_of_ne hMV (Ne.symm hne))
    ⟨blockU L, h.blockU_ne_bot, isPGroup_blockU' L, rfl⟩

theorem normalizer_eq (hE1 : FooteNonsolvableSimple) : Subgroup.normalizer (L : Set G) = M := by
  refine le_antisymm (fun g hg => ?_) (h.normal hE1)
  rw [← h.normalizer_blockU_eq hE1, Subgroup.mem_normalizer_iff]
  intro u
  refine ⟨fun hu => conj_mem_blockU hg hu, fun hu => ?_⟩
  have := conj_mem_blockU ((Subgroup.normalizer (L : Set G)).inv_mem hg) hu
  simpa [mul_assoc] using this

theorem centralizer_le (hE1 : FooteNonsolvableSimple) :
    Subgroup.centralizer (L : Set G) ≤ M := fun _ hc =>
  (h.normalizer_eq hE1) ▸ Subgroup.centralizer_le_normalizer (L : Set G) hc

end T2Hyp

end CFSG.CGT.PushingUpLit.T2K
