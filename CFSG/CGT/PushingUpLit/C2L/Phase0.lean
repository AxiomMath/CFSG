module

public import CFSG.CGT.PushingUpLit.C2L.Defs
public import CFSG.CGT.Timmesfeld75.SimpleCase
public import CFSG.CGT.Timmesfeld75.StdPair
import CFSG.CGT.PushingUpLit.C2L.Phase0List
import CFSG.CGT.PushingUpLit.T2KSW.Prop28
import CFSG.CGT.PushingUpLit.T2KSW.RD
import CFSG.CGT.PushingUpLit.T2KSW.ZStarE

public section

namespace CFSG.CGT.PushingUpLit.C2L

open CFSG CFSG.ABGLocalTools CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.T2K
  CFSG.CGT.PushingUpLit.T2KSW CFSG.CGT.Timmesfeld75
open CFSG.EvenSporadicStandard.Finkelstein77 (Asc76Lemma25)

variable {G : Type} [Group G] [Finite G] {L M T : Subgroup G} {n : ℕ}

theorem card_Ec_le_card_T (hs : Sec4 G L M T n) (hMN : M ≤ Subgroup.normalizer (L : Set G))
    (hME : M ≤ Subgroup.normalizer (Ec L T : Set G)) :
    2 ^ (3 * n) * Nat.card (Ec L T) ≤ Nat.card T := by
  have h : NatBlock L n := hs.hyp.natBlock
  have hLM : L ≤ M := hs.hyp.le
  have hRDT : Rl L T ⊔ Dc L T ≤ T := sup_le Rl_le_T Dc_le_T
  have hT : 2 ^ n * Nat.card (Dc L T) ≤ Nat.card T := by
    rw [← card_Rl_sup_Dc h hLM hMN hs.sylow]
    exact Subgroup.card_le_of_le hRDT
  have hVT : blockU L ≤ T := NatBlock.blockU_le_sylow hLM hMN hs.sylow
  have hVD : blockU L ≤ Dc L T := blockU_le_Dc h hLM hMN hs.sylow
  have hVn : blockU L ≤ Subgroup.normalizer (Ec L T : Set G) :=
    hVT.trans (hs.sylow.le.trans hME)
  have hEV := Aux.card_sup_mul_card_inf_of_le_normalizer hVn
  have hEVcap : Ec L T ⊓ blockU L = blockZ L := by
    ext x
    simp only [Subgroup.mem_inf]
    exact ⟨fun hx => ⟨hx.2, hx.1.2⟩, fun hx => ⟨⟨hVT hx.1, hx.2⟩, hx.1⟩⟩
  rw [hEVcap, h.card_blockU] at hEV
  have hZpos : 0 < Nat.card (blockZ L) := Nat.card_pos
  have hEVcard : Nat.card (Ec L T ⊔ blockU L : Subgroup G) = (2 ^ n) ^ 2 * Nat.card (Ec L T) := by
    apply Nat.eq_of_mul_eq_mul_right hZpos
    rw [hEV]
    ring
  have hEVD : Ec L T ⊔ blockU L ≤ Dc L T := sup_le Ec_le_Dc hVD
  have hle : (2 ^ n) ^ 2 * Nat.card (Ec L T) ≤ Nat.card (Dc L T) :=
    hEVcard ▸ Subgroup.card_le_of_le hEVD
  have h2n : 2 ^ (3 * n) = 2 ^ n * (2 ^ n) ^ 2 := by
    rw [← pow_mul, ← pow_add]
    congr 1
    ring
  calc 2 ^ (3 * n) * Nat.card (Ec L T) = 2 ^ n * ((2 ^ n) ^ 2 * Nat.card (Ec L T)) := by
        rw [h2n, mul_assoc]
    _ ≤ 2 ^ n * Nat.card (Dc L T) := Nat.mul_le_mul_left _ hle
    _ ≤ Nat.card T := hT

private theorem eq_bot_of_isPGroup_of_le_of_odd' {P Q : Subgroup G} (hP : IsPGroup 2 ↥P)
    (hPQ : P ≤ Q) (hQ : Odd (Nat.card ↥Q)) : P = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).1 hP
  have hdvd : Nat.card ↥P ∣ Nat.card ↥Q := Subgroup.card_dvd_of_le hPQ
  have hk0 : k = 0 := by
    by_contra hne
    have h2 : 2 ∣ Nat.card ↥P := by
      rw [hk]
      exact dvd_pow_self 2 hne
    exact (Nat.not_even_iff_odd.2 hQ) (even_iff_two_dvd.2 (h2.trans hdvd))
  rw [hk0, pow_zero] at hk
  exact Subgroup.eq_bot_of_card_eq _ hk

theorem normalizer_Ec_eq_of_sec4 (hs : Sec4 G L M T n) (hE : Ec L T ≠ ⊥)
    (hME : M ≤ Subgroup.normalizer (Ec L T : Set G)) :
    Subgroup.normalizer (Ec L T : Set G) = M := by
  by_contra hne
  have hlt : M < Subgroup.normalizer (Ec L T : Set G) := lt_of_le_of_ne hME (Ne.symm hne)
  exact hs.hyp.maxLocal.2 _ hlt ⟨Ec L T, hE, hs.sylow.isPGroup.to_le inf_le_left, rfl⟩

theorem Ec_inf_conj_eq_bot_of_sec4 (hs : Sec4 G L M T n) {g : G} (hg : g ∉ M) :
    Ec L T ⊓ (Ec L T).map (MulAut.conj g).toMonoidHom = ⊥ :=
  eq_bot_of_isPGroup_of_le_of_odd'
    ((hs.sylow.isPGroup.to_le inf_le_left : IsPGroup 2 ↥(Ec L T)).to_le inf_le_left)
    (inf_le_inf inf_le_right (Subgroup.map_mono inf_le_right)) (hs.hyp.odd_inf_conj hg)

private theorem natBlock_ne_bot {L : Subgroup G} (h : NatBlock L n) : L ≠ ⊥ := by
  intro hL
  have := h.sixty_le_card
  rw [hL, Subgroup.card_bot] at this
  omega

private theorem exists_noncomm_of_natBlock' {L : Subgroup G} (h : NatBlock L n) :
    ∃ a b : G, a * b ≠ b * a := by
  by_contra hcomm
  push Not at hcomm
  exact natBlock_ne_bot h
    (eq_bot_of_perfect_of_pairwise_comm h.perfect fun x _ y _ => hcomm x y)

theorem phase0_of
    (hE1 : FooteNonsolvableSimple) (hE8 : SolomonTimmesfeldTight) (h25 : Asc76Lemma25)
    (hSCL : SimpleCaseListStmt) (hList : ListWCIdentification) : Phase0 := by
  intro G _ _ L M T n hs hE hcl hw
  have hMN : M ≤ Subgroup.normalizer (L : Set G) := hs.hyp.normal hE1
  obtain ⟨-, -, hME⟩ := hs.hyp.four_four hE1 hE8 h25 hs.sylow
  have : IsSimpleGroup G := hs.hyp.simple
  have hstd : StdPair G (Ec L T) :=
    stdPair_of_weaklyClosed hSCL hList (exists_noncomm_of_natBlock' hs.hyp.natBlock) Ec_le_T hE
      hs.S_elem (normalizer_Ec_eq_of_sec4 hs hE hME) hs.sylow hs.sylowG
      (fun g hg => Ec_inf_conj_eq_bot_of_sec4 hs hg) hw
  exact list_false_le hs.hyp.two_le hs.hyp.natBlock.perfect (natBlock_ne_bot hs.hyp.natBlock)
    hs.sylowG hcl (le_centralizer_inf_centralizer L T) (card_Ec_le_card_T hs hMN hME) hstd

end CFSG.CGT.PushingUpLit.C2L
