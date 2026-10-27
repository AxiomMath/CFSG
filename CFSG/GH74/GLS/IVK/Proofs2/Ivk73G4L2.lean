module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4Defs
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4Sections
public import CFSG.GH74.GLS.C3.Layer1.BkIvk73
public import CFSG.GH74.GLS.C3.Layer1.EvenCore
public import CFSG.GH74.GLS.C3.Layer1.Back91
public import CFSG.GH74.GLS.C3.Layer1.EvenCoreSC
public import CFSG.Walter.Bender1970.S2.Involutions

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools Blueprint CFSG.ComponentClassification EvenCore
open scoped commutatorElement

@[expose] def B_ivk_7_3_L2_g4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (N L K Q : Subgroup G),
    Gen4 ↥N → GHList ↥L → IsKGroupNative ↥N → IsSimpleSocle L N → K ≤ L → IsSimpleGroup ↥K →
    HasL2Model ↥K Odd → IsSylowOf 2 Q (centralizer (K : Set G) ⊓ N) → 2 ≤ pRank 2 ↥Q →
    (∀ y ∈ N, orderOf y = 2 → y ∈ centralizer (K : Set G) →
      IsCompIn (centralizer ({y} : Set G) ⊓ N) K) →
    EvenMaxCase K L N

theorem b_ivk_7_3_L2_of_g4 (h73 : IVK.IVK_7_3_g4) : B_ivk_7_3_L2_g4 := by
  intro G _ _ N L K Q hgen hGH hN hsoc hKL hKs hKodd hQ hrank hterm
  obtain ⟨u, huQ, -, -, hu2, -, -, -⟩ := C3.Layer1.U1a.exists_commuting_involutions hrank
  have huC : u ∈ centralizer (K : Set G) ⊓ N := hQ.le huQ
  have hcomp := hterm u huC.2 hu2 huC.1
  have hKq : IsQuasisimple ↥K :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hcomp.1) hcomp.2.1
  have hnc : ∃ a b : ↥K, a * b ≠ b * a := by
    obtain ⟨-, -, a', b', hab'⟩ := hKq
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a'
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b'
    exact ⟨a, b, fun hh => hab' (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hh])⟩
  have hO : pPrimeCore 2 ↥K = ⊥ := CFSG.Walter.pPrimeCore_eq_bot_of_isSimpleGroup hnc
  let e : ↥K ≃* (↥K ⧸ pPrimeCore 2 ↥K) :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hO.symm)
  have hU2 : InU2 (↥K ⧸ pPrimeCore 2 ↥K) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e hKq,
      Or.inl (TwoThin.hasL2Model_of_mulEquiv e hKodd)⟩
  obtain ⟨-, -, hcases⟩ := h73 G N L K Q hgen hGH hN
    ⟨hsoc.le, hsoc.normal, hsoc.simple, hsoc.centralizer_trivial⟩ hKL hKq hU2 hQ hrank hterm
  have hcK : center ↥K = ⊥ := by
    have := hKs
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center ↥K) with hb | ht
    · exact hb
    · exfalso
      obtain ⟨a, b, hab⟩ := hnc
      apply hab
      have ha : a ∈ center ↥K := by rw [ht]; exact Subgroup.mem_top a
      exact (Subgroup.mem_center_iff.1 ha b).symm
  have hcenter : center (↥K ⧸ pPrimeCore 2 ↥K) = ⊥ := by
    rw [← Subgroup.map_center_eq e, hcK, Subgroup.map_bot]
  obtain ⟨q, hq, hcardK⟩ := exists_odd_two_mul_card_of_hasL2Model hKodd
  rcases hcases with ⟨hA5, hM, hN⟩ | ⟨hA5, hJ, hN⟩ | ⟨hNL, n, hn, hAn, hL⟩ | ⟨hL34, -, -⟩ |
    ⟨hL34, -, hc4, -⟩
  · obtain ⟨e5⟩ := hA5
    exact Or.inr (Or.inl ⟨⟨e.trans e5⟩, hM, hN⟩)
  · obtain ⟨e5⟩ := hA5
    exact Or.inr (Or.inr ⟨⟨e.trans e5⟩, hJ, hN⟩)
  · obtain ⟨eA⟩ := hAn
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with rfl | rfl | rfl
    · exact Or.inl ⟨hNL, 5, by simp, ⟨e.trans eA⟩, hL⟩
    · exact Or.inl ⟨hNL, 6, by simp, ⟨e.trans eA⟩, hL⟩
    · exfalso
      have h7 : Nat.card ↥K = 2520 := by
        rw [Nat.card_congr (e.trans eA).toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
        decide
      rw [h7] at hcardK
      exact no_q_mul_sq_sub_one_eq_5040 q (by omega)
  · exfalso
    have h1 := card_eq_of_lieModel_L34 hL34
    have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center (↥K ⧸ pPrimeCore 2 ↥K))
    rw [h1, hcenter, Subgroup.card_bot, mul_one, ← Nat.card_congr e.toEquiv] at h2
    rw [h2] at hcardK
    exact no_q_mul_sq_sub_one_eq_40320 q (by omega)
  · exfalso
    rw [hcenter, Subgroup.card_bot] at hc4
    omega

theorem b_even_N_core_of_7_3_g4
    (h73 : B_ivk_7_3_L2_g4) : B_even_N_core := by
  intro G _ _ hG hE hV x K T Q N hs hstd hgam hMN hN
  have hMle : normalizer (K : Set G) ≤ N := hMN.le
  have hQC : IsSylowOf 2 Q (centralizer (K : Set G)) := hs.sylowQ
  have hCKN : centralizer (K : Set G) ≤ N := fun c hc => hMle (centralizer_le_normalizer _ hc)
  have hKN : K ≤ N := Subgroup.le_normalizer.trans hMle
  have hQN : Q ≤ N := hQC.le.trans hCKN
  have hNM : ¬ N ≤ normalizer (K : Set G) := not_le_of_gt hMN
  have hCN : ∀ y ∈ centralizer (K : Set G), orderOf y = 2 → centralizer ({y} : Set G) ≤ N :=
    fun y hy hy2 => centralizer_le_of_mem_centralizer hQC hgam hMle hy hy2
  have hQ2 : ∀ b ∈ Q, orderOf b = 2 → centralizer ({b} : Set G) ≤ normalizer (K : Set G) :=
    fun b hb hb2 => centralizer_le_normalizer_of_mem hgam hb hb2
  have hcoreOf : pPrimeCoreOf 2 N = ⊥ :=
    pPrimeCoreOf_eq_bot hs.rankQ hQN (fun b hb hb2 => hCN b (hQC.le hb) hb2) hE.2.1
  have hcoreN : pPrimeCore 2 ↥N = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ N.subtype_injective).mp hcoreOf
  obtain ⟨u, huQ, v, hvQ, hu2, hv2, hne, hcomm⟩ :=
    C3.Layer1.U1a.exists_commuting_involutions hs.rankQ
  have hw2 : orderOf (u * v) = 2 := by
    have huu : u * u = 1 := by
      have := pow_orderOf_eq_one u
      rwa [hu2, pow_two] at this
    have hvv : v * v = 1 := by
      have := pow_orderOf_eq_one v
      rwa [hv2, pow_two] at this
    refine orderOf_eq_prime ?_ ?_
    · calc (u * v) ^ 2 = u * v * (u * v) := sq _
        _ = u * (v * u) * v := by simp only [mul_assoc]
        _ = u * (u * v) * v := by rw [← hcomm]
        _ = (u * u) * (v * v) := by simp only [mul_assoc]
        _ = 1 := by rw [huu, hvv, one_mul]
    · intro h
      apply hne
      have : u = v⁻¹ := eq_inv_of_mul_eq_one_left h
      rw [this]
      exact (inv_eq_of_mul_eq_one_right hvv).symm ▸ rfl
  have huvQ : u * v ∈ Q := Q.mul_mem huQ hvQ
  have hKC : ∀ b ∈ Q, K ≤ centralizer ({b} : Set G) := by
    intro b hb k hk
    rw [mem_centralizer_singleton_iff]
    exact (mem_centralizer_iff.mp (hQC.le hb) k hk)
  have hKb : ∀ b ∈ Q, orderOf b = 2 → IsPCompIn 2 (centralizer ({b} : Set G)) K := fun b hb hb2 =>
    hs.isPCompIn_of_le_normalizer (hKC b hb) (hQ2 b hb hb2)
  have hmemN : ∀ b ∈ Q, b ∈ N := fun b hb => hQN hb
  have hCQ : ∀ b ∈ Q, orderOf b = 2 → centralizer ({b} : Set G) ≤ N :=
    fun b hb hb2 => hCN b (hQC.le hb) hb2
  obtain ⟨Lh, hLc, hKL⟩ := exists_component_ge_of_fourGroup (H := ↥N) hcoreN
    (K := K.subgroupOf N) (u := ⟨u, hmemN u huQ⟩) (v := ⟨v, hmemN v hvQ⟩)
    (by rw [Subgroup.orderOf_mk]; exact hu2) (by rw [Subgroup.orderOf_mk]; exact hv2)
    (Subtype.ext hcomm) (fun h => hne (congrArg Subtype.val h))
    (isTwoComponent_in_N (hmemN u huQ) (hCQ u huQ hu2) (hKb u huQ hu2))
    (isTwoComponent_in_N (hmemN v hvQ) (hCQ v hvQ hv2) (hKb v hvQ hv2))
    (isTwoComponent_in_N (hmemN (u * v) huvQ) (hCQ (u * v) huvQ hw2) (hKb (u * v) huvQ hw2))
  have hKq : CFSG.IsQuasisimple ↥K := hs.isQuasisimple_K
  obtain ⟨hKlt, hsoc⟩ := exists_simpleSocle hcoreN hQC hCKN hgam hNM hKN hKq hstd hQ2 hLc hKL
  have hKodd : HasL2Model ↥K Odd :=
    C3.Layer1.Back.hasL2Model_mono (fun q hq => C3.Layer1.Back.isFM9_odd hq) hs.isL2
  refine ⟨_, hKlt, hsoc, ?_⟩
  have hnonab : ∃ a b : ↥(Lh.map N.subtype), a * b ≠ b * a := by
    obtain ⟨-, -, a', b', hab'⟩ := hKq
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a'
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b'
    refine ⟨⟨a, hKlt.le a.2⟩, ⟨b, hKlt.le b.2⟩, fun hh => hab' ?_⟩
    have hh' : (a : G) * (b : G) = (b : G) * (a : G) :=
      congrArg (fun z : ↥(Lh.map N.subtype) => (z : G)) hh
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    exact congrArg QuotientGroup.mk (Subtype.ext hh')
  have hGH : GHList ↥(Lh.map N.subtype) :=
    IVK.ghList_of_le_ne_top hG.kgh hN hsoc.le hsoc.simple hnonab
  refine h73 G N _ K Q (Gen4.subgroup N hG.gen4) hGH
    (hG.kproper.isKGroupNative_of_ne_top hN) hsoc hKlt.le hs.K_simple hKodd ?_
    hs.rankQ ?_
  · rwa [inf_eq_left.mpr hCKN]
  · intro y hy hy2 hyC
    have h1 := hs.terminal.2.2.2 y hy2 hyC
    rwa [inf_eq_left.mpr (hCN y hyC hy2)]

end CFSG.GH74.GLS
