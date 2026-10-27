module

public import CFSG.GH74.GLS.C3.Layer1.Th2Pump
public import CFSG.GH74.GLS.C3.Layer1.BkA7Facts
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsTransfer

public section

namespace CFSG.GH74.GLS.Th2.P43f

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1.Bk
  CFSG.GH74.GLS.C3.Layer1.Back CFSG.GH74.GLS.Th2 Equiv Equiv.Perm

variable {G : Type} [Group G] [Finite G] {x y : G} {K T S : Subgroup G}

theorem exists_pumpup_at_Q (hG : C3Hyp G) (hs : Th2Std x y K T S) {u : G} (hu : u ∈ CxK x K)
    (hu2 : orderOf u = 2) : ∃ M : Subgroup G, PumpUpLT 2 x K u M := by
  have hterm : IsTwoTerminal x K := hs.v2ss.isV2Triple.2.1
  have hR3 : 3 ≤ pRank 2 ↥(centralizer ({u} : Set G)) :=
    TwoThin.rankThreeCentralizers G hG.kproper.1 hG.kproper.2.1
      (by have := hG.pRank_eq_four; omega) u hu2
  exact TwoThin.exists_pumpup_of_involution hs.orderOf_x hu2 hs.comp hu.1 hu.2 hterm.1 hR3

theorem card_le_of_le_centralizer_Q (hG : C3Hyp G) (hs : Th2Std x y K T S)
    (e7 : kBar K ≃* alternatingGroup (Fin 7)) (hP2 : 2 ≤ pRank 2 ↥(T ⊓ K))
    {u : G} (hu : u ∈ T ⊓ CxK x K) (hu2 : orderOf u = 2)
    (huQ : ∀ q ∈ T ⊓ CxK x K, u * q = q * u) {W : Subgroup G} (hW : IsPGroup 2 ↥W)
    (hWu : W ≤ centralizer ({u} : Set G)) :
    Nat.card ↥W ≤ Nat.card ↥(T ⊓ CxK x K) * 16 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcen : CenterlessBar K := centerlessBar_of_A7 ⟨e7⟩
  have hterm : IsTwoTerminal x K := hs.v2ss.isV2Triple.2.1
  obtain ⟨M, hlt⟩ := exists_pumpup_at_Q hG hs hu.2 hu2
  obtain ⟨-, ⟨eMK⟩⟩ := hterm.2.1 u M hlt
  have hSylQM : IsSylowOf 2 (T ⊓ CxK x K) (CxK u M) :=
    hterm.2.2 (T ⊓ CxK x K) hs.sylow_Q u M hlt hu huQ
  have hM : IsPCompIn 2 (centralizer ({u} : Set G)) M := hlt.2.1.2.2
  have hcenM : CenterlessBar M := Th2.centerlessBar_of_equiv hcen eMK
  have hodd : ∀ X : Subgroup G, ¬ 2 ∣ Nat.card (pPrimeCore 2 ↥X) := by
    intro X
    rw [← even_iff_two_dvd, Nat.not_even_iff_odd]
    exact Nat.coprime_two_left.1 pPrimeCore_coprime_card
  have hrM2 : pRank 2 (kBar M) = pRank 2 ↥M :=
    CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd Nat.prime_two
      (pPrimeCore 2 ↥M) (hodd M)
  have hrK2 : pRank 2 (kBar K) = pRank 2 ↥K :=
    CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd Nat.prime_two
      (pPrimeCore 2 ↥K) (hodd K)
  have hrMK : pRank 2 (kBar M) = pRank 2 (kBar K) :=
    CFSG.RankThree.PartOne.Quotient36.pRank_congr_mulEquiv one_lt_two eMK
  have hK2 : 2 ≤ pRank 2 ↥K := hP2.trans (C3.Layer1.Back.pRank_mono' (inf_le_right : T ⊓ K ≤ K))
  have hrM : 2 ≤ pRank 2 ↥M := by omega
  have hnormM := hs.pumpup_normal hG hcen hP2 hu2 hM hcenM hrM hSylQM
  obtain ⟨ψ, hker, -⟩ := lemma113d_alt hM.1 hnormM (n := 7) (by norm_num) (by norm_num)
    (eMK.trans e7)
  have hker' : ψ.ker = (CxK u M).subgroupOf (centralizer ({u} : Set G)) := hker
  set f : ↥W →* Perm (Fin 7) := ψ.comp (Subgroup.inclusion hWu) with hf
  have hrangeP : IsPGroup 2 f.range := hW.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hrangeP
  have hdvd : Nat.card f.range ∣ 5040 := by
    have := Subgroup.card_subgroup_dvd_card f.range
    rwa [Nat.card_perm, Nat.card_fin] at this
  have hn4 : n ≤ 4 := by
    by_contra hcon
    push Not at hcon
    have h32 : 2 ^ 5 ∣ 2 ^ n := Nat.pow_dvd_pow 2 hcon
    rw [← hn] at h32
    have := h32.trans hdvd
    norm_num [Nat.factorial] at this
  have hrange16 : Nat.card f.range ≤ 16 := by
    rw [hn]
    calc 2 ^ n ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hn4
      _ = 16 := by norm_num
  have hkerle : Nat.card f.ker ≤ Nat.card ↥(T ⊓ CxK x K) := by
    have hkerf : f.ker = (W ⊓ CxK u M).subgroupOf W := by
      ext w
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      have h1 : ψ (Subgroup.inclusion hWu w) = 1 ↔ (w : G) ∈ CxK u M := by
        rw [← MonoidHom.mem_ker, hker', Subgroup.mem_subgroupOf]
        rfl
      show ψ (Subgroup.inclusion hWu w) = 1 ↔ _
      rw [h1]
      exact ⟨fun h => ⟨w.2, h⟩, fun h => h.2⟩
    rw [hkerf, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]
    have hFp : IsPGroup 2 ↥(W ⊓ CxK u M) := hW.to_le inf_le_left
    obtain ⟨g, -, hg⟩ := Th2.exists_cj_le_of_isSylowOf hSylQM inf_le_right hFp
    calc Nat.card ↥(W ⊓ CxK u M) = Nat.card ↥(cj g (W ⊓ CxK u M)) := by
          unfold cj
          exact (Subgroup.card_map_of_injective (MulAut.conj g).injective).symm
      _ ≤ Nat.card ↥(T ⊓ CxK x K) := Subgroup.card_le_of_le hg
  have hmul := Subgroup.card_ker_mul_card_range f
  calc Nat.card ↥W = Nat.card f.ker * Nat.card f.range := hmul.symm
    _ ≤ Nat.card ↥(T ⊓ CxK x K) * 16 := Nat.mul_le_mul hkerle hrange16

end CFSG.GH74.GLS.Th2.P43f
