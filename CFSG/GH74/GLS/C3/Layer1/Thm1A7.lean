module

public import CFSG.GH74.GLS.C3.Layer1.Thm1A7Two
public import CFSG.GH74.GLS.C3.Layer1.Th2P64A
public import CFSG.GH74.GLS.C3.Layer1.Thm1P31

public section

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1
  CFSG.GH74.GLS.C3.Layer1.Thm1 CFSG.GH74.GLS.C3.Layer1.Thm1G33

namespace CFSG.GH74.GLS

theorem b_thm1_A7_any_proved
    (hGKF : CFSG.GH74.Generic.GenericKnownFacts) (hE2 : CFSG.GH74.E2.E2ComponentFacts)
    (hL34 : B_gen4_noL34_elem) (hS34 : P34.S_prop34) : B_thm1_A7_any := by
  classical
  intro G _ _ hG x y K hu2 e7 h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hrk : 2 ≤ pRank 2 ↥(CxK x K)
  · exact Or.inl hrk
  right
  have hrk' : pRank 2 ↥(CxK x K) ≤ 1 := by omega
  obtain ⟨T, hT⟩ := Thm1.exists_setup1D x K
  obtain ⟨f, z, E⟩ := Thm1A7.exists_a7env hG hu2 e7 hrk' hT
  have hCxN : ∀ c ∈ centralizer ({x} : Set G), ∀ q ∈ CxK x K, c * q * c⁻¹ ∈ CxK x K :=
    fun c hc q hq => P34Real.CMK_conj E.hKN hc hq
  have hQsyl : IsSylowOf 2 (T ⊓ CxK x K) (CxK x K) :=
    hT.sylowT.inf_of_le_normalizer (fun q hq => hq.1)
      (fun c hc => U1a.mem_normalizer_of_norm hCxN hc)
  have hQ3 : 2 < Nat.card ↥(T ⊓ CxK x K) := by
    rw [hQsyl.card_eq]
    exact h2
  obtain ⟨S, hS, hTS'⟩ := EvenSporTransfer.exists_isSylowOf_ge (N := (⊤ : Subgroup G)) (A := T)
    le_top hT.sylowT.isPGroup
  have hS2 : IsPGroup 2 ↥S := hS.isPGroup
  have hTne : T ≠ S := by
    intro hTS
    subst hTS
    have hidx : ¬ 2 ∣ T.index := by
      have := (isSylowOf_iff.1 hS).2.2
      rwa [Subgroup.relIndex_top_right] at this
    have hcen : CFSG.GH74.IsCentralInvolution x := by
      refine ⟨E.hu2.1.1.1, hS2.toSylow hidx, ?_, ?_⟩
      · rw [IsPGroup.toSylow_coe]
        exact E.hxT
      · rw [IsPGroup.toSylow_coe]
        intro s hs
        exact (mem_centralizer_singleton_iff.1 (E.hTC hs))
    have hyp : P34.Prop34Hyp G x K :=
      { simple := hG.kproper.1
        nonab := hG.kproper.2.1
        central := hcen
        comp := hu2.1.1.2
        unique := Thm1A7.unique_of_rank_le_one hGKF hE2 hL34 hG hrk' hu2
        shape := Or.inr e7
        sylowQ := Thm1.exists_Q_of_card_le_two (Thm1A7.card_le_two_of_rank_le_one hrk') }
    exact hS34 G x K hyp f E.hfC E.hf2 E.hind
  have hTS : T < S := lt_of_le_of_ne hTS' hTne
  obtain ⟨b, hbS, hbN, hbT⟩ := exists_mem_normalizer_not_mem hTS.le hTS.ne hS2
  have hb2 : ∃ k : ℕ, b ^ (2 ^ k) = 1 := by
    obtain ⟨k, hk⟩ := hS2 ⟨b, hbS⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  obtain ⟨a, ha, haT, ha2⟩ := exists_pow_not_mem_sq_mem hb2 hbT
  have haS : a ∈ S := (zpowers_le).2 hbS ha
  have haN : a ∈ normalizer (T : Set G) := (zpowers_le).2 hbN ha
  have hxa : a * x * a⁻¹ ≠ x := by
    intro h
    have hac : a ∈ centralizer ({x} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      calc a * x = a * x * a⁻¹ * a := by group
        _ = x * a := by rw [h]
    have hN₂C : T ⊔ zpowers a ≤ centralizer ({x} : Set G) :=
      sup_le E.hTC ((zpowers_le).2 hac)
    have hN₂S : T ⊔ zpowers a ≤ S := sup_le hTS.le ((zpowers_le).2 haS)
    have hN₂ : IsPGroup 2 ↥(T ⊔ zpowers a) := hS2.to_le hN₂S
    have heq := hT.sylowT.eq_of_le le_sup_left hN₂C hN₂
    exact haT (heq ▸ Subgroup.mem_sup_right (mem_zpowers a))
  exact E.exceptional_of hS hTS haS haN haT ha2 hxa hQ3

end CFSG.GH74.GLS

end
