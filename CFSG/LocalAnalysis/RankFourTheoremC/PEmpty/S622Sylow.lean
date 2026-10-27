module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614ExtDefs
import CFSG.Goldschmidt.Steps.G310Basic

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC (IsMaxTwoInvariantIn)

theorem s622_sylow_isSylowOf_of_fusion {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {S K : Subgroup G} (h : fusionIsSylowIn p S K) : CFSG.ABGLocalTools.IsSylowOf p S K :=
  CFSG.Goldschmidt.G310.exists_sylow_of_fusionIsSylowIn h

theorem s622_sylow_not_dvd_card_sup {G : Type} [Group G] [Finite G] {q r : ℕ} (hq : q.Prime)
    (hr : r.Prime) (hqr : q ≠ r) {P K : Subgroup G} (hP : IsPGroup q P)
    (hPK : P ≤ normalizer (K : Set G)) (hK : ¬ r ∣ Nat.card K) :
    ¬ r ∣ Nat.card (P ⊔ K : Subgroup G) := by
  haveI : Fact q.Prime := ⟨hq⟩
  set A : Subgroup G := P ⊔ K with hA
  have hPA : P ≤ A := le_sup_left
  have hKA : K ≤ A := le_sup_right
  have hAK : A ≤ normalizer (K : Set G) := sup_le hPK Subgroup.le_normalizer
  have hKn : (K.subgroupOf A).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hAK
  have htop : P.subgroupOf A ⊔ K.subgroupOf A = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hPA hKA, ← hA, Subgroup.subgroupOf_self]
  have hidx : (K.subgroupOf A).index = (K.subgroupOf A).relIndex (P.subgroupOf A) := by
    rw [← Subgroup.relIndex_sup_right (P.subgroupOf A) (K.subgroupOf A), htop,
      Subgroup.relIndex_top_right]
  have hdvd : (K.subgroupOf A).relIndex (P.subgroupOf A) ∣ Nat.card (P.subgroupOf A) :=
    Subgroup.relIndex_dvd_card _ _
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have hPcard : Nat.card (P.subgroupOf A) = q ^ n := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPA).toEquiv, hn]
  have hKcard : Nat.card (K.subgroupOf A) = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKA).toEquiv
  intro hrA
  rw [← Subgroup.index_mul_card (K.subgroupOf A), hKcard] at hrA
  rcases (Nat.Prime.dvd_mul hr).mp hrA with h | h
  · rw [hidx] at h
    have hrq : r ∣ q ^ n := h.trans (hPcard ▸ hdvd)
    exact hqr ((Nat.prime_dvd_prime_iff_eq hr hq).mp (hr.dvd_of_dvd_pow hrq)).symm
  · exact hK h

theorem s622_isSylowOf_inf {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {B H D S : Subgroup G} (hB : IsPGroup p B) (hDH : D ≤ H) (hDn : (D.subgroupOf H).Normal)
    (hpD : ¬ p ∣ Nat.card D) (hBD : B ≤ normalizer (D : Set G))
    (hS : IsMaxTwoInvariantIn B H S) :
    CFSG.ABGLocalTools.IsSylowOf 2 (S ⊓ D) D := by
  obtain ⟨⟨hSH, hS2, hBS⟩, hmax⟩ := hS
  have hHD : H ≤ normalizer (D : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDH).mp hDn
  have hSD : S ≤ normalizer (D : Set G) := hSH.trans hHD
  have hAD : S ⊔ D ≤ normalizer (D : Set G) := sup_le hSD Subgroup.le_normalizer
  have hBA : B ≤ normalizer ((S ⊔ D : Subgroup G) : Set G) :=
    CFSG.Goldschmidt.G310.le_normalizer_sup hBS hBD
  have hpA : ¬ p ∣ Nat.card (S ⊔ D : Subgroup G) :=
    s622_sylow_not_dvd_card_sup Nat.prime_two hp (Ne.symm hp2) hS2 hSD hpD
  obtain ⟨S', hS'syl, hSS', hBS'⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing hp
    Nat.prime_two hB hpA hBA le_sup_left hS2 hBS
  have hS'H : S' ≤ H := hS'syl.1.trans (sup_le hSH hDH)
  have hS'S : S' = S := hmax S' ⟨hS'H, hS'syl.2.1, hBS'⟩ hSS'
  rw [hS'S] at hS'syl
  exact (s622_sylow_isSylowOf_of_fusion hS'syl).inf_of_le_normalizer le_sup_right hAD

theorem s622_le_sup_normalizer {G : Type} [Group G] [Finite G] {q : ℕ} (hq : q.Prime)
    {H N W : Subgroup G} (hNH : N ≤ H) (hNn : (N.subgroupOf H).Normal)
    (hW : CFSG.ABGLocalTools.IsSylowOf q W N) :
    H ≤ N ⊔ (normalizer (W : Set G) ⊓ H) := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hWH : W ≤ H := hW.le.trans hNH
  have hW' : CFSG.ABGLocalTools.IsSylowOf q (W.subgroupOf H) (N.subgroupOf H) := by
    rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff H, Subgroup.subgroupOf_map_subtype,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hWH, inf_eq_left.mpr hNH]
    exact hW
  obtain ⟨Q, hQ⟩ := hW'
  have hfr := Sylow.normalizer_sup_eq_top Q
  rw [hQ] at hfr
  intro x hx
  have hx' : (⟨x, hx⟩ : H) ∈
      normalizer ((W.subgroupOf H : Subgroup H) : Set H) ⊔ N.subgroupOf H := by
    rw [hfr]
    trivial
  obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_right.mp hx'
  have hyW : (y : G) ∈ normalizer (W : Set G) := by
    have hy' : y ∈ (normalizer (W : Set G)).subgroupOf H := by
      rw [Subgroup.subgroupOf_normalizer_eq hWH]
      exact hy
    exact hy'
  have hxyz : x = (y : G) * (z : G) := congrArg Subtype.val hyz.symm
  rw [hxyz, sup_comm]
  exact Subgroup.mul_mem_sup (Subgroup.mem_inf.mpr ⟨hyW, y.2⟩) hz

theorem s622_exists_invariant_sylow_inf_ne_bot {G : Type} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) {B D M : Subgroup G} (hB : IsPGroup p B) (hpD : ¬ p ∣ Nat.card D)
    (hBD : B ≤ normalizer (D : Set G)) (hBM : B ≤ M) (hDodd : Odd (Nat.card D))
    (hDM : D ⊓ M ≠ ⊥) :
    ∃ (f : ℕ) (F : Subgroup G), f.Prime ∧ f ≠ 2 ∧ f ≠ p ∧
      CFSG.ABGLocalTools.IsSylowOf f F D ∧ B ≤ normalizer (F : Set G) ∧ F ⊓ M ≠ ⊥ := by
  have hE1 : Nat.card (D ⊓ M : Subgroup G) ≠ 1 := fun h => hDM (Subgroup.card_eq_one.mp h)
  obtain ⟨f, hf, hfE⟩ := Nat.exists_prime_and_dvd hE1
  haveI : Fact f.Prime := ⟨hf⟩
  have hfD : f ∣ Nat.card D := hfE.trans (Subgroup.card_dvd_of_le inf_le_left)
  have hpE : ¬ p ∣ Nat.card (D ⊓ M : Subgroup G) :=
    fun h => hpD (h.trans (Subgroup.card_dvd_of_le inf_le_left))
  have hBE : B ≤ normalizer ((D ⊓ M : Subgroup G) : Set G) :=
    CFSG.Goldschmidt.G310.le_normalizer_inf hBD (hBM.trans Subgroup.le_normalizer)
  have hbotp : IsPGroup f (⊥ : Subgroup G) := IsPGroup.of_card (n := 0) (by simp)
  obtain ⟨F₀, hF₀, -, hBF₀⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing hp hf hB
    hpE hBE bot_le hbotp (CFSG.Goldschmidt.G310.le_normalizer_of_normal (K := ⊥))
  have hF₀E : F₀ ≤ D ⊓ M := hF₀.1
  have hF₀ne : F₀ ≠ ⊥ := by
    intro h
    have hc := (s622_sylow_isSylowOf_of_fusion hF₀).card_eq
    rw [h, Subgroup.card_bot] at hc
    have hpos : 0 < (Nat.card (D ⊓ M : Subgroup G)).factorization f :=
      hf.factorization_pos_of_dvd Nat.card_pos.ne' hfE
    have hgt : 1 < f ^ (Nat.card (D ⊓ M : Subgroup G)).factorization f :=
      Nat.one_lt_pow hpos.ne' hf.one_lt
    omega
  obtain ⟨F, hFsyl, hF₀F, hBF⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing hp hf hB
    hpD hBD (hF₀E.trans inf_le_left) hF₀.2.1 hBF₀
  refine ⟨f, F, hf, fun h => hDodd.not_two_dvd_nat (h ▸ hfD), fun h => hpD (h ▸ hfD),
    s622_sylow_isSylowOf_of_fusion hFsyl, hBF, fun h => hF₀ne ?_⟩
  exact le_bot_iff.mp (h ▸ le_inf hF₀F (hF₀E.trans inf_le_right))

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
