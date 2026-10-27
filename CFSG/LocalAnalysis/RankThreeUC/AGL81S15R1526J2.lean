module

import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1526P0c
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.RankThree.PartOne.S12.InputsSec15

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open Subgroup KFactsPair
open scoped commutatorElement

section Row28NonG

variable {G : Type} [Group G] [Finite G]

theorem gamma_D_le_M_aux1 {Y : Type} [Group Y] {A B : Subgroup Y}
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : Y} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  let P : Subgroup Y :=
    { carrier := {y | ∃ a ∈ A, ∃ b ∈ B, y = a * b}
      mul_mem' := by
        rintro _ _ ⟨a₁, ha₁, b₁, hb₁, rfl⟩ ⟨a₂, ha₂, b₂, hb₂, rfl⟩
        refine ⟨a₁ * a₂, A.mul_mem ha₁ ha₂, b₁ * b₂, B.mul_mem hb₁ hb₂, ?_⟩
        calc a₁ * b₁ * (a₂ * b₂) = a₁ * (b₁ * a₂) * b₂ := by group
          _ = a₁ * (a₂ * b₁) * b₂ := by rw [← h a₂ ha₂ b₁ hb₁]
          _ = a₁ * a₂ * (b₁ * b₂) := by group
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, (one_mul 1).symm⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
        have hc : a * b = b * a := h a ha b hb
        calc (a * b)⁻¹ = (b * a)⁻¹ := by rw [hc]
          _ = a⁻¹ * b⁻¹ := by group }
  have hAP : A ≤ P := fun a ha => ⟨a, ha, 1, B.one_mem, (mul_one a).symm⟩
  have hBP : B ≤ P := fun b hb => ⟨1, A.one_mem, b, hb, (one_mul b).symm⟩
  exact sup_le hAP hBP hx

theorem gamma_D_le_M_aux2 {Y : Type} [Group Y] {Q A B : Subgroup Y}
    (h : ∀ q ∈ Q, q ∈ A ∨ q ∈ B) : Q ≤ A ∨ Q ≤ B := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hQA, hQB⟩ := hcon
  rw [SetLike.not_le_iff_exists] at hQA hQB
  obtain ⟨q₁, hq₁Q, hq₁A⟩ := hQA
  obtain ⟨q₂, hq₂Q, hq₂B⟩ := hQB
  have hq₁B : q₁ ∈ B := (h q₁ hq₁Q).resolve_left hq₁A
  have hq₂A : q₂ ∈ A := (h q₂ hq₂Q).resolve_right hq₂B
  rcases h (q₂ * q₁) (Q.mul_mem hq₂Q hq₁Q) with hm | hm
  · exact hq₁A (by simpa using A.mul_mem (A.inv_mem hq₂A) hm)
  · exact hq₂B (by simpa using B.mul_mem hm (B.inv_mem hq₁B))

theorem gamma_D_le_M_aux3 {Y : Type} [Group Y] [Finite Y] {Q : Subgroup Y}
    (h : 1 ≤ CFSG.Open.pRank 3 Q) : Q ≠ ⊥ := by
  obtain ⟨E, hEQ, -, hcard⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) Q
  intro hQ
  have hE : E = ⊥ := by rw [hQ] at hEQ; exact le_bot_iff.1 hEQ
  rw [hE, Subgroup.card_bot] at hcard
  have h1 : 1 < 3 ^ CFSG.Open.pRank 3 Q := Nat.one_lt_pow (by omega) (by norm_num)
  omega

theorem gamma_D_le_M_aux4 {Y : Type} [Group Y] [Finite Y] {Q K : Subgroup Y} (hK : Nat.card K = 3)
    (hQK : Q ≤ K) (hQ : Q ≠ ⊥) : Q = K := by
  have hdvd : Nat.card Q ∣ 3 := hK ▸ Subgroup.card_dvd_of_le hQK
  have hne : Nat.card Q ≠ 1 := fun h => hQ (Subgroup.card_eq_one.1 h)
  have h3 : Nat.card Q = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
    · exact absurd h hne
    · exact h
  exact Subgroup.eq_of_le_of_card_ge hQK (by omega)

theorem gamma_D_le_M_aux5 {M : Subgroup G} {x : ↥M} (hx : orderOf x = 7) {S : Set G}
    (hxS : ∀ s ∈ S, (x : G) * s = s * (x : G)) :
    7 ∣ Nat.card ↥(M ⊓ Subgroup.centralizer S) := by
  have hle : Subgroup.zpowers (x : G) ≤ M ⊓ Subgroup.centralizer S := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.mem_inf.2 ⟨x.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hxS y hy).symm
  have hc : Nat.card (Subgroup.zpowers (x : G)) = 7 := by
    rw [Nat.card_zpowers]
    have : orderOf (x : G) = orderOf x := Subgroup.orderOf_coe x
    rw [this, hx]
  rw [← hc]
  exact Subgroup.card_dvd_of_le hle

theorem gamma_D_le_M_gen {M : Subgroup G}
    (hs7 : CFSG.RankThree.PartOne.IsStronglyPEmbedded 7 M) {A B : Subgroup ↥M}
    (hA3 : Nat.card A = 3) (hB3 : Nat.card B = 3)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hAB1 : ∀ x ∈ A ⊓ B, x = 1)
    (hNA : Subgroup.normalizer ((A.map M.subtype : Subgroup G) : Set G) ≤ M)
    (hNB : Subgroup.normalizer ((B.map M.subtype : Subgroup G) : Set G) ≤ M)
    (hC : ∀ a ∈ A, a ≠ 1 → ∀ b ∈ B, b ≠ 1 →
      Subgroup.centralizer ({((a * b : ↥M) : G)} : Set G) ≤ M)
    (hx : ∃ x : ↥M, orderOf x = 7 ∧ (∀ a ∈ A, x * a = a * x) ∧ ∀ b ∈ B, x * b = b * x) :
    CFSG.Open.rankThreeGamma 1 3 ((A ⊔ B).map M.subtype) ≤ M := by
  obtain ⟨x, hx7, hxA, hxB⟩ := hx
  have hxD : ∀ m ∈ A ⊔ B, x * m = m * x := by
    have hle : A ⊔ B ≤ Subgroup.centralizer ({x} : Set ↥M) := by
      refine sup_le (fun a ha => ?_) (fun b hb => ?_)
      · rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff.1 hh]
        exact hxA a ha
      · rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff.1 hh]
        exact hxB b hb
    intro m hm
    exact Subgroup.mem_centralizer_iff.1 (hle hm) x (Set.mem_singleton x)
  have hA'3 : Nat.card (A.map M.subtype) = 3 := by
    rw [Subgroup.card_map_of_injective M.subtype_injective]; exact hA3
  have hB'3 : Nat.card (B.map M.subtype) = 3 := by
    rw [Subgroup.card_map_of_injective M.subtype_injective]; exact hB3
  unfold CFSG.Open.rankThreeGamma CFSG.Open.GLBCore
  refine sSup_le ?_
  rintro N ⟨Q, hQD, hQ1, rfl⟩
  have hQne : Q ≠ ⊥ := gamma_D_le_M_aux3 hQ1
  by_cases hU : ∀ q ∈ Q, q ∈ A.map M.subtype ∨ q ∈ B.map M.subtype
  · rcases gamma_D_le_M_aux2 hU with hQA | hQB
    · rw [gamma_D_le_M_aux4 hA'3 hQA hQne]
      exact hNA
    · rw [gamma_D_le_M_aux4 hB'3 hQB hQne]
      exact hNB
  · push Not at hU
    obtain ⟨q, hqQ, hqA, hqB⟩ := hU
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 (hQD hqQ)
    obtain ⟨a, ha, b, hb, rfl⟩ := gamma_D_le_M_aux1 hAB hm
    have ha1 : a ≠ 1 := by
      rintro rfl
      exact hqB ⟨b, hb, by simp⟩
    have hb1 : b ≠ 1 := by
      rintro rfl
      exact hqA ⟨a, ha, by simp⟩
    have hcent : Subgroup.centralizer (Q : Set G) ≤ M :=
      (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hqQ)).trans (hC a ha ha1 b hb hb1)
    refine normalizer_le_of_centralizer_le hs7 hcent (gamma_D_le_M_aux5 hx7 ?_)
    intro s hs
    obtain ⟨m', hm', rfl⟩ := Subgroup.mem_map.1 (hQD hs)
    exact congrArg Subtype.val (hxD m' hm')

end Row28NonG

end CFSG.LocalAnalysis.RankThreeUC.S15
