module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.U6Model

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSFourU

open CFSG.Open CFSG.HardMathSupport.Dickson.I271 Bal209F4Aux
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87 (innSub)

theorem actHom_mem_innSub_of_innerAt {X : Type} [Group X] {K : Subgroup X} {b : X}
    (hb : b ∈ Subgroup.normalizer (K : Set X)) (hin : InnerAt K b) :
    actHom K ⟨b, hb⟩ ∈ innSub (↥K ⧸ Subgroup.center ↥K) := by
  obtain ⟨k, hk, c, hc, rfl⟩ := Bal209F4Aux.innerAt_iff.1 hin
  rw [actHom_eq_conj_of_mul hk hc hb]
  exact ⟨_, rfl⟩

theorem actPre_autImage_eq {X : Type} [Group X] {B K : Subgroup X}
    (hBN : B ≤ Subgroup.normalizer (K : Set X)) : actPre B K (autImage B K) = B :=
  le_antisymm actPre_le_left fun x hx =>
    mem_actPre.2 ⟨hBN hx, hx, mem_autImage.2 ⟨x, hBN hx, hx, rfl⟩⟩

theorem card_autImage_le_three_mul {X : Type} [Group X] [Finite X] {K B : Subgroup X}
    (hBN : B ≤ Subgroup.normalizer (K : Set X)) {x : X} (hx : x ∈ B) (hx3 : x ^ 3 = 1)
    (hdec : ∀ b ∈ B, ∃ i : ℕ, InnerAt K (x ^ i * b)) :
    Nat.card ↥(autImage B K) ≤
      3 * Nat.card ↥(autImage B K ⊓ innSub (↥K ⧸ Subgroup.center ↥K)) := by
  have hgP : actHom K ⟨x, hBN hx⟩ ∈ autImage B K := mem_autImage.2 ⟨x, hBN hx, hx, rfl⟩
  have hg3 : actHom K ⟨x, hBN hx⟩ ^ 3 = 1 := by
    rw [← map_pow, show (⟨x, hBN hx⟩ : ↥(Subgroup.normalizer (K : Set X))) ^ 3 = 1 from
      Subtype.ext hx3, map_one]
  have hzc : Nat.card ↥(Subgroup.zpowers (actHom K ⟨x, hBN hx⟩)) ≤ 3 := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hg3)
  let F : ↥(Subgroup.zpowers (actHom K ⟨x, hBN hx⟩)) ×
      ↥(autImage B K ⊓ innSub (↥K ⧸ Subgroup.center ↥K)) → ↥(autImage B K) :=
    fun pq => ⟨(pq.1 : MulAut (↥K ⧸ Subgroup.center ↥K)) * pq.2,
      Subgroup.mul_mem _ (Subgroup.zpowers_le.2 hgP pq.1.2) (Subgroup.mem_inf.1 pq.2.2).1⟩
  have hF : Function.Surjective F := by
    rintro ⟨e, he⟩
    obtain ⟨b, hbN, hbB, hbe⟩ := mem_autImage.1 he
    obtain ⟨i, hi⟩ := hdec b hbB
    have hyN : x ^ i * b ∈ Subgroup.normalizer (K : Set X) :=
      Subgroup.mul_mem _ (Subgroup.pow_mem _ (hBN hx) i) hbN
    have hyB : x ^ i * b ∈ B := B.mul_mem (B.pow_mem hx i) hbB
    have hsplit : actHom K ⟨x ^ i * b, hyN⟩ = actHom K ⟨x, hBN hx⟩ ^ i * e := by
      rw [← hbe, ← map_pow, ← map_mul]
      congr 1
    refine ⟨(⟨(actHom K ⟨x, hBN hx⟩ ^ i)⁻¹,
        Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) i)⟩,
      ⟨actHom K ⟨x ^ i * b, hyN⟩, Subgroup.mem_inf.2
        ⟨mem_autImage.2 ⟨x ^ i * b, hyN, hyB, rfl⟩, actHom_mem_innSub_of_innerAt hyN hi⟩⟩),
      Subtype.ext ?_⟩
    show (actHom K ⟨x, hBN hx⟩ ^ i)⁻¹ * actHom K ⟨x ^ i * b, hyN⟩ = e
    rw [hsplit, inv_mul_cancel_left]
  have hcard : Nat.card ↥(autImage B K) ≤
      Nat.card ↥(Subgroup.zpowers (actHom K ⟨x, hBN hx⟩)) *
        Nat.card ↥(autImage B K ⊓ innSub (↥K ⧸ Subgroup.center ↥K)) := by
    rw [← Nat.card_prod]
    exact Nat.card_le_card_of_surjective F hF
  exact hcard.trans (Nat.mul_le_mul_right _ hzc)

theorem card_innerPart_ge {X : Type} [Group X] [Finite X] {K B : Subgroup X}
    (hperf : commutator ↥K = ⊤) (hBel : IsElemAbelian 3 B)
    (hBN : B ≤ Subgroup.normalizer (K : Set X)) {x : X} (hx : x ∈ B) (hxI : ¬ InnerAt K x)
    (hdec : ∀ b ∈ B, ∃ i : ℕ, InnerAt K (x ^ i * b)) {r : ℕ}
    (hr : CFSG.Open.pRank 3 (B ⊓ Subgroup.centralizer (K : Set X) : Subgroup X) + (r + 1) ≤
      CFSG.Open.pRank 3 B) :
    3 ^ r ≤ Nat.card ↥(autImage B K ⊓ innSub (↥K ⧸ Subgroup.center ↥K)) := by
  have hCel : IsElemAbelian 3 (B ⊓ Subgroup.centralizer (K : Set X) : Subgroup X) :=
    CFSG.Open.IsElemAbelian.mono hBel inf_le_left
  have hcardB : Nat.card ↥B = Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set X) : Subgroup X) *
      Nat.card ↥(autImage B K) := by
    have h := card_actPre hperf (le_refl (autImage B K))
    rwa [actPre_autImage_eq hBN] at h
  have hB3 := Bal209TwoAux.card_eq_pow_pRank Nat.prime_three hBel
  have hC3 := Bal209TwoAux.card_eq_pow_pRank Nat.prime_three hCel
  have hP := card_autImage_le_three_mul hBN hx (hBel.2 x hx) hdec
  set c := CFSG.Open.pRank 3 (B ⊓ Subgroup.centralizer (K : Set X) : Subgroup X)
  set m := CFSG.Open.pRank 3 B
  have h1 : 3 ^ (c + (r + 1)) ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) hr
  have h2 : 3 ^ m = 3 ^ c * Nat.card ↥(autImage B K) := by
    rw [← hB3, hcardB, hC3]
  have h3 : 3 ^ c * 3 ^ (r + 1) ≤ 3 ^ c * Nat.card ↥(autImage B K) := by
    rw [← pow_add, ← h2]
    exact h1
  have h4 := Nat.le_of_mul_le_mul_left h3 (pow_pos (by norm_num) _)
  rw [pow_succ] at h4
  omega

end KSFourU

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

end
