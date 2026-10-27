module

public import CFSG.CGT.PushingUpLit.SolK.Basics
public import CFSG.CGT.PushingUpLit.SolK.Block

public section

namespace CFSG.CGT.PushingUpLit.SolK

open CFSG CFSG.Assembly
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_mem_normalizer_of_lt {A T : Subgroup G} (hT : IsPGroup 2 T) (hAT : A ≤ T)
    (hne : A ≠ T) : ∃ t ∈ T, t ∉ A ∧ t ∈ Subgroup.normalizer (A : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let IP : Subgroup T := A.subgroupOf T
  have hIPne : IP ≠ ⊤ := by
    intro htop
    apply hne
    refine le_antisymm hAT fun x hx => ?_
    have : (⟨x, hx⟩ : T) ∈ IP := by rw [htop]; trivial
    exact Subgroup.mem_subgroupOf.1 this
  have hIPlt : IP < ⊤ := lt_of_le_of_ne le_top hIPne
  have : Group.IsNilpotent T := hT.isNilpotent
  have hnc : NormalizerCondition T := Group.normalizerCondition_of_isNilpotent (G := T)
  have hlt : IP < Subgroup.normalizer (IP : Set T) := hnc IP hIPlt
  obtain ⟨x, hxN, hxnotIP⟩ := IsConcreteLE.exists_of_lt hlt
  refine ⟨(x : G), x.2, fun hxA => hxnotIP (Subgroup.mem_subgroupOf.2 hxA), ?_⟩
  have hxsub : x ∈ (Subgroup.normalizer (A : Set G)).subgroupOf T := by
    rw [Subgroup.subgroupOf_normalizer_eq hAT]
    exact hxN
  exact Subgroup.mem_subgroupOf.1 hxsub

omit [Finite G] in
theorem pCoreOf_normalized_of_normal {K N : Subgroup G}
    (hnorm : ∀ n ∈ N, ∀ k ∈ K, n * k * n⁻¹ ∈ K) {n : G} (hn : n ∈ N) {p : G}
    (hp : p ∈ pCoreOf 2 K) : n * p * n⁻¹ ∈ pCoreOf 2 K := by
  let P : Subgroup G := (pCoreOf 2 K).map (MulAut.conj n).toMonoidHom
  have hPK : P ≤ K := by
    rintro _ ⟨z, hz, rfl⟩
    exact hnorm n hn z (pCoreOf_le_self K hz)
  have hP2 : IsPGroup 2 P := (isPGroup_pCoreOf' K).map (MulAut.conj n).toMonoidHom
  have hPnorm : ∀ k ∈ K, ∀ z ∈ P, k * z * k⁻¹ ∈ P := by
    rintro k hk _ ⟨z, hz, rfl⟩
    have h1 : n⁻¹ * k * n ∈ K := by
      have := hnorm n⁻¹ (N.inv_mem hn) k hk
      simpa using this
    refine ⟨(n⁻¹ * k * n) * z * (n⁻¹ * k * n)⁻¹, pCoreOf_normalized K h1 hz, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]
  exact le_pCoreOf_of_normalized hPK hPnorm hP2 ⟨p, hp, rfl⟩

theorem exists_isMaximalTwoLocal_ge {H : Subgroup G} (hH : IsPLocal 2 H) :
    ∃ M, IsMaximalTwoLocal M ∧ H ≤ M := by
  classical
  obtain ⟨K, hK, hmax⟩ := Set.exists_max_image {K : Subgroup G | IsPLocal 2 K ∧ H ≤ K}
    (fun K => Nat.card K) (Set.toFinite _) ⟨H, hH, le_rfl⟩
  refine ⟨K, ⟨hK.1, fun H' hKH' hH'loc => ?_⟩, hK.2⟩
  have h1 := hmax H' ⟨hH'loc, hK.2.trans hKH'.le⟩
  exact absurd (Subgroup.card_lt_of_lt hKH') (not_lt.2 h1)

theorem local_le_of_unique {M : Subgroup G} {X : Subgroup G}
    (hu : maximalTwoLocalsContaining (X : Set G) = {M}) {H : Subgroup G} (hH : IsPLocal 2 H)
    (hXH : X ≤ H) : H ≤ M := by
  obtain ⟨M', hM', hHM'⟩ := exists_isMaximalTwoLocal_ge hH
  have : M' ∈ maximalTwoLocalsContaining (X : Set G) := ⟨hM', fun x hx => hHM' (hXH hx)⟩
  rw [hu] at this
  rw [← Set.mem_singleton_iff.1 this]
  exact hHM'

omit [Finite G] in
theorem centralizer_normalized {B : Subgroup G} {n : G} (hn : n ∈ Subgroup.normalizer (B : Set G))
    {k : G} (hk : k ∈ Subgroup.centralizer (B : Set G)) :
    n * k * n⁻¹ ∈ Subgroup.centralizer (B : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hk ⊢
  intro b hb
  have hb' : n⁻¹ * b * n ∈ B := by
    have := (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer (B : Set G)).inv_mem hn) b).1 hb
    simpa using this
  have h1 := hk _ hb'
  calc b * (n * k * n⁻¹) = n * ((n⁻¹ * b * n) * k) * n⁻¹ := by group
    _ = n * (k * (n⁻¹ * b * n)) * n⁻¹ := by rw [h1]
    _ = n * k * n⁻¹ * b := by group

theorem centralizer_two_constrained (hchar : IsCharTwoType G) {B : Subgroup G} (hB : B ≠ ⊥)
    (hB2 : IsPGroup 2 B) :
    Subgroup.centralizer (B : Set G) ⊓ Subgroup.centralizer
        (pCoreOf 2 (Subgroup.centralizer (B : Set G)) : Set G) ≤
      pCoreOf 2 (Subgroup.centralizer (B : Set G)) := by
  classical
  set N : Subgroup G := Subgroup.normalizer (B : Set G) with hN
  set K : Subgroup G := Subgroup.centralizer (B : Set G) with hK
  set P : Subgroup G := pCoreOf 2 K with hP
  set S : Subgroup G := pCoreOf 2 N with hS
  have hKN : K ≤ N := Subgroup.centralizer_le_normalizer (B : Set G)
  have hNloc : IsTwoLocal N := ⟨B, hB, hB2, rfl⟩
  have hcN : N ⊓ Subgroup.centralizer (S : Set G) ≤ S := hchar N hNloc
  have hKnorm : ∀ n ∈ N, ∀ k ∈ K, n * k * n⁻¹ ∈ K := fun n hn k hk => centralizer_normalized hn hk
  have hPnorm : ∀ n ∈ N, ∀ p ∈ P, n * p * n⁻¹ ∈ P := fun n hn p hp =>
    pCoreOf_normalized_of_normal hKnorm hn hp
  have hSnorm : ∀ n ∈ N, ∀ s ∈ S, n * s * n⁻¹ ∈ S := fun n hn s hs => pCoreOf_normalized N hn hs
  have hPS : P ≤ S := le_pCoreOf_of_normalized (((pCoreOf_le_self K).trans hKN))
    hPnorm (isPGroup_pCoreOf' K)
  have hKSP : K ⊓ S ≤ P := by
    refine le_pCoreOf_of_normalized inf_le_left (fun k hk z hz => ?_)
      (isPGroup_of_le (isPGroup_pCoreOf' N) inf_le_right)
    exact Subgroup.mem_inf.2 ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hk hz.1) (K.inv_mem hk),
      hSnorm k (hKN hk) z hz.2⟩
  intro c hc
  obtain ⟨hcK, hcP⟩ := Subgroup.mem_inf.1 hc
  let H : Subgroup G := K ⊓ Subgroup.centralizer (P : Set G)
  have hHN : ∀ n ∈ N, ∀ h ∈ H, n * h * n⁻¹ ∈ H := by
    intro n hn h hh
    refine Subgroup.mem_inf.2 ⟨hKnorm n hn h hh.1, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    have hp' : n⁻¹ * p * n ∈ P := by
      have := hPnorm n⁻¹ (N.inv_mem hn) p hp
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.1 hh.2 _ hp'
    calc p * (n * h * n⁻¹) = n * ((n⁻¹ * p * n) * h) * n⁻¹ := by group
      _ = n * (h * (n⁻¹ * p * n)) * n⁻¹ := by rw [h1]
      _ = n * h * n⁻¹ * p := by group
  have hH2 : ∀ h ∈ H, ∃ k : ℕ, h ^ (2 ^ k) = 1 := by
    intro h hh
    have hhN : h ∈ N := hKN hh.1
    have hcomm : ∀ s ∈ S, ⁅s, h⁆ ∈ P := by
      intro s hs
      have h1 : ⁅s, h⁆ ∈ H := by
        have : ⁅s, h⁆ = (s * h * s⁻¹) * h⁻¹ := by simp only [commutatorElement_def]
        rw [this]
        exact Subgroup.mul_mem _ (hHN s (pCoreOf_le_self N hs) h hh) (H.inv_mem hh)
      have h2 : ⁅s, h⁆ ∈ S := by
        have : ⁅s, h⁆ = s * (h * s⁻¹ * h⁻¹) := by simp only [commutatorElement_def]; group
        rw [this]
        exact Subgroup.mul_mem _ hs (hSnorm h hhN s⁻¹ (S.inv_mem hs))
      exact hKSP ⟨h1.1, h2⟩
    have hpow : ∀ k : ℕ, ∀ s ∈ S, h ^ k * s * (h ^ k)⁻¹ = (⁅h, s⁆ ^ k) * s := by
      intro k s hs
      have hz : ⁅h, s⁆ ∈ P := by
        rw [← commutator_inv' s h]
        exact P.inv_mem (hcomm s hs)
      induction k with
      | zero => simp
      | succ k ih =>
        have hzc : h * ⁅h, s⁆ * h⁻¹ = ⁅h, s⁆ := by
          have := Subgroup.mem_centralizer_iff.1 hh.2 _ hz
          rw [← this, mul_inv_cancel_right]
        calc h ^ (k + 1) * s * (h ^ (k + 1))⁻¹
            = h * (h ^ k * s * (h ^ k)⁻¹) * h⁻¹ := by group
          _ = h * (⁅h, s⁆ ^ k * s) * h⁻¹ := by rw [ih]
          _ = (h * ⁅h, s⁆ * h⁻¹) ^ k * (h * s * h⁻¹) := by rw [conj_pow]; group
          _ = ⁅h, s⁆ ^ k * (⁅h, s⁆ * s) := by rw [hzc, conj_eq_commutator_mul]
          _ = ⁅h, s⁆ ^ (k + 1) * s := by rw [pow_succ, mul_assoc]
    obtain ⟨a, ha⟩ := (IsPGroup.iff_card.1 (isPGroup_pCoreOf' K)).imp fun a ha => ha
    have hcardP : Nat.card P = 2 ^ a := ha
    have hzpow : ∀ s ∈ S, ⁅h, s⁆ ^ (2 ^ a) = 1 := by
      intro s hs
      have hz : ⁅h, s⁆ ∈ P := by
        rw [← commutator_inv' s h]
        exact P.inv_mem (hcomm s hs)
      have := pow_card_eq_one' (G := ↥P) (x := (⟨⁅h, s⁆, hz⟩ : ↥P))
      rw [hcardP] at this
      exact congrArg Subtype.val this
    have hcent : h ^ (2 ^ a) ∈ Subgroup.centralizer (S : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      have := hpow (2 ^ a) s hs
      rw [hzpow s hs, one_mul] at this
      exact (mul_inv_eq_iff_eq_mul.1 this).symm
    have hpS : h ^ (2 ^ a) ∈ S := hcN ⟨N.pow_mem hhN _, hcent⟩
    have hpK : h ^ (2 ^ a) ∈ K := K.pow_mem hh.1 _
    have hpP : h ^ (2 ^ a) ∈ P := hKSP ⟨hpK, hpS⟩
    obtain ⟨b, hb⟩ := (isPGroup_pCoreOf' K) ⟨h ^ (2 ^ a), hpP⟩
    refine ⟨a + b, ?_⟩
    have := congrArg Subtype.val hb
    simpa [pow_add, pow_mul] using this
  have hH2' : IsPGroup 2 H := fun h => by
    obtain ⟨k, hk⟩ := hH2 h h.2
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  have hHS : H ≤ S := le_pCoreOf_of_normalized (inf_le_left.trans hKN) hHN hH2'
  exact hKSP ⟨hcK, hHS ⟨hcK, hcP⟩⟩

end CFSG.CGT.PushingUpLit.SolK
