module

import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction
import CFSG.LocalAnalysis.SignalizerFunctor.TwoPrimeOrderSolvability
public import CFSG.LocalAnalysis.AGLEmbedding.Signalizer

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers

section Derived

variable {X X' : Type*} [Group X] [Group X']

def iterCommutator (A : Subgroup X) : ℕ → Subgroup X
  | 0 => A
  | n + 1 => ⁅iterCommutator A n, iterCommutator A n⁆

theorem iterCommutator_map (f : X →* X') (A : Subgroup X) (n : ℕ) :
    (iterCommutator A n).map f = iterCommutator (A.map f) n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [iterCommutator, Subgroup.map_commutator, ih]

theorem iterCommutator_succ_le (A : Subgroup X) (n : ℕ) :
    iterCommutator A (n + 1) ≤ iterCommutator A n := by
  refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)

theorem iterCommutator_le (A : Subgroup X) (n : ℕ) : iterCommutator A n ≤ A := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact (iterCommutator_succ_le A n).trans ih

theorem le_iterCommutator_of_commutator_eq {Y A : Subgroup X} (hY : ⁅Y, Y⁆ = Y) (hYA : Y ≤ A)
    (n : ℕ) : Y ≤ iterCommutator A n := by
  induction n with
  | zero => exact hYA
  | succ n ih =>
    calc Y = ⁅Y, Y⁆ := hY.symm
      _ ≤ ⁅iterCommutator A n, iterCommutator A n⁆ := Subgroup.commutator_mono ih ih

theorem exists_iterCommutator_eq_bot (A : Subgroup X) [Group.IsSolvable A] :
    ∃ n, iterCommutator A n = ⊥ := by
  obtain ⟨n, hn⟩ := Group.IsSolvable.solvable (G := A)
  have key : ∀ k, (derivedSeries A k).map A.subtype = iterCommutator A k := by
    intro k
    induction k with
    | zero =>
      rw [derivedSeries_zero, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
      rfl
    | succ k ih =>
      rw [derivedSeries_succ, Subgroup.map_commutator, ih]
      rfl
  exact ⟨n, by rw [← key, hn, Subgroup.map_bot]⟩

theorem exists_iterCommutator_perfect [Finite X] (A : Subgroup X) :
    ∃ n, ⁅iterCommutator A n, iterCommutator A n⁆ = iterCommutator A n := by
  by_contra hne
  simp only [not_exists] at hne
  have hlt : ∀ n, Nat.card (iterCommutator A (n + 1)) < Nat.card (iterCommutator A n) := by
    intro n
    have hle := iterCommutator_succ_le A n
    exact lt_of_le_of_ne (Subgroup.card_le_of_le hle) fun heq =>
      hne n (Subgroup.eq_of_le_of_card_ge hle heq.ge)
  have hbound : ∀ n, Nat.card (iterCommutator A n) + n ≤ Nat.card A := by
    intro n
    induction n with
    | zero => exact le_refl _
    | succ n ih => have := hlt n; omega
  have h1 := hbound (Nat.card A)
  have h2 : 0 < Nat.card (iterCommutator A (Nat.card A)) := Nat.card_pos
  omega

end Derived

theorem isSolvable_normalizer_of_card_eq_nine {X : Type*} [Group X] [Finite X] {A : Subgroup X}
    (hA : Nat.card A = 3 ^ 2)
    (hC : ∀ r : ℕ, r.Prime → r ∣ Nat.card (Subgroup.centralizer (A : Set X)) → r = 2 ∨ r = 3) :
    Group.IsSolvable (Subgroup.normalizer (A : Set X)) := by
  refine CFSG.SignalizerFunctor.Helpers.two_prime_order_solvable _ 2 3 Nat.prime_two
    Nat.prime_three fun r hr hdvd => ?_
  by_contra hne
  simp only [not_or] at hne
  obtain ⟨hr2, hr3⟩ := hne
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨n, hn⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.normalizer (A : Set X)) r hdvd
  set Z : Subgroup X := Subgroup.zpowers (n : X) with hZ
  have hZN : Z ≤ Subgroup.normalizer (A : Set X) := Subgroup.zpowers_le.mpr n.2
  have hnr : orderOf (n : X) = r := by rw [Subgroup.orderOf_coe]; exact hn
  have hZr : IsPGroup r Z := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hnr, pow_one])
  let _ : MulDistribMulAction Z A := Subgroup.conjMulDistribMulActionOfLeNormalizer Z A hZN
  have hmod := hZr.card_modEq_card_fixedPoints A
  have hfix : Nat.card (FixedPoints.subgroup Z A) ∣ 3 ^ 2 := by
    rw [← hA]
    exact Subgroup.card_subgroup_dvd_card _
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hfix
  have hmodk : 3 ^ 2 ≡ 3 ^ k [MOD r] := by
    rw [← hA, ← hk']
    exact hmod
  have h2 : ¬ r ∣ 2 := fun h => hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h)
  have h3 : ¬ r ∣ 3 := fun h => hr3 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp h)
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 by omega) with rfl | rfl | rfl
  · have hd : r ∣ 3 ^ 2 - 3 ^ 0 := (Nat.modEq_iff_dvd' (by norm_num)).mp hmodk.symm
    norm_num at hd
    exact h2 (hr.dvd_of_dvd_pow (show r ∣ 2 ^ 3 by norm_num; exact hd))
  · have hd : r ∣ 3 ^ 2 - 3 ^ 1 := (Nat.modEq_iff_dvd' (by norm_num)).mp hmodk.symm
    norm_num at hd
    rcases (Nat.Prime.dvd_mul hr).mp (show r ∣ 2 * 3 by norm_num; exact hd) with h | h
    · exact h2 h
    · exact h3 h
  ·
    have htop : FixedPoints.subgroup Z A = ⊤ :=
      Subgroup.eq_top_of_card_eq _ (by rw [hk', hA])
    have hnC : (n : X) ∈ Subgroup.centralizer (A : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have hmem : (⟨a, ha⟩ : A) ∈ FixedPoints.subgroup Z A := htop ▸ Subgroup.mem_top _
      have h1 := congrArg Subtype.val
        ((FixedPoints.mem_subgroup Z A _).mp hmem ⟨(n : X), Subgroup.mem_zpowers _⟩)
      have h1' : (n : X) * a * (n : X)⁻¹ = a := h1
      calc a * (n : X) = (n : X) * a * (n : X)⁻¹ * (n : X) := by rw [h1']
        _ = (n : X) * a := by group
    have hd := orderOf_dvd_natCard (⟨(n : X), hnC⟩ : Subgroup.centralizer (A : Set X))
    rw [Subgroup.orderOf_mk, hnr] at hd
    rcases hC r hr hd with h | h
    · exact hr2 h
    · exact hr3 h

theorem isSolvable_normalizer_of_card_eq_nine_of_le {X : Type*} [Group X] [Finite X]
    {A : Subgroup X} (hA : Nat.card A = 3 ^ 2)
    (hC : Subgroup.centralizer (A : Set X) ≤ A) :
    Group.IsSolvable (Subgroup.normalizer (A : Set X)) :=
  isSolvable_normalizer_of_card_eq_nine hA fun r hr hd => Or.inr
    ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp
      (hr.dvd_of_dvd_pow (hd.trans ((Subgroup.card_dvd_of_le hC).trans (by rw [hA])))))

theorem not_dvd_card_inf_glbConj_map {G : Type*} [Group G] {p : ℕ} {M H : Subgroup G}
    (hM : ∀ g : G, g ∉ M → ¬ p ∣ Nat.card (M ⊓ GLBConj g M : Subgroup G))
    (O : Subgroup H) [O.Normal] (hOM : O ≤ (H ⊓ M).subgroupOf H) (x : H ⧸ O)
    (hx : x ∉ ((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' O)) :
    ¬ p ∣ Nat.card (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' O) ⊓
      GLBConj x (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' O)) : Subgroup (H ⧸ O)) := by
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective O x
  set B := (H ⊓ M).subgroupOf H
  have hhM : (h : G) ∉ M := fun hm =>
    hx (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr ⟨h.2, hm⟩))
  intro hdvd
  apply hM h hhM
  have hle : B.map (QuotientGroup.mk' O) ⊓
      GLBConj (QuotientGroup.mk' O h) (B.map (QuotientGroup.mk' O)) ≤
      (B ⊓ GLBConj h B).map (QuotientGroup.mk' O) := by
    rintro z ⟨⟨a, ha, rfl⟩, w, ⟨b, hb, rfl⟩, hzb⟩
    refine ⟨a, ⟨ha, h * a * h⁻¹, ?_, ?_⟩, rfl⟩
    · have e : QuotientGroup.mk' O a = QuotientGroup.mk' O (h⁻¹ * b * h) := by
        rw [← hzb]
        simp
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at e
      have ho : h * (a⁻¹ * (h⁻¹ * b * h))⁻¹ * h⁻¹ ∈ O :=
        Subgroup.Normal.conj_mem inferInstance _ (O.inv_mem e) h
      have e2 : h * a * h⁻¹ = b * (h * (a⁻¹ * (h⁻¹ * b * h))⁻¹ * h⁻¹) := by group
      rw [e2]
      exact B.mul_mem hb (hOM ho)
    · simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply]
      group
  refine (hdvd.trans ((Subgroup.card_dvd_of_le hle).trans (Subgroup.card_map_dvd _ _))).trans ?_
  rw [← Subgroup.card_map_of_injective H.subtype_injective]
  refine Subgroup.card_dvd_of_le ?_
  rintro _ ⟨c, ⟨hcB, b, hb, rfl⟩, rfl⟩
  refine ⟨(Subgroup.mem_subgroupOf.mp hcB).2, b, (Subgroup.mem_subgroupOf.mp hb).2, ?_⟩
  simp

@[expose] def D2PerfectThreePrime {G : Type*} [Group G] (H M : Subgroup G) : Prop :=
  ∀ L : Subgroup G, L ≤ H ⊓ M → ⁅L, L⁆ = L → ¬ 3 ∣ Nat.card L

variable {G : Type*} [Group G] [Finite G] {H M : Subgroup G}

theorem d2PerfectThreePrime_of_le
    (h : ∀ L : Subgroup G, L ≤ H ⊓ M → ⁅L, L⁆ = L → L ≤ GLBPrimeCore 3 H) :
    D2PerfectThreePrime H M := fun L hL hLp hdvd =>
  (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (glbPrimeCore_coprime 3 H)
    (hdvd.trans (Subgroup.card_dvd_of_le (h L hL hLp)))

theorem d2PerfectThreePrime_of_perfect_eq_bot
    (h : ∀ Y : Subgroup (H ⧸ primeComplementCore (G := H) 3),
      Y ≤ ((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)) →
      ⁅Y, Y⁆ = Y → Y = ⊥) :
    D2PerfectThreePrime H M := by
  refine d2PerfectThreePrime_of_le fun L hLHM hL => ?_
  have hLH : L ≤ H := hLHM.trans inf_le_left
  have hL' : ⁅L.subgroupOf H, L.subgroupOf H⁆ = L.subgroupOf H := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hLH, hL]
  have himg : (L.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)) ≤
      ((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)) :=
    Subgroup.map_mono fun l hl =>
      Subgroup.mem_subgroupOf.mpr (hLHM (Subgroup.mem_subgroupOf.mp hl))
  have hbot := h _ himg (by rw [← Subgroup.map_commutator, hL'])
  have hLO : L.subgroupOf H ≤ (GLBPrimeCore 3 H).subgroupOf H := by
    rw [glbPrimeCore_subgroupOf, ← QuotientGroup.ker_mk' (primeComplementCore (G := H) 3)]
    exact (Subgroup.map_eq_bot_iff _).mp hbot
  intro l hl
  exact Subgroup.mem_subgroupOf.mp (hLO (Subgroup.mem_subgroupOf.mpr hl : (⟨l, hLH hl⟩ : H) ∈ _))

theorem d2PerfectThreePrime_of_isSolvable
    (hsolv : Group.IsSolvable (((H ⊓ M).subgroupOf H).map
      (QuotientGroup.mk' (primeComplementCore (G := H) 3)))) :
    D2PerfectThreePrime H M := by
  obtain ⟨n, hn⟩ := exists_iterCommutator_eq_bot
    (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)))
  refine d2PerfectThreePrime_of_perfect_eq_bot fun Y hY hYp => ?_
  rw [eq_bot_iff, ← hn]
  exact le_iterCommutator_of_commutator_eq hYp hY n

end CFSG.AGLEmbeddingD2
