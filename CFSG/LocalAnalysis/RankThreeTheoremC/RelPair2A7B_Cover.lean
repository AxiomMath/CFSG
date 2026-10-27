module

public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2A7_Main

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup

theorem exists_invariantTwo_lift {Y X : Type} [Group Y] [Finite Y] [Group X] {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (π : Y →* X) (hπ : Function.Surjective π)
    (hker : q.Coprime (Nat.card π.ker)) {N Q : Subgroup Y} (hQN : Q ≤ N) (hQ : IsPGroup q Q)
    {W : Subgroup X} (hW2 : IsPGroup 2 W) (hQW : Q.map π ≤ normalizer (W : Set X))
    (hWN : W ≤ N.map π) :
    ∃ B : Subgroup Y, B ≤ N ∧ IsPGroup 2 B ∧ Q ≤ normalizer (B : Set Y) ∧ B.map π = W := by
  classical
  have hfin : Finite X := Finite.of_surjective π hπ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Wt : Subgroup Y := N ⊓ W.comap π with hWt
  have hQWt : Q ≤ normalizer (Wt : Set Y) := by
    intro d hd
    rw [mem_normalizer_iff]
    intro x
    have hdN : d ∈ N := hQN hd
    have hπd : π d ∈ normalizer (W : Set X) := hQW ⟨d, hd, rfl⟩
    have h1 := mem_normalizer_iff.mp hπd (π x)
    simp only [hWt, Subgroup.mem_inf, Subgroup.mem_comap, map_mul, map_inv]
    constructor
    · rintro ⟨hxN, hxW⟩
      exact ⟨N.mul_mem (N.mul_mem hdN hxN) (N.inv_mem hdN), h1.mp hxW⟩
    · rintro ⟨hxN, hxW⟩
      refine ⟨?_, h1.mpr hxW⟩
      have := N.mul_mem (N.mul_mem (N.inv_mem hdN) hxN) hdN
      simpa [mul_assoc] using this
  have hmap : Wt.map π = W := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hx.2
    · intro w hw
      obtain ⟨n, hn, rfl⟩ := hWN hw
      exact ⟨n, ⟨hn, hw⟩, rfl⟩
  have hcop : q.Coprime (Nat.card Wt) := by
    have h := card_eq_card_map_mul_card_inf_ker π Wt
    rw [hmap] at h
    rw [h]
    obtain ⟨k, hk⟩ := hW2.exists_card_eq
    refine Nat.Coprime.mul_right ?_ ?_
    · rw [hk]
      exact Nat.Coprime.pow_right k ((Nat.coprime_primes hq Nat.prime_two).mpr hq2)
    · exact hker.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right)
  obtain ⟨B, hBS, hQB⟩ := exists_isSylowOf_normalized_by_pGroup hq hQ hQWt hcop
  have hS := isSylowOf_map_hom (p := 2) π hBS
  rw [hmap] at hS
  refine ⟨B, hBS.le.trans inf_le_left, hBS.isPGroup, hQB, ?_⟩
  exact (hS.eq_of_le hS.le le_rfl hW2).symm

variable {G : Type} [Group G] [Finite G]

theorem IsOptimalRelPair.not_map_conj_le_of_normalizer {p : ℕ} {P : Sylow p G}
    {M D R T H V : Subgroup G} (hd : MaximalRelativePair p P M D R T)
    (hopt : IsOptimalRelPair p M D R T H V) (hfacts : OptimalRelPairFacts p M D H V)
    (hp3 : p = 3) {Y : Subgroup G} (hYV : Y ≤ V) (hY1 : Y ≠ ⊥)
    (hY : normalizer (V : Set G) ≤ normalizer (Y : Set G)) {n : G} (hnH : n ∈ H)
    (hnD : n ∈ normalizer (D : Set G))
    (hjoin : p ∣ Nat.card (V ⊔ V.map (MulAut.conj n).toMonoidHom : Subgroup G)) :
    ¬ (V.map (MulAut.conj n).toMonoidHom ≤
      (H ⊓ normalizer (Y : Set G)) ⊔ (primeComplementCore (G := H) p).map H.subtype) := by
  subst hp3
  intro hle
  classical
  have hprime : (3 : ℕ).Prime := Nat.prime_three
  have hfact : Fact (Nat.Prime 3) := ⟨hprime⟩
  have hDH : D ≤ H := (le_sup_right : D ≤ relPairBase R T ⊔ D).trans hopt.pair.cand.base_le
  have hVH : V ≤ H := hfacts.maximal.1
  have hV2 : IsPGroup 2 V := hfacts.maximal.2.1
  have hDV : D ≤ normalizer (V : Set G) := hfacts.maximal.2.2.1
  set K : Subgroup ↥H := primeComplementCore (G := ↥H) 3 with hK
  set π : ↥H →* ↥H ⧸ K := QuotientGroup.mk' K with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective K
  have hker : π.ker = K := QuotientGroup.ker_mk' K
  have hkerc : (3 : ℕ).Coprime (Nat.card π.ker) := by
    rw [hker]
    exact primeComplementCore_coprime 3
  have hDp : IsPGroup 3 D := P.isPGroup'.to_le hd.ext.obstruction.2.1
  set Dy : Subgroup ↥H := D.subgroupOf H with hDy
  have hDy3 : IsPGroup 3 Dy := hDp.of_equiv (Subgroup.subgroupOfEquivOfLe hDH).symm
  set N' : Subgroup G := H ⊓ normalizer (Y : Set G) with hN'
  have hN'H : N' ≤ H := inf_le_left
  have hDN' : D ≤ N' := le_inf hDH (hDV.trans hY)
  have hVN' : V ≤ N' := le_inf hVH ((Subgroup.le_normalizer).trans hY)
  set Vn : Subgroup G := V.map (MulAut.conj n).toMonoidHom with hVn
  have hVnH : Vn ≤ H := by
    rintro _ ⟨v, hv, rfl⟩
    exact H.mul_mem (H.mul_mem hnH (hVH hv)) (H.inv_mem hnH)
  have hVn2 : IsPGroup 2 Vn := hV2.map _
  have hDVn : D ≤ normalizer (Vn : Set G) := by
    intro d hd'
    rw [hVn, mem_normalizer_map_conj_iff]
    have h1 := (mem_normalizer_iff.mp (inv_mem hnD) d).mp hd'
    simp only [inv_inv] at h1
    exact hDV h1
  set Vy : Subgroup ↥H := V.subgroupOf H with hVy
  set Wy : Subgroup ↥H := Vn.subgroupOf H with hWy
  set Ny : Subgroup ↥H := N'.subgroupOf H with hNy
  have hDyNy : Dy ≤ Ny := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hDN' (Subgroup.mem_subgroupOf.mp hx))
  have hVyNy : Vy ≤ Ny := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hVN' (Subgroup.mem_subgroupOf.mp hx))
  have hWy2 : IsPGroup 2 Wy := hVn2.of_equiv (Subgroup.subgroupOfEquivOfLe hVnH).symm
  have hVy2 : IsPGroup 2 Vy := hV2.of_equiv (Subgroup.subgroupOfEquivOfLe hVH).symm
  have hDyWy : Dy ≤ normalizer (Wy : Set ↥H) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hVnH]
    exact fun x hx => Subgroup.mem_subgroupOf.mpr (hDVn (Subgroup.mem_subgroupOf.mp hx))
  have hπDW : Dy.map π ≤ normalizer ((Wy.map π : Subgroup (↥H ⧸ K)) : Set (↥H ⧸ K)) :=
    (Subgroup.map_mono hDyWy).trans (Subgroup.le_normalizer_map π)
  have hsup : (Ny ⊔ K).map H.subtype =
      N' ⊔ (primeComplementCore (G := H) 3).map H.subtype := by
    rw [Subgroup.map_sup, hNy, Subgroup.map_subgroupOf_eq_of_le hN'H]
  have hWN : Wy.map π ≤ Ny.map π := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' : (x : G) ∈ N' ⊔ (primeComplementCore (G := H) 3).map H.subtype :=
      hle (Subgroup.mem_subgroupOf.mp hx)
    rw [← hsup] at hx'
    obtain ⟨y, hy, hyx⟩ := hx'
    have hyx' : y = x := Subtype.ext hyx
    rw [hyx'] at hy
    obtain ⟨a, ha, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hy
    refine ⟨a, ha, ?_⟩
    have hz1 : π z = 1 := (QuotientGroup.eq_one_iff z).mpr hz
    simp [hz1]
  obtain ⟨B, hBN, hB2, hDB, hBπ⟩ := exists_invariantTwo_lift hprime (by norm_num) π hπs hkerc
    hDyNy hDy3 (hWy2.map π) hπDW hWN
  have hVV : Vy.map H.subtype = V := Subgroup.map_subgroupOf_eq_of_le hVH
  have hWW : Wy.map H.subtype = Vn := Subgroup.map_subgroupOf_eq_of_le hVnH
  have hjoinY : 3 ∣ Nat.card (Vy ⊔ Wy : Subgroup ↥H) := by
    have h1 := Subgroup.card_map_of_injective H.subtype_injective (K := (Vy ⊔ Wy : Subgroup ↥H))
    rw [Subgroup.map_sup, hVV, hWW] at h1
    rw [← h1]
    exact hjoin
  have hjoinπ : 3 ∣ Nat.card ((Vy ⊔ Wy).map π) := by
    have h := card_eq_card_map_mul_card_inf_ker π (Vy ⊔ Wy)
    rw [h] at hjoinY
    have hcop : (3 : ℕ).Coprime (Nat.card ((Vy ⊔ Wy) ⊓ π.ker : Subgroup ↥H)) :=
      hkerc.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right)
    exact hcop.dvd_of_dvd_mul_right hjoinY
  have hBV : 3 ∣ Nat.card (B ⊔ Vy : Subgroup ↥H) := by
    have h1 : (B ⊔ Vy).map π = (Vy ⊔ Wy).map π := by
      rw [Subgroup.map_sup, Subgroup.map_sup, hBπ, sup_comm]
    have := Subgroup.card_map_dvd (B ⊔ Vy) π
    rw [h1] at this
    exact hjoinπ.trans this
  set B' : Subgroup G := B.map H.subtype with hB'
  have hB'N' : B' ≤ N' := by
    refine (Subgroup.map_mono hBN).trans ?_
    rw [hNy, Subgroup.map_subgroupOf_eq_of_le hN'H]
  have hB'2 : IsPGroup 2 B' := hB2.map _
  have hDB' : D ≤ normalizer (B' : Set G) := by
    intro d hd'
    have hdy : (⟨d, hDH hd'⟩ : ↥H) ∈ Dy := Subgroup.mem_subgroupOf.mpr hd'
    exact Subgroup.le_normalizer_map H.subtype ⟨_, hDB hdy, rfl⟩
  have hjoin' : B' ⊔ V ≤ invariantTwoJoinIn D N' :=
    sup_le (le_invariantTwoJoinIn hB'N' hB'2 hDB') (le_invariantTwoJoinIn hVN' hV2 hDV)
  have hcardBV : Nat.card (B' ⊔ V : Subgroup G) = Nat.card (B ⊔ Vy : Subgroup ↥H) := by
    have h1 := Subgroup.card_map_of_injective H.subtype_injective (K := (B ⊔ Vy : Subgroup ↥H))
    rw [Subgroup.map_sup, hVV] at h1
    exact h1
  have hdvd : 3 ∣ Nat.card (B' ⊔ V : Subgroup G) := by
    rw [hcardBV]
    exact hBV
  exact hfacts.not_dvd Y hYV hY1 hY (hdvd.trans (Subgroup.card_dvd_of_le hjoin'))

end CFSG.LocalAnalysis.RankThreeTheoremC
