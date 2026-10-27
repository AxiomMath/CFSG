module

import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62yBasic
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem sr630a_eq_of_le_sylow {f : ℕ} [Fact f.Prime] {K E E' : Subgroup G} (hEK : E ≤ K)
    (hE'K : E' ≤ K) (hEp : IsPGroup f E) (hE'p : IsPGroup f E')
    (hs : ¬ f ∣ (E.subgroupOf K).index) (hle : E ≤ E') : E' = E := by
  have hEp' : IsPGroup f (E.subgroupOf K) :=
    hEp.of_equiv (Subgroup.subgroupOfEquivOfLe hEK).symm
  have hE'p' : IsPGroup f (E'.subgroupOf K) :=
    hE'p.of_equiv (Subgroup.subgroupOfEquivOfLe hE'K).symm
  have h := (hEp'.toSylow hs).is_maximal' hE'p' (fun g hg => hle hg)
  have h2 : E' ⊓ K = E ⊓ K := Subgroup.subgroupOf_inj.mp h
  rwa [inf_eq_left.mpr hE'K, inf_eq_left.mpr hEK] at h2

theorem sr630a_exists_central {f : ℕ} [Fact f.Prime] {F H : Subgroup G} (hH : IsPGroup f H)
    (hFH : F ≤ H) (hHN : H ≤ normalizer (F : Set G)) (hF : F ≠ ⊥) :
    ∃ a ∈ F, a ≠ 1 ∧ ∀ h ∈ H, h * a = a * h := by
  have : Group.IsNilpotent H := hH.isNilpotent
  have hnorm : (F.subgroupOf H).Normal := (normal_subgroupOf_iff_le_normalizer hFH).mpr hHN
  obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hF
  have hne : F.subgroupOf H ≠ ⊥ := by
    refine Subgroup.ne_bot_iff_exists_ne_one.mpr ⟨⟨⟨a, hFH a.2⟩, a.2⟩, ?_⟩
    intro h
    apply ha
    exact Subtype.ext (congrArg (fun t : F.subgroupOf H => ((t : H) : G)) h)
  obtain ⟨c, hc1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  refine ⟨((c : H) : G), c.2.1, ?_, ?_⟩
  · intro h
    exact hc1 (Subtype.ext (Subtype.ext h))
  · intro h hh
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp c.2.2 ⟨h, hh⟩)

theorem sr630a_not_dvd_index {f : ℕ} (hfp : f.Prime) (hf2 : f ≠ 2) {F E : Subgroup G}
    (hFE : F ≤ E) (hFne : F ≠ ⊥) (hFe : ∀ e ∈ F, e ^ f = 1)
    (hFall : ∀ e ∈ E, e ^ f = 1 → e ∈ F) (hEp : IsPGroup f E)
    (hEC : E ≤ centralizer (F : Set G))
    (hEs : ¬ f ∣ (E.subgroupOf (centralizer (F : Set G))).index)
    (hiii : ∀ a ∈ F, a ≠ 1 → ∀ g ∈ normalizer (F : Set G) ⊓ centralizer ({a} : Set G),
      ∃ n : ℕ, g ^ (2 ^ n) ∈ centralizer (F : Set G)) : ¬ f ∣ E.index := by
  have : Fact f.Prime := ⟨hfp⟩
  obtain ⟨Q, hEQ⟩ := hEp.exists_le_sylow
  suffices hEQ' : E = (Q : Subgroup G) by
    rw [hEQ']
    exact Q.not_dvd_index
  by_contra hne
  obtain ⟨n, hnQ, hnE, hnnE⟩ :=
    sr628_exists_mem_normalizer_not_mem Q.isPGroup' (lt_of_le_of_ne hEQ hne)
  have hnF : n ∈ normalizer (F : Set G) := by
    have key : ∀ g ∈ normalizer (E : Set G), ∀ e ∈ F, g * e * g⁻¹ ∈ F := by
      intro g hg e he
      refine hFall _ ((mem_normalizer_iff.mp hg e).mp (hFE he)) ?_
      rw [conj_pow, hFe e he, mul_one, mul_inv_cancel]
    rw [mem_normalizer_iff]
    intro h
    refine ⟨key n hnE h, fun hh => ?_⟩
    have := key n⁻¹ (inv_mem hnE) _ hh
    simpa [mul_assoc] using this
  have hHQ : zpowers n ⊔ F ≤ (Q : Subgroup G) :=
    sup_le (zpowers_le.mpr hnQ) (hFE.trans hEQ)
  have hHp : IsPGroup f (zpowers n ⊔ F : Subgroup G) := Q.isPGroup'.to_le hHQ
  have hHN : zpowers n ⊔ F ≤ normalizer (F : Set G) :=
    sup_le (zpowers_le.mpr hnF) Subgroup.le_normalizer
  obtain ⟨a, haF, ha1, hcomm⟩ := sr630a_exists_central hHp le_sup_right hHN hFne
  have hna : n * a = a * n := hcomm n (Subgroup.mem_sup_left (mem_zpowers n))
  obtain ⟨m, hm⟩ := hiii a haF ha1 n ⟨hnF, mem_centralizer_singleton_iff.mpr hna⟩
  have hnC : n ∈ centralizer (F : Set G) := by
    obtain ⟨k, hk⟩ := Q.isPGroup' ⟨n, hnQ⟩
    have hnk : n ^ (f ^ k) = 1 := by simpa using congrArg Subtype.val hk
    have h2 : Nat.Coprime 2 f := (Nat.coprime_primes Nat.prime_two hfp).mpr (Ne.symm hf2)
    have hcop : Nat.Coprime (2 ^ m) (orderOf n) :=
      Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hnk) (Nat.Coprime.pow m k h2)
    obtain ⟨j, hj⟩ := exists_pow_eq_self_of_coprime hcop
    have := pow_mem hm j
    rwa [hj] at this
  have hE'Q : E ⊔ zpowers n ≤ (Q : Subgroup G) := sup_le hEQ (zpowers_le.mpr hnQ)
  have hE'p : IsPGroup f (E ⊔ zpowers n : Subgroup G) := Q.isPGroup'.to_le hE'Q
  have heq := sr630a_eq_of_le_sylow hEC (sup_le hEC (zpowers_le.mpr hnC)) hEp hE'p hEs
    le_sup_left
  have hmem : n ∈ E ⊔ zpowers n := Subgroup.mem_sup_right (mem_zpowers n)
  rw [heq] at hmem
  exact hnnE hmem

theorem sr630a_pRank_eq {f : ℕ} (hfp : f.Prime) {F E : Subgroup G} (hFE : F ≤ E)
    (hFe : IsElemAbelian f F) (hF4 : Nat.card F = f ^ 4)
    (hFall : ∀ e ∈ E, e ^ f = 1 → e ∈ F) : CFSG.Open.pRank f E = 4 := by
  have hbdd : BddAbove {k : ℕ | ∃ A : Subgroup G, A ≤ E ∧ IsElemAbelian f A ∧
      Nat.card A = f ^ k} := by
    refine ⟨Nat.card G, ?_⟩
    rintro k ⟨A, -, -, hk⟩
    have h1 : k < f ^ k := Nat.lt_pow_self hfp.one_lt
    have h2 : Nat.card A ≤ Nat.card G := Subgroup.card_le_card_group A
    omega
  apply le_antisymm
  · unfold CFSG.Open.pRank
    apply csSup_le'
    rintro k ⟨A, hAE, hA, hk⟩
    have hAF : A ≤ F := fun a ha => hFall a (hAE ha) (hA.2 a ha)
    have hle : f ^ k ≤ f ^ 4 :=
      calc f ^ k = Nat.card A := hk.symm
        _ ≤ Nat.card F := Subgroup.card_le_of_le hAF
        _ = f ^ 4 := hF4
    exact (Nat.pow_le_pow_iff_right hfp.one_lt).mp hle
  · unfold CFSG.Open.pRank
    exact le_csSup hbdd ⟨F, hFE, hFe, hF4⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
