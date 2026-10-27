module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLZeroIaThreeDiag
import CFSG.LocalAnalysis.AGLEmbedding.TwoLocalPairBlockRank

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

theorem le_pRank_of_blocks {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
    (h : D1PhaseThree p P M H R)
    (hB3 : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L → BlockHasThree M (pCoreOf 2 H) L)
    {m : ℕ} (Lj : Fin m → Subgroup G) (hLj : ∀ j, IsWeakSBlock M (pCoreOf 2 H) (Lj j))
    (hinj : Function.Injective fun j => barM M (Lj j)) :
    m ≤ CFSG.Open.pRank 3 (H ⊓ M) := by
  have h1 := h.toTwoLocalPair.card_le_pRank_three_of_blocks hB3 Lj hLj
    fun i j hij => hinj (congrArg (barM M) hij)
  rwa [Nat.card_eq_fintype_card, Fintype.card_fin] at h1

theorem weakSBlock_or_coprime_of_component {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
    (h : D1PhaseThree p P M H R)
    (hperf : ∀ U : Subgroup G, U ≤ H ⊓ M → ⁅U, U⁆ = U → Nat.Coprime 3 (Nat.card U))
    {Lb : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hLb : IsComponentOf Lb ⊤) :
    (∃ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L ∧ barM M L = Lb) ∨
      Nat.Coprime 3 (Nat.card Lb) := by
  obtain ⟨L, hL2, rfl, hw | hle⟩ := h.exists_weakSBlock_or_le_inf hLb
  · exact Or.inl ⟨L, hw, rfl⟩
  · right
    have hc := hperf L hle hL2.perfect
    have hdvd : Nat.card (barM M L) ∣ Nat.card L := by
      have h1 := Subgroup.card_map_dvd (L.subgroupOf M) (QuotientGroup.mk' (CFSG.pCore 2 ↥M))
      have h2 : Nat.card (L.subgroupOf M) = Nat.card L :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hL2.le).toEquiv
      exact h2 ▸ h1
    exact Nat.Coprime.coprime_dvd_right hdvd hc

theorem false_of_four_conj_components {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
    (h : D1PhaseThree p P M H R)
    (hB3 : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L → BlockHasThree M (pCoreOf 2 H) L)
    (hrank : CFSG.Open.pRank 3 (H ⊓ M) ≤ 3)
    (hperf : ∀ U : Subgroup G, U ≤ H ⊓ M → ⁅U, U⁆ = U → Nat.Coprime 3 (Nat.card U))
    {Lb : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hLb : IsComponentOf Lb ⊤)
    (h3 : ¬ Nat.Coprime 3 (Nat.card Lb)) (g : Fin 4 → ↥M ⧸ CFSG.pCore 2 ↥M)
    (hinj : Function.Injective fun i => Lb.map (MulAut.conj (g i)).toMonoidHom) : False := by
  have hcomp : ∀ i, IsComponentOf (Lb.map (MulAut.conj (g i)).toMonoidHom) ⊤ := fun i =>
    isComponentOf_map_conj hLb (g i)
  have hcard : ∀ i, Nat.card (Lb.map (MulAut.conj (g i)).toMonoidHom) = Nat.card Lb := fun i =>
    Subgroup.card_map_of_injective (MulAut.conj (g i)).injective
  have hw : ∀ i, ∃ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L ∧
      barM M L = Lb.map (MulAut.conj (g i)).toMonoidHom := by
    intro i
    rcases weakSBlock_or_coprime_of_component h hperf (hcomp i) with hw | hc
    · exact hw
    · exact absurd (hcard i ▸ hc) h3
  choose L hL hLeq using hw
  have hle := le_pRank_of_blocks h hB3 L hL (by
    intro i j hij
    apply hinj
    simp only at hij ⊢
    rw [← hLeq i, ← hLeq j, hij])
  omega

theorem mem_normalizer_of_coprime_six {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
    (h : D1PhaseThree p P M H R)
    (hB3 : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L → BlockHasThree M (pCoreOf 2 H) L)
    (hrank : CFSG.Open.pRank 3 (H ⊓ M) ≤ 3)
    (hperf : ∀ U : Subgroup G, U ≤ H ⊓ M → ⁅U, U⁆ = U → Nat.Coprime 3 (Nat.card U))
    {Lb : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hLb : IsComponentOf Lb ⊤)
    (h3 : ¬ Nat.Coprime 3 (Nat.card Lb)) {t : ↥M ⧸ CFSG.pCore 2 ↥M}
    (ht : Nat.Coprime 6 (orderOf t)) :
    t ∈ Subgroup.normalizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  by_contra hnot
  have hpow : ∀ d : ℕ, 0 < d → d < 4 →
      t ^ d ∉ Subgroup.normalizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    intro d hd0 hd4 hd
    apply hnot
    have hcop : Nat.Coprime d (orderOf t) := by
      interval_cases d
      · exact Nat.coprime_one_left _
      · exact Nat.Coprime.coprime_dvd_left (by norm_num : 2 ∣ 6) ht
      · exact Nat.Coprime.coprime_dvd_left (by norm_num : 3 ∣ 6) ht
    exact (Subgroup.zpowers_le.mpr hd) (mem_zpowers_pow_iff.mpr hcop)
  have hstep : ∀ i j : ℕ, i < j → j < 4 →
      Lb.map (MulAut.conj (t ^ i)).toMonoidHom = Lb.map (MulAut.conj (t ^ j)).toMonoidHom →
      False := by
    intro i j hij hj heq
    apply hpow (j - i) (by omega) (by omega)
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have e : t ^ j = t ^ i * t ^ (j - i) := by rw [← pow_add]; congr 1; omega
    rw [e, map_conj_mul] at heq
    exact (Subgroup.map_injective (MulAut.conj (t ^ i)).injective heq).symm
  refine false_of_four_conj_components h hB3 hrank hperf hLb h3 (fun i => t ^ (i : ℕ)) ?_
  intro i j hij
  simp only at hij
  by_contra hne
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
  · exact hstep i j hlt j.2 hij
  · exact hstep j i hlt i.2 hij.symm

theorem le_normalizer_of_irreducible {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
    (h : D1PhaseThree p P M H R)
    (hB3 : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L → BlockHasThree M (pCoreOf 2 H) L)
    (hrank : CFSG.Open.pRank 3 (H ⊓ M) ≤ 3)
    (hperf : ∀ U : Subgroup G, U ≤ H ⊓ M → ⁅U, U⁆ = U → Nat.Coprime 3 (Nat.card U))
    {Lb : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hLb : IsComponentOf Lb ⊤)
    (h3 : ¬ Nat.Coprime 3 (Nat.card Lb)) {A : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)}
    (hA4 : 4 ≤ Nat.card A) {t : ↥M ⧸ CFSG.pCore 2 ↥M}
    (htA : t ∈ Subgroup.normalizer (A : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (htL : t ∈ Subgroup.normalizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hirr : ∀ F : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), F ≤ A →
      t ∈ Subgroup.normalizer (F : Set (↥M ⧸ CFSG.pCore 2 ↥M)) → F = ⊥ ∨ F = A) :
    A ≤ Subgroup.normalizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  set F := A ⊓ Subgroup.normalizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) with hF
  have htF : t ∈ Subgroup.normalizer (F : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨htA, Subgroup.le_normalizer htL⟩
  rcases hirr F inf_le_left htF with hbot | htop
  · exfalso
    have : Fintype A := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card] at hA4
    let e : Fin 4 → A := fun i => (Fintype.equivFin A).symm (Fin.castLE hA4 i)
    have he : Function.Injective e := fun i j hij =>
      Fin.castLE_injective hA4 ((Fintype.equivFin A).symm.injective hij)
    refine false_of_four_conj_components h hB3 hrank hperf hLb h3
      (fun i => ((e i : A) : ↥M ⧸ CFSG.pCore 2 ↥M)) ?_
    intro i j hij
    simp only at hij
    have hmem : ((e i : A) : ↥M ⧸ CFSG.pCore 2 ↥M)⁻¹ * ((e j : A) : ↥M ⧸ CFSG.pCore 2 ↥M) ∈
        F := by
      refine ⟨A.mul_mem (A.inv_mem (e i).2) (e j).2, ?_⟩
      show ((e i : A) : ↥M ⧸ CFSG.pCore 2 ↥M)⁻¹ * ((e j : A) : ↥M ⧸ CFSG.pCore 2 ↥M) ∈
        Subgroup.normalizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M))
      have heq : Lb.map (MulAut.conj (((e i : A) : ↥M ⧸ CFSG.pCore 2 ↥M)⁻¹ *
          ((e j : A) : ↥M ⧸ CFSG.pCore 2 ↥M))).toMonoidHom = Lb := by
        rw [map_conj_mul, ← hij, ← map_conj_mul, inv_mul_cancel, map_conj_one]
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq
    rw [hbot, Subgroup.mem_bot, inv_mul_eq_one] at hmem
    exact he (Subtype.ext hmem)
  · rw [htop] at hF
    exact hF ▸ inf_le_right

end CFSG.AGLEmbedding
