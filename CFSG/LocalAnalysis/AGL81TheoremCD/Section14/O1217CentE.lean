module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.O1217OTwo

import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Conclusion76Basic
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Conclusion76
import CFSG.ClassicalGroups.PCoreSection

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14.O1217

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.LocalAnalysis.RankThreeUC.AGL81C
  CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
  CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Sec7Core4

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {q p : ℕ} {E : Subgroup G}

private lemma sup_zpowers_eq_of_card_eq_prime_sq {p : ℕ} (hp : p.Prime) {E A : Subgroup G}
    (hcard : Nat.card E = p ^ 2) (hAE : A ≤ E) (hA : Nat.card A = p) {b : G}
    (hbE : b ∈ E) (hbA : b ∉ A) : A ⊔ Subgroup.zpowers b = E := by
  let S : Subgroup G := A ⊔ Subgroup.zpowers b
  have hAleS : A ≤ S := le_sup_left
  have hSE : S ≤ E := sup_le hAE (Subgroup.zpowers_le.mpr hbE)
  have hbS : b ∈ S := Subgroup.mem_sup_right (Subgroup.mem_zpowers b)
  have hSne : S ≠ A := by
    intro h
    exact hbA (h ▸ hbS)
  have hrelE : A.relIndex E * Nat.card A = Nat.card E := by
    have h := Subgroup.relIndex_mul_card (H := A) (K := E)
    rwa [inf_eq_left.mpr hAE] at h
  have hrelE_eq : A.relIndex E = p := by
    rw [hcard, hA, pow_two] at hrelE
    exact Nat.eq_of_mul_eq_mul_right hp.pos hrelE
  have hrelS_ne : A.relIndex S ≠ 1 := by
    intro h1
    exact hSne (le_antisymm ((Subgroup.relIndex_eq_one).mp h1) hAleS)
  have hrelS_dvd : A.relIndex S ∣ A.relIndex E := by
    have h := Subgroup.relIndex_mul_relIndex (H := A) (K := S) (L := E) hAleS hSE
    exact ⟨S.relIndex E, h.symm⟩
  have hrelS_eq : A.relIndex S = p := by
    have hdvd : A.relIndex S ∣ p := by
      rw [← hrelE_eq]
      exact hrelS_dvd
    rcases hp.eq_one_or_self_of_dvd _ hdvd with h1 | hp'
    · exact absurd h1 hrelS_ne
    · exact hp'
  have hScard : Nat.card S = p ^ 2 := by
    have h := Subgroup.relIndex_mul_card (H := A) (K := S)
    rw [inf_eq_left.mpr hAleS, hrelS_eq, hA] at h
    rw [← h, pow_two]
  have hSEeq : S = E :=
    Subgroup.eq_of_le_of_card_ge hSE (by rw [hScard, hcard])
  simpa only [S] using hSEeq

private lemma pCoreOf_inf_centralizer_le_pCoreOf_normalizer_inf (M Y : Subgroup G) :
    CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer (Y : Set G) ≤
      CFSG.Open.pCoreOf 2 (Subgroup.normalizer (Y : Set G) ⊓ M) := by
  classical
  set N : Subgroup G := CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer (Y : Set G)
  refine CFSG.ClassicalGroups.PCoreSection.le_pCoreOf ?_ ?_ ?_
  · intro n hn
    rw [Subgroup.mem_inf] at hn ⊢
    exact ⟨Subgroup.centralizer_le_normalizer (Y : Set G) hn.2,
      CFSG.ClassicalGroups.PCoreSection.pCoreOf_le 2 M hn.1⟩
  · intro x hx y hy
    have hxM : x ∈ M := hx.2
    have hxO : x ∈ Subgroup.normalizer (CFSG.Open.pCoreOf 2 M : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro o
      constructor
      · intro ho
        exact CFSG.ClassicalGroups.PCoreSection.conj_mem_pCoreOf hxM ho
      · intro ho
        have h := CFSG.ClassicalGroups.PCoreSection.conj_mem_pCoreOf
          (X := M) (g := x⁻¹) (M.inv_mem hxM) ho
        have h' : x⁻¹ * (x * o * x⁻¹) * x⁻¹⁻¹ = o := by group
        rwa [h'] at h
    have hxY : x ∈ Subgroup.normalizer
        (Subgroup.centralizer (Y : Set G) : Set G) := by
      have hNY : Subgroup.normalizer (Y : Set G) ≤
          Subgroup.normalizer (Subgroup.centralizer (Y : Set G) : Set G) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer
          (Subgroup.centralizer_le_normalizer (Y : Set G))).mp
          (Subgroup.normal_subgroupOf_centralizer_normalizer (Y : Set G))
      exact hNY hx.1
    have hxN : x ∈ Subgroup.normalizer (N : Set G) :=
      Subgroup.inf_normalizer_le_normalizer_inf ⟨hxO, hxY⟩
    exact (Subgroup.mem_normalizer_iff.mp hxN y).mp hy
  · exact (CFSG.ClassicalGroups.PCoreSection.isPGroup_pCoreOf 2 M).to_le inf_le_left

private lemma Hyp1417.le_centralizer_kSub_of_not_le (h : Hyp1417 G M q p E)
    (h1 : NineFourTwoSigmaGen)
    {A : Subgroup G} (hAE : A ≤ E) (hA : Nat.card A = p)
    (hH : ¬ Subgroup.normalizer (A : Set G) ≤ M) :
    A ≤ Subgroup.centralizer
      (AGL81C.kSub q M (Subgroup.normalizer (A : Set G)) : Set G) := by
  obtain ⟨Q, F, s⟩ := h.exists_setting hAE hA hH
  haveI : Fact p.Prime := ⟨h.hp⟩
  haveI : IsCyclic A := isCyclic_of_prime_card hA
  exact s.le_centralizer_kSub h1 le_rfl

theorem Hyp1417.normalizer_le_of_two_lt (h : Hyp1417 G M q p E)
    (h1 : NineFourTwoSigmaGen)
    (hNT : CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.KFactNineThreeNoTwo)
    (hL34 : KFactL34InvTwo) {B : Subgroup G} (hBE : B ≤ E) (hB : Nat.card B = p)
    (h2 : 2 < Nat.card ↥(CFSG.Open.pCoreOf 2
      (Subgroup.normalizer (B : Set G) ⊓ M))) :
    Subgroup.normalizer (B : Set G) ≤ M := by
  by_contra hH
  obtain ⟨Q, F, s⟩ := h.exists_setting hBE hB hH
  have hle := s.card_pCoreOf_two_le_two h1 hNT hL34
  omega

theorem Hyp1417.centralizer_le (h : Hyp1417 G M q p E)
    (h1 : NineFourTwoSigmaGen)
    (hNT : CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.KFactNineThreeNoTwo)
    (hL34 : KFactL34InvTwo) :
    Subgroup.centralizer (E : Set G) ≤ M := by
  classical
  haveI : Fact p.Prime := ⟨h.hp⟩
  obtain ⟨Y, hYE, hYcard, hYnotcent⟩ :=
    exists_card_eq_not_le_centralizer_pCoreOf_inf_centralizer (r := p)
      h.cstar.charTwo h.maxLocal.1 h.hp2 h.le h.elem h.card
  have hY2 : 2 < Nat.card ↥(CFSG.Open.pCoreOf 2 M ⊓
      Subgroup.centralizer (Y : Set G)) :=
    two_lt_card_pCoreOf_inf_centralizer h.le
      (Subgroup.le_centralizer_iff_isMulCommutative.mpr h.elem.1) hYE hYnotcent
  have hNle : CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer (Y : Set G) ≤
      CFSG.Open.pCoreOf 2 (Subgroup.normalizer (Y : Set G) ⊓ M) :=
    pCoreOf_inf_centralizer_le_pCoreOf_normalizer_inf M Y
  have h2 : 2 < Nat.card ↥(CFSG.Open.pCoreOf 2
      (Subgroup.normalizer (Y : Set G) ⊓ M)) :=
    hY2.trans_le (Subgroup.card_le_of_le hNle)
  have hNYM : Subgroup.normalizer (Y : Set G) ≤ M :=
    h.normalizer_le_of_two_lt h1 hNT hL34 hYE hYcard h2
  exact (Subgroup.centralizer_le hYE).trans
    ((Subgroup.centralizer_le_normalizer (Y : Set G)).trans hNYM)

theorem Hyp1417.inf_centralizer_kSub_eq (h : Hyp1417 G M q p E)
    (h1 : NineFourTwoSigmaGen)
    (hNT : CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.KFactNineThreeNoTwo)
    (hL34 : KFactL34InvTwo) {A : Subgroup G} (hAE : A ≤ E) (hA : Nat.card A = p)
    (hH : ¬ Subgroup.normalizer (A : Set G) ≤ M) :
    E ⊓ Subgroup.centralizer
      (AGL81C.kSub q M (Subgroup.normalizer (A : Set G)) : Set G) = A := by
  classical
  obtain ⟨Q, F, s⟩ := h.exists_setting hAE hA hH
  have hAcent : A ≤ Subgroup.centralizer
      (AGL81C.kSub q M (Subgroup.normalizer (A : Set G)) : Set G) :=
    h.le_centralizer_kSub_of_not_le h1 hAE hA hH
  let D : Subgroup G := E ⊓ Subgroup.centralizer
    (AGL81C.kSub q M (Subgroup.normalizer (A : Set G)) : Set G)
  have hAleD : A ≤ D := le_inf hAE hAcent
  have hDE : D ≠ E := by
    intro hEq
    have hEcent : E ≤ Subgroup.centralizer
        (AGL81C.kSub q M (Subgroup.normalizer (A : Set G)) : Set G) := by
      rw [← hEq]
      exact inf_le_right
    have hKAleCE : AGL81C.kSub q M (Subgroup.normalizer (A : Set G)) ≤
        Subgroup.centralizer (E : Set G) :=
      (Subgroup.le_centralizer_iff).mp hEcent
    exact s.kSub_not_le h1 (hKAleCE.trans (h.centralizer_le h1 hNT hL34))
  have hDdvd : Nat.card D ∣ p ^ 2 := by
    have := Subgroup.card_dvd_of_le (show D ≤ E from inf_le_left)
    rwa [h.card] at this
  have hDcard : Nat.card D = p := by
    obtain ⟨k, hk_le, hk_eq⟩ :=
      (Nat.dvd_prime_pow h.hp (m := 2) (i := Nat.card D)).mp hDdvd
    have hk0 : k ≠ 0 := by
      intro h0
      have hle := Subgroup.card_le_of_le hAleD
      rw [hA, hk_eq, h0, pow_zero] at hle
      have hp2 : 2 ≤ p := h.hp.two_le
      omega
    have hk1 : k = 1 := by
      rcases Nat.lt_or_ge k 2 with hlt | hge
      · omega
      · have hk2 : k = 2 := by omega
        exfalso
        apply hDE
        have hDEcard : Nat.card D = Nat.card E := by rw [hk_eq, hk2, h.card]
        exact Subgroup.eq_of_le_of_card_ge (show D ≤ E from inf_le_left)
          (by rw [hDEcard])
    rw [hk_eq, hk1, pow_one]
  have hDA : D = A := by
    have hcard_le : Nat.card D ≤ Nat.card A := by rw [hDcard, hA]
    exact (Subgroup.eq_of_le_of_card_ge hAleD hcard_le).symm
  change D = A
  exact hDA

theorem Hyp1417.kSub_inf_centralizer_le (h : Hyp1417 G M q p E)
    (h1 : NineFourTwoSigmaGen)
    (hNT : CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.KFactNineThreeNoTwo)
    (hL34 : KFactL34InvTwo) {A : Subgroup G} (hAE : A ≤ E) (hA : Nat.card A = p)
    (hH : ¬ Subgroup.normalizer (A : Set G) ≤ M) {b : G} (hbE : b ∈ E) (hbA : b ∉ A) :
    AGL81C.kSub q M (Subgroup.normalizer (A : Set G)) ⊓
      Subgroup.centralizer ({b} : Set G) ≤ M := by
  classical
  have hAcent : A ≤ Subgroup.centralizer
      (AGL81C.kSub q M (Subgroup.normalizer (A : Set G)) : Set G) :=
    h.le_centralizer_kSub_of_not_le h1 hAE hA hH
  have hKA_le_CA : AGL81C.kSub q M (Subgroup.normalizer (A : Set G)) ≤
      Subgroup.centralizer (A : Set G) :=
    (Subgroup.le_centralizer_iff).mp hAcent
  have hE_sup : A ⊔ Subgroup.zpowers b = E :=
    sup_zpowers_eq_of_card_eq_prime_sq h.hp h.card hAE hA hbE hbA
  have hK_le_CA : AGL81C.kSub q M (Subgroup.normalizer (A : Set G)) ⊓
      Subgroup.centralizer ({b} : Set G) ≤
      Subgroup.centralizer (A : Set G) :=
    inf_le_left.trans hKA_le_CA
  have hK_le_CZ : AGL81C.kSub q M (Subgroup.normalizer (A : Set G)) ⊓
      Subgroup.centralizer ({b} : Set G) ≤
      Subgroup.centralizer (Subgroup.zpowers b : Set G) := by
    intro x hx
    rw [Subgroup.mem_inf] at hx
    simpa only [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] using hx.2
  have hleCsup := CFSG.GorensteinWalter.le_centralizer_sup_of_le_centralizers
    (A := A) (B := Subgroup.zpowers b) hK_le_CA hK_le_CZ
  rw [hE_sup] at hleCsup
  exact hleCsup.trans (h.centralizer_le h1 hNT hL34)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14.O1217
