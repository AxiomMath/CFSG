
module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWAdmBase

public import Certificates.Certificate27825

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Fin76b.W16

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative

section Adm

theorem admCheck_facts :
    (∀ i < 60, admTabOK i = true) ∧ (∀ i < 60, admIsoOK i = true) ∧
      (∀ i < 60, ∀ j < 60, i ≠ j → eqA 128 admArr[i]! admArr[j]! = false) ∧
      countW admW blocksPg [] = 60 := by
  have h := Certificates.certificate27825
  unfold admCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨-, -⟩, hT⟩, hI⟩, hP⟩, hC⟩ := h
  refine ⟨hT, hI, fun i hi j hj hij => ?_, hC⟩
  have h' := hP i hi j hj
  have hne : (i == j) = false := beq_eq_false_iff_ne.2 hij
  rw [hne, Bool.false_or] at h'
  simpa using h'

theorem card_adm : Nat.card {x : ↥Pg // AdmPred x} = 60 := by
  classical
  rw [card_eq_countW_Pg (f := admW) (Pr := AdmPred) fun w g hw hg => admW_iff hw hg]
  exact admCheck_facts.2.2.2

theorem adm_rep {i : ℕ} (hi : i < 60) : Rep 128 admArr[i]! (permOfArr 128 admArr[i]!) := by
  have hTab := admCheck_facts.1 i hi
  unfold admTabOK at hTab
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hTab
  exact (rep_permOfArr hTab.1.1.2).1

theorem adm_complete (g : ↥Pg) (hg : AdmPred g) :
    ∃ i < 60, (g : Equiv.Perm (Fin 128)) = permOfArr 128 admArr[i]! := by
  classical
  have hT : ∀ i < 60, permOfArr 128 admArr[i]! ∈ Pg ∧
      AdmPred (permOfArr 128 admArr[i]!) := by
    intro i hi
    have hTab := admCheck_facts.1 i hi
    unfold admTabOK at hTab
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hTab
    have hrep := (rep_permOfArr hTab.1.1.2).1
    have hmem : permOfArr 128 admArr[i]! ∈ Pg := (inPg_iff hrep).1 hTab.1.2
    exact ⟨hmem, (admW_iff (RepW.single hrep) hmem).1 hTab.2⟩
  have hne : ∀ i < 60, ∀ j < 60, permOfArr 128 admArr[i]! = permOfArr 128 admArr[j]! → i = j := by
    intro i hi j hj heq
    by_contra hij
    have h1 := (eqA_iff (adm_rep hi) (adm_rep hj)).2 heq
    rw [admCheck_facts.2.2.1 i hi j hj hij] at h1
    exact Bool.false_ne_true h1
  let F : Fin 60 → {x : ↥Pg // AdmPred (x : Equiv.Perm (Fin 128))} := fun i =>
    ⟨⟨permOfArr 128 admArr[(i : ℕ)]!, (hT (i : ℕ) i.2).1⟩, (hT (i : ℕ) i.2).2⟩
  have hinj : Function.Injective F := by
    intro i j hij
    have h1 : permOfArr 128 admArr[(i : ℕ)]! = permOfArr 128 admArr[(j : ℕ)]! :=
      congrArg (fun x : {x : ↥Pg // AdmPred (x : Equiv.Perm (Fin 128))} =>
        ((x.1 : ↥Pg) : Equiv.Perm (Fin 128))) hij
    exact Fin.ext (hne i i.2 j j.2 h1)
  have hfin : Finite {x : ↥Pg // AdmPred (x : Equiv.Perm (Fin 128))} :=
    Nat.finite_of_card_ne_zero (by rw [card_adm]; norm_num)
  have hfin36 : Nat.card (Fin 60) = 60 := Nat.card_eq_fintype_card.trans (Fintype.card_fin 60)
  have hbij : Function.Bijective F :=
    Function.Injective.bijective_of_nat_card_le hinj (by rw [card_adm, hfin36])
  obtain ⟨i, hi⟩ := hbij.2 ⟨g, hg⟩
  refine ⟨(i : ℕ), i.isLt, ?_⟩
  have h2 : ((((F i).1 : ↥Pg)) : Equiv.Perm (Fin 128)) = (g : Equiv.Perm (Fin 128)) :=
    congrArg (fun x : {x : ↥Pg // AdmPred (x : Equiv.Perm (Fin 128))} =>
      ((x.1 : ↥Pg) : Equiv.Perm (Fin 128))) hi
  exact h2.symm

theorem admIso_facts {i : ℕ} (hi : i < 60) :
    (admIso[i]!).size = 32 ∧ (admIso[i]!)[0]! = 0 ∧ (admIso[i]!)[21]! = 21 ∧
      (∀ k < 32, (admIso[i]!)[k]! < 128 ∧ (admArr[i]!)[(admIso[i]!)[k]!]! = (admIso[i]!)[k]!) ∧
      (∀ a < 32, ∀ b < 32, (admIso[i]!)[mulE0 a b]! = mulC (admIso[i]!)[a]! (admIso[i]!)[b]!) ∧
      (∀ a < 32, ∀ b < 32, (admIso[i]!)[a]! = (admIso[i]!)[b]! → a = b) ∧
      (∀ c < 128, (admArr[i]!)[c]! = c → ∃ k < 32, (admIso[i]!)[k]! = c) := by
  have hI := admCheck_facts.2.1 i hi
  unfold admIsoOK at hI
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, bne_iff_ne, ne_eq, Bool.or_eq_true,
    List.all_eq_true, List.mem_range, List.any_eq_true] at hI
  obtain ⟨⟨⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩, c7⟩, -⟩ := hI
  refine ⟨c1, c2, c3, fun k hk => c4 k hk, fun a ha b hb => c5 a ha b hb,
    fun a ha b hb hab => (c6 a ha b hb).resolve_right (fun hne => hne hab), fun c hc hpc => ?_⟩
  rcases c7 c hc with h | ⟨k, hk, hkc⟩
  · exact absurd hpc h
  · exact ⟨k, hk, hkc⟩

theorem admIso_card {i : ℕ} (hi : i < 60) :
    ((List.range 128).filter fun c => (List.range 128).all fun g =>
      (admArr[i]!)[g]! != g || mulC c g == mulC g c).length = 8 := by
  have hI := admCheck_facts.2.1 i hi
  unfold admIsoOK at hI
  simp only [Bool.and_eq_true, beq_iff_eq] at hI
  exact hI.2

theorem adm_facts {i : ℕ} (hi : i < 60) :
    Rep 128 admArr[i]! (permOfArr 128 admArr[i]!) ∧
      (admIso[i]!).size = 32 ∧ (admIso[i]!)[0]! = 0 ∧ (admIso[i]!)[21]! = 21 ∧
      (∀ k < 32, (admIso[i]!)[k]! < 128 ∧ (admArr[i]!)[(admIso[i]!)[k]!]! = (admIso[i]!)[k]!) ∧
      (∀ a < 32, ∀ b < 32, (admIso[i]!)[mulE0 a b]! = mulC (admIso[i]!)[a]! (admIso[i]!)[b]!) ∧
      (∀ a < 32, ∀ b < 32, (admIso[i]!)[a]! = (admIso[i]!)[b]! → a = b) ∧
      (∀ c < 128, (admArr[i]!)[c]! = c → ∃ k < 32, (admIso[i]!)[k]! = c) :=
  ⟨adm_rep hi, admIso_facts hi⟩

theorem adm_cent_card {i : ℕ} (hi : i < 60) :
    (Finset.univ.filter fun c : Fin 128 => ∀ g : Fin 128, (permOfArr 128 admArr[i]!) g = g →
      mulC (c : ℕ) (g : ℕ) = mulC (g : ℕ) (c : ℕ)).card = 8 := by
  have hrep := adm_rep hi
  have hP : ∀ c : Fin 128, (∀ g : Fin 128, (permOfArr 128 admArr[i]!) g = g →
      mulC (c : ℕ) (g : ℕ) = mulC (g : ℕ) (c : ℕ)) ↔ ((c : ℕ) < 128 ∧
        (List.range 128).all (fun g => (admArr[i]!)[g]! != g || mulC (c : ℕ) g == mulC g (c : ℕ))
          = true) := by
    intro c
    constructor
    · intro h
      refine ⟨c.isLt, ?_⟩
      simp only [List.all_eq_true, List.mem_range]
      intro g hg
      by_cases hpg : (admArr[i]!)[g]! = g
      · have hfix : permOfArr 128 admArr[i]! ⟨g, hg⟩ = ⟨g, hg⟩ :=
          Fin.ext ((hrep ⟨g, hg⟩).symm.trans hpg)
        have hm : mulC (c : ℕ) g = mulC g (c : ℕ) := h ⟨g, hg⟩ hfix
        simp [hpg, hm]
      · simp [hpg]
    · rintro ⟨-, hQ⟩ g hg
      simp only [List.all_eq_true, List.mem_range] at hQ
      have hg2 := hQ (g : ℕ) g.isLt
      have hpg : (admArr[i]!)[(g : ℕ)]! = (g : ℕ) := by rw [hrep g, hg]
      rw [hpg] at hg2
      simpa using hg2
  rw [card_filter_fin_range (m := 128) (Q := fun c : ℕ => (List.range 128).all fun g =>
    (admArr[i]!)[g]! != g || mulC c g == mulC g c) (le_refl 128) _ hP]
  exact admIso_card hi

end Adm

end CFSG.EvenSporadicStandard.Fin76b.W16
