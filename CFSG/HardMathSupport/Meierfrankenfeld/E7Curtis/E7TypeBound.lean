module

public import CFSG.HardMathSupport.Meierfrankenfeld.E7Curtis.E7Nodes
public import CFSG.HardMathSupport.Meierfrankenfeld.Proving.E7Curtis.E7CaseI
public import CFSG.HardMathSupport.Meierfrankenfeld.Proving.E7Curtis.E7CaseII
public import CFSG.HardMathSupport.Meierfrankenfeld.Proving.E7Curtis.E7NoJUniv

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Meierfrankenfeld.E7Curtis

open CFSG.Quasithin.SmithCurtis CFSG.Quasithin.SmithCurtis.Chev CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CoxeterSystem CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc
  CFSG.HardMathSupport.Meierfrankenfeld.Proving.E7Curtis

section TypeBound


variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem eq_erase_of_forall_ne {J : Finset (Fin Tag.E7.rank)} {s : Fin Tag.E7.rank}
    (hJ : ∀ j, j ≠ s → j ∈ J) (hs : s ∉ J) : J = Finset.univ.erase s := by
  ext j
  simp only [Finset.mem_erase, Finset.mem_univ, and_true]
  exact ⟨fun h hjs => hs (hjs ▸ h), hJ j⟩

theorem e7TypeBound {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) :
    ∀ (k : Type) [Field k] [Finite k] [CharP k 2] [Algebra K k] (m : ℕ)
      (ρ : Representation k (adjointGroup .E7 K) (Fin m → k)) (y : Fin m → k)
      (χ : adjointGroup .E7 K → k) (J : Finset (Fin Tag.E7.rank)) (g : ℕ),
      IsSimpleRep ρ → Function.Injective ρ →
      IsChevType .E7 K 2 CFSG.HardMathSupport.Timmesfeld.LangTorus.exists_weyl_neg_E7 ρ y χ J →
      1 ≤ g → g ∣ n →
      (∀ (i : Fin Tag.E7.rank) (t : Kˣ), χ (dC .E7 K i t) ^ (2 ^ g) = χ (dC .E7 K i t)) →
      (n / g = 1 → 133 ≤ m ∨ ∃ s, (s = n7 ∨ s = n1) ∧ J = Finset.univ.erase s ∧
        ∃ b < n, ∀ z : Kˣ, χ (dC .E7 K s z) = (algebraMap K k (z : K)) ^ (2 ^ b)) ∧
      (2 ≤ n / g → 133 * (n / g) + 1 ≤ m) := by
  intro k _ _ _ _ m ρ y χ J g hρ hinj ht hg hgn hper
  have hfin : Module.finrank k (Fin m → k) = m := Module.finrank_fin_fun k
  by_cases hex : ∃ s : Fin Tag.E7.rank, 1 ≤ s.val ∧ s.val ≤ 5 ∧ s ∉ J
  · obtain ⟨s, hs1, hs5, hs⟩ := hex
    have h := caseI_bound_e7 hn hK hρ ht ⟨hs1, hs5⟩ hs hg hgn (fun z => hper s z)
    rw [hfin] at h
    exact ⟨fun _ => Or.inl (by omega), fun _ => h⟩
  push Not at hex
  have hmid : ∀ s : Fin Tag.E7.rank, 1 ≤ s.val → s.val ≤ 5 → s ∈ J := fun s h1 h5 => hex s h1 h5
  by_cases h1 : n1 ∈ J <;> by_cases h7 : n7 ∈ J
  · exfalso
    refine no_J_univ_e7 hn hK hρ hinj ht (Finset.eq_univ_of_forall fun s => ?_)
    by_cases hs0 : s.val = 0
    · have : s = n1 := Fin.ext hs0
      exact this ▸ h1
    by_cases hs6 : s.val = 6
    · have : s = n7 := Fin.ext hs6
      exact this ▸ h7
    exact hmid s (by omega) (by have := s.isLt; change s.val < 7 at this; omega)
  · have hJ : ∀ j, j ≠ n7 → j ∈ J := by
      intro j hj
      by_cases hj0 : j.val = 0
      · have : j = n1 := Fin.ext hj0
        exact this ▸ h1
      have hj6 : j.val ≠ 6 := fun h => hj (Fin.ext h)
      exact hmid j (by omega) (by have := j.isLt; change j.val < 7 at this; omega)
    refine ⟨fun ht1 => ?_, fun ht2 => ?_⟩
    · rcases node7_bound hn hK hρ ht hJ h7 with hb | hb
      · exact Or.inr ⟨n7, Or.inl rfl, eq_erase_of_forall_ne hJ h7, hb⟩
      · rw [hfin] at hb
        exact Or.inl (by omega)
    · have := node7_bound_two hn hK hρ ht hJ h7 hg hgn (fun z => hper n7 z) ht2
      rwa [hfin] at this
  · have hJ : ∀ j, j ≠ n1 → j ∈ J := by
      intro j hj
      by_cases hj6 : j.val = 6
      · have : j = n7 := Fin.ext hj6
        exact this ▸ h7
      have hj0 : j.val ≠ 0 := fun h => hj (Fin.ext h)
      exact hmid j (by omega) (by have := j.isLt; change j.val < 7 at this; omega)
    refine ⟨fun ht1 => ?_, fun ht2 => ?_⟩
    · rcases node1_bound hn hK hρ ht hJ h1 with hb | hb
      · exact Or.inr ⟨n1, Or.inr rfl, eq_erase_of_forall_ne hJ h1, hb⟩
      · rw [hfin] at hb
        exact Or.inl (by omega)
    · have := node1_bound_two hn hK hρ ht hJ h1 hg hgn (fun z => hper n1 z) ht2
      rwa [hfin] at this
  · have h := caseII_bound_e7 hn hK hρ ht hmid h1 h7 hg hgn hper
    rw [hfin] at h
    exact ⟨fun _ => Or.inl (by omega), fun _ => h⟩

end TypeBound

end CFSG.HardMathSupport.Meierfrankenfeld.E7Curtis
