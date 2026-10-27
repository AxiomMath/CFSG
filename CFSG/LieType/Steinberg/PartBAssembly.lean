module

public import CFSG.LieType.Steinberg.PartBProof

public noncomputable section

namespace CFSG.LieType.Steinberg

open CFSG.LieType.Universal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

section CommOrder

variable (Φ : RootSystem ι)

omit [Fintype ι] [DecidableEq ι] in
private theorem zsmul_ne_zero' {γ : ι → ℤ} (hγ : γ ≠ 0) {c : ℤ} (hc : c ≠ 0) : c • γ ≠ 0 :=
  fun h => (smul_eq_zero.1 h).elim hc hγ

theorem expPairs_finite (hred : ∀ γ ∈ Φ.roots, ∀ δ ∈ Φ.roots, γ ≠ 2 • δ) {α β : ι → ℤ}
    (hα : α ∈ Φ.roots) (hβ : β ∈ Φ.roots) (hαβ : α + β ≠ 0) : (expPairs Φ α β).Finite := by
  have hα0 : α ≠ 0 := fun h => Φ.zero_notMem (h ▸ hα)
  by_cases hli : LinIndepPair α β
  · refine (Φ.finite_roots.preimage (f := fun p : ℕ × ℕ => p.1 • α + p.2 • β) ?_).subset
      fun p hp => hp.2.2
    intro p _ q _ hpq
    have h := hli ((p.1 : ℤ) - q.1) ((p.2 : ℤ) - q.2) (by
      simp only at hpq
      rw [sub_smul, sub_smul, natCast_zsmul, natCast_zsmul, natCast_zsmul, natCast_zsmul]
      rw [show p.1 • α - q.1 • α + (p.2 • β - q.2 • β) =
        (p.1 • α + p.2 • β) - (q.1 • α + q.2 • β) by abel, hpq, sub_self])
    exact Prod.ext (by omega) (by omega)
  · have hneg : -α ∈ Φ.roots := Φ.neg_mem α hα
    have hnegβ : -β ∈ Φ.roots := Φ.neg_mem β hβ
    rcases Φ.proportional α hα β hβ hli with h | h | h | h | h | h
    ·
      subst h
      refine Set.Finite.subset Set.finite_empty fun p hp => ?_
      obtain ⟨hp1, hp2, hpr⟩ := hp
      have hsum : p.1 • α + p.2 • α = (p.1 + p.2) • α := (add_nsmul α p.1 p.2).symm
      rw [hsum] at hpr
      have hli' : ¬ LinIndepPair ((p.1 + p.2) • α) α := fun hl => by
        have := hl 1 (-((p.1 + p.2 : ℕ) : ℤ)) (by
          rw [one_smul, neg_smul, natCast_zsmul, add_neg_cancel])
        exact one_ne_zero this.1
      exfalso
      set n := p.1 + p.2 with hn
      rcases Φ.proportional _ hpr α hα hli' with h' | h' | h' | h' | h' | h'
      · exact zsmul_ne_zero' hα0 (c := (n : ℤ) - 1) (by omega)
          (by linear_combination (norm := module) h')
      · exact zsmul_ne_zero' hα0 (c := (n : ℤ) + 1) (by omega)
          (by linear_combination (norm := module) h')
      · exact hred _ hpr α hα h'
      · exact zsmul_ne_zero' hα0 (c := (n : ℤ) + 2) (by omega)
          (by linear_combination (norm := module) h')
      · exact zsmul_ne_zero' hα0 (c := 2 * (n : ℤ) - 1) (by omega)
          (by linear_combination (norm := module) -h')
      · exact zsmul_ne_zero' hα0 (c := 2 * (n : ℤ) + 1) (by omega)
          (by linear_combination (norm := module) h')
    · exact absurd (by rw [h, neg_add_cancel]) hαβ
    · exact absurd h (hred α hα β hβ)
    · exact absurd (by rw [h, neg_neg]) (hred (-α) hneg β hβ)
    · exact absurd h (hred β hβ α hα)
    · exact absurd (by rw [h, neg_neg]) (hred (-β) hnegβ α hα)

theorem nonempty_commOrder (hred : ∀ γ ∈ Φ.roots, ∀ δ ∈ Φ.roots, γ ≠ 2 • δ) :
    Nonempty (CommOrder Φ) := by
  classical
  refine ⟨⟨fun α β => if h : α ∈ Φ.roots ∧ β ∈ Φ.roots ∧ α + β ≠ 0 then
    (expPairs_finite Φ hred h.1 h.2.1 h.2.2).toFinset.toList else [], fun α β => ?_,
    fun α hα β hβ hαβ p => ?_⟩⟩
  · split_ifs
    · exact Finset.nodup_toList _
    · exact List.nodup_nil
  · rw [dite_eq_left ⟨hα, hβ, hαβ⟩, Finset.mem_toList, Set.Finite.mem_toFinset]

end CommOrder

theorem nonempty_commOrder_ofCartan {I : Type} [Fintype I] [DecidableEq I] {A : Matrix I I ℤ}
    (hA : TauCeti.IsFiniteType A) {Dv : Set I} (hDv : Dv = ∅) :
    Nonempty (CommOrder (RootSystem.ofCartan hA Dv)) :=
  nonempty_commOrder _ fun _ _ δ hδ e => two_smul_notMem_roots hA hDv hδ (e ▸ ‹_›)

section Assembly

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {k : Type*} [Field k]
  {x : (Fin D.rank → ℤ) → k → K}

theorem presentationB_of [Finite k] (hD : D.divisible = ∅)
    (hC : ∀ O : CommOrder (RootSystem.ofCartan D.isFiniteType D.divisible),
      ∃ C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ,
        (∀ α ∈ (RootSystem.ofCartan D.isFiniteType D.divisible).roots,
          ∀ β ∈ (RootSystem.ofCartan D.isFiniteType D.divisible).roots,
            ∀ p ∈ expPairs (RootSystem.ofCartan D.isFiniteType D.divisible) α β,
              (C α β p).natAbs ∈ ({1, 2, 3} : Set ℕ)) ∧ CommutatorFormula x O C)
    (hE : ∀ (O : CommOrder (RootSystem.ofCartan D.isFiniteType D.divisible))
      (C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ),
        CommutatorFormula x O C → ChevalleyExtras D k x C O)
    (hbij : Function.Bijective
      (stPi (RootSystem.ofCartan D.isFiniteType D.divisible) D.rootGroup)) :
    PresentationB (Φ := RootSystem.ofCartan D.isFiniteType D.divisible) x :=
  fun O => ⟨hC O, fun C hCf => chevPresented_bijective hD (hE O C hCf) hbij⟩

theorem redundantR2_of [Finite k] (hD : D.divisible = ∅)
    (hC : ∀ O : CommOrder (RootSystem.ofCartan D.isFiniteType D.divisible),
      ∃ C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ, CommutatorFormula x O C)
    (hE : ∀ (O : CommOrder (RootSystem.ofCartan D.isFiniteType D.divisible))
      (C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ),
        CommutatorFormula x O C → ChevalleyExtras D k x C O)
    (hbij : Function.Bijective
      (stPi (RootSystem.ofCartan D.isFiniteType D.divisible) D.rootGroup)) :
    RedundantR2 (RootSystem.ofCartan D.isFiniteType D.divisible) D.rootGroup := by
  obtain ⟨O⟩ := nonempty_commOrder_ofCartan D.isFiniteType hD
  obtain ⟨C, hCf⟩ := hC O
  exact redundantR2 hD (hE O C hCf) hbij

end Assembly

end CFSG.LieType.Steinberg
