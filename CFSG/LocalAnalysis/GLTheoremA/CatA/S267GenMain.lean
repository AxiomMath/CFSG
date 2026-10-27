module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Gen

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA
open scoped commutatorElement

variable {Ω : Type} [Group Ω] [Finite Ω]

theorem exists_isMaxTriple {p : ℕ} {S B B₀ : Subgroup Ω} {d₀ : Ω} {J₀ : Subgroup Ω}
    (h : InTriple p S B B₀ d₀ J₀) : ∃ (B' : Subgroup Ω) (d : Ω) (J : Subgroup Ω),
      IsMaxTriple p S B B' d J := by
  set s : Set (Subgroup Ω) := {J | ∃ (B' : Subgroup Ω) (d : Ω), InTriple p S B B' d J} with hs
  have hfin : s.Finite := Set.toFinite s
  have hne : s.Nonempty := ⟨J₀, B₀, d₀, h⟩
  obtain ⟨J, ⟨B', d, hJ⟩, hmax⟩ := Set.exists_max_image s (fun J => Nat.card J) hfin hne
  exact ⟨B', d, J, hJ, fun B'' d' J' h' => hmax J' ⟨B'', d', h'⟩⟩

theorem exists_isMaxTriple_normalizer {Q : TauCeti.LieTypeIndex → Prop} (h1 : GenStep1On Q)
    (hI : GenStepI112On Q) (h3 : GenStep3On Q) {p q : ℕ} {S B : Subgroup Ω}
    (H : GenHyp Q p q S B) : ∃ (B' : Subgroup Ω) (d : Ω) (J : Subgroup Ω),
      IsMaxTriple p S B B' d J ∧ B' ≤ Subgroup.normalizer (J : Set Ω) := by
  obtain ⟨d₀, J₀, h₀⟩ := h1 p q Ω S B H
  obtain ⟨B', d, J, hmax⟩ := exists_isMaxTriple h₀
  by_cases hN : B' ≤ Subgroup.normalizer (J : Set Ω)
  · exact ⟨B', d, J, hmax, hN⟩
  · obtain ⟨B'', hB'', hN''⟩ := h3 p q Ω S B H (hI p q Ω S B H) B' d J hmax.1 hN
    exact ⟨B'', d, J, ⟨hB'', hmax.2⟩, hN''⟩

theorem s267FactGenOn_of_steps {Q : TauCeti.LieTypeIndex → Prop} (h1 : GenStep1On Q)
    (hC : GenStepCentOn Q) (hI : GenStepI112On Q) (h3 : GenStep3On Q) (h4 : GenStep4On Q)
    (h5 : GenStep5On Q) (h6 : GenStep6On Q) : S267FactGenOn Q := by
  intro p q Ω _ _ S B H
  obtain ⟨B', d, J, hmax, hN⟩ := exists_isMaxTriple_normalizer h1 hI h3 H
  obtain ⟨⟨hB'el, hB'c, hB'case⟩, hdB', hdS, hJ⟩ := hmax.1
  have hcomp := h4 p q Ω S B H (hI p q Ω S B H) B' d J hmax hN
  have hD := h5 p q Ω S B H B' d J hmax.1 hN hcomp
  obtain ⟨E, hEB', hEel, hEcard, hDE, hElayer⟩ := h6 p q Ω S B H B' d J hmax.1 hN hD
  set D : Subgroup Ω := B' ⊓ centModSubgroup p J with hDdef
  have hp := H.pPrime
  have hB'4 : p ^ 4 ≤ Nat.card B' := by
    rcases hB'case with rfl | ⟨hle, -⟩
    · exact H.four
    · exact H.four.trans hle
  have hdp : d ^ p = 1 := hB'el.2 d hdB'
  have hDC : ∀ x ∈ D, x ∈ Subgroup.centralizer (J : Set Ω) := fun x hx =>
    hC p q Ω S B H d J hdp hdS hJ x ((centMod_iff).2 hx.2)
  have hJD : J ≤ S ⊓ Subgroup.centralizer (D : Set Ω) := by
    intro j hj
    refine ⟨(hJ.1 hj).1, ?_⟩
    show j ∈ Subgroup.centralizer (D : Set Ω)
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (Subgroup.mem_centralizer_iff.1 (hDC x hx) j hj).symm
  have hdD : d ∈ D := by
    refine ⟨hdB', (centMod_iff).1 ⟨?_, ?_⟩⟩
    · exact hN hdB'
    ·
      rw [Subgroup.commutator_le]
      intro j hj y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      have hjd : Commute j d := Subgroup.mem_centralizer_singleton_iff.1 (hJ.1 hj).2
      have hc : ⁅j, d ^ k⁆ = 1 := by
        rw [commutatorElement_eq_one_iff_mul_comm]
        exact (hjd.zpow_right k).eq
      rw [hc]
      exact Subgroup.one_mem _
  have hDle : S ⊓ Subgroup.centralizer (D : Set Ω) ≤ S ⊓ Subgroup.centralizer ({d} : Set Ω) :=
    inf_le_inf le_rfl (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hdD))
  refine ⟨B', D, J, hB'el, ⟨⟨inf_le_left, ?_, ?_⟩, ⟨?_, hN, ?_⟩, fun _ => ⟨E, hEB', hEel, hEcard,
    hDE, hElayer⟩⟩, hB'case, hB'c⟩
  · rw [hD]
  · rw [hD, ← pow_add]
    exact hB'4
  · exact glaPComponent_of_le hp hJ hJD hDle
  · intro b hb
    constructor
    · intro hbc
      exact ⟨hb, (centMod_iff).1 hbc⟩
    · intro hbD
      exact (centMod_iff).2 hbD.2

end CFSG.LocalAnalysis.GLTheoremA.S267.Gen
