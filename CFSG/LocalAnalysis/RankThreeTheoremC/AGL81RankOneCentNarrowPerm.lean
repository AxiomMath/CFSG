module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentNarrowCriteria
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent

open CFSG.Open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.HardMathSupport.Dickson.I271

theorem narrowGamma_eq_top_of_cgFacts {p : ℕ} (hp : p.Prime) {X K : Type} [Group X] [Finite X]
    [Group K] [Finite K] (eK : X ≃* K) {e f s₁ s₂ : X}
    (hs : Subgroup.closure ({s₁, s₂} : Set X) = ⊤) (he : e ^ p = 1) (hf : f ^ p = 1)
    (hef : e * f = f * e) (he1 : e ≠ 1) (hfe : ∀ k < p, f ≠ e ^ k) (h₁ : s₁ * e = e * s₁)
    (h₂ : s₂ * f = f * s₂) (T : Sylow p K) : narrowGamma p (T : Subgroup K) = ⊤ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hfz : f ∉ Subgroup.zpowers e := by
    classical
    intro hfz
    rw [mem_zpowers_iff_mem_range_orderOf, orderOf_eq_prime he he1] at hfz
    obtain ⟨k, hk, hke⟩ := Finset.mem_image.1 hfz
    exact hfe k (Finset.mem_range.1 hk) hke.symm
  have hf1 : f ≠ 1 := by simpa using hfe 0 hp.pos
  have hEc : Nat.card (Subgroup.closure ({e, f} : Set _)) = p ^ 2 :=
    card_closure_pair_sq hef he hf he1 hfz
  have hEel : IsElemAbelian p (Subgroup.closure ({e, f} : Set _)) :=
    IsElemAbelian.closure_of_commute
      (by rintro x (rfl | rfl) y (rfl | rfl); exacts [rfl, hef, hef.symm, rfl])
      (by rintro x (rfl | rfl); exacts [he, hf])
  have hsub : ({s₁, s₂} : Set X) ⊆
      {k | ∃ x ∈ Subgroup.closure ({e, f} : Set X), x ≠ 1 ∧ k * x = x * k} := by
    rintro x (rfl | rfl)
    · exact ⟨e, Subgroup.subset_closure (Set.mem_insert _ _), he1, h₁⟩
    · exact ⟨f, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl), hf1, h₂⟩
  have hgen : Subgroup.closure
      {k | ∃ x ∈ Subgroup.closure ({e, f} : Set X), x ≠ 1 ∧ k * x = x * k} = ⊤ := by
    rw [eq_top_iff, ← hs]
    exact Subgroup.closure_mono hsub
  exact narrowGamma_eq_top_of_le_sylow hp eK hEel.isPGroup
    (narrowGamma_eq_top_of_closure_centralizer hp le_rfl hEel hEc hgen) T

theorem closure_pair_subtype_eq_top {G : Type*} [Group G] {H : Subgroup G} {s₁ s₂ : G}
    (hs : Subgroup.closure ({s₁, s₂} : Set G) = H) (h₁ : s₁ ∈ H) (h₂ : s₂ ∈ H) :
    Subgroup.closure ({⟨s₁, h₁⟩, ⟨s₂, h₂⟩} : Set H) = ⊤ := by
  subst hs
  refine Eq.trans ?_ (Subgroup.closure_closure_coe_preimage (k := ({s₁, s₂} : Set G)))
  congr 1
  ext ⟨g, hg⟩
  simp [Subtype.ext_iff]

theorem narrowGamma_eq_top_of_permPlane {n p : ℕ} (hp : p.Prime)
    {H : Subgroup (Equiv.Perm (Fin n))} {e f s₁ s₂ : Equiv.Perm (Fin n)}
    (hs : Subgroup.closure {s₁, s₂} = H) (heH : e ∈ H) (hfH : f ∈ H) (he : e ^ p = 1)
    (hf : f ^ p = 1) (hef : e * f = f * e) (he1 : e ≠ 1) (hfe : ∀ k < p, f ≠ e ^ k)
    (h₁ : s₁ * e = e * s₁) (h₂ : s₂ * f = f * s₂) {K : Type} [Group K] [Finite K] (eK : H ≃* K)
    (T : Sylow p K) : narrowGamma p (T : Subgroup K) = ⊤ := by
  have hs₁ : s₁ ∈ H := hs ▸ Subgroup.subset_closure (Set.mem_insert _ _)
  have hs₂ : s₂ ∈ H := hs ▸ Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  refine narrowGamma_eq_top_of_cgFacts hp eK (e := ⟨e, heH⟩) (f := ⟨f, hfH⟩)
    (closure_pair_subtype_eq_top hs hs₁ hs₂) (Subtype.ext (by simpa using he))
    (Subtype.ext (by simpa using hf)) (Subtype.ext (by simpa using hef))
    (fun h => he1 (by simpa using congrArg Subtype.val h))
    (fun k hk h => hfe k hk (by simpa using congrArg Subtype.val h))
    (Subtype.ext (by simpa using h₁)) (Subtype.ext (by simpa using h₂)) T

end CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent
