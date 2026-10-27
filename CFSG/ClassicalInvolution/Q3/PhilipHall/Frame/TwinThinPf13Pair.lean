module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf13Z

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC CFSG.ClassicalInvolution.Q3.TC.Graph
  CFSG.ClassicalInvolution.Q3.TC.Thin
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

set_option linter.unusedSectionVars false

namespace TwinThin

variable {G : Type} [Group G] [Finite G] {K₀ K K' : Subgroup G} {z : G} {π : Set (Subgroup G)}
  {g : G}

theorem closure_comm_closure (S0 T0 : Set G) (h : ∀ s ∈ S0, ∀ t ∈ T0, s * t = t * s) :
    ∀ a ∈ Subgroup.closure S0, ∀ b ∈ Subgroup.closure T0, a * b = b * a := by
  have step1 : ∀ s ∈ S0, ∀ b ∈ Subgroup.closure T0, s * b = b * s := by
    intro s hs b hb
    have hle : Subgroup.closure T0 ≤ Subgroup.centralizer {s} := by
      refine (Subgroup.closure_le _).mpr ?_
      intro t ht
      exact Subgroup.mem_centralizer_singleton_iff.mpr (h s hs t ht).symm
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hb)).symm
  intro a ha b hb
  have hle : Subgroup.closure S0 ≤ Subgroup.centralizer {b} := by
    refine (Subgroup.closure_le _).mpr ?_
    intro t ht
    exact Subgroup.mem_centralizer_singleton_iff.mpr (step1 t ht b hb)
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle ha)

theorem conj_closure {U : Set G} {x : G} (h : ∀ s ∈ U, x * s * x⁻¹ ∈ Subgroup.closure U) :
    ∀ d ∈ Subgroup.closure U, x * d * x⁻¹ ∈ Subgroup.closure U := by
  intro d hd
  induction hd using Subgroup.closure_induction with
  | mem t ht => exact h t ht
  | one => simpa using (Subgroup.closure U).one_mem
  | mul a b ha hb iha ihb =>
    have := (Subgroup.closure U).mul_mem iha ihb
    simpa [mul_assoc] using this
  | inv a ha iha =>
    have := (Subgroup.closure U).inv_mem iha
    simpa [mul_assoc] using this

theorem gens_conj {U : Set G} {Pm : Set (Subgroup G)}
    (h : ∀ M ∈ Pm, ∀ y ∈ M, ∀ s ∈ U, y * s * y⁻¹ ∈ Subgroup.closure U) :
    ∀ x ∈ (⨆ M ∈ Pm, M : Subgroup G), ∀ s ∈ U, x * s * x⁻¹ ∈ Subgroup.closure U := by
  intro x hx
  refine Subgroup.iSup_induction (fun M : Subgroup G => ⨆ _ : M ∈ Pm, M)
    (C := fun x => ∀ s ∈ U, x * s * x⁻¹ ∈ Subgroup.closure U) hx ?_ ?_ ?_
  · intro M y hy
    refine Subgroup.iSup_induction (fun _ : M ∈ Pm => M)
      (C := fun x => ∀ s ∈ U, x * s * x⁻¹ ∈ Subgroup.closure U) hy ?_ ?_ ?_
    · intro hM y hy
      exact h M hM y hy
    · intro s hs; simpa using Subgroup.subset_closure hs
    · intro a b ha hb s hs
      have := conj_closure ha _ (hb s hs)
      simpa [mul_assoc] using this
  · intro s hs; simpa using Subgroup.subset_closure hs
  · intro a b ha hb s hs
    have := conj_closure ha _ (hb s hs)
    simpa [mul_assoc] using this

theorem Dz_eq (K : Subgroup G) (π : Set (Subgroup G)) (g : G) :
    Dz K π g = Subgroup.closure (Zset π ∪ Zset (fam K (conjSub g (piGen π)))) := by
  apply le_antisymm
  · refine (Subgroup.closure_le _).mpr ?_
    rintro x (hx | hx)
    · exact Subgroup.closure_mono Set.subset_union_left hx
    · exact Subgroup.closure_mono Set.subset_union_right hx
  · refine (Subgroup.closure_le _).mpr ?_
    rintro x (hx | hx)
    · exact Subgroup.subset_closure (Or.inl (Subgroup.subset_closure hx))
    · exact Subgroup.subset_closure (Or.inr (Subgroup.subset_closure hx))

@[expose] def ThinCrossPair (K : Subgroup G) (π : Set (Subgroup G)) (g : G) : Prop :=
  (∀ J ∈ π, ∀ L ∈ fam K (conjSub g (piGen π)), ∀ u v : G, IsUniqueInvolution J u →
      IsUniqueInvolution L v → u * v = v * u) ∧
  (∀ J ∈ π, ∀ x ∈ J, ∀ L ∈ fam K (conjSub g (piGen π)), ∀ v : G, IsUniqueInvolution L v →
      x * v * x⁻¹ ∈ Dz K π g) ∧
  (∀ L ∈ fam K (conjSub g (piGen π)), ∀ x ∈ L, ∀ J ∈ π, ∀ u : G, IsUniqueInvolution J u →
      x * u * x⁻¹ ∈ Dz K π g)

namespace Setting

variable (S : Setting K₀ K K' z π g)
include S

theorem thinCross_of_pair (hp : ThinCrossPair K π g) : ThinCross K π g := by
  obtain ⟨p1, p2, p3⟩ := hp
  refine ⟨?_, ?_, ?_⟩
  · refine closure_comm_closure _ _ ?_
    rintro s ⟨J, hJ, hs⟩ t ⟨L, hL, ht⟩
    exact p1 J hJ L hL s t hs ht
  · intro x hx e' he'
    have hQ : ∀ s ∈ Zset π ∪ Zset (fam K (conjSub g (piGen π))),
        x * s * x⁻¹ ∈ Dz K π g := by
      rw [Dz_eq]
      refine gens_conj (Pm := π) ?_ x hx
      intro J hJ y hy s hs
      rcases hs with ⟨J'', hJ'', hs⟩ | ⟨L, hL, hs⟩
      · exact Subgroup.subset_closure (Or.inl
          ⟨conjSub y J'', stable_of_maxOrb S.hos.graph S.hπ y (le_piGen hJ hy) J'' hJ'', hs.conj y⟩)
      · have := p2 J hJ y hy L hL s hs
        rwa [Dz_eq] at this
    have hmem : e' ∈ Subgroup.closure (Zset π ∪ Zset (fam K (conjSub g (piGen π)))) := by
      rw [← Dz_eq]
      exact Subgroup.subset_closure (Or.inr he')
    rw [Dz_eq]
    exact conj_closure (fun s hs => by have := hQ s hs; rwa [Dz_eq] at this) e' hmem
  · intro x hx e he
    have hx2 : x ∈ pSpan (fam K (conjSub g (piGen π))) := by rw [S.fam_gen]; exact hx
    have hQ : ∀ s ∈ Zset π ∪ Zset (fam K (conjSub g (piGen π))),
        x * s * x⁻¹ ∈ Dz K π g := by
      rw [Dz_eq]
      refine gens_conj (Pm := fam K (conjSub g (piGen π))) ?_ x hx2
      intro L hL y hy s hs
      rcases hs with ⟨J, hJ, hs⟩ | ⟨L'', hL'', hs⟩
      · have := p3 L hL y hy J hJ s hs
        rwa [Dz_eq] at this
      · have hyX : y ∈ conjSub g (piGen π) := by
          rw [← S.fam_gen]; exact le_pSpan hL hy
        exact Subgroup.subset_closure (Or.inr
          ⟨conjSub y L'', fam_inv L'' hL'' y hyX, hs.conj y⟩)
    have hmem : e ∈ Subgroup.closure (Zset π ∪ Zset (fam K (conjSub g (piGen π)))) := by
      rw [← Dz_eq]
      exact Subgroup.subset_closure (Or.inl he)
    rw [Dz_eq]
    exact conj_closure (fun s hs => by have := hQ s hs; rwa [Dz_eq] at this) e hmem

end Setting

end TwinThin

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
