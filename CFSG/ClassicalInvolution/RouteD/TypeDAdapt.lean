module

public import CFSG.ClassicalInvolution.RouteD.TypeDChain
public import CFSG.ClassicalInvolution.RouteD.LocalTwinAdapt

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.LieType CFSG.LieType.RootSystem CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.CurtisTits CFSG.Timmesfeld CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Generic (Commutes conjSub FundamentalSingleClass
  fundamentalSubgroups modelUniv InClass IsClassicalMember LocalOddCentral ExactMembers
  centralizingMembers)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)

variable {p f : ℕ} [Fact p.Prime]

theorem exists_equiv_cartan_plus {m : ℕ} (hm : 3 ≤ m) :
    ∃ e : Fin (modelUniv .POmegaPlus m p f Fact.out).D.rank ≃ Fin m,
      ∀ a b, (modelUniv .POmegaPlus m p f Fact.out).D.cartan a b = cartanD m (e a) (e b) := by
  rw [modelUniv_POmegaPlus_eq (p := p) (f := f) hm]
  exact ⟨Equiv.refl _, fun _ _ => rfl⟩

theorem standardPair_plusDatum_of_cartan {F : Type} [Field F] [Finite F] {m : ℕ} (hm3 : 3 ≤ m)
    {i j : Fin m} (h : cartanD m i j = -1) :
    ∃ W, LinearBlockStandardPair F W (rankOne (plusDatum m F hm3).rootGroup i)
      (rankOne (plusDatum m F hm3).rootGroup j) := by
  rw [LevisSpin.cartanD_apply] at h
  by_cases h1 : i = j
  · simp [h1] at h
  · have h2 : (i.val + 1 = j.val ∧ j.val + 1 < m) ∨ (j.val + 1 = i.val ∧ i.val + 1 < m) ∨
        (i.val + 3 = m ∧ j.val + 1 = m) ∨ (j.val + 3 = m ∧ i.val + 1 = m) := by
      by_contra h2
      simp [h1, h2] at h
    rcases h2 with h2 | h2 | h2 | h2
    · exact standardPair_plusDatum_edge hm3 (Or.inl h2)
    · obtain ⟨W, hW⟩ := standardPair_plusDatum_edge (F := F) hm3 (i := j) (j := i) (Or.inl h2)
      exact ⟨W, CFSG.ClassicalInvolution.Generic.linearBlockStandardPair_symm hW⟩
    · exact standardPair_plusDatum_edge hm3 (Or.inr h2)
    · obtain ⟨W, hW⟩ := standardPair_plusDatum_edge (F := F) hm3 (i := j) (j := i) (Or.inr h2)
      exact ⟨W, CFSG.ClassicalInvolution.Generic.linearBlockStandardPair_symm hW⟩

namespace TCtx

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G} {K : Subgroup G}

theorem exists_nodes_plus' {m : ℕ} (hm : 4 ≤ m) (c : TCtx p f .POmegaPlus m Ω K z)
    (e : Fin (modelUniv .POmegaPlus m p f Fact.out).D.rank ≃ Fin m)
    (he : ∀ a b, (modelUniv .POmegaPlus m p f Fact.out).D.cartan a b = cartanD m (e a) (e b)) :
    ∃ j : Fin (modelUniv .POmegaPlus m p f Fact.out).D.rank → Subgroup G,
      (∀ a, j a ∈ centralizingMembers Ω {z} ∧ j a ≠ K ∧ ¬ locImg Ω z (j a) ≤ c.d.Q₁) ∧
      (∀ a, locImg Ω z (j a) =
        (rankOne (modelUniv .POmegaPlus m p f Fact.out).D.rootGroup a).map c.d.ψ) ∧
      (∀ a, Commutes K (j a)) ∧
      (∀ a b, a ≠ b → ¬ edgeD m (e a) (e b) → ¬ edgeD m (e b) (e a) → Commutes (j a) (j b)) ∧
      (∀ a b, edgeD m (e a) (e b) → ∃ W : Subgroup G,
        LinearBlockStandardPair (GaloisField p f) W (j a) (j b)) := by
  have hm3 : 3 ≤ m := by omega
  have hR : ∀ a, rankOne (modelUniv .POmegaPlus m p f Fact.out).D.rootGroup a ∈
      fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus m p f Fact.out).D := by
    rw [modelUniv_POmegaPlus_eq (p := p) (f := f) hm3]
    exact fun a => rankOne_mem_fundamentalSubgroups_plusDatum hm3 a
  have hcomm : ∀ a b : Fin (modelUniv .POmegaPlus m p f Fact.out).D.rank,
      (modelUniv .POmegaPlus m p f Fact.out).D.cartan a b = 0 →
      Commutes (rankOne (modelUniv .POmegaPlus m p f Fact.out).D.rootGroup a)
        (rankOne (modelUniv .POmegaPlus m p f Fact.out).D.rootGroup b) := by
    rw [modelUniv_POmegaPlus_eq (p := p) (f := f) hm3]
    exact fun a b h => commutes_rankOne_plusDatum hm3 h
  have hstd : ∀ a b : Fin (modelUniv .POmegaPlus m p f Fact.out).D.rank,
      (modelUniv .POmegaPlus m p f Fact.out).D.cartan a b = -1 →
      ∃ W : Subgroup (modelUniv .POmegaPlus m p f Fact.out).K,
        LinearBlockStandardPair (GaloisField p f) W
          (rankOne (modelUniv .POmegaPlus m p f Fact.out).D.rootGroup a)
          (rankOne (modelUniv .POmegaPlus m p f Fact.out).D.rootGroup b) := by
    rw [modelUniv_POmegaPlus_eq (p := p) (f := f) hm3]
    exact fun a b h => standardPair_plusDatum_of_cartan hm3 h
  have heinj : ∀ a b, a ≠ b → e a ≠ e b := fun a b hab h => hab (e.injective h)
  obtain ⟨j, hj, hjc, hjp, hjK⟩ := c.exists_nodes
    (fun a => rankOne (modelUniv .POmegaPlus m p f Fact.out).D.rootGroup a) hR
    (fun a b => edgeD m (e a) (e b))
    (fun a b hab h1 h2 => hcomm a b (by rw [he]; exact (LevisSpin.cartanD_of_not_edgeD
      (heinj a b hab) h1 h2).1))
    (fun a b h => hstd a b (by rw [he]; exact (LevisSpin.cartanD_of_edgeD h).1))
  exact ⟨j, fun a => ⟨(hj a).1, (hj a).2.1, (hj a).2.2.1⟩, fun a => (hj a).2.2.2, hjK, hjc, hjp⟩

end TCtx

theorem PartnerPatternD.of_toral {G : Type} [Group G] [Finite G] {m : ℕ} (hm : 4 ≤ m)
    {Ω : Set (Subgroup G)} {z : G} {K β : Subgroup G} (c : TCtx p f .POmegaPlus m Ω K z) {t : G}
    (ht : t * z * t⁻¹ = z)
    (e : Fin (modelUniv .POmegaPlus m p f Fact.out).D.rank ≃ Fin m)
    {j : Fin (modelUniv .POmegaPlus m p f Fact.out).D.rank → Subgroup G}
    (hj : ∀ a, j a ∈ centralizingMembers Ω {z}) (hjK : ∀ a, Commutes K (j a))
    (hjimg : ∀ a, locImg Ω z (j a) =
      (rankOne (modelUniv .POmegaPlus m p f Fact.out).D.rootGroup a).map c.d.ψ)
    (hjc : ∀ a b, a ≠ b → ¬ edgeD m (e a) (e b) → ¬ edgeD m (e b) (e a) → Commutes (j a) (j b))
    (hjp : ∀ a b, edgeD m (e a) (e b) → ∃ W : Subgroup G,
      LinearBlockStandardPair (GaloisField p f) W (j a) (j b))
    (v : Fin (modelUniv .POmegaPlus m p f Fact.out).D.rank → ZMod 2)
    (hT : ∀ γ ∈ (modelUniv .POmegaPlus m p f Fact.out).D.roots,
      (∀ x ∈ ((modelUniv .POmegaPlus m p f Fact.out).D.rootGroup γ ⊔
          (modelUniv .POmegaPlus m p f Fact.out).D.rootGroup (-γ)).map c.d.ψ,
        Gaps.locAut c.hΩ.conjInvariant ht x = x) ↔ charOf v γ = 0)
    (hE : CharReach (modelUniv .POmegaPlus m p f Fact.out).D.cartan v
      (Pi.single (e.symm ⟨0, by omega⟩) 1))
    (hS : ∀ y ∈ locLayer Ω z,
      (∀ b, (∀ x ∈ locImg Ω z (conjSub y (j b)), Gaps.locAut c.hΩ.conjInvariant ht x = x) ↔
        b ≠ e.symm ⟨0, by omega⟩) →
      ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W β
        (conjSub y (j (e.symm ⟨0, by omega⟩)))) :
    PartnerPatternD p f m Ω K β t := by
  have hf1 : 1 ≤ f := Nat.one_le_iff_ne_zero.mpr c.hf
  have hadm : StatedLieAdmissible .POmegaPlus m p f := ⟨Fact.out, hf1, by show 4 ≤ m; omega⟩
  obtain ⟨n, H, hct, -⟩ := ModelFacts.hasBruhatDatum .POmegaPlus m p f Fact.out trivial hadm
  obtain ⟨y, hy, hfix⟩ := c.exists_adapted_y_of_reach hct ht v hT hE hjimg
  have hfix' : ∀ b, (∀ x ∈ locImg Ω z (conjSub y (j b)),
      Gaps.locAut c.hΩ.conjInvariant ht x = x) ↔ b ≠ e.symm ⟨0, by omega⟩ := fun b => by
    rw [hfix b, Pi.single_apply]
    by_cases h : b = e.symm ⟨0, by omega⟩
    · simp [h]
    · simp [h]
  refine PartnerPatternD.of_locAut c (j := fun a : Fin m => j (e.symm a)) (fun a => hj _)
    (fun a => hjK _) ?_ ?_ hy ht ?_ ?_
  · intro a b hab h1 h2
    exact hjc _ _ (fun hh => hab (e.symm.injective hh)) (by simpa using h1) (by simpa using h2)
  · intro a b h
    exact hjp _ _ (by simpa using h)
  · intro a ha x hx
    refine (hfix' (e.symm a)).mpr (fun h => ?_) x hx
    have := e.symm.injective h
    have := congrArg Fin.val this
    simp only at this
    omega
  · intro a ha
    have h0 : e.symm a = e.symm ⟨0, by omega⟩ := congrArg e.symm (Fin.ext ha)
    show ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W β (conjSub y (j (e.symm a)))
    rw [h0]
    exact hS y hy hfix'

end CFSG.ClassicalInvolution.RouteD
