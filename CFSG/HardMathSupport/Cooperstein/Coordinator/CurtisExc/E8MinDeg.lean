module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.E8Adj

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc

open CFSG.Quasithin.SmithCurtis CFSG.Quasithin.SmithCurtis.Chev CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley


theorem e8_two_min_degree_of_nontrivial {F : Type} [Field F] [CharP F 2] {V : Type}
    [AddCommGroup V] [Module F V] [Module.Finite F V]
    {ρ : Representation F (adjointGroup .E8 (ZMod 2)) V} (hρ : IsSimpleRep ρ)
    (hnt : ∃ (g : adjointGroup .E8 (ZMod 2)) (v : V), ρ g v ≠ v) :
    248 ≤ Module.finrank F V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Algebra (ZMod 2) F := (ιF F).toAlgebra
  obtain ⟨y, χ, J, ht⟩ := exists_isChevType (hw := exists_weyl_neg_E8) (p := 2) hρ
  have hy0 : y ≠ 0 := ht.2.1
  have hχ : ∀ h ∈ e8Datum.H, χ h = 1 := by
    intro h hh
    have h1 := ht.2.2.1 h hh
    have e : ρ h y = y := by rw [torus_eq_one hh, map_one, Module.End.one_apply]
    rw [e] at h1
    exact smul_left_injective F hy0 (show χ h • y = (1 : F) • y by
      rw [one_smul]; exact h1.symm)
  by_cases hJ : ∃ s, s ∉ J ∧ s ≠ n8
  · obtain ⟨s, hs, hs8⟩ := hJ
    obtain ⟨w, hw⟩ := exists_orbit_e8Omega s (fun h => hs8 (Fin.ext h))
    exact card_le_finrank_of_isChevType hρ ht hs (reflect_e8Omega s) w hw
  push Not at hJ
  by_cases h8 : n8 ∈ J
  · exfalso
    have hJU : J = Finset.univ := Finset.eq_univ_of_forall fun s => by
      by_contra hs
      exact hs (hJ s hs ▸ h8) |>.elim
    set ρ0 : Representation F (adjointGroup .E8 (ZMod 2)) (Unit →₀ F) :=
      Representation.trivial F _ (Unit →₀ F) with hρ0def
    have hρ0 : IsSimpleRep ρ0 := by
      refine ⟨⟨⟨0, Finsupp.single () 1, fun h => by simpa using congrArg (fun f => f ()) h⟩⟩,
        fun W _ => ?_⟩
      by_cases hW : W = ⊥
      · exact Or.inl hW
      right
      obtain ⟨f, hfW, hf0⟩ := (Submodule.ne_bot_iff W).1 hW
      have hf : f = f () • Finsupp.single () 1 := Finsupp.ext fun u => by cases u; simp
      have hc : f () ≠ 0 := fun h => hf0 (by rw [hf, h, zero_smul])
      generalize f () = c at hf hc
      have hs : Finsupp.single () (1 : F) ∈ W := by
        have := W.smul_mem c⁻¹ hfW
        rwa [hf, smul_smul, inv_mul_cancel₀ hc, one_smul] at this
      refine eq_top_iff.2 fun g _ => ?_
      have : g = g () • Finsupp.single () 1 := Finsupp.ext fun u => by cases u; simp
      rw [this]
      exact Submodule.smul_mem _ _ hs
    have ht0 : IsChevType .E8 (ZMod 2) 2 exists_weyl_neg_E8 ρ0 (Finsupp.single () (1 : F))
        χ J := by
      refine ⟨fun u _ => by simp [hρ0def], fun h => by simpa using congrArg (fun f => f ()) h,
        fun h hh => ?_, fun i => ?_⟩
      · simp [hρ0def, hχ h hh]
      · have hχ' : ∀ t : (ZMod 2)ˣ, χ (dC .E8 (ZMod 2) i t) = 1 := fun t => hχ _ (dC_mem_H i t)
        have hT : e8Datum.heckeT ρ0 i (Finsupp.single () (1 : F)) = 0 := by
          unfold e8Datum
          rw [heckeT_chevDatum]
          simp only [hρ0def, Representation.trivial_apply, Finset.sum_const, Finset.card_univ,
            ZMod.card]
          rw [← Nat.cast_smul_eq_nsmul F]
          have : ((2 : ℕ) : F) = 0 := by exact_mod_cast CharTwo.two_eq_zero
          rw [this, zero_smul]
        simp only [hJU, Finset.mem_univ, hχ', implies_true, true_and, true_iff]
        exact hT
    obtain ⟨β, hβ⟩ := iso_of_isChevType hρ hρ0 ht ht0
    obtain ⟨g, v, hgv⟩ := hnt
    apply hgv
    apply β.injective
    rw [hβ]
    simp [hρ0def]
  · have hJe : J = Finset.univ.erase n8 := by
      ext s
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      constructor
      · rintro hs rfl; exact h8 hs
      · intro hs
        by_contra hsJ
        exact hs (hJ s hsJ)
    subst hJe
    obtain ⟨β, -⟩ := iso_of_isChevType hρ isSimpleRep_adj ht (adj_isChevType χ hχ)
    rw [β.finrank_eq, finrank_adjMod]

theorem e8_two_min_degree {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {ρ : Representation (ZMod 2) (adjointGroup .E8 (ZMod 2)) V} (hρ : IsSimpleRep ρ)
    (hfaith : Function.Injective ρ) : 248 ≤ Module.finrank (ZMod 2) V := by
  have : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  refine e8_two_min_degree_of_nontrivial hρ ?_
  by_contra hcon
  push Not at hcon
  have h1 : xC .E8 (ZMod 2) n8 1 = 1 :=
    hfaith (by ext v; rw [hcon, map_one, Module.End.one_apply])
  exact xC_ne_one n8 1 h1

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc
