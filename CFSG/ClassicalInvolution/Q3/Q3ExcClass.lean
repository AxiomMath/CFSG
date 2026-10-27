module

public import CFSG.ClassicalInvolution.Q3.Q3ExcDatum

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum CFSG.LieType.AlgebraicGroups
  CFSG.ClassicalInvolution.Upgrade
open scoped Pointwise MatrixGroups

variable {τ : Tag} {p₀ : ℕ} [Fact p₀.Prime] {k : Type} [Field k] [CharP k p₀] [IsAlgClosed k]
  {D : OrthogonalSemilinearFixedRootDatum τ p₀ k}

theorem exc3_orbits_nonempty : D.orbits.Nonempty := by
  obtain ⟨i₀, hJ⟩ := D.isThetaOrbit
  obtain ⟨α₀, hα₀⟩ := Quotient.exists_rep i₀
  have hα₀K : α₀.1 ∈ componentRoots D.χ i₀ := ⟨α₀.2, by rw [← hα₀]⟩
  have hi₀ : i₀ ∈ D.J := by
    rw [hJ]
    exact ⟨0, α₀.1, hα₀K, α₀.1, hα₀K, by simp⟩
  obtain ⟨-, -, β₀, hβ₀, -⟩ := exists_smul_simpleRoot (isRootComponent_componentRoots i₀) hα₀K
  exact ⟨_, D.thetaOrbit_mem_orbits (D.mem_simpleRootsJ_iff.2 ⟨i₀, hi₀, hβ₀⟩)⟩

theorem exc3_orbitGroup_big_or_small {c : ModGL τ k} (hc : Exc3Frob D c) (hq3 : p₀ ^ D.e = 3) :
    Exc3Big D.orbitGroup ∨ (Exc3Small D.orbitGroup ∧ ∃ β, D.orbits = {{β}}) := by
  classical
  have hne : D.orbits.Nonempty := exc3_orbits_nonempty
  have hfin : D.orbits.Finite := CFSG.ClassicalInvolution.Upgrade.finite_orbits D
  have hq := orthogonal_semilinear_fixed_root_quasisimplicity D
  by_cases h2 : 2 ≤ D.orbits.ncard
  · exact Or.inl (hc.exc3Big_orbitGroup hq3 (hq.2.2.1 h2))
  · have hcard : D.orbits.ncard = 1 := by
      have := (Set.ncard_pos hfin).2 hne
      omega
    obtain ⟨O, hO⟩ := Set.ncard_eq_one.1 hcard
    have hOm : O ∈ D.orbits := by rw [hO]; exact Set.mem_singleton O
    by_cases h3 : 3 < Nat.card (D.orbitField O)
    · exact Or.inl (hc.exc3Big_orbitGroup hq3 (hq.2.2.2.1 O hO h3))
    · refine Or.inr ?_
      have h3' : Nat.card (D.orbitField O) = 3 :=
        le_antisymm (by omega) (D.three_le_card_orbitField hOm)
      have hcard1 : orbitCard O = 1 := D.orbitCard_eq_one_of_card hOm (by omega)
      obtain ⟨β, hβ⟩ := Set.ncard_eq_one.1 hcard1
      refine ⟨?_, β, by rw [hO, hβ]⟩
      have hp3 : p₀ = 3 := ((Nat.prime_three.pow_eq_iff).1 hq3).1
      have hfinO : Finite (D.orbitField O) := Nat.finite_of_card_ne_zero (by omega)
      have : Fintype (D.orbitField O) := Fintype.ofFinite _
      have : CharP (D.orbitField O) 3 := hp3 ▸ inferInstance
      have hcard3 : Fintype.card (D.orbitField O) = 3 := by
        rw [← Nat.card_eq_fintype_card, h3']
      set φ := ZMod.ringEquiv (D.orbitField O) hcard3 with hφ
      set f := (D.orbitGroupHom hOm).comp (Matrix.SpecialLinearGroup.map φ.toRingHom) with hf
      have hmapinj : Function.Injective (Matrix.SpecialLinearGroup.map (n := Fin 2)
          φ.toRingHom) := by
        intro A B h
        ext i j
        have := congrArg (fun M : SL(2, D.orbitField O) =>
          (M : Matrix (Fin 2) (Fin 2) (D.orbitField O)) i j) h
        simpa [Matrix.SpecialLinearGroup.map_apply_coe] using this
      have hmapsurj : Function.Surjective (Matrix.SpecialLinearGroup.map (n := Fin 2)
          φ.toRingHom) := by
        intro A
        refine ⟨Matrix.SpecialLinearGroup.map φ.symm.toRingHom A, ?_⟩
        ext i j
        simp [Matrix.SpecialLinearGroup.map_apply_coe]
      have hsurj : Function.Surjective f := (D.orbitGroupHom_surjective hOm hO).comp hmapsurj
      have hinj : Function.Injective f := fun A B h =>
        hmapinj (CFSG.ClassicalInvolution.ModelFacts.orbitMap_injective_of_orbitCard_eq_one D
          hcard1 (congrArg Subtype.val h))
      exact ⟨MulEquiv.ofBijective f ⟨hinj, hsurj⟩⟩

end CFSG.ClassicalInvolution.Q3
