module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10RSeitzCubeTriOpp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10RSeitzCubeStd

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.ChevTwo CFSG.LieType.ChevTwo.Semi
  CFSG.LieType.Chevalley CFSG.StandardType CFSG.GH74.GLS.Stage2.OddAut

section Certs


theorem seitzTwoGen_of_twistedChevalleyModel_D4 {S : Type} [Group S] [Finite S] {f : ℕ}
    (hf : 1 ≤ f) (h : TwistedChevalleyModel S .D4 (2 ^ f)) : SeitzTwoGen S := by
  obtain ⟨K, _, hfin, hcard, σ, hσ, ⟨e⟩⟩ := h
  obtain ⟨σ', rfl⟩ : ∃ σ' : K ≃+* K, σ'.toRingHom = σ :=
    ⟨RingEquiv.ofBijective σ ⟨σ.injective, Finite.surjective_of_injective σ.injective⟩,
      RingHom.ext fun _ => rfl⟩
  have hK : Nat.card K = (2 ^ f) ^ 3 := hcard
  obtain ⟨-, -, -, -, -, -, -, ⟨e'⟩⟩ :=
    even_triality_exact_automorphism_normal_form hf K hK σ' hσ
  have hK3 : Nat.card K = 2 ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  haveI hK2 : CharP K 2 := charP_two_of_card_two_pow hK3
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hfinM : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have hσ3 : σ' ^ 3 = 1 := RingEquiv.ext fun c => by
    rw [pow_succ, pow_two]
    exact ringEquiv_cube_apply_eq hK hσ c
  have hσ3' : σ' ^ TwistTag.D4.order = 1 := hσ3
  refine seitzTwoGen_of_mulEquiv (e.trans e').symm ?_
  refine seitzTwoGen_of_family
    (fun j : {J : Set (Fin TwistTag.D4.foldedTag.rank) // J ≠ Set.univ} => radTri K σ' j.1)
    (fun j => parTri K σ' j.1) ?_ ?_ ?_ ?_
  · intro j
    exact isPGroup_radTri σ' j.1
  · intro j
    obtain ⟨-, -, -, -, -, -, -, -, hQ₀P, hQ₀n, -⟩ :=
      diagram_fixed_parabolic_root_radical_Levi_factors (t := TwistTag.D4) K σ' j.1
    have hPQ₀ := (Subgroup.normal_subgroupOf_iff_le_normalizer hQ₀P).1 hQ₀n
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hx' := hPQ₀ (Subgroup.mem_subgroupOf.1 hx)
    simp only [radTri, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.1 hx' y
  · intro Q hQ0 hQ2
    have hQ₀ne : Q.map (graphFixedRootGroup TwistTag.D4 K σ'.toRingHom).subtype ≠ ⊥ :=
      fun hbot => hQ0 ((Subgroup.map_eq_bot_iff_of_injective Q
        (graphFixedRootGroup TwistTag.D4 K σ'.toRingHom).subtype_injective).1 hbot)
    obtain ⟨g, hg, J, hP, hQJ⟩ := CFSG.LieType.Chevalley.EvenOddRadical.exists_optimal_radical_fixed
      (t := TwistTag.D4) σ' hσ3'
      (Subgroup.map_subtype_le Q)
      (hQ2.map (graphFixedRootGroup TwistTag.D4 K σ'.toRingHom).subtype) hQ₀ne
    have hJ : J ≠ Set.univ := by
      rintro rfl
      apply hQ₀ne
      refine eq_bot_iff.2 fun q hq => ?_
      have h1 := hQJ q hq
      rw [CFSG.StandardType.GGOppRadExc.graphFixedParabolicRadical_univ (t := TwistTag.D4) σ'] at h1
      have h2 : q = 1 := by
        have := congrArg (fun z => g * z * g⁻¹) (Subgroup.mem_bot.1 h1)
        simpa [mul_assoc] using this
      rw [h2]
      exact Subgroup.one_mem _
    refine ⟨⟨g, hg⟩, ⟨J, hJ⟩, ?_, ?_⟩
    · intro x hx
      exact Subgroup.mem_subgroupOf.2 (hP x x.2 (mem_normalizer_map_subtype hx))
    · intro q hq
      exact Subgroup.mem_subgroupOf.2 (hQJ q ⟨q, hq, rfl⟩)
  · intro j p hp hp2 R hR hQR hNQ
    exact seitzCubeTri_hcore σ' hf hK hσ j.1 j.2 p hp hp2 hR hQR hNQ

end Certs

end CFSG.LocalAnalysis.GLTheoremA.Y10F
