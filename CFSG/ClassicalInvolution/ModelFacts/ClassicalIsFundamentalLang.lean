module

public import CFSG.LieType.AlgebraicGroups.RationalInnerDiagonal

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {τ : Tag} {K : Type} [Field K] [Finite K]

theorem exists_conj_eq_rootDiagUnit_of_involution
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E8) (hK : Odd (Nat.card K))
    (z : ↥(adjointGroup τ K)) (hz : z * z = 1) :
    ∃ (g : ↥(adjointGroup τ K)) (b : Fin τ.rank → Kˣ), (∀ i, b i = 1 ∨ b i = -1) ∧
      ((g * z * g⁻¹ : ↥(adjointGroup τ K)) : ModGL τ K) = rootDiagUnit τ b := by
  classical
  have : Fintype K := Fintype.ofFinite K
  set L := AlgebraicClosure K
  set ι := algebraMap K L with hι
  set p := ringChar K with hp_def
  have hpK : CharP K p := ringChar.charP K
  obtain ⟨n, hp, hcard⟩ := FiniteField.card K p
  have : Fact p.Prime := ⟨hp⟩
  have : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  set Fr := iterateFrobenius L p n with hFr_def
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hFr_def, iterateFrobenius_def, Nat.card_eq_fintype_card, hcard]
  set x := baseChangeGL ι (z : ModGL τ K) with hx_def
  obtain ⟨-, hHR, -, -⟩ := exceptional_Lang_Frobenius_fixed_derived_root_group τ K hK L Fr hFr
  have hxR : x ∈ adjointGroup τ L ⊓ (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _) :=
    hHR (Subgroup.mem_map_of_mem _ z.2)
  have hx2 : x ^ 2 = 1 := by
    have h1 : (z : ModGL τ K) * (z : ModGL τ K) = 1 := congrArg Subtype.val hz
    rw [hx_def, sq, ← map_mul, h1, map_one]
  obtain ⟨h, hhR, a, ha, hhx, -⟩ :=
    G2_F4_E6_E8_rational_inner_diagonal_involution_fixed_p_components τ K L hτ hK Fr hFr hxR hx2
  obtain ⟨c, u, hu, hhc⟩ := exists_rootDiagUnit_mul_of_frobenius_fixed τ Fr hFr hhR.1 hhR.2
  obtain ⟨g', hg', rfl⟩ := Subgroup.mem_map.1 hu
  have hcomm : baseChangeGL ι (rootDiagUnit τ c) * rootDiagUnit τ a =
      rootDiagUnit τ a * baseChangeGL ι (rootDiagUnit τ c) := by
    rw [baseChangeGL_rootDiagUnit, ← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]
  have hhc' : h = baseChangeGL ι (rootDiagUnit τ c) * baseChangeGL ι g' := hhc
  have hux : baseChangeGL ι g' * x * (baseChangeGL ι g')⁻¹ = rootDiagUnit τ a := by
    have h1 : h * x * h⁻¹ = baseChangeGL ι (rootDiagUnit τ c) *
        (baseChangeGL ι g' * x * (baseChangeGL ι g')⁻¹) *
          (baseChangeGL ι (rootDiagUnit τ c))⁻¹ := by
      rw [hhc']
      group
    rw [hhx] at h1
    calc baseChangeGL ι g' * x * (baseChangeGL ι g')⁻¹ =
        (baseChangeGL ι (rootDiagUnit τ c))⁻¹ *
          (baseChangeGL ι (rootDiagUnit τ c) *
            (baseChangeGL ι g' * x * (baseChangeGL ι g')⁻¹) *
              (baseChangeGL ι (rootDiagUnit τ c))⁻¹) * baseChangeGL ι (rootDiagUnit τ c) := by
          group
      _ = (baseChangeGL ι (rootDiagUnit τ c))⁻¹ * rootDiagUnit τ a *
          baseChangeGL ι (rootDiagUnit τ c) := by rw [← h1]
      _ = rootDiagUnit τ a := by
          rw [mul_assoc, ← hcomm]
          group
  set b : Fin τ.rank → Kˣ := fun i => if a i = 1 then 1 else -1 with hb_def
  have hb : ∀ i, b i = 1 ∨ b i = -1 := fun i => by
    by_cases h1 : a i = 1 <;> simp [hb_def, h1]
  have hab : (fun i => Units.map ι.toMonoidHom (b i)) = a := by
    funext i
    by_cases h1 : a i = 1
    · simp [hb_def, h1]
    · have h2 : a i = -1 := (ha i).resolve_left h1
      rw [h2]
      simp only [hb_def, h1, ↓reduceIte]
      exact Units.ext (by simp)
  refine ⟨⟨g', hg'⟩, b, hb, ?_⟩
  change g' * (z : ModGL τ K) * g'⁻¹ = rootDiagUnit τ b
  apply baseChangeGL_injective ι
  rw [map_mul, map_mul, map_inv, baseChangeGL_rootDiagUnit, hab]
  exact hux

end CFSG.ClassicalInvolution.ModelFacts
