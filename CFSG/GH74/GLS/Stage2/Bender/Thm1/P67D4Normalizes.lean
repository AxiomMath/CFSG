module

public import CFSG.LieType.Chevalley.FixedRootCentralizerGeneration
public import CFSG.RankThree.PartOne.CTP.SeitzFineG2

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.CTP

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

theorem closure_centralizers_graphFixed_D4_of_normalizes {p f : ℕ} (hp : p.Prime) (hp3 : p ≠ 3)
    (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 3)
    (σ : K ≃+* K) (hσ3 : σ ^ TwistTag.D4.order = 1)
    [IsSimpleGroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)]
    (E : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    [IsElementaryAbelian 3 E] (hEcard : Nat.card E = 3 ^ 2)
    (R : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hRp : IsPGroup p R)
    (hR : R ≠ ⊥) (hER : E ≤ Subgroup.normalizer (R : Set (graphFixedRootGroup TwistTag.D4 K
      σ.toRingHom))) :
    Subgroup.closure {k : graphFixedRootGroup TwistTag.D4 K σ.toRingHom |
      ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} = ⊤ := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK3 : Nat.card K = p ^ (f * 3) := by rw [hK, pow_mul]
  have : CharP K p := finite_field_prime_power_characteristic hp (by omega) hK3
  let C : Subgroup (ModGL TwistTag.D4.tag K) := graphFixedRootGroup TwistTag.D4 K σ.toRingHom
  let A : Subgroup (ModGL TwistTag.D4.tag K) := E.map C.subtype
  have hAC : A ≤ C := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have : IsElementaryAbelian 3 A := IsElementaryAbelian.map _
  have hcardA : 3 ^ 2 ≤ Nat.card A := by
    rw [Subgroup.card_map_of_injective C.subtype_injective, hEcard]
  have hRC : R.map C.subtype ≤ C := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hR' : R.map C.subtype ≠ ⊥ := by
    intro h
    apply hR
    rw [eq_bot_iff]
    intro x hx
    have : C.subtype x ∈ R.map C.subtype := ⟨x, hx, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.2 (Subtype.ext this)
  have hAR : A ≤ Subgroup.normalizer ((R.map C.subtype : Subgroup (ModGL TwistTag.D4.tag K)) :
      Set (ModGL TwistTag.D4.tag K)) := by
    rintro _ ⟨e, he, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact ⟨e * r * e⁻¹, (Subgroup.mem_normalizer_iff.1 (hER he) r).1 hr, rfl⟩
    · rintro ⟨r, hr, hry⟩
      refine ⟨e⁻¹ * r * e, ?_, ?_⟩
      · have h := (Subgroup.mem_normalizer_iff.1 (hER (E.inv_mem he)) r).1 hr
        rwa [inv_inv] at h
      · change (e : ModGL TwistTag.D4.tag K)⁻¹ * (r : ModGL TwistTag.D4.tag K) *
          (e : ModGL TwistTag.D4.tag K) = y
        rw [show (r : ModGL TwistTag.D4.tag K) = e * y * e⁻¹ from hry]
        simp [mul_assoc]
  have hmain := fixed_root_invariant_prime_subgroup_centralizer_generation TwistTag.D4 K p 3
    hp3 σ hσ3 A hAC hcardA (R.map C.subtype) hRC (hRp.map C.subtype) hR' hAR
  exact closure_centralizers_of_iSup_eq C E hmain

end CFSG.GH74.GLS.Stage2.Bender.Thm1
