module

public import CFSG.LocalAnalysis.OddStandard.GH71.S55D4Ord3Tor

public section

namespace CFSG.OddStandard.GH71.S55

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.GH74.GLS.Stage2.Bender.Thm1

section Basic

variable {K : Type} [Field K]
  (σ : K ≃+* K)

local notation "𝒞" => graphFixedRootGroup TwistTag.D4 K (RingEquiv.toRingHom σ)

theorem map_conj_U_of_torus {h : 𝒞}
    (hh : (h : ModGL TwistTag.D4.tag K) ∈ graphFixedTorus TwistTag.D4 K σ.toRingHom) :
    ((graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf 𝒞).map
      (MulAut.conj h).toMonoidHom =
    (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf 𝒞 := by
  refine CFSG.LieType.Chevalley.map_conj_eq_of_mem_normalizer ?_
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  exact Subgroup.mem_normalizer_iff.1 (graphFixedTorus_le_normalizer_U σ hh) x

end Basic


variable {K : Type} [Field K] [Finite K] (σ : K ≃+* K)

local notation "𝒞" => graphFixedRootGroup TwistTag.D4 K (RingEquiv.toRingHom σ)

theorem d4_normalizesPSub_toral {ℓ : ℕ} [CharP K ℓ] {h : 𝒞}
    (hh : (h : ModGL TwistTag.D4.tag K) ∈ graphFixedTorus TwistTag.D4 K σ.toRingHom)
    (δ : K ≃+* K) : NormalizesPSub ℓ (MulAut.conj h * fieldActor (t := TwistTag.D4) σ δ) := by
  refine ⟨_, d4_U_ne_bot σ, isPGroup_graphFixedPosUnipotent_subgroupOf ℓ, ?_⟩
  rw [map_mulAut_mul, d4_fieldActor_map_U σ δ, map_conj_U_of_torus σ hh]

theorem d4_movesAbelianTwo {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = (p ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ (p ^ f)) (n : monoY σ)
    (hw3 : weylY σ n ^ 3 = 1) (hw1 : weylY σ n ≠ 1) (δ : K ≃+* K) :
    MovesAbelianTwo (MulAut.conj (n : 𝒞) * fieldActor (t := TwistTag.D4) σ δ) := by
  have hK3 : Nat.card K = p ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K p := finite_field_prime_power_characteristic hp (by omega) hK3
  have h2 : (2 : K) ≠ 0 := by
    intro h0
    have h2p : p ∣ 2 := (CharP.cast_eq_zero_iff K p 2).1 (by exact_mod_cast h0)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2p)
  have hle : graphFixedTorus TwistTag.D4 K σ.toRingHom ≤ 𝒞 :=
    (graphFixedTorus_le_graphFixedMonomial _ _ _).trans (d4_monomial_le_root hp hp2 K hK σ hσ)
  have hnM : ((n : 𝒞) : ModGL TwistTag.D4.tag K) ∈
      graphFixedMonomial TwistTag.D4 K σ.toRingHom := Subgroup.mem_subgroupOf.1 n.2
  have hδinv : (fieldActor (t := TwistTag.D4) σ δ)⁻¹ = fieldActor (t := TwistTag.D4) σ δ⁻¹ := by
    rw [← fieldActorHom_apply, ← fieldActorHom_apply, map_inv]
  have hEδ : (d4TorTwo σ).map (fieldActor (t := TwistTag.D4) σ δ).toMonoidHom = d4TorTwo σ :=
    map_d4TorTwo σ _ (fieldActor_torus σ δ) (fun x hx => by
      rw [hδinv]
      exact fieldActor_torus σ δ⁻¹ x hx)
  have hEn : (d4TorTwo σ).map (MulAut.conj (n : 𝒞)).toMonoidHom = d4TorTwo σ :=
    map_d4TorTwo σ _ (conj_torus σ hnM) (fun x hx => by
      rw [← map_inv]
      exact conj_torus σ (inv_mem hnM) x hx)
  refine ⟨d4TorTwo σ, isPGroup_d4TorTwo σ, d4TorTwo_comm σ, ?_, ?_⟩
  · rw [map_mulAut_mul, hEδ, hEn]
  · have hsign : ∀ c : Fin TwistTag.D4.tag.rank → ℤ, (∃ j, ∀ k,
        (TwistTag.D4.tag.cartan j k - c k) % 2 = 0) → (∀ i, c (TwistTag.D4.perm.symm i) = c i) →
        weylTuple (weylY σ n) (d4Sign K c) ≠ d4Sign K c →
        ∃ x ∈ d4TorTwo σ, (MulAut.conj (n : 𝒞) * fieldActor (t := TwistTag.D4) σ δ) x ≠ x := by
      intro c ⟨j, hj⟩ hρ hmove
      have hmem := rootDiagUnit_d4Sign_mem σ c j hj hρ
      refine ⟨⟨_, hle hmem⟩, ⟨hmem, Subtype.ext ?_⟩, fun h => hmove ?_⟩
      · change rootDiagUnit TwistTag.D4.tag (d4Sign K c) * rootDiagUnit TwistTag.D4.tag (d4Sign K c)
          = 1
        rw [← rootDiagUnit_mul, d4Sign_mul_self, rootDiagUnit_one]
      · have hδt : fieldActor (t := TwistTag.D4) σ δ ⟨_, hle hmem⟩ = ⟨_, hle hmem⟩ :=
          Subtype.ext (by
            rw [coe_fieldActor]
            exact entrywise_rootDiagUnit_d4Sign δ c)
        have h' := congrArg (fun y : 𝒞 => (y : ModGL TwistTag.D4.tag K)) h
        simp only [MulAut.mul_apply, hδt] at h'
        rw [coe_conj_rootDiagUnit_monoY σ n (d4Sign K c) _ rfl] at h'
        exact rootDiagUnit_injective h'
    rcases d4_weyl_moves_sign h2 (graphFixedWeylHom_mem _ _ _ _) hw3 hw1 with hA | hB
    · exact hsign d4ParA ⟨2, by decide⟩ (by decide) hA
    · exact hsign d4ParB ⟨0, by decide⟩ (by decide) hB

end CFSG.OddStandard.GH71.S55
