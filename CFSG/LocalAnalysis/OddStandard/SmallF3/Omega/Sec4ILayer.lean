module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OutLift
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OutComp
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OutOne
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IAct

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

theorem sec4I_exists_layer_involution (Y : Subgroup G) {P : Type} [Group P] (ρ : ↥Y →* P)
    (hρ : OddCentralCover ρ) {s : G} (hs : s * s = 1) (hsN : s ∈ normalizer (Y : Set G))
    (α : MulAut P) (hα : ∀ y : ↥Y, ρ (conjAut Y hs hsN y) = α (ρ y)) {u₀ : P}
    (hu₀ : u₀ ∈ CFSG.inSubgroup CFSG.layer (fixSub α)) (huu : u₀ * u₀ = 1) (hu1 : u₀ ≠ 1) :
    ∃ u : G, u ∈ CFSG.inSubgroup CFSG.layer (Y ⊓ centralizer ({s} : Set G)) ∧ orderOf u = 2 := by
  have hσ2 : conjAut Y hs hsN * conjAut Y hs hsN = 1 := conjAut_mul_self Y hs hsN
  have hcov := hρ.oddCentralCover_fixHom hσ2 hα
  obtain ⟨uF, huF, rfl⟩ := hu₀
  have huFF : uF * uF = 1 := Subtype.ext huu
  obtain ⟨û, hûL, hûû, hûF⟩ := hcov.exists_involution_layer_lift huF huFF
  have hρû : ρ ((û : ↥Y)) = (uF : P) := congrArg Subtype.val hûF
  have hûû' : (û : ↥Y) * û = 1 := congrArg Subtype.val hûû
  have hû1 : (û : ↥Y) ≠ 1 := by
    intro h1
    rw [h1, map_one] at hρû
    exact hu1 hρû.symm
  refine ⟨((û : ↥Y) : G), ?_, ?_⟩
  · have h1 := CFSG.WholeGroup.layer_map_mulEquiv (fixConjEquiv Y hs hsN)
    have h2 : fixConjEquiv Y hs hsN û ∈ CFSG.layer ↥(Y ⊓ centralizer ({s} : Set G)) := by
      rw [← h1]
      exact ⟨û, hûL, rfl⟩
    exact ⟨_, h2, rfl⟩
  · have hu1' : ((û : ↥Y) : G) ≠ 1 := fun h => hû1 (Subtype.ext h)
    have hu2 : ((û : ↥Y) : G) ^ 2 = 1 := by
      rw [pow_two, ← Subgroup.coe_mul, hûû']
      rfl
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime hu2 hu1'

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem sec4I_exists_layer_of_block (hQ : Q.Nondegenerate) {x : OGroup Q} (hx : x * x = 1)
    (hU : 3 ≤ Module.finrank (ZMod 3) (commSp x)) (hW : 0 < Module.finrank (ZMod 3) (fixSp x))
    (hq : CFSG.IsQuasisimple (omegaGroup (nondegenerate_restrict_commSp hQ hx))) :
    ∃ u : ↥(omegaProj hQ), u ∈ CFSG.inSubgroup CFSG.layer (fixSub (projAut hQ x)) ∧
      u * u = 1 ∧ u ≠ 1 := by
  have hQU := nondegenerate_restrict_commSp hQ hx
  have hU2 : 2 ≤ Module.finrank (ZMod 3) (commSp x) := by omega
  obtain ⟨t, htt, htype⟩ := (exists_involution_of_type hQU 2 (-1)).mpr
    ⟨by omega, fun h => absurd h (by decide), fun h => by omega⟩
  have htd : invDim t = 2 := congrArg Prod.fst htype
  have hts : invSign t = -1 := congrArg Prod.snd htype
  have htΩ : t ∈ omegaGroup hQU := by
    refine (involution_mem_omegaGroup_iff hQU htt).mpr ⟨?_, ?_⟩
    · rw [htd]
      exact even_two
    · rw [hts, htd]
      decide
  have hb2 : (⟨t, htΩ⟩ : omegaGroup hQU) * ⟨t, htΩ⟩ = 1 := Subtype.ext htt
  have hb1 : (⟨t, htΩ⟩ : omegaGroup hQU) ≠ 1 := by
    intro h
    have h1 : t = 1 := congrArg Subtype.val h
    rw [h1, invType_one] at htype
    exact absurd (congrArg Prod.fst htype) (by decide)
  have hinj := omegaProjInr_injective hQ hx hU2 hW
  refine ⟨omegaProjInr hQ hx hU2 ⟨t, htΩ⟩, omegaProjInr_mem_layer hQ hx hU2 hW hq ⟨t, htΩ⟩,
    ?_, ?_⟩
  · rw [← map_mul, hb2, map_one]
  · intro h1
    exact hb1 (hinj (h1.trans (map_one _).symm))

variable {L : Subgroup G}

theorem sec4I_exists_layer_of_block_lift [Finite G] (hL : IsOmega7Group L)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* Sec4IOmega) {s : G} (hss : s * s = 1)
    {y : ProjOrth Sec4IQ} (hy : Sec4IActs e s y) {x : OGroup Sec4IQ} (hx : x * x = 1)
    (hxy : toProj Sec4IQ x = y) (hU : 3 ≤ Module.finrank (ZMod 3) (commSp x))
    (hW : 0 < Module.finrank (ZMod 3) (fixSp x))
    (hq : CFSG.IsQuasisimple (omegaGroup (nondegenerate_restrict_commSp sec4IQ_nondegenerate hx))) :
    ∃ u : G, u ∈ CFSG.inSubgroup CFSG.layer (L ⊓ centralizer ({s} : Set G)) ∧ orderOf u = 2 := by
  obtain ⟨u₀, hu₀, huu, hu1⟩ := sec4I_exists_layer_of_block sec4IQ_nondegenerate hx hU hW hq
  refine sec4I_exists_layer_involution L (sec4ICover e) (sec4ICover_odd hL e) hss hy.1
    (projAut sec4IQ_nondegenerate x) (fun l => ?_) hu₀ huu hu1
  apply Subtype.ext
  rw [coe_projAut, hxy]
  exact hy.2 l (conjAut L hss hy.1 l) rfl

end CFSG.OddStandard.SmallF3.Omega
