module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcThreeTwE6VtwCard
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcTwE6ThreeModel

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.TwE6Vtw

open Matrix CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.E6A5Cube CFSG.LieType.SeitzGeneration.ExcWideThree
  CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply)
open CFSG.RankThree.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.ClassicalInvolution.Balance.StrongBalance (GUid mem_GUid conjSUid coe_conjSUid)
open CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.TwE6Conc
open CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.TwE6Outer


variable {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
  (hK : Nat.card K = (ℓ ^ f) ^ 2) (hf : 1 ≤ f)
  {ζ : K} (hζ : ζ ≠ 0) (hσζ : unitaryInvolution K ℓ f ζ = -ζ)
  (P : GL (Fin 6) K) (hP : conjTr (unitaryInvolution K ℓ f) (P : Matrix (Fin 6) (Fin 6) K) *
    (P : Matrix (Fin 6) (Fin 6) K) = antidiag 6)
  {c : Kˣ} (hc : orderOf c = 3) (h3 : 3 ∣ ℓ ^ f + 1)
  (hct : unitaryInvolution K ℓ f ((c : K) + ((c⁻¹ : Kˣ) : K)) = (c : K) + ((c⁻¹ : Kˣ) : K))

theorem vtwV_apply_twE6T :
    ∀ v ∈ vtwV hK hf hζ hσζ P hP hc h3 hct, v (twE6T K ℓ f) = twE6T K ℓ f := by
  rintro _ ⟨y, rfl⟩
  apply Subtype.ext
  rw [MonoidHom.comp_apply, twistedE6InndiagConj_apply,
    vtwPhi_commute_twE6T hK hf hζ hσζ P hP hc h3 hct y, mul_inv_cancel_right]

theorem vtwV_apply_leviSU_of_isDiag :
    ∀ v ∈ vtwV hK hf hζ hσζ P hP hc h3 hct, ∀ s : Su K ℓ f 6,
      ((s : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).IsDiag →
        v (leviSU hK hf hζ hσζ P hP s) = leviSU hK hf hζ hσζ P hP s := by
  rintro _ ⟨y, rfl⟩ s hs
  apply Subtype.ext
  rw [MonoidHom.comp_apply, twistedE6InndiagConj_apply,
    vtwPhi_conj_leviSU hK hf hζ hσζ P hP hc h3 hct y s,
    conjSUid_eq_of_isDiag (coe_vtwA hc h3 y) hs]

theorem vtwV_map_leviJ :
    ∀ v ∈ vtwV hK hf hζ hσζ P hP hc h3 hct,
      ((leviJ K ℓ f).subgroupOf (twistedE6RootGroup K (unitaryInvolution K ℓ f))).map
          v.toMonoidHom =
        (leviJ K ℓ f).subgroupOf (twistedE6RootGroup K (unitaryInvolution K ℓ f)) := by
  rintro v ⟨y, rfl⟩
  haveI : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  haveI : Finite ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f)) := Subtype.finite
  rw [← range_leviSU hK hf hζ hσζ P hP]
  refine Subgroup.eq_of_le_of_card_ge ?_ (Subgroup.card_map_of_injective (MulEquiv.injective _)).ge
  rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
  refine ⟨conjSUid (unitaryInvolution K ℓ f) 6 (vtwA hc h3 y) z, Subtype.ext ?_⟩
  rw [MulEquiv.coe_toMonoidHom, MonoidHom.comp_apply, twistedE6InndiagConj_apply,
    vtwPhi_conj_leviSU hK hf hζ hσζ P hP hc h3 hct y z]

theorem vtwV_mem_zpowers_of_trivial :
    ∀ v ∈ vtwV hK hf hζ hσζ P hP hc h3 hct,
      (∀ j ∈ (leviJ K ℓ f).subgroupOf (twistedE6RootGroup K (unitaryInvolution K ℓ f)),
        j * (v j)⁻¹ ∈ GLAPPrimeCoreOf 3 ((leviJ K ℓ f).subgroupOf
          (twistedE6RootGroup K (unitaryInvolution K ℓ f)))) →
      v ∈ Subgroup.zpowers (MulAut.conj (twE6R0 c hct)) := by
  rintro _ ⟨y, rfl⟩ hv
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  haveI : Finite ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f)) := Subtype.finite
  have hJC₀ : leviJ K ℓ f ≤ twistedE6RootGroup K (unitaryInvolution K ℓ f) :=
    twE6LeviSA_le_twistedE6RootGroup hK hf
  have hJq : CFSG.Open.IsQuasisimple
      ↥((leviJ K ℓ f).subgroupOf (twistedE6RootGroup K (unitaryInvolution K ℓ f))) :=
    CFSG.LocalAnalysis.GLTheoremA.KD264Gen.Co15.isQuasisimple_of_equiv
      (Subgroup.subgroupOfEquivOfLe hJC₀).symm (isQuasisimple_twE6LeviSA hζ hσζ hK).1
  set w : ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f)) :=
    leviSU hK hf hζ hσζ P hP (diagThreeHom c hc h3 (diagGen4 (p := 3))) with hw
  have hwJ : w ∈ (leviJ K ℓ f).subgroupOf (twistedE6RootGroup K (unitaryInvolution K ℓ f)) :=
    Subgroup.mem_subgroupOf.2 (leviSU_mem_leviJ hK hf hζ hσζ P hP _)
  have hw3 : w ^ 3 = 1 := by
    rw [hw, ← map_pow, ← map_pow, pow_eq_one_of_fin, map_one, map_one]
  have hw1 : w ≠ 1 := by
    intro h
    have h' : ((leviSU hK hf hζ hσζ P hP).comp (diagThreeHom c hc h3)) (diagGen4 (p := 3)) =
        ((leviSU hK hf hζ hσζ P hP).comp (diagThreeHom c hc h3)) 1 := by
      rw [map_one]
      exact h
    exact diagGen4_ne_one (p := 3) (leviSU_comp_diagThreeHom_injective c hc h3 h')
  have hwo : orderOf (⟨w, hwJ⟩ : ↥((leviJ K ℓ f).subgroupOf
      (twistedE6RootGroup K (unitaryInvolution K ℓ f)))) = 3 :=
    orderOf_eq_prime (Subtype.ext (by rw [SubgroupClass.coe_pow, hw3]; rfl))
      (fun h => hw1 (congrArg Subtype.val h))
  have hpJ : 3 ∣ Nat.card ↥((leviJ K ℓ f).subgroupOf
      (twistedE6RootGroup K (unitaryInvolution K ℓ f))) :=
    hwo ▸ orderOf_dvd_natCard _
  have hfix := CFSG.LocalAnalysis.GLTheoremA.H81.UniA3.eq_of_mul_inv_mem_glaPPrimeCoreOf
    Nat.prime_three hJq hpJ
      (((twistedE6InndiagConj K (unitaryInvolution K ℓ f)).comp
        (vtwPhi hK hf hζ hσζ P hP hc h3 hct)) y).toMonoidHom fun j hj => by
      have h2 := (GLAPPrimeCoreOf 3 ((leviJ K ℓ f).subgroupOf
        (twistedE6RootGroup K (unitaryInvolution K ℓ f)))).inv_mem (hv j hj)
      rwa [_root_.mul_inv_rev, inv_inv] at h2
  have hcomm : ∀ z : Su K ℓ f 6,
      (vtwPhi hK hf hζ hσζ P hP hc h3 hct y : ModGL TwistTag.E6.tag K) *
          (leviSU hK hf hζ hσζ P hP z : ModGL TwistTag.E6.tag K) *
          (vtwPhi hK hf hζ hσζ P hP hc h3 hct y : ModGL TwistTag.E6.tag K)⁻¹ =
        (leviSU hK hf hζ hσζ P hP z : ModGL TwistTag.E6.tag K) := fun z => by
    have h := congrArg Subtype.val (hfix _
      (Subgroup.mem_subgroupOf.2 (leviSU_mem_leviJ hK hf hζ hσζ P hP z)))
    rwa [MulEquiv.coe_toMonoidHom, MonoidHom.comp_apply, twistedE6InndiagConj_apply] at h
  obtain ⟨h0, h25⟩ := vtwPhi_coords_of_forall_conj_leviSU hK hf hζ hσζ P hP hc h3 hct hcomm
  rw [MonoidHom.comp_apply, vtwPhi_eq_of_eq_one hK hf hζ hσζ P hP hc h3 hct h0 h25,
    twistedE6InndiagConj_inclusion, map_pow]
  exact Subgroup.npow_mem_zpowers _ _

end CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.TwE6Vtw

end
