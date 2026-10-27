module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166TwE6Eight3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166TwE6B4
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotQ2FamilyPiece
public import CFSG.RankThree.PartOne.KF4.QPlusCobound
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiagTwisted
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166TwE6Eight

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.SeitzReduction
open CFSG.SeitzReduction.EPilot
open CFSG.LieType.Steinberg.Adjoint
open CFSG.HardMathSupport.Lang.E6Descent
open CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.RankThree.Chevalley
open CFSG.StandardType.TableBExc.E6Three
open scoped commutatorElement

namespace TwE6Eight

section Certs


variable {Ω : Type} [Field Ω] [CharP Ω 2]
variable {q : ℕ} [NeZero q]

theorem twE6G_eq :
    twE6G Ω = pinnedX Tag.E6 Ω twE6A6 1 * weylElt Tag.E6 Ω twE6Six 1 *
      pinnedX Tag.E6 Ω twE6A6 1 := by
  have hx : pinnedX Tag.E6 Ω twE6A6 1 = xUnit Tag.E6 Ω twE6Six 1 := by
    rw [show twE6A6 = Pi.single twE6Six 1 from rfl, pinnedX_single]
  have hy : pinnedX Tag.E6 Ω (-twE6A6) 1 = yUnit Tag.E6 Ω twE6Six 1 := by
    rw [show -twE6A6 = -Pi.single twE6Six 1 from rfl, pinnedX_neg_single]
  have hx2 : xUnit Tag.E6 Ω twE6Six 1 * xUnit Tag.E6 Ω twE6Six 1 = 1 := by
    rw [← hx, ← pinnedX_add, CharTwo.add_self_eq_zero, pinnedX_zero]
  have hw : weylElt Tag.E6 Ω twE6Six 1 =
      xUnit Tag.E6 Ω twE6Six 1 * yUnit Tag.E6 Ω twE6Six 1 * xUnit Tag.E6 Ω twE6Six 1 := by
    rw [CFSG.Blueprint.Chevalley.weylElt_eq_xUnit_mul]
    simp [CharTwo.neg_eq]
  rw [twE6G, hy, hx, hw]
  calc yUnit Tag.E6 Ω twE6Six 1
      = (xUnit Tag.E6 Ω twE6Six 1 * xUnit Tag.E6 Ω twE6Six 1) *
          yUnit Tag.E6 Ω twE6Six 1 *
          (xUnit Tag.E6 Ω twE6Six 1 * xUnit Tag.E6 Ω twE6Six 1) := by rw [hx2]; group
    _ = xUnit Tag.E6 Ω twE6Six 1 *
        (xUnit Tag.E6 Ω twE6Six 1 * yUnit Tag.E6 Ω twE6Six 1 *
          xUnit Tag.E6 Ω twE6Six 1) * xUnit Tag.E6 Ω twE6Six 1 := by group

theorem theta_twE6U {Fr : Ω →+* Ω} {n : ℕ} (hFr : ∀ c, Fr c = c ^ (2 ^ n))
    {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ) (hdeg : twE6Deg γ = 1)
    (e : Ω) (he : e ^ (2 ^ n) = e + 1) :
    TwistedDiag.theta Fr (twE6U (γ := γ) e) =
      weylElt Tag.E6 Ω twE6Six 1 * twE6U (γ := γ) e *
        (weylElt Tag.E6 Ω twE6Six 1)⁻¹ := by
  have hδ : IsRoot Tag.E6 (twE6A6 - γ) := isRoot_A6_sub hγ hdeg
  have hδdeg : twE6Deg (twE6A6 - γ) = 1 := twE6Deg_A6_sub hdeg
  have hθA : TwistedDiag.theta Fr (pinnedX Tag.E6 Ω γ 1) =
      pinnedX Tag.E6 Ω (-γ) 1 := by
    rw [theta_pinnedX (Ω := Ω) hFr hγ 1, one_pow]
  have hθB : TwistedDiag.theta Fr (pinnedX Tag.E6 Ω (twE6A6 - γ) 1) =
      pinnedX Tag.E6 Ω (γ - twE6A6) 1 := by
    rw [theta_pinnedX (Ω := Ω) hFr hδ 1, one_pow]
    congr 1
    abel
  have hθZ : TwistedDiag.theta Fr (pinnedX Tag.E6 Ω twE6A6 e) =
      pinnedX Tag.E6 Ω (-twE6A6) (e + 1) := by
    rw [theta_pinnedX (α := twE6A6) (Ω := Ω) hFr
      (show IsRoot Tag.E6 twE6A6 from isRoot_single Tag.E6 twE6Six) e, he]
  have hθu : TwistedDiag.theta Fr (twE6U (γ := γ) e) =
      pinnedX Tag.E6 Ω (-γ) 1 * pinnedX Tag.E6 Ω (γ - twE6A6) 1 *
        pinnedX Tag.E6 Ω (-twE6A6) (e + 1) := by
    rw [twE6U, map_mul, map_mul, hθA, hθB, hθZ]
  have hconj : weylElt Tag.E6 Ω twE6Six 1 * twE6U (γ := γ) e *
        (weylElt Tag.E6 Ω twE6Six 1)⁻¹ =
      pinnedX Tag.E6 Ω (γ - twE6A6) 1 * pinnedX Tag.E6 Ω (-γ) 1 *
        pinnedX Tag.E6 Ω (-twE6A6) e := by
    rw [twE6U]
    calc weylElt Tag.E6 Ω twE6Six 1 *
          (pinnedX Tag.E6 Ω γ 1 * pinnedX Tag.E6 Ω (twE6A6 - γ) 1 *
            pinnedX Tag.E6 Ω twE6A6 e) * (weylElt Tag.E6 Ω twE6Six 1)⁻¹
        = (weylElt Tag.E6 Ω twE6Six 1 * pinnedX Tag.E6 Ω γ 1 *
              (weylElt Tag.E6 Ω twE6Six 1)⁻¹) *
            (weylElt Tag.E6 Ω twE6Six 1 * pinnedX Tag.E6 Ω (twE6A6 - γ) 1 *
              (weylElt Tag.E6 Ω twE6Six 1)⁻¹) *
            (weylElt Tag.E6 Ω twE6Six 1 * pinnedX Tag.E6 Ω twE6A6 e *
              (weylElt Tag.E6 Ω twE6Six 1)⁻¹) := by group
      _ = _ := by
        rw [weylElt_six_conj hγ 1, weylElt_six_conj hδ 1,
          weylElt_six_conj (β := twE6A6)
            (show IsRoot Tag.E6 twE6A6 from isRoot_single Tag.E6 twE6Six) e]
        simp [hdeg, hδdeg, twE6Deg_pi_single_six, twE6A6, twE6Six, two_smul]
  rw [hθu, hconj]
  have hAB : pinnedX Tag.E6 Ω (-γ) 1 * pinnedX Tag.E6 Ω (γ - twE6A6) 1 =
      pinnedX Tag.E6 Ω (-twE6A6) 1 *
        (pinnedX Tag.E6 Ω (γ - twE6A6) 1 * pinnedX Tag.E6 Ω (-γ) 1) := by
    have h := commutator_neg_deg_one (Ω := Ω) hγ hdeg
    rw [commutatorElement_def] at h
    calc pinnedX Tag.E6 Ω (-γ) 1 * pinnedX Tag.E6 Ω (γ - twE6A6) 1
        = (pinnedX Tag.E6 Ω (-γ) 1 * pinnedX Tag.E6 Ω (γ - twE6A6) 1 *
            (pinnedX Tag.E6 Ω (-γ) 1)⁻¹ *
            (pinnedX Tag.E6 Ω (γ - twE6A6) 1)⁻¹) *
            (pinnedX Tag.E6 Ω (γ - twE6A6) 1 * pinnedX Tag.E6 Ω (-γ) 1) := by
          group
      _ = _ := by rw [h]
  have hZA : Commute (pinnedX Tag.E6 Ω (-twE6A6) 1) (pinnedX Tag.E6 Ω (-γ) 1) := by
    refine commute_pinnedX_of_not_root (IsRoot.neg (isRoot_single Tag.E6 twE6Six))
      (IsRoot.neg hγ) ?_ ?_ ?_ 1 1
    · intro h
      have hd := congrArg twE6Deg h
      have h1 : twE6Deg (-twE6A6) = -2 := by rw [map_neg, twE6Deg_A6]
      have h2 : twE6Deg (-γ) = -1 := by rw [map_neg, hdeg]
      rw [h1, h2] at hd
      omega
    · intro h
      have hd := congrArg twE6Deg h
      have h1 : twE6Deg (-twE6A6) = -2 := by rw [map_neg, twE6Deg_A6]
      have h2 : twE6Deg (- -γ) = 1 := by simpa using hdeg
      rw [h1, h2] at hd
      omega
    · exact not_isRoot_of_twE6Deg_lt (by
        rw [map_add, map_neg, map_neg, twE6Deg_A6, hdeg]
        norm_num)
  have hZB : Commute (pinnedX Tag.E6 Ω (-twE6A6) 1)
      (pinnedX Tag.E6 Ω (γ - twE6A6) 1) := by
    refine commute_pinnedX_of_not_root (IsRoot.neg (isRoot_single Tag.E6 twE6Six))
      (by have h := IsRoot.neg hδ; simpa [neg_sub] using h) ?_ ?_ ?_ 1 1
    · intro h
      have hd := congrArg twE6Deg h
      have h1 : twE6Deg (-twE6A6) = -2 := by rw [map_neg, twE6Deg_A6]
      have h2 : twE6Deg (γ - twE6A6) = -1 := by
        rw [map_sub, hdeg, twE6Deg_A6]
        norm_num
      rw [h1, h2] at hd
      omega
    · intro h
      have hd := congrArg twE6Deg h
      have h1 : twE6Deg (-twE6A6) = -2 := by rw [map_neg, twE6Deg_A6]
      have h2 : twE6Deg (-(γ - twE6A6)) = 1 := by
        rw [neg_sub, map_sub, twE6Deg_A6, hdeg]
        norm_num
      rw [h1, h2] at hd
      omega
    · exact not_isRoot_of_twE6Deg_lt (by
        rw [map_add, map_neg, map_sub, twE6Deg_A6, hdeg]
        norm_num)
  have hZZ : pinnedX Tag.E6 Ω (-twE6A6) 1 * pinnedX Tag.E6 Ω (-twE6A6) (e + 1) =
      pinnedX Tag.E6 Ω (-twE6A6) e := by
    rw [← pinnedX_add]
    congr 1
    have h2 : (1 : Ω) + 1 = 0 := CharTwo.add_self_eq_zero (1 : Ω)
    linear_combination h2
  calc pinnedX Tag.E6 Ω (-γ) 1 * pinnedX Tag.E6 Ω (γ - twE6A6) 1 *
        pinnedX Tag.E6 Ω (-twE6A6) (e + 1)
      = (pinnedX Tag.E6 Ω (-twE6A6) 1 *
          (pinnedX Tag.E6 Ω (γ - twE6A6) 1 * pinnedX Tag.E6 Ω (-γ) 1)) *
          pinnedX Tag.E6 Ω (-twE6A6) (e + 1) := by rw [hAB]
    _ = pinnedX Tag.E6 Ω (-twE6A6) 1 * pinnedX Tag.E6 Ω (γ - twE6A6) 1 *
          pinnedX Tag.E6 Ω (-γ) 1 * pinnedX Tag.E6 Ω (-twE6A6) (e + 1) := by group
    _ = pinnedX Tag.E6 Ω (γ - twE6A6) 1 * pinnedX Tag.E6 Ω (-twE6A6) 1 *
          pinnedX Tag.E6 Ω (-γ) 1 * pinnedX Tag.E6 Ω (-twE6A6) (e + 1) := by
        rw [hZB.eq]
    _ = pinnedX Tag.E6 Ω (γ - twE6A6) 1 *
          (pinnedX Tag.E6 Ω (-twE6A6) 1 * pinnedX Tag.E6 Ω (-γ) 1) *
          pinnedX Tag.E6 Ω (-twE6A6) (e + 1) := by group
    _ = pinnedX Tag.E6 Ω (γ - twE6A6) 1 *
          (pinnedX Tag.E6 Ω (-γ) 1 * pinnedX Tag.E6 Ω (-twE6A6) 1) *
          pinnedX Tag.E6 Ω (-twE6A6) (e + 1) := by rw [hZA.eq]
    _ = pinnedX Tag.E6 Ω (γ - twE6A6) 1 * pinnedX Tag.E6 Ω (-γ) 1 *
          pinnedX Tag.E6 Ω (-twE6A6) 1 * pinnedX Tag.E6 Ω (-twE6A6) (e + 1) := by
        group
    _ = pinnedX Tag.E6 Ω (γ - twE6A6) 1 * pinnedX Tag.E6 Ω (-γ) 1 *
          (pinnedX Tag.E6 Ω (-twE6A6) 1 * pinnedX Tag.E6 Ω (-twE6A6) (e + 1)) := by
        group
    _ = pinnedX Tag.E6 Ω (γ - twE6A6) 1 * pinnedX Tag.E6 Ω (-γ) 1 *
          pinnedX Tag.E6 Ω (-twE6A6) e := by rw [hZZ]

theorem twE6BZero_apply_six (ζ : Ωˣ) (hζ : ζ ^ q = 1) (c : Fin 4 → ZMod q) :
    zetaVec ζ hζ (twE6Cast (twE6B0Comb c)) twE6Six = 1 := by
  rw [zetaVec_apply]
  have h0 : twE6Cast (twE6B0Comb c) twE6Six = 0 := by
    simpa [twE6Cast, twE6Six] using twE6B0Comb_last c
  rw [h0]
  simp

theorem twE6BZero_le_thetaFixed [IsAlgClosed Ω] {Fr : Ω →+* Ω} {n : ℕ}
    (hFr : ∀ c, Fr c = c ^ (2 ^ n)) (hqQ : q ∣ 2 ^ n + 1) (ζ : Ωˣ) (hζ : ζ ^ q = 1) :
    twE6BZero ζ hζ ≤ TwistedDiag.thetaFixed Fr := by
  rintro b hb
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.1 hb
  rw [← hc]
  change rootDiagUnit Tag.E6 (zetaVec ζ hζ (twE6Cast (twE6B0Comb c))) ∈ TwistedDiag.thetaFixed Fr
  rw [TwistedDiag.mem_thetaFixed]
  refine ⟨rootDiagUnit_mem_adjointGroup_of_isAlgClosed _, ?_⟩
  rw [TwistedDiag.theta_rootDiagUnit_eq_iff Fr hFr]
  intro i
  obtain ⟨m, hm⟩ := hqQ
  rw [zetaVec_apply, ← pow_mul, hm]
  rw [show (twE6Cast (twE6B0Comb c) i).val * (q * m) =
      q * ((twE6Cast (twE6B0Comb c) i).val * m) by ring]
  rw [pow_mul, hζ, one_pow]

theorem twE6BZero_commute_twE6G [IsAlgClosed Ω] (ζ : Ωˣ) (hζ : ζ ^ q = 1) {b : ModGL Tag.E6 Ω}
    (hb : b ∈ twE6BZero ζ hζ) : b * twE6G Ω = twE6G Ω * b := by
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.1 hb
  set a : Fin Tag.E6.rank → Ωˣ := zetaVec ζ hζ (twE6Cast (twE6B0Comb c)) with ha
  have hb' : b = rootDiagUnit Tag.E6 a := by
    rw [← hc, ha]
    rfl
  have ha5 : a twE6Six = 1 := by
    rw [ha]
    exact twE6BZero_apply_six ζ hζ c
  have hchar : rootChar a (-twE6A6) = 1 := by
    rw [show -twE6A6 = 0 - twE6A6 by abel, rootChar_sub, rootChar_zero, one_mul,
      show rootChar a twE6A6 = a twE6Six from by
        rw [show twE6A6 = 1 • Pi.single twE6Six 1 by simp, rootChar_nsmul_single, pow_one],
      ha5, inv_one]
  have h := rootDiagUnit_conj_pinnedX a (IsRoot.neg (isRoot_single Tag.E6 twE6Six)) 1
  rw [hchar] at h
  simp only [Units.val_one, one_mul] at h
  rw [hb']
  change rootDiagUnit Tag.E6 a * pinnedX Tag.E6 Ω (-twE6A6) 1 =
    pinnedX Tag.E6 Ω (-twE6A6) 1 * rootDiagUnit Tag.E6 a
  calc rootDiagUnit Tag.E6 a * pinnedX Tag.E6 Ω (-twE6A6) 1
      = (rootDiagUnit Tag.E6 a * pinnedX Tag.E6 Ω (-twE6A6) 1 *
          (rootDiagUnit Tag.E6 a)⁻¹) * rootDiagUnit Tag.E6 a := by group
    _ = pinnedX Tag.E6 Ω (-twE6A6) 1 * rootDiagUnit Tag.E6 a := by rw [h]

theorem twE6BZero_le_normalizer [IsAlgClosed Ω] {Fr : Ω →+* Ω} {n : ℕ}
    (hFr : ∀ c, Fr c = c ^ (2 ^ n)) (hqQ : q ∣ 2 ^ n + 1) (ζ : Ωˣ) (hζ : ζ ^ q = 1) :
    twE6BZero ζ hζ ≤ Subgroup.normalizer (twE6SBar Fr : Set (ModGL Tag.E6 Ω)) := by
  intro b hb
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.1 hb
  set a : Fin Tag.E6.rank → Ωˣ := zetaVec ζ hζ (twE6Cast (twE6B0Comb c)) with ha
  have hb' : twE6BZeroHom ζ hζ c = rootDiagUnit Tag.E6 a := by
    rw [ha]
    rfl
  have hbR' : b ∈ TwistedDiag.thetaFixed Fr :=
    twE6BZero_le_thetaFixed hFr hqQ ζ hζ hb
  have hbR : rootDiagUnit Tag.E6 a ∈ TwistedDiag.thetaFixed Fr := by
    rw [← hb']
    simpa [hc] using hbR' 
  have ha5 : a twE6Six = 1 := by
    rw [ha]
    exact twE6BZero_apply_six ζ hζ c
  have hcommg : rootDiagUnit Tag.E6 a * twE6G Ω = twE6G Ω * rootDiagUnit Tag.E6 a := by
    rw [← hb']
    exact twE6BZero_commute_twE6G ζ hζ (by rw [hc]; exact hb)
  have hmapU :
      (twE6UPlus Ω).map (MulAut.conj (rootDiagUnit Tag.E6 a)).toMonoidHom = twE6UPlus Ω := by
    rw [twE6UPlus]
    exact map_rootSpan_of_forall fun α hα => map_conj_rootDiagUnit_rootSubgroup a hα.1
  have hbNU : rootDiagUnit Tag.E6 a ∈
      Subgroup.normalizer (twE6UPlus Ω : Set (ModGL Tag.E6 Ω)) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact hmapU
  have hbN : rootDiagUnit Tag.E6 a ∈ Subgroup.normalizer
      (((twE6UPlus Ω).map (MulAut.conj (twE6G Ω)).toMonoidHom) :
        Set (ModGL Tag.E6 Ω)) :=
    CFSG.SeitzReduction.E7Pilot.mem_normalizer_map_conj_of_commute hbNU hcommg
  rw [← hc, hb']
  rw [twE6SBar]
  exact Subgroup.inf_normalizer_le_normalizer_inf
    (Subgroup.mem_inf.2 ⟨hbN, Subgroup.le_normalizer hbR⟩)

private theorem pinnedX_list_prod_injective_deg
    (L : List (Fin Tag.E6.rank → ℤ)) (hnd : L.Nodup)
    (hL : ∀ α ∈ L, IsRoot Tag.E6 α ∧ 0 < twE6Deg α)
    (c c' : (Fin Tag.E6.rank → ℤ) → Ω)
    (heq : (L.map fun α => pinnedX Tag.E6 Ω α (c α)).prod =
      (L.map fun α => pinnedX Tag.E6 Ω α (c' α)).prod) :
    ∀ α ∈ L, c α = c' α := by
  have h := congrArg (fun g : ModGL Tag.E6 Ω =>
    (g : Module.End Ω (RootModule Tag.E6 Ω))) heq
  rw [coe_list_prod_pinnedX c L (fun α hα => (hL α hα).1),
    coe_list_prod_pinnedX c' L (fun α hα => (hL α hα).1)] at h
  have key := RootOperatorFamily.prod_eltOr_injective_of_ring (rootOperatorFamily Tag.E6)
    (φ := twE6Deg) L hnd hL _ _ h
  intro α hα
  have h1 := congrArg (((rootOperatorFamily Tag.E6).pinnedFamilySign α : Ω) * ·) (key α hα)
  simpa only [← mul_assoc, (rootOperatorFamily Tag.E6).pinnedFamilySign_mul_self, one_mul]
    using h1

theorem rootChar_eq_one_of_commute_twE6U {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ)
    (hdeg : twE6Deg γ = 1) (a : Fin Tag.E6.rank → Ωˣ) (e : Ω)
    (hcomm : rootDiagUnit Tag.E6 a * twE6U (γ := γ) e *
        (rootDiagUnit Tag.E6 a)⁻¹ = twE6U (γ := γ) e) :
    rootChar a γ = 1 := by
  have hδ : IsRoot Tag.E6 (twE6A6 - γ) := isRoot_A6_sub hγ hdeg
  have hδdeg : twE6Deg (twE6A6 - γ) = 1 := twE6Deg_A6_sub hdeg
  have hγδ : γ ≠ twE6A6 - γ := by
    intro h
    have h5 := congrFun h twE6Six
    simp [twE6A6, twE6Six] at h5
    omega
  have hγα : γ ≠ twE6A6 := by
    intro h
    have hd := congrArg twE6Deg h
    rw [hdeg, twE6Deg_A6] at hd
    omega
  have hδα : twE6A6 - γ ≠ twE6A6 := by
    intro h
    have hd := congrArg twE6Deg h
    rw [twE6Deg_A6_sub hdeg, twE6Deg_A6] at hd
    omega
  let L : List (Fin Tag.E6.rank → ℤ) := [γ, twE6A6 - γ, twE6A6]
  let c : (Fin Tag.E6.rank → ℤ) → Ω := fun β =>
    if β = γ then 1 else if β = twE6A6 - γ then 1 else e
  let c' : (Fin Tag.E6.rank → ℤ) → Ω := fun β =>
    if β = γ then (rootChar a γ : Ω) * 1
    else if β = twE6A6 - γ then (rootChar a (twE6A6 - γ) : Ω) * 1
    else (rootChar a twE6A6 : Ω) * e
  have hnd : L.Nodup := by
    simp [L, hγδ, hγα, hδα]
  have hL : ∀ α ∈ L, IsRoot Tag.E6 α ∧ 0 < twE6Deg α := by
    intro α hα
    simp only [L, List.mem_cons, List.mem_nil_iff, or_false] at hα
    rcases hα with rfl | rfl | rfl
    · exact ⟨hγ, by rw [hdeg]; norm_num⟩
    · exact ⟨hδ, by rw [hδdeg]; norm_num⟩
    · exact ⟨isRoot_single Tag.E6 twE6Six, by rw [twE6Deg_A6]; norm_num⟩
  have hc : (L.map fun β => pinnedX Tag.E6 Ω β (c β)).prod = twE6U (γ := γ) e := by
    simp [L, c, twE6U, hγδ, hγδ.symm, hγα, hγα.symm, hδα, hδα.symm, mul_assoc]
  have hc' : (L.map fun β => pinnedX Tag.E6 Ω β (c' β)).prod =
      rootDiagUnit Tag.E6 a * twE6U (γ := γ) e * (rootDiagUnit Tag.E6 a)⁻¹ := by
    calc (L.map fun β => pinnedX Tag.E6 Ω β (c' β)).prod
        = pinnedX Tag.E6 Ω γ ((rootChar a γ : Ω) * 1) *
            pinnedX Tag.E6 Ω (twE6A6 - γ) ((rootChar a (twE6A6 - γ) : Ω) * 1) *
            pinnedX Tag.E6 Ω twE6A6 ((rootChar a twE6A6 : Ω) * e) := by
          simp [L, c', hγδ, hγδ.symm, hγα, hγα.symm, hδα, hδα.symm, mul_assoc]
      _ = (rootDiagUnit Tag.E6 a * pinnedX Tag.E6 Ω γ 1 * (rootDiagUnit Tag.E6 a)⁻¹) *
            (rootDiagUnit Tag.E6 a * pinnedX Tag.E6 Ω (twE6A6 - γ) 1 *
              (rootDiagUnit Tag.E6 a)⁻¹) *
            (rootDiagUnit Tag.E6 a * pinnedX Tag.E6 Ω twE6A6 e *
              (rootDiagUnit Tag.E6 a)⁻¹) := by
          rw [← rootDiagUnit_conj_pinnedX a hγ 1,
            ← rootDiagUnit_conj_pinnedX a hδ 1,
            ← rootDiagUnit_conj_pinnedX a (isRoot_single Tag.E6 twE6Six) e]
      _ = rootDiagUnit Tag.E6 a *
            (pinnedX Tag.E6 Ω γ 1 * pinnedX Tag.E6 Ω (twE6A6 - γ) 1 *
              pinnedX Tag.E6 Ω twE6A6 e) * (rootDiagUnit Tag.E6 a)⁻¹ := by group
      _ = rootDiagUnit Tag.E6 a * twE6U (γ := γ) e * (rootDiagUnit Tag.E6 a)⁻¹ := by
          rw [twE6U]
  have heq : (L.map fun β => pinnedX Tag.E6 Ω β (c β)).prod =
      (L.map fun β => pinnedX Tag.E6 Ω β (c' β)).prod := by
    rw [hc, hc', hcomm]
  have hval := pinnedX_list_prod_injective_deg L hnd hL c c' heq
  have hmem : γ ∈ L := by simp [L]
  have h1 := hval γ hmem
  have h2 : (rootChar a γ : Ω) = 1 := by
    simpa [c, c', mul_one] using h1.symm
  exact Units.ext h2

theorem eq_one_of_rootChar_twE6Five {a : Fin Tag.E6.rank → Ωˣ}
    (h6 : rootChar a twE6A6 = 1) (h : ∀ i, rootChar a (twE6Five i) = 1) : a = 1 := by
  have hsingle (i : Fin Tag.E6.rank) : rootChar a (Pi.single i 1) = a i := by
    have := rootChar_nsmul_single a i 1
    simpa using this
  have hneg : ∀ v : Fin Tag.E6.rank → ℤ, rootChar a (-v) = (rootChar a v)⁻¹ := by
    intro v
    rw [show -v = 0 - v by abel, rootChar_sub, rootChar_zero, one_mul]
  have ha5 : a twE6Six = 1 := by
    rw [← hsingle twE6Six]
    exact h6
  have ha4 : a ⟨4, by decide⟩ = 1 := by
    have h0 := h 0
    rw [show twE6Five 0 = -Pi.single ⟨4, by decide⟩ 1 from rfl, hneg, inv_eq_one] at h0
    simpa [hsingle] using h0
  have ha3 : a ⟨3, by decide⟩ = 1 := by
    have h0 := h 0
    have h1 := h 1
    have hr : twE6Five 0 - twE6Five 1 = Pi.single ⟨3, by decide⟩ 1 := by
      decide +kernel
    have hsub : rootChar a (twE6Five 0 - twE6Five 1) = 1 := by
      rw [rootChar_sub, h0, h1, inv_one, mul_one]
    rw [hr, hsingle] at hsub
    exact hsub
  have ha2 : a ⟨2, by decide⟩ = 1 := by
    have h1 := h 1
    have h2 := h 2
    have hr : twE6Five 1 - twE6Five 2 = Pi.single ⟨2, by decide⟩ 1 := by
      decide +kernel
    have hsub : rootChar a (twE6Five 1 - twE6Five 2) = 1 := by
      rw [rootChar_sub, h1, h2, inv_one, mul_one]
    rw [hr, hsingle] at hsub
    exact hsub
  have ha0 : a ⟨0, by decide⟩ = 1 := by
    have h2 := h 2
    have h3 := h 3
    have hr : twE6Five 2 - twE6Five 3 = Pi.single ⟨0, by decide⟩ 1 := by
      decide +kernel
    have hsub : rootChar a (twE6Five 2 - twE6Five 3) = 1 := by
      rw [rootChar_sub, h2, h3, inv_one, mul_one]
    rw [hr, hsingle] at hsub
    exact hsub
  have ha1 : a ⟨1, by decide⟩ = 1 := by
    have h1 := h 1
    have h4 := h 4
    have hr : twE6Five 1 - twE6Five 4 = Pi.single ⟨1, by decide⟩ 1 := by
      decide +kernel
    have hsub : rootChar a (twE6Five 1 - twE6Five 4) = 1 := by
      rw [rootChar_sub, h1, h4, inv_one, mul_one]
    rw [hr, hsingle] at hsub
    exact hsub
  funext i
  fin_cases i
  · exact ha0
  · exact ha1
  · exact ha2
  · exact ha3
  · exact ha4
  · exact ha5

theorem conj_twE6U_mem_twE6SBar {Fr : Ω →+* Ω} {n : ℕ} (hFr : ∀ c, Fr c = c ^ (2 ^ n))
    {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ) (hdeg : twE6Deg γ = 1)
    (e : Ω) (he : e ^ (2 ^ n) = e + 1) :
    twE6G Ω * twE6U (γ := γ) e * (twE6G Ω)⁻¹ ∈ twE6SBar Fr := by
  let x : ModGL Tag.E6 Ω := pinnedX Tag.E6 Ω twE6A6 1
  let nn : ModGL Tag.E6 Ω := weylElt Tag.E6 Ω twE6Six 1
  have hx : x = pinnedX Tag.E6 Ω twE6A6 1 := rfl
  have hθg : TwistedDiag.theta Fr (twE6G Ω) = x := by
    rw [twE6G, theta_pinnedX (α := -twE6A6) (Ω := Ω) hFr
      (IsRoot.neg (isRoot_single Tag.E6 twE6Six)) 1, one_pow, neg_neg]
  have hxγ : Commute x (pinnedX Tag.E6 Ω γ 1) := by
    refine commute_pinnedX_of_deg (isRoot_single Tag.E6 twE6Six) hγ ?_ ?_ 1 1
    · rw [twE6Deg_pi_single_six, hdeg]
      norm_num
    · exact not_isRoot_of_twE6Deg_gt (by
        rw [map_add, twE6Deg_pi_single_six, hdeg]
        norm_num)
  have hxδ : Commute x (pinnedX Tag.E6 Ω (twE6A6 - γ) 1) := by
    refine commute_pinnedX_of_deg (isRoot_single Tag.E6 twE6Six) (isRoot_A6_sub hγ hdeg) ?_ ?_ 1 1
    · rw [twE6Deg_pi_single_six, twE6Deg_A6_sub hdeg]
      norm_num
    · exact not_isRoot_of_twE6Deg_gt (by
        rw [map_add, twE6Deg_pi_single_six, twE6Deg_A6_sub hdeg]
        norm_num)
  have hxα : Commute x (pinnedX Tag.E6 Ω twE6A6 e) := by
    rw [commute_iff_eq, hx, ← pinnedX_add, ← pinnedX_add, add_comm]
  have hxu : Commute x (twE6U (γ := γ) e) := by
    rw [twE6U]
    exact (hxγ.mul_right hxδ).mul_right hxα
  have hfix : TwistedDiag.theta Fr (twE6G Ω * twE6U (γ := γ) e * (twE6G Ω)⁻¹) =
      twE6G Ω * twE6U (γ := γ) e * (twE6G Ω)⁻¹ := by
    rw [map_mul, map_mul, map_inv, hθg, theta_twE6U hFr hγ hdeg e he, twE6G_eq]
    rw [show (x * nn * x) * twE6U (γ := γ) e * (x * nn * x)⁻¹ =
        x * nn * (x * twE6U (γ := γ) e) * x⁻¹ * nn⁻¹ * x⁻¹ by group, hxu.eq]
    simp only [nn]
    group
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · exact Subgroup.mem_map_of_mem (MulAut.conj (twE6G Ω)).toMonoidHom
      (twE6U_mem hγ hdeg e)
  · rw [TwistedDiag.mem_thetaFixed]
    refine ⟨?_, hfix⟩
    refine Subgroup.mul_mem (H := adjointGroup Tag.E6 Ω)
      (Subgroup.mul_mem (H := adjointGroup Tag.E6 Ω) ?_ ?_) ?_
    · exact pinnedX_mem_adjointGroup _ _
    · exact CFSG.SeitzReduction.EPilot.rootSpan_le_adjointGroup' (radicalRoots Tag.E6 twE6A6)
        (twE6U_mem hγ hdeg e)
    · exact Subgroup.inv_mem _ (pinnedX_mem_adjointGroup _ _)


end Certs

end TwE6Eight

section Main


variable {Ω : Type} [Field Ω] [CharP Ω 2] [IsAlgClosed Ω]
variable {q : ℕ} [NeZero q]

theorem exists_twE6_eight_twoGroup (Fr : Ω →+* Ω) {n : ℕ} (hn : 1 ≤ n)
    (hFr : ∀ c, Fr c = c ^ (2 ^ n)) (hqQ : q ∣ 2 ^ n + 1) (ζ : Ωˣ) (hζ : ζ ^ q = 1) :
    ∃ S : Subgroup (ModGL Tag.E6 Ω), S ≤ TwistedDiag.thetaFixed Fr ∧ IsPGroup 2 S ∧
      twE6BZero ζ hζ ≤ Subgroup.normalizer (S : Set (ModGL Tag.E6 Ω)) ∧
      twE6BZero ζ hζ ⊓ Subgroup.centralizer (S : Set (ModGL Tag.E6 Ω)) = ⊥ := by
  obtain ⟨e, he⟩ := CFSG.RankThree.PartOne.KF4.exists_qpOmega (Ω := Ω) (f := n) hn
  refine ⟨TwE6Eight.twE6SBar Fr, inf_le_right, TwE6Eight.isPGroup_twE6SBar Fr,
    TwE6Eight.twE6BZero_le_normalizer hFr hqQ ζ hζ, ?_⟩
  refine le_bot_iff.1 ?_
  intro b hb
  rw [Subgroup.mem_inf] at hb
  obtain ⟨hbB, hbC⟩ := hb
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.1 hbB
  set a : Fin Tag.E6.rank → Ωˣ := zetaVec ζ hζ (twE6Cast (twE6B0Comb c)) with ha
  have hb_eq : b = rootDiagUnit Tag.E6 a := by
    rw [← hc, ha]
    rfl
  have hbg : b * TwE6Eight.twE6G Ω = TwE6Eight.twE6G Ω * b :=
    TwE6Eight.twE6BZero_commute_twE6G ζ hζ hbB
  have hu (i : Fin 5) : b * TwE6Eight.twE6U (γ := TwE6Eight.twE6Five i) e =
      TwE6Eight.twE6U (γ := TwE6Eight.twE6Five i) e * b := by
    have hmem : TwE6Eight.twE6G Ω * TwE6Eight.twE6U (γ := TwE6Eight.twE6Five i) e *
        (TwE6Eight.twE6G Ω)⁻¹ ∈ TwE6Eight.twE6SBar Fr :=
      TwE6Eight.conj_twE6U_mem_twE6SBar hFr (TwE6Eight.twE6Five_isRoot i)
        (TwE6Eight.twE6Deg_twE6Five i) e he
    have hcomm : b * (TwE6Eight.twE6G Ω * TwE6Eight.twE6U (γ := TwE6Eight.twE6Five i) e *
        (TwE6Eight.twE6G Ω)⁻¹) =
        (TwE6Eight.twE6G Ω * TwE6Eight.twE6U (γ := TwE6Eight.twE6Five i) e *
          (TwE6Eight.twE6G Ω)⁻¹) * b :=
      (Subgroup.mem_centralizer_iff.1 hbC _ hmem).symm
    have h1 := (Commute.conj_iff (h := (TwE6Eight.twE6G Ω)⁻¹)).2 hcomm
    rw [inv_inv] at h1
    have hmid : (TwE6Eight.twE6G Ω)⁻¹ *
        (TwE6Eight.twE6G Ω * TwE6Eight.twE6U (γ := TwE6Eight.twE6Five i) e *
          (TwE6Eight.twE6G Ω)⁻¹) * TwE6Eight.twE6G Ω =
        TwE6Eight.twE6U (γ := TwE6Eight.twE6Five i) e := by group
    rw [hmid] at h1
    have h2 : (TwE6Eight.twE6G Ω)⁻¹ * b * TwE6Eight.twE6G Ω = b := by
      calc (TwE6Eight.twE6G Ω)⁻¹ * b * TwE6Eight.twE6G Ω
          = (TwE6Eight.twE6G Ω)⁻¹ * (b * TwE6Eight.twE6G Ω) := by group
        _ = (TwE6Eight.twE6G Ω)⁻¹ * (TwE6Eight.twE6G Ω * b) := by rw [hbg]
        _ = b := by group
    rw [h2] at h1
    exact h1
  have hchar (i : Fin 5) : rootChar a (TwE6Eight.twE6Five i) = 1 := by
    refine TwE6Eight.rootChar_eq_one_of_commute_twE6U
      (TwE6Eight.twE6Five_isRoot i) (TwE6Eight.twE6Deg_twE6Five i) a e ?_
    rw [← hb_eq]
    calc b * TwE6Eight.twE6U (γ := TwE6Eight.twE6Five i) e * b⁻¹
        = (b * TwE6Eight.twE6U (γ := TwE6Eight.twE6Five i) e) * b⁻¹ := rfl
      _ = (TwE6Eight.twE6U (γ := TwE6Eight.twE6Five i) e * b) * b⁻¹ := by rw [hu i]
      _ = TwE6Eight.twE6U (γ := TwE6Eight.twE6Five i) e := by group
  have ha5 : a TwE6Eight.twE6Six = 1 := by
    rw [ha]
    exact TwE6Eight.twE6BZero_apply_six ζ hζ c
  have h6 : rootChar a TwE6Eight.twE6A6 = 1 := by
    rw [show rootChar a TwE6Eight.twE6A6 = a TwE6Eight.twE6Six from by
      rw [show TwE6Eight.twE6A6 = 1 • Pi.single TwE6Eight.twE6Six 1 by simp,
        rootChar_nsmul_single, pow_one]]
    exact ha5
  have ha1 : a = 1 := TwE6Eight.eq_one_of_rootChar_twE6Five h6 hchar
  rw [hb_eq, ha1, rootDiagUnit_one]
  exact Subgroup.mem_bot.2 rfl

end Main

end CFSG.LocalAnalysis.GLTheoremA.Y10F
