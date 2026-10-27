module

public import CFSG.LocalAnalysis.RankThreeTheoremC.ChevTwoInnerRankCover
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.RankThree.PartOne.KP.UnitaryTorus
import CFSG.RankThree.Classical2.UnitarySplitPrimeRank
import CFSG.Adapters.RankTwoModelTransports
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Index

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.ChevTwoInnerRank

open CFSG.RankThree.Classical2 CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.SectionRank.OddCover CFSG.RankThree.Classical CFSG.Assembly.LowTwoRank

theorem centralCoverFour_twistedA5Two (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA 5 q).Valid) (hp : q.p = 2) (he : q.exponent = 1) :
    CentralCoverFour (TauCeti.ValidLieTypeIndex.Group ⟨.twistedA 5 q, hv⟩) := by
  have h6 : CentralCoverFour (StatedProj (StatedSU 6 (2 ^ 1) CFSG.Fischer.F4)) := by
    intro Y _ _ φ hφ hker
    obtain ⟨U, hU, hcard⟩ := CFSG.RankThree.PartOne.stated_psu6_central_cover φ hφ hker
    exact ⟨U, ⟨hU.toIsMulCommutative, fun x hx => CFSG.elemPow_eq_one_of_isElementaryAbelian x hx⟩,
      hcard⟩
  obtain ⟨p, f, hp', hf'⟩ := q
  obtain rfl : p = 2 := hp
  obtain rfl : f = 1 := he
  exact CentralCoverFour.of_mulEquiv
    ((CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 5 _ hv).trans
      (CFSG.Adapters.RankTwoModelTransports.statedProjCongr
        (CFSG.Adapters.RankTwoModelTransports.glCongr CFSG.Fischer.F4.equivGaloisField.symm)
        (CFSG.Adapters.RankTwoModelTransports.glCongr_statedSU _ 6 (2 ^ 1))
        (CFSG.Adapters.RankTwoModelTransports.glCongr_statedScalars _))).symm h6

section Five

variable {K : Type} [Field K]

private def fiveGen (ζ : Kˣ) (j : Fin 4) (i : Fin 5) : Kˣ :=
  if i = j.castSucc then ζ else if i = 4 then ζ⁻¹ else 1

private theorem fiveGen_pow (ζ : Kˣ) {n : ℕ} (hζ : ζ ^ n = 1) (j : Fin 4) (i : Fin 5) :
    fiveGen ζ j i ^ n = 1 := by
  unfold fiveGen
  split_ifs
  · exact hζ
  · rw [inv_pow, hζ, inv_one]
  · exact one_pow n

private theorem fiveGen_prod (ζ : Kˣ) (j : Fin 4) : ∏ i, fiveGen ζ j i = 1 := by
  fin_cases j <;> simp only [fiveGen, Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.castSucc_zero,
    Fin.castSucc_one, Fin.reduceFinMk, Fin.reduceCastSucc, Fin.prod_univ_five, zero_ne_one,
    one_ne_zero, ↓reduceIte, Fin.reduceEq, one_mul, mul_one, mul_inv_cancel]

private theorem castSucc_ne_four (i : Fin 4) : (4 : Fin 5) ≠ i.castSucc := by
  revert i
  decide

private theorem fiveGen_swap (ζ : Kˣ) {i j : Fin 4} :
    fiveGen ζ i ∘ ⇑(Equiv.swap i.castSucc j.castSucc).symm = fiveGen ζ j := by
  funext k
  simp only [Function.comp_apply, Equiv.symm_swap, fiveGen, Equiv.swap_apply_eq_iff,
    Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne (castSucc_ne_four i)
      (castSucc_ne_four j)]

private theorem fiveGen_private (ζ : Kˣ) (hζ : orderOf ζ = 3) (j : Fin 4) :
    ∃ i, (∀ j', j' ≠ j → fiveGen ζ j' i = 1) ∧ orderOf (fiveGen ζ j i) = 3 := by
  refine ⟨j.castSucc, fun j' hj' => ?_, ?_⟩
  · have : j.castSucc ≠ j'.castSucc := fun h => hj' (Fin.castSucc_injective _ h).symm
    simp only [fiveGen, this, ↓reduceIte, Fin.isValue, (castSucc_ne_four j).symm]
  · simp only [fiveGen, ↓reduceIte, hζ]

private theorem pow_three_eq_one (a : Multiplicative (Fin 4 → ZMod 3)) : a ^ 3 = 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one]
  funext i
  have h3 : (3 : ZMod 3) = 0 := by decide
  simp only [Pi.smul_apply, nsmul_eq_mul, Nat.cast_ofNat, h3, zero_mul, Pi.zero_apply]

private theorem centralCoverFour_unitaryPSU_five {f : ℕ} (hK : UnitaryFieldData 2 f K)
    (h3 : 3 ∣ 2 ^ f + 1) : CentralCoverFour (unitaryPSU hK 5) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hchar : CharP K 2 := hK.charP
  have h2K : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  have hneg : (-1 : K) = 1 := by linear_combination -h2K
  obtain ⟨ζ, hζ, hζN⟩ := exists_orderOf_eq_norm_one hK Nat.prime_three h3
  have hζp : ζ ^ 3 = 1 := hζ ▸ pow_orderOf_eq_one ζ
  have hcp := fiveGen_pow ζ hζp
  set E := expHom (p := 3) (fiveGen ζ) hcp with hE
  have hcS : ∀ a, diagHom 5 (E a) ∈ unitarySU 2 f K 5 :=
    diagHom_expHom_mem_unitarySU hK (fiveGen ζ) hcp (fiveGen_prod ζ) (fiveGen_pow ζ hζN)
  have hinj : Function.Injective E := expHom_injective (fiveGen ζ) hcp (fiveGen_private ζ hζ)
  let δ : Multiplicative (Fin 4 → ZMod 3) →* unitarySU 2 f K 5 :=
    ((diagHom 5).comp E).codRestrict _ hcS
  have hδ : ∀ a, (δ a : GL (Fin 5) K) = diagHom 5 (E a) := fun a => rfl
  let θ : Multiplicative (Fin 4 → ZMod 3) →* unitaryPSU hK 5 := (unitaryProj hK 5).comp δ
  have hθsingle : ∀ j, (δ (Multiplicative.ofAdd (Pi.single j 1)) : GL (Fin 5) K) =
      diagHom 5 (fiveGen ζ j) := fun j => by rw [hδ, hE, expHom_single]
  have hθinj : Function.Injective θ := by
    refine (injective_iff_map_eq_one θ).mpr fun a ha => ?_
    have hmem : δ a ∈ unitaryScalars hK 5 := by
      rw [← ker_unitaryProj hK 5]
      exact ha
    obtain ⟨c, -, hcn, hc⟩ := mem_unitaryScalars.mp hmem
    have h1 : (δ (a ^ 3) : GL (Fin 5) K) = 1 := by rw [pow_three_eq_one, map_one]; rfl
    rw [map_pow, Subgroup.coe_pow, hc, ← map_pow] at h1
    have h2 := congrArg (fun g : GL (Fin 5) K => (g : Matrix (Fin 5) (Fin 5) K) 0 0) h1
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.diagonal_apply_eq, Units.val_one, Matrix.one_apply_eq] at h2
    have hc3 : c ^ 3 = 1 := Units.ext (by simpa using h2)
    have hc1 : c = 1 := by
      have := pow_gcd_eq_one.mpr ⟨hc3, hcn⟩
      rwa [show Nat.gcd 3 5 = 1 by norm_num, pow_one] at this
    have h4 : E a = 1 := by
      apply diagHom_injective 5
      rw [← hδ, hc, hc1, map_one, map_one]
    exact hinj (h4.trans (map_one E).symm)
  have hperm : ∀ π : Equiv.Perm (Fin 5), permGL π ∈ unitarySU 2 f K 5 := by
    intro π
    rw [mem_unitarySU_iff hK]
    refine ⟨?_, permGL_unitary hK π⟩
    rw [det_permGL]
    rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h
    · simp only [h, Units.val_one, Int.cast_one]
    · simp only [h, Units.val_neg, Units.val_one, Int.reduceNeg, Int.cast_neg, Int.cast_one,
        hneg]
  let w : Fin 4 → Fin 4 → unitarySU 2 f K 5 := fun i j =>
    ⟨permGL (Equiv.swap i.castSucc j.castSucc), hperm _⟩
  have hconj : ∀ i j : Fin 4, w i j * δ (Multiplicative.ofAdd (Pi.single i 1)) * (w i j)⁻¹ =
      δ (Multiplicative.ofAdd (Pi.single j 1)) := fun i j => by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hθsingle, hθsingle, permGL_mul_diagHom_mul_inv, fiveGen_swap]
  have hw : ∀ i j, w j i = w i j := fun i j => Subtype.ext (by
    simp only [w]
    rw [Equiv.swap_comm])
  refine centralCoverFour_of_swaps θ hθinj (fun i j => unitaryProj hK 5 (w i j)) ?_ ?_
  · intro i j _
    change unitaryProj hK 5 (w i j) * unitaryProj hK 5 (δ _) * (unitaryProj hK 5 (w i j))⁻¹ =
      unitaryProj hK 5 (δ _)
    rw [← map_inv, ← map_mul, ← map_mul, hconj]
  · intro i j _
    have h := hconj j i
    rw [hw i j] at h
    change unitaryProj hK 5 (w i j) * unitaryProj hK 5 (δ _) * (unitaryProj hK 5 (w i j))⁻¹ =
      unitaryProj hK 5 (δ _)
    rw [← map_inv, ← map_mul, ← map_mul, h]

end Five

theorem centralCoverFour_twistedA4Two (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA 4 q).Valid) (hp : q.p = 2) (he : q.exponent = 1) :
    CentralCoverFour (TauCeti.ValidLieTypeIndex.Group ⟨.twistedA 4 q, hv⟩) := by
  obtain ⟨p, f, hp', hf'⟩ := q
  obtain rfl : p = 2 := hp
  obtain rfl : f = 1 := he
  have hK : UnitaryFieldData 2 1 (GaloisField 2 (2 * 1)) :=
    ⟨Nat.prime_two, le_rfl, GaloisField.card 2 (2 * 1) (by norm_num)⟩
  exact CentralCoverFour.of_mulEquiv
    ((unitaryPSUEquiv hK (n := 5) (by norm_num)).trans
      (CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 4 _ hv).symm)
    (centralCoverFour_unitaryPSU_five hK (by norm_num))

end CFSG.LocalAnalysis.RankThreeTheoremC.ChevTwoInnerRank
