module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeUSixPair
public import CFSG.RankThree.PartTwo.CTU6.Model

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.QuasithinUnique.Lin2.Five (tauSp)
open CFSG.LieType.Universal.Unitary (SU)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_involutive)
open CFSG.LieType.Steinberg (fixedSubfield)
open CFSG.RankThree.PartOne.CTP (lbEmb sbEmb)
open CFSG.RankThree.PartTwo.CTU6 (lbSU4 range_lbSU4 lbSU4_injective su4Model)
open CFSG.SeitzReduction.F4Pilot (statedSpMap)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)
open CFSG.Quasithin (perfectCore)
open scoped MatrixGroups

section Tori

variable {K : Type} [Field K] {k : Type} [Field k]

theorem map_statedSpMap_rootTorusSp_eq (ι : K ≃+* k) :
    (rootTorusSp K (0 : Fin 2)).map (statedSpMap (ι : K →+* k) 2) = rootTorusSp k 0 := by
  ext x
  constructor
  · rintro ⟨_, ⟨κ, rfl⟩, rfl⟩
    exact ⟨_, (statedSpMap_rootTorusHom (ι : K →+* k) 0 κ).symm⟩
  · rintro ⟨μ, rfl⟩
    refine ⟨_, ⟨Units.map (ι.symm : k →+* K) μ, rfl⟩, ?_⟩
    rw [statedSpMap_rootTorusHom]
    congr 1
    ext
    simp

variable [CharP k 2]

theorem map_statedSpMap_siegelTorus_eq (ι : K ≃+* k) :
    (siegelTorus K 2).map (statedSpMap (ι : K →+* k) 2) = (rootTorusSp k 0).map tauSp := by
  have hconst : ∀ μ : kˣ, (![μ, μ] : Fin 2 → kˣ) = fun _ => μ := fun μ => by
    funext i
    fin_cases i <;> rfl
  ext x
  constructor
  · rintro ⟨_, ⟨s, rfl⟩, rfl⟩
    refine ⟨_, ⟨Units.map (ι : K →* k) s, rfl⟩, ?_⟩
    change tauSp (rootTorusHom k 2 0 (Units.map (ι : K →* k) s)) =
      statedSpMap (ι : K →+* k) 2 (diagSp K 2 (fun _ => s))
    rw [tauSp_rootTorusHom_zero, statedSpMap_diagSp, hconst]
    rfl
  · rintro ⟨_, ⟨μ, rfl⟩, rfl⟩
    refine ⟨_, ⟨Units.map (ι.symm : k →* K) μ, rfl⟩, ?_⟩
    change statedSpMap (ι : K →+* k) 2 (diagSp K 2 (fun _ => Units.map (ι.symm : k →* K) μ)) =
      tauSp (rootTorusHom k 2 0 μ)
    rw [tauSp_rootTorusHom_zero, statedSpMap_diagSp, hconst]
    congr 1
    funext i
    ext
    simp

end Tori

section Pieces

open CFSG.LieType.Steinberg (card_SU_two card_specialLinearGroup_fin_two)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]
  {f : ℕ} (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (e : L ≃* StatedSp 3 K)
  {K' : Type} [Field K'] [Finite K'] [CharP K' 2] (h : UnitaryFieldData 2 f K')
  [CharP h.fixedField 2] {C₀ : GL (Fin (2 * 2)) K'}
  (hC₀ : (C₀ : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K') = blockSwapJ (2 * 2) 2)
  (ι : K ≃+* h.fixedField) (Φ : gramSU h (C₀ : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K') →* G)
  (hrange : Φ.range = neighbourCore e 0)
  (hker : Φ.ker ≤ center (gramSU h (C₀ : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K')))
  (hN1 : ∀ x : StatedSp 2 K,
    Φ (uModelSU h hC₀ (statedSpMap (ι : K →+* h.fixedField) 2 x)) =
      ((e.symm ((complSpEquiv 0 x : complSp K 0) : StatedSp 3 K) : L) : G))

include hKc hf hrange hker hN1 in
theorem pieceCore_two_eq_map_lbEmb_of_std :
    pieceCore e ({2} : Finset (Fin 3)) =
      ((lbEmb (unitaryInvolution K' 2 f)).range.map
        (ctuGramEquiv h hC₀ (RingEquiv.refl K')).toMonoidHom).map Φ := by
  have hK4 : 4 ≤ Nat.card K := hKc ▸ four_le_two_pow hf
  have hY : (uStdTorus h hC₀).map Φ =
      modelToG e ((rootTorusSp K 0).map (complSpHom (K := K) 0)) := by
    have h1 := map_uModelSU_map_eq_of_N1 e 0 h hC₀ ι (MonoidHom.id _) Φ hN1 (rootTorusSp K 0)
    rwa [Subgroup.map_id, map_statedSpMap_rootTorusSp_eq ι] at h1
  rw [pieceCore_eq_map_perfectCore_centralizer e hK4 (k := 0) (by decide)
    leviTorusSp_two_le_sup map_rootTorusSp_zero_le_leviTorusSp_two Φ hrange hker
    (uStdTorus h hC₀) hY, perfectCore_centralizer_uStdTorus_eq h hC₀ (four_le_two_pow hf)]

include hKc hf hrange hker hN1 in
theorem pieceCore_two_eq_modelToG_of_std [Finite K] :
    pieceCore e ({2} : Finset (Fin 3)) = modelToG e (simpleRootSL2 K 2) := by
  have hK4 : 4 ≤ Nat.card K := hKc ▸ four_le_two_pow hf
  symm
  apply Subgroup.eq_of_le_of_card_ge
    (modelToG_simpleRootSL2_le_pieceCore e hK4 (Finset.mem_singleton_self 2))
  rw [natCard_modelToG_simpleRootSL2,
    pieceCore_two_eq_map_lbEmb_of_std hKc hf e h hC₀ ι Φ hrange hker hN1]
  refine (Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd _ _)).trans ?_
  rw [Subgroup.card_map_of_injective (f := (ctuGramEquiv h hC₀ (RingEquiv.refl K')).toMonoidHom)
      (ctuGramEquiv h hC₀ (RingEquiv.refl K')).injective,
    CFSG.RankThree.PartOne.CTP.natCard_range_lbEmb, card_SU_two h.card_eq_sq,
    card_specialLinearGroup_fin_two, hKc]

omit [CharP K' 2] in
include hKc hf hrange hker hN1 in
theorem pieceCore_one_eq_map_lambdaU_of_std :
    pieceCore e ({1} : Finset (Fin 3)) = (lambdaU h hC₀).range.map Φ := by
  have hK4 : 4 ≤ Nat.card K := hKc ▸ four_le_two_pow hf
  have hk4 : 4 ≤ Nat.card h.fixedField := by
    rw [h.card_fixedField]
    exact four_le_two_pow hf
  have hY : (uTwTorus h hC₀).map Φ =
      modelToG e ((siegelTorus K 2).map (complSpHom (K := K) 0)) := by
    have h1 := map_uModelSU_map_eq_of_N1 e 0 h hC₀ ι (MonoidHom.id _) Φ hN1 (siegelTorus K 2)
    rwa [Subgroup.map_id, map_statedSpMap_siegelTorus_eq ι] at h1
  rw [pieceCore_eq_map_perfectCore_centralizer e hK4 (k := 0) (by decide)
    leviTorusSp_one_le_sup map_siegelTorus_zero_le_leviTorusSp_one Φ hrange hker
    (uTwTorus h hC₀) hY, perfectCore_centralizer_uTwTorus_eq h hC₀ hk4]

include hKc hf hrange hker hN1 in
theorem exists_su4ModelPair_of_std :
    ∃ W, (su4Model h.card_eq_sq).StandardPair W (pieceCore e ({2} : Finset (Fin 3)))
      (pieceCore e ({1} : Finset (Fin 3))) := by
  set χ := ctuGramEquiv h hC₀ (RingEquiv.refl K') with hχ
  set θ : SU (unitaryInvolution K' 2 f) 4 →* G := Φ.comp χ.toMonoidHom with hθ
  have hθker : θ.ker ≤ center _ := fun x hx => mem_center_of_mulEquiv_mem_center χ (hker hx)
  have : CharP (fixedSubfield K' 2 f) 2 :=
    RingHom.charP (fixedSubfield K' 2 f).subtype (fixedSubfield K' 2 f).subtype.injective 2
  refine ⟨θ.range, θ, rfl, hθker,
    injective_comp_of_ker_le_center lbSU4_injective center_SL_two_eq_bot_of_charTwo hθker,
    injective_comp_of_ker_le_center (CFSG.RankThree.PartOne.CTP.sbEmb_injective _ _)
      center_SL_two_eq_bot_of_charTwo hθker, ?_, ?_⟩
  · change (lbSU4 K' f).range.map θ = _
    rw [range_lbSU4, pieceCore_two_eq_map_lbEmb_of_std hKc hf e h hC₀ ι Φ hrange hker hN1,
      Subgroup.map_map]
  · change (sbEmb (unitaryInvolution K' 2 f) (unitaryInvolution_involutive h.card_eq_sq)).range.map
      θ = _
    rw [pieceCore_one_eq_map_lambdaU_of_std hKc hf e h hC₀ ι Φ hrange hker hN1,
      ← map_range_sbEmb_ctuGramEquiv h hC₀, Subgroup.map_map]

end Pieces

end CFSG.SeitzReduction.SymplecticPilot
