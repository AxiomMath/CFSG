module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeUSixModel
public import CFSG.RankThree.PartTwo.CTU6.Long

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.QuasithinUnique.Lin2.Five (tauSp)
open CFSG.LieType.Universal.Unitary (SU)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_involutive)
open CFSG.RankThree.PartOne.CTP (lbEmb sbEmb matS)
open CFSG.RankThree.PartTwo.CTU6 (lbSU4 range_lbSU4)
open CFSG.SeitzReduction.F4Pilot (statedSpMap centralizerPerfectCore
  centralizerPerfectCore_le_centralizer)
open CFSG.SeitzReduction.UnitaryPilot (modelToG symm_mem_modelToG)
open CFSG.Quasithin (perfectCore perfectCore_le le_perfectCore_of_perfect perfectCore_perfect)
open scoped MatrixGroups

section Transport

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K]

theorem map_uModelSU_map_eq_of_N1 (e : L ≃* StatedSp 3 K) (k : Fin 3) {f : ℕ} {K' : Type}
    [Field K'] (h : UnitaryFieldData 2 f K') [CharP h.fixedField 2] {C₀ : GL (Fin (2 * 2)) K'}
    (hC₀ : (C₀ : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K') = blockSwapJ (2 * 2) 2)
    (ι : K ≃+* h.fixedField) (β : StatedSp 2 K →* StatedSp 2 K)
    (Φ : gramSU h (C₀ : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K') →* G)
    (hN1 : ∀ x : StatedSp 2 K,
      Φ (uModelSU h hC₀ (statedSpMap (ι : K →+* h.fixedField) 2 (β x))) =
        ((e.symm ((complSpEquiv k x : complSp K k) : StatedSp 3 K) : L) : G))
    (T₄ : Subgroup (StatedSp 2 K)) :
    (((T₄.map β).map (statedSpMap (ι : K →+* h.fixedField) 2)).map (uModelSU h hC₀)).map Φ =
      modelToG e (T₄.map (complSpHom (K := K) k)) := by
  ext y
  constructor
  · rintro ⟨_, ⟨_, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩, rfl⟩
    change Φ (uModelSU h hC₀ (statedSpMap (ι : K →+* h.fixedField) 2 (β x))) ∈ _
    rw [hN1]
    exact symm_mem_modelToG e ⟨x, hx, rfl⟩
  · intro hy
    obtain ⟨_, ⟨x, hx, rfl⟩, hxy⟩ := (UnitaryPilot.mem_modelToG e).1 hy
    refine ⟨_, ⟨_, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩, ?_⟩
    change Φ (uModelSU h hC₀ (statedSpMap (ι : K →+* h.fixedField) 2 (β x))) = y
    rw [hN1, ← hxy]
    rfl

variable [Finite G]

theorem pieceCore_eq_map_perfectCore_centralizer (e : L ≃* StatedSp 3 K) (hK : 4 ≤ Nat.card K)
    {k : Fin 3} {J : Finset (Fin 3)} (hk : k ∉ spSupport J) {T₄ : Subgroup (StatedSp 2 K)}
    (hfact : leviTorusSp K J ≤ rootTorusSp K k ⊔ T₄.map (complSpHom (K := K) k))
    (hT₄ : T₄.map (complSpHom (K := K) k) ≤ leviTorusSp K J)
    {S : Type*} [Group S] [Finite S] (Φ : S →* G) (hrange : Φ.range = neighbourCore e k)
    (hker : Φ.ker ≤ center S) (Y : Subgroup S)
    (hY : Y.map Φ = modelToG e (T₄.map (complSpHom (K := K) k))) :
    pieceCore e J = (perfectCore (centralizer (Y : Set S))).map Φ := by
  have hΦE : ∀ x, Φ x ∈ neighbourCore e k := fun x => hrange ▸ ⟨x, rfl⟩
  set Φ' := Φ.codRestrict _ hΦE with hΦ'
  have hΦ's : Function.Surjective Φ' := by
    rintro ⟨y, hy⟩
    rw [← hrange] at hy
    obtain ⟨x, rfl⟩ := hy
    exact ⟨x, rfl⟩
  have hker' : Φ'.ker ≤ center S := by
    rw [hΦ', MonoidHom.ker_codRestrict]
    exact hker
  set YG := modelToG e (T₄.map (complSpHom (K := K) k)) with hYG
  have hYE : YG ≤ neighbourCore e k := by
    refine (UnitaryPilot.modelToG_mono e ?_).trans
      (modelToG_complSp_le_neighbourCore e hK (by norm_num) k)
    rintro _ ⟨x, -, rfl⟩
    exact (complSpEquiv k x).2
  have hYmap : Y.map Φ' = YG.subgroupOf (neighbourCore e k) := by
    ext y
    rw [mem_subgroupOf, ← hY]
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s, hs, rfl⟩
    · rintro ⟨s, hs, hsy⟩
      exact ⟨s, hs, Subtype.ext hsy⟩
  rw [pieceCore_eq e hk, inf_centralizer_eq_of_le_sup (H := neighbourCore e k)
    (X := modelToG e (rootTorusSp K k)) (Y := YG) (centralizerPerfectCore_le_centralizer _)
    (UnitaryPilot.modelToG_mono e hT₄)
    (by rw [← UnitaryPilot.modelToG_sup]; exact UnitaryPilot.modelToG_mono e hfact),
    perfectCore_inf_centralizer_eq_map hYE]
  have hcore : perfectCore (centralizer ((YG.subgroupOf (neighbourCore e k) :
      Subgroup (neighbourCore e k)) : Set (neighbourCore e k))) =
        (perfectCore (centralizer (Y : Set S))).map Φ' := by
    rw [← hYmap]
    exact le_antisymm (le_map_perfectCore_centralizer Φ' hΦ's hker' Y (perfectCore_perfect _)
      (perfectCore_le _)) (map_perfectCore_centralizer_le Φ' Y)
  rw [hcore, Subgroup.map_map]
  rfl

end Transport

section Levi

open CFSG.LieType.Steinberg (fixedSubfield card_fixedSubfield card_SU_two
  card_specialLinearGroup_fin_two)

variable {f : ℕ} {K' : Type} [Field K'] [Finite K'] [CharP K' 2] (h : UnitaryFieldData 2 f K')
  [CharP h.fixedField 2] {C₀ : GL (Fin (2 * 2)) K'}
  (hC₀ : (C₀ : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K') = blockSwapJ (2 * 2) 2)

theorem commute_ctuGramEquiv_lbEmb_uModelSU (N : SU (unitaryInvolution K' 2 f) 2)
    (κ : h.fixedFieldˣ) :
    Commute (ctuGramEquiv h hC₀ (RingEquiv.refl K') (lbEmb (unitaryInvolution K' 2 f) N))
      (uModelSU h hC₀ (rootTorusHom h.fixedField 2 0 κ)) := by
  show _ * _ = _ * _
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [coe_ctuGramEquiv_lbEmb, coe_uModelSU_rootTorusHom_zero]
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  fin_cases i <;> fin_cases j <;> simp

theorem map_range_lbEmb_le_centralizer_uStdTorus :
    (lbEmb (unitaryInvolution K' 2 f)).range.map
        (ctuGramEquiv h hC₀ (RingEquiv.refl K')).toMonoidHom ≤
      centralizer (uStdTorus h hC₀ :
        Set (gramSU h (C₀ : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K'))) := by
  rintro _ ⟨_, ⟨N, rfl⟩, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨_, ⟨κ, rfl⟩, rfl⟩
  exact (commute_ctuGramEquiv_lbEmb_uModelSU h hC₀ N κ).symm.eq

omit [CharP h.fixedField 2] in
theorem commutator_map_range_lbEmb (hq : 4 ≤ 2 ^ f) :
    ⁅(lbEmb (unitaryInvolution K' 2 f)).range.map
        (ctuGramEquiv h hC₀ (RingEquiv.refl K')).toMonoidHom,
      (lbEmb (unitaryInvolution K' 2 f)).range.map
        (ctuGramEquiv h hC₀ (RingEquiv.refl K')).toMonoidHom⁆ =
      (lbEmb (unitaryInvolution K' 2 f)).range.map
        (ctuGramEquiv h hC₀ (RingEquiv.refl K')).toMonoidHom := by
  have hF : 4 ≤ Nat.card (fixedSubfield K' 2 f) := by
    rw [card_fixedSubfield h.card_eq_sq]
    exact hq
  have := CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card _ hF
  rw [← range_lbSU4, ← MonoidHom.range_comp, MonoidHom.range_eq_map, ← Subgroup.map_commutator,
    ← commutator_def, Group.IsPerfect.commutator_eq_top]

theorem perfectCore_centralizer_uStdTorus_eq (hq : 4 ≤ 2 ^ f) :
    perfectCore (centralizer (uStdTorus h hC₀ :
        Set (gramSU h (C₀ : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K')))) =
      (lbEmb (unitaryInvolution K' 2 f)).range.map
        (ctuGramEquiv h hC₀ (RingEquiv.refl K')).toMonoidHom := by
  have hle := le_perfectCore_of_perfect (map_range_lbEmb_le_centralizer_uStdTorus h hC₀)
    (commutator_map_range_lbEmb h hC₀ hq)
  symm
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  have hk : 4 ≤ Nat.card h.fixedField := by rw [h.card_fixedField]; exact hq
  refine (Nat.le_of_dvd Nat.card_pos
    (natCard_perfectCore_centralizer_uStdTorus_dvd h hC₀ hk)).trans ?_
  rw [Subgroup.card_map_of_injective (f := (ctuGramEquiv h hC₀ (RingEquiv.refl K')).toMonoidHom)
      (ctuGramEquiv h hC₀ (RingEquiv.refl K')).injective,
    CFSG.RankThree.PartOne.CTP.natCard_range_lbEmb, card_SU_two h.card_eq_sq,
    card_specialLinearGroup_fin_two, h.card_fixedField]

end Levi

end CFSG.SeitzReduction.SymplecticPilot
