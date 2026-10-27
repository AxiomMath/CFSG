module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotParamNormalizeSp4
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotRows
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotSwapBLiftSchur
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourNormalCore
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourParamLift
import CFSG.Dihedral.DisconnectedInvolutionGraph.OddCore

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer solvable_of_equiv)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore OddSchurTrivial HasBLift statedSpMap)
open CFSG.SeitzReduction.UnitaryPilot (modelToG symm_mem_modelToG)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldSp)

section Naturality

variable {K : Type} [Field K] {F : Type} [Field F]

theorem mat_statedSpMap {n : ℕ} (ι : K →+* F) (g : StatedSp n K) :
    mat n F (statedSpMap ι n g) = (mat n K g).map ι :=
  rfl

theorem spEmbed_statedSpMap {m n : ℕ} {σ' : Fin m → Fin n} (hσ' : Function.Injective σ')
    (ι : K →+* F) (g : StatedSp m K) :
    spEmbed σ' hσ' (statedSpMap ι m g) = statedSpMap ι n (spEmbed σ' hσ' g) := by
  refine mat_injective ?_
  rw [mat_spEmbed, mat_statedSpMap, mat_statedSpMap, mat_spEmbed]
  ext a b
  rw [Matrix.map_apply]
  by_cases h : a ∈ Set.range (Sum.map σ' σ') ∧ b ∈ Set.range (Sum.map σ' σ')
  · obtain ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩ := h
    rw [spEmbedMat_apply_image hσ', spEmbedMat_apply_image hσ', Matrix.map_apply]
  · rw [spEmbedMat_apply_of_not_mem _ h, spEmbedMat_apply_of_not_mem _ h]
    by_cases hab : a = b
    · rw [hab, Matrix.one_apply_eq, Matrix.one_apply_eq, map_one]
    · rw [Matrix.one_apply_ne hab, Matrix.one_apply_ne hab, map_zero]

theorem complSpEquiv_statedSpMap {m : ℕ} (ι : K →+* F) (k : Fin (m + 1)) (g : StatedSp m K) :
    ((complSpEquiv k (statedSpMap ι m g) : complSp F k) : StatedSp (m + 1) F) =
      statedSpMap ι (m + 1) (complSpEquiv k g) := by
  rw [coe_complSpEquiv_apply, coe_complSpEquiv_apply, spEmbed_statedSpMap]

theorem complSpEquiv_fieldSp {m : ℕ} (σ : F ≃+* F) (k : Fin (m + 1)) (g : StatedSp m F) :
    ((complSpEquiv k (fieldSp m F σ g) : complSp F k) : StatedSp (m + 1) F) =
      fieldSp (m + 1) F σ (complSpEquiv k g) := by
  rw [F4Pilot.fieldSp_eq_statedSpMap, F4Pilot.fieldSp_eq_statedSpMap, complSpEquiv_statedSpMap]

end Naturality

section QuadraticField

theorem natCard_eq_two_pow_two_mul_of_fix {K F : Type} [Field K] [Field F] [Finite F]
    [CharP F 2] (ι : K →+* F) {f : ℕ} (hK : Nat.card K = 2 ^ f) {σ : F ≃+* F}
    (hσ : orderOf σ = 2) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι) :
    Nat.card F = 2 ^ (2 * f) := by
  obtain ⟨d, hd, hF⟩ := F4Pilot.exists_natCard_eq_two_pow_of_charTwo (K := F)
  have hσσ : σ * σ = 1 := by rw [← sq, ← hσ, pow_orderOf_eq_one]
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hσ
    exact absurd hσ (by norm_num)
  obtain ⟨hdeven, -, hcard⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.SpChain.ringEquiv_involution_facts hd hF hσσ hσ1
  have hfixcard : Nat.card (CFSG.ComponentClassification.UnbalancedCatalog.descentField σ) =
      Nat.card K := by
    rw [← Nat.card_range_of_injective ι.injective]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
    rw [CFSG.ComponentClassification.UnbalancedCatalog.mem_descentField]
    exact hfix x
  rw [hfixcard, hK] at hcard
  have h2 := Nat.pow_right_injective (le_refl 2) hcard
  rw [hF]
  congr 1
  obtain ⟨c, rfl⟩ := hdeven
  omega

end QuadraticField

section BlockEquiv

variable {K : Type} [Field K] {F : Type} [Field F] {m : ℕ}

variable (F) in
@[expose] noncomputable def blockComplEquiv (k : Fin (m + 1)) :
    spBlock F ({k}ᶜ : Finset (Fin (m + 1))) ≃* StatedSp m F :=
  (MulEquiv.subgroupCongr (spBlock_compl_singleton (F := F) k)).trans (complSpEquiv k).symm

theorem coe_complSpEquiv_blockComplEquiv (k : Fin (m + 1))
    (y : spBlock F ({k}ᶜ : Finset (Fin (m + 1)))) :
    ((complSpEquiv k (blockComplEquiv F k y) : complSp F k) : StatedSp (m + 1) F) = y := by
  rw [blockComplEquiv, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  rfl

theorem blockComplEquiv_spFieldMap (ι : K →+* F) (k : Fin (m + 1)) {x : StatedSp (m + 1) K}
    (hx : x ∈ spBlock K ({k}ᶜ : Finset (Fin (m + 1)))) :
    blockComplEquiv F k ⟨spFieldMap (m + 1) ι x, spFieldMap_mem_spBlock ι hx⟩ =
      statedSpMap ι m (blockComplEquiv K k ⟨x, hx⟩) := by
  apply (complSpEquiv (K := F) k).injective
  apply Subtype.ext
  rw [coe_complSpEquiv_blockComplEquiv, complSpEquiv_statedSpMap,
    coe_complSpEquiv_blockComplEquiv]
  rfl

theorem blockComplEquiv_fieldBlockSp (σ : F ≃+* F) (k : Fin (m + 1))
    (x : spBlock F ({k}ᶜ : Finset (Fin (m + 1)))) :
    blockComplEquiv F k (fieldBlockSp σ ({k}ᶜ : Finset (Fin (m + 1))) x) =
      fieldSp m F σ (blockComplEquiv F k x) := by
  apply (complSpEquiv (K := F) k).injective
  apply Subtype.ext
  rw [coe_complSpEquiv_blockComplEquiv, complSpEquiv_fieldSp, coe_complSpEquiv_blockComplEquiv,
    coe_fieldBlockSp_eq_fieldSp]

end BlockEquiv

section Aux

theorem nonempty_mulEquiv_statedSp_of_centerQuotient_of_odd
    {Kc : Type} [Group Kc] [Finite Kc]
    (hKc : Group.IsPerfect Kc) (hodd : Odd (Nat.card (center Kc))) {r : ℕ} {F : Type} [Field F]
    [Finite F] [CharP F 2] (eF : Kc ⧸ center Kc ≃* StatedSp r F) :
    Nonempty (Kc ≃* StatedSp r F) := by
  let η : Kc →* StatedSp r F := eF.toMonoidHom.comp (QuotientGroup.mk' (center Kc))
  have hs : Function.Surjective η := eF.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : η.ker = center Kc := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hinj := F4Pilot.oddSchurTrivial_statedSp r F Kc hKc η hs hker.le (hker ▸ hodd)
  exact ⟨MulEquiv.ofBijective η ⟨hinj, hs⟩⟩

theorem map_eqLocus_normalizerMonoidHom_eq {G : Type*} [Group G] {E : Subgroup G} {t : G}
    (hN : t ∈ normalizer (E : Set G)) :
    (MonoidHom.eqLocus (E.normalizerMonoidHom ⟨t, hN⟩).toMonoidHom (MonoidHom.id E)).map
      E.subtype = E ⊓ centralizer ({t} : Set G) := by
  ext g
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine mem_inf.2 ⟨y.2, ?_⟩
    have h1 : t * (y : G) * t⁻¹ = y := by
      rw [← Subgroup.normalizerMonoidHom_apply_apply_coe E ⟨t, hN⟩ y]
      exact congrArg Subtype.val hy
    rw [mem_centralizer_singleton_iff]
    exact (mul_inv_eq_iff_eq_mul.1 h1).symm
  · intro hg
    obtain ⟨hgE, hgt⟩ := mem_inf.1 hg
    refine ⟨⟨g, hgE⟩, Subtype.ext ?_, rfl⟩
    change ((E.normalizerMonoidHom ⟨t, hN⟩ ⟨g, hgE⟩ : E) : G) = g
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    rw [mem_centralizer_singleton_iff] at hgt
    rw [← hgt, mul_inv_cancel_right]

end Aux

section Fix

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]

theorem perfectCore_neighbourCore_inf_centralizer_eq {m f : ℕ} (hset : SeitzSetting G L)
    (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (hm : 2 ≤ m) (e : L ≃* StatedSp (m + 1) K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) (k : Fin (m + 1)) :
    perfectCore (neighbourCore e k ⊓ centralizer ({t} : Set G)) = modelToG e (complSp K k) := by
  have : Finite K := LinearPilot.finite_of_card_eq_two_pow hKc
  have : CharP K 2 := LinearPilot.charP_two_of_card_eq_two_pow hKc
  have hq : 4 ≤ Nat.card K := hKc ▸ four_le_two_pow hf
  have hcompl : ⁅complSp K k, complSp K k⁆ = complSp K k := by
    rw [← spBlock_compl_singleton]
    exact commutator_spBlock_eq hq _
  have hDperf := UnitaryPilot.modelToG_perfect e hcompl
  have hDE := modelToG_complSp_le_neighbourCore e hq (by omega) k
  have hDt : modelToG e (complSp K k) ≤ centralizer ({t} : Set G) := fun d hd =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htC d (UnitaryPilot.modelToG_le e _ hd))
  refine le_antisymm ?_ (CFSG.Quasithin.le_perfectCore_of_perfect (le_inf hDE hDt) hDperf)
  have hP := CFSG.Quasithin.perfectCore_perfect (neighbourCore e k ⊓ centralizer ({t} : Set G))
  have hPt : perfectCore (neighbourCore e k ⊓ centralizer ({t} : Set G)) ≤
      centralizer ({t} : Set G) := (CFSG.Quasithin.perfectCore_le _).trans inf_le_right
  have hOut : Group.IsSolvable (Outer L) :=
    isSolvable_outer_of_isCyclic (isCyclic_outer_of_mulEquiv_statedSp (by omega : 3 ≤ m + 1) e)
  have hPL := std_perfect_le hset.standardSetting hOut htC ht hP hPt
  have hPX : perfectCore (neighbourCore e k ⊓ centralizer ({t} : Set G)) ≤
      centralizer (modelToG e (rootTorusSp K k) : Set G) :=
    (CFSG.Quasithin.perfectCore_le _).trans
      (inf_le_left.trans (F4Pilot.centralizerPerfectCore_le_centralizer _))
  have hPLX := le_inf hPL hPX
  rw [UnitaryPilot.inf_centralizer_modelToG, (centralizer_rootTorusSp hq k).1,
    UnitaryPilot.modelToG_sup] at hPLX
  have hXD : modelToG e (rootTorusSp K k) ≤ centralizer (modelToG e (complSp K k) : Set G) :=
    UnitaryPilot.modelToG_le_centralizer e
      (le_centralizer_iff.mp (complSp_le_centralizer_rootTorusSp k))
  have hXX : modelToG e (rootTorusSp K k) ≤ centralizer (modelToG e (rootTorusSp K k) : Set G) :=
    UnitaryPilot.modelToG_le_centralizer e (rootTorusSp_le_centralizer_self k)
  have hXsolv : Group.IsSolvable (modelToG e (rootTorusSp K k)) :=
    Group.isSolvable_of_comm fun a b => Subtype.ext (mem_centralizer_iff.1 (hXX b.2) a a.2)
  exact perfect_le_of_le_sup (hXD.trans (centralizer_le_normalizer _)) hXsolv hP
    (by rw [sup_comm]; exact hPLX)

end Fix

section Lift


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]

theorem exists_centralizerPerfectCore_mulEquiv_of_field {m f : ℕ} (hset : SeitzSetting G L)
    (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (hm : 2 ≤ m) (e : L ≃* StatedSp (m + 1) K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) (k : Fin (m + 1)) {X : Subgroup G}
    (hX : X = modelToG e (rootTorusSp K k)) {D : Subgroup G} (hD : D = modelToG e (complSp K k))
    (h : HR8KindAtSp t m f X D .field) (hN : t ∈ normalizer (centralizerPerfectCore X : Set G)) :
    ∃ (F' : Type) (_ : Field F') (_ : Finite F') (_ : CharP F' 2), Nat.card F' = 2 ^ (2 * f) ∧
      Nonempty (StatedSp m F' ≃* centralizerPerfectCore X) ∧
      (centralizerPerfectCore X).normalizerMonoidHom ⟨t, hN⟩ ∉
        (MulAut.conj : centralizerPerfectCore X →* MulAut (centralizerPerfectCore X)).range := by
  have : Finite K := LinearPilot.finite_of_card_eq_two_pow hKc
  have : CharP K 2 := LinearPilot.charP_two_of_card_eq_two_pow hKc
  have hq : 4 ≤ Nat.card K := hKc ▸ four_le_two_pow hf
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  obtain ⟨htX, Kb, hKb, -, hcase⟩ := h
  obtain ⟨-, -, hlt, hsK, hsN, hov, hty⟩ := hcase.resolve_right fun h => by cases h.1
  have hty' : LieModel (Kb ⧸ center Kb) .PSp m 2 (2 * f) := hty
  obtain ⟨F', _, _, _, hF', ⟨eF⟩⟩ := exists_mulEquiv_statedSp_of_lieModel hty'
  have hKbP : Group.IsPerfect Kb := hKb.1.1
  obtain ⟨eK⟩ := nonempty_mulEquiv_statedSp_of_centerQuotient_of_odd hKbP hov.2.1 eF
  have ht' : (⟨t, htX⟩ : centralizer (X : Set G)) * ⟨t, htX⟩ = 1 := Subtype.ext htt
  have hsC : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∉
      centralizer (Kb : Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) := by
    intro hc
    refine hov.1 ⟨1, MulEquiv.ext fun k => Subtype.ext ?_⟩
    rw [map_one, MulAut.one_apply, Subgroup.normalizerMonoidHom_apply_apply_coe,
      ← mem_centralizer_iff.1 hc k k.2, mul_inv_cancel_right]
  have hs1 : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ≠ 1 :=
    fun h1 => hsK (h1 ▸ one_mem Kb)
  have hs2 : orderOf (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩) = 2 :=
    orderOf_eq_prime (by rw [sq, ← map_mul, ht', map_one]) hs1
  have hDt : D ≤ centralizer ({t} : Set G) := by
    rw [hD]
    exact fun d hd => mem_centralizer_singleton_iff.2
      (mem_centralizer_iff.1 htC d (UnitaryPilot.modelToG_le e _ hd))
  have hsD : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∈
      centralizer (((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) : Subgroup _) :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨d, hd, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.1 (hDt (mem_subgroupOf.1 hd)))
  obtain ⟨-, hsyl, -⟩ := neighbour_standard_rootTorusSp_of_seitzSetting hset hKc hq hm e htC ht k
    hX htX hD
  have hOut : Group.IsSolvable (Outer Kb) := by
    have : Group.IsSolvable (Outer (StatedSp m F')) := isSolvable_outer_statedSp hm
    exact solvable_of_equiv eK.symm
  have hcore := LinearPilot.perfectCore_top_eq_of_isComponent
    (F4Pilot.pPrimeCore_two_quotient_oddCore_eq_bot _) hKb hlt.le hs2 hsD hsN hsC hsyl hOut
  obtain ⟨-, -, hBall⟩ := bLift_neighbour_rootTorusSp_of_seitzSetting hset hKc hq hm e htC ht k hX
    htX hD
  have hB : HasBLift Kb := hBall Kb (isPerfect_iff.mp hKbP) hsN
    (F4Pilot.le_commutator_zpowers_of_isQuasisimple hKb.1 hsN hsC)
  obtain ⟨qh, hqs, hqker, hqapp⟩ :=
    LinearPilot.exists_surjective_centralizerPerfectCore_of_perfectCore_eq hcore hB
  have hle : centralizerPerfectCore X ≤ centralizer (X : Set G) :=
    F4Pilot.centralizerPerfectCore_le_centralizer X
  have hmemO : ∀ y : qh.ker, (Subgroup.inclusion hle) (y : centralizerPerfectCore X) ∈
      oddCore (centralizer (X : Set G)) := by
    intro y
    have h1 := hqapp (y : centralizerPerfectCore X)
    rw [MonoidHom.mem_ker.1 y.2] at h1
    exact (QuotientGroup.eq_one_iff _).1 h1.symm
  let φ : qh.ker →* oddCore (centralizer (X : Set G)) :=
    ((Subgroup.inclusion hle).comp qh.ker.subtype).codRestrict _ hmemO
  have hφinj : Function.Injective φ := fun a b hab =>
    Subtype.ext (Subtype.ext (congrArg
      (fun z : oddCore (centralizer (X : Set G)) => ((z : centralizer (X : Set G)) : G)) hab))
  have hkodd : Odd (Nat.card qh.ker) :=
    Odd.of_dvd_nat CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_odd
      (Subgroup.card_dvd_of_injective φ hφinj)
  let η : centralizerPerfectCore X →* StatedSp m F' := eK.toMonoidHom.comp qh
  have hηs : Function.Surjective η := eK.surjective.comp hqs
  have hker : η.ker = qh.ker := by
    ext y
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff]
  have hEperf : Group.IsPerfect (centralizerPerfectCore X) :=
    isPerfect_iff.mpr (F4Pilot.commutator_centralizerPerfectCore X)
  have hinj := F4Pilot.oddSchurTrivial_statedSp m F' (centralizerPerfectCore X) hEperf η hηs
    (hker ▸ hqker) (hker ▸ hkodd)
  refine ⟨F', inferInstance, inferInstance, inferInstance, hF',
    ⟨(MulEquiv.ofBijective η ⟨hinj, hηs⟩).symm⟩, ?_⟩
  have hθ : ∀ y : centralizerPerfectCore X,
      qh ((centralizerPerfectCore X).normalizerMonoidHom ⟨t, hN⟩ y) =
        Kb.normalizerMonoidHom ⟨_, hsN⟩ (qh y) := by
    intro y
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, hqapp, hqapp]
    have e1 : (⟨(((centralizerPerfectCore X).normalizerMonoidHom ⟨t, hN⟩ y :
        centralizerPerfectCore X) : G), hle ((centralizerPerfectCore X).normalizerMonoidHom
          ⟨t, hN⟩ y).2⟩ : centralizer (X : Set G)) =
        ⟨t, htX⟩ * ⟨(y : G), hle y.2⟩ * ⟨t, htX⟩⁻¹ := by
      apply Subtype.ext
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      rfl
    rw [e1, map_mul, map_mul, map_inv]
  rintro ⟨z, hz⟩
  apply hov.1
  refine ⟨qh z, MulEquiv.ext fun w => ?_⟩
  obtain ⟨y, rfl⟩ := hqs w
  rw [MulAut.conj_apply, ← hθ y, ← hz, MulAut.conj_apply, map_mul, map_mul, map_inv]

end Lift


section Param


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]

theorem nonempty_fieldNeighbourParam_of_rootKindSp {m f : ℕ} (hset : SeitzSetting G L)
    (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (hm : 2 ≤ m) (e : L ≃* StatedSp (m + 1) K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) (k : Fin (m + 1)) {F : Type}
    [Field F] [Finite F] (ι : K →+* F) {σ : F ≃+* F} (hσ : orderOf σ = 2)
    (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι) (h : RootKindSp e t f k .field) :
    Nonempty (FieldNeighbourParam e t ι σ k) := by
  have : Finite K := LinearPilot.finite_of_card_eq_two_pow hKc
  have : CharP K 2 := LinearPilot.charP_two_of_card_eq_two_pow hKc
  have : CharP F 2 := charP_of_injective_ringHom ι.injective 2
  have hq : 4 ≤ Nat.card K := hKc ▸ four_le_two_pow hf
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have hFc : Nat.card F = 2 ^ (2 * f) := natCard_eq_two_pow_two_mul_of_fix ι hKc hσ hfix
  have hN : t ∈ normalizer (neighbourCore e k : Set G) := le_normalizer_neighbourCore e htC k
  obtain ⟨F', _, _, _, hF', ⟨ψ₀⟩, hθout⟩ :=
    exists_centralizerPerfectCore_mulEquiv_of_field hset hKc hf hm e htC ht k rfl rfl h hN
  have : Fintype F := Fintype.ofFinite F
  have : Fintype F' := Fintype.ofFinite F'
  have hcc : Fintype.card F = Fintype.card F' := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hFc, hF']
  let ψ : StatedSp m F ≃* neighbourCore e k :=
    (F4Pilot.statedSpCongr (FiniteField.ringEquivOfCardEq hcc) m).trans ψ₀
  have hθθ : (neighbourCore e k).normalizerMonoidHom ⟨t, hN⟩ *
      (neighbourCore e k).normalizerMonoidHom ⟨t, hN⟩ = 1 := by
    rw [← map_mul, show (⟨t, hN⟩ : normalizer (neighbourCore e k : Set G)) * ⟨t, hN⟩ = 1 from
      Subtype.ext htt, map_one]
  have hD : modelToG e (complSp K k) ≤ neighbourCore e k :=
    modelToG_complSp_le_neighbourCore e hq (by omega) k
  let ε₀ : StatedSp m K →* G := L.subtype.comp (e.symm.toMonoidHom.comp
    ((complSp K k).subtype.comp (complSpEquiv k).toMonoidHom))
  have hε₀M : ∀ g, ε₀ g ∈ neighbourCore e k := fun g =>
    hD (symm_mem_modelToG e (complSpEquiv k g).2)
  let ε : StatedSp m K →* neighbourCore e k := ε₀.codRestrict _ hε₀M
  have hεapp : ∀ g, ((ε g : neighbourCore e k) : G) =
      ((e.symm (complSpEquiv k g : StatedSp (m + 1) K) : L) : G) := fun g => rfl
  have hεinj : Function.Injective ε := by
    intro g₁ g₂ h12
    apply (complSpEquiv (K := K) k).injective
    apply Subtype.ext
    apply e.symm.injective
    apply Subtype.ext
    have := congrArg (fun z : neighbourCore e k => (z : G)) h12
    simpa only [hεapp] using this
  have hεrange : ε.range.map (neighbourCore e k).subtype = modelToG e (complSp K k) := by
    ext g
    constructor
    · rintro ⟨_, ⟨g', rfl⟩, rfl⟩
      exact symm_mem_modelToG e (complSpEquiv k g').2
    · intro hg
      obtain ⟨x, hx, rfl⟩ := (UnitaryPilot.mem_modelToG e).1 hg
      obtain ⟨g', hg'⟩ := (complSpEquiv (K := K) k).surjective ⟨x, hx⟩
      refine ⟨ε g', ⟨g', rfl⟩, ?_⟩
      change ((ε g' : neighbourCore e k) : G) = _
      rw [hεapp, hg']
  have hεr : ε.range = perfectCore (MonoidHom.eqLocus
      ((neighbourCore e k).normalizerMonoidHom ⟨t, hN⟩).toMonoidHom (MonoidHom.id _)) := by
    apply map_injective (neighbourCore e k).subtype_injective
    rw [CFSG.Quasithin.map_perfectCore, map_eqLocus_normalizerMonoidHom_eq hN,
      perfectCore_neighbourCore_inf_centralizer_eq hset hKc hf hm e htC ht k, hεrange]
  obtain ⟨ψ', hψ'ι, hψ'σ⟩ :=
    exists_mulEquiv_statedSpMap_eq_comm_of_two_le hm hq ι hσ hfix ψ hθθ hθout ε hεinj hεr
  let Φ : spBlock F ({k}ᶜ : Finset (Fin (m + 1))) →* G :=
    (neighbourCore e k).subtype.comp (ψ'.toMonoidHom.comp (blockComplEquiv F k).toMonoidHom)
  have hΦapp : ∀ y, Φ y = ((ψ' (blockComplEquiv F k y) : neighbourCore e k) : G) := fun y => rfl
  have hΦinj : Function.Injective Φ :=
    Subtype.val_injective.comp (ψ'.injective.comp (blockComplEquiv F k).injective)
  refine ⟨FieldNeighbourParam.ofNormalized Φ ?_ ?_ ?_ ?_⟩
  ·
    have hs : Function.Surjective (ψ'.toMonoidHom.comp (blockComplEquiv F k).toMonoidHom) :=
      ψ'.surjective.comp (blockComplEquiv F k).surjective
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 hs, ← MonoidHom.range_eq_map,
      range_subtype]
  ·
    rw [(MonoidHom.ker_eq_bot_iff Φ).2 hΦinj]
    exact bot_le
  ·
    intro x hx
    rw [hΦapp, blockComplEquiv_spFieldMap ι k hx, hψ'ι, hεapp,
      coe_complSpEquiv_blockComplEquiv]
  ·
    intro y
    rw [hΦapp, hΦapp, blockComplEquiv_fieldBlockSp, ← hψ'σ]
    rfl

end Param

end CFSG.SeitzReduction.SymplecticPilot
