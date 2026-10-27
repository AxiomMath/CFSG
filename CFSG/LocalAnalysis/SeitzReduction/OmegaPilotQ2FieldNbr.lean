module

public import CFSG.LocalAnalysis.SeitzReduction.SeitzQ2OddSplitClassical
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCoverExists
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2Minus
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2PlusNbrBridge
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2PlusNbrStd

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (coordinateQuadPlus coordinateQuadMinus)


section Generic

variable {G : Type} [Group G] [Finite G]

theorem nonempty_centralizerPerfectCore_mulEquiv_of_fieldRow {L : Subgroup G} {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hLt : centralizer ({t} : Set G) ≤ normalizer (L : Set G)) {X D : Subgroup G}
    (htX : t ∈ centralizer (X : Set G)) (hD : D = inSubgroup layer (L ⊓ centralizer (X : Set G)))
    (hDq : CFSG.IsQuasisimple D) (hZD : center D = ⊥)
    (hXo : ∀ c ∈ centralizer (X : Set G) ⊓ centralizer ({t} : Set G) ⊓ centralizer (D : Set G),
      Odd (orderOf c) → c ∈ X)
    (hsyl : ∀ U : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
      IsPGroup 2 U →
      U ≤ centralizer ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) :
        Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
      Nat.card U ≤ 2)
    (hcomp : CFSG.Open.IsComponentOf
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))))
        (centralizer ({QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩} :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))))))
    {m f : ℕ} (hm : 1 ≤ m) (hmf : (m, f) ≠ (4, 1)) {tag : StatedLieTag}
    (htag : tag = .POmegaPlus ∨ tag = .POmegaMinus) (hDm : LieModel D tag m 2 f)
    (hN : NeighbourOvergroupOmega (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
      ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) m f)
    (hrow : OmegaRowAt t X D .field) (F : Type) [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 2 ^ (2 * f)) :
    Nonempty (centralizerPerfectCore X ≃* matrixProjectiveDerived (coordinateQuadPlus m F)) := by
  set s := QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ with hs
  set Db := (D.subgroupOf (centralizer (X : Set G))).map
    (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) with hDb
  have ht' : orderOf (⟨t, htX⟩ : centralizer (X : Set G)) = 2 := by
    rw [orderOf_mk]
    exact ht
  have hs2' : orderOf s = 2 := orderOf_mk_oddCore ht'
  have hs2 : s ^ 2 = 1 := hs2' ▸ pow_orderOf_eq_one s
  have hDperf : ⁅Db, Db⁆ = Db := SymplecticPilot.commutator_eq_self_of_isQuasisimple hcomp.2.2
  have hD1 : Db ≠ ⊥ := ne_bot_of_isQuasisimple hcomp.2.2
  obtain ⟨Kc, hKc, hK⟩ := hN
  obtain ⟨r, hr, hrK⟩ := neighbourRowOmega_of_alternative hKc hK
  obtain ⟨htX', hrow'⟩ := hrow
  have hr1 : r = .field := NeighbourRowOmega.unique hs2 hDperf hD1 hr hrow'
  have hKt : Kc.map (MulAut.conj s).toMonoidHom = Kc := hrK.1 hr1
  have hDX : D ≤ centralizer (X : Set G) :=
    (hD ▸ map_subtype_le _ : D ≤ L ⊓ _).trans inf_le_right
  have hDm' := UnitaryPilot.lieModel_quotient_center_map_oddCore_of_isQuasisimple hDX hDq
    (LinearPilot.lieModel_quotient_center_of_center_eq_bot hZD hDm) hD1
  obtain ⟨hfield, -⟩ := hK.field (F4Pilot.pPrimeCore_two_quotient_oddCore_eq_bot _) hs2' hcomp
    hmf (omegaEvenTypeDetAt m) htag hDm' hKc
  obtain ⟨-, -, -, hmodel, -, q, hqs, hqker, hkodd, -⟩ :=
    neighbourCore_of_field htC ht hLt htX hD hDq hZD hXo hsyl hKc hfield hKt
  have hinj : Function.Injective q := by
    have : Group.IsPerfect (centralizerPerfectCore X) :=
      isPerfect_iff.mpr (F4Pilot.commutator_centralizerPerfectCore X)
    exact SeitzQ2.oddSchurTrivial_of_lieModel_POmegaPlus hmodel (centralizerPerfectCore X)
      this q hqs hqker.le hkodd
  obtain ⟨eK⟩ := nonempty_mulEquiv_statedOmegaPlus_of_lieModel hm hmodel F hF
  exact ⟨((MulEquiv.ofBijective q ⟨hinj, hqs⟩).trans eK).trans (statedOmegaPlusEquiv F m hm)⟩

end Generic

section Two

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem nonempty_centralizerPerfectCore_mulEquiv_anisoTorus_two (hset : SeitzSetting G L)
    {n : ℕ} (hn : 6 ≤ n) {K : Type} [Field K] [Finite K] [CharP K 2] (hK2 : Nat.card K = 2)
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c)) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hN : ∀ htX : t ∈ centralizer (modelToG e (anisoTorus (K := K) (by omega) b c) : Set G),
      NeighbourOvergroupOmega (QuotientGroup.mk' (oddCore (centralizer
          (modelToG e (anisoTorus (K := K) (by omega) b c) : Set G))) ⟨t, htX⟩)
        (((modelToG e (anisoPerp (K := K) (by omega) b c)).subgroupOf
            (centralizer (modelToG e (anisoTorus (K := K) (by omega) b c) : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer
            (modelToG e (anisoTorus (K := K) (by omega) b c) : Set G))))) (n - 1) 1)
    (hrow : OmegaRowAt t (modelToG e (anisoTorus (K := K) (by omega) b c))
      (modelToG e (anisoPerp (K := K) (by omega) b c)) .field)
    (F : Type) [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 4) :
    Nonempty (centralizerPerfectCore (modelToG e (anisoTorus (K := K) (by omega) b c)) ≃*
      matrixProjectiveDerived (coordinateQuadPlus (n - 1) F)) := by
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have hKc : Nat.card K = 2 ^ 1 := by rw [hK2, pow_one]
  obtain ⟨-, htX, -, -, -, -, -, hZ⟩ := neighbour_data_anisoTorus (by omega) hirr e htC rfl rfl
  obtain ⟨hLt, hD, hDq, hXo⟩ := bLift_inputs_anisoTorus hset.standardSetting.standard htC ht hKt
    (by omega) hirr e rfl rfl
  obtain ⟨hcomp, hsyl, -⟩ :=
    neighbour_standard_anisoTorus_of_seitzSetting hset hKc (by omega) hirr e htC ht rfl htX rfl
  obtain ⟨hLie, -⟩ := lieModel_map_anisoPerp hKc (by omega) hirr e rfl
  exact nonempty_centralizerPerfectCore_mulEquiv_of_fieldRow htC ht hLt htX hD hDq hZ hXo hsyl
    hcomp (by omega) (ne_four_one_of_six_le hn) (Or.inl rfl) hLie (hN htX) hrow F
    (by rw [hF]; norm_num)

theorem nonempty_centralizerPerfectCore_mulEquiv_plusAnisoTorus_two (hset : SeitzSetting G L)
    {m : ℕ} (hm : 4 ≤ m) {K : Type} [Field K] [Finite K] [CharP K 2] (hK2 : Nat.card K = 2)
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus (m + 2) K)) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hN : ∀ htX : t ∈ centralizer (modelToG (e.trans (plusAnisoProjEquiv m hirr).symm)
        (plusAnisoTorus m hirr) : Set G),
      NeighbourOvergroupOmega (QuotientGroup.mk' (oddCore (centralizer
          (modelToG (e.trans (plusAnisoProjEquiv m hirr).symm)
            (plusAnisoTorus m hirr) : Set G))) ⟨t, htX⟩)
        (((modelToG (e.trans (plusAnisoProjEquiv m hirr).symm)
            (plusAnisoPerp (K := K) m b c)).subgroupOf
            (centralizer (modelToG (e.trans (plusAnisoProjEquiv m hirr).symm)
              (plusAnisoTorus m hirr) : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer
            (modelToG (e.trans (plusAnisoProjEquiv m hirr).symm)
              (plusAnisoTorus m hirr) : Set G))))) (m + 1) 1)
    (hrow : OmegaRowAt t (modelToG (e.trans (plusAnisoProjEquiv m hirr).symm)
        (plusAnisoTorus m hirr))
      (modelToG (e.trans (plusAnisoProjEquiv m hirr).symm) (plusAnisoPerp (K := K) m b c)) .field)
    (F : Type) [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 4) :
    Nonempty (centralizerPerfectCore (modelToG (e.trans (plusAnisoProjEquiv m hirr).symm)
        (plusAnisoTorus m hirr)) ≃* matrixProjectiveDerived (coordinateQuadPlus (m + 1) F)) := by
  set e' := e.trans (plusAnisoProjEquiv m hirr).symm with he'
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have hKc : Nat.card K = 2 ^ 1 := by rw [hK2, pow_one]
  obtain ⟨-, htX, -, -, -, -, -, hZ⟩ := neighbour_data_plusAnisoTorus (by omega) hirr e' htC rfl rfl
  obtain ⟨hLt, hD, hDq, hXo⟩ := bLift_inputs_plusAnisoTorus hset.standardSetting.standard htC ht
    hKt (by omega) hirr e' rfl rfl
  obtain ⟨hcomp, hsyl, -⟩ := neighbour_standard_plusAnisoTorus hset.standardSetting.standard htC
    ht hKt (by omega) hirr e' rfl htX rfl
  obtain ⟨hLie, -⟩ := lieModel_map_plusAnisoPerp hKc (by omega) hirr e' rfl
  have hmf : (m + 1, 1) ≠ (4, 1) := by
    intro h
    have := congrArg Prod.fst h
    simp only at this
    omega
  exact nonempty_centralizerPerfectCore_mulEquiv_of_fieldRow htC ht hLt htX hD hDq hZ hXo hsyl
    hcomp (by omega) hmf (Or.inr rfl) hLie (hN htX) hrow F (by rw [hF]; norm_num)

end Two

end CFSG.SeitzReduction.OmegaPilot
