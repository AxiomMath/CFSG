module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightSwapCommConj
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightSwapCommOrth
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightDich
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightDichOrth
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightOrthPlusStepA

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (plusIndexEquiv coordinateQuadPlus regular_coordinateQuadPlus)
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)
open CFSG.SeitzReduction.LinearPilot (SLmCatalogueClausesAt)
open scoped MatrixGroups

section Model

theorem map_toMonoidHom_trans {M : Type*} [Group M] (H : Subgroup M) (φ ψ : MulAut M) :
    H.map (φ.trans ψ).toMonoidHom = (H.map φ.toMonoidHom).map ψ.toMonoidHom := by
  rw [Subgroup.map_map]
  rfl

theorem map_le_centralizer_of_le_centralizer {M N : Type*} [Group M] [Group N] {H₁ H₂ : Subgroup M}
    (h : H₁ ≤ centralizer (H₂ : Set M)) (f : M →* N) :
    H₁.map f ≤ centralizer (H₂.map f : Set N) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨y, hy, rfl⟩
  rw [← map_mul, ← map_mul, mem_centralizer_iff.mp (h hx) y hy]

theorem exists_planePerm_four {a b c d : Fin 4} (hab : a ≠ b) (hcd : c ≠ d) (hca : c ≠ a)
    (hcb : c ≠ b) (hda : d ≠ a) (hdb : d ≠ b) :
    ∃ π : Equiv.Perm (Fin 4), π 0 = c ∧ π 1 = d ∧ π 2 = a ∧ π 3 = b := by
  have hinj : Function.Injective ![c, d, a, b] := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  exact ⟨Equiv.ofBijective _ (Finite.injective_iff_bijective.mp hinj), rfl, rfl, rfl, rfl⟩

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
theorem leviFixBar_zero_one_le_stabTwoBar_two_three :
    leviFixBar (plusPair K 0) (plusPair K 1) ≤ stabTwoBar K 2 3 :=
  leviFixBar_le_stabTwoBar_of_orth (plusPair_orth (by decide)) (plusPair_orth (by decide))
    (plusPair_orth (by decide)) (plusPair_orth (by decide))

omit [Finite K] [CharP K 2] in
theorem plusA_le_stabTwoBar_two_three : plusA K ≤ stabTwoBar K 2 3 :=
  leviFixBar_le_stabTwoBar_of_orth (plusPair_orth (by decide)) (plusPair_orth_flip (by decide))
    (plusPair_orth (by decide)) (plusPair_orth_flip (by decide))

theorem stabTwoBar_two_three_le_sup (hq : 4 ≤ Nat.card K) :
    stabTwoBar K 2 3 ≤ leviFixBar (plusPair K 0) (plusPair K 1) ⊔ plusA K := by
  intro x hx
  obtain ⟨y, hy, z, hz, rfl⟩ := exists_mul_of_mem_stabTwoBar hq (i := 2) (j := 3) (k := 0)
    (l := 1) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx
  exact mul_mem (mem_sup_left hy) (mem_sup_right hz)

theorem isSimpleGroup_leviFixBar_zero_one (hq : 4 ≤ Nat.card K) :
    IsSimpleGroup (leviFixBar (plusPair K 0) (plusPair K 1)) := by
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadPlus 4 K (by norm_num)
  have hQ' := (isHypCoord_coordinateQuadPlus (K := K) (n := 4) 0).exists_ne_zero
  have : IsSimpleGroup SL(2, K) := LinearPilot.isSimpleGroup_specialLinearGroup_two hq
  exact (leviFixBarEquiv (plusPair_orth (by decide)) hQ hT hQ').isSimpleGroup

theorem plusZ_ne_one : plusZ K ≠ 1 :=
  rootPairElt_ne_one (regular_coordinateQuadPlus 4 K (by norm_num)).1
    (plusPair_orth_flip (K := K) (show (0 : Fin 4) ≠ 1 by decide))
    (plusPair_orth (show (0 : Fin 4) ≠ 2 by decide))
    (orth_flipPair_left (plusPair_orth (show (1 : Fin 4) ≠ 2 by decide)))

theorem exists_mem_leviFixBar_mul_ne_plusZ :
    ∃ w ∈ leviFixBar (plusPair K 0) (plusPair K 1), plusZ K * w ≠ w * plusZ K := by
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadPlus 4 K (by norm_num)
  have hQ' := (isHypCoord_coordinateQuadPlus (K := K) (n := 4) 0).exists_ne_zero
  by_contra hcon
  have hc : ∀ w ∈ leviFixBar (plusPair K 0) (plusPair K 1), plusZ K * w = w * plusZ K := by
    intro w hw
    by_contra hne
    exact hcon ⟨w, hw, hne⟩
  set ε := leviFixBarEquiv (plusPair_orth (K := K) (show (0 : Fin 4) ≠ 1 by decide)) hQ hT hQ'
    with hε
  have hcen : (⟨plusZ K, plusZ_mem_leviFixBar⟩ : leviFixBar (plusPair K 0) (plusPair K 1)) ∈
      center (leviFixBar (plusPair K 0) (plusPair K 1)) := by
    rw [mem_center_iff]
    intro w
    exact Subtype.ext (hc w w.2).symm
  have h1 : ε ⟨plusZ K, plusZ_mem_leviFixBar⟩ ∈ center SL(2, K) := by
    rw [mem_center_iff]
    intro y
    obtain ⟨y', rfl⟩ := ε.surjective y
    rw [← map_mul, ← map_mul, (mem_center_iff.mp hcen) y']
  rw [center_SL2_eq_bot_of_charTwo, mem_bot] at h1
  have h2 : (⟨plusZ K, plusZ_mem_leviFixBar⟩ : leviFixBar (plusPair K 0) (plusPair K 1)) = 1 :=
    ε.injective (by rw [h1, map_one])
  exact plusZ_ne_one (congrArg Subtype.val h2)

end Model

section Comm

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}
variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem centralizerPerfectCore_le_centralizer_stabTwoBar_swap (hset : SeitzSetting G L) {f : ℕ}
    (hKc : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus 4 K)) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hR5 : ∃ x : G, ∃ z ∈ L ⊓ CFSG.conjugate L x, x⁻¹ * t * x = t * z ∧
      (∃ hz : z ∈ L, IsLongRoot (coordinateQuadPlus 4 K) (e ⟨z, hz⟩)) ∧
      (∃ hz : z ∈ CFSG.conjugate L x,
        IsLongRoot (coordinateQuadPlus 4 K) (((conjugateMulEquiv L x).symm.trans e) ⟨z, hz⟩)))
    {a b c d : Fin 4} (hab : a ≠ b) (hcd : c ≠ d) (hca : c ≠ a) (hcb : c ≠ b) (hda : d ≠ a)
    (hdb : d ≠ b)
    (hrow : OmegaRowAt t (modelToG e (pairTorus (K := K) a)) (modelToG e (pairPerp (K := K) a))
      .swap) :
    centralizerPerfectCore (modelToG e (pairTorus (K := K) a) ⊔
        modelToG e (pairTorus (K := K) b)) ≤
      centralizer (modelToG e (stabTwoBar K c d) : Set G) := by
  have htC := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadPlus 4 K (by norm_num)
  have hQ' : ∃ v, coordinateQuadPlus 4 K v ≠ 0 :=
    (isHypCoord_coordinateQuadPlus (K := K) (n := 4) 0).exists_ne_zero
  have h01 : (plusPair K 0).Orth (plusPair K 1) := plusPair_orth (by decide)
  obtain ⟨P, hinj, hrange⟩ := exists_swapParam_pairTorus_four_of_row hset hKc hq a e htC ht hrow
  obtain ⟨π, hπ0, hπ1, hπ2, hπ3⟩ := exists_planePerm_four hab hcd hca hcb hda hdb
  obtain ⟨δm, hRm, hOm⟩ : ∃ δm : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)),
      (stabTwoBar K 0 1).map δm.toMonoidHom = stabTwoBar K c d ∧
        (stabTwoBar K 2 3).map δm.toMonoidHom = stabTwoBar K a b :=
    ⟨conjProj hQ' (planePermLin_mem_orthogonalGroup (K := K) π),
      by rw [map_conjProj_planePermLin_stabTwoBar, hπ0, hπ1],
      by rw [map_conjProj_planePermLin_stabTwoBar, hπ2, hπ3]⟩
  obtain ⟨φ, hφR, hφO, hφJ⟩ : ∃ φ : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)),
      (stabTwoBar K 0 1).map φ.toMonoidHom = stabTwoBar K 0 1 ∧
        (stabTwoBar K 2 3).map φ.toMonoidHom = stabTwoBar K 2 3 ∧
        (leviFixBar (plusPair K 0) (plusPair K 1)).map φ.toMonoidHom = plusA K :=
    ⟨conjProj hQ' (plusFlipLin_mem_orthogonalGroup (K := K) (n := 4) 1),
      map_conjProj_plusFlipLin_stabTwoBar hQ' 1 0 1,
      map_conjProj_plusFlipLin_stabTwoBar hQ' 1 2 3, map_conjProj_plusFlipLin_leviFixBar hQ'⟩
  obtain ⟨δ, hδf, hδt⟩ : ∃ δ : Bool → MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)),
      δ false = δm ∧ δ true = φ.trans δm := ⟨fun i => cond i (φ.trans δm) δm, rfl, rfl⟩
  have hR : ∀ i, (stabTwoBar K 0 1).map (δ i).toMonoidHom = stabTwoBar K c d := by
    intro i
    cases i
    · rw [hδf, hRm]
    · rw [hδt, map_toMonoidHom_trans, hφR, hRm]
  have hO : ∀ i, (stabTwoBar K 2 3).map (δ i).toMonoidHom = stabTwoBar K a b := by
    intro i
    cases i
    · rw [hδf, hOm]
    · rw [hδt, map_toMonoidHom_trans, hφO, hOm]
  obtain ⟨l, hl⟩ := exists_units_ne_one (K := K) (by omega : 3 ≤ Nat.card K)
  obtain ⟨y₀, hyA, hy1, hyo⟩ : ∃ y₀ : matrixProjectiveDerived (coordinateQuadPlus 4 K),
      y₀ ∈ plusA K ∧ y₀ ≠ 1 ∧ Odd (orderOf y₀) := ⟨_, orthTorusElt_mem_plusA (K := K) hl⟩
  have huJ : ∀ i, ((e.symm (δ i (plusZ K)) : L) : G) ∈
      modelToG e ((leviFixBar (plusPair K 0) (plusPair K 1)).map (δ i).toMonoidHom) := fun i =>
    UnitaryPilot.symm_mem_modelToG e ⟨plusZ K, plusZ_mem_leviFixBar, rfl⟩
  have hOeq : perfectCore (modelToG e (pairPerp (K := K) a) ⊓
      centralizer (modelToG e (pairTorus (K := K) b) : Set G)) =
        modelToG e (stabTwoBar K a b) := by
    rw [perfectCore_modelToG_inf_centralizer]
    exact congrArg (modelToG e) (plusOverlap_eq_stabTwoBar_four hq hab)
  refine centralizerPerfectCore_sup_le_centralizer_of_twist P hinj hrange
    (UnitaryPilot.modelToG_mono e (pairTorus_le_pairPerp hab))
    (fun i => modelToG e ((leviFixBar (plusPair K 0) (plusPair K 1)).map (δ i).toMonoidHom))
    ?_ ?_ ?_ ?_ (fun i => ⟨_, huJ i⟩) ?_ ?_
    (fun i => modelToG e (zpowers (δ i y₀))) ?_ ?_ ?_ ?_
  ·
    intro i
    rw [hOeq]
    exact UnitaryPilot.modelToG_mono e
      ((map_mono leviFixBar_zero_one_le_stabTwoBar_two_three).trans (hO i).le)
  ·
    rw [hOeq, ← hOm]
    have h1 : (stabTwoBar K 2 3).map δm.toMonoidHom ≤
        (leviFixBar (plusPair K 0) (plusPair K 1)).map (δ false).toMonoidHom ⊔
          (leviFixBar (plusPair K 0) (plusPair K 1)).map (δ true).toMonoidHom := by
      refine (map_mono (stabTwoBar_two_three_le_sup hq)).trans ?_
      rw [Subgroup.map_sup, hδf, hδt, map_toMonoidHom_trans, hφJ]
    refine (UnitaryPilot.modelToG_mono e h1).trans ?_
    rw [UnitaryPilot.modelToG_sup]
    exact sup_le
      (le_iSup (fun i => modelToG e ((leviFixBar (plusPair K 0) (plusPair K 1)).map
        (δ i).toMonoidHom)) false)
      (le_iSup (fun i => modelToG e ((leviFixBar (plusPair K 0) (plusPair K 1)).map
        (δ i).toMonoidHom)) true)
  ·
    intro i
    have := isSimpleGroup_leviFixBar_zero_one (K := K) hq
    exact isSimpleGroup_modelToG e
      (((leviFixBar (plusPair K 0) (plusPair K 1)).equivMapOfInjective (δ i).toMonoidHom
        (δ i).injective).symm.isSimpleGroup)
  ·
    intro i
    exact UnitaryPilot.modelToG_perfect e
      (by rw [← map_commutator, commutator_leviFixBar_plus hq h01])
  ·
    intro i
    apply Subtype.ext
    change ((e.symm (δ i (plusZ K)) : L) : G) * ((e.symm (δ i (plusZ K)) : L) : G) = 1
    rw [← L.coe_mul, ← map_mul, ← map_mul, plusZ_mul_self, map_one, map_one, L.coe_one]
  ·
    intro i
    obtain ⟨w, hw, hwne⟩ := exists_mem_leviFixBar_mul_ne_plusZ (K := K)
    refine ⟨⟨((e.symm (δ i w) : L) : G), UnitaryPilot.symm_mem_modelToG e ⟨w, hw, rfl⟩⟩,
      fun h => hwne ?_⟩
    have h' := congrArg Subtype.val h
    change ((e.symm (δ i (plusZ K)) : L) : G) * ((e.symm (δ i w) : L) : G) =
      ((e.symm (δ i w) : L) : G) * ((e.symm (δ i (plusZ K)) : L) : G) at h'
    have h'' : e.symm (δ i (plusZ K * w)) = e.symm (δ i (w * plusZ K)) :=
      Subtype.ext (by simpa [map_mul] using h')
    exact (δ i).injective (e.symm.injective h'')
  ·
    intro i
    refine UnitaryPilot.modelToG_mono e ((zpowers_le).mpr ?_)
    have hmem : δ i y₀ ∈ stabTwoBar K a b := by
      rw [← hO i]
      exact ⟨y₀, plusA_le_stabTwoBar_two_three hyA, rfl⟩
    exact stabTwoBar_le_pairPerp a b hmem
  ·
    intro i
    refine UnitaryPilot.modelToG_le_centralizer e ?_
    rw [le_centralizer_iff, zpowers_le, mem_centralizer_iff]
    intro x hx
    have h1 := map_le_centralizer_of_le_centralizer (leviFixBar_le_centralizer_flip h01 hQ hT)
      (δ i).toMonoidHom
    exact (mem_centralizer_iff.mp (h1 hx) (δ i y₀) ⟨y₀, hyA, rfl⟩).symm
  ·
    intro i
    refine UnitaryPilot.modelToG_le_centralizer e ?_
    rw [← hR i]
    refine map_le_centralizer_of_le_centralizer
      (fun x hx => mem_centralizer_iff.mpr fun y hy => ?_) _
    exact (leviFixBar_commute_stabTwoBar_zero_one (Or.inl rfl) hx hy).symm
  ·
    intro i S hSperf hSsimple hSt hST huS
    obtain ⟨g, hg, hS⟩ := exists_conj_eq_mul_forall_le_centralizer_plus_four_aut hset hKc hq e ht
      hKt hR5 (δ i) hyA hy1 hyo
    rw [← hR i]
    refine hS S hSperf hSsimple (by rw [hg]; exact hSt) (hST.trans (centralizer_le ?_)) huS
    rw [Set.singleton_subset_iff]
    exact UnitaryPilot.symm_mem_modelToG e (mem_zpowers _)

theorem plusFourSwapCommInput_holds : PlusFourSwapCommInput := by
  intro G _ _ L hset f K _ _ _ hKc hf e t ht hKt hR5 hrow a b c d hab hcd hca hcb hda hdb
  have hq : 4 ≤ Nat.card K := (LinearPilot.four_le_card_iff_two_le hKc).2 hf
  obtain ⟨x, z, hz, hxz, h1, h2, -⟩ := hR5
  exact centralizerPerfectCore_le_centralizer_stabTwoBar_swap hset hKc hq e ht hKt
    ⟨x, z, hz, hxz, h1, h2⟩ hab hcd hca hcb hda hdb (hrow a)

end Comm

end CFSG.SeitzReduction.OmegaPilot
