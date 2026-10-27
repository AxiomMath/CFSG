module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotSwapBLiftSchur
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainRows
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainHR8Y
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCTSwapNormalize
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotBLiftF4

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
open CFSG.Quasithin (perfectCore)

section Subtype

variable {G : Type*} [Group G] {H : Subgroup G}

theorem map_subtype_map_conj (A : Subgroup H) (h : H) :
    (A.map (MulAut.conj h).toMonoidHom).map H.subtype =
      (A.map H.subtype).map (MulAut.conj (h : G)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem subgroupOf_map_subtype_self {C : Subgroup G} (A : Subgroup C) :
    (A.map C.subtype).subgroupOf C = A :=
  Subgroup.comap_map_eq_self_of_injective C.subtype_injective A

end Subtype

section Levi

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K]

theorem modelToG_map_subtype_levi (e : L ≃* adjointGroup .F4 K) (N : AmalgamNeighbour) :
    modelToG e ((N.levi K).map (adjointGroup .F4 K).subtype) = neighbourLeviG e N := by
  unfold modelToG neighbourLeviG
  rw [subgroupOf_map_subtype_self]

end Levi

section X

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]

theorem exists_swapDecomposition_X {t : G} {f : ℕ} (hw : F4Work L K t f) (hf : 2 ≤ f)
    (e : L ≃* adjointGroup .F4 K) (hX : HR8Kind e t f .X .swap) :
    ∃ Kc : Subgroup G, Kc.map (MulAut.conj t).toMonoidHom ≤ centralizer (Kc : Set G) ∧
      Kc ⊓ Kc.map (MulAut.conj t).toMonoidHom = ⊥ ∧
      Kc ⊔ Kc.map (MulAut.conj t).toMonoidHom = neighbourCore e .X ∧
      neighbourCore e .X ⊓ centralizer ({t} : Set G) =
        modelToG e ((AmalgamNeighbour.X.levi K).map (adjointGroup .F4 K).subtype) := by
  have := finite_of_natCard_eq_two_pow hw.card_eq
  have := charP_two_of_natCard_eq_two_pow hw.card_eq
  have hq : 4 ≤ Nat.card K := by
    rw [hw.card_eq]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have htC := hw.mem_centralizer
  have htt : t * t = 1 := by rw [← sq, ← hw.orderOf_eq, pow_orderOf_eq_one]
  set X : Subgroup G := neighbourTorusG e .X with hXdef
  set H : Subgroup G := centralizer (X : Set G) with hHdef
  set D : Subgroup G := neighbourLeviG e .X with hDdef
  obtain ⟨htX, Kb, hKb, hDK, hcase⟩ := hX
  have hswap : Kb.map (MulAut.conj (QuotientGroup.mk' (oddCore H) ⟨t, htX⟩)).toMonoidHom ≠ Kb ∧
      ⁅Kb, Kb.map (MulAut.conj (QuotientGroup.mk' (oddCore H) ⟨t, htX⟩)).toMonoidHom⁆ = ⊥ ∧
      Nonempty (Kb ⧸ center Kb ≃*
        ((D.subgroupOf H).map (QuotientGroup.mk' (oddCore H)) : Subgroup (H ⧸ oddCore H))) := by
    rcases hcase with ⟨hκ, -⟩ | ⟨-, h⟩
    · exact absurd rfl hκ
    · exact h
  obtain ⟨hne, hcomm, ⟨eK⟩⟩ := hswap
  set π := QuotientGroup.mk' (oddCore H) with hπ
  set Db : Subgroup (H ⧸ oddCore H) := (D.subgroupOf H).map π with hDbdef
  set t' : H := ⟨t, htX⟩ with ht'def
  have ht't' : t' * t' = 1 := Subtype.ext htt
  obtain ⟨-, hsyl, -⟩ := neighbour_standard_torusLineR hw.standard.standard htC hw.orderOf_eq
    hw.inf_eq hf hw.card_eq e (X := X) rfl htX (D := D) rfl
  have hDH : D ≤ H := map_map_symm_le_centralizer e torusLineR_subgroupOf_le_centralizer
  have hDL : D ≤ L := map_subtype_le _
  have hDt : D ≤ centralizer ({t} : Set G) := fun d hd =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htC d (hDL hd))
  have hτD : π t' ∈ centralizer (Db : Set (H ⧸ oddCore H)) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨d, hd, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.1 (hDt (mem_subgroupOf.1 hd)))
  have hdata : SwapComponentData (π t') Kb Db :=
    ⟨by rw [← map_mul, ht't', map_one], hKb, hne, hcomm, hDK, hτD, hsyl⟩
  have hO := oddCore_quotient_oddCore_eq_bot_of_finite (H := H)
  have hTodd : Odd (Nat.card ((torusLineR K).subgroupOf (adjointGroup .F4 K))) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe torusLineR_le_adjointGroup).toEquiv]
    exact odd_card_torusLineR hw.one_le hw.card_eq
  have hC := mem_center_of_mem_oddCore_of_commute_sup hw.card_eq hw.standard.standard htC
    hw.orderOf_eq hw.inf_eq e (centralizer_torusLineR_eq hq) torusLineR_subgroupOf_le_centralizer
    torusLineR_subgroupOf_le_centralizer_self hTodd le_rfl (X := X) rfl htX (D := D) rfl
  have hZ : center Kb = ⊥ := hdata.center_eq_bot hO
  let eKD : Kb ≃* Db :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans eK
  let eD : C3Levi K ≃* D :=
    ((C3Levi K).equivMapOfInjective e.symm.toMonoidHom e.symm.injective).trans
      (((C3Levi K).map e.symm.toMonoidHom).equivMapOfInjective L.subtype L.subtype_injective)
  let eD' : C3Levi K ≃* D.subgroupOf H := eD.trans (subgroupOfEquivOfLe hDH).symm
  have hD'q : CFSG.Open.IsQuasisimple (D.subgroupOf H) :=
    isQuasisimple_open_of_mulEquiv eD' isQuasisimple_open_C3Levi
  have hD'Z : center (D.subgroupOf H) = ⊥ := center_eq_bot_congr eD' center_C3Levi_eq_bot
  let eDb : D.subgroupOf H ≃* Db :=
    mapMkEquivOfInfEqBot (oddCore H) (D.subgroupOf H) (inf_oddCore_eq_bot hD'q hD'Z)
  let eKC : Kb ≃* C3Levi K := eKD.trans (eDb.symm.trans eD'.symm)
  have hOut := (CFSG.LocalAnalysis.ComponentInitial.outer_isomorphism eKC).2.2
    (isSolvable_outer_C3Levi hw.card_eq)
  have hSchur : OddSchurTrivial Kb :=
    (oddSchurTrivial_statedSp 3 K).of_mulEquiv ((c3LeviEquiv K).trans eKC.symm)
  obtain ⟨hcH, hdH, hsH, -, -, hcardH⟩ := swapLift_decomposition ht't' hC hdata hOut hSchur
  set Kh := oddCoreLift Kb with hKhdef
  have hKct : (Kh.map H.subtype).map (MulAut.conj t).toMonoidHom =
      (Kh.map (MulAut.conj t').toMonoidHom).map H.subtype :=
    (map_subtype_map_conj Kh t').symm
  have hc1 : (Kh.map H.subtype).map (MulAut.conj t).toMonoidHom ≤
      centralizer ((Kh.map H.subtype : Subgroup G) : Set G) := by
    rw [hKct]
    exact map_le_centralizer_map H.subtype hcH
  have hd1 : Kh.map H.subtype ⊓ (Kh.map H.subtype).map (MulAut.conj t).toMonoidHom = ⊥ := by
    rw [hKct, ← Subgroup.map_inf_eq _ _ _ H.subtype_injective, hdH, Subgroup.map_bot]
  have he1 : Kh.map H.subtype ⊔ (Kh.map H.subtype).map (MulAut.conj t).toMonoidHom =
      neighbourCore e .X := by
    rw [hKct, ← Subgroup.map_sup, hsH, CFSG.Quasithin.map_perfectCore, ← MonoidHom.range_eq_map,
      range_subtype]
    rfl
  refine ⟨Kh.map H.subtype, hc1, hd1, he1, ?_⟩
  rw [modelToG_map_subtype_levi]
  have hDeq : D = ((C3Levi K).map e.symm.toMonoidHom).map L.subtype := rfl
  have hDperf : ⁅D, D⁆ = D := by
    have hCp : ⁅C3Levi K, C3Levi K⁆ = C3Levi K := isPerfect_iff.mp isQuasisimple_C3Levi.1
    rw [hDeq, ← map_commutator, ← map_commutator, hCp]
  have hDE : D ≤ neighbourCore e .X := by
    have h1 := modelToG_le_neighbourCore e (levi_le_centralizer_torus (K := K) .X)
      (by rw [modelToG_map_subtype_levi]; exact hDperf)
    rwa [modelToG_map_subtype_levi] at h1
  have hrange := range_swapDiagHom hc1 htt hd1
  rw [he1] at hrange
  have hinj := swapDiagHom_injective hc1 hd1
  have hcard : Nat.card (neighbourCore e .X ⊓ centralizer ({t} : Set G) : Subgroup G) ≤
      Nat.card D := by
    rw [← hrange, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm,
      card_map_of_injective H.subtype_injective, hcardH,
      Nat.card_congr ((eKD.trans eDb.symm).trans (subgroupOfEquivOfLe hDH)).toEquiv]
  exact (Subgroup.eq_of_le_of_card_ge (le_inf hDE hDt) hcard).symm

end X

section Y

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K CFSG.LieType.Ree.ReeTag.F4.prime]

theorem neighbourTorusG_Y_eq_X (e : L ≃* adjointGroup .F4 K) :
    neighbourTorusG e .Y = neighbourTorusG (e.trans (graphAutF4 K).symm) .X :=
  neighbourTorusG_Y_eq e

theorem neighbourLeviG_Y_eq_X (e : L ≃* adjointGroup .F4 K) :
    neighbourLeviG e .Y = neighbourLeviG (e.trans (graphAutF4 K).symm) .X :=
  neighbourLeviG_Y_eq e

theorem hr8Kind_Y_iff_X (e : L ≃* adjointGroup .F4 K) {t : G} {f : ℕ} {κ : Sp6Kind} :
    HR8Kind e t f .Y κ ↔ HR8Kind (e.trans (graphAutF4 K).symm) t f .X κ := by
  have key : ∀ X₁ X₂ D₁ D₂ : Subgroup G, X₁ = X₂ → D₁ = D₂ →
      ((∃ htX : t ∈ centralizer (X₁ : Set G),
        NeighbourOvergroupKind (QuotientGroup.mk' (oddCore (centralizer (X₁ : Set G))) ⟨t, htX⟩)
          ((D₁.subgroupOf (centralizer (X₁ : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (X₁ : Set G))))) f κ) ↔
       (∃ htX : t ∈ centralizer (X₂ : Set G),
        NeighbourOvergroupKind (QuotientGroup.mk' (oddCore (centralizer (X₂ : Set G))) ⟨t, htX⟩)
          ((D₂.subgroupOf (centralizer (X₂ : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (X₂ : Set G))))) f κ)) := by
    rintro X₁ X₂ D₁ D₂ rfl rfl
    exact Iff.rfl
  exact key _ _ _ _ (neighbourTorusG_Y_eq_X e) (neighbourLeviG_Y_eq_X e)

theorem neighbourCore_Y_eq_X (e : L ≃* adjointGroup .F4 K) :
    neighbourCore e .Y = neighbourCore (e.trans (graphAutF4 K).symm) .X := by
  change centralizerPerfectCore (neighbourTorusG e .Y) =
    centralizerPerfectCore (neighbourTorusG (e.trans (graphAutF4 K).symm) .X)
  rw [neighbourTorusG_Y_eq_X]

theorem modelToG_levi_Y_eq_X (e : L ≃* adjointGroup .F4 K) :
    modelToG e ((AmalgamNeighbour.Y.levi K).map (adjointGroup .F4 K).subtype) =
      modelToG (e.trans (graphAutF4 K).symm)
        ((AmalgamNeighbour.X.levi K).map (adjointGroup .F4 K).subtype) := by
  rw [modelToG_map_subtype_levi, modelToG_map_subtype_levi, neighbourLeviG_Y_eq_X]

end Y

section Rows

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]

theorem exists_swapDecomposition_Y {t : G} {f : ℕ} (hw : F4Work L K t f) (hf : 2 ≤ f)
    (e : L ≃* adjointGroup .F4 K) (hY : HR8Kind e t f .Y .swap) :
    ∃ Kc : Subgroup G, Kc.map (MulAut.conj t).toMonoidHom ≤ centralizer (Kc : Set G) ∧
      Kc ⊓ Kc.map (MulAut.conj t).toMonoidHom = ⊥ ∧
      Kc ⊔ Kc.map (MulAut.conj t).toMonoidHom = neighbourCore e .Y ∧
      neighbourCore e .Y ⊓ centralizer ({t} : Set G) =
        modelToG e ((AmalgamNeighbour.Y.levi K).map (adjointGroup .F4 K).subtype) := by
  have := finite_of_natCard_eq_two_pow hw.card_eq
  have : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := charP_two_of_natCard_eq_two_pow hw.card_eq
  rw [neighbourCore_Y_eq_X, modelToG_levi_Y_eq_X]
  exact exists_swapDecomposition_X hw hf _ ((hr8Kind_Y_iff_X e).1 hY)

theorem exists_swapDecomposition {t : G} {f : ℕ} (hw : F4Work L K t f) (hf : 2 ≤ f)
    (e : L ≃* adjointGroup .F4 K) {N : AmalgamNeighbour} (hN : N ≠ .X')
    (h : HR8Kind e t f N .swap) :
    ∃ Kc : Subgroup G, Kc.map (MulAut.conj t).toMonoidHom ≤ centralizer (Kc : Set G) ∧
      Kc ⊓ Kc.map (MulAut.conj t).toMonoidHom = ⊥ ∧
      Kc ⊔ Kc.map (MulAut.conj t).toMonoidHom = neighbourCore e N ∧
      neighbourCore e N ⊓ centralizer ({t} : Set G) =
        modelToG e ((N.levi K).map (adjointGroup .F4 K).subtype) := by
  cases N
  · exact exists_swapDecomposition_X hw hf e h
  · exact exists_swapDecomposition_Y hw hf e h
  · exact absurd rfl hN

theorem swapRowCTInput_holds : SwapRowCTInput := by
  intro G _ _ L K _ _ _ e t f hw hf hX hY
  have htt : t * t = 1 := by rw [← sq, ← hw.orderOf_eq, pow_orderOf_eq_one]
  have hq : 4 ≤ Nat.card K := by
    rw [hw.card_eq]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨KX, hcX, hdX, hEX, hfX⟩ := exists_swapDecomposition_X hw hf e hX
  obtain ⟨KY, hcY, hdY, hEY, hfY⟩ := exists_swapDecomposition_Y hw hf e hY
  obtain ⟨G₁, G₂, ε, h₁₂, hG₂, hsup, -⟩ := exists_swapFactors_of_decomposition hw.mem_centralizer
    htt hq hcX hdX hEX hfX hcY hdY hEY hfY
  refine ⟨G₁, ⟨ε⟩, hG₂ ▸ h₁₂, ?_⟩
  rw [hG₂]
  exact hsup

end Rows

end CFSG.SeitzReduction.F4Pilot
