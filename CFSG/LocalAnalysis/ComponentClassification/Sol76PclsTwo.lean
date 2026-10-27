module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76PclsAlt
public import CFSG.LocalAnalysis.ComponentClassification.Sol76Hq4Sz8
public import CFSG.RankThree.PartTwo.Sec4.Census.DoubleCoverRanksG24
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.DSFactsModel

public section

namespace CFSG.ComponentClassification.Sol76T13.R12.Pcls

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Blueprint.Multiplier
  CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.CentralExt CFSG.RankThree.PartTwo.Sec4.Census

variable {Q : Type} [Group Q] [Finite Q]

theorem card_center_dvd_of_griessRow (hQ : IsQuasisimple Q) {t : StatedLieTag} {n p f : ℕ}
    (hrow : GriessAll.GriessRow (Q ⧸ center Q) t n p f) :
    Nat.card (center Q) ∣ (genericOrders t n p f).1 * (genericOrders t n p f).2 *
      ((exceptionalOrders t n p f).1 * (exceptionalOrders t n p f).2) := by
  obtain ⟨_, φ, hφ⟩ := Hq4.exists_hom_range_eq_center hQ hrow
  have hdvd := Subgroup.card_range_dvd φ
  rw [hφ] at hdvd
  have hm : ∀ k : ℕ, Nat.card (Multiplicative (ZMod k)) = k := fun k =>
    (Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod k) ≃ ZMod k)).trans
      (Nat.card_zmod k)
  rwa [Nat.card_prod, Nat.card_prod, Nat.card_prod, hm, hm, hm, hm] at hdvd

theorem two_dvd_of_griessRow (hQ : IsQuasisimple Q) {t : StatedLieTag} {n p f : ℕ}
    (hrow : GriessAll.GriessRow (Q ⧸ center Q) t n p f) {z : Q} (hzZ : z ∈ center Q)
    (hz2 : orderOf z = 2) :
    2 ∣ (genericOrders t n p f).1 * (genericOrders t n p f).2 *
      ((exceptionalOrders t n p f).1 * (exceptionalOrders t n p f).2) := by
  have h2 : 2 ∣ Nat.card (center Q) := by
    rw [← hz2, ← Subgroup.orderOf_mk z hzZ]
    exact orderOf_dvd_natCard _
  exact h2.trans (card_center_dvd_of_griessRow hQ hrow)

theorem three_le_pRank_of_lifts {X : Type*} [Group X] {φ : Q →* X}
    (hφ : Function.Surjective φ) (hker : φ.ker = center Q) {W : Subgroup X}
    (hW4 : 4 ≤ Nat.card W) (hcomm : ∀ y y' : Q, φ y ∈ W → φ y' ∈ W → y * y' = y' * y)
    (hsq : ∀ y : Q, φ y ∈ W → ∃ c : Q, φ c = 1 ∧ y ^ 2 = c ^ 2) {z : Q} (hzZ : z ∈ center Q)
    (hz2 : orderOf z = 2) : 3 ≤ CFSG.pRank 2 Q := by
  obtain ⟨A, hA, hcard⟩ := TransitiveLift.exists_isElementaryAbelian_card hφ hker.le hcomm hsq
  have hz1 : z ≠ 1 := by rintro rfl; rw [orderOf_one] at hz2; omega
  have hzk : φ z = 1 := by rw [← MonoidHom.mem_ker, hker]; exact hzZ
  have hz2' : z ^ 2 = 1 := by rw [← hz2, pow_orderOf_eq_one]
  have hΩ : 2 ≤ Nat.card {c : Q // φ c = 1 ∧ c ^ 2 = 1} := by
    have : Nontrivial {c : Q // φ c = 1 ∧ c ^ 2 = 1} :=
      ⟨⟨⟨1, map_one φ, one_pow 2⟩, ⟨z, hzk, hz2'⟩, fun h => hz1 (congrArg Subtype.val h).symm⟩⟩
    exact Finite.one_lt_card_iff_nontrivial.mpr this
  refine TransitiveLift.le_pRank_of_card hA (k := 3) ?_
  rw [hcard]
  calc 2 ^ 3 = 4 * 2 := by norm_num
    _ ≤ _ := Nat.mul_le_mul hW4 hΩ

theorem pRank_le_one_of_L24 (hQ : IsQuasisimple Q)
    (hO : pPrimeCore 2 Q = ⊥) (hL : LieModel (Q ⧸ center Q) .PSL 2 2 2) {z : Q}
    (hzZ : z ∈ center Q) (hz2 : orderOf z = 2) : CFSG.pRank 2 Q ≤ 1 := by
  obtain ⟨e⟩ := LocalAnalysis.ComponentInitial.PSL2_four_alternating_five_model _ hL
  exact pRank_le_one_of_alternating_five hQ hO e hzZ hz2

theorem pRank_le_one_of_L32 (hQ : IsQuasisimple Q) (hO : pPrimeCore 2 Q = ⊥)
    (hL : LieModel (Q ⧸ center Q) .PSL 3 2 1) {z : Q} (hzZ : z ∈ center Q)
    (hz2 : orderOf z = 2) : CFSG.pRank 2 Q ≤ 1 := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := GriessNative.classical_of_lieModel
    (LocalAnalysis.ComponentInitial.PSL3_two_PSL2_seven_paired_isomorphism _ hL) (by decide)
  have : CharP K 7 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic (by norm_num) le_rfl hK
  exact pRank_le_one_of_PSL_two hQ hO hzZ hz2 (by rw [ringChar.eq K 7]; omega) e

theorem four_le_pRank_of_L42 (hL : LieModel (Q ⧸ center Q) .PSL 4 2 1) {z : Q}
    (hzZ : z ∈ center Q) (hz2 : orderOf z = 2) : 4 ≤ CFSG.pRank 2 Q := by
  obtain ⟨e⟩ := (SymmetricLocal.lie_model_linear_four_two_iff _).1 hL
  exact four_le_pRank_of_alternating le_rfl e hzZ hz2

omit [Finite Q] in
theorem exists_sp4_of_U42 (hL : LieModel (Q ⧸ center Q) .PSU 4 2 1) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k), ringChar k ≠ 2 ∧
      Nonempty (Q ⧸ center Q ≃* StatedProj (StatedSp 2 k)) := by
  obtain ⟨e⟩ := LieType.Multipliers.U42.nonempty_mulEquiv_PSp43 hL
  exact ⟨ZMod 3, inferInstance, inferInstance, by rw [ZMod.ringChar_zmod_n]; omega, ⟨e⟩⟩

theorem four_le_pRank_of_Sz8 (hL : LieModel (Q ⧸ center Q) .twistedB2 0 2 3) {z : Q}
    (hzZ : z ∈ center Q) (hz2 : orderOf z = 2) : 4 ≤ CFSG.pRank 2 Q := by
  obtain ⟨-, -, a, -, K, _, _, hf, hK, ⟨e⟩⟩ := GriessNative.suzuki_of_lieModel hL
  obtain rfl : a = 1 := by omega
  have hK8 : Nat.card K = 8 := by rw [hK]; norm_num
  exact four_le_pRank_of_e8Datum DoubleCoverRanks.sz8_e8Datum
    (e.trans (Hq4.tauCetiSz8Equiv hK8).symm) hzZ hz2

theorem five_le_pRank_of_G24
    (hQ : IsQuasisimple Q)
    (hL : LieModel (Q ⧸ center Q) .G2 0 2 2) (hrow : GriessAll.GriessRow (Q ⧸ center Q) .G2 0 2 2)
    {z : Q} (hzZ : z ∈ center Q) (hz2 : orderOf z = 2) : 5 ≤ CFSG.pRank 2 Q := by
  obtain ⟨-, -, K, _, _, hK, ⟨e⟩⟩ := GriessNative.chevalley_of_lieModel hL (by decide)
  have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
  have : CharP K 2 := GriessNative.charP_two_of_card (by norm_num) hK rfl
  let eA : AdjointQuotient .G2 K ≃* Chevalley.adjointGroup .G2 K :=
    (QuotientGroup.quotientMulEquivOfEq CFSG.LieType.Chevalley.center_adjointGroup_eq_bot).trans
      QuotientGroup.quotientBot
  let f : Q ⧸ center Q ≃* Chevalley.adjointGroup .G2 K := e.trans eA
  have hZ2 : Nat.card (center Q) = 2 := by
    have h := card_center_dvd_of_griessRow hQ hrow
    have hval : (genericOrders .G2 0 2 2).1 * (genericOrders .G2 0 2 2).2 *
        ((exceptionalOrders .G2 0 2 2).1 * (exceptionalOrders .G2 0 2 2).2) = 2 := by decide
    rw [hval] at h
    have hz1 : z ≠ 1 := by rintro rfl; rw [orderOf_one] at hz2; omega
    have : Nontrivial (center Q) := ⟨⟨⟨z, hzZ⟩, 1, fun h => hz1 (congrArg Subtype.val h)⟩⟩
    exact le_antisymm (Nat.le_of_dvd two_pos h) Finite.one_lt_card
  exact DoubleCoverRanksTwo.five_le_pRank_adjointGroup hK4 (f.toMonoidHom.comp
    (QuotientGroup.mk' (center Q))) (f.surjective.comp (QuotientGroup.mk'_surjective _))
    (ker_quotientMap f) hZ2

theorem three_le_pRank_of_U62 (hQ : IsQuasisimple Q) (hO : pPrimeCore 2 Q = ⊥)
    (hL : LieModel (Q ⧸ center Q) .PSU 6 2 1) : 3 ≤ CFSG.pRank 2 Q := by
  have : Group.IsPerfect Q := hQ.1
  obtain ⟨M, -, hM2, hcard⟩ := EvenSmallLie.UnitarySix.exists_elementary_preimage
    (isPGroup_center_of_pPrimeCore_eq_bot hO) hL
  have hA : CFSG.IsElementaryAbelian 2 M :=
    { toIsMulCommutative :=
        ⟨⟨fun a b => Subtype.ext (DoubleCoverLift.mul_comm_of_sq_eq_one hM2 a.2 b.2)⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a => Subtype.ext (hM2 a a.2) }
  have hle : Nat.card (M.map (QuotientGroup.mk' (center Q))) ≤ Nat.card M :=
    Nat.card_le_card_of_surjective _ (MonoidHom.subgroupMap_surjective _ M)
  refine TransitiveLift.le_pRank_of_card hA (k := 3) ?_
  rw [hcard] at hle
  exact le_trans (by norm_num) hle

theorem three_le_pRank_of_L34 (hL : LieModel (Q ⧸ center Q) .PSL 3 2 2) {z : Q}
    (hzZ : z ∈ center Q) (hz2 : orderOf z = 2) : 3 ≤ CFSG.pRank 2 Q := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := GriessNative.classical_of_lieModel hL (by decide)
  have : CharP K 2 := GriessNative.charP_two_of_card (by norm_num) hK rfl
  have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
  let e' : Q ⧸ center Q ≃* Assembly.RankThreeEven.projSL 3 K :=
    e.trans (RankThree.PartTwo.KFacts.KS44.projSLEquivStatedProj K).symm
  have hφ : Function.Surjective (e'.toMonoidHom.comp (QuotientGroup.mk' (center Q))) :=
    e'.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker := ker_quotientMap e'
  refine three_le_pRank_of_lifts hφ hker (W := (DoubleCoverRanksTwo.rootHom (K := K)).range)
    ?_ (fun y y' hy hy' => DoubleCoverRanksTwo.commute_lift_rootHom hφ hker.le hy hy')
    (fun y hy => ?_) hzZ hz2
  · rw [DoubleCoverRanksTwo.card_range_rootHom, hK4]
  · obtain ⟨a, ha⟩ := hy
    exact DoubleCoverRanksTwo.exists_sq_eq_sq_E hφ hker.le (by omega)
      (ha ▸ DoubleCoverRanksTwo.rootHom_mem_range_uHom a)

theorem four_le_pRank_of_Sp62 (hL : LieModel (Q ⧸ center Q) .PSp 3 2 1) {z : Q}
    (hzZ : z ∈ center Q) (hz2 : orderOf z = 2) : 4 ≤ CFSG.pRank 2 Q := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := GriessNative.classical_of_lieModel hL (by decide)
  have : CharP K 2 := GriessNative.charP_two_of_card le_rfl hK rfl
  have : Fintype K := Fintype.ofFinite K
  have hK2 : Fintype.card K = 2 := by rw [Fintype.card_eq_nat_card, hK, pow_one]
  set ι : ZMod 2 →+* K := ZMod.castHom (dvd_refl 2) K
  set Ψ : GL (Fin 3 ⊕ Fin 3) (ZMod 2) →* GL (Fin 3 ⊕ Fin 3) K :=
    Matrix.GeneralLinearGroup.map ι with hΨ
  have hΨc : ∀ g, ((Ψ g : GL (Fin 3 ⊕ Fin 3) K) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) =
      (g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)).map ι := fun _ => rfl
  have hΨinj : Function.Injective Ψ := by
    intro g h hgh
    apply Units.ext
    apply Matrix.map_injective ι.injective
    change (g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)).map ι =
      (h : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)).map ι
    rw [← hΨc, ← hΨc, hgh]
  have hmem : ∀ M : GL (Fin 3 ⊕ Fin 3) (ZMod 2),
      (M : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2))ᵀ * Assembly.RankThreeEven.sympForm 3
        (ZMod 2) * M = Assembly.RankThreeEven.sympForm 3 (ZMod 2) → Ψ M ∈ StatedSp 3 K := by
    intro M hM
    apply Subgroup.subset_closure
    have hJ : (Assembly.RankThreeEven.sympForm 3 (ZMod 2)).map ι =
        (fromBlocks 0 1 (-1) 0 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) := by
      ext i j
      rcases i with i | i <;> rcases j with j | j <;>
        simp only [Assembly.RankThreeEven.sympForm, Matrix.map_apply, Matrix.fromBlocks_apply₁₁,
          Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
          Matrix.zero_apply, Matrix.neg_apply, Matrix.one_apply, map_zero, map_neg] <;>
        split_ifs <;> simp
    show ((Ψ M : GL (Fin 3 ⊕ Fin 3) K) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K)ᵀ *
      fromBlocks 0 1 (-1) 0 * ((Ψ M : GL (Fin 3 ⊕ Fin 3) K) : Matrix _ _ K) = fromBlocks 0 1 (-1) 0
    rw [hΨc, ← hJ, ← transpose_map, ← Matrix.map_mul,
      ← Matrix.map_mul, hM]
  have hD : DoubleCoverLift.E8Datum (⟨_, hmem _ DoubleCoverRanks.spA₁_symplectic⟩ : StatedSp 3 K)
      ⟨_, hmem _ DoubleCoverRanks.spA₂_symplectic⟩ ⟨_, hmem _ DoubleCoverRanks.spA₃_symplectic⟩
      ⟨_, hmem _ DoubleCoverRanks.spN_symplectic⟩ :=
    DoubleCoverLift.E8Datum.of_map (StatedSp 3 K).subtype Subtype.val_injective
      (DoubleCoverRanks.sp62_gl_e8Datum.map Ψ hΨinj)
  have hunit : ∀ c : Kˣ, c = 1 := fun c => by
    have hc := FiniteField.pow_card (c : K)
    rw [hK2, pow_two] at hc
    exact Units.ext (mul_left_cancel₀ c.ne_zero (by rw [Units.val_one, mul_one, hc]))
  have hinj : Function.Injective (QuotientGroup.mk'
      ((StatedScalars (Fin 3 ⊕ Fin 3) K).subgroupOf (StatedSp 3 K))) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', eq_bot_iff]
    rintro x ⟨c, hc⟩
    rw [hunit c, map_one] at hc
    exact Subgroup.mem_bot.mpr (Subtype.ext hc.symm)
  exact four_le_pRank_of_e8Datum ((hD.map _ hinj).map e.symm.toMonoidHom e.symm.injective)
    (MulEquiv.refl _) hzZ hz2

end CFSG.ComponentClassification.Sol76T13.R12.Pcls
