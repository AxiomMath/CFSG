module

public import CFSG.Sporadic.ONOddCore.SylowEight
public import CFSG.Sporadic.ON.Simple
public import CFSG.Sporadic.Recognition.ONMultiplierCert
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitFixedSimple
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitTypeRank

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup
open CFSG.Blueprint.NativeSporadic (IsSporadic)
open scoped commutatorElement

private theorem three_le_pRank_of_onan_hom
    {Y X : Type} [Group Y] [Group X] [Finite X]
    (e : Y ≃* Blueprint.NativeSporadic.Carrier .ONan) (f : Y →* X) (hf : Function.Injective f) :
    3 ≤ CFSG.pRank 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hA, hcard, -⟩ :=
    CFSG.Sporadic.ONOddCore.glq_on_sylow_characteristic_elementary_eight
  set D := Subgroup.closure {x | ∃ t ∈ CFSG.ONSchreier.onT, t ^ 2 = x} with hD
  set A := Subgroup.closure {x | x ∈ D ∧ x ^ 2 = 1} with hAdef
  have hDT : D ≤ CFSG.ONSchreier.onT := by
    rw [hD, Subgroup.closure_le]
    rintro _ ⟨t, ht, rfl⟩
    exact pow_mem ht 2
  have hAP : A ≤ CFSG.ONSchreier.Pv := by
    have hAD : A ≤ D := by
      rw [hAdef, Subgroup.closure_le]
      exact fun x hx => hx.1
    exact hAD.trans (hDT.trans CFSG.ONSchreier.onT_le)
  have hA' : CFSG.IsElementaryAbelian 2 (A.subgroupOf CFSG.ONSchreier.Pv) :=
    CFSG.IsElementaryAbelian.subgroupOf hAP
  let ψ : ↥CFSG.ONSchreier.Pv ≃* Y := CFSG.ONSchreier.onEquivPv.symm.trans e.symm
  let φ : ↥CFSG.ONSchreier.Pv →* X := f.comp ψ.toMonoidHom
  have hφ : Function.Injective φ := hf.comp ψ.injective
  have hE : CFSG.IsElementaryAbelian 2 ((A.subgroupOf CFSG.ONSchreier.Pv).map φ) :=
    CFSG.IsElementaryAbelian.map _
  have hcardE : Nat.card ((A.subgroupOf CFSG.ONSchreier.Pv).map φ) = 2 ^ 3 := by
    rw [Subgroup.card_map_of_injective hφ,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAP).toEquiv, hcard]
    norm_num
  refine le_csSup ⟨Nat.card X, ?_⟩ ⟨_, hE, hcardE⟩
  rintro r ⟨B, -, hB⟩
  calc r ≤ 2 ^ r := (Nat.lt_pow_self (by norm_num)).le
    _ = Nat.card B := hB.symm
    _ ≤ Nat.card X := Subgroup.card_le_card_group B

theorem three_le_pRank_of_sporadic_onan_pPrimeCore
    {H : Type} [Group H] [Finite H]
    (h : IsSporadic (H ⧸ pPrimeCore 2 H) .ONan) : 3 ≤ pRank 2 H := by
  obtain ⟨e⟩ := h
  rw [CFSG.ComponentClassification.UnbalancedCorr.pRank_eq_pRank_quotient_pPrimeCore H]
  exact three_le_pRank_of_onan_hom e (MonoidHom.id _) Function.injective_id

private theorem isPerfect_of_isSimpleGroup_of_card_not_prime {T : Type*} [Group T] [Finite T]
    [IsSimpleGroup T] (hcard : ¬ (Nat.card T).Prime) : Group.IsPerfect T := by
  rw [Group.isPerfect_def]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (⁅(⊤ : Subgroup T), (⊤ : Subgroup T)⁆) with h | h
  · exfalso
    have hcomm : ∀ a b : T, a * b = b * a := fun a b => by
      have h1 : ⁅a, b⁆ ∈ ⁅(⊤ : Subgroup T), (⊤ : Subgroup T)⁆ :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot] at h1
      exact commutatorElement_eq_one_iff_mul_comm.mp h1
    have : IsMulCommutative T := ⟨⟨hcomm⟩⟩
    exact hcard (Group.is_simple_iff_prime_card.mp inferInstance)
  · exact h

private theorem isPerfect_of_mulEquiv_onan {T : Type} [Group T]
    [Finite T] (e : T ≃* Blueprint.NativeSporadic.ON) : Group.IsPerfect T := by
  have : IsSimpleGroup Blueprint.NativeSporadic.ON := CFSG.Sporadic.ON.isSimpleGroup_ON
  have : IsSimpleGroup T :=
    @MulEquiv.isSimpleGroup T _ Blueprint.NativeSporadic.ON _
      CFSG.Sporadic.ON.isSimpleGroup_ON e
  refine isPerfect_of_isSimpleGroup_of_card_not_prime (T := T) ?_
  have hcard : Nat.card T = 460815505920 := by
    rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.ON.card_ON_eq]
  rw [hcard]
  intro hp
  have heven : Even 460815505920 := by norm_num
  have hne2 : (460815505920 : ℕ) ≠ 2 := by norm_num
  exact (Nat.not_even_iff_odd.mpr (hp.odd_of_ne_two hne2)) heven

private theorem le_center_sup_commutator_of_perfect_center_quotient {X : Type*} [Group X]
    (h : Group.IsPerfect (X ⧸ Subgroup.center X)) :
    (⊤ : Subgroup X) ≤
      Subgroup.center X ⊔ ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ := by
  intro x _
  let π : X →* X ⧸ Subgroup.center X := QuotientGroup.mk' (Subgroup.center X)
  have hmap : Subgroup.map π ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ = ⊤ := by
    rw [Subgroup.map_commutator,
      Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective _)]
    exact Group.IsPerfect.commutator_eq_top
  have hx : π x ∈ Subgroup.map π ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ := by
    rw [hmap]
    exact Subgroup.mem_top _
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
  have hz : y⁻¹ * x ∈ Subgroup.center X := by
    rw [← QuotientGroup.ker_mk' (Subgroup.center X), MonoidHom.mem_ker]
    change π (y⁻¹ * x) = 1
    rw [map_mul, map_inv, hyx, inv_mul_cancel]
  have hx' : x = y * (y⁻¹ * x) := by group
  rw [hx']
  exact Subgroup.mul_mem _
    (Subgroup.mem_sup_right (S := Subgroup.center X) hy)
    (Subgroup.mem_sup_left (T := ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆) hz)

private theorem commutator_commutator_eq_commutator_of_perfect_center_quotient {X : Type*}
    [Group X] (h : Group.IsPerfect (X ⧸ Subgroup.center X)) :
    ⁅⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆, ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆⁆ =
      ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ := by
  let J : Subgroup X := ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆
  have hle := le_center_sup_commutator_of_perfect_center_quotient h
  have htop : (⊤ : Subgroup X) = Subgroup.center X ⊔ J :=
    (le_antisymm le_top hle).symm
  have h1 : ⁅Subgroup.center X, Subgroup.center X ⊔ J⁆ = ⊥ := by
    rw [Subgroup.commutator_sup_left (Subgroup.center X) (Subgroup.center X) J,
      Subgroup.commutator_center_left (Subgroup.center X),
      Subgroup.commutator_center_left J, sup_bot_eq]
  have h2 : ⁅J, Subgroup.center X ⊔ J⁆ = ⁅J, J⁆ := by
    rw [Subgroup.commutator_sup_left J (Subgroup.center X) J,
      Subgroup.commutator_center_right J, bot_sup_eq]
  have hmain : ⁅Subgroup.center X ⊔ J, Subgroup.center X ⊔ J⁆ = ⁅J, J⁆ := by
    rw [Subgroup.commutator_sup_right (Subgroup.center X) J (Subgroup.center X ⊔ J), h1, h2,
      bot_sup_eq]
  have hJ : J = ⁅J, J⁆ := by
    change ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ = ⁅J, J⁆
    rw [htop]
    exact hmain
  exact hJ.symm

private theorem three_le_pRank_of_perfect_center_quotient_onan
    {X : Type} [Group X] [Finite X]
    (hperf : Group.IsPerfect (X ⧸ Subgroup.center X))
    (hZ2 : IsPGroup 2 (Subgroup.center X))
    (h : Nonempty (X ⧸ Subgroup.center X ≃* Blueprint.NativeSporadic.ON)) :
    3 ≤ pRank 2 X := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Z : Subgroup X := Subgroup.center X
  let J : Subgroup X := ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆
  have : Z.Normal := Subgroup.instNormalCenter
  obtain ⟨eXZ⟩ := h
  have hle : (⊤ : Subgroup X) ≤ Z ⊔ J := by
    simpa [Z, J] using le_center_sup_commutator_of_perfect_center_quotient hperf
  have hsupZJ : Z ⊔ J = ⊤ := le_antisymm le_top hle
  have hJJ : ⁅J, J⁆ = J := by
    simpa [Z, J] using commutator_commutator_eq_commutator_of_perfect_center_quotient hperf
  have hJperf : Group.IsPerfect ↥J := Subgroup.isPerfect_iff.mpr hJJ
  have hcenterJ : Subgroup.center ↥J = Z.subgroupOf J := by
    ext x
    constructor
    · intro hx
      change (x : X) ∈ Subgroup.center X
      rw [Subgroup.mem_center_iff] at hx ⊢
      intro y
      have hy : y ∈ Z ⊔ J := by rw [hsupZJ]; exact Subgroup.mem_top y
      obtain ⟨z, hz, j, hj, rfl⟩ : ∃ z ∈ Z, ∃ j ∈ J, z * j = y :=
        Subgroup.mem_sup_of_normal_left.mp (show y ∈ Z ⊔ J from hy)
      have hxj : j * (x : X) = (x : X) * j :=
        congrArg Subtype.val (hx ⟨j, hj⟩)
      calc (z * j) * (x : X) = z * (j * (x : X)) := mul_assoc _ _ _
        _ = z * ((x : X) * j) := by rw [hxj]
        _ = (z * (x : X)) * j := (mul_assoc _ _ _).symm
        _ = ((x : X) * z) * j := by
              rw [← Subgroup.mem_center_iff.mp hz (x : X)]
        _ = (x : X) * (z * j) := mul_assoc _ _ _
    · intro hx
      rw [Subgroup.mem_subgroupOf] at hx
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      exact Subgroup.mem_center_iff.mp hx (y : X)
  have hZ2J : IsPGroup 2 (Subgroup.center ↥J) := by
    rw [hcenterJ]
    exact hZ2.comap_subtype
  have hsupJZ : J ⊔ Z = ⊤ := by rw [sup_comm]; exact hsupZJ
  let e1 : ↥J ⧸ Subgroup.center ↥J ≃*
      (J ⊔ Z : Subgroup X) ⧸ Z.subgroupOf (J ⊔ Z) :=
    (QuotientGroup.quotientMulEquivOfEq hcenterJ).trans
      (QuotientGroup.quotientInfEquivProdNormalQuotient J Z)
  let e2 : (J ⊔ Z : Subgroup X) ⧸ Z.subgroupOf (J ⊔ Z) ≃*
      (⊤ : Subgroup X) ⧸ Z.subgroupOf ⊤ :=
    QuotientGroup.equivQuotientSubgroupOfOfEq (A := J ⊔ Z) (B := ⊤) (A' := Z) (B' := Z)
      rfl hsupJZ
  let e3 : (⊤ : Subgroup X) ⧸ Z.subgroupOf ⊤ ≃* X ⧸ Z :=
    QuotientGroup.congr (Z.subgroupOf ⊤) Z Subgroup.topEquiv
      (Subgroup.map_subgroupOf_eq_of_le le_top)
  let eJZ : ↥J ⧸ Subgroup.center ↥J ≃* X ⧸ Z := e1.trans (e2.trans e3)
  let eJON : ↥J ⧸ Subgroup.center ↥J ≃* Blueprint.NativeSporadic.ON := eJZ.trans eXZ
  have hbotJ : Subgroup.center ↥J = ⊥ :=
    Sporadic.Recognition.ONMultiplier.center_eq_bot_of_certificate hJperf hZ2J eJON
  have eJON' : ↥J ≃* Blueprint.NativeSporadic.ON :=
    ((QuotientGroup.quotientMulEquivOfEq hbotJ).trans QuotientGroup.quotientBot).symm.trans
      eJON
  exact three_le_pRank_of_onan_hom eJON' J.subtype J.subtype_injective

theorem three_le_pRank_of_sporadic_onan_fusionZStar
    {H : Type} [Group H] [Finite H]
    (h : IsSporadic (H ⧸ Open.fusionZStar H) .ONan) : 3 ≤ pRank 2 H := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨eS⟩ := GrSLit.nonempty_quotient_center_equiv_fusionZStar H
  obtain ⟨f⟩ := h
  have hperfQ : Group.IsPerfect
      ((H ⧸ pPrimeCore 2 H) ⧸ Subgroup.center (H ⧸ pPrimeCore 2 H)) :=
    isPerfect_of_mulEquiv_onan (eS.trans f)
  have hZ2 : IsPGroup 2 (Subgroup.center (H ⧸ pPrimeCore 2 H)) :=
    FooteLit.isPGroup_center_quotient_pPrimeCore H
  have h3 : 3 ≤ pRank 2 (H ⧸ pPrimeCore 2 H) :=
    three_le_pRank_of_perfect_center_quotient_onan (X := H ⧸ pPrimeCore 2 H) hperfQ hZ2
      ⟨eS.trans f⟩
  rw [CFSG.ComponentClassification.UnbalancedCorr.pRank_eq_pRank_quotient_pPrimeCore H]
  exact h3

end CFSG.ComponentClassification.GrSLit.L34Sec5S
