module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMSevenCo1
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMSevenB
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMFiveCentA
public import CFSG.Sporadic.Bridge.MonsterModelsGriess
import all CFSG.Monster.Existence.TwoB
import all CFSG.Monster.Existence.Co1Bridge
import all CFSG.Monster.VisQuot.Simple

public section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Dickson.I271.TabMSeven

open CFSG CFSG.Monster CFSG.Monster.Spin CFSG.Monster.SpinLattice CFSG.Monster.Visible
  CFSG.Monster.Existence CFSG.Monster.Griess CFSG.Monster.ScalarKernel
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Dickson.I271.TabMFive

section TwoB


open CFSG.Monster.Existence.Co1Bridge

theorem card_inf_cent_xGriess_le_seven (hS : Co1SevenBound) {k : MGriess} (hk : orderOf k = 7)
    (hxk : xGriess * k = k * xGriess) :
    Nat.card ↥(cent xGriess ⊓ Subgroup.centralizer ({k} : Set MGriess)) ≤ 150528 := by
  haveI : Finite (cent xGriess) := finite_cent_xGriess
  haveI : Finite J24 := finite_J24
  have hkmem : k ∈ cent xGriess := Subgroup.mem_centralizer_singleton_iff.2 hxk.symm
  have hk' : orderOf (⟨k, hkmem⟩ : cent xGriess) = 7 := by
    rw [← Subgroup.orderOf_coe]
    exact hk
  have hj := @orderOf_image_prime (cent xGriess) ↥J24 _ (Subgroup.toGroup J24) _ 7
    (by norm_num) (by norm_num) cosetEquivJ24 ⟨k, hkmem⟩ hk'
  have h1 := card_centralizer_cent_xGriess_le (⟨k, hkmem⟩ : cent xGriess)
  have h2 := hS _ hj
  have h3 := card_centralizer_subtype (C := cent xGriess) (⟨k, hkmem⟩ : cent xGriess)
  exact h3.symm.le.trans (h1.trans h2)

theorem h2B_MGriess_seven (hS : Co1SevenBound) (hE : MonsterExistenceStatement MGriess)
    (hB : Nat.card CFSG.Blueprint.NativeSporadic.B = CFSG.Open.monsterBabyOrder) :
    ∀ t k : MGriess, orderOf t = 2 →
      Nat.card ↥(Subgroup.centralizer ({t} : Set MGriess)) = twoBCentralizerOrder →
      orderOf k = 7 → t * k = k * t →
      Nat.card ↥(Subgroup.centralizer ({t} : Set MGriess) ⊓
        Subgroup.centralizer ({k} : Set MGriess)) ≤ 150528 := by
  intro t k ht htc hk htk
  obtain ⟨g, hg⟩ := isConj_iff.1 (isConj_xGriess_of_card hE hB ht htc)
  rw [← hg, natCard_cent_inf_conj]
  have ho : orderOf (g⁻¹ * k * g) = 7 := by
    have h := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) k
    rw [MulAut.conj_apply, inv_inv] at h
    rw [h]
    exact hk
  refine card_inf_cent_xGriess_le_seven hS (k := g⁻¹ * k * g) ho ?_
  rw [← hg] at htk
  calc xGriess * (g⁻¹ * k * g) = g⁻¹ * (g * xGriess * g⁻¹ * k) * g := by group
    _ = g⁻¹ * (k * (g * xGriess * g⁻¹)) * g := by rw [htk]
    _ = g⁻¹ * k * g * xGriess := by group

theorem card_cent_xGriess_dvd_of_fixCount_le_one (k : cent xGriess)
    (h : fixCount (((cosetEquivJ24 (QuotientGroup.mk k) : J24) : GL (Fin 24) (ZMod 2)) :
      Matrix (Fin 24) (Fin 24) (ZMod 2)) ≤ 1) :
    Nat.card (Subgroup.centralizer ({k} : Set (cent xGriess))) ∣
      2 * Nat.card (Subgroup.centralizer ({cosetEquivJ24 (QuotientGroup.mk k)} : Set J24)) := by
  haveI : Finite (cent xGriess) := finite_cent_xGriess
  haveI : Finite J24 := finite_J24
  obtain ⟨p, hp⟩ := mem_Gvis.1 (centGriessEquiv k).2
  have hp' : thetaEquiv p = (((k : MGriess) : AutO) : SpaceB ≃ₗ[ℚ] SpaceB) := hp
  have h2 := card_pCore_inf_cent_le k p hp'
  have h3 := card_fixed_conjQ_le p
  have h4 := natCard_fixed_modTwoEnd
    ((cosetEquivJ24 (QuotientGroup.mk k) : J24) : GL (Fin 24) (ZMod 2)) p.1.2
    (conjHom_cosetEquivJ24 k p hp')
  rw [h4] at h3
  have hK : Nat.card ↥(pCore 2 (cent xGriess) ⊓
      Subgroup.centralizer ({k} : Set (cent xGriess))) ≤ 2 := by
    have := h2.trans h3
    omega
  obtain ⟨a, ha⟩ := ((pCore_isPGroup (p := 2) (G := cent xGriess)).to_le
    (inf_le_left : pCore 2 (cent xGriess) ⊓ Subgroup.centralizer ({k} : Set (cent xGriess)) ≤
      pCore 2 (cent xGriess))).exists_card_eq
  have hK2 : Nat.card ↥(pCore 2 (cent xGriess) ⊓
      Subgroup.centralizer ({k} : Set (cent xGriess))) ∣ 2 := by
    rw [ha] at hK ⊢
    have ha1 : a ≤ 1 := by
      by_contra hc
      have h5 : 2 ^ 2 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h6 := h5.trans hK
      norm_num at h6
    exact (Nat.pow_dvd_pow 2 ha1).trans (by norm_num)
  have hc := @card_centralizer_eq_mul (cent xGriess) ↥J24 _ (Subgroup.toGroup J24) _
    (pCore 2 (cent xGriess)) _ cosetEquivJ24 k
  have hr := Subgroup.card_dvd_of_le (@range_centMap_le (cent xGriess) ↥J24 _
    (Subgroup.toGroup J24) (pCore 2 (cent xGriess)) _ cosetEquivJ24 k)
  rw [hc]
  exact Nat.mul_dvd_mul hK2 hr

end TwoB

section Classes

variable {G : Type} [Group G]

theorem card_cent_of_isTwoACentralizer {a : G} (ha : orderOf a = 2) (h : IsTwoACentralizer a)
    (hB : Nat.card CFSG.Blueprint.NativeSporadic.B = CFSG.Open.monsterBabyOrder) :
    Nat.card ↥(Subgroup.centralizer ({a} : Set G)) = 2 * CFSG.Open.monsterBabyOrder := by
  obtain ⟨-, hz, ⟨e⟩⟩ := h
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥(cent a))
  have hc : Nat.card ↥(Subgroup.center ↥(cent a)) = 2 := by
    rw [← Subgroup.card_map_of_injective (cent a).subtype_injective, hz, Nat.card_zpowers, ha]
  rw [Nat.card_congr e.toEquiv, hB, hc] at h1
  change Nat.card ↥(cent a) = _
  omega

theorem hcls_of_existence (hE : MonsterExistenceStatement G)
    (hB : Nat.card CFSG.Blueprint.NativeSporadic.B = CFSG.Open.monsterBabyOrder) :
    ∀ t : G, orderOf t = 2 →
      Nat.card ↥(Subgroup.centralizer ({t} : Set G)) = 2 * CFSG.Open.monsterBabyOrder ∨
        Nat.card ↥(Subgroup.centralizer ({t} : Set G)) = twoBCentralizerOrder := by
  intro t ht
  obtain ⟨-, a, z, -, -, -, hcls, hA, hBz, -⟩ := id hE
  rcases hcls t ht with h | h
  · exact Or.inl (card_cent_of_isTwoACentralizer ht (hA t h) hB)
  · exact Or.inr (hBz t h).2.2.2.2.1

end Classes

section TwoA


theorem h2A_seven
    {G : Type} [Group G] (hE : MonsterExistenceStatement G) :
    ∀ t k : G, orderOf t = 2 →
      Nat.card ↥(Subgroup.centralizer ({t} : Set G)) = 2 * CFSG.Open.monsterBabyOrder →
      orderOf k = 7 → t * k = k * t →
      Nat.card ↥(Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer ({k} : Set G)) ≤
        1128960 := by
  intro t k ht htc hk htk
  obtain ⟨⟨hfin, -, -, -⟩, a, z, -, -, -, hcls, hA, hB, -⟩ := id hE
  haveI : Finite G := hfin
  have htA : IsConj a t := by
    rcases hcls t ht with h | h
    · exact h
    · exfalso
      have h2 := (hB t h).2.2.2.2.1
      rw [htc] at h2
      norm_num [twoBCentralizerOrder, CFSG.Open.monsterBabyOrder] at h2
  obtain ⟨-, hZ, ⟨e⟩⟩ := hA t htA
  set X : Subgroup G := Subgroup.centralizer ({t} : Set G) with hX
  have hkX : k ∈ X := Subgroup.mem_centralizer_singleton_iff.2 htk.symm
  set k' : ↥X := ⟨k, hkX⟩ with hk'
  have hk'7 : orderOf k' = 7 := by rw [← Subgroup.orderOf_coe]; exact hk
  have hZcard : Nat.card ↥(Subgroup.center ↥X) = 2 := by
    have h1 : Nat.card ↥((Subgroup.center ↥X).map X.subtype) = Nat.card ↥(Subgroup.center ↥X) :=
      Subgroup.card_map_of_injective X.subtype_injective
    rw [hZ, Nat.card_zpowers, ht] at h1
    exact h1.symm
  haveI : Finite ↥X := inferInstance
  haveI : Finite CFSG.Blueprint.NativeSporadic.B := Finite.of_equiv _ e.toEquiv
  have hbar : orderOf (e (QuotientGroup.mk k')) = 7 := by
    haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    rw [MulEquiv.orderOf_eq]
    refine orderOf_eq_prime ?_ fun h1 => ?_
    · rw [← QuotientGroup.mk_pow, ← hk'7, pow_orderOf_eq_one, QuotientGroup.mk_one]
    · have hmem : k' ∈ Subgroup.center ↥X := (QuotientGroup.eq_one_iff k').1 h1
      have h2 := Subgroup.orderOf_dvd_natCard _ hmem
      rw [Subgroup.orderOf_mk, hk, hZcard] at h2
      norm_num at h2
  have hcard := @card_centralizer_le_mul ↥X CFSG.Blueprint.NativeSporadic.B _ Units.instGroup _ _
    (Subgroup.center ↥X) _ e k'
  have hZk : Nat.card ↥(Subgroup.center ↥X ⊓ Subgroup.centralizer ({k'} : Set ↥X)) ≤ 2 :=
    hZcard ▸ Subgroup.card_le_of_le inf_le_left
  have hBk := card_centralizer_seven_le_B hbar
  have h3 : Nat.card ↥(Subgroup.centralizer ({k'} : Set ↥X)) ≤ 1128960 :=
    hcard.trans (by
      calc _ ≤ 2 * 564480 := Nat.mul_le_mul hZk hBk
        _ = 1128960 := by norm_num)
  rw [card_centralizer_subtype] at h3
  exact h3

end TwoA

section Transport

variable {G G' : Type} [Group G] [Group G']

theorem hcls_of_mulEquiv (e : G ≃* G') {N₁ N₂ : ℕ}
    (h : ∀ t : G, orderOf t = 2 → Nat.card ↥(Subgroup.centralizer ({t} : Set G)) = N₁ ∨
      Nat.card ↥(Subgroup.centralizer ({t} : Set G)) = N₂) :
    ∀ t : G', orderOf t = 2 → Nat.card ↥(Subgroup.centralizer ({t} : Set G')) = N₁ ∨
      Nat.card ↥(Subgroup.centralizer ({t} : Set G')) = N₂ := by
  intro t ht
  have h1 := h (e.symm t) (by rw [MulEquiv.orderOf_eq]; exact ht)
  rwa [← natCard_centralizer_map e (e.symm t), MulEquiv.apply_symm_apply] at h1

theorem inf_bound_of_mulEquiv (e : G ≃* G') {N p M : ℕ}
    (h : ∀ t k : G, orderOf t = 2 → Nat.card ↥(Subgroup.centralizer ({t} : Set G)) = N →
      orderOf k = p → t * k = k * t →
      Nat.card ↥(Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer ({k} : Set G)) ≤ M) :
    ∀ t k : G', orderOf t = 2 → Nat.card ↥(Subgroup.centralizer ({t} : Set G')) = N →
      orderOf k = p → t * k = k * t →
      Nat.card ↥(Subgroup.centralizer ({t} : Set G') ⊓ Subgroup.centralizer ({k} : Set G')) ≤
        M := by
  intro t k ht htc hk htk
  have h1 := h (e.symm t) (e.symm k) (by rw [MulEquiv.orderOf_eq]; exact ht)
    (by rw [← natCard_centralizer_map e, MulEquiv.apply_symm_apply]; exact htc)
    (by rw [MulEquiv.orderOf_eq]; exact hk) (by rw [← map_mul, ← map_mul, htk])
  rwa [← natCard_centralizer_inf_map e, MulEquiv.apply_symm_apply,
    MulEquiv.apply_symm_apply] at h1

theorem hG5_of_mulEquiv (e : G ≃* G') {N : ℕ}
    (h : ∀ A : Subgroup G, (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → (∀ a ∈ A, a ^ 2 = 1) →
      8 ≤ Nat.card ↥A → ∃ u ∈ A, orderOf u = 2 ∧
        Nat.card ↥(Subgroup.centralizer ({u} : Set G)) = N) :
    ∀ A : Subgroup G', (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → (∀ a ∈ A, a ^ 2 = 1) →
      8 ≤ Nat.card ↥A → ∃ u ∈ A, orderOf u = 2 ∧
        Nat.card ↥(Subgroup.centralizer ({u} : Set G')) = N := by
  intro A hAc hAe h8
  obtain ⟨u, hu, hu2, huc⟩ := h (A.comap e.toMonoidHom)
    (fun a ha b hb => e.injective (by
      rw [map_mul, map_mul]
      exact hAc _ (Subgroup.mem_comap.1 ha) _ (Subgroup.mem_comap.1 hb)))
    (fun a ha => e.injective (by
      rw [map_pow, map_one]
      exact hAe _ (Subgroup.mem_comap.1 ha)))
    (by
      rw [Nat.card_congr (Equiv.subtypeEquiv e.toEquiv fun x => Subgroup.mem_comap)]
      exact h8)
  exact ⟨e u, Subgroup.mem_comap.1 hu, by rw [MulEquiv.orderOf_eq]; exact hu2,
    by rw [natCard_centralizer_map]; exact huc⟩

end Transport

section Gmat


open CFSG.Monster.Generated (Gmat)

theorem gmat_seven_bounds
    :
    (∀ t : Gmat, orderOf t = 2 →
      Nat.card ↥(Subgroup.centralizer ({t} : Set Gmat)) = 2 * CFSG.Open.monsterBabyOrder ∨
        Nat.card ↥(Subgroup.centralizer ({t} : Set Gmat)) = twoBCentralizerOrder) ∧
    (∀ t k : Gmat, orderOf t = 2 →
      Nat.card ↥(Subgroup.centralizer ({t} : Set Gmat)) = 2 * CFSG.Open.monsterBabyOrder →
      orderOf k = 7 → t * k = k * t →
      Nat.card ↥(Subgroup.centralizer ({t} : Set Gmat) ⊓ Subgroup.centralizer ({k} : Set Gmat)) ≤
        1128960) ∧
    (∀ t k : Gmat, orderOf t = 2 →
      Nat.card ↥(Subgroup.centralizer ({t} : Set Gmat)) = twoBCentralizerOrder →
      orderOf k = 7 → t * k = k * t →
      Nat.card ↥(Subgroup.centralizer ({t} : Set Gmat) ⊓ Subgroup.centralizer ({k} : Set Gmat)) ≤
        150528) ∧
    (∀ A : Subgroup Gmat, (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → (∀ a ∈ A, a ^ 2 = 1) →
      8 ≤ Nat.card ↥A → ∃ u ∈ A, orderOf u = 2 ∧
        Nat.card ↥(Subgroup.centralizer ({u} : Set Gmat)) = twoBCentralizerOrder) := by
  have hE : MonsterExistenceStatement MGriess :=
    CFSG.Milestones.cl_lit_monster_existence_griess_conway
  have hB := card_nativeB
  let e : MGriess ≃* ↥Gmat :=
    CFSG.YGroups.Y443.griessEquivGmat CFSG.Blueprint.NativeSporadic.MonsterModel.gmat_eq_griess
  exact ⟨hcls_of_mulEquiv e (hcls_of_existence hE hB), inf_bound_of_mulEquiv e (h2A_seven hE),
    inf_bound_of_mulEquiv e (h2B_MGriess_seven co1SevenBound hE hB),
    hG5_of_mulEquiv e (hG5_MGriess hE)⟩

end Gmat

end CFSG.HardMathSupport.Dickson.I271.TabMSeven
