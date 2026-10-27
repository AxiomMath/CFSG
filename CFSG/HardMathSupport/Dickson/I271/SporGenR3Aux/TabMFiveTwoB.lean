module

public import CFSG.Monster.Existence.Simple
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.TwoBLocalBound
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMFiveQFix
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMFiveFixRank
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMFiveEmb
import all CFSG.Monster.Existence.TwoB
import all CFSG.Monster.Existence.Co1Bridge
import all CFSG.Monster.VisQuot.Simple

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Dickson.I271.TabMFive

open CFSG CFSG.Monster CFSG.Monster.Spin CFSG.Monster.SpinLattice CFSG.Monster.Visible
  CFSG.Monster.Existence CFSG.Monster.Griess CFSG.Monster.ScalarKernel Subgroup
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open scoped Matrix

section Core

theorem hmapGriess : (pCore 2 (cent xGriess)).map centGriessEquiv.toMonoidHom = rhoQvis := by
  rw [pCore_map_iso 2 centGriessEquiv, pCore_Gvis]

theorem exists_rho_of_mem_pCore {y : cent xGriess} (hy : y ∈ pCore 2 (cent xGriess)) :
    ∃ r : Q, rhoEquiv r = (((y : MGriess) : AutO) : SpaceB ≃ₗ[ℚ] SpaceB) := by
  have h1 : centGriessEquiv y ∈ rhoQvis := hmapGriess ▸ ⟨y, hy, rfl⟩
  exact mem_rhoQ.1 (Subgroup.mem_subgroupOf.1 h1)

theorem card_pCore_inf_cent_le (h : cent xGriess) (p : Pvis)
    (hp : thetaEquiv p = (((h : MGriess) : AutO) : SpaceB ≃ₗ[ℚ] SpaceB)) :
    Nat.card ↥(pCore 2 (cent xGriess) ⊓ Subgroup.centralizer ({h} : Set (cent xGriess))) ≤
      Nat.card {r : Q // conjQ p r = r} := by
  haveI : Finite Q := Nat.finite_of_card_ne_zero (by rw [natCard_Q]; norm_num)
  have key : ∀ y : ↥(pCore 2 (cent xGriess) ⊓ Subgroup.centralizer ({h} : Set (cent xGriess))),
      ∃ r : Q, rhoEquiv r = (((y.1 : cent xGriess) : MGriess) : AutO) ∧ conjQ p r = r := by
    intro y
    obtain ⟨r, hr⟩ := exists_rho_of_mem_pCore (Subgroup.mem_inf.1 y.2).1
    refine ⟨r, hr, ?_⟩
    have hc : (y.1 : cent xGriess) * h = h * y.1 :=
      Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 y.2).2
    have hc' : (((y.1 : cent xGriess) : MGriess) : AutO).1 * (((h : MGriess) : AutO)).1 =
        (((h : MGriess) : AutO)).1 * (((y.1 : cent xGriess) : MGriess) : AutO).1 :=
      congrArg (fun z : cent xGriess => (((z : MGriess) : AutO) : SpaceB ≃ₗ[ℚ] SpaceB)) hc
    apply rhoEquiv_injective
    rw [← thetaEquiv_conj_rhoEquiv p r, hp, hr]
    rw [← hc', mul_inv_cancel_right]
  refine Nat.card_le_card_of_injective
    (fun y => ⟨Classical.choose (key y), (Classical.choose_spec (key y)).2⟩) ?_
  intro y y' hyy
  have h1 := (Classical.choose_spec (key y)).1
  have h2 := (Classical.choose_spec (key y')).1
  have h3 : Classical.choose (key y) = Classical.choose (key y') := congrArg Subtype.val hyy
  rw [h3] at h1
  exact Subtype.ext (Subtype.ext (Subtype.ext (h1.symm.trans h2)))

end Core

section Quot

open CFSG.Monster.Existence.Co1Bridge CFSG.Monster.VisQuot CFSG.Monster.VisCert

theorem visQuotEquivHvis_mk_thetaEquiv (p : Pvis) :
    ((visQuotEquivHvis (QuotientGroup.mk (⟨thetaEquiv p, thetaEquiv_mem_Gvis p⟩ : Gvis)) : Hvis) :
      GLV) = modTwoUnit p.1.2 := by
  show (OLqOpEquivHvis (visQuotEquiv (QuotientGroup.mk _)) : GLV) = _
  rw [visQuotEquiv_mk, piVis_thetaEquiv]
  rfl

@[expose] noncomputable def cosetEquivJ24 : cent xGriess ⧸ pCore 2 (cent xGriess) ≃* J24 :=
  (QuotientGroup.congr _ _ centGriessEquiv hmapGriess).trans
    (visQuotEquivHvis.trans jEquivHvis.symm)

theorem conjHom_cosetEquivJ24 (h : cent xGriess) (p : Pvis)
    (hp : thetaEquiv p = (((h : MGriess) : AutO) : SpaceB ≃ₗ[ℚ] SpaceB)) :
    conjHom ((cosetEquivJ24 (QuotientGroup.mk h) : J24) : GL (Fin 24) (ZMod 2)) =
      modTwoUnit p.1.2 := by
  have h1 : jEquivHvis (cosetEquivJ24 (QuotientGroup.mk h)) =
      visQuotEquivHvis (QuotientGroup.mk (centGriessEquiv h)) := by
    show jEquivHvis (jEquivHvis.symm (visQuotEquivHvis
      (QuotientGroup.congr _ _ centGriessEquiv hmapGriess (QuotientGroup.mk h)))) = _
    rw [MulEquiv.apply_symm_apply]
    rfl
  have h2 : centGriessEquiv h = ⟨thetaEquiv p, thetaEquiv_mem_Gvis p⟩ := Subtype.ext hp.symm
  rw [h2] at h1
  have h3 := congrArg (fun x : Hvis => (x : GLV)) h1
  exact h3.trans (visQuotEquivHvis_mk_thetaEquiv p)

end Quot

section Fix

open CFSG.Monster.Existence.Co1Bridge

theorem natCard_fixed_modTwoEnd (j : GL (Fin 24) (ZMod 2)) (g : latticeO)
    (hj : conjHom j = modTwoUnit g) :
    Nat.card {v : L2 // modTwoEnd g v = v} = fixCount (j : Matrix (Fin 24) (Fin 24) (ZMod 2)) := by
  have hv : ∀ v : L2, modTwoEnd g v =
      theta ((j : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ theta.symm v) := fun v => by
    have h1 := conjHom_apply j v
    rw [hj] at h1
    exact h1
  refine Nat.card_congr (Equiv.subtypeEquiv theta.symm.toEquiv fun v => ?_)
  show modTwoEnd g v = v ↔ (j : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ theta.symm v = theta.symm v
  rw [hv v]
  constructor
  · intro h
    have := congrArg theta.symm h
    rwa [LinearEquiv.symm_apply_apply] at this
  · intro h
    rw [h, LinearEquiv.apply_symm_apply]

end Fix

section Prime

theorem orderOf_image_prime {H K : Type*} [Group H] [Group K] [Finite H] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (e : H ⧸ pCore 2 H ≃* K) {x : H} (hx : orderOf x = p) :
    orderOf (e (QuotientGroup.mk x)) = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [MulEquiv.orderOf_eq]
  refine orderOf_eq_prime ?_ fun h1 => ?_
  · rw [← QuotientGroup.mk_pow, ← hx, pow_orderOf_eq_one, QuotientGroup.mk_one]
  · have hmem : x ∈ pCore 2 H := (QuotientGroup.eq_one_iff x).1 h1
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := H)) ⟨x, hmem⟩
    have h2 : x ^ (2 ^ n) = 1 := congrArg Subtype.val hn
    have h3 := orderOf_dvd_of_pow_eq_one h2
    rw [hx] at h3
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h3))

end Prime

section Conj

theorem natCard_cent_inf_conj {G : Type*} [Group G] (g x k : G) :
    Nat.card ↥(Subgroup.centralizer ({g * x * g⁻¹} : Set G) ⊓
        Subgroup.centralizer ({k} : Set G)) =
      Nat.card ↥(Subgroup.centralizer ({x} : Set G) ⊓
        Subgroup.centralizer ({g⁻¹ * k * g} : Set G)) := by
  have fwd : ∀ y : G, y ∈ Subgroup.centralizer ({g * x * g⁻¹} : Set G) ⊓
      Subgroup.centralizer ({k} : Set G) → g⁻¹ * y * g ∈ Subgroup.centralizer ({x} : Set G) ⊓
      Subgroup.centralizer ({g⁻¹ * k * g} : Set G) := by
    intro y hy
    obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 hy
    have h1' := Subgroup.mem_centralizer_singleton_iff.1 h1
    have h2' := Subgroup.mem_centralizer_singleton_iff.1 h2
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_,
      Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    · calc g⁻¹ * y * g * x = g⁻¹ * (y * (g * x * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * x * g⁻¹) * y) * g := by rw [h1']
        _ = x * (g⁻¹ * y * g) := by group
    · calc g⁻¹ * y * g * (g⁻¹ * k * g) = g⁻¹ * (y * k) * g := by group
        _ = g⁻¹ * (k * y) * g := by rw [h2']
        _ = g⁻¹ * k * g * (g⁻¹ * y * g) := by group
  have bwd : ∀ y : G, y ∈ Subgroup.centralizer ({x} : Set G) ⊓
      Subgroup.centralizer ({g⁻¹ * k * g} : Set G) → g * y * g⁻¹ ∈
      Subgroup.centralizer ({g * x * g⁻¹} : Set G) ⊓ Subgroup.centralizer ({k} : Set G) := by
    intro y hy
    obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 hy
    have h1' := Subgroup.mem_centralizer_singleton_iff.1 h1
    have h2' := Subgroup.mem_centralizer_singleton_iff.1 h2
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_,
      Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    · calc g * y * g⁻¹ * (g * x * g⁻¹) = g * (y * x) * g⁻¹ := by group
        _ = g * (x * y) * g⁻¹ := by rw [h1']
        _ = g * x * g⁻¹ * (g * y * g⁻¹) := by group
    · calc g * y * g⁻¹ * k = g * (y * (g⁻¹ * k * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * k * g) * y) * g⁻¹ := by rw [h2']
        _ = k * (g * y * g⁻¹) := by group
  exact Nat.card_congr
    { toFun := fun y => ⟨g⁻¹ * y.1 * g, fwd y.1 y.2⟩
      invFun := fun y => ⟨g * y.1 * g⁻¹, bwd y.1 y.2⟩
      left_inv := fun y => Subtype.ext (by group)
      right_inv := fun y => Subtype.ext (by group) }

end Conj

section Main

open CFSG.Monster.Existence.Co1Bridge

theorem twoB_xGriess : IsTwoBCentralizer xGriess :=
  isTwoBCentralizer_MGriess xGriess (IsConj.refl _)

theorem natCard_cent_xGriess : Nat.card (cent xGriess) = twoBCentralizerOrder :=
  twoB_xGriess.2.2.2.2.1

theorem finite_cent_xGriess : Finite (cent xGriess) :=
  Nat.finite_of_card_ne_zero (by rw [natCard_cent_xGriess]; simp [twoBCentralizerOrder])

theorem finite_J24 : Finite J24 :=
  Nat.finite_of_card_ne_zero (by rw [natCard_J24]; norm_num)

theorem card_centralizer_cent_xGriess_le (k : cent xGriess) :
    Nat.card (Subgroup.centralizer ({k} : Set (cent xGriess))) ≤
      2 * fixCount (((cosetEquivJ24 (QuotientGroup.mk k) : J24) : GL (Fin 24) (ZMod 2)) :
          Matrix (Fin 24) (Fin 24) (ZMod 2)) *
        Nat.card (Subgroup.centralizer ({cosetEquivJ24 (QuotientGroup.mk k)} : Set J24)) := by
  haveI : Finite (cent xGriess) := finite_cent_xGriess
  haveI : Finite J24 := finite_J24
  obtain ⟨p, hp⟩ := mem_Gvis.1 (centGriessEquiv k).2
  have hp' : thetaEquiv p = (((k : MGriess) : AutO) : SpaceB ≃ₗ[ℚ] SpaceB) := hp
  have h1 := @card_centralizer_le_mul (cent xGriess) ↥J24 _ (Subgroup.toGroup J24) _ _
    (pCore 2 (cent xGriess)) _ cosetEquivJ24 k
  have h2 := card_pCore_inf_cent_le k p hp'
  have h3 := card_fixed_conjQ_le p
  have h4 := natCard_fixed_modTwoEnd
    ((cosetEquivJ24 (QuotientGroup.mk k) : J24) : GL (Fin 24) (ZMod 2)) p.1.2
    (conjHom_cosetEquivJ24 k p hp')
  rw [h4] at h3
  exact h1.trans (Nat.mul_le_mul (h2.trans h3) le_rfl)

@[expose] def Co1FiveBound : Prop :=
  ∀ j : J24, orderOf j = 5 →
    2 * fixCount ((j : GL (Fin 24) (ZMod 2)) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *
      Nat.card (Subgroup.centralizer ({j} : Set J24)) ≤ 18432000

theorem card_inf_cent_xGriess_le (hS : Co1FiveBound) {k : MGriess} (hk : orderOf k = 5)
    (hxk : xGriess * k = k * xGriess) :
    Nat.card ↥(cent xGriess ⊓ Subgroup.centralizer ({k} : Set MGriess)) ≤ 18432000 := by
  haveI : Finite (cent xGriess) := finite_cent_xGriess
  haveI : Finite J24 := finite_J24
  have hkmem : k ∈ cent xGriess := Subgroup.mem_centralizer_singleton_iff.2 hxk.symm
  have hk' : orderOf (⟨k, hkmem⟩ : cent xGriess) = 5 := by
    rw [← Subgroup.orderOf_coe]
    exact hk
  have hj := @orderOf_image_prime (cent xGriess) ↥J24 _ (Subgroup.toGroup J24) _ 5
    Nat.prime_five (by norm_num) cosetEquivJ24 ⟨k, hkmem⟩ hk'
  have h1 := card_centralizer_cent_xGriess_le (⟨k, hkmem⟩ : cent xGriess)
  have h2 := hS _ hj
  have h3 := card_centralizer_subtype (C := cent xGriess) (⟨k, hkmem⟩ : cent xGriess)
  exact h3.symm.le.trans (h1.trans h2)

theorem card_cent_of_twoA {a : MGriess} (ha : orderOf a = 2) (h : IsTwoACentralizer a)
    (hB : Nat.card CFSG.Blueprint.NativeSporadic.B = CFSG.Open.monsterBabyOrder) :
    Nat.card ↥(cent a) = 2 * CFSG.Open.monsterBabyOrder := by
  obtain ⟨-, hz, ⟨e⟩⟩ := h
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥(cent a))
  have hc : Nat.card ↥(Subgroup.center ↥(cent a)) = 2 := by
    rw [← Subgroup.card_map_of_injective (cent a).subtype_injective, hz, Nat.card_zpowers, ha]
  rw [Nat.card_congr e.toEquiv, hB, hc] at h1
  omega

theorem isConj_xGriess_of_card (hE : MonsterExistenceStatement MGriess)
    (hB : Nat.card CFSG.Blueprint.NativeSporadic.B = CFSG.Open.monsterBabyOrder) {t : MGriess}
    (ht : orderOf t = 2) (htc : Nat.card ↥(cent t) = twoBCentralizerOrder) :
    IsConj xGriess t := by
  obtain ⟨-, a, z, -, -, -, hcls, hA, -, -⟩ := id hE
  have key : ∀ s : MGriess, orderOf s = 2 → Nat.card ↥(cent s) = twoBCentralizerOrder →
      IsConj z s := by
    intro s hs hsc
    rcases hcls s hs with h | h
    · exfalso
      have h1 := card_cent_of_twoA hs (hA s h) hB
      rw [hsc] at h1
      norm_num [twoBCentralizerOrder, CFSG.Open.monsterBabyOrder] at h1
    · exact h
  exact (key xGriess orderOf_xGriess natCard_cent_xGriess).symm.trans (key t ht htc)

theorem h2B_MGriess (hS : Co1FiveBound) (hE : MonsterExistenceStatement MGriess)
    (hB : Nat.card CFSG.Blueprint.NativeSporadic.B = CFSG.Open.monsterBabyOrder) :
    ∀ t k : MGriess, orderOf t = 2 →
      Nat.card ↥(Subgroup.centralizer ({t} : Set MGriess)) = twoBCentralizerOrder →
      orderOf k = 5 → t * k = k * t →
      Nat.card ↥(Subgroup.centralizer ({t} : Set MGriess) ⊓
        Subgroup.centralizer ({k} : Set MGriess)) ≤ 18432000 := by
  intro t k ht htc hk htk
  obtain ⟨g, hg⟩ := isConj_iff.1 (isConj_xGriess_of_card hE hB ht htc)
  rw [← hg, natCard_cent_inf_conj]
  have ho : orderOf (g⁻¹ * k * g) = 5 := by
    have h := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) k
    rw [MulAut.conj_apply, inv_inv] at h
    rw [h]
    exact hk
  refine card_inf_cent_xGriess_le hS (k := g⁻¹ * k * g) ho ?_
  rw [← hg] at htk
  calc xGriess * (g⁻¹ * k * g) = g⁻¹ * (g * xGriess * g⁻¹ * k) * g := by group
    _ = g⁻¹ * (k * (g * xGriess * g⁻¹)) * g := by rw [htk]
    _ = g⁻¹ * k * g * xGriess := by group

end Main

end CFSG.HardMathSupport.Dickson.I271.TabMFive
