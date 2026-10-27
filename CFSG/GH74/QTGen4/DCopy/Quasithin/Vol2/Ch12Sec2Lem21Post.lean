module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem21Post
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsL2
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Lem21Stmts

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped IsMulCommutative commutatorElement

open Lem21Post

theorem lem12223Post_of_F4 (h1222 : Stmt12_2_2_F4) : Lem12223Post_F4 := by
  intro G _ _ T L V H P U I W h v n p hyp hNE hC hpre hU hdata hcard
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hall⟩ := ((h1222 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow).resolve_left
    hyp.notAlt) L hyp.maximal hyp.faithful hyp.quasisimple
  obtain ⟨⟨hVT, hTV, hred, -⟩, -, -, -, -⟩ := hall V hyp.irrPlus
  obtain ⟨hH, -, hp, hp2, -, hPH, -, hHPT, -, hhP, hhM, hI, hUI, hUs, hUd, hUe, -, ⟨hN, ⟨e⟩⟩, -,
    hcomm, -⟩ := hpre
  obtain ⟨hvV, hvU, hvP, hW, hWP, -, -, hWV, -, hO2, -, -⟩ := hdata
  have hTH : T ≤ H := hH.1.1
  have hh1 : h ≠ 1 := fun h1 => hhM (h1 ▸ Subgroup.one_mem _)
  obtain ⟨hPz, hord⟩ := Lem21.eq_zpowers_of_card_eq_prime hp hcard hhP hh1

  have hVc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (mul_comm (⟨x, hx⟩ : ↥V) ⟨y, hy⟩)
  have hVhc : ∀ x ∈ CFSG.conjugate V h, ∀ y ∈ CFSG.conjugate V h, x * y = y * x := by
    intro x hx y hy
    rw [mem_conjugate_iff] at hx hy
    have h' : h * (x * y) * h⁻¹ = h * (y * x) * h⁻¹ := by
      calc h * (x * y) * h⁻¹ = (h * x * h⁻¹) * (h * y * h⁻¹) := by group
        _ = (h * y * h⁻¹) * (h * x * h⁻¹) := hVc _ hx _ hy
        _ = h * (y * x) * h⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h')
  have hUc : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x := by
    have := hUe.1
    exact fun x hx y hy => congrArg Subtype.val (mul_comm (⟨x, hx⟩ : ↥U) ⟨y, hy⟩)
  have hVI : V ≤ I := hI ▸ le_sup_left
  have hVhI : CFSG.conjugate V h ≤ I := hI ▸ le_sup_right
  have hUI' : U ≤ I := hUI ▸ CFSG.LieType.BorelTits.pCoreOf_le 2 I
  have hIU : I ≤ Subgroup.normalizer (U : Set G) :=
    hUI ▸ CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 I

  have hvh : ¬ v * h = h * v := by
    intro hvh
    have hvVh : v ∈ CFSG.conjugate V h := by
      rw [mem_conjugate_iff, ← hvh, mul_inv_cancel_right]
      exact hvV
    have hle : I ≤ Subgroup.centralizer ({v} : Set G) := by
      rw [hI]
      refine sup_le (fun y hy => ?_) (fun y hy => ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (hVc _ hy _ hvV)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (hVhc _ hy _ hvVh)
    have hcen : e (QuotientGroup.mk (⟨v, hVI hvV⟩ : ↥I)) ∈ Subgroup.center (DihedralGroup p) := by
      rw [Subgroup.mem_center_iff]
      intro d
      obtain ⟨q, rfl⟩ := e.surjective d
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      rw [← map_mul, ← map_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 2
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hle x.2))
    rw [DihedralGroup.center_eq_bot_of_odd_ne_one (hp.odd_of_ne_two hp2) hp.ne_one,
      Subgroup.mem_bot, EmbeddingLike.map_eq_one_iff, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf] at hcen
    exact hvU hcen

  have hxP : v * h⁻¹ * v⁻¹ * h ∈ P :=
    P.mul_mem ((Subgroup.mem_normalizer_iff.mp hvP h⁻¹).mp (P.inv_mem hhP)) hhP
  have hxI : v * h⁻¹ * v⁻¹ * h ∈ I := by
    have hy : h⁻¹ * v⁻¹ * h ∈ CFSG.conjugate V h := by
      rw [mem_conjugate_iff]
      simpa [mul_assoc] using V.inv_mem hvV
    have := I.mul_mem (hVI hvV) (hVhI hy)
    simpa [mul_assoc] using this
  have hx1 : v * h⁻¹ * v⁻¹ * h ≠ 1 := by
    intro hx
    apply hvh
    have e1 : v * h⁻¹ * v⁻¹ = h⁻¹ := mul_eq_one_iff_eq_inv.mp hx
    have e2 : v * h⁻¹ = h⁻¹ * v := by
      calc v * h⁻¹ = (v * h⁻¹ * v⁻¹) * v := by group
        _ = h⁻¹ * v := by rw [e1]
    calc v * h = h * (h⁻¹ * v) * h := by group
      _ = h * (v * h⁻¹) * h := by rw [← e2]
      _ = h * v := by group
  have hPI : P ≤ I := by
    rw [(Lem21.eq_zpowers_of_card_eq_prime hp hcard hxP hx1).1]
    exact Subgroup.zpowers_le.mpr hxI

  have hUW : U = W := by
    rw [hW]
    refine le_antisymm (le_conjClosure U P) (conjClosure_le fun x hx u hu => ?_)
    exact (Subgroup.mem_normalizer_iff.mp (hIU (hPI hx)) u).mp hu

  have hIPUV : I = P ⊔ U ⊔ V := by
    refine le_antisymm ?_ (sup_le (sup_le hPI hUI') hVI)
    rw [hI]
    refine sup_le le_sup_right fun y hy => ?_
    rw [mem_conjugate_iff] at hy
    have hhJ : h ∈ P ⊔ U ⊔ V := Subgroup.mem_sup_left (Subgroup.mem_sup_left hhP)
    have hyJ : h⁻¹ * (h * y * h⁻¹) * h ∈ P ⊔ U ⊔ V :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hhJ)
        (Subgroup.mem_sup_right hy)) hhJ
    simpa [mul_assoc] using hyJ

  have hO2U : oTwoUpper H = P ⊔ U := by rw [hO2, hUW]
  have hTI : T ≤ Subgroup.normalizer (I : Set G) := by
    intro t ht
    rw [hIPUV, ← hO2U]
    exact mem_normalizer_sup (le_normalizer_oTwoUpper H (hTH ht)) (hTV ht)
  have hHI : H ≤ Subgroup.normalizer (I : Set G) := by
    rw [hHPT]
    exact sup_le (hPI.trans Subgroup.le_normalizer) hTI
  have hHU : H ≤ Subgroup.normalizer (U : Set G) :=
    hUI ▸ hHI.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 I)
  have hHIT : H = I ⊔ T := by
    refine le_antisymm (hHPT ▸ sup_le_sup_right hPI T) (sup_le ?_ hTH)
    rw [hIPUV]
    exact sup_le (sup_le hPH (hU.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 H)))
      (hVT.trans hTH)

  have hUCP : U ⊓ Subgroup.centralizer (P : Set G) = ⊥ := by
    rw [hPz]
    refine inf_centralizer_eq_bot_of_eq_commutator hUe (hIU (hPI hhP))
      (hord ▸ hp.odd_of_ne_two hp2) ?_
    rw [← hPz, hUW]
    exact hWP

  have hUN : U ≤ Subgroup.normalizer (V : Set G) := by
    have key : ∀ u ∈ U, ∀ x ∈ V, u * x * u⁻¹ ∈ V := by
      intro u hu x hx
      have hc : ⁅u, x⁆ ∈ V := by
        have hc' : ⁅u, x⁆ ∈ ⁅W, V⁆ := Subgroup.commutator_mem_commutator (hUW ▸ hu) hx
        rw [hWV] at hc'
        exact hc'.1
      have e1 : u * x * u⁻¹ = ⁅u, x⁆ * x := by rw [commutatorElement_def]; group
      rw [e1]
      exact V.mul_mem hc hx
    intro u hu
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨key u hu x, fun hx => ?_⟩
    have := key u⁻¹ (U.inv_mem hu) _ hx
    simpa [mul_assoc] using this

  have hCUV : ∀ c ∈ U, c ∈ Subgroup.centralizer (V : Set G) → c ∈ V := by
    intro c hcU hcV
    have hc : c ∈ (U ⊓ V) ⊔ (U ⊓ CFSG.conjugate V h) := hUs ▸ hcU
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup (A := U ⊓ V)
      (B := U ⊓ CFSG.conjugate V h) (fun x hx y hy => hUc x hx.1 y hy.1) hc

    have haC : a ∈ Subgroup.centralizer (V : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun y hy => hVc y hy a ha.2
    have hbC : b ∈ Subgroup.centralizer (V : Set G) := by
      have hb' : b = a⁻¹ * (a * b) := by group
      rw [hb']
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ haC) hcV
    have hbI : I ≤ Subgroup.centralizer ({b} : Set G) := by
      rw [hI]
      refine sup_le (fun y hy => ?_) (fun y hy => ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hbC y hy)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (hVhc _ hy _ hb.2)
    have hbh : h * b * h⁻¹ = b := by
      have := Subgroup.mem_centralizer_singleton_iff.mp (hbI (hPI hhP))
      rw [this, mul_inv_cancel_right]
    have hbV : b ∈ V := by
      have := mem_conjugate_iff.mp hb.2
      rwa [hbh] at this
    have hb1 : b = 1 := by
      have hb0 : b ∈ (U ⊓ V) ⊓ (U ⊓ CFSG.conjugate V h) := ⟨⟨hb.1, hbV⟩, hb⟩
      rw [hUd] at hb0
      exact hb0
    rw [hb1, mul_one]
    exact ha.2

  have hQT : pCoreOf 2 (L ⊔ T) ≤ T :=
    B6.pCoreOf_two_le_of_isSylowTwoOf (isSylowTwoOf_of_quasithinIsSylowTwo hyp.sylow le_sup_right)
  have hQV : pCoreOf 2 (L ⊔ T) ≤ Subgroup.centralizer (V : Set G) :=
    pCoreOf_sup_le_centralizer (le_sup_of_hyp1223 hyp) hred
  have hQU : ⁅pCoreOf 2 (L ⊔ T), U⁆ ≤ U ⊓ V := by
    rw [Subgroup.commutator_le]
    intro q hq u hu
    have hqU : q * u * q⁻¹ ∈ U :=
      (Subgroup.mem_normalizer_iff.mp (hHU (hTH (hQT hq))) u).mp hu
    have hcU : ⁅q, u⁆ ∈ U := by
      rw [commutatorElement_def]
      exact U.mul_mem hqU (U.inv_mem hu)
    refine ⟨hcU, hCUV _ hcU ?_⟩

    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : u⁻¹ * y * u ∈ V := by
      have := (Subgroup.mem_normalizer_iff.mp (hUN (U.inv_mem hu)) y).mp hy
      simpa using this
    have hqy : y * q = q * y := Subgroup.mem_centralizer_iff.mp (hQV hq) y hy
    have hqy' : (u⁻¹ * y * u) * q = q * (u⁻¹ * y * u) :=
      Subgroup.mem_centralizer_iff.mp (hQV hq) _ hy'
    have hqy'' : q⁻¹ * (u⁻¹ * y * u) = (u⁻¹ * y * u) * q⁻¹ := by
      calc q⁻¹ * (u⁻¹ * y * u) = q⁻¹ * ((u⁻¹ * y * u) * q) * q⁻¹ := by group
        _ = q⁻¹ * (q * (u⁻¹ * y * u)) * q⁻¹ := by rw [hqy']
        _ = (u⁻¹ * y * u) * q⁻¹ := by group
    rw [commutatorElement_def]
    calc y * (q * u * q⁻¹ * u⁻¹) = (y * q) * u * q⁻¹ * u⁻¹ := by group
      _ = (q * y) * u * q⁻¹ * u⁻¹ := by rw [hqy]
      _ = q * u * ((u⁻¹ * y * u) * q⁻¹) * u⁻¹ := by group
      _ = q * u * (q⁻¹ * (u⁻¹ * y * u)) * u⁻¹ := by rw [← hqy'']
      _ = q * u * q⁻¹ * u⁻¹ * y := by group
  exact ⟨hUW, hHU, hHI, hIPUV, hHIT, hUCP, hQU⟩

end CFSG.Quasithin.H13
