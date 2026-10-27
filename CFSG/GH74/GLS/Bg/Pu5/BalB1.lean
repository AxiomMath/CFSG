module

public import CFSG.GH74.GLS.Bg.Pu5.BalBL
public import CFSG.GH74.GLS.Balance.Bender.Final
import CFSG.ClassicalInvolution.SolvableCase.SL2Three

public section

namespace CFSG.GH74.GLS.Bg.Pu5

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm2.Recip.BalanceSolv CFSG.GH74.GLS.Bg.Iii2 CFSG.ComponentClassification
  CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement MatrixGroups

section Rank

variable {G : Type} [Group G] [Finite G]

theorem one_le_pRank_of_involution {Λ : Subgroup G} {y : G} (hy : y ∈ Λ) (hy2 : orderOf y = 2) :
    1 ≤ pRank 2 ↥Λ := by
  have hysq : y * y = 1 := mul_self_eq_one_of_orderOf_eq_two hy2
  have hcl : Subgroup.closure ({y, y} : Set G) = Subgroup.zpowers y := by
    simp [Subgroup.zpowers_eq_closure]
  have hEel := isElemAbelian_closure_pair hysq hysq (rfl : y * y = y * y)
  have hcard : Nat.card ↥(Subgroup.closure ({y, y} : Set G)) = 2 ^ 1 := by
    rw [hcl, Nat.card_zpowers, hy2]
    norm_num
  have hle : Subgroup.closure ({y, y} : Set G) ≤ Λ := (Subgroup.closure_le _).2 (by simp [hy])
  rw [TwoThin.pRank_two_subgroup_eq_open]
  exact CFSG.SectionRank.le_pRank one_lt_two hle hEel hcard

theorem pRank_eq_one_of_le {K Λ : Subgroup G} (hΛK : Λ ≤ K) (hK : pRank 2 ↥K = 1) {y : G}
    (hy : y ∈ Λ) (hy2 : orderOf y = 2) : pRank 2 ↥Λ = 1 := by
  have h1 : pRank 2 ↥Λ ≤ pRank 2 ↥K := by
    rw [TwoThin.pRank_two_subgroup_eq_open Λ, TwoThin.pRank_two_subgroup_eq_open K]
    exact CFSG.SectionRank.pRank_mono one_lt_two hΛK
  exact le_antisymm (hK ▸ h1) (one_le_pRank_of_involution hy hy2)

end Rank

section Nonsolv

variable {G : Type} [Group G] [Finite G]

theorem bal1_nonsolv (hBL : BLS) (hG : IsKProperSimple G) {a b : G} (ha : orderOf a = 2)
    (hb : orderOf b = 2) (hab : b ∈ centralizer ({a} : Set G)) {K : Subgroup G}
    (hK : IsRigidRankOneComp a K) (hbN : b ∈ normalizer (K : Set G))
    (hL' : ∃ L' : Subgroup ↥(fixedSubgroup (Hat K) (phi K b hbN)), IsPComponent 2 L') :
    ∃ y ∈ K, orderOf y = 2 ∧ y ∈ centralizer ({b} : Set G) ∧
      ∀ L : Subgroup G, IsRigidRankOneComp b L → y ∈ cSec L := by
  obtain ⟨L', hL'⟩ := hL'
  have hKC : IsPCompIn 2 (centralizer ({a} : Set G)) K := rr_pcomp hK
  set X : Subgroup G := K ⊓ centralizer ({b} : Set G) with hX
  have hL'2 : TwoComponents.IsTwoComponent L' := (CatalogueBAlternating.pComponent_two_iff L').mp hL'
  obtain ⟨Λz, hΛz, hΛzmap⟩ := OddKernelTwoComponents.exists_lift (fixedRestrict K hbN)
    (fixedRestrict_surjective K hb hbN) (odd_card_ker_fixedRestrict K hbN) L' hL'2
  set Λ : Subgroup G := Λz.map X.subtype with hΛdef
  have hΛX : Λ ≤ X := Subgroup.map_subtype_le Λz
  have hsub : Λ.subgroupOf X = Λz :=
    Subgroup.comap_map_eq_self_of_injective X.subtype_injective Λz
  have hΛpc : IsPCompIn 2 X Λ := TwoThin.isPCompIn_two_iff.mpr ⟨hΛX, by rw [hsub]; exact hΛz⟩
  have hΛW : IsPCompIn 2 (centralizer ({a} : Set G) ⊓ centralizer ({b} : Set G)) Λ := by
    set W := centralizer ({a} : Set G) ⊓ centralizer ({b} : Set G) with hW
    have hXW : X ≤ W := le_inf ((inf_le_left : X ≤ K).trans hKC.1) inf_le_right
    refine TwoThin.isPCompIn_two_iff.mpr ⟨hΛX.trans hXW, ?_⟩
    have hKsub : (K.subgroupOf (centralizer ({a} : Set G))).IsSubnormal :=
      Components.mathlib_subnormal_of_chain (TwoThin.isPCompIn_two_iff.mp hKC).2.1
        Subgroup.IsSubnormal.top
    have hsubW : (X.subgroupOf W).IsSubnormal := by
      have h1 := TwoThin.isSubnormal_inf_subgroupOf hKsub (inf_le_left : W ≤ centralizer ({a} : Set G))
      have h2 : X.subgroupOf W = K.subgroupOf W := by
        ext c
        simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, hX]
        exact ⟨fun h => h.1, fun h => ⟨h, (Subgroup.mem_inf.mp c.2).2⟩⟩
      rwa [h2]
    exact TwoComponentTransport.extend_nested Λ _ W hΛX hXW hsubW (TwoThin.isPCompIn_two_iff.mp hΛpc).2
  obtain ⟨u, huΛz, hu2⟩ := exists_involution_of_isPComponent
    ((CatalogueBAlternating.pComponent_two_iff Λz).mpr hΛz)
  have hyΛ : (u : G) ∈ Λ := ⟨u, huΛz, rfl⟩
  have hy2 : orderOf (u : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hu2
  have hΛK : Λ ≤ K := hΛX.trans inf_le_left
  have hrank : pRank 2 ↥Λ = 1 := pRank_eq_one_of_le hΛK hK.2 hyΛ hy2
  exact ⟨u, hΛK hyΛ, hy2, (Subgroup.mem_inf.mp (hΛX hyΛ)).2,
    fun L hL => hBL G hG a b ha hb hab Λ hΛW hrank u hyΛ hy2 L hL⟩

end Nonsolv

section Solv

theorem exists_solvTwoComp_of_fixed_comp {G : Type} [Group G] [Finite G] {x y : G}
    (hxy : Commute x y) {L : Subgroup G} (hLC : IsPCompIn 2 (centralizer ({x} : Set G)) L)
    (hy : orderOf y = 2) (hyN : y ∈ normalizer (L : Set G))
    (hsolv : HasSolvableTwoComponentSL23 ↥(fixedSubgroup (↥L ⧸ pPrimeCore 2 ↥L)
      (inducedQuotAut L (pPrimeCore 2 ↥L) ⟨y, hyN⟩))) :
    ∃ (V : Subgroup ↥(centralizer ({y} : Set G))) (v : ↥(centralizer ({y} : Set G))),
      Balance.IsSolvTwoCompSL23In
        (centralizer ({Balance.xC hxy} : Set ↥(centralizer ({y} : Set G)))) V ∧
        v ∈ V ∧ orderOf v = 2 ∧ (v : G) ∈ L := by
  classical
  have hLCx : L ≤ centralizer ({x} : Set G) := hLC.1
  have hLsub : (L.subgroupOf (centralizer ({x} : Set G))).IsSubnormal := by
    obtain ⟨-, -, hsub, -⟩ := hLC.2
    exact hsub
  set Cy : Subgroup G := centralizer ({y} : Set G) with hCy
  set x' : ↥Cy := Balance.xC hxy with hx'
  set C' : Subgroup ↥Cy := centralizer ({x'} : Set ↥Cy) with hC'
  set Hg : Subgroup (Hat L) := fixedSubgroup (Hat L) (phi L y hyN) with hHg
  set q : ↥Hg →* ↥Hg ⧸ pPrimeCore 2 ↥Hg := QuotientGroup.mk' (pPrimeCore 2 ↥Hg) with hq
  obtain ⟨W, hWsub, ⟨eW⟩⟩ := (Balance.hasSolvableTwoComponentSL23_iff _).mp hsolv
  let f : ↥C' →* ↥(centralizer ({x} : Set G)) :=
    (Cy.subtype.comp C'.subtype).codRestrict (centralizer ({x} : Set G)) (fun g => by
      have h1 := mem_centralizer_singleton_iff.mp g.2
      have h2 := congrArg Subtype.val h1
      exact mem_centralizer_singleton_iff.mpr h2)
  set U : Subgroup ↥C' := (L.subgroupOf (centralizer ({x} : Set G))).comap f with hU
  have hUsub : U.IsSubnormal := hLsub.comap f
  have hmemU : ∀ u : ↥C', u ∈ U ↔ (((u : ↥Cy)) : G) ∈ L := fun u => Iff.rfl
  let j : ↥U →* ↥(L ⊓ Cy) :=
    ((Cy.subtype.comp C'.subtype).comp U.subtype).codRestrict (L ⊓ Cy) (fun u =>
      ⟨(hmemU _).mp u.2, ((u : ↥C') : ↥Cy).2⟩)
  have hjinj : Function.Injective j := by
    intro a b hab
    have h : (((j a : ↥(L ⊓ Cy)) : G)) = ((j b : ↥(L ⊓ Cy)) : G) := congrArg Subtype.val hab
    exact Subtype.ext (Subtype.ext (Subtype.ext h))
  have hjsurj : Function.Surjective j := by
    rintro ⟨a, haL, haCy⟩
    have hax : a * x = x * a := mem_centralizer_singleton_iff.mp (hLCx haL)
    have hC'mem : (⟨a, haCy⟩ : ↥Cy) ∈ C' := by
      rw [hC', mem_centralizer_singleton_iff]
      exact Subtype.ext hax
    exact ⟨⟨⟨⟨a, haCy⟩, hC'mem⟩, haL⟩, rfl⟩
  let r : ↥(L ⊓ Cy) →* ↥Hg := fixedRestrict L hyN
  have hrsurj : Function.Surjective r := fixedRestrict_surjective L hy hyN
  have hrodd : Odd (Nat.card r.ker) := odd_card_ker_fixedRestrict L hyN
  let ψ : ↥U →* ↥Hg ⧸ pPrimeCore 2 ↥Hg := q.comp (r.comp j)
  have hqsurj : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hψsurj : Function.Surjective ψ := hqsurj.comp (hrsurj.comp hjsurj)
  have hjker : Odd (Nat.card j.ker) := by
    rw [(MonoidHom.ker_eq_bot_iff j).mpr hjinj, Subgroup.card_bot]
    exact odd_one
  have hrjodd : Odd (Nat.card (r.comp j).ker) := Balance.odd_card_ker_comp j r hjsurj hjker hrodd
  have hqker : Odd (Nat.card q.ker) := by
    rw [hq, QuotientGroup.ker_mk']
    exact TwoThin.odd_card_pPrimeCore _
  have hψodd : Odd (Nat.card ψ.ker) :=
    Balance.odd_card_ker_comp (r.comp j) q (hrsurj.comp hjsurj) hrjodd hqker
  have hψker : ∀ u : ↥U, ψ u = 1 → ((u : ↥C') : ↥C') ∈ pPrimeCore 2 ↥C' := by
    intro u hu
    have hle : ψ.ker ≤ pPrimeCore 2 ↥U :=
      le_sSup ⟨inferInstance, Nat.coprime_two_left.mpr hψodd⟩
    have hmem : u ∈ pPrimeCore 2 ↥U := hle (MonoidHom.mem_ker.mpr hu)
    exact CFSG.Walter.map_pPrimeCore_le_of_isSubnormal hUsub ⟨u, hmem, rfl⟩
  set Vt : Subgroup ↥C' := (W.comap ψ).map U.subtype with hVt
  have hVtsub : Vt.IsSubnormal := by
    refine Subgroup.IsSubnormal.trans (Subgroup.map_subtype_le _) ?_ hUsub
    have h1 : (Vt.subgroupOf U) = W.comap ψ :=
      Subgroup.comap_map_eq_self_of_injective U.subtype_injective _
    rw [h1]
    exact hWsub.comap ψ
  let eV : ↥(W.comap ψ) ≃* ↥Vt := (W.comap ψ).equivMapOfInjective U.subtype U.subtype_injective
  let χ : ↥Vt →* SL(2, ZMod 3) :=
    eW.toMonoidHom.comp ((ψ.subgroupComap W).comp eV.symm.toMonoidHom)
  have hχsurj : Function.Surjective χ := by
    intro s
    obtain ⟨w, hw⟩ := eW.surjective s
    obtain ⟨u, hu⟩ := hψsurj (w : ↥Hg ⧸ pPrimeCore 2 ↥Hg)
    refine ⟨eV ⟨u, by rw [Subgroup.mem_comap, hu]; exact w.2⟩, ?_⟩
    show eW ((ψ.subgroupComap W) (eV.symm (eV _))) = s
    rw [MulEquiv.symm_apply_apply, ← hw]
    congr 1
    exact Subtype.ext hu
  have hχker : ∀ n : ↥Vt, χ n = 1 → (n : ↥C') ∈ pPrimeCore 2 ↥C' := by
    intro n hn
    have h1 : (ψ.subgroupComap W) (eV.symm n) = 1 := eW.map_eq_one_iff.mp hn
    have h2 : ψ ((eV.symm n : ↥(W.comap ψ)) : ↥U) = 1 := by
      have := congrArg Subtype.val h1
      exact this
    have h3 := hψker _ h2
    have h4 : (n : ↥C') = (((eV.symm n : ↥(W.comap ψ)) : ↥U) : ↥C') := by
      conv_lhs => rw [← eV.apply_symm_apply n]
      rfl
    rw [h4]
    exact h3
  have hV := Balance.isSolvTwoCompSL23_of_subnormal Vt hVtsub χ hχsurj hχker
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardVt : 2 ∣ Nat.card ↥Vt := by
    have h1 := Subgroup.card_ker_mul_card_of_surjective hχsurj
    rw [CFSG.ClassicalInvolution.natCard_sl2Three] at h1
    exact ⟨Nat.card χ.ker * 12, by rw [← h1]; ring⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥Vt) 2 hcardVt
  have htmem : (t : ↥C') ∈ Vt := t.2
  obtain ⟨u, hu, hut⟩ := htmem
  refine ⟨(Vt ⊔ pPrimeCore 2 ↥C').map C'.subtype, (t : ↥C').1, ⟨Subgroup.map_subtype_le _, ?_⟩,
    ⟨(t : ↥C'), Subgroup.mem_sup_left t.2, rfl⟩, ?_, ?_⟩
  · rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective C'.subtype_injective]
    exact hV
  · have : orderOf ((t : ↥C') : ↥Cy) = 2 := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
      exact ht
    exact this
  · have hu' : (((u : ↥C') : ↥Cy) : G) ∈ L := (hmemU _).mp u.2
    have : (t : ↥C') = (u : ↥C') := hut.symm
    rw [this]
    exact hu'

end Solv


section SolvCase

variable {G : Type} [Group G] [Finite G]

theorem bal1_solv (h44 : II4_44) (hG : IsKProperSimple G) {a b : G} (ha : orderOf a = 2)
    (hb : orderOf b = 2) (hab : b ∈ centralizer ({a} : Set G)) {K : Subgroup G}
    (hK : IsRigidRankOneComp a K) (hbN : b ∈ normalizer (K : Set G))
    (hsolv : HasSolvableTwoComponentSL23 ↥(fixedSubgroup (Hat K) (phi K b hbN))) :
    ∃ y ∈ K, orderOf y = 2 ∧ y ∈ centralizer ({b} : Set G) ∧
      ∀ L : Subgroup G, IsRigidRankOneComp b L → y ∈ cSec L := by
  have hxy : Commute a b := (Subgroup.mem_centralizer_singleton_iff.mp hab).symm
  have hKC : IsPCompIn 2 (centralizer ({a} : Set G)) K := rr_pcomp hK
  obtain ⟨V, v, hV, hvV, hv2, hvK⟩ := exists_solvTwoComp_of_fixed_comp hxy hKC hb hbN hsolv
  have ha' : orderOf (Balance.xC hxy) = 2 := by
    rw [Balance.xC, Subgroup.orderOf_mk]
    exact ha
  have hv2' : orderOf (v : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hv2
  have hvres : v ∈ oPrimeResidualOf 2 V :=
    Balance.mem_oPrimeResidualOf_of_sq hvV (by
      have := pow_orderOf_eq_one v
      rwa [hv2] at this)
  refine ⟨(v : G), hvK, hv2', v.2, fun R hR => ?_⟩
  rcases Balance.solvableL2PrimeBalance_proved ↥(centralizer ({b} : Set G)) (Balance.xC hxy) ha' V hV
    with h1 | ⟨L', hL', -, hRL'⟩
  · exact O22_le_cSec (rr_pcomp hR) ⟨v, h1 hvres, rfl⟩
  · have hM : IsPCompIn 2 (centralizer ({b} : Set G)) (L'.map (centralizer ({b} : Set G)).subtype) := by
      refine ⟨Subgroup.map_subtype_le _, ?_⟩
      have e : (L'.map (centralizer ({b} : Set G)).subtype).subgroupOf (centralizer ({b} : Set G)) =
          L' := Subgroup.comap_map_eq_self_of_injective (centralizer ({b} : Set G)).subtype_injective L'
      rw [e]
      exact hL'
    have hvM : (v : G) ∈ L'.map (centralizer ({b} : Set G)).subtype := ⟨v, hRL' hvres, rfl⟩
    by_cases hMR : L'.map (centralizer ({b} : Set G)).subtype = R
    · rw [hMR] at hvM
      exact rr_inv_mem_cSec h44 hG hR hvM hv2'
    · exact le_cSec_of_ne hM (rr_pcomp hR) hMR hvM

end SolvCase

theorem bal1_of (h44 : II4_44) : Bal1S := by
  intro G _ _ hG a b ha hb hab K hK hbN hF
  obtain ⟨hbN', hF'⟩ := hF
  obtain ⟨-, -, -, -, hcomp | hsolv⟩ := hF'
  · exact bal1_nonsolv (bl_of h44) hG ha hb hab hK hbN' hcomp
  · exact bal1_solv h44 hG ha hb hab hK hbN' hsolv

end CFSG.GH74.GLS.Bg.Pu5
