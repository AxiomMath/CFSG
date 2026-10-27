module

public import CFSG.GH74.GLS.Balance.OResidual
public import CFSG.GH74.GLS.Balance.Defs
public import CFSG.GH74.GLS.TwoThin.Struct

public section

namespace CFSG.GH74.GLS.Balance

open Subgroup CFSG CFSG.GH74.GLS
open scoped commutatorElement MatrixGroups


theorem odd_card_of_forall_odd_orderOf {G : Type*} [Group G] [Finite G] (H : Subgroup G)
    (h : ∀ g ∈ H, Odd (orderOf g)) : Odd (Nat.card H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hnot
  have h2 : 2 ∣ Nat.card H := by
    rcases Nat.even_or_odd (Nat.card H) with h' | h'
    · exact even_iff_two_dvd.mp h'
    · exact absurd h' hnot
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := H) 2 h2
  have := h g g.2
  rw [Subgroup.orderOf_coe, hg] at this
  exact absurd this (by decide)

theorem map_pPrimeCore_eq {Y Y' : Type*} [Group Y] [Group Y'] [Finite Y] [Finite Y']
    (f : Y →* Y') (hf : Function.Surjective f) (hodd : Odd (Nat.card f.ker)) :
    (pPrimeCore 2 Y).map f = pPrimeCore 2 Y' ∧ f.ker ≤ pPrimeCore 2 Y := by
  have hkerle : f.ker ≤ pPrimeCore 2 Y :=
    le_sSup ⟨inferInstance, Nat.coprime_two_left.mpr hodd⟩
  refine ⟨le_antisymm ?_ ?_, hkerle⟩
  ·
    have hn : ((pPrimeCore 2 Y).map f).Normal := Subgroup.Normal.map inferInstance f hf
    have hodd1 : Odd (Nat.card (pPrimeCore 2 Y)) := TwoThin.odd_card_pPrimeCore Y
    have hodd2 : Odd (Nat.card ((pPrimeCore 2 Y).map f)) :=
      Odd.of_dvd_nat hodd1 (Subgroup.card_map_dvd _ _)
    exact le_sSup ⟨hn, Nat.coprime_two_left.mpr hodd2⟩
  ·
    have hodd' : Odd (Nat.card (pPrimeCore 2 Y')) := TwoThin.odd_card_pPrimeCore Y'
    have hpre : (pPrimeCore 2 Y').comap f ≤ pPrimeCore 2 Y := by
      have hn : ((pPrimeCore 2 Y').comap f).Normal := Subgroup.Normal.comap inferInstance f
      have hoddpre : Odd (Nat.card ((pPrimeCore 2 Y').comap f)) := by
        apply odd_card_of_forall_odd_orderOf
        intro g hg
        have hg' : f g ∈ pPrimeCore 2 Y' := hg
        have h1 : Odd (orderOf (f g)) := by
          exact Odd.of_dvd_nat hodd' (Subgroup.orderOf_dvd_natCard (pPrimeCore 2 Y') hg')
        have hker : g ^ orderOf (f g) ∈ f.ker := by
          rw [MonoidHom.mem_ker, map_pow, pow_orderOf_eq_one]
        have h2 : Odd (orderOf (g ^ orderOf (f g))) := by
          exact Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard f.ker hker)
        have hdvd : orderOf g ∣ orderOf (f g) * orderOf (g ^ orderOf (f g)) := by
          apply orderOf_dvd_of_pow_eq_one
          rw [pow_mul, pow_orderOf_eq_one]
        exact Odd.of_dvd_nat (h1.mul h2) hdvd
      exact le_sSup ⟨hn, Nat.coprime_two_left.mpr hoddpre⟩
    intro y hy
    obtain ⟨g, rfl⟩ := hf y
    exact ⟨g, hpre (show g ∈ (pPrimeCore 2 Y').comap f from hy), rfl⟩

theorem isSolvTwoCompSL23_map {Y Y' : Type*} [Group Y] [Group Y'] [Finite Y] [Finite Y']
    (f : Y →* Y') (hf : Function.Surjective f) (hodd : Odd (Nat.card f.ker))
    {V' : Subgroup Y} (hV : IsSolvTwoCompSL23 Y V') : IsSolvTwoCompSL23 Y' (V'.map f) := by
  obtain ⟨W, hWsub, ⟨eW⟩, hVW⟩ := hV
  obtain ⟨hmapO, hkerO⟩ := map_pPrimeCore_eq f hf hodd
  set g : Y →* Y' ⧸ pPrimeCore 2 Y' := (QuotientGroup.mk' (pPrimeCore 2 Y')).comp f with hg
  have hgs : Function.Surjective g := (QuotientGroup.mk'_surjective _).comp hf
  have hgker : g.ker = pPrimeCore 2 Y := by
    apply le_antisymm
    · intro y hy
      have : f y ∈ pPrimeCore 2 Y' := by
        have := (MonoidHom.mem_ker.mp hy)
        exact (QuotientGroup.eq_one_iff _).mp this
      rw [← hmapO] at this
      obtain ⟨o, ho, hoe⟩ := this
      have : y * o⁻¹ ∈ f.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hoe]; group
      have h2 : y * o⁻¹ ∈ pPrimeCore 2 Y := hkerO this
      have := mul_mem h2 ho
      simpa using this
    · intro y hy
      rw [MonoidHom.mem_ker]
      show (QuotientGroup.mk' (pPrimeCore 2 Y')) (f y) = 1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ← hmapO]
      exact ⟨y, hy, rfl⟩
  let ψ : (Y ⧸ pPrimeCore 2 Y) ≃* (Y' ⧸ pPrimeCore 2 Y') :=
    (QuotientGroup.quotientMulEquivOfEq hgker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective g hgs)
  have hψ : ∀ y : Y, ψ (QuotientGroup.mk y) = QuotientGroup.mk (f y) := fun y => rfl
  refine ⟨W.map ψ.toMonoidHom, hWsub.map ψ.surjective,
    ⟨((W.equivMapOfInjective ψ.toMonoidHom ψ.injective).symm.trans eW)⟩, ?_⟩
  ext y'
  constructor
  · rintro ⟨v, hv, rfl⟩
    have hv' : (QuotientGroup.mk' (pPrimeCore 2 Y)) v ∈ W := by
      rw [← Subgroup.mem_comap, ← hVW]; exact hv
    refine ⟨_, hv', ?_⟩
    exact hψ v
  · intro hy
    obtain ⟨y, rfl⟩ := hf y'
    obtain ⟨w, hw, hwe⟩ := hy
    have : QuotientGroup.mk' (pPrimeCore 2 Y) y = w := by
      apply ψ.injective
      have h1 : ψ w = QuotientGroup.mk (f y) := hwe
      rw [h1]; exact (hψ y).symm
    have hyV : y ∈ V' := by
      rw [hVW]
      exact (show (QuotientGroup.mk' (pPrimeCore 2 Y)) y ∈ W by rw [this]; exact hw)
    exact ⟨y, hyV, rfl⟩

theorem centralizer_zpowers_eq {X : Type*} [Group X] (x : X) :
    centralizer ((zpowers x : Subgroup X) : Set X) = centralizer ({x} : Set X) := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

theorem centralizer_quotient_eq {X : Type} [Group X] [Finite X] {x : X} (hx : orderOf x = 2) :
    centralizer ({QuotientGroup.mk' (pPrimeCore 2 X) x} : Set (X ⧸ pPrimeCore 2 X)) =
      (centralizer ({x} : Set X)).map (QuotientGroup.mk' (pPrimeCore 2 X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA : IsPGroup 2 (zpowers x) := by
    rw [IsPGroup.iff_card, Nat.card_zpowers, hx]; exact ⟨1, by norm_num⟩
  have : Fact (IsPGroup 2 ↥(zpowers x)) := ⟨hA⟩
  have hcop : Nat.Coprime 2 (Nat.card (pPrimeCore 2 X)) :=
    Nat.coprime_two_left.mpr (TwoThin.odd_card_pPrimeCore X)
  have h := CFSG.centralizer_map_quotient_eq_map_centralizer 2 (zpowers x) (pPrimeCore 2 X)
    inferInstance hcop
  simp only at h
  rw [MonoidHom.map_zpowers, centralizer_zpowers_eq, centralizer_zpowers_eq] at h
  simpa using h

theorem pPrimeCore_le_of_isSolvTwoCompSL23 {Y : Type*} [Group Y] {V' : Subgroup Y}
    (hV : IsSolvTwoCompSL23 Y V') : pPrimeCore 2 Y ≤ V' := by
  obtain ⟨W, -, -, hVW⟩ := hV
  intro y hy
  rw [hVW]
  show (QuotientGroup.mk' (pPrimeCore 2 Y)) y ∈ W
  have h1 : (QuotientGroup.mk' (pPrimeCore 2 Y)) y = 1 := (QuotientGroup.eq_one_iff y).mpr hy
  rw [h1]
  exact W.one_mem

theorem isSolvTwoCompSL23In_quotient {X : Type} [Group X] [Finite X] {x : X} (hx : orderOf x = 2)
    {V : Subgroup X} (hV : IsSolvTwoCompSL23In (centralizer ({x} : Set X)) V) :
    IsSolvTwoCompSL23In
      (centralizer ({QuotientGroup.mk' (pPrimeCore 2 X) x} : Set (X ⧸ pPrimeCore 2 X)))
      (V.map (QuotientGroup.mk' (pPrimeCore 2 X))) := by
  set N : Subgroup X := pPrimeCore 2 X with hN
  set q : X →* X ⧸ N := QuotientGroup.mk' N with hq
  set C : Subgroup X := centralizer ({x} : Set X) with hC
  set C' : Subgroup (X ⧸ N) := centralizer ({q x} : Set (X ⧸ N)) with hC'
  have hC'eq : C' = C.map q := centralizer_quotient_eq hx
  obtain ⟨hVC, hsolv⟩ := hV
  have hNodd : Odd (Nat.card N) := TwoThin.odd_card_pPrimeCore X
  have hVq : V.map q ≤ C' := by rw [hC'eq]; exact Subgroup.map_mono hVC
  refine ⟨hVq, ?_⟩
  let f : ↥C →* ↥C' := (q.comp C.subtype).codRestrict C' (fun c => by
    rw [hC'eq]; exact ⟨c, c.2, rfl⟩)
  have hfv : ∀ c : ↥C, ((f c : ↥C') : X ⧸ N) = q c := fun c => rfl
  have hf_surj : Function.Surjective f := by
    rintro ⟨y, hy⟩
    rw [hC'eq] at hy
    obtain ⟨c, hc, rfl⟩ := hy
    exact ⟨⟨c, hc⟩, Subtype.ext rfl⟩
  have hf_odd : Odd (Nat.card f.ker) := by
    have hinj : Function.Injective
        (((C.subtype.comp f.ker.subtype).codRestrict N (fun c => by
          have h1 : f (c : ↥C) = 1 := c.2
          have h2 := congrArg Subtype.val h1
          change q (c : ↥C) = 1 at h2
          exact (QuotientGroup.eq_one_iff _).1 h2)) : f.ker →* N) := by
      intro a b hab
      have h1 := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext h1)
    exact Odd.of_dvd_nat hNodd (Subgroup.card_dvd_of_injective _ hinj)
  have h1 := isSolvTwoCompSL23_map f hf_surj hf_odd hsolv
  have hO : pPrimeCore 2 ↥C ≤ V.subgroupOf C := pPrimeCore_le_of_isSolvTwoCompSL23 hsolv
  have e : (V.subgroupOf C).map f = (V.map q).subgroupOf C' := by
    ext c'
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨c, hc, rfl⟩
    · intro hc'
      obtain ⟨c, rfl⟩ := hf_surj c'
      obtain ⟨v, hv, hvq⟩ := hc'
      refine ⟨c, ?_, rfl⟩
      have hvc : q v = q c := hvq
      have hn : v⁻¹ * (c : X) ∈ N := (QuotientGroup.eq).mp hvc
      have hvC : v ∈ C := hVC hv
      have hnC : v⁻¹ * (c : X) ∈ C := C.mul_mem (C.inv_mem hvC) c.2
      have hnO : (⟨v⁻¹ * (c : X), hnC⟩ : ↥C) ∈ pPrimeCore 2 ↥C := by
        have hnorm : (N.subgroupOf C).Normal := Subgroup.normal_subgroupOf
        have hodd' : Odd (Nat.card (N.subgroupOf C)) := by
          have e' : Nat.card (N.subgroupOf C) ∣ Nat.card N :=
            Subgroup.card_dvd_of_injective
              ((C.subtype.comp (N.subgroupOf C).subtype).codRestrict N (fun c => c.2))
              (by
                intro a b hab
                have h1 := congrArg Subtype.val hab
                exact Subtype.ext (Subtype.ext h1))
          exact Odd.of_dvd_nat hNodd e'
        have : N.subgroupOf C ≤ pPrimeCore 2 ↥C :=
          le_sSup ⟨hnorm, Nat.coprime_two_left.mpr hodd'⟩
        exact this hn
      have hnV : (⟨v⁻¹ * (c : X), hnC⟩ : ↥C) ∈ V.subgroupOf C := hO hnO
      have hnV' : v⁻¹ * (c : X) ∈ V := hnV
      have : (c : X) = v * (v⁻¹ * (c : X)) := by group
      show (c : X) ∈ V
      rw [this]
      exact V.mul_mem hv hnV'
  rw [← e]
  exact h1

theorem solvableL2PrimeBalance_of_core
    (core : ∀ (X : Type) [Group X] [Finite X], pPrimeCore 2 X = ⊥ → ∀ x : X, orderOf x = 2 →
      ∀ V : Subgroup X, IsSolvTwoCompSL23In (centralizer ({x} : Set X)) V →
        oPrimeResidualOf 2 V ≤ pCore 2 X ∨
          ∃ K : Subgroup X, IsComponent K ∧ x ∈ normalizer (K : Set X) ∧
            oPrimeResidualOf 2 V ≤ K) :
    SolvableL2PrimeBalance := by
  intro X _ _ x hx V hV
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup X := pPrimeCore 2 X with hN
  set q : X →* X ⧸ N := QuotientGroup.mk' N with hq
  have hqs : Function.Surjective q := QuotientGroup.mk'_surjective N
  have hNodd : Odd (Nat.card N) := TwoThin.odd_card_pPrimeCore X
  have hqodd : Odd (Nat.card q.ker) := by rw [hq, QuotientGroup.ker_mk']; exact hNodd
  have hxq : orderOf (q x) = 2 := by
    have hx1 : q x ≠ 1 := by
      intro h1
      have : x ∈ N := (QuotientGroup.eq_one_iff x).mp h1
      have := Subgroup.orderOf_dvd_natCard N this
      rw [hx] at this
      exact absurd (Odd.of_dvd_nat hNodd this) (by decide)
    have hx2 : q x ^ 2 = 1 := by
      have h2 : x ^ 2 = 1 := by
        have := pow_orderOf_eq_one x
        rwa [hx] at this
      rw [← map_pow, h2, map_one]
    exact orderOf_eq_prime hx2 hx1
  have hVq := isSolvTwoCompSL23In_quotient hx hV
  have hcore := core (X ⧸ N) (CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 2) (q x) hxq (V.map q) hVq
  have hRq := map_oPrimeResidualOf_le q V
  rcases hcore with h | ⟨K', hK', hxK', hRK'⟩
  · left
    intro r hr
    exact h (hRq ⟨r, hr, rfl⟩)
  · right
    have hcorefree : pPrimeCore 2 (X ⧸ N) = ⊥ := CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 2
    have hnot : ¬ K' ≤ pPrimeCore 2 (X ⧸ N) := by
      rw [hcorefree]
      exact LocalAnalysis.ComponentInitial.not_le_of_isComponent_of_isSolvable hK' inferInstance
    have hK'p : IsPComponent 2 K' :=
      LocalAnalysis.ComponentInitial.isPComponent_of_isComponent_of_not_le 2 hK' hnot
    have hK'2 := (ComponentClassification.CatalogueBAlternating.pComponent_two_iff K').1 hK'p
    obtain ⟨K, hK2, hKq⟩ := ComponentClassification.OddKernelTwoComponents.exists_lift q hqs hqodd
      K' hK'2
    have hKp : IsPComponent 2 K :=
      (ComponentClassification.CatalogueBAlternating.pComponent_two_iff K).2 hK2
    have hKconj : K.map (MulAut.conj x).toMonoidHom = K := by
      have hK1p : IsPComponent 2 (K.map (MulAut.conj x).toMonoidHom) :=
        LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2 (MulAut.conj x) hKp
      have hK1 := (ComponentClassification.CatalogueBAlternating.pComponent_two_iff _).1 hK1p
      refine ComponentClassification.OddKernelTwoComponents.lift_unique q hqs hqodd _ K hK1 hK2 ?_
      have hxK'm : (K'.map (MulAut.conj (q x)).toMonoidHom) = K' := by
        ext y
        constructor
        · rintro ⟨k, hk, rfl⟩
          exact (mem_normalizer_iff.mp hxK' k).mp hk
        · intro hy
          refine ⟨(q x)⁻¹ * y * (q x), ?_, ?_⟩
          · have := (mem_normalizer_iff.mp ((normalizer (K' : Set (X ⧸ N))).inv_mem hxK') y).mp hy
            rw [inv_inv] at this
            exact this
          · show q x * ((q x)⁻¹ * y * q x) * (q x)⁻¹ = y
            group
      have hcomm : q.comp (MulAut.conj x).toMonoidHom =
          (MulAut.conj (q x)).toMonoidHom.comp q := by
        ext k
        simp [MulAut.conj_apply]
      rw [Subgroup.map_map, hcomm, ← Subgroup.map_map, hKq, hxK'm]
    refine ⟨K, hKp, mem_normalizer_of_map_conj_eq hKconj, ?_⟩
    apply oPrimeResidualOf_le_of_two_elements
    intro r hr hr2
    have hqr : q r ∈ oPrimeResidualOf 2 (V.map q) :=
      hRq ⟨r, mem_oPrimeResidualOf_of_two_element hr hr2, rfl⟩
    have hqrK' : q r ∈ K' := hRK' hqr
    have hY : r ∈ (K.map q).comap q := by rw [hKq]; exact hqrK'
    have hres := ComponentClassification.OddKernelTwoComponents.lift_subgroupOf_eq_residual q hqs
      hqodd K hK2
    have : (⟨r, hY⟩ : ↥((K.map q).comap q)) ∈ ComponentClassification.TwoResidual.subgroup
        ↥((K.map q).comap q) := by
      obtain ⟨k, hk⟩ := hr2
      have hk' : (⟨r, hY⟩ : ↥((K.map q).comap q)) ^ (2 ^ k) = 1 := Subtype.ext (by simpa using hk)
      have h2g : IsPGroup 2 (zpowers (⟨r, hY⟩ : ↥((K.map q).comap q))) := by
        rw [IsPGroup.iff_card, Nat.card_zpowers]
        obtain ⟨j, -, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk')
        exact ⟨j, hj'⟩
      exact ComponentClassification.TwoResidual.twoSubgroup_le _ h2g (Subgroup.mem_zpowers _)
    rw [← hres] at this
    exact this


end CFSG.GH74.GLS.Balance
