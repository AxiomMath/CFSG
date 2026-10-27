module

public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Local.CyclicCentralizerFactorRestriction
import CFSG.FeitThompson.Local.ElementaryMaximalPLengthOneConstraint
import CFSG.FeitThompson.Local.CriticalRegularComplementFixedPoints
import CFSG.FeitThompson.Local.ControlledNormalElementaryPlane
import CFSG.FeitThompson.Local.MaximalPlaneCommonCyclicFactor
import CFSG.FeitThompson.Local.AbelianPlaneCentralizerNoncentralOrbit
import CFSG.FeitThompson.Local.FrattiniArgumentNormalSylow
import CFSG.FeitThompson.Foundations.SolvableHallExistence
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.Star
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type*} [Group G] {p : ℕ}

theorem isCyclic_map {H : Type*} [Group H] {f : H →* G} (hf : Function.Injective f)
    {U : Subgroup H} (h : IsCyclic ↥U) : IsCyclic ↥(U.map f) :=
  isCyclic_of_surjective (Subgroup.equivMapOfInjective U f hf)
    (Subgroup.equivMapOfInjective U f hf).surjective

theorem isInternalDirectProduct_map {H : Type*} [Group H] {f : H →* G}
    (hf : Function.Injective f) {W U V : Subgroup H} (h : IsInternalDirectProduct W U V) :
    IsInternalDirectProduct (W.map f) (U.map f) (V.map f) where
  left_le := Subgroup.map_mono h.left_le
  right_le := Subgroup.map_mono h.right_le
  coe_eq_mul := by
    rw [Subgroup.coe_map, Subgroup.coe_map, Subgroup.coe_map, h.coe_eq_mul, Set.image_mul]
  inf_eq_bot := by rw [← Subgroup.map_inf _ _ _ hf, h.inf_eq_bot, Subgroup.map_bot]
  commutator_eq_bot := by rw [← Subgroup.map_commutator, h.commutator_eq_bot, Subgroup.map_bot]

theorem exists_mulEquiv_pi_of_isElementaryAbelianSubgroup [Finite G] (hp : p.Prime)
    {B : Subgroup G} (hB : IsElementaryAbelianSubgroup p B) :
    ∃ d : ℕ, Nonempty (↥B ≃* (Fin d → Multiplicative (ZMod p))) := by
  have := Fact.mk hp
  obtain ⟨d, hd⟩ := hB.isPGroup.exists_card_eq
  have : IsMulCommutative ↥B := hB.isMulCommutative
  let _ : CommGroup ↥B := IsMulCommutative.instCommGroup
  exact ⟨d, nonempty_mulEquiv_pi_of_exponent hp (fun x => Subtype.ext (hB.pow_eq_one x.1 x.2)) hd⟩

theorem isElementaryAbelianSubgroup_of_mulEquiv {d : ℕ} {A : Subgroup G}
    (f : ↥A ≃* (Fin d → Multiplicative (ZMod p))) :
    IsElementaryAbelianSubgroup p A ∧ Nat.card A = p ^ d := by
  refine ⟨isElementaryAbelianSubgroup_iff.2 ⟨IsMulCommutative.of_comm fun a b =>
    f.injective (by simpa using mul_comm (f a) (f b)), fun x hx => ?_⟩, ?_⟩
  · have h : (⟨x, hx⟩ : A) ^ p = 1 :=
      f.injective (by rw [map_pow, pow_eq_one_pi_multiplicative_zmod, map_one])
    exact congrArg (Subgroup.subtype A) h
  · rw [Nat.card_congr f.toEquiv, card_pi_multiplicative_zmod]

theorem maximal_isElementaryAbelianSubgroup_of_forall [Finite G] (hp : p.Prime) {A : Subgroup G}
    (hA : IsElementaryAbelianSubgroup p A)
    (hmax : ∀ A' : Subgroup G, A < A' → ∀ d : ℕ,
      ¬ Nonempty (↥A' ≃* (Fin d → Multiplicative (ZMod p)))) :
    Maximal (IsElementaryAbelianSubgroup p) A := by
  refine ⟨hA, fun B hB hAB => ?_⟩
  by_contra hcon
  obtain ⟨d, hd⟩ := exists_mulEquiv_pi_of_isElementaryAbelianSubgroup hp hB
  exact hmax B (lt_of_le_of_ne hAB fun h => hcon (h ▸ le_rfl)) d hd

theorem exists_line_ne_of_card_eq_sq [Finite G] (hp : p.Prime) {A Z : Subgroup G}
    (hAexp : ∀ x ∈ A, x ^ p = 1) (hAcard : Nat.card A = p ^ 2) (hZA : Z ≤ A)
    (hZcard : Nat.card Z = p) :
    ∃ A₀ : Subgroup G, A₀ ≤ A ∧ Nat.card A₀ = p ∧ A₀ ≠ Z := by
  have hlt : Z < A := by
    refine lt_of_le_of_ne hZA fun h => ?_
    rw [h, hAcard] at hZcard
    nlinarith [hZcard, pow_pos hp.pos 2, hp.two_le]
  obtain ⟨x, hxA, hxZ⟩ := SetLike.exists_of_lt hlt
  have hx1 : x ≠ 1 := fun h => hxZ (h ▸ one_mem _)
  have := Fact.mk hp
  exact ⟨zpowers x, zpowers_le.2 hxA,
    by rw [Nat.card_zpowers, orderOf_eq_prime (hAexp x hxA) hx1],
    fun h => hxZ (h ▸ mem_zpowers x)⟩

theorem map_centerTorsionBy_subtype (P : Subgroup G) (n : ℕ) :
    (centerTorsionBy ↥P n).map P.subtype = subgroupCenterTorsionBy P n := by
  ext z
  simp only [Subgroup.mem_map, Subgroup.coe_subtype, mem_centerTorsionBy,
    mem_subgroupCenterTorsionBy, mem_center_iff]
  constructor
  · rintro ⟨w, ⟨hwc, hwn⟩, rfl⟩
    exact ⟨w.2, fun x hx => congrArg Subtype.val (hwc ⟨x, hx⟩),
      by simpa using congrArg Subtype.val hwn⟩
  · rintro ⟨hzP, hzc, hzn⟩
    exact ⟨⟨z, hzP⟩, ⟨fun x => Subtype.ext (hzc (x : G) x.2),
      Subtype.ext (by simpa using hzn)⟩, rfl⟩

theorem map_subgroupCenterTorsionBy_subgroupOf {K P : Subgroup G} (hPK : P ≤ K) (n : ℕ) :
    Subgroup.map K.subtype (subgroupCenterTorsionBy (P.subgroupOf K) n)
      = subgroupCenterTorsionBy P n := by
  ext z
  simp only [Subgroup.mem_map, Subgroup.coe_subtype, mem_subgroupCenterTorsionBy,
    Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨w, ⟨hwP, hwc, hwn⟩, rfl⟩
    refine ⟨hwP, fun x hx => ?_, by simpa using congrArg Subtype.val hwn⟩
    exact congrArg Subtype.val (hwc ⟨x, hPK hx⟩ hx)
  · rintro ⟨hzP, hzc, hzn⟩
    exact ⟨⟨z, hPK hzP⟩, ⟨hzP, fun x hx => Subtype.ext (hzc (x : G) hx),
      Subtype.ext (by simpa using hzn)⟩, rfl⟩

theorem mem_normalizer_of_mem_normalizer_subgroupOf {A P : Subgroup G} (hAP : A ≤ P) {g : ↥P}
    (hg : g ∈ normalizer ((A.subgroupOf P : Subgroup ↥P) : Set ↥P)) :
    (g : G) ∈ normalizer (A : Set G) := by
  rw [mem_normalizer_iff] at hg ⊢
  intro y
  refine ⟨fun hy => (hg ⟨y, hAP hy⟩).1 hy, fun hy => ?_⟩
  have hyP : y ∈ P := by
    have h : (g : G)⁻¹ * ((g : G) * y * (g : G)⁻¹) * (g : G) ∈ P :=
      mul_mem (mul_mem (inv_mem g.2) (hAP hy)) g.2
    simpa [mul_assoc] using h
  exact (hg ⟨y, hyP⟩).2 hy

end

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

public section

open Subgroup CFSG.FeitThompson

universe u

theorem FPL_global_maximal_plane_geometry
    (h₁ : CFSG.FeitThompson.Statements.FPL_low_rank_sylow_central_product.{u}) :
    CFSG.FeitThompson.Statements.FPL_global_maximal_plane_geometry.{u} := by
  intro G _ _ _ p hp hodd A P hA hAmax hPcard hAP hPnc Z₀ hZ₀
  have hfp := Fact.mk hp
  obtain ⟨f⟩ := hA
  obtain ⟨hAea, hAcard⟩ := isElementaryAbelianSubgroup_of_mulEquiv f
  have hAcomm : IsMulCommutative ↥A := hAea.isMulCommutative
  have hAglobmax : Maximal (IsElementaryAbelianSubgroup p) A :=
    maximal_isElementaryAbelianSubgroup_of_forall hp hAea hAmax
  obtain ⟨n, hn⟩ := hPcard
  have hPp : IsPGroup p ↥P := IsPGroup.of_card hn
  obtain ⟨S, hPS⟩ := hPp.exists_le_sylow
  have hSp : IsPGroup p ↥(S : Subgroup G) := S.isPGroup'
  have hAS : A ≤ (S : Subgroup G) := hAP.trans hPS
  have hsylow : CFSG.FeitThompson.Prep06.IsSylowIn p (S : Subgroup G) ⊤ := by
    refine CFSG.FeitThompson.Prep06.isSylowIn_iff.2 ⟨le_top, ?_⟩
    rw [Subgroup.card_top]
    exact S.card_eq_multiplicity
  have hEP' : A.subgroupOf (S : Subgroup G) ≤ P.subgroupOf (S : Subgroup G) :=
    Subgroup.comap_mono hAP
  have hEmax : Maximal (IsElementaryAbelianSubgroup p) (A.subgroupOf (S : Subgroup G)) :=
    maximal_isElementaryAbelianSubgroup_subgroupOf hAglobmax hAS
  have hEcard : Nat.card (A.subgroupOf (S : Subgroup G)) = p ^ 2 := by
    rw [natCard_subgroupOf_of_le hAS, hAcard]
  have hSnc : ¬ IsMulCommutative ↥(S : Subgroup G) := fun hc =>
    hPnc (have := hc; isMulCommutative_of_le hPS)
  have hP'nc : ¬ IsMulCommutative ↥(P.subgroupOf (S : Subgroup G)) := fun hc =>
    hPnc (have := hc; isMulCommutative_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hPS).symm)
  obtain ⟨Y₁, hY₁cyc, hZY₁, hZcard, hprod⟩ :
      ∃ Y₁ : Subgroup ↥(S : Subgroup G), IsCyclic ↥Y₁ ∧
        centerTorsionBy ↥(S : Subgroup G) p ≤ Y₁ ∧
        Nat.card (centerTorsionBy ↥(S : Subgroup G) p) = p ∧
        ∀ A₀ : Subgroup ↥(S : Subgroup G), A₀ ≤ A.subgroupOf (S : Subgroup G) →
          Nat.card A₀ = p → A₀ ≠ centerTorsionBy ↥(S : Subgroup G) p →
          IsInternalDirectProduct
            (centralizer ((A.subgroupOf (S : Subgroup G) : Subgroup ↥(S : Subgroup G)) :
              Set ↥(S : Subgroup G))) A₀ Y₁ := by
    rcases le_or_gt 3 (elementaryAbelianPRank p ↥(S : Subgroup G)) with hrank | hrank
    ·
      obtain ⟨hcyc, hle, hpr⟩ := planeCyclicFactor_spec hp hodd hSp
        (maximal_isElementaryAbelianSubgroup_iff.1 hEmax) hEcard hrank
      exact ⟨_, hcyc, hle, natCard_centerTorsionBy_of_maximal hp hSp
        (maximal_isElementaryAbelianSubgroup_iff.1 hEmax) hEcard hrank, hpr⟩
    ·
      obtain ⟨B, C, hBS, hCS, hBC, hBcard, hBnc, hBexp, hCbot, hCcyc, hCcen, hBCcen,
        hBCset, hBCcard⟩ := h₁ G ‹_› p hp hodd (S : Subgroup G) hsylow (by omega) hSnc
      have hstruct : IsRankTwoCentralProduct p ↥(S : Subgroup G)
          (B.subgroupOf (S : Subgroup G)) (C.subgroupOf (S : Subgroup G))
          ((B ⊓ C).subgroupOf (S : Subgroup G)) :=
        { prime := hp
          odd := hodd
          finite := inferInstance
          isPGroup := hSp
          sup_eq_top := by
            rw [← Subgroup.subgroupOf_sup hBS hCS, hBC, Subgroup.subgroupOf_self]
          card_base := by rw [natCard_subgroupOf_of_le hBS, hBcard]
          base_not_isMulCommutative := fun hc =>
            hBnc (have := hc; isMulCommutative_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hBS).symm)
          pow_eq_one_of_mem_base := fun b hb => Subtype.ext (by simpa using hBexp (b : G) hb)
          central := fun x hx => mem_center_iff.2 fun y => Subtype.ext (by
            push_cast
            exact (mem_centralizer_iff.1 (hCcen hx).2) (y : G) y.2)
          isCyclic := isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hCS).symm
            (Subgroup.subgroupOfEquivOfLe hCS).symm.surjective
          central_ne_bot := fun hcon => hCbot (Subgroup.card_eq_one.1
            (by rw [← natCard_subgroupOf_of_le hCS, hcon, Subgroup.card_bot]))
          coe_socle := by
            ext z
            simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Set.mem_ofPred_eq]
            have h1 : ((z : G) ∈ (B ⊓ C : Subgroup G)) ↔ (z : G) ∈ {c | c ∈ C ∧ c ^ p = 1} := by
              rw [← SetLike.mem_coe, hBCset]
            refine h1.trans ?_
            simp only [Set.mem_ofPred_eq]
            exact ⟨fun ⟨h2, h3⟩ => ⟨h2, Subtype.ext (by simpa using h3)⟩,
              fun ⟨h2, h3⟩ => ⟨h2, by simpa using congrArg Subtype.val h3⟩⟩
          inf_base_central := Subgroup.comap_inf B C _
          center_base := by
            rw [centralizer_subgroupOf_of_le hBS, hBCcen]
            exact (Subgroup.comap_inf _ _ _).symm
          card_socle := by
            rw [natCard_subgroupOf_of_le (inf_le_left.trans hBS), hBCcard] }
      have hZeq : centerTorsionBy ↥(S : Subgroup G) p
          = (B ⊓ C).subgroupOf (S : Subgroup G) := by
        ext z
        rw [mem_centerTorsionBy, hstruct.center_eq, hstruct.mem_socle_iff]
      refine ⟨C.subgroupOf (S : Subgroup G), hstruct.isCyclic,
        hZeq ▸ hstruct.socle_le_central, ?_, ?_⟩
      · rw [hZeq, natCard_subgroupOf_of_le (inf_le_left.trans hBS), hBCcard]
      · intro A₀ hA₀E hA₀card hA₀ne
        exact hstruct.isInternalDirectProduct_centralizer_plane hEmax.prop.isMulCommutative
          hEmax.prop.pow_eq_one hEcard hA₀E hA₀card (by rwa [hZeq] at hA₀ne)
  obtain ⟨hZ₀eq, hprod', hYcyc', hZ₀le⟩ := plane_centralizer_restriction
    (R := ↥(S : Subgroup G)) hp hEmax hEcard hEP' hP'nc hZcard hY₁cyc hZY₁ hprod
  obtain ⟨L₁, hL₁E, hL₁card, hL₁ne⟩ := exists_line_ne_of_card_eq_sq (G := ↥(S : Subgroup G)) hp
    hEmax.prop.pow_eq_one hEcard
    (centerTorsionBy_le_of_maximal (maximal_isElementaryAbelianSubgroup_iff.1 hEmax)) hZcard
  have hinj : Function.Injective (S : Subgroup G).subtype := (S : Subgroup G).subtype_injective
  have hmapP : Subgroup.map (S : Subgroup G).subtype (P.subgroupOf (S : Subgroup G)) = P :=
    Subgroup.map_subgroupOf_eq_of_le hPS
  have hmapA : Subgroup.map (S : Subgroup G).subtype (A.subgroupOf (S : Subgroup G)) = A :=
    Subgroup.map_subgroupOf_eq_of_le hAS
  have hmapZ : Subgroup.map (S : Subgroup G).subtype
      (subgroupCenterTorsionBy (P.subgroupOf (S : Subgroup G)) p)
      = subgroupCenterTorsionBy P p := map_subgroupCenterTorsionBy_subgroupOf hPS p
  have hmapC : Subgroup.map (S : Subgroup G).subtype
      (P.subgroupOf (S : Subgroup G) ⊓
        centralizer ((A.subgroupOf (S : Subgroup G) : Subgroup ↥(S : Subgroup G)) :
          Set ↥(S : Subgroup G)))
      = P ⊓ centralizer (A : Set G) := by
    rw [Subgroup.map_inf _ _ _ hinj, hmapP, centralizer_subgroupOf_of_le hAS,
      Subgroup.subgroupOf_map_subtype]
    ext z
    simp only [Subgroup.mem_inf]
    exact ⟨fun ⟨h1, h2, _⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨h1, h2, hPS h1⟩⟩
  have hZ₀A : subgroupCenterTorsionBy P p ≤ A := by
    rw [← hmapZ, ← hmapA]
    exact Subgroup.map_mono (subgroupCenterTorsionBy_le_of_maximal hEmax hEP')
  have hZ₀card : Nat.card (subgroupCenterTorsionBy P p) = p := by
    rw [← hmapZ, Subgroup.card_map_of_injective hinj, hZ₀eq, hZcard]
  have hkey : ∀ A₀ : Subgroup G, A₀ ≤ A → Nat.card A₀ = p →
      A₀ ≠ subgroupCenterTorsionBy P p →
      IsInternalDirectProduct (P ⊓ centralizer (A : Set G)) A₀
        (Subgroup.map (S : Subgroup G).subtype (P.subgroupOf (S : Subgroup G) ⊓ Y₁)) := by
    intro A₀ hA₀A hA₀card hA₀ne
    have hA₀S : A₀ ≤ (S : Subgroup G) := hA₀A.trans hAS
    have hmapA₀ : Subgroup.map (S : Subgroup G).subtype (A₀.subgroupOf (S : Subgroup G)) = A₀ :=
      Subgroup.map_subgroupOf_eq_of_le hA₀S
    have hne : A₀.subgroupOf (S : Subgroup G) ≠ centerTorsionBy ↥(S : Subgroup G) p := by
      intro hcon
      exact hA₀ne (by rw [← hmapA₀, hcon, ← hZ₀eq, hmapZ])
    have hres := hprod' (A₀.subgroupOf (S : Subgroup G)) (Subgroup.comap_mono hA₀A)
      (by rw [natCard_subgroupOf_of_le hA₀S, hA₀card]) hne
    have hmap := isInternalDirectProduct_map hinj hres
    rwa [hmapC, hmapA₀] at hmap
  refine ⟨subgroupCenterTorsionBy P p, ?_, hZ₀A, hZ₀card,
    ⟨Subgroup.map (S : Subgroup G).subtype (P.subgroupOf (S : Subgroup G) ⊓ Y₁), ?_,
      isCyclic_map hinj hYcyc', ?_, ?_⟩, ?_⟩
  ·
    rw [hZ₀]
    ext z
    simp only [SetLike.mem_coe, mem_subgroupCenterTorsionBy, Set.mem_ofPred_eq, Subgroup.mem_inf,
      mem_centralizer_iff]
    exact ⟨fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h2⟩, h3⟩, fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, h3⟩⟩
  ·
    rw [← hmapC]
    exact Subgroup.map_mono (le_inf inf_le_left
      (inf_le_right.trans (hprod L₁ hL₁E hL₁card hL₁ne).right_le))
  ·
    rw [← hmapZ]
    exact Subgroup.map_mono hZ₀le
  ·
    intro A₀ hA₀A hA₀card hA₀ne
    have hmap := hkey A₀ hA₀A hA₀card hA₀ne
    exact ⟨hmap.sup_eq, hmap.inf_eq_bot, hmap.commutator_eq_bot⟩
  ·
    intro A₀ A₁ hA₀A hA₁A hA₀card hA₁card hA₀ne hA₁ne
    have hCPAcomm : IsMulCommutative ↥(P ⊓ centralizer (A : Set G)) := by
      obtain ⟨L, hLA, hLcard, hLne⟩ := exists_line_ne_of_card_eq_sq hp hAea.pow_eq_one hAcard
        hZ₀A hZ₀card
      have hmap := hkey L hLA hLcard hLne
      have : IsMulCommutative ↥L := have := hAcomm; isMulCommutative_of_le hLA
      have : IsCyclic ↥(Subgroup.map (S : Subgroup G).subtype
        (P.subgroupOf (S : Subgroup G) ⊓ Y₁)) := isCyclic_map hinj hYcyc'
      have : IsMulCommutative ↥(Subgroup.map (S : Subgroup G).subtype
        (P.subgroupOf (S : Subgroup G) ⊓ Y₁)) := IsCyclic.isMulCommutative
      exact hmap.isMulCommutative
    have hAPmax : Maximal (IsElementaryAbelianSubgroup p) (A.subgroupOf P) :=
      maximal_isElementaryAbelianSubgroup_subgroupOf hAglobmax hAP
    have hAPcard : Nat.card (A.subgroupOf P) = p ^ 2 := by
      rw [natCard_subgroupOf_of_le hAP, hAcard]
    have hPinj : Function.Injective P.subtype := P.subtype_injective
    have hCcomm : IsMulCommutative ↥(centralizer ((A.subgroupOf P : Subgroup ↥P) : Set ↥P)) := by
      rw [centralizer_subgroupOf_of_le hAP]
      have := hCPAcomm
      refine isMulCommutative_of_mulEquiv (B := ↥(P ⊓ centralizer (A : Set G))) ?_
      exact (Subgroup.equivMapOfInjective _ P.subtype hPinj).trans
        (MulEquiv.subgroupCongr (by rw [Subgroup.subgroupOf_map_subtype, inf_comm]))
    have hZPmap : Subgroup.map P.subtype (centerTorsionBy ↥P p) = subgroupCenterTorsionBy P p :=
      map_centerTorsionBy_subtype P p
    have hZPcard : Nat.card (centerTorsionBy ↥P p) = p := by
      rw [← Subgroup.card_map_of_injective (f := P.subtype) hPinj, hZPmap, hZ₀card]
    have hline : ∀ L : Subgroup G, L ≤ A → L ≠ subgroupCenterTorsionBy P p →
        L.subgroupOf P ≠ centerTorsionBy ↥P p := by
      intro L hLA hLne hcon
      exact hLne (by rw [← Subgroup.map_subgroupOf_eq_of_le (hLA.trans hAP), hcon, hZPmap])
    obtain ⟨g, hgN, hgeq⟩ := exists_mem_normalizer_map_conj_eq (R := ↥P) hp hPp
      (maximal_isElementaryAbelianSubgroup_iff.1 hAPmax) hAPcard hPnc hCcomm hZPcard
      (L₁ := A₁.subgroupOf P) (L₂ := A₀.subgroupOf P) (Subgroup.comap_mono hA₁A)
      (Subgroup.comap_mono hA₀A) (by rw [natCard_subgroupOf_of_le (hA₁A.trans hAP), hA₁card])
      (by rw [natCard_subgroupOf_of_le (hA₀A.trans hAP), hA₀card])
      (hline A₁ hA₁A hA₁ne) (hline A₀ hA₀A hA₀ne)
    refine ⟨(g : G), Subgroup.mem_inf.2 ⟨g.2,
      mem_normalizer_of_mem_normalizer_subgroupOf hAP hgN⟩, ?_⟩
    have hpush : Subgroup.map (MulAut.conj (g : G) : G ≃* G) A₁ = A₀ := by
      rw [← Subgroup.map_subgroupOf_eq_of_le (hA₁A.trans hAP), Subgroup.map_map,
        ← Subgroup.map_subgroupOf_eq_of_le (hA₀A.trans hAP), ← hgeq, Subgroup.map_map]
      rfl
    have hcomp : ((MulAut.conj (g : G)⁻¹ : G ≃* G) : G →* G).comp
        ((MulAut.conj (g : G) : G ≃* G) : G →* G) = MonoidHom.id G := by
      ext x
      simp [MulAut.conj, mul_assoc]
    rw [← hpush, Subgroup.map_map, hcomp, Subgroup.map_id]

end

end CFSG.FeitThompson.Proofs
