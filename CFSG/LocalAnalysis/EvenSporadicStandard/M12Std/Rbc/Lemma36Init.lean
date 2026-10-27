module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Rbc.Cor14GChain
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Rbc.NotF3
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.FS79Inner
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.PropA.Facts
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.PropA.Perfect
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.SolomonK.Consumer

public section

namespace CFSG.EvenSporadicStandard.M12Std.Rbc

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction

section Perfect

theorem isSimpleGroup_of_isPerfect_of_card_sixty {J : Type*} [Group J] [Finite J]
    [hP : Group.IsPerfect J] (h : Nat.card J = 60) : IsSimpleGroup J := by
  haveI : Nontrivial J := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  refine ⟨fun N hN => ?_⟩
  by_contra hne
  push Not at hne
  obtain ⟨hbot, htop⟩ := hne
  haveI : N.Normal := hN
  haveI : Group.IsPerfect (J ⧸ N) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
  haveI : Nontrivial (J ⧸ N) := by
    have h1 : 1 < N.index := Subgroup.one_lt_index_of_ne_top htop
    rw [Subgroup.index_eq_card] at h1
    exact Finite.one_lt_card_iff_nontrivial.mp h1
  have hN2 : 1 < Nat.card N := (Subgroup.one_lt_card_iff_ne_bot N).mpr hbot
  have hcard : Nat.card N * N.index = 60 := by rw [Subgroup.card_mul_index, h]
  have hlt : Nat.card (J ⧸ N) < 60 := by
    rw [← Subgroup.index_eq_card]
    by_contra hge
    push Not at hge
    nlinarith
  exact Group.IsPerfect.not_isSolvable (J ⧸ N)
    (CFSG.GroupTheory.groups_order_below_sixty_solvable hlt)

variable {G : Type} [Group G] [Finite G]

theorem jOf_commutator_eq {L : Subgroup G} {t x : G} (hF : PropA.Facts L t x)
    (hxt : x ∈ centralizer ({t} : Set G)) (hx2 : orderOf x = 2) :
    ⁅jOf L x, jOf L x⁆ = jOf L x := by
  obtain ⟨R, hRle, hRperf, hR60⟩ := hF.G2 x hxt hx2 (by rw [hF.card_Cx])
  have hRJ : R ≤ jOf L x :=
    PropA.le_of_perfect_of_card_two_pow hF.J_le hF.J_normal 4
      (by rw [hF.card_Cx, hF.card_J]; norm_num) hRle hRperf
  have hJR : jOf L x = R :=
    (Subgroup.eq_of_le_of_card_ge hRJ (by rw [hF.card_J]; exact hR60)).symm
  rw [hJR]
  exact hRperf

theorem isQuasisimple_jOf {L : Subgroup G} {t x : G} (hF : PropA.Facts L t x)
    (hxt : x ∈ centralizer ({t} : Set G)) (hx2 : orderOf x = 2) :
    CFSG.IsQuasisimple ↥(jOf L x) ∧ center ↥(jOf L x) = ⊥ := by
  haveI : Group.IsPerfect ↥(jOf L x) := Subgroup.isPerfect_iff.mpr (jOf_commutator_eq hF hxt hx2)
  haveI : IsSimpleGroup ↥(jOf L x) := isSimpleGroup_of_isPerfect_of_card_sixty hF.card_J
  refine CFSG.LocalCores.isQuasisimple_of_isSimpleGroup ?_
  by_contra hcomm
  push Not at hcomm
  haveI : Nontrivial ↥(jOf L x) := Finite.one_lt_card_iff_nontrivial.mp (by rw [hF.card_J]; omega)
  exact Group.IsPerfect.not_isSolvable ↥(jOf L x)
    (Group.isSolvable_of_comm fun a b => hcomm a b)

theorem cqOrd_jOf {L : Subgroup G} {t x : G} (hF : PropA.Facts L t x)
    (hxt : x ∈ centralizer ({t} : Set G)) (hx2 : orderOf x = 2) : cqOrd (jOf L x) = 60 := by
  have hZ := (isQuasisimple_jOf hF hxt hx2).2
  unfold cqOrd
  rw [Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hZ).trans
    QuotientGroup.quotientBot).toEquiv, hF.card_J]

theorem isCompIn_jOf {L : Subgroup G} {t x : G} (hF : PropA.Facts L t x)
    (hxt : x ∈ centralizer ({t} : Set G)) (hx2 : orderOf x = 2) :
    IsCompIn (jOf L x) (centralizer ((zpowers t ⊔ zpowers x : Subgroup G) : Set G)) := by
  have hCT : centralizer ((zpowers t : Subgroup G) : Set G) = centralizer ({t} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hX : centralizer ((zpowers t ⊔ zpowers x : Subgroup G) : Set G) =
      centralizer ({x} : Set G) ⊓ centralizer ({t} : Set G) := by
    rw [Step.centralizer_sup_zpowers, hCT, inf_comm]
  rw [hX]
  exact isCompIn_of_normal hF.J_le (isQuasisimple_jOf hF hxt hx2).1 hF.J_normal

end Perfect

section Chain

variable {G : Type} [Group G] [Finite G]

theorem jOf_le_inf (L : Subgroup G) (x : G) : jOf L x ≤ L ⊓ centralizer ({x} : Set G) := by
  refine Subgroup.commutator_le.2 fun g₁ h₁ g₂ h₂ => ?_
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem h₁ h₂) (inv_mem h₁)) (inv_mem h₂)

theorem map_conj_eq_self_of_mem {H : Subgroup G} {g : G} (hg : g ∈ H) :
    H.map (MulAut.conj g).toMonoidHom = H := by
  ext y
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact H.mul_mem (H.mul_mem hg hm) (H.inv_mem hg)
  · intro hy
    exact ⟨g⁻¹ * y * g, H.mul_mem (H.mul_mem (H.inv_mem hg) hy) hg, by group⟩

theorem isPGroup_zpowers_of_orderOf_eq_two {a : G} (ha : orderOf a = 2) :
    IsPGroup 2 ↥(zpowers a) :=
  IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha, pow_one])

theorem sq_eq_one_of_orderOf_eq_two {a : G} (ha : orderOf a = 2) : a ^ 2 = 1 := by
  rw [← ha]
  exact pow_orderOf_eq_one a

theorem tLinks_initial {L : Subgroup G} {t x : G} (hO : Out G L t) (hxL : x ∈ L)
    (hx2 : orderOf x = 2) (hF : PropA.Facts L t x) :
    TLinks G 2 (seq3 (jOf L x) L ⊤) (seq3 (zpowers t ⊔ zpowers x) (zpowers t) ⊥)
      (seq3 1 x t) := by
  have hxt : x ∈ centralizer ({t} : Set G) :=
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hO.mem x hxL)
  have hCT : centralizer ((zpowers t : Subgroup G) : Set G) = centralizer ({t} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hbot : centralizer (((⊥ : Subgroup G)) : Set G) = ⊤ := by
    rw [Subgroup.coe_bot, Subgroup.centralizer_eq_top_iff_subset]
    simp
  have hG := hO.std.simple
  have hna := hO.std.nonabelian
  have hT2 : IsPGroup 2 ↥(zpowers t) := isPGroup_zpowers_of_orderOf_eq_two hO.inv
  have hx2' : x ^ 2 ∈ zpowers t := by
    rw [sq_eq_one_of_orderOf_eq_two hx2]
    exact one_mem _
  have hxN : x ∈ normalizer ((zpowers t : Subgroup G) : Set G) :=
    Subgroup.centralizer_le_normalizer _ (by rw [hCT]; exact hxt)
  have hTx : IsPGroup 2 ↥(zpowers t ⊔ zpowers x) := isPGroup_sup_zpowers hT2 hxN hx2'
  have hJc := isCompIn_jOf hF hxt hx2
  have hJq := (isQuasisimple_jOf hF hxt hx2).1
  have hJL : jOf L x ≤ L := (jOf_le_inf L x).trans inf_le_left
  have hLc : IsCompIn L (centralizer ((zpowers t : Subgroup G) : Set G)) := by
    rw [hCT]
    exact hO.isCompIn
  have hLq := hO.isCompIn.isQuasisimple
  have hcl1 : conjClosure (jOf L x) (layerIn (centralizer ((zpowers t : Subgroup G) : Set G))) =
      L := conjClosure_layerIn_eq_of_le hLc hJL hJq
  have hcl2 : conjClosure L (layerIn (centralizer (((⊥ : Subgroup G)) : Set G))) = ⊤ := by
    rw [hbot]
    exact conjClosure_layerIn_eq_of_le (isCompIn_top_top hG hna) le_top hLq
  have htN : t ∈ normalizer (((⊥ : Subgroup G)) : Set G) := by
    rw [Solomon78.mem_normalizer_iff_map_conj_eq, Subgroup.map_bot]
  have hbotP : IsPGroup 2 ↥(⊥ : Subgroup G) := IsPGroup.of_card (n := 0) (by simp)
  have ht2 : t ^ 2 ∈ (⊥ : Subgroup G) := Subgroup.mem_bot.2 (sq_eq_one_of_orderOf_eq_two hO.inv)
  have hTc : IsCompIn L (centralizer (((⊥ : Subgroup G) ⊔ zpowers t : Subgroup G) : Set G)) := by
    rw [bot_sup_eq, hCT]
    exact hO.isCompIn
  refine ⟨fun i hi => ?_, fun i h1 hi => ?_, fun i h1 hi => ?_, fun i h1 hi => ?_⟩
  · interval_cases i
    · exact ⟨hTx, hJc⟩
    · exact ⟨hT2, hLc⟩
    · show IsPGroup 2 ↥(⊥ : Subgroup G) ∧
        IsCompIn (⊤ : Subgroup G) (centralizer (((⊥ : Subgroup G)) : Set G))
      rw [hbot]
      exact ⟨hbotP, isCompIn_top_top hG hna⟩
  · interval_cases i
    · exact ⟨isPGroup_zpowers_of_orderOf_eq_two hx2, hxN, hx2', hJc⟩
    · exact ⟨isPGroup_zpowers_of_orderOf_eq_two hO.inv, htN, ht2, hTc⟩
  · interval_cases i
    · show jOf L x ≤ L ⊔ L.map (MulAut.conj x).toMonoidHom ∧
        L ⊔ L.map (MulAut.conj x).toMonoidHom =
          conjClosure (jOf L x) (layerIn (centralizer ((zpowers t : Subgroup G) : Set G)))
      rw [map_conj_eq_self_of_mem hxL, sup_idem, hcl1]
      exact ⟨hJL, rfl⟩
    · show L ≤ (⊤ : Subgroup G) ⊔ (⊤ : Subgroup G).map (MulAut.conj t).toMonoidHom ∧
        (⊤ : Subgroup G) ⊔ (⊤ : Subgroup G).map (MulAut.conj t).toMonoidHom =
          conjClosure L (layerIn (centralizer (((⊥ : Subgroup G)) : Set G)))
      rw [map_conj_eq_self_of_mem (mem_top t), sup_idem, hcl2]
      exact ⟨le_top, rfl⟩
  · interval_cases i
    · refine Or.inr ?_
      show L = L.map (MulAut.conj x).toMonoidHom
      exact (map_conj_eq_self_of_mem hxL).symm
    · refine Or.inr ?_
      show (⊤ : Subgroup G) = (⊤ : Subgroup G).map (MulAut.conj t).toMonoidHom
      exact (map_conj_eq_self_of_mem (mem_top t)).symm

theorem inCG_initial {L : Subgroup G} {t x : G} (hO : Out G L t) (hxL : x ∈ L)
    (hx2 : orderOf x = 2) (hx : Nat.card ↥(L ⊓ centralizer ({x} : Set G)) = 240)
    (hF : PropA.Facts L t x) :
    InCG G 2 (seq3 (jOf L x) L ⊤) (seq3 (zpowers t ⊔ zpowers x) (zpowers t) ⊥)
      (seq3 1 x t) := by
  have hJL : jOf L x ≤ L := (jOf_le_inf L x).trans inf_le_left
  have hLtop : L ≠ ⊤ := hO.std.ne_top
  have hJne : jOf L x ≠ L := by
    intro h
    have hle : L ≤ centralizer ({x} : Set G) := by
      have h1 := jOf_le_inf L x
      rw [h] at h1
      exact (le_inf_iff.1 h1).2
    have h240 : Nat.card ↥L = 240 := by rw [← inf_eq_left.2 hle]; exact hx
    have h60 : Nat.card ↥L = 60 := by rw [← h]; exact hF.card_J
    omega
  have hJtop : jOf L x ≠ ⊤ := fun h => hLtop (top_le_iff.1 (h ▸ hJL))
  refine ⟨by norm_num, by simp [seq3], ?_, tLinks_initial hO hxL hx2 hF, ?_⟩
  · intro i hi j hj h
    interval_cases i <;> interval_cases j <;>
      first
      | rfl
      | exact absurd (by simpa [seq3] using h) hJne
      | exact absurd (by simpa [seq3] using h.symm) hJne
      | exact absurd (by simpa [seq3] using h) hJtop
      | exact absurd (by simpa [seq3] using h.symm) hJtop
      | exact absurd (by simpa [seq3] using h) hLtop
      | exact absurd (by simpa [seq3] using h.symm) hLtop
  · simpa [seq3] using hO.std.solStd.stdBare

end Chain

section TwoAHelpers

theorem card_inf_centralizer_coe {G : Type} [Group G] (X : Subgroup G) (a : ↥X) :
    Nat.card ↥(X ⊓ centralizer ({(a : G)} : Set G)) =
      Nat.card ↥(centralizer ({a} : Set ↥X)) := by
  have h : (centralizer ({a} : Set ↥X)).map X.subtype =
      X ⊓ centralizer ({(a : G)} : Set G) := by
    ext g
    simp only [Subgroup.mem_map, Subgroup.mem_inf, mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, congrArg Subtype.val hy⟩
    · rintro ⟨hgX, hg⟩
      exact ⟨⟨g, hgX⟩, Subtype.ext hg, rfl⟩
  rw [← h]
  exact Subgroup.card_map_of_injective X.subtype_injective

theorem card_centralizer_congr {X M : Type*} [Group X] [Group M] (e : X ≃* M) (a : X) :
    Nat.card ↥(centralizer ({a} : Set X)) = Nat.card ↥(centralizer ({e a} : Set M)) :=
  Nat.card_congr
    { toFun := fun y => ⟨e y.1, mem_centralizer_singleton_iff.2 (by
        rw [← map_mul, ← map_mul, mem_centralizer_singleton_iff.1 y.2])⟩
      invFun := fun z => ⟨e.symm z.1, mem_centralizer_singleton_iff.2 (by
        apply e.injective
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
        exact mem_centralizer_singleton_iff.1 z.2)⟩
      left_inv := fun y => Subtype.ext (e.symm_apply_apply _)
      right_inv := fun z => Subtype.ext (e.apply_symm_apply _) }

end TwoAHelpers

section TwoA


theorem exists_twoA {G : Type} [Group G] {X : Subgroup G} (hX : IsSporadic X .M12) :
    ∃ x ∈ X, orderOf x = 2 ∧ Nat.card ↥(X ⊓ centralizer ({x} : Set G)) = 240 := by
  obtain ⟨e₀⟩ := hX
  let e : ↥X ≃* NativeSporadic.M12 := e₀
  refine ⟨e.symm CFSG.ComponentClassification.M12Cover.elemA1, (e.symm _).2, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact CFSG.ComponentClassification.M12Cover.orderOf_elemA1
  · rw [card_inf_centralizer_coe X _, ← card_centralizer_congr e.symm _]
    exact CFSG.ComponentClassification.M12Cover.card_centralizer_elemA1

end TwoA

section Initial


variable {G : Type} [Group G] [Finite G]

theorem inCGb_initial {L : Subgroup G} {t x : G} (hO : Out G L t) (hxL : x ∈ L)
    (hx2 : orderOf x = 2) (hx : Nat.card ↥(L ⊓ centralizer ({x} : Set G)) = 240)
    (hF : PropA.Facts L t x) :
    InCGb G 2 (seq3 (jOf L x) L ⊤) (seq3 (zpowers t ⊔ zpowers x) (zpowers t) ⊥)
      (seq3 1 x t) := by
  have hxt : x ∈ centralizer ({t} : Set G) :=
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hO.mem x hxL)
  exact ⟨inCG_initial hO hxL hx2 hx hF, notF3Five_of_card_sixty (cqOrd_jOf hF hxt hx2)⟩

end Initial

section Outer


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G}

theorem Out.relIndex_eq_two (hO : Out G L t) :
    (L ⊔ centralizer (L : Set G)).relIndex (normalizer (L : Set G)) = 2 := by
  rcases m12_dichotomy hO.std hO.m12 hO.mem hO.inv with ⟨hC, -, hz⟩ | hidx
  · exact absurd (by rw [hC]; exact sup_le_sup_left hz L) hO.outer
  · exact hidx

theorem Out.exists_mem_centralizer_act_eq (hO : Out G L t) {g : G}
    (hg : g ∈ normalizer (L : Set G)) :
    ∃ c ∈ centralizer ({t} : Set G), ∀ y ∈ L, g * y * g⁻¹ = c * y * c⁻¹ := by
  have hLC : L ≤ centralizer ({t} : Set G) := fun l hl =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hO.mem l hl)
  by_cases hgL : g ∈ L ⊔ centralizer (L : Set G)
  · obtain ⟨l, hl, hact⟩ := mem_sup_centralizer_iff.1 hgL
    exact ⟨l, hLC hl, hact⟩
  · obtain ⟨w, hwC, hwL⟩ := SetLike.not_le_iff_exists.1 hO.outer
    have hwN : w ∈ normalizer (L : Set G) := hO.std.centralizer_le_normalizer hO.mem hO.inv hwC
    have h2 : ((L ⊔ centralizer (L : Set G)).subgroupOf (normalizer (L : Set G))).index = 2 :=
      hO.relIndex_eq_two
    have hmem : g * w⁻¹ ∈ L ⊔ centralizer (L : Set G) := by
      have h3 : (⟨g, hg⟩ * (⟨w, hwN⟩ : normalizer (L : Set G))⁻¹ : normalizer (L : Set G)) ∈
          (L ⊔ centralizer (L : Set G)).subgroupOf (normalizer (L : Set G)) := by
        rw [Subgroup.mul_mem_iff_of_index_two h2, inv_mem_iff]
        exact iff_of_false (fun h => hgL h) (fun h => hwL h)
      exact h3
    obtain ⟨l, hl, hact⟩ := mem_sup_centralizer_iff.1 hmem
    refine ⟨l * w, mul_mem (hLC hl) hwC, fun y hy => ?_⟩
    have hwy : w * y * w⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 hwN y).1 hy
    have h4 := hact _ hwy
    calc g * y * g⁻¹ = g * w⁻¹ * (w * y * w⁻¹) * (g * w⁻¹)⁻¹ := by group
      _ = l * (w * y * w⁻¹) * l⁻¹ := h4
      _ = l * w * y * (l * w)⁻¹ := by group

end Outer

section OuterTop


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G}

theorem outer_at_top (hY : SolomonK.Yoshida74Co3K) (hO : Out G L t) {X : Subgroup G}
    (hX : StdHyp G X) (hXm : IsSporadic X .M12) : ∃ u : G, Out G X u := by
  obtain ⟨u, hu, hu2⟩ := hX.exists_involution_centralizer
  refine ⟨u, hX, hXm, hu, hu2, fun hinn => ?_⟩
  have hCo3 : IsSporadic G .Co3 :=
    hY G hO.std.kProper hO.std.simple u hu2 (m12_inner_nonempty_equiv hX hXm hu hu2 hinn)
  exact hO.outer (centralizer_le_sup_of_isSporadic_co3 hO.std hO.m12 hCo3 hO.mem hO.inv)

end OuterTop

end CFSG.EvenSporadicStandard.M12Std.Rbc
