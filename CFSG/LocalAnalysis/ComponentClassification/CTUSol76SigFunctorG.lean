module

public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigPumpG

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.Sol76T13
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {N K K' : Subgroup G}

omit [Finite G] in
theorem mem_normalizer_commutator {A B : Subgroup G} {g : G} (hA : g ∈ normalizer (A : Set G))
    (hB : g ∈ normalizer (B : Set G)) : g ∈ normalizer ((⁅A, B⁆ : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator,
    mem_normalizer_iff_map_conj_eq.mp hA, mem_normalizer_iff_map_conj_eq.mp hB]

omit [Finite G] in
theorem mem_normalizer_inf {A B : Subgroup G} {g : G} (hA : g ∈ normalizer (A : Set G))
    (hB : g ∈ normalizer (B : Set G)) : g ∈ normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff]
  intro y
  rw [mem_inf, mem_inf, mem_normalizer_iff.mp hA, mem_normalizer_iff.mp hB]

theorem theta_inf_centralizer_le_of_mem (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') {V : Subgroup G} (hV : IsKleinFour V) (hVK' : V ≤ K') {b ε : G}
    (hb2 : orderOf b = 2) (hbQ : b ∈ coreActionKernel K')
    (hbV : V ≤ centralizer ({b} : Set G)) (hεK : ε ∈ K) (hε2 : orderOf ε = 2)
    (hεb : ε * b = b * ε) (hVε : V ≤ centralizer ({ε} : Set G)) :
    theta V b ⊓ centralizer (V : Set G) ≤
      oddCoreIn (centralizer ({b} : Set G)) ⊓ oddCoreIn (centralizer (V : Set G)) := by
  set Ob := oddCoreIn (centralizer ({b} : Set G)) with hOb
  set X := ⁅Ob, V⁆ with hX
  set T := Ob ⊓ oddCoreIn (centralizer (V : Set G)) with hT
  have hV2 : IsPGroup 2 V := isPGroup_of_isKleinFour hV
  have hVc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := comm_of_isKleinFour hV
  have hVOb : V ≤ normalizer (Ob : Set G) := hbV.trans (le_normalizer_oddCoreIn _)
  have hObodd : Odd (Nat.card Ob) := Nat.coprime_two_left.mp (coprime_card_oddCoreIn _)
  have hXOb : X ≤ Ob := CFSG.SignalizerFunctor.Helpers.commutator_le_of_normalizing Ob V hVOb
  have hXodd : Odd (Nat.card X) := Nat.coprime_two_left.mp
    (Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hXOb) (coprime_card_oddCoreIn _))
  have hVX : V ≤ normalizer (X : Set G) := le_normalizer_commutator hVOb
  have hXX : ⁅X, V⁆ = X :=
    CFSG.ClassicalInvolution.Balance.commutator_commutator_eq_of_isPGroup hV2 hObodd hVOb
  have hεCb : ε ∈ normalizer (centralizer ({b} : Set G) : Set G) :=
    le_normalizer (mem_centralizer_singleton_iff.mpr hεb)
  have hεOb : ε ∈ normalizer (Ob : Set G) := mem_normalizer_oddCoreIn hεCb
  have hεV : ε ∈ normalizer (V : Set G) := by
    have hεC : ε ∈ centralizer (V : Set G) := mem_centralizer_iff.mpr fun v hv =>
      mem_centralizer_singleton_iff.mp (hVε hv)
    exact Subgroup.centralizer_le_normalizer (V : Set G) hεC
  have hεX : ε ∈ normalizer (X : Set G) := mem_normalizer_commutator hεOb hεV
  have hCX : X ⊓ centralizer (V : Set G) ≤ oddCoreIn (centralizer (V : Set G)) := by
    rw [inf_centralizer_eq_iSup_of_isKleinFour hV hVX hXodd hXX]
    refine iSup₂_le fun w hw => iSup_le fun hw1 => ?_
    have hw2 : orderOf w = 2 := orderOf_eq_two_of_isKleinFour hV hw hw1
    have hVw : V ≤ centralizer ({w} : Set G) := fun v hv =>
      mem_centralizer_singleton_iff.mpr (hVc v hv w hw)
    set Y := ⁅X ⊓ centralizer ({w} : Set G), V⁆ with hY
    have hVXw : V ≤ normalizer ((X ⊓ centralizer ({w} : Set G) : Subgroup G) : Set G) :=
      fun v hv => mem_normalizer_inf (hVX hv) (le_normalizer (hVw hv))
    have hYle : Y ≤ X ⊓ centralizer ({w} : Set G) :=
      CFSG.SignalizerFunctor.Helpers.commutator_le_of_normalizing _ V hVXw
    have hXwodd : Odd (Nat.card (X ⊓ centralizer ({w} : Set G) : Subgroup G)) :=
      Nat.coprime_two_left.mp (Nat.Coprime.coprime_dvd_right
        (Subgroup.card_dvd_of_le (inf_le_left.trans hXOb)) (coprime_card_oddCoreIn _))
    have hYY : ⁅Y, V⁆ = Y :=
      CFSG.ClassicalInvolution.Balance.commutator_commutator_eq_of_isPGroup hV2 hXwodd hVXw
    have hwb : w * b = b * w := mem_centralizer_singleton_iff.mp (hbV hw)
    have hεw : ε * w = w * ε := (mem_centralizer_singleton_iff.mp (hVε hw)).symm
    have hεY : ε ∈ normalizer (Y : Set G) :=
      mem_normalizer_commutator (mem_normalizer_inf hεX
        (le_normalizer (mem_centralizer_singleton_iff.mpr hεw))) hεV
    have hYO := le_oddCoreIn_of_pump_of_mem hq hR1 hG hN hK hK' hne (hVK' hw) hw2 hb2 hbQ hwb hεK
      hε2 hεb hεw hVK' hV2 hVw hVε (hYle.trans (inf_le_inf_right _ hXOb))
      (le_normalizer_commutator hVXw) hεY hYY
    have hzw : zpowers w ≤ V := zpowers_le.mpr hw
    have h2 : oddCoreIn (centralizer ({w} : Set G)) ⊓ centralizer (V : Set G) ≤
        oddCoreIn (centralizer (V : Set G)) := by
      have := oddCoreIn_inf_centralizer_le (U₁ := zpowers w) (V₁ := V) hzw
      rwa [centralizer_zpowers_eq] at this
    exact (inf_le_inf_right _ hYO).trans h2
  have hTX : T ≤ normalizer (X : Set G) := inf_le_left.trans
    (CFSG.SignalizerFunctor.Helpers.normalized_commutator_target_normalizes V Ob hVOb)
  have hVT : V ≤ normalizer (T : Set G) := fun v hv => mem_normalizer_inf (hVOb hv)
    (le_normalizer_oddCoreIn _ (le_centralizer_of_le_of_comm le_rfl hVc hv))
  intro y hy
  have hθ : ((theta V b : Subgroup G) : Set G) = (X : Set G) * (T : Set G) := by
    rw [show theta V b = X ⊔ T from rfl]
    exact coe_mul_of_right_le_normalizer_left X T hTX
  have hθle : theta V b ≤ Ob := theta_le_oddCoreIn hbV
  have hfix := CFSG.SignalizerFunctor.Helpers.normalized_product_fixed_points 2 Nat.prime_two V
    (theta V b) X T hV2 (le_normalizer_theta (hbV.trans le_normalizer) le_normalizer
      (fun v hv => le_normalizer (le_centralizer_of_le_of_comm le_rfl hVc hv)))
    hVX hVT le_sup_left le_sup_right
    (Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hθle) (coprime_card_oddCoreIn _))
    hθ.symm
  have hy' : y ∈ (((theta V b) ⊓ centralizer (V : Set G) : Subgroup G) : Set G) := hy
  rw [← hfix] at hy'
  obtain ⟨x, hx, t, ht, rfl⟩ := hy'
  have hx' : x ∈ Ob ⊓ oddCoreIn (centralizer (V : Set G)) := ⟨hXOb hx.1, hCX hx⟩
  exact mul_mem hx' ht.1

omit [Finite G] in
theorem exists_mem_ne_one_of_isKleinFour {E : Subgroup G} (hE : IsKleinFour E) :
    ∃ e ∈ E, e ≠ 1 := by
  by_contra h
  push Not at h
  have h4 := hE.card_four
  rw [show E = ⊥ from eq_bot_iff.mpr fun x hx => (mem_bot).mpr (h x hx), card_bot] at h4
  norm_num at h4

theorem theta_inf_centralizer_le_of_two_actual_hulls
    {B E F : Subgroup G} {b : G}
    (hE : IsKleinFour E) (hF : IsKleinFour F)
    (hEB : E ≤ B) (hBF : B ≤ centralizer (F : Set G))
    (hB : CFSG.Open.IsElemAbelian 2 B)
    (hleft : ∀ e ∈ E, e ≠ 1 → ∃ J : Subgroup G,
      IsTwoComponentIn J (centralizer ({e} : Set G)) ∧
        F ≤ J ∧ B ≤ coreActionKernel J)
    (hright : ∀ u ∈ F, u ≠ 1 → ∃ I : Subgroup G,
      IsTwoComponentIn I (centralizer ({u} : Set G)) ∧
        E ≤ I ∧ ⁅I, F⁆ ≤ oddCoreIn (centralizer ({u} : Set G)))
    (hb : b ∈ B) (hb1 : b ≠ 1) :
    theta F b ⊓ centralizer (F : Set G) ≤
      oddCoreIn (centralizer ({b} : Set G)) ⊓ oddCoreIn (centralizer (F : Set G)) := by
  classical
  have hb2 : orderOf b = 2 := orderOf_eq_prime (hB.2 b hb) hb1
  have hF2 : IsPGroup 2 F := isPGroup_of_isKleinFour hF
  have hFc : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x := comm_of_isKleinFour hF
  have hEF : E ≤ centralizer (F : Set G) := hEB.trans hBF
  have hbF : F ≤ centralizer ({b} : Set G) := fun w hw =>
    mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp (hBF hb)) w hw)
  set Ob : Subgroup G := oddCoreIn (centralizer ({b} : Set G)) with hOb
  set X : Subgroup G := ⁅Ob, F⁆ with hX
  set T : Subgroup G := Ob ⊓ oddCoreIn (centralizer (F : Set G)) with hT
  have hFOb : F ≤ normalizer (Ob : Set G) := hbF.trans (le_normalizer_oddCoreIn _)
  have hObodd : Odd (Nat.card Ob) := Nat.coprime_two_left.mp (coprime_card_oddCoreIn _)
  have hXOb : X ≤ Ob :=
    CFSG.SignalizerFunctor.Helpers.commutator_le_of_normalizing Ob F hFOb
  have hXodd : Odd (Nat.card X) := Nat.coprime_two_left.mp
    (Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hXOb) (coprime_card_oddCoreIn _))
  have hFX : F ≤ normalizer (X : Set G) := le_normalizer_commutator hFOb
  have hXX : ⁅X, F⁆ = X :=
    CFSG.ClassicalInvolution.Balance.commutator_commutator_eq_of_isPGroup hF2 hObodd hFOb
  obtain ⟨ε, hεE, hε1⟩ := exists_mem_ne_one_of_isKleinFour hE
  have hε2 : orderOf ε = 2 := orderOf_eq_two_of_isKleinFour hE hεE hε1
  have hεb : ε * b = b * ε := (hB.comm hb (hEB hεE)).symm
  have hεCb : ε ∈ normalizer (centralizer ({b} : Set G) : Set G) :=
    le_normalizer (mem_centralizer_singleton_iff.mpr hεb)
  have hεOb : ε ∈ normalizer (Ob : Set G) := mem_normalizer_oddCoreIn hεCb
  have hεF : ε ∈ centralizer (F : Set G) := hEF hεE
  have hεX : ε ∈ normalizer (X : Set G) :=
    mem_normalizer_commutator hεOb (Subgroup.centralizer_le_normalizer (F : Set G) hεF)
  obtain ⟨Jε, hJε, hFJε, hBJε⟩ := hleft ε hεE hε1
  have hCX : X ⊓ centralizer (F : Set G) ≤ oddCoreIn (centralizer (F : Set G)) := by
    rw [inf_centralizer_eq_iSup_of_isKleinFour hF hFX hXodd hXX]
    refine iSup₂_le fun w hw => iSup_le fun hw1 => ?_
    have hw2 : orderOf w = 2 := orderOf_eq_two_of_isKleinFour hF hw hw1
    have hFw : F ≤ centralizer ({w} : Set G) := fun x hx =>
      mem_centralizer_singleton_iff.mpr (hFc x hx w hw)
    set Y : Subgroup G := ⁅X ⊓ centralizer ({w} : Set G), F⁆ with hY
    have hFY : F ≤ normalizer ((X ⊓ centralizer ({w} : Set G) : Subgroup G) : Set G) :=
      fun v hv => mem_normalizer_inf (hFX hv) (le_normalizer (hFw hv))
    have hYle : Y ≤ X ⊓ centralizer ({w} : Set G) :=
      CFSG.SignalizerFunctor.Helpers.commutator_le_of_normalizing _ F hFY
    have hXwodd : Odd (Nat.card (X ⊓ centralizer ({w} : Set G) : Subgroup G)) :=
      Nat.coprime_two_left.mp (Nat.Coprime.coprime_dvd_right
        (Subgroup.card_dvd_of_le (inf_le_left.trans hXOb)) (coprime_card_oddCoreIn _))
    have hYY : ⁅Y, F⁆ = Y :=
      CFSG.ClassicalInvolution.Balance.commutator_commutator_eq_of_isPGroup hF2 hXwodd hFY
    have hwb : w * b = b * w := mem_centralizer_singleton_iff.mp (hbF hw)
    have hεw : ε * w = w * ε := (mem_centralizer_iff.mp hεF w hw).symm
    have hεY : ε ∈ normalizer (Y : Set G) :=
      mem_normalizer_commutator (mem_normalizer_inf hεX
        (le_normalizer (mem_centralizer_singleton_iff.mpr hεw)))
        (Subgroup.centralizer_le_normalizer (F : Set G) hεF)
    obtain ⟨I, hI, hEI, hIF⟩ := hright w hw hw1
    have hYO : Y ≤ oddCoreIn (centralizer ({w} : Set G)) :=
      le_oddCoreIn_of_two_actual_hulls hw2 hb2 hε2 hwb hεb hF2 hFw
        (le_inf (hYle.trans (inf_le_left.trans hXOb)) (hYle.trans inf_le_right))
        (le_normalizer_commutator hFY) hεY hYY
        hI (hEI hεE) hIF hJε hFJε (hBJε hb)
    have hzw : zpowers w ≤ F := zpowers_le.mpr hw
    have h2 : oddCoreIn (centralizer ({w} : Set G)) ⊓ centralizer (F : Set G) ≤
        oddCoreIn (centralizer (F : Set G)) := by
      have := oddCoreIn_inf_centralizer_le (U₁ := zpowers w) (V₁ := F) hzw
      rwa [centralizer_zpowers_eq] at this
    exact (inf_le_inf_right _ hYO).trans h2
  have hTX : T ≤ normalizer (X : Set G) := inf_le_left.trans
    (CFSG.SignalizerFunctor.Helpers.normalized_commutator_target_normalizes F Ob hFOb)
  have hFT : F ≤ normalizer (T : Set G) := fun v hv =>
    mem_normalizer_inf (hFOb hv)
      (le_normalizer_oddCoreIn _ (le_centralizer_of_le_of_comm le_rfl hFc hv))
  have hFθ : F ≤ normalizer (theta F b : Set G) :=
    le_normalizer_theta (hbF.trans le_normalizer) le_normalizer
      ((le_centralizer_of_le_of_comm le_rfl hFc).trans le_normalizer)
  have hθ : ((theta F b : Subgroup G) : Set G) = (X : Set G) * (T : Set G) := by
    rw [show theta F b = X ⊔ T from rfl]
    exact coe_mul_of_right_le_normalizer_left X T hTX
  have hθle : theta F b ≤ Ob := theta_le_oddCoreIn hbF
  have hfix := CFSG.SignalizerFunctor.Helpers.normalized_product_fixed_points 2 Nat.prime_two F
    (theta F b) X T hF2 hFθ hFX hFT le_sup_left le_sup_right
    (Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hθle) (coprime_card_oddCoreIn _))
    hθ.symm
  intro y hy
  have hy' : y ∈ (((theta F b) ⊓ centralizer (F : Set G) : Subgroup G) : Set G) := hy
  rw [← hfix] at hy'
  obtain ⟨x, hx, t, ht, rfl⟩ := hy'
  have hx' : x ∈ T := ⟨hXOb hx.1, hCX hx⟩
  exact mul_mem hx' ht.1

theorem theta_inf_le_theta_of_mem (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') {V : Subgroup G} (hV : IsKleinFour V) (hVK' : V ≤ K') {a b : G}
    (ha2 : orderOf a = 2) (haQ : a ∈ coreActionKernel K') (hb2 : orderOf b = 2)
    (hbQ : b ∈ coreActionKernel K') (hab : a * b = b * a)
    (haV : V ≤ centralizer ({a} : Set G)) (hbV : V ≤ centralizer ({b} : Set G))
    {E : Subgroup G} (hE : IsKleinFour E) (hEK : E ≤ K) (hEa : E ≤ centralizer ({a} : Set G))
    (hEb : E ≤ centralizer ({b} : Set G)) (hEV : E ≤ centralizer (V : Set G)) :
    theta V b ⊓ centralizer ({a} : Set G) ≤ theta V a := by
  obtain ⟨ε, hεE, hε1⟩ := exists_mem_ne_one_of_isKleinFour hE
  have hε2 : orderOf ε = 2 := orderOf_eq_two_of_isKleinFour hE hεE hε1
  have hεb : ε * b = b * ε := mem_centralizer_singleton_iff.mp (hEb hεE)
  have hVε : V ≤ centralizer ({ε} : Set G) := fun v hv =>
    mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp (hEV hεE)) v hv)
  have hPa := conjClosure_le_of_isKleinFour hq hR1 hG hN hK' hK hne.symm haQ ha2 hE hEK hEa
  have hV2 : IsPGroup 2 V := isPGroup_of_isKleinFour hV
  have hba : b ∈ centralizer ({a} : Set G) := mem_centralizer_singleton_iff.mpr hab.symm
  have hold := component_dichotomy_of_pump_of_le hK' haQ ha2 hPa
    (S₁ := V) (S₂ := zpowers b) hV2 (le_inf hVK' haV) (zpowers_le.mpr hbQ)
    (zpowers_le.mpr hba)
  exact theta_inf_le_theta_of_target_dichotomy hV ha2 hb2 hab haV hbV
    (component_dichotomy_of_pump_swap hab hold)
    (theta_inf_centralizer_le_of_mem hq hR1 hG hN hK hK' hne hV hVK' hb2 hbQ hbV
      (hEK hεE) hε2 hεb hVε)

theorem isSolvableSignalizerFunctor_theta_of_mem (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') {V B E : Subgroup G} (hV : IsKleinFour V) (hVK' : V ≤ K')
    (hBQ : B ≤ coreActionKernel K') (hBV : B ≤ centralizer (V : Set G))
    (hB : CFSG.Open.IsElemAbelian 2 B) (hE : IsKleinFour E) (hEB : E ≤ B) (hEK : E ≤ K) :
    CFSG.Open.IsSolvableSignalizerFunctor 2 B (theta V) := by
  have hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hB.1.is_comm.comm (⟨x, hx⟩ : B) ⟨y, hy⟩)
  have hinv : ∀ a ∈ B, a ≠ 1 → orderOf a = 2 := fun a ha ha1 => orderOf_eq_prime (hB.2 a ha) ha1
  have hVa : ∀ a ∈ B, V ≤ centralizer ({a} : Set G) := fun a ha w hw =>
    mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp (hBV ha)) w hw)
  have hBa : ∀ a ∈ B, B ≤ centralizer ({a} : Set G) := fun a ha x hx =>
    mem_centralizer_singleton_iff.mpr (hBc x hx a ha)
  refine isSolvableSignalizerFunctor_theta_of_balance (B := B) (V := V) hB.1 hBV ?_
  intro a ha ha1 b hb hb1
  exact theta_inf_le_theta_of_mem hq hR1 hG hN hK hK' hne hV hVK' (hinv b hb hb1) (hBQ hb)
    (hinv a ha ha1) (hBQ ha) (hBc b hb a ha) (hVa b hb) (hVa a ha) hE hEK
    (hEB.trans (hBa b hb)) (hEB.trans (hBa a ha)) (hEB.trans hBV)

theorem wGroup_spec_of_mem (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') {V B E : Subgroup G} (hV : IsKleinFour V) (hVK' : V ≤ K')
    (hBQ : B ≤ coreActionKernel K') (hBV : B ≤ centralizer (V : Set G))
    (hB : CFSG.Open.IsElemAbelian 2 B) (hE : IsKleinFour E) (hEB : E ≤ B) (hEK : E ≤ K)
    (h8 : 2 ^ 3 ∣ Nat.card B) :
    Nat.Coprime 2 (Nat.card (wGroup B V)) ∧ Group.IsSolvable (wGroup B V) ∧
      ∀ b ∈ B, b ≠ 1 → theta V b = wGroup B V ⊓ centralizer ({b} : Set G) :=
  CFSG.SignalizerFunctorTheorem.Solvable.glauberman_of_le_three G 2 Nat.prime_two (by norm_num) B
    hB.1 hB.2 h8 (theta V)
    (isSolvableSignalizerFunctor_theta_of_mem hq hR1 hG hN hK hK' hne hV hVK' hBQ hBV hB hE hEB hEK)

end CFSG.ComponentClassification.Sol76.Sig
