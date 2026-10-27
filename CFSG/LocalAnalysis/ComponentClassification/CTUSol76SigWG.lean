module

public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigFunctorG
public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigH

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.Sol76T13
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {N K K' : Subgroup G}

theorem theta_le_wGroup_of_commute_of_mem (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') {V F : Subgroup G} (hV : IsKleinFour V) (hVK' : V ≤ K') (hF : IsKleinFour F)
    (hFK : F ≤ K) (hFV : F ≤ centralizer (V : Set G)) {e : G} (he2 : orderOf e = 2)
    (heQ : e ∈ coreActionKernel K') (heV : V ≤ centralizer ({e} : Set G))
    (heF : F ≤ centralizer ({e} : Set G)) :
    theta V e ≤ wGroup F V := by
  have hθle : theta V e ≤ oddCoreIn (centralizer ({e} : Set G)) := theta_le_oddCoreIn heV
  have hcop : Nat.Coprime 2 (Nat.card (theta V e)) := Nat.Coprime.coprime_dvd_right
    (Subgroup.card_dvd_of_le hθle) (coprime_card_oddCoreIn _)
  have hFθ : F ≤ normalizer (theta V e : Set G) :=
    le_normalizer_theta (heF.trans le_normalizer)
      (fun _ h => Subgroup.centralizer_le_normalizer (V : Set G) (hFV h))
      (fun _ h => le_normalizer (hFV h))
  have hFc := comm_of_isKleinFour hF
  refine (le_iSup_inf_centralizer_of_isKleinFour hF hFθ hcop).trans ?_
  refine iSup₂_le fun f hf => iSup_le fun hf1 => ?_
  have hf2 : orderOf f = 2 := orderOf_eq_two_of_isKleinFour hF hf hf1
  have hfV : V ≤ centralizer ({f} : Set G) := fun w hw =>
    mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp (hFV hf)) w hw)
  have hfe : f * e = e * f := mem_centralizer_singleton_iff.mp (heF hf)
  have hfQ : f ∈ coreActionKernel K' := mem_coreActionKernel_of_ne hK hK' hne (hFK hf)
  have hFf : F ≤ centralizer ({f} : Set G) := fun x hx =>
    mem_centralizer_singleton_iff.mpr (hFc x hx f hf)
  exact (theta_inf_le_theta_of_mem hq hR1 hG hN hK hK' hne hV hVK' hf2 hfQ he2 heQ hfe hfV heV
    hF hFK hFf heF hFV).trans (theta_le_wGroup hf hf1)

theorem wGroup_eq_of_commute (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') {V E F : Subgroup G} (hV : IsKleinFour V) (hVK' : V ≤ K') (hE : IsKleinFour E)
    (hEQ : E ≤ coreActionKernel K') (hEV : E ≤ centralizer (V : Set G)) (hF : IsKleinFour F)
    (hFK : F ≤ K) (hFV : F ≤ centralizer (V : Set G)) (hEF : E ≤ centralizer (F : Set G)) :
    wGroup E V = wGroup F V := by
  have hFE : F ≤ centralizer (E : Set G) := fun f hf => mem_centralizer_iff.mpr fun e he =>
    ((mem_centralizer_iff.mp (hEF he)) f hf).symm
  refine le_antisymm (iSup₂_le fun e he => iSup_le fun he1 => ?_)
    (iSup₂_le fun f hf => iSup_le fun hf1 => ?_)
  · have he2 : orderOf e = 2 := orderOf_eq_two_of_isKleinFour hE he he1
    exact theta_le_wGroup_of_commute_of_mem hq hR1 hG hN hK hK' hne hV hVK' hF hFK hFV he2
      (hEQ he) (le_centralizer_singleton_of_mem hEV he) (le_centralizer_singleton_of_mem hEF he)
  ·
    have hf2 : orderOf f = 2 := orderOf_eq_two_of_isKleinFour hF hf hf1
    have hfV : V ≤ centralizer ({f} : Set G) := le_centralizer_singleton_of_mem hFV hf
    have hfQ : f ∈ coreActionKernel K' := mem_coreActionKernel_of_ne hK hK' hne (hFK hf)
    have hθle : theta V f ≤ oddCoreIn (centralizer ({f} : Set G)) := theta_le_oddCoreIn hfV
    have hcop : Nat.Coprime 2 (Nat.card (theta V f)) := Nat.Coprime.coprime_dvd_right
      (Subgroup.card_dvd_of_le hθle) (coprime_card_oddCoreIn _)
    have hEθ : E ≤ normalizer (theta V f : Set G) :=
      le_normalizer_theta ((le_centralizer_singleton_of_mem hFE hf).trans le_normalizer)
        (fun _ h => Subgroup.centralizer_le_normalizer (V : Set G) (hEV h))
        (fun _ h => le_normalizer (hEV h))
    have hFc := comm_of_isKleinFour hF
    refine (le_iSup_inf_centralizer_of_isKleinFour hE hEθ hcop).trans ?_
    refine iSup₂_le fun e he => iSup_le fun he1 => ?_
    have he2 : orderOf e = 2 := orderOf_eq_two_of_isKleinFour hE he he1
    have hef : e * f = f * e := (mem_centralizer_iff.mp (hEF he)) f hf |>.symm
    have hFf : F ≤ centralizer ({f} : Set G) := fun x hx =>
      mem_centralizer_singleton_iff.mpr (hFc x hx f hf)
    exact (theta_inf_le_theta_of_mem hq hR1 hG hN hK hK' hne hV hVK' he2 (hEQ he) hf2 hfQ hef
      (le_centralizer_singleton_of_mem hEV he) hfV hF hFK
      (le_centralizer_singleton_of_mem hEF he) hFf hFV).trans (theta_le_wGroup he he1)

theorem wGroup_eq_of_le_of_mem (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') {V B E S : Subgroup G} (hV : IsKleinFour V) (hVK' : V ≤ K')
    (hBQ : B ≤ coreActionKernel K') (hBV : B ≤ centralizer (V : Set G))
    (hB : CFSG.Open.IsElemAbelian 2 B) (hE : IsKleinFour E) (hEB : E ≤ B) (hEK : E ≤ K)
    (hS : IsKleinFour S) (hSB : S ≤ B) : wGroup S V = wGroup B V := by
  have hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hB.1.is_comm.comm (⟨x, hx⟩ : B) ⟨y, hy⟩)
  have hbalance : ∀ b ∈ B, b ≠ 1 → ∀ s ∈ S, s ≠ 1 →
      theta V b ⊓ centralizer ({s} : Set G) ≤ theta V s := by
    intro b hb hb1 s hs hs1
    have hb2 : orderOf b = 2 := orderOf_eq_prime (hB.2 b hb) hb1
    have hs2 : orderOf s = 2 := orderOf_eq_prime (hB.2 s (hSB hs)) hs1
    have hsb : s * b = b * s := hBc s (hSB hs) b hb
    have hEs : E ≤ centralizer ({s} : Set G) := fun e he =>
      mem_centralizer_singleton_iff.mpr (hBc e (hEB he) s (hSB hs))
    have hEb : E ≤ centralizer ({b} : Set G) := fun e he =>
      mem_centralizer_singleton_iff.mpr (hBc e (hEB he) b hb)
    exact theta_inf_le_theta_of_mem hq hR1 hG hN hK hK' hne hV hVK'
      hs2 (hBQ (hSB hs)) hb2 (hBQ hb) hsb
      (le_centralizer_singleton_of_mem hBV (hSB hs)) (le_centralizer_singleton_of_mem hBV hb)
      hE hEK hEs hEb (hEB.trans hBV)
  exact (wGroup_eq_of_cross_balance hS hSB hBc hBV hbalance).symm

theorem theta_le_theta_zpowers_of_mem (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') {V F : Subgroup G} (hV : IsKleinFour V) (hVK' : V ≤ K') (hF : IsKleinFour F)
    (hFK : F ≤ K) (hFV : F ≤ centralizer (V : Set G)) {e : G} (he2 : orderOf e = 2)
    (heQ : e ∈ coreActionKernel K') (heV : V ≤ centralizer ({e} : Set G))
    (heF : F ≤ centralizer ({e} : Set G)) {v : G} (hv : v ∈ V) (hv1 : v ≠ 1) :
    theta V e ≤ theta (zpowers v) e := by
  have h32 := lemma32FullFor_simple_of_twoPart hq hR1
  set Oe := oddCoreIn (centralizer ({e} : Set G)) with hOe
  set Cv := centralizer ({v} : Set G) with hCv
  have hVc := comm_of_isKleinFour hV
  have hFc := comm_of_isKleinFour hF
  have hv2 : orderOf v = 2 := orderOf_eq_two_of_isKleinFour hV hv hv1
  have hzv2 : IsPGroup 2 (zpowers v) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hv2, pow_one])
  have hVCV : V ≤ centralizer (V : Set G) := le_centralizer_of_le_of_comm le_rfl hVc
  have hVθ : V ≤ normalizer (theta V e : Set G) :=
    le_normalizer_theta (heV.trans le_normalizer) le_normalizer (hVCV.trans le_normalizer)
  have hθle : theta V e ≤ Oe := theta_le_oddCoreIn heV
  have hcop : Nat.Coprime 2 (Nat.card (theta V e)) := Nat.Coprime.coprime_dvd_right
    (Subgroup.card_dvd_of_le hθle) (coprime_card_oddCoreIn _)
  have hzvθ : zpowers v ≤ normalizer (theta V e : Set G) := (zpowers_le.mpr hv).trans hVθ
  have hfac := CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_factorization 2
    Nat.prime_two (zpowers v) (theta V e) hzv2 hzvθ hcop
  rw [centralizer_zpowers_eq] at hfac
  rw [← hfac]
  refine sup_le ?_ ?_
  · exact le_sup_of_le_left (Subgroup.commutator_mono hθle le_rfl)
  · refine le_sup_of_le_right (le_inf (inf_le_left.trans hθle) ?_)
    rw [centralizer_zpowers_eq]
    set Y := theta V e ⊓ Cv with hY
    have hFY : F ≤ normalizer (Y : Set G) := by
      intro x hx
      have hxθ : x ∈ normalizer (theta V e : Set G) :=
        le_normalizer_theta (heF.trans le_normalizer)
          (fun _ h => Subgroup.centralizer_le_normalizer (V : Set G) (hFV h))
          (fun _ h => le_normalizer (hFV h)) hx
      exact mem_normalizer_inf hxθ (le_normalizer (show x ∈ Cv from
        mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp (hFV hx)) v hv).symm))
    have hYcop : Nat.Coprime 2 (Nat.card Y) := Nat.Coprime.coprime_dvd_right
      (Subgroup.card_dvd_of_le inf_le_left) hcop
    refine (le_iSup_inf_centralizer_of_isKleinFour hF hFY hYcop).trans ?_
    refine iSup₂_le fun f hf => iSup_le fun hf1 => ?_
    have hf2 : orderOf f = 2 := orderOf_eq_two_of_isKleinFour hF hf hf1
    have hfV : V ≤ centralizer ({f} : Set G) := le_centralizer_singleton_of_mem hFV hf
    have hfe : f * e = e * f := mem_centralizer_singleton_iff.mp (heF hf)
    have hfQ : f ∈ coreActionKernel K' := mem_coreActionKernel_of_ne hK hK' hne (hFK hf)
    have hFf : F ≤ centralizer ({f} : Set G) := fun x hx =>
      mem_centralizer_singleton_iff.mpr (hFc x hx f hf)
    have hbal := theta_inf_le_theta_of_mem hq hR1 hG hN hK hK' hne hV hVK' hf2 hfQ he2 heQ hfe
      hfV heV hF hFK hFf heF hFV
    intro y hy
    exact theta_inf_le_oddCoreIn_of_mem h32 hG hN hK hK' hne hV hVK' (hFK hf) hf2 hfV hv hv1
      ⟨hbal ⟨hy.1.1, hy.2⟩, hy.1.2⟩

theorem wGroup_eq_wGroup_zpowers_of_mem (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') {V S F : Subgroup G} (hV : IsKleinFour V) (hVK' : V ≤ K')
    (hS : IsKleinFour S) (hSQ : S ≤ coreActionKernel K') (hSV : S ≤ centralizer (V : Set G))
    (hF : IsKleinFour F) (hFK : F ≤ K) (hFV : F ≤ centralizer (V : Set G))
    (hSF : S ≤ centralizer (F : Set G)) {v : G} (hv : v ∈ V) (hv1 : v ≠ 1) :
    wGroup S V = wGroup S (zpowers v) := by
  refine le_antisymm (iSup₂_le fun e he => iSup_le fun he1 => ?_)
    (iSup₂_le fun e he => iSup_le fun he1 => ?_)
  · have he2 : orderOf e = 2 := orderOf_eq_two_of_isKleinFour hS he he1
    exact (theta_le_theta_zpowers_of_mem hq hR1 hG hN hK hK' hne hV hVK' hF hFK hFV he2 (hSQ he)
      (le_centralizer_singleton_of_mem hSV he) (le_centralizer_singleton_of_mem hSF he) hv
      hv1).trans (theta_le_wGroup he he1)
  · exact (theta_mono (zpowers_le.mpr hv) (isPGroup_of_isKleinFour hV) (comm_of_isKleinFour hV)
      (le_centralizer_singleton_of_mem hSV he)).trans (theta_le_wGroup he he1)

theorem wGroup_eq_of_two_actual_hulls
    {B E F : Subgroup G}
    (hE : IsKleinFour E) (hF : IsKleinFour F)
    (hEB : E ≤ B) (hBF : B ≤ centralizer (F : Set G))
    (hB : CFSG.Open.IsElemAbelian 2 B)
    (hleft : ∀ e ∈ E, e ≠ 1 → ∃ J : Subgroup G,
      IsTwoComponentIn J (centralizer ({e} : Set G)) ∧
        F ≤ J ∧ B ≤ coreActionKernel J)
    (hright : ∀ u ∈ F, u ≠ 1 → ∃ I : Subgroup G,
      IsTwoComponentIn I (centralizer ({u} : Set G)) ∧
        E ≤ I ∧ ⁅I, F⁆ ≤ oddCoreIn (centralizer ({u} : Set G))) :
    wGroup B F = wGroup E F := by
  refine wGroup_eq_of_cross_balance hE hEB (fun x hx y hy => hB.comm hx hy) hBF ?_
  intro b hb hb1 e he he1
  have hb2 : orderOf b = 2 := orderOf_eq_prime (hB.2 b hb) hb1
  have he2 : orderOf e = 2 := orderOf_eq_two_of_isKleinFour hE he he1
  have hbe : e * b = b * e := hB.comm (hEB he) hb
  have hFe : F ≤ centralizer ({e} : Set G) := fun w hw =>
    mem_centralizer_singleton_iff.mpr
      ((mem_centralizer_iff.mp (hBF (hEB he))) w hw)
  have hFb : F ≤ centralizer ({b} : Set G) := fun w hw =>
    mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp (hBF hb)) w hw)
  obtain ⟨J, hJ, hFJ, hBJ⟩ := hleft e he he1
  have hlocal := component_dichotomy_of_actual_hull_kernel (D := centralizer ({e} : Set G))
    (J := J) (S := zpowers b) (V := F) hJ (zpowers_le.mpr (hBJ hb)) hFJ
  have hfixed := theta_inf_centralizer_le_of_two_actual_hulls hE hF hEB hBF hB hleft hright hb hb1
  exact theta_inf_le_theta_of_target_dichotomy hF he2 hb2 hbe hFe hFb hlocal hfixed

theorem le_normalizer_wGroup_of_odd_of_two_actual_hulls
    {B E F X : Subgroup G}
    (hE : IsKleinFour E) (hF : IsKleinFour F)
    (hEB : E ≤ B) (hBF : B ≤ centralizer (F : Set G))
    (hB : CFSG.Open.IsElemAbelian 2 B)
    (hleft : ∀ e ∈ E, e ≠ 1 → ∃ J : Subgroup G,
      IsTwoComponentIn J (centralizer ({e} : Set G)) ∧
        F ≤ J ∧ B ≤ coreActionKernel J ∧
          IsSimpleGroup (↥J ⧸ pPrimeCore 2 ↥J))
    (hright : ∀ u ∈ F, u ≠ 1 → ∃ I : Subgroup G,
      IsTwoComponentIn I (centralizer ({u} : Set G)) ∧
        E ≤ I ∧ ⁅I, F⁆ ≤ oddCoreIn (centralizer ({u} : Set G)))
    (hX : Nat.Coprime 2 (Nat.card X))
    (hEX : E ≤ normalizer (X : Set G))
    (hFX : F ≤ normalizer (X : Set G)) :
    X ≤ normalizer (wGroup B F : Set G) := by
  have hleft' : ∀ e ∈ E, e ≠ 1 → ∃ J : Subgroup G,
      IsTwoComponentIn J (centralizer ({e} : Set G)) ∧
        F ≤ J ∧ B ≤ coreActionKernel J := by
    intro e he he1
    obtain ⟨J, hJ, hFJ, hBJ, -⟩ := hleft e he he1
    exact ⟨J, hJ, hFJ, hBJ⟩
  have hEFfix : ∀ b ∈ E, b ≠ 1 → ∀ v ∈ F, v ≠ 1 →
      theta F b ⊓ centralizer ({v} : Set G) ≤
        oddCoreIn (centralizer ({v} : Set G)) := by
    intro b hb hb1 v hv hv1
    have hb2 : orderOf b = 2 := orderOf_eq_two_of_isKleinFour hE hb hb1
    have hFb : F ≤ centralizer ({b} : Set G) := fun w hw =>
      mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp (hBF (hEB hb))) w hw)
    refine theta_inf_le_oddCoreIn_of_component_dichotomy hF hb2 hFb ?_ hv hv1
    refine component_dichotomy_of_actual_hulls (V := F) (f := b) ?_
    intro w hw hw1
    obtain ⟨I, hI, hEI, hIF⟩ := hright w hw hw1
    exact ⟨I, hI, hEI hb, hIF⟩
  have hFEfix : ∀ v ∈ F, v ≠ 1 → ∀ b ∈ E, b ≠ 1 →
      theta E v ⊓ centralizer ({b} : Set G) ≤
        oddCoreIn (centralizer ({b} : Set G)) := by
    intro v hv hv1 b hb hb1
    have hv2 : orderOf v = 2 := orderOf_eq_two_of_isKleinFour hF hv hv1
    have hEv : E ≤ centralizer ({v} : Set G) := fun e he =>
      mem_centralizer_singleton_iff.mpr
        (((Subgroup.mem_centralizer_iff.mp (hBF (hEB he))) v hv).symm)
    refine theta_inf_le_oddCoreIn_of_component_dichotomy hE hv2 hEv ?_ hb hb1
    refine component_dichotomy_of_actual_hulls (V := E) (f := v) ?_
    intro w hw hw1
    obtain ⟨J, hJ, hFJ, hBJ⟩ := hleft' w hw hw1
    refine ⟨J, hJ, hFJ hv, ?_⟩
    exact (commutator_le_oddCoreIn_of_le_coreActionKernel
      (S := E) (J := J) (fun e he => hBJ (hEB he))).trans
        (oddCoreIn_le_of_isTwoComponentIn hJ)
  have hlocal : ∀ b ∈ E, b ≠ 1 →
      let C := centralizer ({b} : Set G)
      let π := QuotientGroup.mk' (pPrimeCore 2 ↥C)
      ∃ S : Subgroup (↥C ⧸ pPrimeCore 2 ↥C),
        CFSG.IsComponent S ∧ IsSimpleGroup ↥S ∧
        (F.subgroupOf C).map π ≤ S ∧
        (E.subgroupOf C).map π ≤ centralizer (S : Set _) := by
    intro b hb hb1
    obtain ⟨J, hJ, hFJ, hBJ, hJsimple⟩ := hleft b hb hb1
    have hEC : E ≤ centralizer ({b} : Set G) := fun e he =>
      mem_centralizer_singleton_iff.mpr (hB.comm (hEB he) (hEB hb))
    have hJE : ⁅J, E⁆ ≤ oddCoreIn (centralizer ({b} : Set G)) :=
      (commutator_le_oddCoreIn_of_le_coreActionKernel
        (S := E) (J := J) (fun e he => hBJ (hEB he))).trans
        (oddCoreIn_le_of_isTwoComponentIn hJ)
    exact exists_image_component_simple_of_commutator_le_oddCoreIn hJ hJsimple hEC hFJ hJE
  have hle := le_normalizer_wGroup_of_odd_of_local_data hE hF (hEB.trans hBF)
    hEFfix hFEfix hlocal hX hEX hFX
  rw [← wGroup_eq_of_two_actual_hulls hE hF hEB hBF hB hleft' hright] at hle
  exact hle

theorem le_normalizer_wGroup_oddCoreIn_centralizer_of_two_actual_hulls
    {B E F : Subgroup G} {s : G}
    (hE : IsKleinFour E) (hF : IsKleinFour F)
    (hEB : E ≤ B) (hBF : B ≤ centralizer (F : Set G))
    (hB : CFSG.Open.IsElemAbelian 2 B)
    (hleft : ∀ e ∈ E, e ≠ 1 → ∃ J : Subgroup G,
      IsTwoComponentIn J (centralizer ({e} : Set G)) ∧
        F ≤ J ∧ B ≤ coreActionKernel J ∧
          IsSimpleGroup (↥J ⧸ pPrimeCore 2 ↥J))
    (hright : ∀ u ∈ F, u ≠ 1 → ∃ I : Subgroup G,
      IsTwoComponentIn I (centralizer ({u} : Set G)) ∧
        E ≤ I ∧ ⁅I, F⁆ ≤ oddCoreIn (centralizer ({u} : Set G)))
    (hEs : E ≤ centralizer ({s} : Set G))
    (hFs : F ≤ centralizer ({s} : Set G)) :
    oddCoreIn (centralizer ({s} : Set G)) ≤ normalizer (wGroup B F : Set G) :=
  le_normalizer_wGroup_of_odd_of_two_actual_hulls hE hF hEB hBF hB hleft hright
    (coprime_card_oddCoreIn (centralizer ({s} : Set G)))
    (hEs.trans (le_normalizer_oddCoreIn _))
    (hFs.trans (le_normalizer_oddCoreIn _))

theorem le_normalizer_wGroup_of_mem_of_mem (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') {V B E S : Subgroup G} (hV : IsKleinFour V) (hVK' : V ≤ K')
    (hBQ : B ≤ coreActionKernel K') (hBV : B ≤ centralizer (V : Set G))
    (hB : CFSG.Open.IsElemAbelian 2 B) (hE : IsKleinFour E) (hEB : E ≤ B) (hEK : E ≤ K)
    (hS : IsKleinFour S) (hSB : S ≤ B) {v : G} (hv : v ∈ V) (hv1 : v ≠ 1) {g : G}
    (hgS : g ∈ normalizer (S : Set G)) (hgv : g ∈ centralizer ({v} : Set G)) :
    g ∈ normalizer (wGroup B V : Set G) := by
  have hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hB.1.is_comm.comm (⟨x, hx⟩ : B) ⟨y, hy⟩)
  have hSE : S ≤ centralizer (E : Set G) := fun x hx => mem_centralizer_iff.mpr fun y hy =>
    hBc y (hEB hy) x (hSB hx)
  rw [← wGroup_eq_of_le_of_mem hq hR1 hG hN hK hK' hne hV hVK' hBQ hBV hB hE hEB hEK hS hSB,
    wGroup_eq_wGroup_zpowers_of_mem hq hR1 hG hN hK hK' hne hV hVK' hS (hSB.trans hBQ)
      (hSB.trans hBV) hE hEK (hEB.trans hBV) hSE hv hv1]
  refine le_normalizer_wGroup hgS ?_
  rw [← centralizer_zpowers_eq] at hgv
  exact Subgroup.centralizer_le_normalizer ((zpowers v : Subgroup G) : Set G) hgv

theorem le_normalizer_wGroup_of_odd_of_mem (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') {V B E X : Subgroup G} (hV : IsKleinFour V) (hVK' : V ≤ K')
    (hBQ : B ≤ coreActionKernel K') (hBV : B ≤ centralizer (V : Set G))
    (hB : CFSG.Open.IsElemAbelian 2 B) (hE : IsKleinFour E) (hEB : E ≤ B) (hEK : E ≤ K)
    (hB8 : Nat.card B = 8) (hXodd : Nat.Coprime 2 (Nat.card X))
    (hBX : B ≤ normalizer (X : Set G)) (hVX : V ≤ normalizer (X : Set G)) :
    X ≤ normalizer (wGroup B V : Set G) := by
  have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 2 2
    Nat.prime_two B X hB (by rw [hB8]; norm_num) hBX hXodd
  refine hgen.symm.le.trans (iSup₂_le fun S hS => ?_)
  obtain ⟨hSB, hScard⟩ := hS
  have hSK : IsKleinFour S :=
    isKleinFour_of_card_eq_four (by rw [hScard]; norm_num) fun x hx => hB.2 x (hSB hx)
  set Y := X ⊓ centralizer (S : Set G) with hY
  have hVS : V ≤ centralizer (S : Set G) := fun v hv => mem_centralizer_iff.mpr fun s hs =>
    ((mem_centralizer_iff.mp (hBV (hSB hs))) v hv).symm
  have hVY : V ≤ normalizer (Y : Set G) := fun v hv =>
    mem_normalizer_inf (hVX hv) (le_normalizer (hVS hv))
  have hYodd : Nat.Coprime 2 (Nat.card Y) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left) hXodd
  have hgen2 := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 2 1
    Nat.prime_two V Y (isElemAbelian_of_isKleinFour hV) (by rw [hV.card_four]; norm_num) hVY
    hYodd
  refine hgen2.symm.le.trans (iSup₂_le fun T hT => ?_)
  obtain ⟨hTV, hTcard⟩ := hT
  have : Nontrivial T := Finite.one_lt_card_iff_nontrivial.mp (by rw [hTcard]; norm_num)
  obtain ⟨t, ht⟩ := exists_ne (1 : ↥T)
  have ht1 : (t : G) ≠ 1 := fun h => ht (Subtype.ext h)
  intro y hy
  have hyS : y ∈ normalizer (S : Set G) :=
    Subgroup.centralizer_le_normalizer (S : Set G) hy.1.2
  have hyt : y ∈ centralizer ({(t : G)} : Set G) :=
    centralizer_le (Set.singleton_subset_iff.mpr t.2) hy.2
  exact le_normalizer_wGroup_of_mem_of_mem hq hR1 hG hN hK hK' hne hV hVK' hBQ hBV hB hE hEB hEK
    hSK hSB (hTV t.2) ht1 hyS hyt

end CFSG.ComponentClassification.Sol76.Sig
