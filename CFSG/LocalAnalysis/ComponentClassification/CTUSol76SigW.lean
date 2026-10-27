module

public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigFunctor

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.Sol76T13
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {𝒜 : Thm13Ambient} {N K K' : Subgroup G}

theorem le_iSup_inf_centralizer_of_isKleinFour {F X : Subgroup G} (hF : IsKleinFour F)
    (hFX : F ≤ normalizer (X : Set G)) (hX : Nat.Coprime 2 (Nat.card X)) :
    X ≤ ⨆ (f : G) (_ : f ∈ F) (_ : f ≠ 1), X ⊓ centralizer ({f} : Set G) := by
  have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 2 1
    Nat.prime_two F X (isElemAbelian_of_isKleinFour hF)
    (by rw [hF.card_four]; norm_num) hFX hX
  refine hgen.symm.le.trans (iSup₂_le fun S hS => ?_)
  obtain ⟨hSF, hScard⟩ := hS
  have : Nontrivial S := Finite.one_lt_card_iff_nontrivial.mp (by rw [hScard]; norm_num)
  obtain ⟨s, hs⟩ := exists_ne (1 : ↥S)
  have hs1 : (s : G) ≠ 1 := fun h => hs (Subtype.ext h)
  have hs2 : orderOf (s : G) = 2 := orderOf_eq_two_of_isKleinFour hF (hSF s.2) hs1
  have hSz : zpowers (s : G) = S := Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr s.2)
    (by rw [hScard, Nat.card_zpowers, hs2, pow_one])
  rw [← hSz, centralizer_zpowers_eq]
  exact le_iSup₂_of_le (s : G) (hSF s.2) (le_iSup_of_le hs1 le_rfl)

theorem wGroup_eq_of_cross_balance {B E F : Subgroup G}
    (hE : IsKleinFour E) (hEB : E ≤ B)
    (hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (hBF : B ≤ centralizer (F : Set G))
    (hbalance : ∀ b ∈ B, b ≠ 1 → ∀ e ∈ E, e ≠ 1 →
      theta F b ⊓ centralizer ({e} : Set G) ≤ theta F e) :
    wGroup B F = wGroup E F := by
  have hEF : E ≤ centralizer (F : Set G) := hEB.trans hBF
  refine le_antisymm ?_ ?_
  · refine iSup₂_le fun b hb => iSup_le fun hb1 => ?_
    have hFb : F ≤ centralizer ({b} : Set G) := fun f hf =>
      mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp (hBF hb)) f hf)
    have hEb : E ≤ centralizer ({b} : Set G) := fun e he =>
      mem_centralizer_singleton_iff.mpr (hBc e (hEB he) b hb)
    have hFθ : E ≤ normalizer (theta F b : Set G) :=
      le_normalizer_theta (hEb.trans le_normalizer)
        (fun e he => Subgroup.centralizer_le_normalizer (F : Set G) (hEF he))
        (fun e he => le_normalizer (hEF he))
    have hcop : Nat.Coprime 2 (Nat.card (theta F b)) :=
      Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le (theta_le_oddCoreIn hFb))
        (coprime_card_oddCoreIn _)
    refine (le_iSup_inf_centralizer_of_isKleinFour hE hFθ hcop).trans ?_
    refine iSup₂_le fun e he => iSup_le fun he1 => ?_
    exact (hbalance b hb hb1 e he he1).trans (theta_le_wGroup he he1)
  · exact iSup₂_le fun e he => iSup_le fun he1 => theta_le_wGroup (hEB he) he1

theorem theta_eq_theta_zpowers_of_fixed_bound {V : Subgroup G} {b v : G}
    (hV : IsKleinFour V)
    (hVb : V ≤ centralizer ({b} : Set G))
    (hv : v ∈ V) (hv1 : v ≠ 1)
    (hfix : theta V b ⊓ centralizer ({v} : Set G) ≤
      oddCoreIn (centralizer ({v} : Set G))) :
    theta V b = theta (zpowers v) b := by
  have hVc := comm_of_isKleinFour hV
  have hv2 : orderOf v = 2 := orderOf_eq_two_of_isKleinFour hV hv hv1
  have hzv2 : IsPGroup 2 (zpowers v) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hv2, pow_one])
  have hVCV : V ≤ centralizer (V : Set G) := le_centralizer_of_le_of_comm le_rfl hVc
  have hVθ : V ≤ normalizer (theta V b : Set G) :=
    le_normalizer_theta (hVb.trans le_normalizer) le_normalizer (hVCV.trans le_normalizer)
  have hθle : theta V b ≤ oddCoreIn (centralizer ({b} : Set G)) := theta_le_oddCoreIn hVb
  have hcop : Nat.Coprime 2 (Nat.card (theta V b)) := Nat.Coprime.coprime_dvd_right
    (Subgroup.card_dvd_of_le hθle) (coprime_card_oddCoreIn _)
  have hzvθ : zpowers v ≤ normalizer (theta V b : Set G) := (zpowers_le.mpr hv).trans hVθ
  have hfac := CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_factorization 2
    Nat.prime_two (zpowers v) (theta V b) hzv2 hzvθ hcop
  rw [centralizer_zpowers_eq] at hfac
  refine le_antisymm ?_ ?_
  · rw [← hfac]
    refine sup_le ?_ ?_
    · exact le_sup_of_le_left (Subgroup.commutator_mono hθle le_rfl)
    · refine le_sup_of_le_right (le_inf (inf_le_left.trans hθle) ?_)
      rw [centralizer_zpowers_eq]
      exact hfix
  · exact theta_mono (zpowers_le.mpr hv) (isPGroup_of_isKleinFour hV)
      (comm_of_isKleinFour hV) hVb

private theorem wGroup_le_wGroup_of_fixed_bounds {E F : Subgroup G}
    (hE : IsKleinFour E) (hF : IsKleinFour F)
    (hEF : E ≤ centralizer (F : Set G))
    (hfix : ∀ b ∈ E, b ≠ 1 → ∀ v ∈ F, v ≠ 1 →
      theta F b ⊓ centralizer ({v} : Set G) ≤
        oddCoreIn (centralizer ({v} : Set G))) :
    wGroup E F ≤ wGroup F E := by
  refine iSup₂_le fun b hb => iSup_le fun hb1 => ?_
  have hFb : F ≤ centralizer ({b} : Set G) := fun f hf =>
    mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp (hEF hb)) f hf)
  have hFc := comm_of_isKleinFour hF
  have hFθ : F ≤ normalizer (theta F b : Set G) :=
    le_normalizer_theta (hFb.trans le_normalizer) le_normalizer
      ((le_centralizer_of_le_of_comm le_rfl hFc).trans le_normalizer)
  have hθle : theta F b ≤ oddCoreIn (centralizer ({b} : Set G)) := theta_le_oddCoreIn hFb
  have hcop : Nat.Coprime 2 (Nat.card (theta F b)) := Nat.Coprime.coprime_dvd_right
    (Subgroup.card_dvd_of_le hθle) (coprime_card_oddCoreIn _)
  refine (le_iSup_inf_centralizer_of_isKleinFour hF hFθ hcop).trans ?_
  refine iSup₂_le fun v hv => iSup_le fun hv1 => ?_
  have hEFv : E ≤ centralizer ({v} : Set G) := fun e he =>
    mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp (hEF he)) v hv).symm
  have hYle : theta F b ⊓ centralizer ({v} : Set G) ≤ theta E v := by
    have hYOb : theta F b ⊓ centralizer ({v} : Set G) ≤
        oddCoreIn (centralizer ({b} : Set G)) := inf_le_left.trans hθle
    have hYOv : theta F b ⊓ centralizer ({v} : Set G) ≤
        oddCoreIn (centralizer ({v} : Set G)) := hfix b hb hb1 v hv hv1
    have hstep : theta F b ⊓ centralizer ({v} : Set G) ≤ theta (zpowers b) v := by
      refine le_sup_of_le_right (le_inf hYOv ?_)
      rw [centralizer_zpowers_eq]
      exact hYOb
    exact hstep.trans (theta_mono (zpowers_le.mpr hb) (isPGroup_of_isKleinFour hE)
      (comm_of_isKleinFour hE) hEFv)
  exact hYle.trans (theta_le_wGroup hv hv1)

theorem wGroup_eq_swap_of_fixed_bounds {E F : Subgroup G}
    (hE : IsKleinFour E) (hF : IsKleinFour F)
    (hEF : E ≤ centralizer (F : Set G))
    (hEFfix : ∀ b ∈ E, b ≠ 1 → ∀ v ∈ F, v ≠ 1 →
      theta F b ⊓ centralizer ({v} : Set G) ≤
        oddCoreIn (centralizer ({v} : Set G)))
    (hFEfix : ∀ v ∈ F, v ≠ 1 → ∀ b ∈ E, b ≠ 1 →
      theta E v ⊓ centralizer ({b} : Set G) ≤
        oddCoreIn (centralizer ({b} : Set G))) :
    wGroup E F = wGroup F E := by
  have hFE : F ≤ centralizer (E : Set G) := fun f hf =>
    mem_centralizer_iff.mpr fun e he => (mem_centralizer_iff.mp (hEF he) f hf).symm
  exact le_antisymm
    (wGroup_le_wGroup_of_fixed_bounds hE hF hEF hEFfix)
    (wGroup_le_wGroup_of_fixed_bounds hF hE hFE hFEfix)

theorem theta_inf_le_oddCoreIn_of_component_dichotomy {V : Subgroup G} {f v : G}
    (hV : IsKleinFour V) (hf2 : orderOf f = 2)
    (hfV : V ≤ centralizer ({f} : Set G))
    (hlocal : ∀ w ∈ V, w ≠ 1 → ∀ M : Subgroup G,
      IsTwoComponentIn M (centralizer ({w} : Set G)) →
        zpowers f ≤ coreActionKernel M ∨
          ⁅M, V⁆ ≤ oddCoreIn (centralizer ({w} : Set G)))
    (hv : v ∈ V) (hv1 : v ≠ 1) :
    theta V f ⊓ centralizer ({v} : Set G) ≤ oddCoreIn (centralizer ({v} : Set G)) := by
  set Of := oddCoreIn (centralizer ({f} : Set G)) with hOf
  set X := ⁅Of, V⁆ with hX
  set T := Of ⊓ oddCoreIn (centralizer (V : Set G)) with hT
  set Cv := centralizer ({v} : Set G) with hCv
  have hV2 := isPGroup_of_isKleinFour hV
  have hVc := comm_of_isKleinFour hV
  have hVe := isElemAbelian_of_isKleinFour hV
  have hV1 : V ≠ ⊥ := fun h => by
    have := hV.card_four
    rw [h, Subgroup.card_bot] at this
    norm_num at this
  have hv2 : orderOf v = 2 := orderOf_eq_two_of_isKleinFour hV hv hv1
  have hVv : V ≤ Cv := fun w hw => mem_centralizer_singleton_iff.mpr (hVc w hw v hv)
  have hfv : f ∈ Cv := mem_centralizer_singleton_iff.mpr
    ((mem_centralizer_singleton_iff.mp (hfV hv)).symm)
  have hfe := isElemAbelian_zpowers (sq_eq_one_of_orderOf_eq_two hf2)
  have hf1 := zpowers_ne_bot_of_orderOf_eq_two hf2
  have hVOf : V ≤ normalizer (Of : Set G) := hfV.trans (le_normalizer_oddCoreIn _)
  have hXOf : X ≤ Of := CFSG.SignalizerFunctor.Helpers.commutator_le_of_normalizing Of V hVOf
  have hB : Of ⊓ oddCoreIn (centralizer (V : Set G)) ⊓ Cv ≤ oddCoreIn Cv := by
    have h := inf_inf_le_oddCoreIn_of_component_dichotomy hv2 hf1 hfe (zpowers_le.mpr hfv)
      hV1 hVe hVv (hlocal v hv hv1)
    rwa [centralizer_zpowers_eq] at h
  have hzv2 : IsPGroup 2 (zpowers v) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hv2, pow_one])
  have hzvV : zpowers v ≤ V := zpowers_le.mpr hv
  have hTX : T ≤ normalizer (X : Set G) := inf_le_left.trans
    (CFSG.SignalizerFunctor.Helpers.normalized_commutator_target_normalizes V Of hVOf)
  have hVCV : V ≤ centralizer (V : Set G) := le_centralizer_of_le_of_comm le_rfl hVc
  have hVT : V ≤ normalizer (T : Set G) := by
    intro w hw
    rw [mem_normalizer_iff]
    intro y
    rw [hT, mem_inf, mem_inf, mem_normalizer_iff.mp (hVOf hw),
      mem_normalizer_iff.mp (le_normalizer_oddCoreIn _ (hVCV hw))]
  have hVX : V ≤ normalizer (X : Set G) := le_normalizer_commutator hVOf
  have hVθ : V ≤ normalizer (theta V f : Set G) :=
    le_normalizer_theta (hfV.trans le_normalizer) le_normalizer (hVCV.trans le_normalizer)
  have hθ : ((theta V f : Subgroup G) : Set G) = (X : Set G) * (T : Set G) := by
    rw [show theta V f = X ⊔ T from rfl]
    exact coe_mul_of_right_le_normalizer_left X T hTX
  have hθle : theta V f ≤ Of := theta_le_oddCoreIn hfV
  have hcop : Nat.Coprime 2 (Nat.card (theta V f)) := Nat.Coprime.coprime_dvd_right
    (Subgroup.card_dvd_of_le hθle) (coprime_card_oddCoreIn _)
  have hfix := CFSG.SignalizerFunctor.Helpers.normalized_product_fixed_points 2 Nat.prime_two
    (zpowers v) (theta V f) X T hzv2 (hzvV.trans hVθ) (hzvV.trans hVX) (hzvV.trans hVT)
    le_sup_left le_sup_right hcop hθ.symm
  rw [centralizer_zpowers_eq] at hfix
  intro y hy
  have hy' : y ∈ (((theta V f) ⊓ Cv : Subgroup G) : Set G) := hy
  rw [← hfix] at hy'
  obtain ⟨x, hx, t, ht, rfl⟩ := hy'
  refine mul_mem ?_ (hB ⟨ht.1, ht.2⟩)
  set Z := X ⊓ Cv with hZ
  have hVZ : V ≤ normalizer (Z : Set G) := by
    intro w hw
    rw [mem_normalizer_iff]
    intro y
    rw [hZ, mem_inf, mem_inf, mem_normalizer_iff.mp (hVX hw),
      mem_normalizer_iff.mp (le_normalizer (hVv hw))]
  have hZcop : Nat.Coprime 2 (Nat.card Z) := Nat.Coprime.coprime_dvd_right
    (Subgroup.card_dvd_of_le (inf_le_left.trans hXOf)) (coprime_card_oddCoreIn _)
  have hZodd : Odd (Nat.card Z) := Nat.coprime_two_left.mp hZcop
  have hZfac := CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_factorization 2
    Nat.prime_two V Z hV2 hVZ hZcop
  have hZO : Z ≤ oddCoreIn Cv := by
    rw [← hZfac]
    refine sup_le ?_ ?_
    ·
      have hZZ : ⁅⁅Z, V⁆, V⁆ = ⁅Z, V⁆ :=
        CFSG.ClassicalInvolution.Balance.commutator_commutator_eq_of_isPGroup hV2 hZodd hVZ
      have hZV : ⁅Z, V⁆ ≤ Z := CFSG.SignalizerFunctor.Helpers.commutator_le_of_normalizing Z V hVZ
      have hvf : v * f = f * v := mem_centralizer_singleton_iff.mp hfv |>.symm
      exact le_oddCoreIn_of_component_dichotomy hv2 hf2 hvf hVv
        (le_inf (hZV.trans (inf_le_left.trans hXOf)) (hZV.trans inf_le_right))
        hZZ (hlocal v hv hv1)
    ·
      intro z hz
      have h1 := theta_inf_centralizer_le_of_component_dichotomy hV hf2 hfV hlocal
        ⟨mem_sup_left hz.1.1, hz.2⟩
      exact hB ⟨h1, hz.1.2⟩
  exact hZO ⟨hx.1, hx.2⟩

theorem theta_inf_le_oddCoreIn_of_mem (h32 : Lemma32FullFor 𝒜) (hG : 𝒜 G)
    (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') {V : Subgroup G} (hV : IsKleinFour V) (hVK' : V ≤ K') {f : G} (hfK : f ∈ K)
    (hf2 : orderOf f = 2) (hfV : V ≤ centralizer ({f} : Set G)) {v : G} (hv : v ∈ V)
    (hv1 : v ≠ 1) :
    theta V f ⊓ centralizer ({v} : Set G) ≤ oddCoreIn (centralizer ({v} : Set G)) := by
  have hVQ : V ≤ coreActionKernel K := hVK'.trans (le_coreActionKernel_of_ne hK hK' hne)
  have hSp : IsPGroup 2 (zpowers f) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hf2, pow_one])
  have hlocal : ∀ w ∈ V, w ≠ 1 → ∀ M : Subgroup G,
      IsTwoComponentIn M (centralizer ({w} : Set G)) →
        zpowers f ≤ coreActionKernel M ∨
          ⁅M, V⁆ ≤ oddCoreIn (centralizer ({w} : Set G)) := by
    intro w hw hw1 M hM
    have hw2 : orderOf w = 2 := orderOf_eq_two_of_isKleinFour hV hw hw1
    have hVw : V ≤ centralizer ({w} : Set G) := fun x hx =>
      mem_centralizer_singleton_iff.mpr (comm_of_isKleinFour hV x hx w hw)
    have hfw : f ∈ centralizer ({w} : Set G) := mem_centralizer_singleton_iff.mpr
      ((mem_centralizer_singleton_iff.mp (hfV hw)).symm)
    exact component_dichotomy_of_pump h32 hG hN hK hK' hne (hVK' hw) hw2
      (S₁ := zpowers f) (S₂ := V) hSp
      (le_inf (zpowers_le.mpr hfK) (zpowers_le.mpr hfw)) hVQ hVw M hM
  exact theta_inf_le_oddCoreIn_of_component_dichotomy hV hf2 hfV hlocal hv hv1

theorem theta_le_theta_zpowers (h32 : Lemma32FullFor 𝒜) (hG : 𝒜 G) (hN : IsSolomonChoice N)
    (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N) (hne : K ≠ K')
    {V : Subgroup G} (hV : IsKleinFour V) (hVK' : V ≤ K') {e : G} (heK : e ∈ K)
    (he2 : orderOf e = 2) (heV : V ≤ centralizer ({e} : Set G)) {v : G}
    (hv : v ∈ V) (hv1 : v ≠ 1) :
    theta V e ≤ theta (zpowers v) e :=
  (theta_eq_theta_zpowers_of_fixed_bound hV heV hv hv1
    (theta_inf_le_oddCoreIn_of_mem h32 hG hN hK hK' hne hV hVK' heK he2 heV hv hv1)).le

theorem theta_le_wGroup_of_commute (h32 : Lemma32FullFor 𝒜) (hG : 𝒜 G) (hN : IsSolomonChoice N)
    (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N) (hne : K ≠ K')
    {V F : Subgroup G} (hV : IsKleinFour V) (hVK' : V ≤ K') (hF : IsKleinFour F) (hFK : F ≤ K)
    (hFV : F ≤ centralizer (V : Set G)) {e : G} (heK : e ∈ K) (he2 : orderOf e = 2)
    (heV : V ≤ centralizer ({e} : Set G)) (heF : F ≤ centralizer ({e} : Set G)) :
    theta V e ≤ wGroup F V := by
  have hθle : theta V e ≤ oddCoreIn (centralizer ({e} : Set G)) := theta_le_oddCoreIn heV
  have hcop : Nat.Coprime 2 (Nat.card (theta V e)) := Nat.Coprime.coprime_dvd_right
    (Subgroup.card_dvd_of_le hθle) (coprime_card_oddCoreIn _)
  have hFθ : F ≤ normalizer (theta V e : Set G) :=
    le_normalizer_theta (heF.trans le_normalizer)
      (fun _ h => Subgroup.centralizer_le_normalizer (V : Set G) (hFV h))
      (fun _ h => le_normalizer (hFV h))
  refine (le_iSup_inf_centralizer_of_isKleinFour hF hFθ hcop).trans ?_
  refine iSup₂_le fun f hf => iSup_le fun hf1 => ?_
  have hf2 : orderOf f = 2 := orderOf_eq_two_of_isKleinFour hF hf hf1
  have hfV : V ≤ centralizer ({f} : Set G) := fun w hw =>
    mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp (hFV hf)) w hw)
  have hef : f * e = e * f := (mem_centralizer_singleton_iff.mp (heF hf))
  exact (theta_inf_le_theta h32 hG hN hK hK' hne hV hVK' (hFK hf) hf2 heK he2 hef hfV heV).trans
    (theta_le_wGroup hf hf1)

theorem wGroup_le_wGroup (h32 : Lemma32FullFor 𝒜) (hG : 𝒜 G) (hN : IsSolomonChoice N)
    (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N) (hne : K ≠ K')
    {V E F : Subgroup G} (hV : IsKleinFour V) (hVK' : V ≤ K') (hE : IsKleinFour E) (hEK : E ≤ K)
    (hEV : E ≤ centralizer (V : Set G)) (hF : IsKleinFour F) (hFK : F ≤ K)
    (hFV : F ≤ centralizer (V : Set G)) (hEF : E ≤ centralizer (F : Set G)) :
    wGroup E V ≤ wGroup F V := by
  refine iSup₂_le fun e he => iSup_le fun he1 => ?_
  have he2 : orderOf e = 2 := orderOf_eq_two_of_isKleinFour hE he he1
  have heV : V ≤ centralizer ({e} : Set G) := fun w hw =>
    mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp (hEV he)) w hw)
  have heF : F ≤ centralizer ({e} : Set G) := fun f hf =>
    mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp (hEF he)) f hf)
  exact theta_le_wGroup_of_commute h32 hG hN hK hK' hne hV hVK' hF hFK hFV (hEK he) he2 heV heF

theorem wGroup_eq_wGroup_zpowers (h32 : Lemma32FullFor 𝒜) (hG : 𝒜 G) (hN : IsSolomonChoice N)
    (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N) (hne : K ≠ K')
    {V E : Subgroup G} (hV : IsKleinFour V) (hVK' : V ≤ K') (hE : IsKleinFour E) (hEK : E ≤ K)
    (hEV : E ≤ centralizer (V : Set G)) {v : G} (hv : v ∈ V) (hv1 : v ≠ 1) :
    wGroup E V = wGroup E (zpowers v) := by
  refine le_antisymm (iSup₂_le fun e he => iSup_le fun he1 => ?_)
    (iSup₂_le fun e he => iSup_le fun he1 => ?_)
  · have he2 : orderOf e = 2 := orderOf_eq_two_of_isKleinFour hE he he1
    have heV : V ≤ centralizer ({e} : Set G) := fun w hw =>
      mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp (hEV he)) w hw)
    exact (theta_le_theta_zpowers h32 hG hN hK hK' hne hV hVK' (hEK he) he2 heV
      hv hv1).trans (theta_le_wGroup he he1)
  · have heV : V ≤ centralizer ({e} : Set G) := fun w hw =>
      mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp (hEV he)) w hw)
    exact (theta_mono (zpowers_le.mpr hv) (isPGroup_of_isKleinFour hV)
      (comm_of_isKleinFour hV) heV).trans (theta_le_wGroup he he1)

end CFSG.ComponentClassification.Sol76.Sig
