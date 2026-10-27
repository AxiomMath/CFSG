module

public import CFSG.ClassicalInvolution.Q3.Q3TMFSParts
public import CFSG.ClassicalInvolution.Q3.TL3DichMain

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

variable {Y : Type} [Group Y]

@[expose] def subgroupOfToSub (R H : Subgroup Y) : ↥(R.subgroupOf H) →* ↥R :=
  ((H.subtype).comp (R.subgroupOf H).subtype).codRestrict R fun x => x.2

theorem coe_subgroupOfToSub (R H : Subgroup Y) (x : ↥(R.subgroupOf H)) :
    ((subgroupOfToSub R H x : R) : Y) = ((x : H) : Y) := rfl

theorem subgroupOfToSub_injective (R H : Subgroup Y) :
    Function.Injective (subgroupOfToSub R H) := by
  intro a b h
  apply Subtype.ext
  apply Subtype.ext
  have := congrArg (fun z : ↥R => (z : Y)) h
  simpa [coe_subgroupOfToSub] using this

variable [Finite Y]

theorem isPGroup_two_quotient_subgroupOf (R H : Subgroup Y)
    (h : IsPGroup 2 (R ⧸ classicalInvolutionOddCore R)) :
    IsPGroup 2 (↥(R.subgroupOf H) ⧸ classicalInvolutionOddCore ↥(R.subgroupOf H)) := by
  set ι := subgroupOfToSub R H with hι
  have hinj : Function.Injective ι := subgroupOfToSub_injective R H
  set K1 : Subgroup ↥(R.subgroupOf H) := (classicalInvolutionOddCore ↥R).comap ι with hK1
  have hK1n : K1.Normal := (classicalInvolutionOddCore_normal _).comap ι
  have hK1odd : Odd (Nat.card K1) := by
    have hdvd : Nat.card K1 ∣ Nat.card (classicalInvolutionOddCore ↥R) :=
      Subgroup.card_dvd_of_injective (ι.subgroupComap (classicalInvolutionOddCore ↥R))
        (fun a b hab => Subtype.ext (hinj (congrArg Subtype.val hab)))
    exact Odd.of_dvd_nat (QuaternionStructure.odd_natCard_oddCore R) hdvd
  have hK1le : K1 ≤ classicalInvolutionOddCore ↥(R.subgroupOf H) :=
    le_sSup ⟨hK1n, hK1odd⟩
  intro x
  obtain ⟨x0, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨m, hm⟩ := h (QuotientGroup.mk (ι x0))
  refine ⟨m, ?_⟩
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
  apply hK1le
  show ι (x0 ^ 2 ^ m) ∈ classicalInvolutionOddCore ↥R
  rw [map_pow]
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hm
  exact hm

omit [Finite Y] in
theorem tightCore_subgroupOf {R H : Subgroup Y} (hKH : tightCore R ≤ H) :
    tightCore (R.subgroupOf H) = (tightCore R).subgroupOf H := by
  apply Subgroup.map_injective (Subgroup.subtype_injective H)
  rw [Subgroup.map_subgroupOf_eq_of_le hKH]
  unfold tightCore
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨x, ⟨hxR, hx2⟩, rfl⟩
    refine ⟨hxR, ?_⟩
    have h2 : IsPGroup 2 ↥(Subgroup.map H.subtype (Subgroup.zpowers x)) := hx2.map _
    rw [MonoidHom.map_zpowers] at h2
    exact h2
  · rintro ⟨hyR, hy2⟩
    have hyK : y ∈ tightCore R := Subgroup.subset_closure ⟨hyR, hy2⟩
    refine ⟨⟨y, hKH hyK⟩, ⟨hyR, ?_⟩, rfl⟩
    have h2 : IsPGroup 2 ↥(Subgroup.map H.subtype (Subgroup.zpowers (⟨y, hKH hyK⟩ : H))) := by
      rw [MonoidHom.map_zpowers]
      exact hy2
    let e := Subgroup.equivMapOfInjective (Subgroup.zpowers (⟨y, hKH hyK⟩ : H)) H.subtype
      H.subtype_injective
    exact h2.of_injective e.toMonoidHom e.injective

theorem TightDatum.restrict {R : Subgroup Y} {S : Sylow 2 R} {t : Y} (hd : TightDatum R S t)
    {H : Subgroup Y} (hSH : (S : Subgroup R).map R.subtype ≤ H) :
    ∃ S' : Sylow 2 (R.subgroupOf H),
      TightDatum (R.subgroupOf H) S' (⟨t, hSH hd.mem⟩ : H) ∧
        Nonempty ((S' : Subgroup (R.subgroupOf H)) ≃* (S : Subgroup R)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set SY : Subgroup Y := (S : Subgroup R).map R.subtype with hSY
  have hSR : SY ≤ R := Subgroup.map_subtype_le _
  have hle : SY.subgroupOf H ≤ R.subgroupOf H := Subgroup.subgroupOf_mono H hSR
  set P0 : Subgroup ↥(R.subgroupOf H) := (SY.subgroupOf H).subgroupOf (R.subgroupOf H) with hP0
  let e1 : ↥P0 ≃* ↥(SY.subgroupOf H) := Subgroup.subgroupOfEquivOfLe hle
  let e2 : ↥(SY.subgroupOf H) ≃* ↥SY := Subgroup.subgroupOfEquivOfLe hSH
  let e3 : ↥SY ≃* ↥(S : Subgroup R) :=
    (Subgroup.equivMapOfInjective (S : Subgroup R) R.subtype R.subtype_injective).symm
  let e : ↥P0 ≃* ↥(S : Subgroup R) := e1.trans (e2.trans e3)
  have hb : 2 ^ (Nat.card ↥R).factorization 2 = Nat.card P0 := by
    rw [Nat.card_congr e.toEquiv, Sylow.card_eq_multiplicity S]
  have hdvdR : Nat.card ↥(R.subgroupOf H) ∣ Nat.card ↥R :=
    Subgroup.card_dvd_of_injective (subgroupOfToSub R H) (subgroupOfToSub_injective R H)
  have hP0dvd : Nat.card P0 ∣ Nat.card ↥(R.subgroupOf H) := Subgroup.card_subgroup_dvd_card P0
  have hle1 : (Nat.card ↥(R.subgroupOf H)).factorization 2 ≤ (Nat.card ↥R).factorization 2 :=
    (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr hdvdR 2
  have hle2 : (Nat.card ↥R).factorization 2 ≤ (Nat.card ↥(R.subgroupOf H)).factorization 2 := by
    rw [← Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne', hb]
    exact hP0dvd
  have hcard : Nat.card P0 = 2 ^ (Nat.card ↥(R.subgroupOf H)).factorization 2 := by
    rw [le_antisymm hle1 hle2, hb]
  have hS'coe : ((Sylow.ofCard P0 hcard : Sylow 2 ↥(R.subgroupOf H)) :
      Subgroup ↥(R.subgroupOf H)) = P0 := rfl
  have htR : (⟨t, hSH hd.mem⟩ : H) ∈ R.subgroupOf H := Subgroup.mem_subgroupOf.mpr hd.mem_right
  have hcent : R.subgroupOf H ≤ Subgroup.centralizer ({(⟨t, hSH hd.mem⟩ : H)} : Set H) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hd.cent hx))
  refine ⟨Sylow.ofCard P0 hcard, ?_, ⟨e⟩⟩
  obtain ⟨r, hr, ⟨f⟩⟩ := hd.quat
  refine ⟨⟨r, hr, ⟨e.trans f⟩⟩, ?_, ?_, hcent, ?_, ?_⟩
  · rw [hS'coe]
    exact ⟨⟨⟨t, hSH hd.mem⟩, htR⟩,
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr hd.mem), rfl⟩
  · rw [Subgroup.orderOf_mk]
    exact hd.order
  · refine (Subgroup.normal_subgroupOf_iff_le_normalizer hcent).mpr ?_
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hcN : (c : Y) ∈ Subgroup.normalizer (R : Set Y) := by
      apply hd.le_normalizer
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hc)
    have := (Subgroup.mem_normalizer_iff.mp hcN) (x : Y)
    exact this
  · exact isPGroup_two_quotient_subgroupOf R H hd.twoGroup

omit [Finite Y] in
theorem iSup_conjSub_eq_top_of_subnormalClosure {X : Type} [Group X] [Finite X] {K : Subgroup X}
    (h : subnormalClosure K = ⊤) : (⨆ g : X, conjSub g K) = ⊤ := by
  set N : Subgroup X := ⨆ g : X, conjSub g K with hN
  have hKN : K ≤ N := by
    have := le_iSup (fun g : X => conjSub g K) 1
    simpa [conjSub_one] using this
  have hnormal : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    refine Subgroup.iSup_induction (fun g : X => conjSub g K)
      (C := fun x => g * x * g⁻¹ ∈ N) hn (fun h x hx => ?_) (by simp) (fun x y hx hy => ?_)
    · refine (le_iSup (fun g : X => conjSub g K) (g * h)) ?_
      rw [mem_conjSub_iff] at hx ⊢
      simpa [mul_assoc] using hx
    · have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
      show g * (x * y) * g⁻¹ ∈ N
      rw [this]
      exact N.mul_mem hx hy
  have hsub : IsSubnormal N ⊤ := isSubnormal_of_normal_subgroupOf le_top (hnormal.subgroupOf ⊤)
  have := subnormalClosure_le hKN hsub
  rw [h] at this
  exact eq_top_iff.mpr this

omit [Finite Y] in
theorem twoSubgroupsFourGenerated_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : TwoSubgroupsFourGenerated A) : TwoSubgroupsFourGenerated B := by
  classical
  intro P hP
  obtain ⟨s, hs, hcl⟩ := h (P.map e.symm.toMonoidHom) (hP.map _)
  refine ⟨s.image e, ?_, ?_⟩
  · exact (Finset.card_image_le).trans hs
  · rw [Finset.coe_image]
    show Subgroup.closure ((e.toMonoidHom : A → B) '' (s : Set A)) = P
    rw [← MonoidHom.map_closure, hcl, Subgroup.map_map]
    ext x
    simp

omit [Finite Y] in
theorem not_inO2_of_fstar_le {G : Type} [Group G] [Finite G]
    [IsSimpleGroup (genFittingFStar G)] (hnab : ∃ a b : genFittingFStar G, a * b ≠ b * a)
    {H : Subgroup G} (hFH : genFittingFStar G ≤ H) {t : H} (ht : orderOf t = 2) :
    ¬ TightInO2 t := by
  rintro ⟨P, hPn, hP2, htP⟩
  obtain ⟨hC, -⟩ := centralizer_fstar_eq_bot_and_oddCore_eq_bot hnab
  have hFn : (genFittingFStar G).Normal := genFittingFStar_normal G
  set F := genFittingFStar G with hF
  set PG : Subgroup G := P.map H.subtype with hPG
  have hconj : ∀ (f : G) (hf : f ∈ H) (p : G), p ∈ PG → f * p * f⁻¹ ∈ PG := by
    rintro f hf _ ⟨p, hp, rfl⟩
    refine ⟨(⟨f, hf⟩ : H) * p * (⟨f, hf⟩ : H)⁻¹, hPn.conj_mem p hp ⟨f, hf⟩, ?_⟩
    simp
  have hAn : ((PG ⊓ F).subgroupOf F).Normal := by
    rw [Subgroup.normal_subgroupOf_iff inf_le_right]
    rintro a f ⟨haP, haF⟩ hfF
    exact ⟨hconj f (hFH hfF) a haP, by simpa using hFn.conj_mem a haF f⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((PG ⊓ F).subgroupOf F) with hA | hA
  ·
    have hinf : ∀ x ∈ PG ⊓ F, x = 1 := by
      intro x hx
      have : (⟨x, hx.2⟩ : F) ∈ (PG ⊓ F).subgroupOf F := hx
      rw [hA, Subgroup.mem_bot] at this
      exact congrArg Subtype.val this
    have hcent : ∀ p ∈ PG, p ∈ Subgroup.centralizer (F : Set G) := by
      intro p hp
      rw [Subgroup.mem_centralizer_iff]
      intro f hf
      have h1 : p * f * p⁻¹ * f⁻¹ = 1 := by
        apply hinf
        refine ⟨?_, ?_⟩
        · have := PG.mul_mem hp (hconj f (hFH hf) p⁻¹ (PG.inv_mem hp))
          simpa [mul_assoc] using this
        · exact F.mul_mem (hFn.conj_mem f hf p) (F.inv_mem hf)
      calc f * p = (p * f * p⁻¹ * f⁻¹)⁻¹ * (p * f) := by group
        _ = p * f := by rw [h1]; simp
    have htG : (t : G) ∈ PG := ⟨t, htP, rfl⟩
    have := hcent _ htG
    rw [hC, Subgroup.mem_bot] at this
    have h1 : t = 1 := Subtype.ext this
    rw [h1, orderOf_one] at ht
    exact absurd ht (by norm_num)
  ·
    have hFP : ∀ x ∈ F, x ∈ PG := by
      intro x hx
      have : (⟨x, hx⟩ : F) ∈ (PG ⊓ F).subgroupOf F := by rw [hA]; exact Subgroup.mem_top _
      exact this.1
    have hF2 : IsPGroup 2 ↥F := by
      intro x
      obtain ⟨p, hp, hpx⟩ := hFP x.1 x.2
      obtain ⟨k, hk⟩ := hP2 ⟨p, hp⟩
      refine ⟨k, Subtype.ext ?_⟩
      have h1 := congrArg (fun z : ↥P => ((z : H) : G)) hk
      simp only [Subgroup.coe_pow, OneMemClass.coe_one] at h1
      show (x : G) ^ 2 ^ k = 1
      rw [← hpx]
      exact h1
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨a, b, hab⟩ := hnab
    have : Nontrivial ↥F := ⟨⟨a, 1, fun h => hab (by rw [h]; simp)⟩⟩
    have hnt := hF2.center_nontrivial
    rw [CFSG.ComponentClassification.Helpers.center_eq_bot F ⟨a, b, hab⟩] at hnt
    exact (Subgroup.nontrivial_iff_ne_bot ⊥).mp hnt rfl

omit [Finite Y] in
theorem nonempty_equiv_genFittingFStar_subgroup {G : Type} [Group G] [Finite G]
    [IsSimpleGroup (genFittingFStar G)] (hnab : ∃ a b : genFittingFStar G, a * b ≠ b * a)
    {H : Subgroup G} (hFH : genFittingFStar G ≤ H) :
    Nonempty (↥(genFittingFStar ↥H) ≃* ↥(genFittingFStar G)) := by
  obtain ⟨hC, -⟩ := centralizer_fstar_eq_bot_and_oddCore_eq_bot hnab
  have hFn : (genFittingFStar G).Normal := genFittingFStar_normal G
  set F := genFittingFStar G with hF
  let e : ↥(F.subgroupOf H) ≃* ↥F := Subgroup.subgroupOfEquivOfLe hFH
  have : (F.subgroupOf H).Normal := hFn.subgroupOf H
  have : IsSimpleGroup ↥(F.subgroupOf H) := e.isSimpleGroup
  have hnab' : ∃ a b : ↥(F.subgroupOf H), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩
  have hC' : Subgroup.centralizer ((F.subgroupOf H : Subgroup H) : Set H) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_centralizer_iff] at hx
    have : (x : G) ∈ Subgroup.centralizer (F : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro f hf
      exact congrArg Subtype.val (hx ⟨f, hFH hf⟩ hf)
    rw [hC, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (Subtype.ext this)
  have hFH' : genFittingFStar ↥H = F.subgroupOf H :=
    genFittingFStar_eq_of_normal_simple (F.subgroupOf H) hnab' hC'
  exact ⟨(MulEquiv.subgroupCongr hFH').trans e⟩

omit [Finite Y] in
theorem not_twoSubgroupsFourGenerated_subgroup {G : Type} [Group G] [Finite G]
    [IsSimpleGroup (genFittingFStar G)] (hnab : ∃ a b : genFittingFStar G, a * b ≠ b * a)
    (hlarge : ¬ TwoSubgroupsFourGenerated (genFittingFStar G)) {H : Subgroup G}
    (hFH : genFittingFStar G ≤ H) : ¬ TwoSubgroupsFourGenerated (genFittingFStar ↥H) := by
  obtain ⟨e⟩ := nonempty_equiv_genFittingFStar_subgroup hnab hFH
  intro hTF
  exact hlarge (twoSubgroupsFourGenerated_of_mulEquiv e hTF)

omit [Finite Y] in
theorem isQuasisimple_genFittingFStar_subgroup {G : Type} [Group G] [Finite G]
    [IsSimpleGroup (genFittingFStar G)] (hnab : ∃ a b : genFittingFStar G, a * b ≠ b * a)
    {H : Subgroup G} (hFH : genFittingFStar G ≤ H) : TightFStarQuasisimple ↥H := by
  obtain ⟨e⟩ := nonempty_equiv_genFittingFStar_subgroup hnab hFH
  have : (genFittingFStar G).Normal := genFittingFStar_normal G
  exact CFSG.ComponentClassification.Components.quasisimple_of_equiv e
    (isComponentOf_top_of_normal_simple (genFittingFStar G) hnab).2.2

omit [Finite Y] in
theorem isClassicalMember3_map_subnormal {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (hH : IsSubnormal H ⊤) {L : Subgroup H} {z : H} (hL : IsClassicalMember3 L z) :
    IsClassicalMember3 (L.map H.subtype) (z : G) where
  orderOf_eq_two := by rw [Subgroup.orderOf_coe]; exact hL.orderOf_eq_two
  mem := Subgroup.mem_map_of_mem _ hL.mem
  subnormal := by
    have h1 : IsSubnormal (L.map H.subtype)
        ((Subgroup.centralizer ({z} : Set H)).map H.subtype) :=
      CFSG.ComponentClassification.Components.chain_map H.subtype hL.subnormal
    have h2 : (Subgroup.centralizer ({z} : Set H)).map H.subtype =
        Subgroup.centralizer ({(z : G)} : Set G) ⊓ H := by
      have := subgroupOf_centralizer_inf (z := (z : G)) z.2
      rw [Subtype.coe_eta] at this
      rw [← this, Subgroup.map_subgroupOf_eq_of_le inf_le_right]
    have h3 : IsSubnormal (Subgroup.centralizer ({(z : G)} : Set G) ⊓ H)
        (Subgroup.centralizer ({(z : G)} : Set G)) := by
      have := isSubnormal_inf hH (Subgroup.centralizer ({(z : G)} : Set G))
      rwa [inf_comm, top_inf_eq] at this
    rw [h2] at h1
    exact isSubnormal_trans h1 h3
  nonempty_equiv := by
    obtain ⟨e'⟩ := hL.nonempty_equiv
    let e : L ≃* L.map H.subtype := L.equivMapOfInjective H.subtype H.subtype_injective
    have hO : (classicalInvolutionOddCore L).map e.toMonoidHom =
        classicalInvolutionOddCore (L.map H.subtype) :=
      CFSG.ComponentClassification.OddCore.equiv_invariant e
    exact ⟨(QuotientGroup.congr _ _ e hO).symm.trans e'⟩

omit [Finite Y] in
theorem tightTopRestrict :
    ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup (genFittingFStar G)],
      (∃ a b : genFittingFStar G, a * b ≠ b * a) →
      ¬ TwoSubgroupsFourGenerated (genFittingFStar G) →
      ∀ (R : Subgroup G) (S : Sylow 2 R) (t : G), TightDatum R S t →
        Nonempty ((S : Subgroup R) ≃* QuaternionGroup 2) →
        ∃ (H : Subgroup G) (R' : Subgroup H) (S' : Sylow 2 R') (t' : H),
          TightDatum R' S' t' ∧ TightCls H R' S' t' ∧ ¬ TightInO2 t' ∧
          TightFStarQuasisimple H ∧ Subgroup.center ↥H = ⊥ ∧
          ¬ TwoSubgroupsFourGenerated (genFittingFStar H) ∧
          ((∃ L : Subgroup H, IsClassicalMember3 L t') →
            ∃ (z : G) (J : Subgroup G), IsClassicalMember3 J z) := by
  intro G _ _ _ hnab hlarge R S t hd hq8
  obtain ⟨hC, hO⟩ := centralizer_fstar_eq_bot_and_oddCore_eq_bot hnab
  have : (genFittingFStar G).Normal := genFittingFStar_normal G
  have ht2 : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hd.order]; norm_num)
  have htK : t ∈ tightCore R := Subgroup.subset_closure ⟨hd.mem_right, ht2⟩
  have hK0ne : tightCore R ≠ ⊥ := by
    intro h
    rw [h, Subgroup.mem_bot] at htK
    have := hd.order
    rw [htK, orderOf_one] at this
    norm_num at this
  have hSK : (S : Subgroup R).map R.subtype ≤ tightCore R := by
    rintro _ ⟨s, hs, rfl⟩
    refine Subgroup.subset_closure ⟨s.2, ?_⟩
    have h1 : IsPGroup 2 ↥(Subgroup.zpowers s) := S.isPGroup'.to_le (Subgroup.zpowers_le.mpr hs)
    have h2 : IsPGroup 2 ↥((Subgroup.zpowers s).map R.subtype) := h1.map _
    rw [MonoidHom.map_zpowers] at h2
    exact h2
  set H := subnormalClosure (tightCore R) with hH
  have hHsub : IsSubnormal H ⊤ := isSubnormal_subnormalClosure _
  have hKH : tightCore R ≤ H := le_subnormalClosure _
  have hFH : genFittingFStar G ≤ H :=
    le_subnormalClosure_of_isComponentOf (isComponentOf_top_of_normal_simple _ hnab) hC hK0ne
  have hSH : (S : Subgroup R).map R.subtype ≤ H := hSK.trans hKH
  obtain ⟨S', hd', ⟨eS⟩⟩ := hd.restrict hSH
  have hord : orderOf (⟨t, hSH hd.mem⟩ : H) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact hd.order
  refine ⟨H, R.subgroupOf H, S', ⟨t, hSH hd.mem⟩, hd', ⟨⟨eS.trans hq8.some⟩, ?_, ?_⟩, ?_, ?_, ?_,
    ?_, ?_⟩
  · unfold TightSelfGen
    rw [tightCore_subgroupOf hKH]
    exact iSup_conjSub_eq_top_of_subnormalClosure (subnormalClosure_subgroupOf_subnormalClosure _)
  · exact CFSG.ComponentClassification.OddCore.subnormal_corefree hO H hHsub
  · exact not_inO2_of_fstar_le hnab hFH hord
  · exact isQuasisimple_genFittingFStar_subgroup hnab hFH
  ·
    rw [eq_bot_iff]
    intro x hx
    have hxC : (x : G) ∈ Subgroup.centralizer (genFittingFStar G : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro f hf
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hx ⟨f, hFH hf⟩)
    rw [hC, Subgroup.mem_bot] at hxC
    exact (Subgroup.mem_bot).mpr (Subtype.ext hxC)
  · exact not_twoSubgroupsFourGenerated_subgroup hnab hlarge hFH
  · rintro ⟨L, hL⟩
    exact ⟨_, _, isClassicalMember3_map_subnormal hHsub hL⟩

theorem tightHasMember3LargeBelow_of_inductive (hI : ∀ N, TightInductive N)
    (hE : ∀ n, TightLargeEdge n) (hR4 : TightR4) : Q3T.MFS.TightHasMember3LargeBelow := by
  intro n hn G _ _ _ hlt hnab hlarge R S hS t ht hto hRC hRn h2
  have hd : TightDatum R S t := ⟨hS, ht, hto, hRC, hRn, h2⟩
  obtain ⟨H, R', S', t', hd', hcls, hE2, hQS, hZH, hlargeH, hmem⟩ :=
    tightTopRestrict G hnab hlarge R S t hd (hR4 n hn G hlt hnab hlarge R S t hd)
  have hHn : Nat.card H < n :=
    lt_of_le_of_lt (Nat.card_le_card_of_injective _ H.subtype_injective) hlt
  have hbelow : TightBelow (Nat.card H) := fun Y _ _ hlt' R S t hd hc =>
    hI n hn Y (lt_trans hlt' hHn) R S t hd hc
  have hedge := hE (Nat.card H) (CIT3Below.mono hHn.le hn) hbelow H rfl R' S' t' hd' hcls hE2 hQS
    hlargeH
  rcases hI n hn H hHn R' S' t' hd' hcls with
    (hex | ⟨hedgeless, -⟩ | ⟨hedgeless, -⟩ | h4) | hgood
  · exact absurd hex hE2
  · exact absurd hedgeless hedge
  · exact absurd hedgeless hedge
  · exact absurd h4 (hd'.not_tightE4 hcls hE2 hZH)
  · obtain ⟨L, -, hL⟩ := tightHasLift_of_good hd' hgood
    exact hmem ⟨L, hL⟩

end CFSG.ClassicalInvolution.Q3
