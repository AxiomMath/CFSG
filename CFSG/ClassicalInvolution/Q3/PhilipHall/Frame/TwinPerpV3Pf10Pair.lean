module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6Main
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf2Dich
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6Sec
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinSecNoExit

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6
open scoped commutatorElement

section Pair



section Pullback

variable {H : Type} [Group H] [Finite H] {N : Subgroup H} [N.Normal]

theorem exists_classicalMember_of_oddQuot3 (hNodd : Odd (Nat.card ↥N)) {t : H}
    (ht2 : t * t = 1) {L : Subgroup (H ⧸ N)}
    (hL : IsClassicalMember3 L (QuotientGroup.mk' N t)) :
    ∃ K : Subgroup H, IsClassicalMember3 K t ∧ (∀ k ∈ K, QuotientGroup.mk' N k ∈ L) ∧
      (∀ l ∈ L, ∃ k ∈ K, QuotientGroup.mk' N k = l) ∧
      (∀ h : H, QuotientGroup.mk' N h ∈ L → h * t = t * h → h ∈ K) := by
  classical
  set π : H →* H ⧸ N := QuotientGroup.mk' N with hπ
  set C : Subgroup H := Subgroup.centralizer ({t} : Set H) with hC
  set P : Subgroup H := L.comap π with hP
  set K : Subgroup H := P ⊓ C with hK
  have htP : t ∈ P := Subgroup.mem_comap.mpr hL.mem
  have htC : t ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have htK : t ∈ K := ⟨htP, htC⟩
  have hLC : L ≤ Subgroup.centralizer ({π t} : Set (H ⧸ N)) := isSubnormal_le' hL.subnormal
  have hCbar : Subgroup.centralizer ({π t} : Set (H ⧸ N)) = C.map π :=
    OddQ.centralizer_mk_eq hNodd ht2
  have hKL : ∀ k : K, π (k : H) ∈ L := fun k => Subgroup.mem_comap.mp k.2.1
  set f : ↥K →* ↥L := (π.comp K.subtype).codRestrict L hKL with hf
  have hfs : Function.Surjective f := by
    intro x
    have hx := hLC x.2
    rw [hCbar] at hx
    obtain ⟨c, hcC, hcx⟩ := hx
    have hcP : c ∈ P := Subgroup.mem_comap.mpr (by rw [hcx]; exact x.2)
    exact ⟨⟨c, hcP, hcC⟩, Subtype.ext hcx⟩
  have hfk : Odd (Nat.card f.ker) := by
    have hker : f.ker = N.subgroupOf K := by
      ext k
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      constructor
      · intro h1
        exact (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val h1)
      · intro h1
        exact Subtype.ext ((QuotientGroup.eq_one_iff _).mpr h1)
    rw [hker]
    have h1 : Nat.card (N.subgroupOf K) = Nat.card (N ⊓ K : Subgroup H) := by
      rw [← Subgroup.subgroupOf_map_subtype, Subgroup.card_map_of_injective K.subtype_injective]
    rw [h1]
    exact hNodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have ht2' : orderOf t = 2 := by
    refine orderOf_eq_prime (by rw [pow_two]; exact ht2) ?_
    intro h1
    have := hL.orderOf_eq_two
    rw [hπ, QuotientGroup.mk'_apply, h1, QuotientGroup.mk_one, orderOf_one] at this
    omega
  refine ⟨K, ⟨ht2', htK, ?_, ?_⟩, fun k hk => Subgroup.mem_comap.mp hk.1, ?_, ?_⟩
  · have h1 := isSubnormal_comap' π hL.subnormal
    rw [hCbar] at h1
    have h2 := isSubnormal_inf h1 C
    have h3 : (C.map π).comap π ⊓ C = C := by
      rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
      exact inf_eq_right.mpr le_sup_left
    rw [h3] at h2
    exact h2
  · obtain ⟨e⟩ := hL.nonempty_equiv
    exact ⟨(CFSG.ComponentClassification.OddKernel.coreQuotientEquiv f hfs hfk).trans e⟩
  · intro l hl
    obtain ⟨k, hk⟩ := hfs ⟨l, hl⟩
    exact ⟨k, k.2, congrArg Subtype.val hk⟩
  · intro h h1 h2
    exact ⟨Subgroup.mem_comap.mpr h1, Subgroup.mem_centralizer_singleton_iff.mpr h2⟩

end Pullback

section Section

theorem exists_sectionMember_of_lift3 {Y : Type} [Group Y] [Finite Y] {C : Subgroup Y} {H : Subgroup ↥C}
    (hH : IsSubnormal H ⊤) {t : ↥C}
    (ht : t ∈ H) (ht2 : t * t = 1) {L : Subgroup (↥H ⧸ classicalInvolutionOddCore ↥H)}
    (hL : IsClassicalMember3 L (QuotientGroup.mk' (classicalInvolutionOddCore ↥H) ⟨t, ht⟩)) :
    ∃ K : Subgroup Y, Q3NL.IsSectionMember3 C K (t : Y) ∧
      (∀ k ∈ K, ∃ h : ↥H, (((h : ↥C)) : Y) = k ∧
        QuotientGroup.mk' (classicalInvolutionOddCore ↥H) h ∈ L) ∧
      (∀ l ∈ L, ∃ h : ↥H, (((h : ↥C)) : Y) ∈ K ∧
        QuotientGroup.mk' (classicalInvolutionOddCore ↥H) h = l) ∧
      (∀ h : ↥H, QuotientGroup.mk' (classicalInvolutionOddCore ↥H) h ∈ L →
        (h : ↥C) * t = t * (h : ↥C) → (((h : ↥C)) : Y) ∈ K) := by
  obtain ⟨K, hK, hKL, hLK, hpull⟩ := exists_classicalMember_of_oddQuot3
    (CFSG.ComponentClassification.OddCore.odd_card ↥H) (t := (⟨t, ht⟩ : H))
    (Subtype.ext ht2) hL
  have hKC := isClassicalMember3_map_subnormal hH hK
  refine ⟨_, TL4.isSectionMember3_map hKC, ?_, ?_, ?_⟩
  · rintro k ⟨_, ⟨h, hh, rfl⟩, rfl⟩
    exact ⟨h, rfl, hKL h hh⟩
  · intro l hl
    obtain ⟨k, hk, hkl⟩ := hLK l hl
    exact ⟨k, ⟨_, ⟨k, hk, rfl⟩, rfl⟩, hkl⟩
  · intro h h1 h2
    exact ⟨_, ⟨h, hpull h h1 (Subtype.ext h2), rfl⟩, rfl⟩

end Section

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem liftPair_of_twins (hΩ : HypOmegaGen Ω) (hc2' : IsPGroup 2 (Subgroup.zpowers c))
    (hS : Q8Section (↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c)) (secFam Ω c))
    {J J' : Subgroup G} (hJtq : J ∈ tqMembers3 Ω c) (hJ'tq : J' ∈ tqMembers3 Ω c)
    (hJne : J' ≠ J) {t : G} (htJ : IsUniqueInvolution J t) (htJ' : IsUniqueInvolution J' t)
    (htC : t ∈ Subgroup.centralizer ({c} : Set G))
    (hlf : SecMemberLifted Ω c J ∧ SecMemberLifted Ω c J')
    {x : G} (hxc : x ∈ Subgroup.centralizer ({c} : Set G))
    (hxJ : x ∈ centralizerModOdd ⊤ J) (hxJ' : x ∈ centralizerModOdd ⊤ J') :
    ∃ M M' : Subgroup G,
      Q3NL.IsSectionMember3 (Subgroup.centralizer ({c} : Set G)) M t ∧
      Q3NL.IsSectionMember3 (Subgroup.centralizer ({c} : Set G)) M' t ∧
      modOdd c M ≠ modOdd c M' ∧
      (∀ a ∈ modOdd c M, ∀ b ∈ modOdd c M', a * b = b * a) ∧
      (∀ a ∈ modOdd c M, oddQuotMk c ⟨x, hxc⟩ * a = a * oddQuotMk c ⟨x, hxc⟩) ∧
      (∀ a ∈ modOdd c M', oddQuotMk c ⟨x, hxc⟩ * a = a * oddQuotMk c ⟨x, hxc⟩) ∧
      (∀ g ∈ TwinADescent.coreAt c J, g * t = t * g → g ∈ M) ∧
      (∀ g ∈ TwinADescent.coreAt c J', g * t = t * g → g ∈ M') := by
  classical
  have ht2 : t * t = 1 := htJ.sq
  have hsq' : (⟨t, htC⟩ : ↥(Subgroup.centralizer ({c} : Set G))) * ⟨t, htC⟩ = 1 :=
    Subtype.ext ht2
  obtain ⟨⟨hJ2, ⟨L0, u0, hL0⟩, hOJ⟩, ⟨hJ'2, ⟨L0', u0', hL0'⟩, hOJ'⟩⟩ := hlf
  have hq8 : ∀ J₀ ∈ TwinDisc.secFam Ω c,
      IsPGroup 2 J₀ → Nonempty (↥J₀ ≃* QuaternionGroup 2) := fun J₀ hJ₀ hJ₀2 => by
    have hKS : IsSylow2In J₀ J₀ :=
      ⟨le_rfl, hJ₀2, fun V' hV'K _ hKV' => le_antisymm hV'K hKV'⟩
    exact hS.q8 J₀ hJ₀ J₀ hKS
  have htcore : ∀ J₀ : Subgroup G, IsUniqueInvolution J₀ t → t ∈ TwinADescent.coreAt c J₀ := by
    intro J₀ hJ₀
    have hle : Subgroup.zpowers t ≤ J₀ ⊓ Subgroup.centralizer ({c} : Set G) :=
      Subgroup.zpowers_le.mpr ⟨hJ₀.mem, htC⟩
    exact le_tightCore_of_isPGroup hle
      (CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one ht2)
      (Subgroup.mem_zpowers t)
  have htH : (⟨t, htC⟩ : ↥(Subgroup.centralizer ({c} : Set G))) ∈
      coreHull Ω c :=
    le_coreHull hJtq (Subgroup.mem_subgroupOf.mpr (htcore J htJ))
  set tb : ↥(coreHull Ω c) ⧸
      classicalInvolutionOddCore ↥(coreHull Ω c) :=
    QuotientGroup.mk' _
      (⟨⟨t, htC⟩, htH⟩ : ↥(coreHull Ω c)) with htb
  have tbar : ∀ J₀ : Subgroup G, J₀ ∈ tqMembers3 Ω c →
      IsUniqueInvolution J₀ t →
      ∀ u' : ↥(coreHull Ω c) ⧸
        classicalInvolutionOddCore ↥(coreHull Ω c),
      IsUniqueInvolution (secImg Ω c J₀) u' →
      tb = u' := by
    intro J₀ hJ₀ hJ₀t u' hinv
    have hmem : tb ∈ secImg Ω c J₀ :=
      ⟨⟨⟨t, htC⟩, htH⟩, Subgroup.mem_subgroupOf.mpr
        (Subgroup.mem_subgroupOf.mpr (htcore J₀ hJ₀t)), rfl⟩
    have htb1 : tb ≠ 1 := by
      intro h1
      have h1' : (⟨⟨t, htC⟩, htH⟩ : ↥(coreHull Ω c)) ∈
          classicalInvolutionOddCore ↥(coreHull Ω c) :=
        (QuotientGroup.eq_one_iff _).mp h1
      have hord : orderOf (⟨⟨t, htC⟩, htH⟩ :
          ↥(coreHull Ω c)) = 2 := by
        refine orderOf_eq_prime (by rw [pow_two]; exact Subtype.ext hsq') ?_
        intro e
        exact hJ₀t.ne_one (congrArg (fun w : ↥(coreHull Ω c) =>
          (((w : ↥(Subgroup.centralizer ({c} : Set G)))) : G)) e)
      have hdvd := Subgroup.orderOf_dvd_natCard _ h1'
      rw [hord] at hdvd
      exact absurd ((CFSG.ComponentClassification.OddCore.odd_card _).of_dvd_nat hdvd)
        (by decide)
    have htb2 : tb * tb = 1 := by
      rw [htb, ← map_mul]
      have : (⟨⟨t, htC⟩, htH⟩ : ↥(coreHull Ω c)) *
          ⟨⟨t, htC⟩, htH⟩ = 1 := Subtype.ext hsq'
      rw [this, map_one]
    exact (hinv.unique tb hmem htb2).resolve_left htb1
  have hu0 : tb = u0 := tbar J hJtq htJ u0 hL0.inv
  have hu0' : tb = u0' := tbar J' hJ'tq htJ' u0' hL0'.inv
  have hinvJ : IsUniqueInvolution (secImg Ω c J) tb :=
    hu0 ▸ hL0.inv
  have hinvJ' : IsUniqueInvolution (secImg Ω c J') tb :=
    hu0' ▸ hL0'.inv
  have hne_img : secImg Ω c J ≠
      secImg Ω c J' := by
    intro heq
    have hΛ : HypOmegaGen (cFam Ω c) :=
      TwinADescent.hypOmegaGen_coreFamily hΩ hc2'
    have hcore_ne : (TwinADescent.coreAt c J).subgroupOf (Subgroup.centralizer ({c} : Set G)) ≠
        (TwinADescent.coreAt c J').subgroupOf (Subgroup.centralizer ({c} : Set G)) := by
      intro he
      have := congrArg (Subgroup.map (Subgroup.centralizer ({c} : Set G)).subtype) he
      rw [Subgroup.map_subgroupOf_eq_of_le (TwinADescent.coreAt_le_centralizer c J),
        Subgroup.map_subgroupOf_eq_of_le (TwinADescent.coreAt_le_centralizer c J')] at this
      exact hJne (eq_of_coreAt_eq hΩ hc2' hJtq hJ'tq this).symm
    exact TwinExitPf2.false_of_imgOf_eq hΛ
      ⟨TwinADescent.coreAt c J, TwinADescent.coreAt_mem_coreFamily hJtq,
        TwinADescent.coreAt_le_centralizer c J, rfl⟩
      ⟨TwinADescent.coreAt c J', TwinADescent.coreAt_mem_coreFamily hJ'tq,
        TwinADescent.coreAt_le_centralizer c J', rfl⟩
      hcore_ne
      (isUniqueInvolution_subgroupOf
        (isUniqueInvolution_coreAt_of_tq hΩ hc2' hJtq htJ)
        (TwinADescent.coreAt_le_centralizer c J))
      (isUniqueInvolution_subgroupOf
        (isUniqueInvolution_coreAt_of_tq hΩ hc2' hJ'tq htJ')
        (TwinADescent.coreAt_le_centralizer c J'))
      (le_coreHull hJtq) (le_coreHull hJ'tq) heq
  obtain ⟨L₁, L₂, hL₁, hL₂, hJL₁, hJL₂, hLne, hcomm, hfix₁, hfix₂⟩ :=
    exists_lifted_pair hS.hyp (secImg_mem_secFam hJtq) (secImg_mem_secFam hJ'tq) hJ2 hJ'2
      (hq8 _ (secImg_mem_secFam hJtq) hJ2) (hq8 _ (secImg_mem_secFam hJ'tq) hJ'2)
      hinvJ hinvJ' ⟨L0, hu0 ▸ hL0⟩ ⟨L0', hu0' ▸ hL0'⟩ (hOJ tb hinvJ) hne_img
      (secAut Ω c hΩ hc2' ⟨x, hxc⟩)
      (secAut_fix_secImg hΩ hc2' hJ2 hxc hxJ)
      (secAut_fix_secImg hΩ hc2' hJ'2 hxc hxJ')
  have hH : IsSubnormal (coreHull Ω c) ⊤ := by
    have := normal_coreHull hΩ hc2'
    exact isSubnormal_of_normal_subgroupOf le_top inferInstance
  obtain ⟨M₁, hM₁, hM₁a, hM₁b, hM₁c⟩ :=
    exists_sectionMember_of_lift3 hH (t := ⟨t, htC⟩) htH hsq' hL₁
  obtain ⟨M₂, hM₂, hM₂a, hM₂b, hM₂c⟩ :=
    exists_sectionMember_of_lift3 hH (t := ⟨t, htC⟩) htH hsq' hL₂
  have hmem₁ := fun a => mem_modOdd_iff_of_lift hΩ hc2' hM₁a hM₁b (a := a)
  have hmem₂ := fun a => mem_modOdd_iff_of_lift hΩ hc2' hM₂a hM₂b (a := a)
  refine ⟨M₁, M₂, hM₁, hM₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro heq
    have inc : ∀ l ∈ L₁, l ∈ L₂ := by
      intro l hl1
      have h1 : secMap _ c hΩ hc2' l ∈ modOdd c M₁ := (hmem₁ _).2 ⟨l, hl1, rfl⟩
      rw [heq] at h1
      obtain ⟨l₂, hl₂, he⟩ := (hmem₂ _).1 h1
      rw [← secMap_injective hΩ hc2' he]
      exact hl₂
    have inc' : ∀ l ∈ L₂, l ∈ L₁ := by
      intro l hl2
      have h1 : secMap _ c hΩ hc2' l ∈ modOdd c M₂ := (hmem₂ _).2 ⟨l, hl2, rfl⟩
      rw [← heq] at h1
      obtain ⟨l₁, hl₁, he⟩ := (hmem₁ _).1 h1
      rw [← secMap_injective hΩ hc2' he]
      exact hl₁
    exact hLne (le_antisymm inc inc')
  · intro a ha b hb
    obtain ⟨l₁, hl₁, rfl⟩ := (hmem₁ a).1 ha
    obtain ⟨l₂, hl₂, rfl⟩ := (hmem₂ b).1 hb
    rw [← map_mul, ← map_mul, hcomm l₁ hl₁ l₂ hl₂]
  · intro a ha
    obtain ⟨l₁, hl₁, rfl⟩ := (hmem₁ a).1 ha
    exact oddQuot_centralizes_of_fix hΩ hc2' ⟨x, hxc⟩ hfix₁ hl₁
  · intro a ha
    obtain ⟨l₂, hl₂, rfl⟩ := (hmem₂ a).1 ha
    exact oddQuot_centralizes_of_fix hΩ hc2' ⟨x, hxc⟩ hfix₂ hl₂
  · intro g hg hgt
    have hgC := TwinADescent.coreAt_le_centralizer c J hg
    have hgH : (⟨g, hgC⟩ : ↥(Subgroup.centralizer ({c} : Set G))) ∈ coreHull Ω c :=
      le_coreHull hJtq (Subgroup.mem_subgroupOf.mpr hg)
    exact hM₁c ⟨⟨g, hgC⟩, hgH⟩ (hJL₁ ⟨⟨⟨g, hgC⟩, hgH⟩, hg, rfl⟩) (Subtype.ext hgt)
  · intro g hg hgt
    have hgC := TwinADescent.coreAt_le_centralizer c J' hg
    have hgH : (⟨g, hgC⟩ : ↥(Subgroup.centralizer ({c} : Set G))) ∈ coreHull Ω c :=
      le_coreHull hJ'tq (Subgroup.mem_subgroupOf.mpr hg)
    exact hM₂c ⟨⟨g, hgC⟩, hgH⟩ (hJL₂ ⟨⟨⟨g, hgC⟩, hgH⟩, hg, rfl⟩) (Subtype.ext hgt)


end Pair

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
