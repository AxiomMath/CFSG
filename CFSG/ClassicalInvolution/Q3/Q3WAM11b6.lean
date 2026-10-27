module

public import CFSG.ClassicalInvolution.Q3.Q3WAM11b4
public import CFSG.ClassicalInvolution.Q3.Q3WAM11b5
public import CFSG.ClassicalInvolution.Q3.Q3WAM11One
public import CFSG.ClassicalInvolution.Q3.Q3TCP1
public import CFSG.ClassicalInvolution.Q3.Q3WASTInner

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.Phan (UnitaryBlockStandardPair)


section Closure

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K₀ : Subgroup G} {z₀ : G}

theorem false_of_twin_nbhds3 [IsSimpleGroup G] (hnab : ∃ x y : G, x * y ≠ y * x)
    (hΩ : InClass3 Ω) (hconn : RouteD.DeltaConnected Ω)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K₀) (hz : IsClassicalMember3 K₀ z₀)
    (hD1 : ∀ L ∈ centralizingMembers Ω {z₀}, L ≠ K₀ → Commutes K₀ L) {K j₀ : Subgroup G}
    (hK : K ∈ Ω) (hj₀ : j₀ ∈ Ω) (hKj₀ : Commutes K j₀)
    (htw : ∀ N ∈ commNbhd3 Ω K, commNbhd3 Ω N = commNbhd3 Ω j₀) : False := by
  have hν : ∀ a ∈ Ω, (commNbhd3 Ω a).ncard + 1 = (centralizingMembers Ω {z₀}).ncard :=
    fun a ha => ncard_commNbhd3_add_one hΩ hsingle hz hD1 ha
  have hfin : ∀ a, (commNbhd3 Ω a).Finite := fun a => Set.toFinite _
  have hLM : ∀ K' ∈ commNbhd3 Ω j₀, ∀ N ∈ commNbhd3 Ω K, Commutes K' N := by
    intro K' hK' N hN
    have h1 : K' ∈ commNbhd3 Ω N := (htw N hN).symm ▸ hK'
    exact h1.2.symm
  have hnK' : ∀ K' ∈ commNbhd3 Ω j₀, commNbhd3 Ω K' = commNbhd3 Ω K := by
    intro K' hK'
    apply Eq.symm
    refine Set.eq_of_subset_of_ncard_le (fun N hN => ⟨hN.1, hLM K' hK' N hN⟩) ?_ (hfin _)
    have h0 := hν K' hK'.1
    have h1 := hν K hK
    omega
  have hnN : ∀ N ∈ commNbhd3 Ω K, commNbhd3 Ω N = commNbhd3 Ω j₀ := htw
  have hKL : K ∈ commNbhd3 Ω j₀ := ⟨hK, hKj₀.symm⟩
  have hS : Ω ⊆ commNbhd3 Ω j₀ ∪ commNbhd3 Ω K := by
    refine subset_of_adj_closed hconn (𝔖 := commNbhd3 Ω j₀ ∪ commNbhd3 Ω K) ?_ ⟨K, Or.inl hKL⟩ ?_
    · rintro N (hN | hN)
      exacts [hN.1, hN.1]
    · rintro A (hA | hA) L hL' hLA hc
      · exact Or.inr (hnK' A hA ▸ ⟨hL', hc⟩)
      · exact Or.inl (hnN A hA ▸ ⟨hL', hc⟩)
  let M₁ : Subgroup G := ⨆ L ∈ commNbhd3 Ω j₀, L
  have hle : ∀ N ∈ commNbhd3 Ω K, ∀ n ∈ N, M₁ ≤ Subgroup.centralizer ({n} : Set G) := by
    intro N hN n hn
    exact iSup₂_le fun L hL' l hl => Subgroup.mem_centralizer_singleton_iff.mpr
      (hLM L hL' N hN l hl n hn)
  have hcent : ∀ N ∈ commNbhd3 Ω K, ∀ n ∈ N, ∀ m ∈ M₁, n * m * n⁻¹ = m := by
    intro N hN n hn m hm
    rw [mul_inv_eq_iff_eq_mul]
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle N hN n hn hm)).symm
  have hnorm : M₁.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hΩ.generated]
    refine iSup₂_le fun N hN => ?_
    rcases hS hN with hN' | hN'
    · exact le_trans (le_iSup₂ (f := fun L (_ : L ∈ commNbhd3 Ω j₀) => L) N hN')
        Subgroup.le_normalizer
    · intro n hn
      refine Subgroup.mem_normalizer_iff.mpr fun m => ⟨fun hm => ?_, fun hm => ?_⟩
      · rw [hcent N hN' n hn m hm]
        exact hm
      · have h1 := hcent N hN' n⁻¹ (N.inv_mem hn) _ hm
        have h2 : n⁻¹ * (n * m * n⁻¹) * n⁻¹⁻¹ = m := by group
        rw [h2] at h1
        rw [h1]
        exact hm
  have := hnorm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal M₁ with h | h
  · obtain ⟨u, hu⟩ := hΩ.classical K hK
    have hKle : K ≤ M₁ := le_iSup₂ (f := fun L (_ : L ∈ commNbhd3 Ω j₀) => L) K hKL
    rw [h] at hKle
    have hu1 : u = 1 := Subgroup.mem_bot.mp (hKle hu.mem)
    have := hu.orderOf_eq_two
    rw [hu1, orderOf_one] at this
    omega
  · obtain ⟨u, hu⟩ := hΩ.classical j₀ hj₀
    have hj₀M : j₀ ∈ commNbhd3 Ω K := ⟨hj₀, hKj₀⟩
    have hmem : u ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : g ∈ M₁ := h ▸ Subgroup.mem_top g
      exact Subgroup.mem_centralizer_singleton_iff.mp (hle j₀ hj₀M u hu.mem hg)
    rw [CoreAssembly.center_eq_bot hnab, Subgroup.mem_bot] at hmem
    have := hu.orderOf_eq_two
    rw [hmem, orderOf_one] at this
    omega

end Closure

section Twins

variable {G : Type} [Group G] [Finite G]

theorem M11Pic.ne_of_cross {Ω : Set (Subgroup G)} {x : G} (c : LocOK Ω x) (P : M11Pic Ω x)
    {A B : Subgroup G} (hA : A ∈ compMembers3 Ω x P.D P.i₀) (hB : B ∈ compMembers3 Ω x P.D P.i₁)
    {a b : G} (ha : IsClassicalMember3 A a) (hb : IsClassicalMember3 B b) : a ≠ b := by
  intro hab
  subst hab
  have haY : a ∈ locLayer Ω x := le_centralizingLayer hA.1 ha.mem
  have hU := ConnectedA2.isUniqueInvolution_locImg c.hex hA.1
    (isUniqueInvolution_of_exact3 (c.hex A hA.1.1) ha)
  have hy1 : Gaps.locMk Ω x ⟨a, haY⟩ ≠ 1 := hU.ne_one
  have hyA : Gaps.locMk Ω x ⟨a, haY⟩ ∈ (P.D.hom P.i₀).range :=
    hA.2 ⟨⟨a, haY⟩, Subgroup.mem_subgroupOf.mpr ha.mem, rfl⟩
  have hyB : Gaps.locMk Ω x ⟨a, haY⟩ ∈ (P.D.hom P.i₁).range :=
    hB.2 ⟨⟨a, haY⟩, Subgroup.mem_subgroupOf.mpr hb.mem, rfl⟩
  obtain ⟨w, hw⟩ := hyB
  apply hy1
  rw [← hw]
  have hwc : w ∈ Subgroup.center (P.D.kind P.i₁).G := by
    rw [Subgroup.mem_center_iff]
    intro v
    apply m11_hom_injective_gen P.k₁ (P.D.hom P.i₁) (P.D.ker_le_center P.i₁)
    rw [map_mul, map_mul, hw]
    exact (commutes_range3 P.D P.ne _ hyA _ ⟨v, rfl⟩).symm
  rw [m11_center_eq_bot_gen P.k₁, Subgroup.mem_bot] at hwc
  rw [hwc, map_one]

theorem le_centralizer_mul3 {N : Subgroup G} {a b : G} (h₁ : N ≤ Subgroup.centralizer ({a} : Set G))
    (h₂ : N ≤ Subgroup.centralizer ({b} : Set G)) :
    N ≤ Subgroup.centralizer ({a * b} : Set G) := by
  intro n hn
  have e1 := Subgroup.mem_centralizer_singleton_iff.mp (h₁ hn)
  have e2 := Subgroup.mem_centralizer_singleton_iff.mp (h₂ hn)
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc n * (a * b) = (n * a) * b := (mul_assoc _ _ _).symm
    _ = (a * n) * b := by rw [e1]
    _ = a * (n * b) := mul_assoc _ _ _
    _ = a * (b * n) := by rw [e2]
    _ = a * b * n := (mul_assoc _ _ _).symm

theorem classical3_mul_self {Y : Type} [Group Y] {L : Subgroup Y} {z : Y}
    (h : IsClassicalMember3 L z) : z * z = 1 := by
  have := pow_orderOf_eq_one z
  rwa [h.orderOf_eq_two, pow_two] at this

variable [IsSimpleGroup G] {K : Subgroup G} {z : G}

theorem claimT (hA : M11AutInner) (hP : Q3TC.ProductP1Input3) (hnab : ∃ x y : G, x * y ≠ y * x)
    (h : RouteD3Setup K z) (h3 : LocalOddThreeFree3 (conjClass3 K) z)
    (hshape : LocalShapeC3 1 CompData.m11 (conjClass3 K) z) (P : M11Pic (conjClass3 K) z)
    {L₁ L₂ : Subgroup G} (hL₁ : L₁ ∈ compMembers3 (conjClass3 K) z P.D P.i₁)
    (hL₂ : L₂ ∈ compMembers3 (conjClass3 K) z P.D P.i₁) (hadj : MemAdj L₁ L₂) :
    commNbhd3 (conjClass3 K) L₁ = commNbhd3 (conjClass3 K) L₂ := by
  classical
  obtain ⟨hne, t, s, ht, hs, hts⟩ := hadj
  have hΩ := h.inClass
  obtain ⟨hex, hP1⟩ := h.setup
  have hc : LocOK (conjClass3 K) z := ⟨hΩ, hex, hP1, h3⟩
  have hsingle : ∀ L ∈ conjClass3 K, ∃ g : G, L = conjSub g K := by
    rintro L ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  have hKΩ : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  have hKz : K ∈ centralizingMembers (conjClass3 K) {z} :=
    ⟨hKΩ, isSubnormal_le h.cls.subnormal⟩
  have hKV : K ∈ compMembers3 (conjClass3 K) z P.D P.i₀ := P.vertex_mem hKz h.cls
  have hD1 : ∀ L ∈ centralizingMembers (conjClass3 K) {z}, L ≠ K → Commutes K L :=
    fun L hL hLK => P.vertex_universal hc hKV L hL hLK
  have hD1all : ∀ N ∈ conjClass3 K, ∀ u : G, IsClassicalMember3 N u →
      ∀ L ∈ centralizingMembers (conjClass3 K) {u}, L ≠ N → Commutes N L :=
    fun N hN u hu L hL hLN => commutes_of_centralizing3 hΩ hsingle h.cls hD1 hN hu hL hLN
  have hν : ∀ a ∈ conjClass3 K, (commNbhd3 (conjClass3 K) a).ncard + 1 =
      (centralizingMembers (conjClass3 K) {z}).ncard :=
    fun a ha => ncard_commNbhd3_add_one hΩ hsingle h.cls hD1 ha
  have hL₁Ω : L₁ ∈ conjClass3 K := hL₁.1.1
  have hL₂Ω : L₂ ∈ conjClass3 K := hL₂.1.1
  have hKL₁ : Commutes K L₁ := P.commutes_cross hc hKV hL₁
  have hKL₂ : Commutes K L₂ := P.commutes_cross hc hKV hL₂
  have hsK : K ≤ Subgroup.centralizer ({s} : Set G) := le_centralizer_of_commutes3 hKL₂ hs.mem
  have htK : K ≤ Subgroup.centralizer ({t} : Set G) := le_centralizer_of_commutes3 hKL₁ ht.mem
  have hKL₁ne : K ≠ L₁ := fun he => not_commutes_self3 h.cls (he ▸ hKL₁)
  have hKL₂ne : K ≠ L₂ := fun he => not_commutes_self3 h.cls (he ▸ hKL₂)
  obtain ⟨g, hg⟩ := hsingle L₁ hL₁Ω
  have htg : t = g * z * g⁻¹ := by
    refine involution_unique3 ht ?_
    rw [hg]
    exact h.cls.conj g
  obtain ⟨Pt⟩ : Nonempty (M11Pic (conjClass3 K) t) := by
    refine nonempty_pic ?_
    rw [htg]
    exact LocalShapeC3.conjShape3 hΩ.conjInvariant g hshape
  have ct : LocOK (conjClass3 K) t := by
    rw [htg]
    exact hc.conj g
  have hL₁t : L₁ ∈ centralizingMembers (conjClass3 K) {t} :=
    ⟨hL₁Ω, isSubnormal_le ht.subnormal⟩
  have hL₁V : L₁ ∈ compMembers3 (conjClass3 K) t Pt.D Pt.i₀ := Pt.vertex_mem hL₁t ht
  have hKt : K ∈ centralizingMembers (conjClass3 K) {t} := ⟨hKΩ, htK⟩
  have hKm : K ∈ compMembers3 (conjClass3 K) t Pt.D Pt.i₁ := Pt.mem_i₁ ct hL₁V hKt hKL₁ne
  have hs1 : s * t * s⁻¹ = t := mul_inv_eq_iff_eq_mul.mpr hts.symm
  have hs2 : s * s = 1 := classical3_mul_self hs
  have hz2 : z * z = 1 := classical3_mul_self h.cls
  rcases Pt.layer_dichotomy hA ct hL₁V hKm h.cls hs1 hs2 hsK with hI | hII
  ·
    have hn1 : commNbhd3 (conjClass3 K) L₁ = centralizingMembers (conjClass3 K) {t} \ {L₁} :=
      commNbhd3_eq hΩ hsingle h.cls hD1 hL₁Ω ht
    have hn2 : commNbhd3 (conjClass3 K) L₂ = centralizingMembers (conjClass3 K) {s} \ {L₂} :=
      commNbhd3_eq hΩ hsingle h.cls hD1 hL₂Ω hs
    have hsub : commNbhd3 (conjClass3 K) L₁ ⊆ commNbhd3 (conjClass3 K) L₂ := by
      intro N hN
      rw [hn1] at hN
      rw [hn2]
      obtain ⟨hNt, hNL₁⟩ := hN
      have hNm := Pt.mem_i₁ ct hL₁V hNt fun he => hNL₁ he
      refine ⟨⟨hNt.1, hI N hNm⟩, ?_⟩
      intro hNL₂
      have hNeq : N = L₂ := hNL₂
      rw [hNeq] at hNt
      exact P.not_commutes hc hL₁ hL₂ (hD1all L₁ hL₁Ω t ht L₂ hNt (Ne.symm hne))
    refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)
    have h0 := hν L₁ hL₁Ω
    have h1 := hν L₂ hL₂Ω
    omega
  ·
    exfalso
    have hsz : s * z = z * s := Subgroup.mem_centralizer_singleton_iff.mp (hL₂.1.2 hs.mem)
    have hzs : z * s = s * z := hsz.symm
    have hzs_ne : z ≠ s := fun he => M11Pic.ne_of_cross hc P hKV hL₂ h.cls hs he
    obtain ⟨hP1x, hO3x⟩ := hP G K z h L₂ hL₂Ω s hs hKL₂ hzs_ne
    have htw := twin_condition_x3 hD1all hKΩ hL₂Ω h.cls hs hKL₂ rfl
    obtain ⟨u₀, hu₀⟩ := Pt.hasInv_exists ct hKm
    have hu₀2 : orderOf u₀ = 2 := by
      obtain ⟨R, -, hR⟩ := hu₀
      exact hR.orderOf_eq_two
    obtain ⟨u', hu'2, hu'ne, hu'c⟩ := m11_exists_commuting_gen Pt.k₁ hu₀2
    obtain ⟨β, hβi⟩ := Pt.exists_hasInv_of_involution ct hu'2
    have hβm := Pt.mem_of_hasInv hβi
    have hβK : β ≠ K := fun he => hu'ne (Pt.hasInv_unique (he ▸ hβi) hu₀)
    obtain ⟨v, hv⟩ := hΩ.classical β hβm.1.1
    have hzY : z ∈ locLayer (conjClass3 K) t := le_centralizingLayer hKt h.cls.mem
    have hvY : v ∈ locLayer (conjClass3 K) t := le_centralizingLayer hβm.1 hv.mem
    have hzv : z * v = v * z := by
      refine commute_of_locMk_commute ct.hP1 hzY hvY hz2 (classical3_mul_self hv) ?_
      have e1 := Pt.locMk_eq ct hKt h.cls hu₀
      have e2 := Pt.locMk_eq ct hβm.1 hv hβi
      rw [e1, e2, ← map_mul, ← map_mul, hu'c]
    have hvK : conjSub v K = K :=
      P.conjSub_vertex hc hKV (mul_inv_eq_iff_eq_mul.mpr hzv.symm)
    have hβx : β ∈ centralizingMembers (conjClass3 K) {z * s} := by
      refine ⟨hβm.1.1, ?_⟩
      rw [hzs]
      exact hII β hβm
    have hKx : K ∈ centralizingMembers (conjClass3 K) {z * s} :=
      ⟨hKΩ, le_centralizer_mul3 hKz.2 hsK⟩
    have hL₂x : L₂ ∈ centralizingMembers (conjClass3 K) {z * s} :=
      ⟨hL₂Ω, le_centralizer_mul3 hL₂.1.2 (isSubnormal_le hs.subnormal)⟩
    have hzs1 : z * s ≠ 1 := by
      intro h1
      apply hzs_ne
      have e := eq_inv_of_mul_eq_one_right h1
      rw [e, inv_eq_of_mul_eq_one_right hz2]
    have hxc : ¬ ({z * s} : Set G) ⊆ Subgroup.center G := not_subset_center_of_ne_one hnab hzs1
    have hnKβ : ¬ Commutes K β := Pt.not_commutes ct hKm hβm
    have hβ_not : ¬ (β = K ∨ Commutes β K) := by
      rintro (h' | h')
      · exact hβK h'
      · exact hnKβ h'.symm
    have hnβL₂ : ¬ (β = L₂ ∨ Commutes β L₂) := fun h' => hβ_not ((htw β hβx).mpr h')
    have hβL₂ : β ≠ L₂ := fun he => hnβL₂ (Or.inl he)
    have hnβM : ¬ Commutes β L₂ := fun h' => hnβL₂ (Or.inr h')
    have key := chainSign_images3 hΩ hex h.ih hxc hP1x hO3x h.cls hv hs hKx hβx hL₂x rfl hzs_ne
      hKL₂ hKL₂ne (Ne.symm hβK) hβL₂ hnKβ hnβM hvK htw
    have hs' : (∃ W, LinearBlockStandardPair (GaloisField 3 1) W
          (locImg (conjClass3 K) (z * s) K) (locImg (conjClass3 K) (z * s) β)) ∨
        ∃ W, UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W
          (locImg (conjClass3 K) (z * s) K) (locImg (conjClass3 K) (z * s) β) := by
      rcases key with ⟨h1, -⟩ | ⟨h1, -⟩
      exacts [Or.inl h1, Or.inr h1]
    exact Pt.false_of_std_pair ct hKm hβm hKx hβx hs'

theorem false_of_m11_one (hA : M11AutInner) (hP : Q3TC.ProductP1Input3)
    (hnab : ∃ x y : G, x * y ≠ y * x) (h : RouteD3Setup K z)
    (h3 : LocalOddThreeFree3 (conjClass3 K) z)
    (hshape : LocalShapeC3 1 CompData.m11 (conjClass3 K) z) : False := by
  classical
  obtain ⟨P⟩ := nonempty_pic hshape
  have hΩ := h.inClass
  obtain ⟨hex, hP1⟩ := h.setup
  have hc : LocOK (conjClass3 K) z := ⟨hΩ, hex, hP1, h3⟩
  have hsingle : ∀ L ∈ conjClass3 K, ∃ g : G, L = conjSub g K := by
    rintro L ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  have hKΩ : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  have hKz : K ∈ centralizingMembers (conjClass3 K) {z} :=
    ⟨hKΩ, isSubnormal_le h.cls.subnormal⟩
  have hKV : K ∈ compMembers3 (conjClass3 K) z P.D P.i₀ := P.vertex_mem hKz h.cls
  have hD1 : ∀ L ∈ centralizingMembers (conjClass3 K) {z}, L ≠ K → Commutes K L :=
    fun L hL hLK => P.vertex_universal hc hKV L hL hLK
  have hS : ∀ N ∈ commNbhd3 (conjClass3 K) K, N ∈ compMembers3 (conjClass3 K) z P.D P.i₁ := by
    intro N hN
    have hNz : N ∈ centralizingMembers (conjClass3 K) {z} :=
      ⟨hN.1, le_centralizer_of_commutes3 hN.2.symm h.cls.mem⟩
    have hNK : N ≠ K := fun he => not_commutes_self3 h.cls (he ▸ hN.2)
    exact P.mem_i₁ hc hKV hNz hNK
  obtain ⟨N₀, N₀', hN₀, hN₀', -⟩ := P.exists_ne hc
  have htw : ∀ N ∈ commNbhd3 (conjClass3 K) K,
      commNbhd3 (conjClass3 K) N = commNbhd3 (conjClass3 K) N₀ := by
    intro N hN
    have hconn := P.members_connected hc (hS N hN) hN₀
    induction hconn with
    | refl => rfl
    | tail hchain hstep ih =>
      exact (ih hstep.1).trans (claimT hA hP hnab h h3 hshape P hstep.1 hstep.2.1 hstep.2.2)
  exact false_of_twin_nbhds3 hnab hΩ ((CoreAssembly.deltaConnected_iff K).mp h.conn) hsingle
    h.cls hD1 hKΩ hN₀.1.1 (P.commutes_cross hc hKV hN₀) htw

end Twins

section Final

theorem m11OneInput_of_inputs (h3 : OddThreeFreeInput) (hP : Q3TC.ProductP1Input3)
    (hA : M11AutInner) : M11OneInput := by
  intro G _ _ _ hnab K z hR hshape
  exact (false_of_m11_one hA hP hnab hR (h3 G K z hR) hshape).elim

theorem pieceM11₃_of_inputs (h3 : OddThreeFreeInput) (hP : Q3TC.ProductP1Input3)
    (hA : M11AutInner) : PieceM11₃ :=
  pieceM11₃_of_input h3 (m11OneInput_of_inputs h3 hP hA)

end Final

end CFSG.ClassicalInvolution.Q3.Q3W
