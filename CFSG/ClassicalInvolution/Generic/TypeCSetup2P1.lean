module

public import CFSG.ClassicalInvolution.Generic.TypeCSmallSetupInputs
import CFSG.ClassicalInvolution.Balance.BootstrapFrameFactsTriality
import CFSG.ClassicalInvolution.Balance.BootstrapUntouched
import CFSG.ClassicalInvolution.Balance.Theorem5Untouched

public section

namespace CFSG.ClassicalInvolution.Generic.TypeCSetup

open CFSG.Open CFSG.Assembly.Dichotomy CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.CoreAssembly
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

section Component

omit [Finite G] in
private theorem mathlib_isSubnormal_subgroupOf {A B : Subgroup G} (h : IsSubnormal A B) :
    (A.subgroupOf B).IsSubnormal :=
  h.subgroupOf

theorem commutes_of_component_of_normalized {H L M : Subgroup G} (hL : IsComponentOf L H)
    (hMH : M ≤ H) (hMn : ∀ h ∈ H, ∀ m ∈ M, h * m * h⁻¹ ∈ M) (hodd : Odd (Nat.card M)) :
    ∀ l ∈ L, ∀ m ∈ M, l * m = m * l := by
  have hL' : IsComponentOf (L.subgroupOf H) ⊤ := by
    refine ⟨le_top, ?_, Components.quasisimple_of_equiv (Subgroup.subgroupOfEquivOfLe hL.1)
      hL.2.2⟩
    exact Components.chain_of_mathlib_subnormal (mathlib_isSubnormal_subgroupOf hL.2.1)
  have hMn' : (M.subgroupOf H).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hMH]
    exact fun x c hx hc => hMn c hc x hx
  have hsolv : Group.IsSolvable ↥M := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have hsolv' : Group.IsSolvable ↥(M.subgroupOf H) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hMH).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hMH).injective
  have hcomm := LocalComponents.commutes_with_solvable_subnormal (L.subgroupOf H)
    (M.subgroupOf H) hL' (isSubnormal_of_normal_subgroupOf le_top inferInstance)
  intro l hl m hm
  have h1 : (⟨l, hL.1 hl⟩ : ↥H) ∈ L.subgroupOf H := hl
  have h2 : (⟨m, hMH hm⟩ : ↥H) ∈ M.subgroupOf H := hm
  have h3 := Subgroup.commutator_mem_commutator h1 h2
  rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h3
  exact congrArg Subtype.val h3

end Component

section Member

variable [IsSimpleGroup G] {Ω : Set (Subgroup G)}

theorem isQuasisimple_member_of_deltaCore_eq_bot (hnab : ∃ a b : G, a * b ≠ b * a)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω) (hIH : LocalLieSystems p f Ω)
    {L : Subgroup G} {w : G} (hLΩ : L ∈ Ω) (hw : IsClassicalMember p f L w) {F : Subgroup G}
    (hF : IsElemAbelian 2 F) (hLF : L ≤ Subgroup.centralizer (F : Set G))
    (hΔ : deltaCore F = ⊥) : CFSG.Open.IsQuasisimple L := by
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  have hW : WeakMember (GaloisField p f) L w :=
    ⟨hw.orderOf_eq_two, hw.mem, hw.perfect, hw.subnormal, hw.nonempty_equiv⟩
  have h4 : 4 ≤ Nat.card (GaloisField p f) := by
    rw [GaloisField.card p f hf.ne']
    omega
  have hmem := IsInvolutionMember.of_weakMember hW h4
  set C : Subgroup G := Subgroup.centralizer ({w} : Set G) with hC
  have hzF : ∀ x ∈ F, w * x = x * w := fun x hx =>
    (Subgroup.mem_centralizer_iff.mp (hLF hw.mem) x hx).symm
  have hFC : F ≤ C := fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr (hzF x hx).symm
  have hsub : IsSubnormal L (C ⊓ Subgroup.centralizer (F : Set G)) := by
    have h := isSubnormal_inf hw.subnormal (C ⊓ Subgroup.centralizer (F : Set G))
    rwa [inf_eq_left.mpr (le_inf (isSubnormal_le hw.subnormal) hLF),
      inf_eq_right.mpr inf_le_left] at h
  refine isQuasisimple_of_deltaCore_eq_bot_layer hw.subnormal hmem.perfect hmem.quasisimple hF
    hFC hLF hΔ hsub ?_
  intro f₀ hf₀ hf₀1 M hM
  exact hB_of_localLieSystems hp2 CFSG.ClassicalInvolution.ModelFacts.modelClauseZero
    fundamentalWholeA1 hΩ hIH hLΩ hw.isCentralInvolution
    (not_subset_center_of_ne_one hnab hf₀1)
    (hLF.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hf₀))) (hzF f₀ hf₀) M hM

theorem member_commutes_oddCoreIn_of_deltaCore_eq_bot (hnab : ∃ a b : G, a * b ≠ b * a)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω) (hIH : LocalLieSystems p f Ω)
    {x w : G} {F : Subgroup G} (hxF : x ∈ F) (hwF : w ∈ F) (hF : IsElemAbelian 2 F)
    {L : Subgroup G} (hLΩ : L ∈ Ω) (hw : IsClassicalMember p f L w)
    (hLF : L ≤ Subgroup.centralizer (F : Set G)) (hΔ : deltaCore F = ⊥)
    (hN : oddCoreIn (Subgroup.centralizer ({x} : Set G)) ≤ Subgroup.centralizer (F : Set G)) :
    ∀ n ∈ oddCoreIn (Subgroup.centralizer ({x} : Set G)), ∀ l ∈ L, n * l = l * n := by
  have hqs := isQuasisimple_member_of_deltaCore_eq_bot hnab hp2 hq hΩ hIH hLΩ hw hF hLF hΔ
  set H : Subgroup G := Subgroup.centralizer (F : Set G) with hH
  have hHw : H ≤ Subgroup.centralizer ({w} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hwF)
  have hHx : H ≤ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hxF)
  have hsub : IsSubnormal L H := by
    have h := isSubnormal_inf hw.subnormal H
    rwa [inf_eq_left.mpr hLF, inf_eq_right.mpr hHw] at h
  intro n hn l hl
  exact (commutes_of_component_of_normalized ⟨hLF, hsub, hqs⟩ hN
    (fun h hh m hm => conj_mem_oddCoreIn (hHx hh) hm) (odd_card_oddCoreIn _) l hl n hn).symm

end Member

section Alpha

omit [Finite G] in
private theorem closure_pair_conj (g a b : G) :
    Subgroup.closure ({g * a * g⁻¹, g * b * g⁻¹} : Set G) =
      conjSub g (Subgroup.closure ({a, b} : Set G)) := by
  rw [conjSub, MonoidHom.map_closure, Set.image_pair]
  rfl

omit [Finite G] in
private theorem closure_pair_mul_left (a b : G) :
    Subgroup.closure ({a, a * b} : Set G) = Subgroup.closure ({a, b} : Set G) := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | hx
    · exact Subgroup.subset_closure (by simp)
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  · rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | hx
    · exact Subgroup.subset_closure (by simp)
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      have h1 : (a : G) ∈ Subgroup.closure ({a, a * x} : Set G) := Subgroup.subset_closure (by simp)
      have h2 : a * x ∈ Subgroup.closure ({a, a * x} : Set G) := Subgroup.subset_closure (by simp)
      have := mul_mem (inv_mem h1) h2
      simpa using this

omit [Finite G] in
theorem alphaCore_conjSub_eq_bot {F : Subgroup G} (h : alphaCore F = ⊥) (g : G) :
    alphaCore (conjSub g F) = ⊥ := by
  have := Theorem5.alphaCore_map g F
  rw [h, Subgroup.map_bot] at this
  exact this.symm

omit [Finite G] in
theorem oddCoreIn_centralizer_le_centralizer_of_alphaCore_eq_bot {F : Subgroup G} {x : G}
    (hxF : x ∈ F) (hx1 : x ≠ 1) (h : alphaCore F = ⊥) :
    oddCoreIn (Subgroup.centralizer ({x} : Set G)) ≤ Subgroup.centralizer (F : Set G) := by
  intro u hu
  have huF : u ∈ uCore F := involutionOddCore_le_uCore hxF hx1 hu
  rw [Subgroup.mem_centralizer_iff]
  intro f hf
  have h1 : ⁅u, f⁆ ∈ alphaCore F := commutator_le_alphaCore (Subgroup.commutator_mem_commutator
    huF hf)
  rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1.symm

end Alpha

section Local

variable {Ω : Set (Subgroup G)}

theorem inCommonComponent_or_commutes (hp2 : p ≠ 2) (hΩ : InClass p f Ω)
    (hIH : LocalLieSystems p f Ω) {x : G} (hxne : ¬ ({x} : Set G) ⊆ Subgroup.center G)
    {L M : Subgroup G} (hL : L ∈ centMembers Ω x) (hM : M ∈ centMembers Ω x) :
    InCommonComponent x L M ∨ ∀ a ∈ modOdd x L, ∀ b ∈ modOdd x M, a * b = b * a := by
  obtain ⟨D⟩ := lieDecomposition_memberImages hp2
    CFSG.ClassicalInvolution.ModelFacts.modelClauseZero fundamentalWholeA1 hΩ hIH hxne
  have := memberJoin_normal (a := x) hΩ.conjInvariant
  obtain ⟨i, hi⟩ := D.exists_le _ (⟨L, hL, rfl⟩ : modOdd x L ∈ memberImages Ω x)
  obtain ⟨j, hj⟩ := D.exists_le _ (⟨M, hM, rfl⟩ : modOdd x M ∈ memberImages Ω x)
  by_cases hij : i = j
  · subst hij
    exact Or.inl ⟨D.Q i, (CFSG.isComponent_iff_open _).mpr (D.isComponentOf i), hi, hj⟩
  · exact Or.inr fun a ha b hb => D.commute i j hij a (hi ha) b (hj hb)

theorem exists_layer_conj_of_inCommonComponent (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hIH : LocalLieSystems p f Ω) {x : G} (hxne : ¬ ({x} : Set G) ⊆ Subgroup.center G)
    {L M : Subgroup G} (hL : L ∈ centMembers Ω x) (hM : M ∈ centMembers Ω x)
    (hcc : InCommonComponent x L M) {w y : G} (hw : IsClassicalMember p f L w)
    (hy : IsClassicalMember p f M y) : ∃ g ∈ centralizingLayer Ω {x}, w = g * y * g⁻¹ := by
  obtain ⟨D⟩ := hIH {x} hxne
  obtain ⟨w', hw'Y, hU⟩ := exists_conj_involution_of_inCommonComponent hΩ hp2 hq
    (twoClassInvolutionsConj (p := p)) D hL hM hcc hw hy
  have hw'' : IsClassicalMember p f (conjSub w' L) (w' * w * w'⁻¹) := hw.conj w'
  obtain ⟨o, ho, hoz⟩ := DeltaClosure.exists_conj_of_mul_mem hw''.isCentralInvolution.sq
    hy.isCentralInvolution.sq (odd_card_oddCoreIn _) hU
  refine ⟨w'⁻¹ * o⁻¹, mul_mem (inv_mem hw'Y) (inv_mem (oddCoreIn_le _ ho)), ?_⟩
  rw [hoz]
  group

theorem exists_involution_conj_commuting {x : G} {L M : Subgroup G} (hL : L ∈ centMembers Ω x)
    (hM : M ∈ centMembers Ω x)
    (hcomm : ∀ a ∈ modOdd x L, ∀ b ∈ modOdd x M, a * b = b * a) {w y : G}
    (hw : IsClassicalMember p f L w) (hy : IsClassicalMember p f M y) :
    ∃ o ∈ oddCoreIn (Subgroup.centralizer ({x} : Set G)),
      (o⁻¹ * w * o) * y = y * (o⁻¹ * w * o) := by
  set C : Subgroup G := Subgroup.centralizer ({x} : Set G) with hC
  have hwC : w ∈ C := hL.2 hw.mem
  have hyC : y ∈ C := hM.2 hy.mem
  have hw2 : w * w = 1 := hw.isCentralInvolution.sq
  have hy2 : y * y = 1 := hy.isCentralInvolution.sq
  have hE : Subgroup.zpowers y ≤ C := (Subgroup.zpowers_le).mpr hyC
  have hE2 : ∀ e ∈ Subgroup.zpowers y, e * e = 1 := fun e he => by
    rcases mem_zpowers_involution hy2 he with h | h
    · rw [h, one_mul]
    · rw [h]
      exact hy2
  have hz2 : oddQuotMk x ⟨w, hwC⟩ * oddQuotMk x ⟨w, hwC⟩ = 1 := by
    rw [← map_mul]
    have : (⟨w, hwC⟩ : ↥C) * ⟨w, hwC⟩ = 1 := Subtype.ext hw2
    rw [this, map_one]
  have hcomm' : ∀ (e : G) (he : e ∈ Subgroup.zpowers y), oddQuotMk x ⟨e, hE he⟩ *
      oddQuotMk x ⟨w, hwC⟩ = oddQuotMk x ⟨w, hwC⟩ * oddQuotMk x ⟨e, hE he⟩ := by
    intro e he
    rcases mem_zpowers_involution hy2 he with h | h
    · subst h
      have : (⟨1, hE he⟩ : ↥C) = 1 := rfl
      rw [this, map_one, one_mul, mul_one]
    · subst h
      exact (hcomm _ (oddQuotMk_mem_modOdd hw.mem hwC) _
        (oddQuotMk_mem_modOdd hy.mem hyC)).symm
  obtain ⟨g, hgC, hgE, hg2, hgimg⟩ := exists_involution_lift_centralizer (a := x)
    (E := Subgroup.zpowers y) hE hE2 hz2 hcomm'
  have hn : w * g ∈ oddCoreIn C := by
    have h1 : ((⟨w, hwC⟩ : ↥C)⁻¹ * ⟨g, hgC⟩) ∈ componentClassificationOddCore ↥C :=
      QuotientGroup.eq.mp hgimg.symm
    refine ⟨_, h1, ?_⟩
    simp [inv_eq_of_mul_eq_one_right hw2]
  obtain ⟨o, ho, hwo⟩ := DeltaClosure.exists_conj_of_mul_mem hg2 hw2 (odd_card_oddCoreIn C) hn
  refine ⟨o, ho, ?_⟩
  have hgy : y * g = g * y :=
    Subgroup.mem_centralizer_iff.mp hgE y (Subgroup.mem_zpowers y)
  have hg' : o⁻¹ * w * o = g := by rw [hwo]; group
  rw [hg']
  exact hgy.symm

end Local

section Edge

variable [IsSimpleGroup G]

theorem alphaCore_pair_eq_bot {K : Subgroup G} {z : G} (hbr : TypeCBranch p f G K z)
    {K₁ K₂ : Subgroup G} {z₁ z₂ : G} {A : Subgroup G}
    (hed : BalancedEdge p f (CoreAssembly.conjClass K) K₁ K₂ z₁ z₂ A) {L : Subgroup G}
    (hL : L ∈ centMembers (CoreAssembly.conjClass K) z₁) {w : G}
    (hw : IsClassicalMember p f L w) (hwz : w ≠ z₁) :
    alphaCore (Subgroup.closure ({z₁, w} : Set G)) = ⊥ := by
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simpa using hbr.five
    · exact h
  have hΩ : InClass p f (CoreAssembly.conjClass K) := inClass_conjugates hbr.cls
  have hIH := localLieSystems_of_citBelowU hΩ hbr.below
  have hxne : ¬ ({z₁} : Set G) ⊆ Subgroup.center G :=
    not_subset_center_of_ne_one hbr.nonabelian hed.cls₁.ne_one
  have hα := hed.alphaCore_eq_bot hbr.nonabelian
  have hK₂ : K₂ ∈ centMembers (CoreAssembly.conjClass K) z₁ :=
    ⟨hed.mem₂, fun k hk => Subgroup.mem_centralizer_singleton_iff.mpr
      (hed.comm z₁ hed.cls₁.mem k hk).symm⟩
  rcases inCommonComponent_or_commutes hbr.odd hΩ hIH hxne hL hK₂ with hcc | hcomm
  · obtain ⟨g, hgY, hgw⟩ := exists_layer_conj_of_inCommonComponent hbr.odd hbr.five hΩ hIH hxne hL
      hK₂ hcc hw hed.cls₂
    have hgC : g ∈ Subgroup.centralizer ({z₁} : Set G) :=
      centralizingLayer_le_centralizer _ {z₁} hgY
    have hgx : g * z₁ * g⁻¹ = z₁ := by
      rw [Subgroup.mem_centralizer_singleton_iff.mp hgC]
      group
    have e : Subgroup.closure ({z₁, w} : Set G) =
        conjSub g (Subgroup.closure ({z₁, z₂} : Set G)) := by
      rw [← closure_pair_conj, hgx, ← hgw]
    rw [e]
    exact alphaCore_conjSub_eq_bot hα g
  · obtain ⟨o, ho, hoc⟩ := exists_involution_conj_commuting hL hK₂ hcomm hw hed.cls₂
    set g' : G := o⁻¹ * w * o with hg'
    have hoC : o ∈ Subgroup.centralizer ({z₁} : Set G) := oddCoreIn_le _ ho
    have hoz : o * z₁ * o⁻¹ = z₁ := by
      rw [Subgroup.mem_centralizer_singleton_iff.mp hoC]
      group
    have hwC : w ∈ Subgroup.centralizer ({z₁} : Set G) := hL.2 hw.mem
    have hg'C : g' ∈ Subgroup.centralizer ({z₁} : Set G) :=
      mul_mem (mul_mem (inv_mem hoC) hwC) hoC
    have hcl : IsClassicalMember p f (conjSub o⁻¹ L) g' := by
      have := hw.conj o⁻¹
      rwa [inv_inv] at this
    have hL'Ω : conjSub o⁻¹ L ∈ CoreAssembly.conjClass K := by
      obtain ⟨a, ha⟩ := hL.1
      have ha' : conjSub a K = L := ha
      exact ⟨o⁻¹ * a, by show conjSub (o⁻¹ * a) K = conjSub o⁻¹ L; rw [conjSub_mul, ha']⟩
    have hne₁ : z₁ ≠ g' := by
      intro h
      apply hwz
      have : w = o * g' * o⁻¹ := by rw [hg']; group
      rw [this, ← h, hoz]
    have hc₁ : z₁ * g' = g' * z₁ := (Subgroup.mem_centralizer_singleton_iff.mp hg'C).symm
    have hK₁L : Commutes K₁ (conjSub o⁻¹ L) :=
      commutes_of_not_a2Configuration hbr.odd hf hbr.cls hbr.noA2 hed.mem₁ hL'Ω hed.cls₁ hcl hne₁
        hc₁
    have hB : Subgroup.closure ({z₁, g'} : Set G) = Subgroup.closure ({z₁, z₂} : Set G) := by
      by_cases hg2 : g' = z₂
      · rw [hg2]
      · have hne₂ : z₂ ≠ g' := fun h => hg2 h.symm
        have hK₂L : Commutes K₂ (conjSub o⁻¹ L) :=
          commutes_of_not_a2Configuration hbr.odd hf hbr.cls hbr.noA2 hed.mem₂ hL'Ω hed.cls₂ hcl
            hne₂ hoc.symm
        have T := depTriple_of_not_bootData hbr.noBoot hed.mem₁ hed.cls₁ hed.cls₂ hcl hed.comm
          hK₁L hK₂L hed.ne hne₁ hne₂
        rw [← T.prod, closure_pair_mul_left]
    have e : Subgroup.closure ({z₁, w} : Set G) =
        conjSub o (Subgroup.closure ({z₁, g'} : Set G)) := by
      have hw' : o * g' * o⁻¹ = w := by rw [hg']; group
      rw [← closure_pair_conj, hoz, hw']
    rw [e, hB]
    exact alphaCore_conjSub_eq_bot hα o

theorem member_commutes_oddCoreIn_of_balancedEdge {K : Subgroup G} {z : G}
    (hbr : TypeCBranch p f G K z) {K₁ K₂ : Subgroup G} {z₁ z₂ : G} {A : Subgroup G}
    (hed : BalancedEdge p f (CoreAssembly.conjClass K) K₁ K₂ z₁ z₂ A) {L : Subgroup G}
    (hL : L ∈ centMembers (CoreAssembly.conjClass K) z₁) :
    ∀ n ∈ oddCoreIn (Subgroup.centralizer ({z₁} : Set G)), ∀ l ∈ L, n * l = l * n := by
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simpa using hbr.five
    · exact h
  have hΩ : InClass p f (CoreAssembly.conjClass K) := inClass_conjugates hbr.cls
  have hIH := localLieSystems_of_citBelowU hΩ hbr.below
  have hα := hed.alphaCore_eq_bot hbr.nonabelian
  obtain ⟨w, hw⟩ := hΩ.classical L hL.1
  by_cases hwz : w = z₁
  · obtain ⟨a, ha⟩ := hL.1
    obtain ⟨b, hb⟩ := hed.mem₁
    have ha' : conjSub a K = L := ha
    have hb' : conjSub b K = K₁ := hb
    set g : G := a * b⁻¹ with hg
    have hLg : L = conjSub g K₁ := by
      rw [← hb', ← ha', ← conjSub_mul, hg]
      group
    have hw' : IsCentralInvolution (conjSub g K₁) w := hLg ▸ hw.isCentralInvolution
    have hwg : w = g * z₁ * g⁻¹ :=
      (hed.cls₁.conj g).eq_of_isCentralInvolution hbr.odd hf hw'
    have hgx : g * z₁ * g⁻¹ = z₁ := hwg.symm.trans hwz
    have hB : IsElemAbelian 2 (Subgroup.closure ({z₁, z₂} : Set G)) :=
      CFSG.SignalizerFunctor.Helpers.elementary_abelian_of_le 2 hed.balance.elem hed.pair_le
    have hα' := alphaCore_conjSub_eq_bot hα g
    have hΔ : deltaCore (conjSub g (Subgroup.closure ({z₁, z₂} : Set G))) = ⊥ := by
      have hle := deltaCore_le_alphaCore (F := conjSub g (Subgroup.closure ({z₁, z₂} : Set G)))
      rw [hα'] at hle
      exact le_bot_iff.mp hle
    have hxF : z₁ ∈ conjSub g (Subgroup.closure ({z₁, z₂} : Set G)) := by
      have := conj_mem_conjSub (n := g) (Subgroup.subset_closure
        (by simp : z₁ ∈ ({z₁, z₂} : Set G)))
      rwa [hgx] at this
    have hLF : L ≤ Subgroup.centralizer (conjSub g (Subgroup.closure ({z₁, z₂} : Set G)) : Set G) :=
      by rw [hLg]; exact BootRank3.conjSub_le_centralizer hed.le_centralizer₁ g
    exact member_commutes_oddCoreIn_of_deltaCore_eq_bot hbr.nonabelian hbr.odd hbr.five hΩ hIH hxF
      (hwz ▸ hxF) (BootRank3.isElemAbelian_two_conjSub hB g) hL.1 hw hLF hΔ
      (oddCoreIn_centralizer_le_centralizer_of_alphaCore_eq_bot hxF hed.cls₁.ne_one hα')
  · have hα' := alphaCore_pair_eq_bot hbr hed hL hw hwz
    have hwC : w ∈ Subgroup.centralizer ({z₁} : Set G) := hL.2 hw.mem
    have hcomm : z₁ * w = w * z₁ := (Subgroup.mem_centralizer_singleton_iff.mp hwC).symm
    have hF : IsElemAbelian 2 (Subgroup.closure ({z₁, w} : Set G)) := by
      refine Theorem5.isElemAbelian_closure_of_commuting_involutions ?_ ?_
      · intro s hs
        rcases hs with rfl | hs
        · exact hed.cls₁.isCentralInvolution.sq
        · rw [Set.mem_singleton_iff] at hs
          subst hs
          exact hw.isCentralInvolution.sq
      · intro s hs t ht
        rcases hs with rfl | hs <;> rcases ht with rfl | ht
        · rfl
        · rw [Set.mem_singleton_iff] at ht
          subst ht
          exact hcomm
        · rw [Set.mem_singleton_iff] at hs
          subst hs
          exact hcomm.symm
        · rw [Set.mem_singleton_iff] at hs ht
          subst hs ht
          rfl
    have hΔ : deltaCore (Subgroup.closure ({z₁, w} : Set G)) = ⊥ := by
      have hle := deltaCore_le_alphaCore (F := Subgroup.closure ({z₁, w} : Set G))
      rw [hα'] at hle
      exact le_bot_iff.mp hle
    have hxF : z₁ ∈ Subgroup.closure ({z₁, w} : Set G) := Subgroup.subset_closure (by simp)
    have hwF : w ∈ Subgroup.closure ({z₁, w} : Set G) := Subgroup.subset_closure (by simp)
    have hLF : L ≤ Subgroup.centralizer (Subgroup.closure ({z₁, w} : Set G) : Set G) := by
      rw [Subgroup.centralizer_closure]
      intro k hk
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      rcases hx with rfl | hx
      · exact (Subgroup.mem_centralizer_singleton_iff.mp (hL.2 hk)).symm
      · rw [Set.mem_singleton_iff] at hx
        subst hx
        exact (Subgroup.mem_centralizer_singleton_iff.mp
          (CFSG.ClassicalInvolution.RouteD.le_centralizer_of_isClassicalMember hw hk)).symm
    exact member_commutes_oddCoreIn_of_deltaCore_eq_bot hbr.nonabelian hbr.odd hbr.five hΩ hIH hxF
      hwF hF hL.1 hw hLF hΔ
      (oddCoreIn_centralizer_le_centralizer_of_alphaCore_eq_bot hxF hed.cls₁.ne_one hα')

end Edge

theorem typeCP1Step : TypeCP1Step p f := by
  intro G _ _ _ K z hbr K₁ K₂ z₁ z₂ A hed _
  have hΩ : InClass p f (CoreAssembly.conjClass K) := inClass_conjugates hbr.cls
  intro d hd
  rw [Subgroup.mem_center_iff]
  intro y
  by_cases hne : (centralizingMembers (CoreAssembly.conjClass K) {z₁}).Nonempty
  · have hgen := (inClass_local hΩ {z₁} hne).generated
    have hle : (⨆ L ∈ restrictFamily (centralizingMembers (CoreAssembly.conjClass K) {z₁})
        (centralizingLayer (CoreAssembly.conjClass K) {z₁}), L) ≤
        Subgroup.centralizer ({d} : Set ↥(centralizingLayer (CoreAssembly.conjClass K) {z₁})) := by
      refine iSup₂_le fun L hL => ?_
      obtain ⟨M, hM, hMY, rfl⟩ := hL
      intro k hk
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hdO : (d : G) ∈ oddCoreIn (Subgroup.centralizer ({z₁} : Set G)) :=
        ⟨Subgroup.inclusion (centLayer_le_centralizer (CoreAssembly.conjClass K) z₁) d,
          map_inclusion_oddCore_le hΩ.conjInvariant ⟨d, hd, rfl⟩, rfl⟩
      exact Subtype.ext (member_commutes_oddCoreIn_of_balancedEdge hbr hed hM _ hdO k
        (Subgroup.mem_subgroupOf.mp hk)).symm
    have hy : y ∈ (⨆ L ∈ restrictFamily (centralizingMembers (CoreAssembly.conjClass K) {z₁})
        (centralizingLayer (CoreAssembly.conjClass K) {z₁}), L) := hgen ▸ Subgroup.mem_top y
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hy)
  · have hY : centLayer (CoreAssembly.conjClass K) z₁ = ⊥ := by
      refine le_bot_iff.mp (centLayer_le fun L hL => ?_)
      exact absurd ⟨L, hL⟩ hne
    have htriv : ∀ u : ↥(centLayer (CoreAssembly.conjClass K) z₁), u = 1 := fun u =>
      Subtype.ext (by
        have := u.2
        simpa only [hY, Subgroup.mem_bot, Subgroup.coe_one] using this)
    rw [htriv y, htriv d]

end CFSG.ClassicalInvolution.Generic.TypeCSetup
