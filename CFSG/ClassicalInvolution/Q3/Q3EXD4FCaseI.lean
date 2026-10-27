module

public import CFSG.ClassicalInvolution.Q3.Q3EXD4FInv
public import CFSG.ClassicalInvolution.Q3.Q3NGCount
public import CFSG.ClassicalInvolution.Q3.Q3WAM11Comp
public import CFSG.ClassicalInvolution.Balance.Theorem5Untouched
public import CFSG.ClassicalInvolution.RouteD.ExoticD4FourMain

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3W.EX

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD.Exotic CFSG.ClassicalInvolution.Balance
open CFSG.ClassicalInvolution.RouteD.Gaps (locMk)
open scoped commutatorElement


section Aux

variable {G : Type} [Group G] {ι : Type} {Ω : Set (Subgroup G)}

theorem range_hom_normal3 {X : Type} [Group X] {Φ : Set (Subgroup X)}
    (D : LieSystemData3 ι X Φ) (i : ι) : ((D.hom i).range).Normal := by
  have key : ∀ g ∈ (⨆ k, (D.hom k).range : Subgroup X), ∀ n ∈ (D.hom i).range,
      g * n * g⁻¹ ∈ (D.hom i).range := by
    intro g hg
    induction hg using Subgroup.iSup_induction' with
    | hp k y hy =>
      intro n hn
      by_cases hki : k = i
      · subst hki
        exact (D.hom k).range.mul_mem ((D.hom k).range.mul_mem hy hn)
          ((D.hom k).range.inv_mem hy)
      · have := commutes_range3 D hki y hy n hn
        rw [this, mul_assoc, mul_inv_cancel, mul_one]
        exact hn
    | h1 => intro n hn; simpa using hn
    | hmul x y _ _ hx hy =>
      intro n hn
      have e : x * y * n * (x * y)⁻¹ = x * (y * n * y⁻¹) * x⁻¹ := by group
      rw [e]
      exact hx _ (hy n hn)
  refine ⟨fun n hn g => key g ?_ n hn⟩
  rw [D.generate]
  trivial

theorem conjSub_mem_compMembers_of_mem_layer3 (hΩ : ConjInvariant Ω) {u : G}
    {D : LieSystemData3 ι (locQuot Ω u) (locFamily Ω u)} {i : ι} {N : Subgroup G}
    (hN : N ∈ compMembers3 Ω u D i) {c : G} (hc : c ∈ locLayer Ω u) :
    conjSub c N ∈ compMembers3 Ω u D i := by
  have hcC : c ∈ Subgroup.centralizer ({u} : Set G) := centralizingLayer_le_centralizer Ω {u} hc
  refine ⟨⟨hΩ c N hN.1.1, ?_⟩, ?_⟩
  · intro y hy
    rw [mem_conjSub_iff] at hy
    have h1 := hN.1.2 hy
    have e : y = c * (c⁻¹ * y * c) * c⁻¹ := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hcC h1) (Subgroup.inv_mem _ hcC)
  · rw [Gaps.locImg_conjSub_layer N ⟨c, hc⟩]
    rintro _ ⟨a, ha, rfl⟩
    exact (range_hom_normal3 D i).conj_mem a (hN.2 ha) (locMk Ω u ⟨c, hc⟩)

theorem commutes_partner_of_commutes_u {x : G} {D : LieSystemData3 ι (locQuot Ω x) (locFamily Ω x)}
    {i : ι} (hk : PowCop3 (D.kind i)) {N N' : Subgroup G} {R R' : Subgroup (D.kind i).G}
    (h : Corr3 Ω x D i N R) (h' : Corr3 Ω x D i N' R') (hc : Commutes N N') : Commutes R R' := by
  have h1 := commutes_locImg_of_commutes (x := x) (Ω := Ω) hc
  rw [h.2.2, h'.2.2] at h1
  intro a ha b hb
  exact (commutes_of_map_commute_exponent3 (D.hom i) (D.ker_le_center i)
    (fun w hw => hk.cop w (D.ker_le_center i hw)) (A := R') (L := R) (hk.pow3 R h.2.1)
    (fun a' ha' l hl => (h1 _ ⟨l, hl, rfl⟩ _ ⟨a', ha', rfl⟩).symm) b hb a ha).symm

end Aux

section LemmaZ

variable {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G} {a : ℕ}

theorem members_eq_or_commute3 (S : D4Ctx3 G K z a) {M K' : Subgroup G}
    (hM : M ∈ conjClass3 K) (hK' : K' ∈ conjClass3 K) {w : G} (hwM : IsClassicalMember3 M w)
    (hwK : IsClassicalMember3 K' w) : K' = M ∨ Commutes K' M := by
  classical
  set Ω := conjClass3 K with hΩdef
  have hΩ : InClass3 Ω := S.setup.inClass
  obtain ⟨hex, -⟩ := S.setup.setup
  obtain ⟨w₀, hw₀, hP1, hO3, ι, hι, D, i₁, hcard, hk, hrest⟩ := exists_D4At3 S hM
  have hww : w₀ = w := involution_unique3 hw₀ hwM
  subst hww
  have hout := outerSet_eq_compMembers3 hΩ hex hw₀ hM hP1 hO3 (single_class_of_mem3 hM) D hk hrest
  have hMc : M ∈ centralizingMembers Ω {w₀} := ⟨hM, isSubnormal_le hw₀.subnormal⟩
  have hK'c : K' ∈ centralizingMembers Ω {w₀} := ⟨hK', isSubnormal_le hwK.subnormal⟩
  obtain ⟨j, hj, -⟩ := exists_unique_comp3 hΩ hex hP1 hO3 D hK'c
  obtain ⟨j', hj', -⟩ := exists_unique_comp3 hΩ hex hP1 hO3 D hMc
  by_cases hjj : j = j'
  · subst hjj
    have hji : j ≠ i₁ := by
      rintro rfl
      have hMo : M ∈ outerSet Ω M := hout ▸ hj'
      exact hMo.2 rfl
    exact Or.inl (eq_of_mem_compMembers_a13 hΩ hex hP1 hO3 (hrest j hji) hj hj')
  · exact Or.inr (commutes_of_ne_comp3 hΩ hex hP1 hO3 D hjj hj hj')

theorem centralizes_of_exact_of_comm_mem_oddCoreIn3 (S : D4Ctx3 G K z a) {a₀ : G}
    {X : Subgroup G} (hX : X ∈ conjClass3 K) (hXC : X ≤ Subgroup.centralizer ({a₀} : Set G))
    {zX : G} (hzX : IsClassicalMember3 X zX) {g : G} (hgz : g * zX * g⁻¹ = zX)
    (hcomm : ∀ y ∈ X, g * y * g⁻¹ * y⁻¹ ∈ oddCoreIn (Subgroup.centralizer ({a₀} : Set G))) :
    ∀ y ∈ X, g * y = y * g := by
  intro y hy
  have hΩ : InClass3 (conjClass3 K) := S.setup.inClass
  obtain ⟨hex, -⟩ := S.setup.setup
  have hbot := Balance.Theorem5.exact_inf_oddCoreIn_eq_bot hex hX hXC
  have hgXΩ : conjSub g X ∈ conjClass3 K := hΩ.conjInvariant g X hX
  have hz'' : IsClassicalMember3 (conjSub g X) zX := by
    have := hzX.conj g
    rwa [hgz] at this
  rcases members_eq_or_commute3 S hX hgXΩ hzX hz'' with heq | hc
  · have h1 : g * y * g⁻¹ ∈ X := heq ▸ conj_mem_conjSub hy
    have h2 : g * y * g⁻¹ * y⁻¹ ∈ X ⊓ oddCoreIn (Subgroup.centralizer ({a₀} : Set G)) :=
      ⟨Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hy), hcomm y hy⟩
    rw [hbot, Subgroup.mem_bot] at h2
    calc g * y = g * y * g⁻¹ * y⁻¹ * y * g := by group
      _ = y * g := by rw [h2]; group
  · exfalso
    obtain ⟨k₁, hk₁, k₂, hk₂, hk⟩ := exists_commutator_eq_involution3 hex hX hzX
    have hcm := hcomm k₁ hk₁
    have hconj := conj_mem_oddCoreIn (hXC hk₂) hcm
    have h2 := hc _ (conj_mem_conjSub hk₁) k₂ hk₂
    have h3 : (g * k₁ * g⁻¹)⁻¹ * k₂ * (g * k₁ * g⁻¹) = k₂ := by
      calc _ = (g * k₁ * g⁻¹)⁻¹ * (k₂ * (g * k₁ * g⁻¹)) := by group
        _ = (g * k₁ * g⁻¹)⁻¹ * ((g * k₁ * g⁻¹) * k₂) := by rw [h2]
        _ = k₂ := by group
    have e : k₁ * k₂ * k₁⁻¹ * k₂⁻¹ =
        (g * k₁ * g⁻¹ * k₁⁻¹)⁻¹ * (k₂ * (g * k₁ * g⁻¹ * k₁⁻¹) * k₂⁻¹) := by
      calc k₁ * k₂ * k₁⁻¹ * k₂⁻¹
          = k₁ * ((g * k₁ * g⁻¹)⁻¹ * k₂ * (g * k₁ * g⁻¹)) * k₁⁻¹ * k₂⁻¹ := by rw [h3]
        _ = _ := by group
    have hzO : zX ∈ oddCoreIn (Subgroup.centralizer ({a₀} : Set G)) := by
      rw [← hk, e]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hcm) hconj
    have hz2 : zX * zX = 1 := mul_self_of_isClassicalMember3 hzX
    have hz4 : zX ^ 4 = 1 := by
      calc zX ^ 4 = (zX * zX) * (zX * zX) := by
            simp only [pow_succ, pow_zero, one_mul, mul_assoc]
        _ = 1 := by rw [hz2, one_mul]
    have hz1 := eq_one_of_mem_oddCoreIn_of_pow_four hzO hz4
    have h2' := hzX.orderOf_eq_two
    rw [hz1, orderOf_one] at h2'
    omega

end LemmaZ

section Main

variable {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G} {ι : Type}

local notation "Ω₀" => conjClass3 K

theorem not_mem_comp_of_outer3 (S : D4Ctx3 G K z 4) {N : Subgroup G}
    (hN : N ∈ conjClass3 K) {z₀ : G} (hz₀ : IsClassicalMember3 N z₀) {u : G}
    (D : LieSystemData3 ι (locQuot (conjClass3 K) u) (locFamily (conjClass3 K) u)) {i : ι}
    (hNi : N ∈ compMembers3 (conjClass3 K) u D i)
    (H1 : ∀ L ∈ outerSet (conjClass3 K) N, L ≤ Subgroup.centralizer ({u} : Set G))
    (H3 : ∃ T ∈ conjClass3 K, cnbhd (conjClass3 K) T = cnbhd (conjClass3 K) N ∧
      ∃ g ∈ T, u * g ≠ g * u)
    {M' : Subgroup G} (hM' : M' ∈ outerSet (conjClass3 K) N) :
    M' ∉ compMembers3 (conjClass3 K) u D i := by
  classical
  intro hM'i
  have hΩ : InClass3 Ω₀ := S.setup.inClass
  obtain ⟨hex, -⟩ := S.setup.setup
  have hM'Ω' : M' ∈ Ω₀ := hM'.1.1
  have hNM' : N ∈ outerSet Ω₀ M' := mem_outerSet_symm hN hM'
  have hθ : outerGen Ω₀ N ≤ locLayer Ω₀ u :=
    iSup₂_le fun L hL => le_centralizingLayer ⟨hL.1.1, H1 L hL⟩
  have hall : ∀ L ∈ outerSet Ω₀ N, L ∈ compMembers3 Ω₀ u D i := by
    intro L hL
    obtain ⟨y, hy, hyL⟩ := exists_conj_of_shape3 S hN hM' hL
    rw [← hyL]
    exact conjSub_mem_compMembers_of_mem_layer3 hΩ.conjInvariant hM'i (hθ hy)
  obtain ⟨T₂, T₃, T₄, h23, h24, h34, h2M, h3M, h4M, hT⟩ := exists_three_twins3 S hM'Ω'
  have hTmem : ∀ T, (T = T₂ ∨ T = T₃ ∨ T = T₄) →
      T ∈ Ω₀ ∧ cnbhd Ω₀ T = cnbhd Ω₀ M' := fun T h => (hT T).mpr (Or.inr h)
  have hTout : ∀ T, (T = T₂ ∨ T = T₃ ∨ T = T₄) → T ∈ outerSet Ω₀ N := fun T h =>
    twin_mem_outerSet (hTmem T h).1 (hTmem T h).2 hNM'
  have h2' : T₂ = T₂ ∨ T₂ = T₃ ∨ T₂ = T₄ := Or.inl rfl
  have h3' : T₃ = T₂ ∨ T₃ = T₃ ∨ T₃ = T₄ := Or.inr (Or.inl rfl)
  have h4' : T₄ = T₂ ∨ T₄ = T₃ ∨ T₄ = T₄ := Or.inr (Or.inr rfl)
  have hct : ∀ {T T'}, (T = T₂ ∨ T = T₃ ∨ T = T₄) → (T' = T₂ ∨ T' = T₃ ∨ T' = T₄) → T ≠ T' →
      Commutes T T' := fun hT1 hT2 hne =>
    commutes_of_twins (hTmem _ hT1).1 (hTmem _ hT1).2 (hTmem _ hT2).2 hne
  have hT2 := hall T₂ (hTout T₂ h2')
  have hT3 := hall T₃ (hTout T₃ h3')
  have hT4 := hall T₄ (hTout T₄ h4')
  rcases D.valid i with ⟨t, n, hft, hadm, hk⟩ | hk | hk
  ·
    obtain ⟨hG2, hD4⟩ := tag3_ne_of_commuting_triple hΩ hex D hT2 hT3 hT4 (hct h2' h3' h23)
      (hct h2' h4' h24) (hct h3' h4' h34) hadm hk
    have hsc := singleClass_of_kind hk hft hadm hG2 hD4
    obtain ⟨RN, hRN⟩ := exists_corr_left_u hΩ hex D hNi
    obtain ⟨RM, hRM⟩ := exists_corr_left_u hΩ hex D hM'i
    obtain ⟨g, hg⟩ := hsc RN hRN.2.1 RM hRM.2.1
    obtain ⟨ĝ, hĝ⟩ := QuotientGroup.mk_surjective (D.hom i g)
    have hĝY : (ĝ : G) ∈ locLayer Ω₀ u := ĝ.2
    have hK₁c : conjSub (ĝ : G) N ∈ compMembers3 Ω₀ u D i :=
      conjSub_mem_compMembers_of_mem_layer3 hΩ.conjInvariant hNi hĝY
    have himg1 : locImg Ω₀ u (conjSub (ĝ : G) N) = locImg Ω₀ u M' := by
      rw [Gaps.locImg_conjSub_layer N ĝ, hRN.2.2, show locMk Ω₀ u ĝ = D.hom i g from hĝ, hRM.2.2,
        hg]
      unfold conjSub
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
      ext a
      simp
    obtain ⟨zM, hzM⟩ := hΩ.classical M' hM'Ω'
    have hz₁ : IsClassicalMember3 (conjSub (ĝ : G) N) ((ĝ : G) * z₀ * (ĝ : G)⁻¹) := hz₀.conj ĝ
    have hz₁Y : (ĝ : G) * z₀ * (ĝ : G)⁻¹ ∈ locLayer Ω₀ u :=
      le_centralizingLayer hK₁c.1 hz₁.mem
    have hzMY : zM ∈ locLayer Ω₀ u := le_centralizingLayer hM'i.1 hzM.mem
    have heq := locMk_eq_of_involutions3 hΩ hex hK₁c.1 hM'i.1 himg1 hz₁ hzM hz₁Y hzMY
    have hz₁sq := mul_self_of_isClassicalMember3 hz₁
    have hzMsq := mul_self_of_isClassicalMember3 hzM
    have hzMi : zM⁻¹ = zM := inv_eq_of_mul_eq_one_right hzMsq
    have hmemO : (⟨zM, hzMY⟩⁻¹ * ⟨(ĝ : G) * z₀ * (ĝ : G)⁻¹, hz₁Y⟩ : ↥(locLayer Ω₀ u)) ∈
        classicalInvolutionOddCore ↥(locLayer Ω₀ u) := QuotientGroup.eq.mp heq.symm
    have hn : zM * ((ĝ : G) * z₀ * (ĝ : G)⁻¹) ∈ oddCoreIn (locLayer Ω₀ u) :=
      ⟨_, hmemO, by simp [hzMi]⟩
    obtain ⟨o, ho, hoeq⟩ := DeltaClosure.exists_conj_of_mul_mem hz₁sq hzMsq
      (odd_card_oddCoreIn (locLayer Ω₀ u)) hn
    have hoY : o ∈ locLayer Ω₀ u := oddCoreIn_le _ ho
    have hoO : (⟨o, hoY⟩ : ↥(locLayer Ω₀ u)) ∈ classicalInvolutionOddCore ↥(locLayer Ω₀ u) := by
      obtain ⟨o', ho', hoo'⟩ := ho
      have : o' = ⟨o, hoY⟩ := Subtype.ext hoo'
      rw [← this]
      exact ho'
    have hK₂c := conjSub_mem_compMembers_of_mem_layer3 hΩ.conjInvariant hK₁c hoY
    have himg2 : locImg Ω₀ u (conjSub o (conjSub (ĝ : G) N)) =
        locImg Ω₀ u (conjSub (ĝ : G) N) := by
      rw [Gaps.locImg_conjSub_layer _ ⟨o, hoY⟩]
      have h1 : locMk Ω₀ u ⟨o, hoY⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr hoO
      rw [h1]
      ext a
      simp
    have hz₂ : IsClassicalMember3 (conjSub o (conjSub (ĝ : G) N)) zM := by
      have := hz₁.conj o
      rwa [← hoeq] at this
    rcases members_eq_or_commute3 S hM'Ω' hK₂c.1.1 hzM hz₂ with hK₂M | hcomm
    ·
      have hM'eq : M' = conjSub (o * (ĝ : G)) N := by
        rw [conjSub_mul]
        exact hK₂M.symm
      have hcY : o * (ĝ : G) ∈ locLayer Ω₀ u := (locLayer Ω₀ u).mul_mem hoY hĝY
      have hcC : o * (ĝ : G) ∈ Subgroup.centralizer ({u} : Set G) :=
        centralizingLayer_le_centralizer Ω₀ {u} hcY
      obtain ⟨T, hTΩ, hTN, g₀, hg₀T, hg₀⟩ := H3
      have hTM' : T ∈ outerSet Ω₀ M' := twin_mem_outerSet hTΩ hTN hM'
      have hTX : T ≤ outerGen Ω₀ M' := le_outerGen hTM'
      rw [hM'eq, outerGen_conj hΩ.conjInvariant (o * (ĝ : G)) N] at hTX
      have hg₀' := hTX hg₀T
      rw [mem_conjSub_iff] at hg₀'
      have hΘ : outerGen Ω₀ N ≤ Subgroup.centralizer ({u} : Set G) := iSup₂_le fun L hL => H1 L hL
      have hX : Commute u ((o * (ĝ : G))⁻¹ * g₀ * (o * (ĝ : G))) :=
        (Subgroup.mem_centralizer_singleton_iff.mp (hΘ hg₀')).symm
      have hcu : Commute u (o * (ĝ : G)) := (Subgroup.mem_centralizer_singleton_iff.mp hcC).symm
      have e : g₀ = (o * (ĝ : G)) * ((o * (ĝ : G))⁻¹ * g₀ * (o * (ĝ : G))) *
          (o * (ĝ : G))⁻¹ := by group
      apply hg₀
      rw [e]
      exact ((hcu.mul_right hX).mul_right hcu.inv_right).eq
    · exfalso
      refine locImg_not_commutes_u hΩ hex hM'i.1 ?_
      intro a ha b hb
      have ha' : a ∈ locImg Ω₀ u (conjSub o (conjSub (ĝ : G) N)) := by
        rw [himg2, himg1]
        exact ha
      obtain ⟨a₀, ha₀, rfl⟩ := ha'
      obtain ⟨b₀, hb₀, rfl⟩ := hb
      show locMk Ω₀ u a₀ * locMk Ω₀ u b₀ = locMk Ω₀ u b₀ * locMk Ω₀ u a₀
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact hcomm _ (Subgroup.mem_subgroupOf.mp ha₀) _ (Subgroup.mem_subgroupOf.mp hb₀)
  ·
    exfalso
    have hrange : ∀ T ∈ compMembers3 Ω₀ u D i, locImg Ω₀ u T = (D.hom i).range := by
      intro T hT
      obtain ⟨R, hR⟩ := exists_corr_left_u hΩ hex D hT
      rw [hR.2.2, eq_top_of_mem_fund_sl23 hk hR.2.1, Subgroup.map_top]
    refine locImg_not_commutes_u hΩ hex hT2.1 ?_
    have hc := commutes_locImg_of_commutes (x := u) (Ω := Ω₀) (hct h2' h3' h23)
    rwa [(hrange T₃ hT3).trans (hrange T₂ hT2).symm] at hc
  ·
    exfalso
    obtain ⟨R₂, hR₂⟩ := exists_corr_left_u hΩ hex D hT2
    obtain ⟨R₃, hR₃⟩ := exists_corr_left_u hΩ hex D hT3
    have hpc : PowCop3 (D.kind i) := hk ▸ powCop3_m11
    have hRR := commutes_partner_of_commutes_u hpc hR₂ hR₃ (hct h2' h3' h23)
    have key : ∀ c : CompData, c = CompData.m11 → ∀ R R' : Subgroup c.G, R ∈ c.fund →
        R' ∈ c.fund → ¬ Commutes R R' := by
      rintro c rfl R R' hR hR'
      exact not_commutes_of_mem_m11Class hR hR'
    exact key _ hk R₂ R₃ hR₂.2.1 hR₃.2.1 hRR

end Main

end CFSG.ClassicalInvolution.Q3.Q3W.EX
