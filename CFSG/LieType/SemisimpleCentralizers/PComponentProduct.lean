module

public import CFSG.LocalAnalysis.StandardType.GGNbrBalanceBasic
public import CFSG.GroupTheory.PerfectLeOfPGroupQuotient

public section

namespace CFSG.LieType.SemisimpleCentralizers

open CFSG.Assembly

variable {G : Type*} [Group G] [Finite G] {p : ℕ}

theorem le_of_largeEvenPComponent_of_isSolvable_quotient {Y E C : Subgroup G}
    (hEn : (E.subgroupOf Y).Normal) (hsolv : IsSolvable (Y ⧸ E.subgroupOf Y))
    (hC : LargeEvenPComponent p Y C) : C ≤ E := by
  obtain ⟨hCY, hCl⟩ := (CFSG.StandardType.largeEvenPComponent_iff_lBalance p Y C).1 hC
  have hCcomm : ⁅C, C⁆ = C :=
    Subgroup.isPerfect_iff.mp (CFSG.ComponentClassification.LBalance.pComponent_perfect p Y C hCl)
  have hCsub : ⁅C.subgroupOf Y, C.subgroupOf Y⁆ = C.subgroupOf Y := by
    apply Subgroup.map_injective Y.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hCY, hCcomm]
  haveI : (E.subgroupOf Y).Normal := hEn
  haveI : Group.IsSolvable (Y ⧸ E.subgroupOf Y) := hsolv
  have hle := Subgroup.le_of_commutator_eq_self_of_isSolvable_quotient
    (M := E.subgroupOf Y) (H := C.subgroupOf Y) hCsub
  intro c hc
  have hcY : (⟨c, hCY hc⟩ : Y) ∈ C.subgroupOf Y := by
    exact Subgroup.mem_subgroupOf.mpr hc
  exact Subgroup.mem_subgroupOf.mp (hle hcY)

theorem exists_quasisimple_factor_of_commuting_product {Y E : Subgroup G} {ι : Type*} [Finite ι]
    (L : ι → Subgroup G)
    (hEY : E ≤ Y) (hEn : (E.subgroupOf Y).Normal)
    (hsolv : IsSolvable (Y ⧸ E.subgroupOf Y))
    (hE : E = ⨆ i, L i)
    (hcomm : ∀ i j, i ≠ j → ∀ x ∈ L i, ∀ y ∈ L j, Commute x y)
    (hL : ∀ i, CFSG.Assembly.IsQuasisimple ↥(L i) ∨ IsSolvable ↥(L i))
    {C : Subgroup G} (hC : LargeEvenPComponent p Y C) :
    ∃ i, CFSG.Assembly.IsQuasisimple ↥(L i) ∧
      CFSG.Assembly.IsSubnormal (L i) Y ∧
      CFSG.ComponentClassification.LBalance.quotientImage p Y C =
        CFSG.ComponentClassification.LBalance.quotientImage p Y (L i) := by
  classical
  let Q := ↥Y ⧸ CFSG.pPrimeCore p ↥Y
  let π : ↥Y →* Q := QuotientGroup.mk' (CFSG.pPrimeCore p ↥Y)
  let M : Subgroup Q := CFSG.ComponentClassification.LBalance.quotientImage p Y C
  let Mi : ι → Subgroup Q := fun i =>
    CFSG.ComponentClassification.LBalance.quotientImage p Y (L i)
  haveI : Finite Q := by dsimp only [Q]; infer_instance
  obtain ⟨hCY, hCl⟩ := (CFSG.StandardType.largeEvenPComponent_iff_lBalance p Y C).1 hC
  obtain ⟨-, hCimgO, -⟩ :=
    (CFSG.ComponentClassification.LBalance.pComponent_iff_minimal_image p Y C hCY).1 hCl
  have hMqO : CFSG.Open.IsQuasisimple ↥M := hCimgO.2.2
  have hMnt : Nontrivial ↥M :=
    CFSG.ComponentClassification.Quasisimple.nontrivial hMqO
  have hMne : M ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot M).mp hMnt
  have hMperf : ⁅M, M⁆ = M := by
    refine CFSG.StandardType.commutator_self_eq_of_isQuasisimple ?_
    exact hMqO
  have hMnsolv : ¬ Group.IsSolvable ↥M := by
    letI : Nontrivial ↥M := hMnt
    letI : Group.IsPerfect ↥M := ⟨hMqO.1⟩
    exact Group.IsPerfect.not_isSolvable ↥M
  have hMcompA : CFSG.Assembly.IsComponentOf M ⊤ :=
    (CFSG.Assembly.isComponentOf_iff_open (L := M) (K := ⊤)).mpr hCimgO
  have hLiE : ∀ i, L i ≤ E := fun i =>
    (le_iSup (fun i => L i) i).trans hE.ge
  have hLiNormE : ∀ i, ((L i).subgroupOf E).Normal := by
    intro i
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer (hLiE i)).mpr ?_
    rw [hE]
    refine iSup_le fun j => ?_
    by_cases hji : j = i
    · subst hji
      exact Subgroup.le_normalizer
    · refine (show L j ≤ Subgroup.centralizer ((L i : Subgroup G) : Set G) from ?_).trans
        (Subgroup.centralizer_le_normalizer _)
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact (hcomm i j (Ne.symm hji) x hx y hy).eq
  have hEsnY : CFSG.Assembly.IsSubnormal E Y :=
    CFSG.Assembly.IsSubnormal.step hEY hEn (CFSG.Assembly.IsSubnormal.refl Y)
  have hLiSnY : ∀ i, CFSG.Assembly.IsSubnormal (L i) Y := fun i =>
    CFSG.Assembly.IsSubnormal.step (hLiE i) (hLiNormE i) hEsnY
  have hLiY : ∀ i, L i ≤ Y := fun i => (hLiE i).trans hEY
  let f : (i : ι) → ↥(L i) →* ↥(Mi i) := fun i =>
    ((QuotientGroup.mk' (CFSG.pPrimeCore p ↥Y)).comp
      (Subgroup.inclusion (hLiY i))).codRestrict (Mi i) fun x =>
        Subgroup.mem_map.mpr
          ⟨⟨x, hLiY i x.2⟩, Subgroup.mem_subgroupOf.mpr x.2, rfl⟩
  have hf : ∀ i, Function.Surjective (f i) := by
    intro i q
    obtain ⟨y, hy, hyq⟩ := Subgroup.mem_map.mp q.2
    refine ⟨⟨y, Subgroup.mem_subgroupOf.mp hy⟩, Subtype.ext ?_⟩
    exact hyq
  have hMiSub : ∀ i, CFSG.Assembly.IsSubnormal (Mi i) ⊤ := by
    intro i
    have hsub : ((L i).subgroupOf Y).IsSubnormal :=
      CFSG.Assembly.IsSubnormal.subgroupOf (hLiSnY i)
    have hmap : (Mi i).IsSubnormal := by
      simpa only [Mi, CFSG.ComponentClassification.LBalance.quotientImage] using
        hsub.map (QuotientGroup.mk'_surjective (CFSG.pPrimeCore p ↥Y))
    exact CFSG.Assembly.IsSubnormal.top_iff.mpr hmap
  have hMiSolv : ∀ i, Group.IsSolvable ↥(L i) → Group.IsSolvable ↥(Mi i) := by
    intro i hsolvLi
    letI : Group.IsSolvable ↥(L i) := hsolvLi
    exact Group.isSolvable_of_surjective (f := f i) (hf i)
  have hMiq_of_ne_bot : ∀ i, CFSG.Assembly.IsQuasisimple ↥(L i) → Mi i ≠ ⊥ →
      CFSG.Assembly.IsQuasisimple ↥(Mi i) := by
    intro i hq hne
    have hker : (f i).ker ≠ ⊤ := by
      intro htop
      have hrangeBot : (f i).range = ⊥ := by
        rw [eq_bot_iff]
        rintro _ ⟨x, rfl⟩
        have hx : x ∈ (f i).ker := by rw [htop]; exact Subgroup.mem_top x
        exact MonoidHom.mem_ker.mp hx
      have hrangeTop : (f i).range = ⊤ := MonoidHom.range_eq_top.mpr (hf i)
      have hbotTop : (⊥ : Subgroup ↥(Mi i)) = ⊤ := by rw [← hrangeBot, hrangeTop]
      apply hne
      rw [← le_bot_iff]
      intro x hx
      have hxbot : (⟨x, hx⟩ : ↥(Mi i)) ∈ (⊥ : Subgroup ↥(Mi i)) := by
        rw [hbotTop]
        exact Subgroup.mem_top _
      exact Subgroup.mem_bot.mpr (by
        simpa using congrArg Subtype.val (Subgroup.mem_bot.mp hxbot))
    have hrangeq : CFSG.Open.IsQuasisimple ↥((f i).range) :=
      CFSG.ComponentClassification.Quasisimple.range_quasisimple_of_ker_ne_top
        hq (f i) hker
    have hrangeTop : (f i).range = ⊤ := MonoidHom.range_eq_top.mpr (hf i)
    rw [hrangeTop] at hrangeq
    exact (CFSG.Assembly.IsQuasisimple.congr Subgroup.topEquiv).mp hrangeq
  have key : ∀ i, (M = Mi i ∧ CFSG.Assembly.IsQuasisimple ↥(L i)) ∨ ⁅M, Mi i⁆ = ⊥ := by
    intro i
    rcases CFSG.StandardType.isComponentOf_le_or_commutator_eq_bot
      (G := Q) hMcompA (hMiSub i) with hle | hcommM
    · rcases hL i with hq | hsolvLi
      · have hMi_ne_bot : Mi i ≠ ⊥ := by
          intro hbot
          exact hMne (le_bot_iff.mp (hle.trans (le_of_eq hbot)))
        have hMiq := hMiq_of_ne_bot i hq hMi_ne_bot
        have hMicomp : CFSG.Assembly.IsComponentOf (Mi i) ⊤ :=
          ⟨le_top, hMiSub i, hMiq⟩
        have hMcompO : CFSG.Open.IsComponentOf M ⊤ :=
          (CFSG.Assembly.isComponentOf_iff_open (L := M) (K := ⊤)).mp hMcompA
        have hMicompO : CFSG.Open.IsComponentOf (Mi i) ⊤ :=
          (CFSG.Assembly.isComponentOf_iff_open (L := Mi i) (K := ⊤)).mp hMicomp
        exact Or.inl ⟨CFSG.ComponentClassification.LocalComponents.eq_of_le M (Mi i)
          hMcompO hMicompO hle, hq⟩
      · exfalso
        letI : Group.IsSolvable ↥(Mi i) := hMiSolv i hsolvLi
        exact hMnsolv (Group.isSolvable_of_isSolvable_injective
          (Subgroup.inclusion_injective hle))
    · exact Or.inr hcommM
  have hEimg : CFSG.ComponentClassification.LBalance.quotientImage p Y E = ⨆ i, Mi i := by
    have hEsub : E.subgroupOf Y = ⨆ i, (L i).subgroupOf Y := by
      rw [hE]
      exact CFSG.LieType.Steinberg.iSup_subgroupOf hLiY
    simp only [Mi, CFSG.ComponentClassification.LBalance.quotientImage]
    rw [hEsub, Subgroup.map_iSup]
  have hMleN : M ≤ ⨆ i, Mi i := by
    have hCLE : C ≤ E := le_of_largeEvenPComponent_of_isSolvable_quotient hEn hsolv hC
    have hsub : C.subgroupOf Y ≤ E.subgroupOf Y := Subgroup.subgroupOf_mono Y hCLE
    have hmap := Subgroup.map_mono (f := π) hsub
    rw [← hEimg]
    simpa only [M, CFSG.ComponentClassification.LBalance.quotientImage] using hmap
  have hex : ∃ i, M = Mi i ∧ CFSG.Assembly.IsQuasisimple ↥(L i) := by
    by_contra hno
    push Not at hno
    have hcommAll : ∀ i, ⁅M, Mi i⁆ = ⊥ := by
      intro i
      rcases key i with hfirst | hcommM
      · exact absurd hfirst.2 (hno i hfirst.1)
      · exact hcommM
    have hcent : M ≤ Subgroup.centralizer ((⨆ i, Mi i : Subgroup Q) : Set Q) := by
      refine CFSG.subgroup_le_centralizer_iSup_of_le_centralizer (fun i => Mi i) fun i => ?_
      exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hcommAll i))
    have hcentM : M ≤ Subgroup.centralizer (M : Set Q) :=
      hcent.trans (Subgroup.centralizer_le hMleN)
    have hMbot : ⁅M, M⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hcentM
    have hMeqBot : M = ⊥ := by
      rw [← hMperf]
      exact hMbot
    exact hMne hMeqBot
  obtain ⟨i, hi, hq⟩ := hex
  exact ⟨i, hq, hLiSnY i, hi⟩

theorem eq_of_largeEvenPComponent_of_quotientImage_eq {Y J C : Subgroup G}
    (hJq : CFSG.Assembly.IsQuasisimple ↥J)
    (hJs : CFSG.Assembly.IsSubnormal J Y)
    (himg : CFSG.ComponentClassification.LBalance.quotientImage p Y C =
      CFSG.ComponentClassification.LBalance.quotientImage p Y J)
    (hC : LargeEvenPComponent p Y C) : C = J := by
  let π : ↥Y →* ↥Y ⧸ CFSG.pPrimeCore p ↥Y :=
    QuotientGroup.mk' (CFSG.pPrimeCore p ↥Y)
  have hCY : C ≤ Y := hC.1
  have hCsY : CFSG.Assembly.IsSubnormal C Y := hC.2.1
  have hJY : J ≤ Y := hJs.le
  have hJcomp : CFSG.Assembly.IsComponentOf J Y := ⟨hJY, hJs, hJq⟩
  rcases CFSG.StandardType.isComponentOf_le_or_commutator_eq_bot (G := G) hJcomp hCsY with
    hJC | hcommJC
  · obtain ⟨-, hCl⟩ := (CFSG.StandardType.largeEvenPComponent_iff_lBalance p Y C).1 hC
    obtain ⟨-, -, hCmin⟩ :=
      (CFSG.ComponentClassification.LBalance.pComponent_iff_minimal_image p Y C hCY).1 hCl
    have hJsO : CFSG.Open.IsSubnormal J Y := (CFSG.Assembly.isSubnormal_iff_open).mp hJs
    have heq : CFSG.ComponentClassification.LBalance.quotientImage p Y J =
        CFSG.ComponentClassification.LBalance.quotientImage p Y C := himg.symm
    exact (hCmin J hJC hJsO heq).symm
  · exfalso
    obtain ⟨-, hCl⟩ := (CFSG.StandardType.largeEvenPComponent_iff_lBalance p Y C).1 hC
    have hMq : CFSG.Open.IsQuasisimple ↥
        (CFSG.ComponentClassification.LBalance.quotientImage p Y C) :=
      (CFSG.ComponentClassification.LBalance.pComponent_image p Y C hCl).2.2
    have hMnt : Nontrivial ↥
        (CFSG.ComponentClassification.LBalance.quotientImage p Y C) :=
      CFSG.ComponentClassification.Quasisimple.nontrivial hMq
    have hMne : CFSG.ComponentClassification.LBalance.quotientImage p Y C ≠ ⊥ :=
      (Subgroup.nontrivial_iff_ne_bot _).mp hMnt
    have hMperf : ⁅CFSG.ComponentClassification.LBalance.quotientImage p Y C,
        CFSG.ComponentClassification.LBalance.quotientImage p Y C⁆ =
        CFSG.ComponentClassification.LBalance.quotientImage p Y C := by
      refine CFSG.StandardType.commutator_self_eq_of_isQuasisimple ?_
      exact hMq
    have hJcentC : J ≤ Subgroup.centralizer (C : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommJC
    have hMJ_MC : ⁅CFSG.ComponentClassification.LBalance.quotientImage p Y J,
        CFSG.ComponentClassification.LBalance.quotientImage p Y C⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.mp ha
      obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hb
      change π c * π j = π j * π c
      have hjJ : (j : G) ∈ J := Subgroup.mem_subgroupOf.mp hj
      have hcC : (c : G) ∈ C := Subgroup.mem_subgroupOf.mp hc
      have hcj : (c : G) * (j : G) = (j : G) * (c : G) :=
        (Subgroup.mem_centralizer_iff.mp (hJcentC hjJ)) (c : G) hcC
      have hY : c * j = j * c := Subtype.ext hcj
      rw [← map_mul, ← map_mul]
      exact congrArg π hY
    have hMbot : ⁅CFSG.ComponentClassification.LBalance.quotientImage p Y C,
        CFSG.ComponentClassification.LBalance.quotientImage p Y C⁆ = ⊥ := by
      simpa only [himg] using hMJ_MC
    have hMeqBot : CFSG.ComponentClassification.LBalance.quotientImage p Y C = ⊥ := by
      rw [← hMperf]
      exact hMbot
    exact hMne hMeqBot

theorem largeEvenPComponent_eq_of_commuting_product {Y E : Subgroup G} {ι : Type*} [Finite ι]
    (L : ι → Subgroup G)
    (hEY : E ≤ Y) (hEn : (E.subgroupOf Y).Normal)
    (hsolv : IsSolvable (Y ⧸ E.subgroupOf Y))
    (hE : E = ⨆ i, L i)
    (hcomm : ∀ i j, i ≠ j → ∀ x ∈ L i, ∀ y ∈ L j, Commute x y)
    (hL : ∀ i, CFSG.Assembly.IsQuasisimple ↥(L i) ∨ IsSolvable ↥(L i))
    {C : Subgroup G} (hC : LargeEvenPComponent p Y C) :
    ∃ i, C = L i ∧ CFSG.Assembly.IsQuasisimple ↥(L i) := by
  obtain ⟨i, hq, hsn, himg⟩ :=
    exists_quasisimple_factor_of_commuting_product L hEY hEn hsolv hE hcomm hL hC
  exact ⟨i, eq_of_largeEvenPComponent_of_quotientImage_eq hq hsn himg hC, hq⟩

end CFSG.LieType.SemisimpleCentralizers

end
