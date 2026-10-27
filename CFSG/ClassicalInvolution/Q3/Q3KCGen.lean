module

public import CFSG.ClassicalInvolution.Q3.Q3KBTriple
public import CFSG.ClassicalInvolution.Q3.Q3NGBoot

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3KC

open CFSG.Open CFSG.Assembly.Dichotomy CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Q3.Q3KB
  CFSG.ClassicalInvolution.Q3.Q3NG


section Defs

variable {G : Type} [Group G]

@[expose] def fourCentralizerJoin (Ω : Set (Subgroup G)) (A : Subgroup G) (a : G) : Subgroup G :=
  ⨆ F ∈ signalizerFunctorEk 2 2 A, Subgroup.centralizer (F : Set G) ⊓ centralizingLayer Ω {a}

@[expose] def fourCentralizerImage (Ω : Set (Subgroup G)) (A : Subgroup G) (a : G) :
    Subgroup (↥(centralizingLayer Ω {a}) ⧸ classicalInvolutionOddCore ↥(centralizingLayer Ω {a})) :=
  ((fourCentralizerJoin Ω A a).subgroupOf (centralizingLayer Ω {a})).map
    (QuotientGroup.mk' (classicalInvolutionOddCore ↥(centralizingLayer Ω {a})))

end Defs

section Lift

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {A : Subgroup G}

theorem mem_fourCentralizerImage_of_centralizes (hA : IsElemAbelian 2 A) {a : G} (haA : a ∈ A)
    (ha1 : a ≠ 1) (hAY : A ≤ centralizingLayer Ω {a}) {f : G} (hfA : f ∈ A) (hf1 : f ≠ 1)
    (hfa : f ≠ a)
    {q : ↥(centralizingLayer Ω {a}) ⧸ classicalInvolutionOddCore ↥(centralizingLayer Ω {a})}
    (hq : QuotientGroup.mk' (classicalInvolutionOddCore ↥(centralizingLayer Ω {a}))
        ⟨f, hAY hfA⟩ * q = q * QuotientGroup.mk'
          (classicalInvolutionOddCore ↥(centralizingLayer Ω {a})) ⟨f, hAY hfA⟩) :
    q ∈ fourCentralizerImage Ω A a := by
  have hf2 : f * f = 1 := Q3C.elem_sq hA hfA
  have ha2 : a * a = 1 := Q3C.elem_sq hA haA
  obtain ⟨y, hyf, hyq⟩ := Q3Y2.centralizer_mk_le (centralizingLayer Ω {a}) (hAY hfA) hf2 hq
  have hcomm : a * f = f * a := Q3C.elem_comm hA haA hfA
  have hF4 := card_closure_pair_eq_four ha2 hf2 ha1 hf1 hfa.symm hcomm
  have hFA : Subgroup.closure ({a, f} : Set G) ≤ A := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    exacts [haA, hfA]
  have hF : Subgroup.closure ({a, f} : Set G) ∈ signalizerFunctorEk 2 2 A :=
    ⟨hFA, by rw [hF4]; norm_num⟩
  have hya : (y : G) * a = a * y :=
    Subgroup.mem_centralizer_singleton_iff.mp (centralizingLayer_le_centralizer Ω {a} y.2)
  have hyF : (y : G) ∈ Subgroup.centralizer (Subgroup.closure ({a, f} : Set G) : Set G) := by
    rw [Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
    intro x hx
    rcases hx with rfl | hx
    · exact hya.symm
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact hyf.symm
  have hyJ : (y : G) ∈ fourCentralizerJoin Ω A a :=
    (le_iSup₂ (f := fun (F : Subgroup G) (_ : F ∈ signalizerFunctorEk 2 2 A) =>
      Subgroup.centralizer (F : Set G) ⊓ centralizingLayer Ω {a}) _ hF) ⟨hyF, y.2⟩
  exact ⟨y, Subgroup.mem_subgroupOf.mpr hyJ, hyq⟩

end Lift

section Abstract

variable {X : Type} [Group X] {ι : Type} {Φ : Set (Subgroup X)}

theorem kind_ne_sl23_of_distinct (D : LieSystemData3 ι X Φ) {k : ι} {K J : Subgroup X}
    (hK : K ∈ Φ) (hJ : J ∈ Φ) (hne : K ≠ J) {ζ ξ : X} (hζK : ζ ∈ K) (hξJ : ξ ∈ J)
    (hζnc : ¬ ∀ q ∈ (D.hom k).range, ζ * q = q * ζ)
    (hξnc : ¬ ∀ q ∈ (D.hom k).range, ξ * q = q * ξ) : D.kind k ≠ CompData.sl23 := by
  intro hc
  have hcommc : ∀ {c d : ι}, c ≠ d → ∀ {a b : X}, a ∈ (D.hom c).range → b ∈ (D.hom d).range →
      a * b = b * a := by
    rintro c d h _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact D.commute c d h x y
  have key : ∀ {M : Subgroup X} {m : X}, M ∈ Φ → m ∈ M →
      (¬ ∀ q ∈ (D.hom k).range, m * q = q * m) → M = (D.hom k).range := by
    intro M m hM hmM hnc
    obtain ⟨i, R, hR, hMR⟩ := D.fundamental M hM
    have hik : i = k := by
      by_contra h
      refine hnc fun q hq => hcommc h ?_ hq
      rw [hMR] at hmM
      exact Subgroup.map_le_range _ _ hmM
    subst hik
    rw [hMR, fund_eq_top_of_sl23 hc R hR, ← MonoidHom.range_eq_map]
  exact hne ((key hK hζK hζnc).trans (key hJ hξJ hξnc).symm)

end Abstract

section Pair

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {A : Subgroup G}

theorem range_le_fourCentralizerImage_of_pair (hA : IsElemAbelian 2 A) {a : G} (haA : a ∈ A)
    (ha1 : a ≠ 1) (hAY : A ≤ centralizingLayer Ω {a}) {ι : Type}
    (D : LieSystemData3 ι (↥(centralizingLayer Ω {a}) ⧸
      classicalInvolutionOddCore ↥(centralizingLayer Ω {a}))
      (oddQuotientFamily (restrictFamily (centralizingMembers Ω {a})
        (centralizingLayer Ω {a}))))
    {k : ι} {K K' : Subgroup G} {w w' : G} (P : MemberPair Ω A K K' w w')
    (hw : IsClassicalMember3 K w) (hw' : IsClassicalMember3 K' w') (hwa : w ≠ a) (hw'a : w' ≠ a)
    (hww' : w * w' ≠ a)
    (hnc : ¬ ∀ q ∈ (D.hom k).range, QuotientGroup.mk'
        (classicalInvolutionOddCore ↥(centralizingLayer Ω {a})) ⟨w, hAY P.memA⟩ * q =
          q * QuotientGroup.mk' (classicalInvolutionOddCore ↥(centralizingLayer Ω {a}))
            ⟨w, hAY P.memA⟩)
    (hnc' : ¬ ∀ q ∈ (D.hom k).range, QuotientGroup.mk'
        (classicalInvolutionOddCore ↥(centralizingLayer Ω {a})) ⟨w', hAY P.memA'⟩ * q =
          q * QuotientGroup.mk' (classicalInvolutionOddCore ↥(centralizingLayer Ω {a}))
            ⟨w', hAY P.memA'⟩) :
    (D.hom k).range ≤ fourCentralizerImage Ω A a := by
  let Y : Subgroup G := centralizingLayer Ω {a}
  have hbc : ∀ {M : Subgroup G}, M ≤ Subgroup.centralizer (A : Set G) →
      M ≤ Subgroup.centralizer ({a} : Set G) := fun hM =>
    hM.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr haA))
  have hmK : K ∈ centralizingMembers Ω {a} := ⟨P.memΩ, hbc P.le⟩
  have hmK' : K' ∈ centralizingMembers Ω {a} := ⟨P.memΩ', hbc P.le'⟩
  have hKY : K ≤ Y := le_centralizingLayer hmK
  have hK'Y : K' ≤ Y := le_centralizingLayer hmK'
  have hwY : w ∈ Y := hKY P.mem
  have hw'Y : w' ∈ Y := hK'Y P.mem'
  have hwwY : w * w' ∈ Y := Y.mul_mem hwY hw'Y
  set π := QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) with hπ
  have hΦ : ∀ {M : Subgroup G}, M ∈ centralizingMembers Ω {a} →
      modOddIn Y M ∈ oddQuotientFamily (restrictFamily (centralizingMembers Ω {a}) Y) :=
    fun {M} hM => ⟨M.subgroupOf Y, ⟨M, hM, le_centralizingLayer hM, rfl⟩, rfl⟩
  have hww : w * w' = w' * w := P.comm w P.mem w' P.mem'
  have hsqww : (w * w') * (w * w') = 1 := by
    calc (w * w') * (w * w') = w * (w' * w) * w' := by group
      _ = w * (w * w') * w' := by rw [← hww]
      _ = (w * w) * (w' * w') := by group
      _ = 1 := by rw [P.sq, P.sq', one_mul]
  have hww1 : w * w' ≠ 1 := fun h => P.ne (by
    have h' : w' = w⁻¹ := eq_inv_of_mul_eq_one_right h
    exact (h'.trans (inv_eq_of_mul_eq_one_right P.sq)).symm)
  have hζmem : π ⟨w, hwY⟩ ∈ modOddIn Y K :=
    ⟨⟨w, hwY⟩, Subgroup.mem_subgroupOf.mpr P.mem, rfl⟩
  have hξmem : π ⟨w', hw'Y⟩ ∈ modOddIn Y K' :=
    ⟨⟨w', hw'Y⟩, Subgroup.mem_subgroupOf.mpr P.mem', rfl⟩
  have hζ2 : π ⟨w, hwY⟩ * π ⟨w, hwY⟩ = 1 := by
    rw [← map_mul]
    have : (⟨w, hwY⟩ : ↥Y) * ⟨w, hwY⟩ = 1 := Subtype.ext P.sq
    rw [this, map_one]
  have hξ2 : π ⟨w', hw'Y⟩ * π ⟨w', hw'Y⟩ = 1 := by
    rw [← map_mul]
    have : (⟨w', hw'Y⟩ : ↥Y) * ⟨w', hw'Y⟩ = 1 := Subtype.ext P.sq'
    rw [this, map_one]
  have hζ1 : π ⟨w, hwY⟩ ≠ 1 := Q3Y.mk_ne_one_of_involution Y hwY P.sq P.ne_one
  have hξ1 : π ⟨w', hw'Y⟩ ≠ 1 := Q3Y.mk_ne_one_of_involution Y hw'Y P.sq' P.ne_one'
  have hmul : π ⟨w * w', hwwY⟩ = π ⟨w, hwY⟩ * π ⟨w', hw'Y⟩ := by
    rw [← map_mul]
    rfl
  have hζξ : π ⟨w, hwY⟩ ≠ π ⟨w', hw'Y⟩ := by
    intro h
    apply Q3Y.mk_ne_one_of_involution Y hwwY hsqww hww1
    rw [hmul, ← h, hζ2]
  have hKK' : ∀ y ∈ modOddIn Y K, ∀ y' ∈ modOddIn Y K', y * y' = y' * y := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (P.comm x (Subgroup.mem_subgroupOf.mp hx) x'
      (Subgroup.mem_subgroupOf.mp hx'))
  have hζc : ∀ y ∈ modOddIn Y K, π ⟨w, hwY⟩ * y = y * π ⟨w, hwY⟩ := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (P.central x (Subgroup.mem_subgroupOf.mp hx)).symm
  have hξc : ∀ y ∈ modOddIn Y K', π ⟨w', hw'Y⟩ * y = y * π ⟨w', hw'Y⟩ := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (P.central' x (Subgroup.mem_subgroupOf.mp hx)).symm
  have hk : D.kind k ≠ CompData.sl23 := by
    refine kind_ne_sl23_of_distinct D (hΦ hmK) (hΦ hmK') (fun h => ?_) hζmem hξmem hnc hnc'
    have hmem := mul_mem_oddCoreIn_of_modOddIn_eq3 hw hw' hKY hK'Y h
    exact hww1 (eq_one_of_mem_of_odd_of_sq (odd_card_oddCoreIn Y) hmem hsqww)
  have hrange := range_le_of_pair D hk (hΦ hmK) (hΦ hmK') hζmem hξmem hζ2 hξ2 hζ1 hξ1 hζξ hKK'
    hζc hξc hnc hnc'
  refine hrange.trans (sup_le (sup_le ?_ ?_) ?_)
  · rintro q ⟨hq, -⟩
    exact mem_fourCentralizerImage_of_centralizes hA haA ha1 hAY P.memA P.ne_one hwa
      (Subgroup.mem_centralizer_singleton_iff.mp hq).symm
  · rintro q ⟨hq, -⟩
    exact mem_fourCentralizerImage_of_centralizes hA haA ha1 hAY P.memA' P.ne_one' hw'a
      (Subgroup.mem_centralizer_singleton_iff.mp hq).symm
  · rintro q ⟨hq, -⟩
    have hq' := Subgroup.mem_centralizer_singleton_iff.mp hq
    rw [← hmul] at hq'
    exact mem_fourCentralizerImage_of_centralizes hA haA ha1 hAY (A.mul_mem P.memA P.memA')
      hww1 hww' hq'.symm

end Pair

section Triple

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem centralizerGenerationModOTwo_of_exactTriple (hIH : LocalLieSystems3 Ω)
    {K₁ K₂ K₃ : Subgroup G} {z₁ z₂ z₃ : G} (T : ExactTriple K₁ K₂ K₃ z₁ z₂ z₃)
    (hind : z₁ * z₂ ≠ z₃) (hΩ₁ : K₁ ∈ Ω) (hΩ₂ : K₂ ∈ Ω) (hΩ₃ : K₃ ∈ Ω)
    (hz₁ : IsClassicalMember3 K₁ z₁) (hz₂ : IsClassicalMember3 K₂ z₂)
    (hz₃ : IsClassicalMember3 K₃ z₃) {a : G} (ha : a ∈ T.group) (ha1 : a ≠ 1)
    (hnc : a ∉ Subgroup.center G) : CentralizerGenerationModOTwo Ω T.group a := by
  classical
  have hA := T.isElemAbelian
  have hAY : T.group ≤ centralizingLayer Ω {a} :=
    group_le_centralizingLayer_of_exactTriple T hΩ₁ hΩ₂ hΩ₃ ha
  have hz₁A : z₁ ∈ T.group := Subgroup.subset_closure (by simp)
  have hz₂A : z₂ ∈ T.group := Subgroup.subset_closure (by simp)
  have hz₃A : z₃ ∈ T.group := Subgroup.subset_closure (by simp)
  have P12 : MemberPair Ω T.group K₁ K₂ z₁ z₂ :=
    ⟨hΩ₁, hΩ₂, T.le_centralizer₁, T.le_centralizer₂, T.mem₁, T.mem₂, hz₁A, hz₂A, T.central₁,
      T.central₂, T.comm₁₂, T.sq₁, T.sq₂, T.ne₁₂, T.ne_one₁, T.ne_one₂⟩
  have P13 : MemberPair Ω T.group K₁ K₃ z₁ z₃ :=
    ⟨hΩ₁, hΩ₃, T.le_centralizer₁, T.le_centralizer₃, T.mem₁, T.mem₃, hz₁A, hz₃A, T.central₁,
      T.central₃, T.comm₁₃, T.sq₁, T.sq₃, T.ne₁₃, T.ne_one₁, T.ne_one₃⟩
  have P23 : MemberPair Ω T.group K₂ K₃ z₂ z₃ :=
    ⟨hΩ₂, hΩ₃, T.le_centralizer₂, T.le_centralizer₃, T.mem₂, T.mem₃, hz₂A, hz₃A, T.central₂,
      T.central₃, T.comm₂₃, T.sq₂, T.sq₃, T.ne₂₃, T.ne_one₂, T.ne_one₃⟩
  have h23 : z₂ * z₃ ≠ z₁ := by
    intro h
    apply hind
    calc z₁ * z₂ = z₂ * z₁ := T.comm₁₂'
      _ = z₂ * (z₂ * z₃) := by rw [h]
      _ = (z₂ * z₂) * z₃ := by group
      _ = z₃ := by rw [T.sq₂, one_mul]
  have h13 : z₁ * z₃ ≠ z₂ := by
    intro h
    apply hind
    calc z₁ * z₂ = z₁ * (z₁ * z₃) := by rw [h]
      _ = (z₁ * z₁) * z₃ := by group
      _ = z₃ := by rw [T.sq₁, one_mul]
  obtain ⟨ι, -, ⟨D⟩⟩ := hIH {a} (fun h => hnc (h rfl))
  have hrange : ∀ i : ι, (D.hom i).range ≤ fourCentralizerImage Ω T.group a := by
    intro i
    by_cases hα : ∃ (f : G) (hfA : f ∈ T.group), f ≠ 1 ∧ f ≠ a ∧
        ∀ q ∈ (D.hom i).range, QuotientGroup.mk'
          (classicalInvolutionOddCore ↥(centralizingLayer Ω {a})) ⟨f, hAY hfA⟩ * q =
            q * QuotientGroup.mk' (classicalInvolutionOddCore ↥(centralizingLayer Ω {a}))
              ⟨f, hAY hfA⟩
    · obtain ⟨f, hfA, hf1, hfa, hall⟩ := hα
      exact fun q hq =>
        mem_fourCentralizerImage_of_centralizes hA ha ha1 hAY hfA hf1 hfa (hall q hq)
    · have key : ∀ {M M' : Subgroup G} {w w' : G}, MemberPair Ω T.group M M' w w' →
          IsClassicalMember3 M w → IsClassicalMember3 M' w' → w ≠ a → w' ≠ a → w * w' ≠ a →
          (D.hom i).range ≤ fourCentralizerImage Ω T.group a :=
        fun P hw hw' hwa hw'a hww' =>
          range_le_fourCentralizerImage_of_pair hA ha ha1 hAY D P hw hw' hwa hw'a hww'
            (fun hall => hα ⟨_, P.memA, P.ne_one, hwa, hall⟩)
            (fun hall => hα ⟨_, P.memA', P.ne_one', hw'a, hall⟩)
      by_cases e1 : a = z₁
      · exact key P23 hz₂ hz₃ (by rw [e1]; exact T.ne₁₂.symm) (by rw [e1]; exact T.ne₁₃.symm)
          (by rw [e1]; exact h23)
      by_cases e2 : a = z₂
      · exact key P13 hz₁ hz₃ (by rw [e2]; exact T.ne₁₂) (by rw [e2]; exact T.ne₂₃.symm)
          (by rw [e2]; exact h13)
      by_cases e3 : a = z₃
      · exact key P12 hz₁ hz₂ (by rw [e3]; exact T.ne₁₃) (by rw [e3]; exact T.ne₂₃)
          (by rw [e3]; exact hind)
      by_cases e4 : a = z₁ * z₂
      · exact key P13 hz₁ hz₃ (Ne.symm e1) (Ne.symm e3) (by
          rw [e4]
          intro h
          exact T.ne₂₃ (mul_left_cancel h).symm)
      · exact key P12 hz₁ hz₂ (Ne.symm e1) (Ne.symm e2) (Ne.symm e4)
  show centralizingLayer Ω {a} ≤
    oddCoreIn (centralizingLayer Ω {a}) ⊔ fourCentralizerJoin Ω T.group a
  refine Q3Y2.oddCoreIn_sup_of_range_le _ fun y => ?_
  have htop : (⊤ : Subgroup (↥(centralizingLayer Ω {a}) ⧸
      classicalInvolutionOddCore ↥(centralizingLayer Ω {a}))) ≤
        fourCentralizerImage Ω T.group a := by
    rw [← D.generate]
    exact iSup_le hrange
  obtain ⟨j, hjJ, hjy⟩ := (show QuotientGroup.mk'
    (classicalInvolutionOddCore ↥(centralizingLayer Ω {a})) y ∈
      fourCentralizerImage Ω T.group a from htop trivial)
  exact ⟨j, Subgroup.mem_subgroupOf.mp hjJ, hjy⟩

end Triple

theorem centralizerGenerationModOTwoAt : CentralizerGenerationModOTwoAt := by
  intro G _ _ _ K z hS K₁ K₂ K₃ z₁ z₂ z₃ T a ha hfa
  have hΩ : InClass3 (conjClass3 K) := inClass3_conjugates hS.member
  have hIH : LocalLieSystems3 (conjClass3 K) := localLieSystems3_of_cit3Below hΩ hS.below
  have hnc : ∀ b : G, b ≠ 1 → b ∉ Subgroup.center G := fun b hb1 hbc =>
    not_subset_center_of_ne_one hS.nonabelian hb1 (Set.singleton_subset_iff.mpr hbc)
  obtain ⟨L, -, hLa⟩ := hfa
  exact centralizerGenerationModOTwo_of_exactTriple hIH T.exact T.ind T.mem₁ T.mem₂ T.mem₃
    T.cls₁ T.cls₂ T.cls₃ ha hLa.ne_one (hnc a hLa.ne_one)

end CFSG.ClassicalInvolution.Q3.Q3KC
