module

public import CFSG.ClassicalInvolution.Q3.Q3NLExact
public import CFSG.ClassicalInvolution.Asc77.WP3L52Main
public import CFSG.ClassicalInvolution.Q3.LieDecomposition
public import CFSG.ClassicalInvolution.Q3.M11Kernel

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3CH

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Asc77

section Family

variable {G : Type} [Group G] [Finite G] {s : G}

omit [Finite G] in
theorem isSectionMember3_conj {Y K : Subgroup G} {z : G} (h : IsSectionMember3 Y K z) {n : G}
    (hn : n ∈ Y) : IsSectionMember3 Y (conjSub n K) (n * z * n⁻¹) where
  le := by
    have := conjSub_mono (n := n) h.le
    rwa [conjSub_eq_self_of_mem hn] at this
  orderOf_eq_two := by
    have := orderOf_injective (MulAut.conj n).toMonoidHom (MulAut.conj n).injective z
    simpa [h.orderOf_eq_two] using this
  mem := conj_mem_conjSub h.mem
  subnormal := by
    have h1 := isSubnormal_map_conj h.subnormal n
    have h2 : (Subgroup.centralizer ({z} : Set G) ⊓ Y).map (MulAut.conj n).toMonoidHom =
        Subgroup.centralizer ({n * z * n⁻¹} : Set G) ⊓ Y := by
      rw [Subgroup.map_inf_eq _ _ (MulAut.conj n).toMonoidHom (MulAut.conj n).injective]
      rw [← conjSub_centralizer_singleton n z]
      show conjSub n (Subgroup.centralizer ({z} : Set G)) ⊓ conjSub n Y = _
      rw [conjSub_eq_self_of_mem hn]
    exact h2 ▸ h1
  nonempty_equiv := by
    obtain ⟨e'⟩ := h.nonempty_equiv
    let ε : ↥K ≃* ↥(conjSub n K) :=
      Subgroup.equivMapOfInjective K (MulAut.conj n).toMonoidHom (MulAut.conj n).injective
    exact ⟨(QuotientGroup.congr _ _ ε.symm (OddCore.equiv_invariant ε.symm)).trans e'⟩

@[expose] def sFamily3 (s : G) (L₁ L₂ L₃ : Subgroup G) : Set (Subgroup G) :=
  {M | ∃ h ∈ Subgroup.centralizer ({s} : Set G),
    M = conjSub h L₁ ∨ M = conjSub h L₂ ∨ M = conjSub h L₃}

omit [Finite G] in
theorem mem_sFamily3_one (s : G) (L₁ L₂ L₃ : Subgroup G) : L₁ ∈ sFamily3 s L₁ L₂ L₃ :=
  ⟨1, Subgroup.one_mem _, Or.inl (conjSub_one L₁).symm⟩

omit [Finite G] in
theorem mem_sFamily3_two (s : G) (L₁ L₂ L₃ : Subgroup G) : L₂ ∈ sFamily3 s L₁ L₂ L₃ :=
  ⟨1, Subgroup.one_mem _, Or.inr (Or.inl (conjSub_one L₂).symm)⟩

omit [Finite G] in
theorem mem_sFamily3_three (s : G) (L₁ L₂ L₃ : Subgroup G) : L₃ ∈ sFamily3 s L₁ L₂ L₃ :=
  ⟨1, Subgroup.one_mem _, Or.inr (Or.inr (conjSub_one L₃).symm)⟩

theorem secData3_sFamily3 {z₁ z₂ z₃ : G} {L₁ L₂ L₃ : Subgroup G}
    (h₁ : IsSectionMember3 (Subgroup.centralizer ({s} : Set G)) L₁ z₁)
    (h₂ : IsSectionMember3 (Subgroup.centralizer ({s} : Set G)) L₂ z₂)
    (h₃ : IsSectionMember3 (Subgroup.centralizer ({s} : Set G)) L₃ z₃) :
    SecData3 s (sFamily3 s L₁ L₂ L₃) where
  nonempty := ⟨L₁, mem_sFamily3_one s L₁ L₂ L₃⟩
  le := by
    rintro M ⟨h, hh, rfl | rfl | rfl⟩
    · exact (conjSub_mono h₁.le).trans (conjSub_eq_self_of_mem hh).le
    · exact (conjSub_mono h₂.le).trans (conjSub_eq_self_of_mem hh).le
    · exact (conjSub_mono h₃.le).trans (conjSub_eq_self_of_mem hh).le
  conj := by
    rintro n hn M ⟨h, hh, rfl | rfl | rfl⟩
    · exact ⟨n * h, Subgroup.mul_mem _ hn hh, Or.inl (conjSub_mul n h L₁).symm⟩
    · exact ⟨n * h, Subgroup.mul_mem _ hn hh, Or.inr (Or.inl (conjSub_mul n h L₂).symm)⟩
    · exact ⟨n * h, Subgroup.mul_mem _ hn hh, Or.inr (Or.inr (conjSub_mul n h L₃).symm)⟩
  member := by
    rintro M ⟨h, hh, rfl | rfl | rfl⟩
    · exact ⟨_, isSectionMember3_conj h₁ hh⟩
    · exact ⟨_, isSectionMember3_conj h₂ hh⟩
    · exact ⟨_, isSectionMember3_conj h₃ hh⟩

end Family

section Layer

variable {G : Type} [Group G] [Finite G] {Φ : Set (Subgroup G)} {a : G}

theorem normalizesLayer_of_secData3 (h : SecData3 a Φ) : NormalizesLayer Φ a := by
  have key : ∀ c : G, c ∈ Subgroup.centralizer ({a} : Set G) →
      centLayer Φ a ≤ conjSub c⁻¹ (centLayer Φ a) := by
    intro c hc
    refine centLayer_le fun L hL => ?_
    have hLc : conjSub c L ∈ centMembers Φ a :=
      ⟨h.conj c hc L hL.1, h.le _ (h.conj c hc L hL.1)⟩
    have h1 := conjSub_mono (n := c⁻¹) (le_centLayer hLc)
    rwa [conjSub_inv_conjSub] at h1
  intro c hc
  have h2 := key c⁻¹ (inv_mem hc)
  rw [inv_inv] at h2
  have h3 : conjSub c (centLayer Φ a) ≤ centLayer Φ a := by
    have := conjSub_mono (n := c) (key c hc)
    rwa [conjSub_conjSub_inv] at this
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr (le_antisymm h3 h2)

theorem not_le_center_of_secData3 (h : SecData3 a Φ) :
    ∀ L ∈ oddQuotientFamily (restrictFamily (centralizingMembers Φ {a})
      (centralizingLayer Φ {a})), ¬ L ≤ Subgroup.center (↥(centralizingLayer Φ {a}) ⧸
        classicalInvolutionOddCore ↥(centralizingLayer Φ {a})) := by
  rintro _ ⟨_, ⟨K, hK, hKY, rfl⟩, rfl⟩
  obtain ⟨z, hz⟩ := h.member K hK.1
  obtain ⟨hzY, hcl⟩ := (hz.restrict (centralizingLayer_le_centralizer Φ {a}) hKY).toIn
  exact hcl.map_oddQuotient.not_le_center

end Layer


theorem lieSystemMod3_of_secData3 {G : Type} [Group G] [Finite G] {Φ : Set (Subgroup G)} {a : G}
    (h : SecData3 a Φ) (hBelow : CIT3Below (Nat.card G))
    (ha : ¬ ({a} : Set G) ⊆ Subgroup.center G) :
    LieSystemMod3 (restrictFamily (centralizingMembers Φ {a}) (centralizingLayer Φ {a})) :=
  hBelow _ (card_centralizingLayer_lt Φ ha) _ h.inClass3

section Abstract

variable {X Yb : Type} [Group X] [Group Yb] {Ψ : Set (Subgroup Yb)} {ι : Type}

theorem ker_comp_le_center (D : LieSystemData3 ι Yb Ψ) (θ : Yb →* X)
    (hθ : Function.Injective θ) (i : ι) :
    (θ.comp (D.hom i)).ker ≤ Subgroup.center (D.kind i).G := fun x hx => by
  apply D.ker_le_center i
  rw [MonoidHom.mem_ker] at hx ⊢
  exact hθ (by simpa using hx)

theorem exists_comp_ne_one (D : LieSystemData3 ι Yb Ψ) (θ : Yb →* X) (hθ : Function.Injective θ)
    (i : ι) : ∃ x, (θ.comp (D.hom i)) x ≠ 1 := by
  obtain ⟨R, -, hmeet⟩ := D.meets i
  have h24 := D.card_eq _ hmeet
  obtain ⟨m, hm, hm1⟩ : ∃ m ∈ R.map (D.hom i), m ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : R.map (D.hom i) = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hcon
    rw [hbot, Subgroup.card_bot] at h24
    omega
  obtain ⟨r, -, rfl⟩ := hm
  exact ⟨r, fun h => hm1 (hθ (by simpa using h))⟩

@[expose] noncomputable def lieDecomposition3Of (h0 : ModelClauseZero) (hM : M11Facts)
    (D : LieSystemData3 ι Yb Ψ) (θ : Yb →* X) (hθ : Function.Injective θ)
    (hnc : ∀ L ∈ Ψ, ¬ L ≤ Subgroup.center Yb) :
    LieDecomposition3 (Subgroup.map θ '' Ψ) θ.range where
  ι := ι
  Q i := (θ.comp (D.hom i)).range
  commute := by
    rintro i j hij _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    simp only [MonoidHom.comp_apply]
    rw [← map_mul, ← map_mul, D.commute i j hij a b]
  iSup_eq := by
    simp_rw [MonoidHom.range_comp θ]
    rw [← Subgroup.map_iSup, D.generate, Subgroup.map_top]
  exists_le := by
    rintro _ ⟨L, hL, rfl⟩
    obtain ⟨i, R, -, rfl⟩ := D.fundamental L hL
    exact ⟨i, (MonoidHom.range_comp θ (D.hom i)).symm ▸
      Subgroup.map_mono (Subgroup.map_le_range _ _)⟩
  kind := by
    intro i
    have hQmap : (θ.comp (D.hom i)).range = (D.hom i).range.map θ := MonoidHom.range_comp θ _
    obtain ⟨t, n, ht, hadm, hc⟩ | hc | hc := D.valid i
    · exact Or.inr (Or.inl (range_model3 h0 ht hadm hc (θ.comp (D.hom i))
        (ker_comp_le_center D θ hθ i) (exists_comp_ne_one D θ hθ i)))
    · left
      have hfund : ∀ R ∈ (D.kind i).fund, R = ⊤ := fund_eq_top_of_sl23 hc
      refine ⟨?_, ?_, isSolvable_range_of_sl23 hc (θ.comp (D.hom i))⟩
      · obtain ⟨R, hR, hmeet⟩ := D.meets i
        rw [hfund R hR, Subgroup.map_top] at hmeet
        exact ⟨(D.hom i).range.map θ, ⟨(D.hom i).range, hmeet, rfl⟩, hQmap.symm⟩
      · rintro _ ⟨L₁, hL₁, rfl⟩ hle
        rw [hQmap] at hle ⊢
        have hle' : L₁ ≤ (D.hom i).range := (Subgroup.map_le_map_iff_of_injective hθ).mp hle
        obtain ⟨j, R', hR', hL₁eq⟩ := D.fundamental L₁ hL₁
        by_cases hji : j = i
        · subst hji
          rw [hfund R' hR', Subgroup.map_top] at hL₁eq
          rw [hL₁eq]
        · refine absurd ?_ (hnc L₁ hL₁)
          have hL₁j : L₁ ≤ (D.hom j).range := hL₁eq ▸ Subgroup.map_le_range _ _
          intro x hx
          have hxi := hle' hx
          have hxj := hL₁j hx
          rw [Subgroup.mem_center_iff]
          intro g
          have hg : g ∈ (⨆ k, (D.hom k).range : Subgroup Yb) := by rw [D.generate]; trivial
          have hcen : ∀ k, (D.hom k).range ≤ Subgroup.centralizer ({x} : Set Yb) := by
            rintro k _ ⟨y, rfl⟩
            rw [Subgroup.mem_centralizer_singleton_iff]
            by_cases hki : k = i
            · subst hki
              obtain ⟨z, rfl⟩ := hxj
              exact (D.commute j k hji z y).symm
            · obtain ⟨z, rfl⟩ := hxi
              exact (D.commute i k (Ne.symm hki) z y).symm
          exact Subgroup.mem_centralizer_singleton_iff.mp ((iSup_le hcen) hg)
    · exact Or.inr (Or.inr (range_m11 hM hc (θ.comp (D.hom i)) (exists_comp_ne_one D θ hθ i)))

theorem lieDecomposition3Of_Q (h0 : ModelClauseZero) (hM : M11Facts)
    (D : LieSystemData3 ι Yb Ψ) (θ : Yb →* X) (hθ : Function.Injective θ)
    (hnc : ∀ L ∈ Ψ, ¬ L ≤ Subgroup.center Yb) (i : ι) :
    (lieDecomposition3Of h0 hM D θ hθ hnc).Q i = (θ.comp (D.hom i)).range :=
  rfl

theorem eq_range_or_commutes [Finite X] (h0 : ModelClauseZero) (hM : M11Facts)
    (D : LieSystemData3 ι Yb Ψ) (θ : Yb →* X) (hθ : Function.Injective θ)
    (hnc : ∀ L ∈ Ψ, ¬ L ≤ Subgroup.center Yb) (hY : θ.range.Normal) {L : Subgroup X}
    (hL : CFSG.Open.IsComponentOf L ⊤) :
    (∃ i, L = (θ.comp (D.hom i)).range) ∨ Commutes L θ.range :=
  @LieDecomposition3.eq_or_commutes_of_isComponentOf _ _ _ _
    (lieDecomposition3Of h0 hM D θ hθ hnc) _ hY _ hL

theorem kind_ne_sl23_of_isQuasisimple (D : LieSystemData3 ι Yb Ψ) (θ : Yb →* X) {i : ι}
    (hq : CFSG.Open.IsQuasisimple ↥(θ.comp (D.hom i)).range) : D.kind i ≠ CompData.sl23 := by
  intro hc
  have hsolv := isSolvable_range_of_sl23 hc (θ.comp (D.hom i))
  have hsimple : IsSimpleGroup (↥(θ.comp (D.hom i)).range ⧸
      Subgroup.center ↥(θ.comp (D.hom i)).range) := hq.2
  have hnt : Nontrivial ↥(θ.comp (D.hom i)).range := by
    by_contra hcon
    rw [not_nontrivial_iff_subsingleton] at hcon
    have : Subsingleton (↥(θ.comp (D.hom i)).range ⧸
        Subgroup.center ↥(θ.comp (D.hom i)).range) := inferInstance
    exact (not_nontrivial_iff_subsingleton.mpr this) hsimple.toNontrivial
  exact (Group.IsSolvable.commutator_lt_top_of_nontrivial _).ne hq.1

end Abstract

section Section

variable {G : Type} [Group G] [Finite G] {Φ : Set (Subgroup G)} {a : G} {ι : Type}

@[expose] noncomputable def secComp (h : SecData3 a Φ)
    (D : LieSystemData3 ι (↥(centralizingLayer Φ {a}) ⧸
      classicalInvolutionOddCore ↥(centralizingLayer Φ {a}))
      (oddQuotientFamily (restrictFamily (centralizingMembers Φ {a})
        (centralizingLayer Φ {a})))) (i : ι) : Subgroup (OddQuot a) :=
  ((sectionQuotientHom (normalizesLayer_of_secData3 h)).comp (D.hom i)).range

variable (h : SecData3 a Φ)
    (D : LieSystemData3 ι (↥(centralizingLayer Φ {a}) ⧸
      classicalInvolutionOddCore ↥(centralizingLayer Φ {a}))
      (oddQuotientFamily (restrictFamily (centralizingMembers Φ {a})
        (centralizingLayer Φ {a}))))
include h

theorem eq_secComp_or_commutes {L : Subgroup (OddQuot a)} (hL : CFSG.IsComponent L) :
    (∃ i, L = secComp h D i) ∨ Commutes L (memberJoin Φ a) := by
  have hN := normalizesLayer_of_secData3 h
  have hY : (sectionQuotientHom hN).range.Normal := by
    rw [range_sectionQuotientHom hN]
    exact memberJoin_normal_of_normalizes hN
  rcases eq_range_or_commutes ModelFacts.modelClauseZero m11Facts D (sectionQuotientHom hN)
    (sectionQuotientHom_injective hN) (not_le_center_of_secData3 h) hY
    ((CFSG.isComponent_iff_open L).mp hL) with hk | hk
  · exact Or.inl hk
  · refine Or.inr fun x hx y hy => ?_
    rw [← range_sectionQuotientHom hN] at hy
    exact hk x hx y hy

theorem kind_of_isComponent_secComp {j : ι} (hL : CFSG.IsComponent (secComp h D j)) :
    (∃ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n : ℕ), IsFundTag t ∧
      CFSG.Assembly.LowTwoRank.StatedLieAdmissible t n 3 1 ∧ D.kind j = CompData.model t n) ∨
      D.kind j = CompData.m11 := by
  have hq : CFSG.Open.IsQuasisimple ↥(secComp h D j) :=
    ((CFSG.isComponent_iff_open _).mp hL).2.2
  rcases D.valid j with hm | hc | hc
  · exact Or.inl hm
  · exact absurd hc (kind_ne_sl23_of_isQuasisimple D _ hq)
  · exact Or.inr hc

theorem exists_modOdd_le_secComp {M : Subgroup G} (hM : M ∈ Φ) :
    ∃ i, modOdd a M ≤ secComp h D i := by
  have hN := normalizesLayer_of_secData3 h
  have hMc : M ∈ centMembers Φ a := ⟨hM, h.le M hM⟩
  have hMY : M ≤ centralizingLayer Φ {a} := le_centLayer hMc
  have hMfam : modOddIn (centralizingLayer Φ {a}) M ∈
      oddQuotientFamily (restrictFamily (centralizingMembers Φ {a}) (centralizingLayer Φ {a})) :=
    ⟨M.subgroupOf _, ⟨M, hMc, hMY, rfl⟩, rfl⟩
  obtain ⟨i, R, -, hMR⟩ := D.fundamental _ hMfam
  refine ⟨i, fun x hx => ?_⟩
  rw [← map_sectionQuotientHom_modOddIn hN hMc] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  rw [hMR] at hy
  obtain ⟨r, -, rfl⟩ := hy
  exact ⟨r, rfl⟩

theorem eq_secComp_of_not_commute {x : OddQuot a} {j : ι} (hxj : x ∈ secComp h D j)
    {L : Subgroup (OddQuot a)} (hL : CFSG.IsComponent L) (hx : ∃ y ∈ L, x * y ≠ y * x) :
    L = secComp h D j := by
  obtain ⟨y, hyL, hy⟩ := hx
  rcases eq_secComp_or_commutes h D hL with ⟨i, rfl⟩ | hcomm
  · by_cases hij : i = j
    · rw [hij]
    · exfalso
      obtain ⟨m, rfl⟩ := hyL
      obtain ⟨k, rfl⟩ := hxj
      apply hy
      have h1 := map_mul (sectionQuotientHom (normalizesLayer_of_secData3 h)) (D.hom j k)
        (D.hom i m)
      have h2 := map_mul (sectionQuotientHom (normalizesLayer_of_secData3 h)) (D.hom i m)
        (D.hom j k)
      have h3 := congrArg (sectionQuotientHom (normalizesLayer_of_secData3 h))
        (D.commute j i (Ne.symm hij) k m)
      exact h1.symm.trans (h3.trans h2)
  · exfalso
    apply hy
    have hxJ : x ∈ memberJoin Φ a := by
      rw [← range_sectionQuotientHom (normalizesLayer_of_secData3 h)]
      obtain ⟨k, rfl⟩ := hxj
      exact ⟨D.hom j k, rfl⟩
    exact (hcomm y hyL x hxJ).symm

theorem eq_secComp_of_movedByAll {B : Subgroup G} (hB : CFSG.Open.IsElemAbelian 2 B) (haB : a ∈ B)
    (ha1 : a ≠ 1) {b : G} (hbB : b ∈ B) (hb1 : b ≠ 1) (hba : b ≠ a)
    (hbC : b ∈ Subgroup.centralizer ({a} : Set G)) {j : ι}
    (hbj : oddQuotMk a ⟨b, hbC⟩ ∈ secComp h D j) {L : Subgroup (OddQuot a)}
    (hL : CFSG.IsComponent L) (hmov : MovedByAll B a L) : L = secComp h D j :=
  eq_secComp_of_not_commute h D hbj hL (hmov _ (oddQuotMk_mem_modOdd hbB hbC)
    (Lemma52Proof.oddQuotMk_not_mem_zpowers hB haB ha1 hbB hb1 hba hbC))

end Section

end CFSG.ClassicalInvolution.Q3.Q3CH
