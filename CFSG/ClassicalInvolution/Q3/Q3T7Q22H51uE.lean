module

public import CFSG.ClassicalInvolution.Q3.Q3T7Q22H51uB

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Q3.Q3CH CFSG.ClassicalInvolution.Asc77


section Component

theorem alphaOf_eq_bot_of_twinOuter_comp3 (hrows : TwinOuterAlphaAll3) {c : CompData}
    (hc : ∃ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n : ℕ), IsFundTag t ∧
      CFSG.Assembly.LowTwoRank.StatedLieAdmissible t n 3 1 ∧ c = CompData.model t n)
    {H : Type} [Group H] [Finite H] (ψ : c.G →* H) (R R' : Subgroup c.G) (x x' : c.G)
    (hker : ψ.ker ≤ Subgroup.center c.G) (hR : R ∈ c.fund) (hR' : R' ∈ c.fund) (hne : R ≠ R')
    (hcomm : Commutes R R') (hx : x ∈ R) (hx2 : x * x = 1) (hx1 : x ≠ 1) (hx' : x' ∈ R')
    (hx'2 : x' * x' = 1) (hx'1 : x' ≠ 1) (hsame : ψ x = ψ x') (v : ↥(inducedAutOn ψ.range))
    (hvR : ∀ r ∈ R, v * FrameVertex.innerHom ψ r = FrameVertex.innerHom ψ r * v)
    (hvR' : ∀ r ∈ R', v * FrameVertex.innerHom ψ r = FrameVertex.innerHom ψ r * v)
    (hv4 : v * v * (v * v) = 1) (hv1 : v * v ≠ 1) (hvx : v * v ≠ FrameVertex.innerHom ψ x) :
    alphaOf (Subgroup.closure ({FrameVertex.innerHom ψ x, v * v} :
      Set ↥(inducedAutOn ψ.range))) = ⊥ := by
  obtain ⟨t, n, ht, hadm, rfl⟩ := hc
  exact hrows t n ht hadm H ψ R R' x x'
    ⟨hker, hR, hR', hne, hcomm, hx, hx2, hx1, hx', hx'2, hx'1, hsame⟩ v hvR hvR' hv4 hv1 hvx

end Component

section Alpha

variable {G : Type} [Group G] [Finite G] {Φ : Set (Subgroup G)} {c : G} {ι : Type}

theorem alpha_of_twinOuter3 (hrows : TwinOuterAlphaAll3) (hΦ : SecData3 c Φ)
    (D : LieSystemData3 ι (↥(centralizingLayer Φ {c}) ⧸
      classicalInvolutionOddCore ↥(centralizingLayer Φ {c}))
      (oddQuotientFamily (restrictFamily (centralizingMembers Φ {c})
        (centralizingLayer Φ {c}))))
    {j : ι} {B : Subgroup G} (hB : IsElemAbelian 2 B) (hcB : c ∈ B) (hc1 : c ≠ 1) {z t : G}
    (hzB : z ∈ B) (htB : t ∈ B) (hz1 : z ≠ 1) (ht1 : t ≠ 1) (hzc : z ≠ c) (htc : t ≠ c)
    (hztc : z * t ≠ c) (hzt1 : z * t ≠ 1) (hBeq : B = Subgroup.closure ({z, t, c} : Set G))
    {M M' : Subgroup G} (hM : M ∈ Φ) (hM' : M' ∈ Φ) (htU : IsUniqueInvolution M t)
    (htU' : IsUniqueInvolution M' t) (hne : modOdd c M ≠ modOdd c M')
    (hcomm : ∀ x ∈ modOdd c M, ∀ y ∈ modOdd c M', x * y = y * x) {a : G}
    (haC : a ∈ Subgroup.centralizer ({c} : Set G)) (ha2 : a * a = z) (hat : a * t = t * a)
    (hcommM : ∀ x ∈ modOdd c M, oddQuotMk c ⟨a, haC⟩ * x = x * oddQuotMk c ⟨a, haC⟩)
    (hcommM' : ∀ x ∈ modOdd c M', oddQuotMk c ⟨a, haC⟩ * x = x * oddQuotMk c ⟨a, haC⟩)
    (hMj : modOdd c M ≤ secComp hΦ D j) (hmov : MovedByAll B c (secComp hΦ D j))
    (hLc : CFSG.IsComponent (secComp hΦ D j)) :
    alphaOf (inducedImage (secComp hΦ D j) (modOdd c B)) = ⊥ := by
  classical
  have hzC : z ∈ Subgroup.centralizer ({c} : Set G) :=
    Lemma52Proof.le_centralizer_of_mem hB hcB hzB
  have htC : t ∈ Subgroup.centralizer ({c} : Set G) :=
    Lemma52Proof.le_centralizer_of_mem hB hcB htB
  have hM'j : modOdd c M' ≤ secComp hΦ D j :=
    modOdd_twin_le_secComp3 hΦ D hB hcB hc1 htB ht1 htc htC hmov hLc hM' htU'.mem
  have hk : ∃ (t' : CFSG.Assembly.LowTwoRank.StatedLieTag) (n : ℕ), IsFundTag t' ∧
      CFSG.Assembly.LowTwoRank.StatedLieAdmissible t' n 3 1 ∧ D.kind j = CompData.model t' n := by
    rcases kind_of_isComponent_secComp hΦ D hLc with hk | hk
    · exact hk
    · exact absurd (Q3T6D.m11_twin_glue hΦ D hk hM hM' hMj hM'j htU htU') hne
  obtain ⟨R, R', x₁, x₁', hR, hR', hRR', hcommR, hx, hx2, hx1, hx', hx'2, hx'1, hsame, hRψ,
    hR'ψ, hψx₁⟩ := exists_twinData3 hΦ D hk hM hM' htU htU' htC hMj hM'j hne hcomm
  have hN := normalizesLayer_of_secData3 hΦ
  have hker : (compHom3 hΦ D j).ker ≤ Subgroup.center (D.kind j).G :=
    Q3CH.ker_comp_le_center D (sectionQuotientHom hN) (sectionQuotientHom_injective hN) j
  set ψ := compHom3 hΦ D j with hψdef
  have hx₁nc : ¬ ∀ y ∈ ψ.range, ψ x₁ * y = y * ψ x₁ := fun hall =>
    hx1 (model_fund_noncentral3 hk ψ hker hR hx hall)
  have hn : oddQuotMk c ⟨a, haC⟩ ∈ Subgroup.normalizer (ψ.range : Set (OddQuot c)) :=
    mem_normalizer_of_commute_noncentral hLc ⟨x₁, rfl⟩ hx₁nc
      (g := oddQuotMk c ⟨a, haC⟩) (by
        rw [hψx₁, ← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext hat)
  have hψnorm : ∀ w : (D.kind j).G, ψ w ∈ Subgroup.normalizer (ψ.range : Set (OddQuot c)) :=
    FrameVertex.mem_normalizer_range ψ
  set v : ↥(inducedAutOn ψ.range) :=
    toInducedAutOn ψ.range ⟨oddQuotMk c ⟨a, haC⟩, hn⟩ with hv
  have hvR : ∀ r ∈ R, v * FrameVertex.innerHom ψ r = FrameVertex.innerHom ψ r * v := by
    intro r hr
    rw [FrameVertex.innerHom_apply, hv, ← map_mul, ← map_mul]
    have hr' : ψ r ∈ modOdd c M := hRψ ▸ Subgroup.mem_map_of_mem ψ hr
    congr 1
    exact Subtype.ext (hcommM (ψ r) hr')
  have hvR' : ∀ r ∈ R', v * FrameVertex.innerHom ψ r = FrameVertex.innerHom ψ r * v := by
    intro r hr
    rw [FrameVertex.innerHom_apply, hv, ← map_mul, ← map_mul]
    have hr' : ψ r ∈ modOdd c M' := hR'ψ ▸ Subgroup.mem_map_of_mem ψ hr
    congr 1
    exact Subtype.ext (hcommM' (ψ r) hr')
  have hxx : oddQuotMk c ⟨a, haC⟩ * oddQuotMk c ⟨a, haC⟩ = oddQuotMk c ⟨z, hzC⟩ := by
    rw [← map_mul]
    congr 1
    exact Subtype.ext ha2
  have hzn : oddQuotMk c ⟨z, hzC⟩ ∈ Subgroup.normalizer (ψ.range : Set (OddQuot c)) := by
    rw [← hxx]
    exact Subgroup.mul_mem _ hn hn
  have htn : oddQuotMk c ⟨t, htC⟩ ∈ Subgroup.normalizer (ψ.range : Set (OddQuot c)) := by
    rw [← hψx₁]
    exact hψnorm x₁
  have hvv : v * v = toInducedAutOn ψ.range ⟨oddQuotMk c ⟨z, hzC⟩, hzn⟩ := by
    rw [hv, ← map_mul]
    congr 1
    exact Subtype.ext hxx
  have hzz : oddQuotMk c ⟨z, hzC⟩ * oddQuotMk c ⟨z, hzC⟩ = 1 := by
    rw [← map_mul]
    have : (⟨z, hzC⟩ * ⟨z, hzC⟩ : ↥(Subgroup.centralizer ({c} : Set G))) = 1 :=
      Subtype.ext (Lemma52Proof.mul_self_eq_one_of_mem hB hzB)
    rw [this, map_one]
  have htt : oddQuotMk c ⟨t, htC⟩ * oddQuotMk c ⟨t, htC⟩ = 1 := by
    rw [← map_mul]
    have : (⟨t, htC⟩ * ⟨t, htC⟩ : ↥(Subgroup.centralizer ({c} : Set G))) = 1 :=
      Subtype.ext htU.sq
    rw [this, map_one]
  have hvv2 : v * v * (v * v) = 1 := by
    rw [hvv, ← map_mul]
    have : (⟨oddQuotMk c ⟨z, hzC⟩, hzn⟩ * ⟨oddQuotMk c ⟨z, hzC⟩, hzn⟩ :
        ↥(Subgroup.normalizer (ψ.range : Set (OddQuot c)))) = 1 := Subtype.ext hzz
    rw [this, map_one]
  have hmovz := hmov (oddQuotMk c ⟨z, hzC⟩) (oddQuotMk_mem_modOdd hzB hzC)
    (Lemma52Proof.oddQuotMk_not_mem_zpowers hB hcB hc1 hzB hz1 hzc hzC)
  have hvv1 : v * v ≠ 1 := by
    rw [hvv]
    obtain ⟨y', hy', hxy'⟩ := hmovz
    exact Lemma52Proof.toInducedAutOn_ne_one_of_moved ψ.range hzn hy' hxy'
  have hztC : z * t ∈ Subgroup.centralizer ({c} : Set G) := Subgroup.mul_mem _ hzC htC
  have hztB : z * t ∈ B := Subgroup.mul_mem _ hzB htB
  have hmovzt := hmov (oddQuotMk c ⟨z * t, hztC⟩) (oddQuotMk_mem_modOdd hztB hztC)
    (Lemma52Proof.oddQuotMk_not_mem_zpowers hB hcB hc1 hztB hzt1 hztc hztC)
  have hv4 : v * v ≠ FrameVertex.innerHom ψ x₁ := by
    intro h
    have h1 : toInducedAutOn ψ.range ⟨oddQuotMk c ⟨z, hzC⟩, hzn⟩ =
        toInducedAutOn ψ.range ⟨oddQuotMk c ⟨t, htC⟩, htn⟩ := by
      rw [← hvv, h, FrameVertex.innerHom_apply]
      congr 1
      exact Subtype.ext hψx₁
    have hztn : oddQuotMk c ⟨z * t, hztC⟩ ∈ Subgroup.normalizer (ψ.range : Set (OddQuot c)) := by
      have : oddQuotMk c ⟨z * t, hztC⟩ = oddQuotMk c ⟨z, hzC⟩ * oddQuotMk c ⟨t, htC⟩ :=
        map_mul (oddQuotMk c) (⟨z, hzC⟩ : ↥(Subgroup.centralizer ({c} : Set G))) ⟨t, htC⟩
      rw [this]
      exact Subgroup.mul_mem _ hzn htn
    have h2 : toInducedAutOn ψ.range ⟨oddQuotMk c ⟨z * t, hztC⟩, hztn⟩ = 1 := by
      have h3 : (⟨oddQuotMk c ⟨z * t, hztC⟩, hztn⟩ :
          ↥(Subgroup.normalizer (ψ.range : Set (OddQuot c)))) =
            ⟨oddQuotMk c ⟨z, hzC⟩, hzn⟩ * ⟨oddQuotMk c ⟨t, htC⟩, htn⟩ :=
        Subtype.ext (map_mul (oddQuotMk c)
          (⟨z, hzC⟩ : ↥(Subgroup.centralizer ({c} : Set G))) ⟨t, htC⟩)
      rw [h3, map_mul, h1, ← map_mul]
      have h4 : (⟨oddQuotMk c ⟨t, htC⟩, htn⟩ * ⟨oddQuotMk c ⟨t, htC⟩, htn⟩ :
          ↥(Subgroup.normalizer (ψ.range : Set (OddQuot c)))) = 1 := Subtype.ext htt
      rw [h4, map_one]
    have hcomm' := Lemma52Proof.commute_of_toInducedAutOn_eq_one ψ.range hztn h2
    obtain ⟨y', hy', hxy'⟩ := hmovzt
    exact hxy' (hcomm' y' hy')
  have key := alphaOf_eq_bot_of_twinOuter_comp3 hrows hk ψ R R' x₁ x₁' hker hR hR' hRR' hcommR
    hx hx2 hx1 hx' hx'2 hx'1 hsame v hvR hvR' hvv2 hvv1 hv4
  set T : Subgroup ↥(inducedAutOn ψ.range) :=
    Subgroup.closure ({FrameVertex.innerHom ψ x₁, v * v} : Set ↥(inducedAutOn ψ.range)) with hT
  have hcC : c ∈ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hS : ({z, t, c} : Set G) ⊆ Subgroup.centralizer ({c} : Set G) := by
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with hg | hg | hg <;> rw [hg]
    · exact hzC
    · exact htC
    · exact hcC
  have hgen : ∀ s : G, s ∈ ({z, t, c} : Set G) → ∀ hs' : s ∈ Subgroup.centralizer ({c} : Set G),
      ∃ hn' : oddQuotMk c ⟨s, hs'⟩ ∈ Subgroup.normalizer (ψ.range : Set (OddQuot c)),
        toInducedAutOn ψ.range ⟨oddQuotMk c ⟨s, hs'⟩, hn'⟩ ∈ T := by
    intro s hs' hsC
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs'
    rcases hs' with hs' | hs' | hs'
    · subst s
      refine ⟨hzn, ?_⟩
      rw [← hvv]
      exact Subgroup.subset_closure (by simp)
    · subst s
      refine ⟨htn, ?_⟩
      have h1 : toInducedAutOn ψ.range ⟨oddQuotMk c ⟨t, hsC⟩, htn⟩ =
          FrameVertex.innerHom ψ x₁ := by
        rw [FrameVertex.innerHom_apply]
        congr 1
        exact Subtype.ext hψx₁.symm
      rw [h1]
      exact Subgroup.subset_closure (by simp)
    · subst s
      obtain ⟨hcn, hc1'⟩ := oddQuotSelf_induced c ψ.range
      refine ⟨hcn, ?_⟩
      have h1 : toInducedAutOn ψ.range ⟨oddQuotMk c ⟨c, hsC⟩, hcn⟩ = 1 := hc1'
      rw [h1]
      exact T.one_mem
  have hle1 : inducedImage ψ.range (modOdd c B) ≤ T := by
    rw [hBeq]
    exact inducedImage_modOdd_closure_le hS ψ.range T (fun s hs'' => hgen s hs'' (hS hs''))
  have hψx₁B : ψ x₁ ∈ modOdd c B := by
    rw [hψx₁]
    exact oddQuotMk_mem_modOdd htB htC
  have hle2 : T ≤ inducedImage ψ.range (modOdd c B) := by
    refine (Subgroup.closure_le _).mpr ?_
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with hg | hg
    · rw [hg, FrameVertex.innerHom_apply]
      exact ⟨⟨ψ x₁, hψnorm x₁⟩, Subgroup.mem_subgroupOf.mpr hψx₁B, rfl⟩
    · rw [hg, hvv]
      exact ⟨⟨oddQuotMk c ⟨z, hzC⟩, hzn⟩,
        Subgroup.mem_subgroupOf.mpr (oddQuotMk_mem_modOdd hzB hzC), rfl⟩
  exact (congrArg alphaOf (le_antisymm hle1 hle2)).trans key

end Alpha

end CFSG.ClassicalInvolution.Q3.Q3T7
