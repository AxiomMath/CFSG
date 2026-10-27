module

public import CFSG.ClassicalInvolution.Q3.Q3T7Q22H51uA
public import CFSG.ClassicalInvolution.Q3.Q3WASTTags
public import CFSG.ClassicalInvolution.Q3.Q3T6DH51M11

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Q3.Q3CH CFSG.ClassicalInvolution.Asc77


section Model

theorem model_fund_noncentral3 {c : CompData}
    (hc : ∃ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n : ℕ), IsFundTag t ∧
      CFSG.Assembly.LowTwoRank.StatedLieAdmissible t n 3 1 ∧ c = CompData.model t n)
    {X : Type} [Group X] (ψ : c.G →* X) (hker : ψ.ker ≤ Subgroup.center c.G)
    {R : Subgroup c.G} (hR : R ∈ c.fund) {r : c.G} (hr : r ∈ R)
    (hall : ∀ y ∈ ψ.range, ψ r * y = y * ψ r) : r = 1 := by
  obtain ⟨t, n, ht, hadm, rfl⟩ := hc
  exact CFSG.ClassicalInvolution.ModelFacts.fundNoncentral_generic 3 t n 1 ht hadm
    (Q3W.not_psl_two_of_admissible3 hadm) R hR r hr (fun y => by
      apply hker
      rw [MonoidHom.mem_ker]
      simp only [map_mul, map_inv]
      rw [hall (ψ y) ⟨y, rfl⟩]
      group)

theorem model_fund_eq_one3 {c : CompData}
    (hc : ∃ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n : ℕ), IsFundTag t ∧
      CFSG.Assembly.LowTwoRank.StatedLieAdmissible t n 3 1 ∧ c = CompData.model t n)
    {X : Type} [Group X] (ψ : c.G →* X) (hker : ψ.ker ≤ Subgroup.center c.G)
    {R : Subgroup c.G} (hR : R ∈ c.fund) {r : c.G} (hr : r ∈ R) (h1 : ψ r = 1) : r = 1 := by
  obtain ⟨t, n, ht, hadm, rfl⟩ := hc
  have hrc : r ∈ Subgroup.center _ := hker (MonoidHom.mem_ker.mpr h1)
  exact CFSG.ClassicalInvolution.ModelFacts.fundNoncentral_generic 3 t n 1 ht hadm
    (Q3W.not_psl_two_of_admissible3 hadm) R hR r hr (fun y => by
      have h2 : r * y * r⁻¹ * y⁻¹ = 1 := by
        rw [← Subgroup.mem_center_iff.mp hrc y]
        group
      rw [h2]
      exact Subgroup.one_mem _)

theorem model_fund_commutes3 {c : CompData}
    (hc : ∃ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n : ℕ), IsFundTag t ∧
      CFSG.Assembly.LowTwoRank.StatedLieAdmissible t n 3 1 ∧ c = CompData.model t n)
    {X : Type} [Group X] (ψ : c.G →* X) (hker : ψ.ker ≤ Subgroup.center c.G)
    {R R' : Subgroup c.G} (hR : R ∈ c.fund) (hR' : R' ∈ c.fund)
    (h : ∀ a ∈ R.map ψ, ∀ b ∈ R'.map ψ, a * b = b * a) : Commutes R R' := by
  obtain ⟨t, n, ht, hadm, hc⟩ := hc
  by_cases hex : t = .G2 ∨ t = .trialityD4
  · subst hc
    have hZ : Subgroup.center (modelUniv t n 3 1 Nat.prime_three).K = ⊥ :=
      RouteD.G2D4.center_modelUniv_g2d4_eq_bot (by norm_num) hex n le_rfl
    have hinj : Function.Injective ψ := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      exact hker.trans hZ.le
    intro a ha b hb
    apply hinj
    rw [map_mul, map_mul]
    exact h _ (Subgroup.mem_map_of_mem ψ ha) _ (Subgroup.mem_map_of_mem ψ hb)
  · have hG2 : t ≠ .G2 := fun e => hex (Or.inl e)
    have hD4 : t ≠ .trialityD4 := fun e => hex (Or.inr e)
    have hpc := Q3W.powCop3_of_kind3 hc ht hadm hG2 hD4
    have hcop : ∀ w ∈ ψ.ker, ¬ 3 ∣ orderOf w := fun w hw => hpc.cop w (hker hw)
    have key := Q3W.commutes_of_map_commute_exponent3 ψ hker hcop (A := R') (L := R)
      (hpc.pow3 R hR) (fun a ha l hl =>
        (h _ (Subgroup.mem_map_of_mem ψ hl) _ (Subgroup.mem_map_of_mem ψ ha)).symm)
    intro a ha b hb
    exact (key b hb a ha).symm

end Model

section Twin

variable {G : Type} [Group G] [Finite G] {Φ : Set (Subgroup G)} {c : G} {ι : Type}

theorem modOdd_twin_le_secComp3 (hΦ : SecData3 c Φ)
    (D : LieSystemData3 ι (↥(centralizingLayer Φ {c}) ⧸
      classicalInvolutionOddCore ↥(centralizingLayer Φ {c}))
      (oddQuotientFamily (restrictFamily (centralizingMembers Φ {c})
        (centralizingLayer Φ {c}))))
    {B : Subgroup G} (hB : IsElemAbelian 2 B) (hcB : c ∈ B) (hc1 : c ≠ 1) {b : G} (hbB : b ∈ B)
    (hb1 : b ≠ 1) (hbc : b ≠ c) (hbC : b ∈ Subgroup.centralizer ({c} : Set G)) {j : ι}
    (hmov : MovedByAll B c (secComp hΦ D j)) (hLc : CFSG.IsComponent (secComp hΦ D j))
    {M' : Subgroup G} (hM' : M' ∈ Φ) (hbM' : b ∈ M') : modOdd c M' ≤ secComp hΦ D j := by
  obtain ⟨i, hi⟩ := exists_modOdd_le_secComp hΦ D hM'
  have hbi : oddQuotMk c ⟨b, hbC⟩ ∈ secComp hΦ D i := hi (oddQuotMk_mem_modOdd hbM' hbC)
  have h := eq_secComp_of_movedByAll hΦ D hB hcB hc1 hbB hb1 hbc hbC hbi hLc hmov
  rw [h]
  exact hi

noncomputable abbrev compHom3 (hΦ : SecData3 c Φ)
    (D : LieSystemData3 ι (↥(centralizingLayer Φ {c}) ⧸
      classicalInvolutionOddCore ↥(centralizingLayer Φ {c}))
      (oddQuotientFamily (restrictFamily (centralizingMembers Φ {c})
        (centralizingLayer Φ {c})))) (j : ι) : (D.kind j).G →* OddQuot c :=
  (sectionQuotientHom (normalizesLayer_of_secData3 hΦ)).comp (D.hom j)

theorem exists_twinData3 (hΦ : SecData3 c Φ)
    (D : LieSystemData3 ι (↥(centralizingLayer Φ {c}) ⧸
      classicalInvolutionOddCore ↥(centralizingLayer Φ {c}))
      (oddQuotientFamily (restrictFamily (centralizingMembers Φ {c})
        (centralizingLayer Φ {c}))))
    {j : ι}
    (hk : ∃ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n : ℕ), IsFundTag t ∧
      CFSG.Assembly.LowTwoRank.StatedLieAdmissible t n 3 1 ∧ D.kind j = CompData.model t n)
    {M M' : Subgroup G} {b : G} (hM : M ∈ Φ) (hM' : M' ∈ Φ) (hbU : IsUniqueInvolution M b)
    (hbU' : IsUniqueInvolution M' b) (hbC : b ∈ Subgroup.centralizer ({c} : Set G))
    (hMj : modOdd c M ≤ secComp hΦ D j) (hM'j : modOdd c M' ≤ secComp hΦ D j)
    (hne : modOdd c M ≠ modOdd c M')
    (hcomm : ∀ x ∈ modOdd c M, ∀ y ∈ modOdd c M', x * y = y * x) :
    ∃ (R R' : Subgroup (D.kind j).G) (x x' : (D.kind j).G),
      R ∈ (D.kind j).fund ∧ R' ∈ (D.kind j).fund ∧ R ≠ R' ∧ Commutes R R' ∧
        x ∈ R ∧ x * x = 1 ∧ x ≠ 1 ∧ x' ∈ R' ∧ x' * x' = 1 ∧ x' ≠ 1 ∧
        compHom3 hΦ D j x = compHom3 hΦ D j x' ∧
        R.map (compHom3 hΦ D j) = modOdd c M ∧ R'.map (compHom3 hΦ D j) = modOdd c M' ∧
        compHom3 hΦ D j x = oddQuotMk c ⟨b, hbC⟩ := by
  classical
  have hN := normalizesLayer_of_secData3 hΦ
  have hθ : Function.Injective (sectionQuotientHom hN) := sectionQuotientHom_injective hN
  have hker : (compHom3 hΦ D j).ker ≤ Subgroup.center (D.kind j).G :=
    Q3CH.ker_comp_le_center D (sectionQuotientHom hN) hθ j
  have hMc : M ∈ centMembers Φ c := ⟨hM, hΦ.le M hM⟩
  have hM'c : M' ∈ centMembers Φ c := ⟨hM', hΦ.le M' hM'⟩
  have hMY : M ≤ centralizingLayer Φ {c} := le_centLayer hMc
  have hM'Y : M' ≤ centralizingLayer Φ {c} := le_centLayer hM'c
  have hfam : ∀ {N : Subgroup G}, N ∈ centMembers Φ c → N ≤ centralizingLayer Φ {c} →
      modOddIn (centralizingLayer Φ {c}) N ∈ oddQuotientFamily
        (restrictFamily (centralizingMembers Φ {c}) (centralizingLayer Φ {c})) :=
    fun hNc hNY => ⟨_, ⟨_, hNc, hNY, rfl⟩, rfl⟩
  have hle : ∀ {N : Subgroup G}, N ∈ centMembers Φ c → modOdd c N ≤ secComp hΦ D j →
      modOddIn (centralizingLayer Φ {c}) N ≤ (D.hom j).range := by
    intro N hNc hNj
    have h1 : (modOddIn (centralizingLayer Φ {c}) N).map (sectionQuotientHom hN) ≤
        (D.hom j).range.map (sectionQuotientHom hN) := by
      rw [map_sectionQuotientHom_modOddIn hN hNc]
      exact hNj.trans (MonoidHom.range_comp (sectionQuotientHom hN) (D.hom j)).le
    exact (Subgroup.map_le_map_iff_of_injective hθ).mp h1
  obtain ⟨R, hR, hMR⟩ := Q3T6D.exists_fund_of_le_range3 D (hfam hMc hMY) (hle hMc hMj)
    (not_le_center_of_secData3 hΦ _ (hfam hMc hMY))
  obtain ⟨R', hR', hMR'⟩ := Q3T6D.exists_fund_of_le_range3 D (hfam hM'c hM'Y) (hle hM'c hM'j)
    (not_le_center_of_secData3 hΦ _ (hfam hM'c hM'Y))
  have hRψ : R.map (compHom3 hΦ D j) = modOdd c M := by
    rw [← map_sectionQuotientHom_modOddIn hN hMc, hMR]
    exact (Subgroup.map_map (sectionQuotientHom hN) (D.hom j) (K := R)).symm
  have hR'ψ : R'.map (compHom3 hΦ D j) = modOdd c M' := by
    rw [← map_sectionQuotientHom_modOddIn hN hM'c, hMR']
    exact (Subgroup.map_map (sectionQuotientHom hN) (D.hom j) (K := R')).symm
  have hbb : oddQuotMk c ⟨b, hbC⟩ * oddQuotMk c ⟨b, hbC⟩ = 1 := by
    rw [← map_mul]
    have : (⟨b, hbC⟩ * ⟨b, hbC⟩ : ↥(Subgroup.centralizer ({c} : Set G))) = 1 :=
      Subtype.ext hbU.sq
    rw [this, map_one]
  have hb1 : oddQuotMk c ⟨b, hbC⟩ ≠ 1 := fun h => hbU.ne_one (congrArg Subtype.val
    (eq_one_of_oddQuotMk_eq_one (x := ⟨b, hbC⟩) (Subtype.ext hbU.sq) h))
  obtain ⟨x, hxR, hxψ⟩ : oddQuotMk c ⟨b, hbC⟩ ∈ R.map (compHom3 hΦ D j) := by
    rw [hRψ]
    exact oddQuotMk_mem_modOdd hbU.mem hbC
  obtain ⟨x', hxR', hxψ'⟩ : oddQuotMk c ⟨b, hbC⟩ ∈ R'.map (compHom3 hΦ D j) := by
    rw [hR'ψ]
    exact oddQuotMk_mem_modOdd hbU'.mem hbC
  refine ⟨R, R', x, x', hR, hR', fun h => hne (by rw [← hRψ, ← hR'ψ, h]),
    model_fund_commutes3 hk (compHom3 hΦ D j) hker hR hR' (fun a ha b hb => by
      rw [hRψ] at ha
      rw [hR'ψ] at hb
      exact hcomm a ha b hb), hxR, ?_, ?_, hxR', ?_, ?_, ?_, hRψ, hR'ψ, hxψ⟩
  · refine model_fund_eq_one3 hk (compHom3 hΦ D j) hker hR (R.mul_mem hxR hxR) ?_
    rw [map_mul, hxψ, hbb]
  · intro h
    rw [h, map_one] at hxψ
    exact hb1 hxψ.symm
  · refine model_fund_eq_one3 hk (compHom3 hΦ D j) hker hR' (R'.mul_mem hxR' hxR') ?_
    rw [map_mul, hxψ', hbb]
  · intro h
    rw [h, map_one] at hxψ'
    exact hb1 hxψ'.symm
  · rw [hxψ, hxψ']

end Twin

section Alpha

variable {G : Type} [Group G] [Finite G] {Φ : Set (Subgroup G)} {c : G} {ι : Type}

theorem alpha_of_twinSq3 (hrows : TwinSqAlphaAll3) (hΦ : SecData3 c Φ)
    (D : LieSystemData3 ι (↥(centralizingLayer Φ {c}) ⧸
      classicalInvolutionOddCore ↥(centralizingLayer Φ {c}))
      (oddQuotientFamily (restrictFamily (centralizingMembers Φ {c})
        (centralizingLayer Φ {c}))))
    {j : ι} {B : Subgroup G} (hB : IsElemAbelian 2 B) (hcB : c ∈ B) (hc1 : c ≠ 1) {z : G}
    (hzB : z ∈ B) (hz1 : z ≠ 1) (hzc : z ≠ c) {M M' : Subgroup G} (hM : M ∈ Φ) (hM' : M' ∈ Φ)
    (hzU : IsUniqueInvolution M z) (hzU' : IsUniqueInvolution M' z)
    (hne : modOdd c M ≠ modOdd c M')
    (hcomm : ∀ x ∈ modOdd c M, ∀ y ∈ modOdd c M', x * y = y * x) {a m : G}
    (haC : a ∈ Subgroup.centralizer ({c} : Set G)) (ha2 : a * a = z)
    (hcommM : ∀ x ∈ modOdd c M, oddQuotMk c ⟨a, haC⟩ * x = x * oddQuotMk c ⟨a, haC⟩)
    (hcommM' : ∀ x ∈ modOdd c M', oddQuotMk c ⟨a, haC⟩ * x = x * oddQuotMk c ⟨a, haC⟩)
    (hm : m ∈ M) (hm2 : m * m = z) (hamB : a * m ∈ B)
    (hBle : B ≤ Subgroup.closure ({c, z, a * m} : Set G))
    (hMj : modOdd c M ≤ secComp hΦ D j) (hmov : MovedByAll B c (secComp hΦ D j))
    (hLc : CFSG.IsComponent (secComp hΦ D j)) :
    alphaOf (inducedImage (secComp hΦ D j) (modOdd c B)) = ⊥ := by
  classical
  have hzC : z ∈ Subgroup.centralizer ({c} : Set G) :=
    Lemma52Proof.le_centralizer_of_mem hB hcB hzB
  have hM'j : modOdd c M' ≤ secComp hΦ D j :=
    modOdd_twin_le_secComp3 hΦ D hB hcB hc1 hzB hz1 hzc hzC hmov hLc hM' hzU'.mem
  have hk : ∃ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n : ℕ), IsFundTag t ∧
      CFSG.Assembly.LowTwoRank.StatedLieAdmissible t n 3 1 ∧ D.kind j = CompData.model t n := by
    rcases kind_of_isComponent_secComp hΦ D hLc with hk | hk
    · exact hk
    · exact absurd (Q3T6D.m11_twin_glue hΦ D hk hM hM' hMj hM'j hzU hzU') hne
  obtain ⟨R, R', x₁, x₁', hR, hR', hRR', hcommR, hx, hx2, hx1, hx', hx'2, hx'1, hsame, hRψ,
    hR'ψ, hψx₁⟩ := exists_twinData3 hΦ D hk hM hM' hzU hzU' hzC hMj hM'j hne hcomm
  have hN := normalizesLayer_of_secData3 hΦ
  have hker : (compHom3 hΦ D j).ker ≤ Subgroup.center (D.kind j).G :=
    Q3CH.ker_comp_le_center D (sectionQuotientHom hN) (sectionQuotientHom_injective hN) j
  set ψ := compHom3 hΦ D j with hψdef
  have haz : a * z = z * a := by rw [← ha2]; group
  have hx₁nc : ¬ ∀ y ∈ ψ.range, ψ x₁ * y = y * ψ x₁ := fun hall =>
    hx1 (model_fund_noncentral3 hk ψ hker hR hx hall)
  have hn : oddQuotMk c ⟨a, haC⟩ ∈ Subgroup.normalizer (ψ.range : Set (OddQuot c)) :=
    mem_normalizer_of_commute_noncentral hLc ⟨x₁, rfl⟩ hx₁nc
      (g := oddQuotMk c ⟨a, haC⟩) (by
        rw [hψx₁, ← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext haz)
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
  have hvv : v * v = toInducedAutOn ψ.range ⟨oddQuotMk c ⟨z, hzC⟩, hzn⟩ := by
    rw [hv, ← map_mul]
    congr 1
    exact Subtype.ext hxx
  have hvx : v * v = FrameVertex.innerHom ψ x₁ := by
    rw [hvv, FrameVertex.innerHom_apply]
    congr 1
    exact Subtype.ext hψx₁.symm
  have hmC : m ∈ Subgroup.centralizer ({c} : Set G) := hΦ.le M hM hm
  have hmMod : oddQuotMk c ⟨m, hmC⟩ ∈ modOdd c M := oddQuotMk_mem_modOdd hm hmC
  obtain ⟨k, hkR, hk'⟩ : ∃ k ∈ R, ψ k = oddQuotMk c ⟨m, hmC⟩ := by
    have : oddQuotMk c ⟨m, hmC⟩ ∈ R.map ψ := by
      rw [hRψ]
      exact hmMod
    exact Subgroup.mem_map.mp this
  have hkk : ψ k * ψ k = ψ x₁ := by
    rw [hk', hψx₁, ← map_mul]
    congr 1
    exact Subtype.ext hm2
  have key := alphaOf_eq_bot_of_twinSq_comp3 hrows hk ψ R R' x₁ x₁' hker hR hR' hRR' hcommR hx hx2
    hx1 hx' hx'2 hx'1 hsame hkR hkk v hvR hvR' hvx
  set T : Subgroup ↥(inducedAutOn ψ.range) :=
    Subgroup.closure ({FrameVertex.innerHom ψ k * v, FrameVertex.innerHom ψ x₁} :
      Set ↥(inducedAutOn ψ.range)) with hT
  have hcB' : c ∈ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hamC : a * m ∈ Subgroup.centralizer ({c} : Set G) := Subgroup.mul_mem _ haC hmC
  have hmn : oddQuotMk c ⟨m, hmC⟩ ∈ Subgroup.normalizer (ψ.range : Set (OddQuot c)) := by
    rw [← hk']
    exact hψnorm k
  have hamn : oddQuotMk c ⟨a * m, hamC⟩ ∈ Subgroup.normalizer (ψ.range : Set (OddQuot c)) := by
    have : oddQuotMk c ⟨a * m, hamC⟩ = oddQuotMk c ⟨a, haC⟩ * oddQuotMk c ⟨m, hmC⟩ :=
      map_mul (oddQuotMk c) (⟨a, haC⟩ : ↥(Subgroup.centralizer ({c} : Set G))) ⟨m, hmC⟩
    rw [this]
    exact Subgroup.mul_mem _ hn hmn
  have hamv : toInducedAutOn ψ.range ⟨oddQuotMk c ⟨a * m, hamC⟩, hamn⟩ =
      FrameVertex.innerHom ψ k * v := by
    rw [FrameVertex.innerHom_apply, hv, ← map_mul]
    congr 1
    refine Subtype.ext ?_
    show oddQuotMk c ⟨a * m, hamC⟩ = ψ k * oddQuotMk c ⟨a, haC⟩
    have hcm := hcommM _ hmMod
    calc oddQuotMk c ⟨a * m, hamC⟩ = oddQuotMk c ⟨a, haC⟩ * oddQuotMk c ⟨m, hmC⟩ :=
          map_mul (oddQuotMk c) (⟨a, haC⟩ : ↥(Subgroup.centralizer ({c} : Set G))) ⟨m, hmC⟩
      _ = oddQuotMk c ⟨m, hmC⟩ * oddQuotMk c ⟨a, haC⟩ := hcm
      _ = ψ k * oddQuotMk c ⟨a, haC⟩ := by rw [hk']
  have hBeq : B = Subgroup.closure ({c, z, a * m} : Set G) := by
    refine le_antisymm hBle ((Subgroup.closure_le _).mpr ?_)
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · exact hcB
    · exact hzB
    · exact hamB
  have hS : ({c, z, a * m} : Set G) ⊆ Subgroup.centralizer ({c} : Set G) := by
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · exact hcB'
    · exact hzC
    · exact hamC
  have hgen : ∀ s : G, s ∈ ({c, z, a * m} : Set G) →
      ∀ hs' : s ∈ Subgroup.centralizer ({c} : Set G),
      ∃ hn' : oddQuotMk c ⟨s, hs'⟩ ∈ Subgroup.normalizer (ψ.range : Set (OddQuot c)),
        toInducedAutOn ψ.range ⟨oddQuotMk c ⟨s, hs'⟩, hn'⟩ ∈ T := by
    intro s hs' hsC
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs'
    rcases hs' with hs' | hs' | hs'
    · subst s
      obtain ⟨hcn, hc1'⟩ := oddQuotSelf_induced c ψ.range
      refine ⟨hcn, ?_⟩
      have h1 : toInducedAutOn ψ.range ⟨oddQuotMk c ⟨c, hsC⟩, hcn⟩ = 1 := hc1'
      rw [h1]
      exact T.one_mem
    · subst s
      refine ⟨hzn, ?_⟩
      have h1 : toInducedAutOn ψ.range ⟨oddQuotMk c ⟨z, hsC⟩, hzn⟩ =
          FrameVertex.innerHom ψ x₁ := by
        rw [FrameVertex.innerHom_apply]
        congr 1
        exact Subtype.ext hψx₁.symm
      rw [h1]
      exact Subgroup.subset_closure (by simp)
    · subst s
      refine ⟨hamn, ?_⟩
      rw [hamv]
      exact Subgroup.subset_closure (by simp)
  have hle1 : inducedImage ψ.range (modOdd c B) ≤ T := by
    rw [hBeq]
    exact inducedImage_modOdd_closure_le hS ψ.range T (fun s hs'' => hgen s hs'' (hS hs''))
  have hle2 : T ≤ inducedImage ψ.range (modOdd c B) := by
    refine (Subgroup.closure_le _).mpr ?_
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with hg | hg
    · rw [hg, ← hamv]
      exact ⟨⟨oddQuotMk c ⟨a * m, hamC⟩, hamn⟩, Subgroup.mem_subgroupOf.mpr
        (oddQuotMk_mem_modOdd hamB hamC), rfl⟩
    · have hzmod : ψ x₁ ∈ modOdd c B := by
        rw [hψx₁]
        exact oddQuotMk_mem_modOdd hzB hzC
      rw [hg, FrameVertex.innerHom_apply]
      exact ⟨⟨ψ x₁, hψnorm x₁⟩, Subgroup.mem_subgroupOf.mpr hzmod, rfl⟩
  exact (congrArg alphaOf (le_antisymm hle1 hle2)).trans key

end Alpha

end CFSG.ClassicalInvolution.Q3.Q3T7
