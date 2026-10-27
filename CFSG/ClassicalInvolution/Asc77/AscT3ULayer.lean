module

public import CFSG.ClassicalInvolution.Asc77.AscT3UG2D4
public import CFSG.ClassicalInvolution.Asc77.AscE187Img
public import CFSG.ClassicalInvolution.Asc77.WP3FrameChain
public import CFSG.ClassicalInvolution.ModelFacts.Orth15TwinT

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T3CII.T3U

open CFSG CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Disconnected
open CFSG.Open (IsElemAbelian classicalInvolutionOddCore IsSubnormal)
open scoped commutatorElement

section Induced

variable {H : Type} [Group H]

omit [Group H] in
theorem inducedImage_mono [Group H] (L : Subgroup H) {A₁ A₂ : Subgroup H} (h : A₁ ≤ A₂) :
    inducedImage L A₁ ≤ inducedImage L A₂ :=
  Subgroup.map_mono fun _ hx => h hx

end Induced

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)}

theorem hyp51At_of_twin_layer (hres : TwinSmallInner p) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmegaMod p f Ω) (hBelow : CITBelowU p f (Nat.card G))
    {K K' : Subgroup G} {b d c : G}
    (hKΩ : K ∈ Ω) (hK'Ω : K' ∈ Ω) (hne : K' ≠ K)
    (hbK : IsUniqueInvolution K b) (hbK' : IsUniqueInvolution K' b)
    (hMK : K ∈ tqMembers Ω c) (hMK' : K' ∈ tqMembers Ω c)
    {B : Subgroup G} (hB : IsElemAbelian 2 B) (hbB : b ∈ B) (hdB : d ∈ B) (hcB : c ∈ B)
    (hBgen : B = Subgroup.closure ({b, d, c} : Set G))
    (hc1 : c ≠ 1) (hbc : b ≠ c) (hd1 : d ≠ 1) (hdb : d ≠ b) (hd2 : d * d = 1)
    (hdsup : d ∈ exactCore c K ⊔ exactCore c K') :
    Hyp51At B c := by
  have hcK : IsClassicalMember p f K b := isClassicalMember_of_twin hΩ hKΩ hbK
  have hcK' : IsClassicalMember p f K' b := isClassicalMember_of_twin hΩ hK'Ω hbK'
  have hc2 : IsPGroup 2 (Subgroup.zpowers c) :=
    isPGroup_zpowers_of_sq_eq_one (by simpa only [pow_two] using hB.2 c hcB)
  have hnonab : ∃ x y : G, x * y ≠ y * x := exists_noncomm_of_isClassicalMember hcK
  have hnc : ¬ ({c} : Set G) ⊆ Subgroup.center G :=
    Balance.not_subset_center_of_ne_one hnonab hc1
  have hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    DeltaClosure.comm_of_mem_elemAbelian hB hx hy
  refine FrameVertex.hyp51At_of_witness_alpha hp hq hΩ.conjInvariant hΩ.classical
    hBelow hc2 hnc hB hcB hc1 hbB hbK.ne_one hbc hMK hcK ?_
  intro D j hMj hmov
  have hM'j := vertexTwin_mem hΩ hc2 hB hcB hc1 hbB hbK.ne_one hbc hMK hMK' hcK' D j hmov
  set ψ := secComponentHom (normalizesLayer_exactFamily hΩ.conjInvariant) D j with hψdef
  have hbC : b ∈ Subgroup.centralizer ({c} : Set G) :=
    Lemma52Proof.le_centralizer_of_mem hB hcB hbB
  have huC : d ∈ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm d hdB c hcB)
  have hu2 : oddQuotMk c ⟨d, huC⟩ * oddQuotMk c ⟨d, huC⟩ = 1 := by
    rw [← map_mul]
    have : (⟨d, huC⟩ * ⟨d, huC⟩ : ↥(Subgroup.centralizer ({c} : Set G))) = 1 := Subtype.ext hd2
    rw [this, map_one]
  have hu1 : oddQuotMk c ⟨d, huC⟩ ≠ 1 := by
    intro h
    have h' : oddQuotMk c ⟨d, huC⟩ = oddQuotMk c ⟨1, Subgroup.one_mem _⟩ := by
      rw [h]
      exact (map_one _).symm
    exact hd1 (eq_of_oddQuotMk_eq hB hdB (Subgroup.one_mem _) huC (Subgroup.one_mem _) h')
  have hψnorm : ∀ y : (compModel D j).K, ψ y ∈ Subgroup.normalizer (ψ.range : Set (OddQuot c)) :=
    FrameVertex.mem_normalizer_range ψ
  have hS : ({b, d, c} : Set G) ⊆ Subgroup.centralizer ({c} : Set G) := by
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with hg | hg | hg
    · rw [hg]; exact hbC
    · rw [hg]; exact huC
    · rw [hg]; exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hbmem : oddQuotMk c ⟨b, hbC⟩ ∈ modOdd c (exactCore c K) :=
    oddQuotMk_mem_modOdd (mem_exactCore hcK hc2 hMK.2) hbC
  have hsup : oddQuotMk c ⟨d, huC⟩ ∈ modOdd c (exactCore c K) ⊔ modOdd c (exactCore c K') :=
    TwinVertex.oddQuotMk_mem_sup (exactCore_le_centralizer c K)
      (exactCore_le_centralizer c K') hdsup huC
  by_cases hg : D.tag j = .G2 ∨ D.tag j = .trialityD4
  ·
    have hb2 : oddQuotMk c ⟨b, hbC⟩ * oddQuotMk c ⟨b, hbC⟩ = 1 := by
      rw [← map_mul]
      have : (⟨b, hbC⟩ * ⟨b, hbC⟩ : ↥(Subgroup.centralizer ({c} : Set G))) = 1 :=
        Subtype.ext hbK.sq
      rw [this, map_one]
    have hb1 : oddQuotMk c ⟨b, hbC⟩ ≠ 1 := by
      intro h
      have h' : oddQuotMk c ⟨b, hbC⟩ = oddQuotMk c ⟨1, Subgroup.one_mem _⟩ := by
        rw [h]
        exact (map_one _).symm
      exact hbK.ne_one (eq_of_oddQuotMk_eq hB hbB (Subgroup.one_mem _) hbC (Subgroup.one_mem _) h')
    have hbd : oddQuotMk c ⟨b, hbC⟩ ≠ oddQuotMk c ⟨d, huC⟩ := fun h =>
      hdb (eq_of_oddQuotMk_eq hB hdB hbB huC hbC h.symm)
    have hbdc : oddQuotMk c ⟨b, hbC⟩ * oddQuotMk c ⟨d, huC⟩ =
        oddQuotMk c ⟨d, huC⟩ * oddQuotMk c ⟨b, hbC⟩ := by
      rw [← map_mul, ← map_mul]
      exact congrArg _ (Subtype.ext (hcomm b hbB d hdB))
    have hD := T7A.isElemAbelian2_closure_pair hb2 hu2 hb1 hu1 hbd hbdc
    set A : Subgroup (OddQuot c) :=
      Subgroup.closure ({oddQuotMk c ⟨b, hbC⟩, oddQuotMk c ⟨d, huC⟩} : Set (OddQuot c)) with hA
    have hbmemR : oddQuotMk c ⟨b, hbC⟩ ∈ ψ.range := hMj hbmem
    have hdmemR : oddQuotMk c ⟨d, huC⟩ ∈ ψ.range := (sup_le hMj hM'j) hsup
    have hAL : A ≤ ψ.range := by
      rw [hA, Subgroup.closure_le]
      intro g hg'
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg'
      rcases hg' with rfl | rfl
      · exact hbmemR
      · exact hdmemR
    have hAN : A ≤ Subgroup.normalizer (ψ.range : Set (OddQuot c)) := fun x hx =>
      Subgroup.le_normalizer (hAL hx)
    have key : alphaOf (inducedImage ψ.range A) = ⊥ :=
      alphaOf_inducedImage_eq_bot_of_g2d4 hp hq hg (D.isFundTag j) (D.admissible j)
        (D.exp_eq j) ψ (secComponentHom_ker_le_center _ D j) hD.1 hD.2 hAL
    refine (congrArg alphaOf (le_antisymm ?_ ?_)).trans key
    · rw [hBgen]
      have hgen : ∀ s : G, s ∈ ({b, d, c} : Set G) → ∀ hs' : s ∈ Subgroup.centralizer ({c} : Set G),
          ∃ hn : oddQuotMk c ⟨s, hs'⟩ ∈ Subgroup.normalizer (ψ.range : Set (OddQuot c)),
            toInducedAutOn ψ.range ⟨oddQuotMk c ⟨s, hs'⟩, hn⟩ ∈ inducedImage ψ.range A := by
        intro s hs hs'
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
        rcases hs with hs | hs | hs
        · subst s
          have hn : oddQuotMk c ⟨b, hs'⟩ ∈ Subgroup.normalizer (ψ.range : Set (OddQuot c)) :=
            Subgroup.le_normalizer hbmemR
          refine ⟨hn, ⟨⟨oddQuotMk c ⟨b, hs'⟩, hn⟩, Subgroup.mem_subgroupOf.mpr ?_, rfl⟩⟩
          exact Subgroup.subset_closure (by simp)
        · subst s
          have hn : oddQuotMk c ⟨d, hs'⟩ ∈ Subgroup.normalizer (ψ.range : Set (OddQuot c)) :=
            Subgroup.le_normalizer hdmemR
          refine ⟨hn, ⟨⟨oddQuotMk c ⟨d, hs'⟩, hn⟩, Subgroup.mem_subgroupOf.mpr ?_, rfl⟩⟩
          exact Subgroup.subset_closure (by simp)
        · subst s
          obtain ⟨hcn, hc1'⟩ := oddQuotSelf_induced c ψ.range
          have h1 : oddQuotMk c ⟨c, hs'⟩ = Lemma52Proof.oddQuotSelf c := rfl
          refine ⟨by rw [h1]; exact hcn, ?_⟩
          have h2 : (⟨oddQuotMk c ⟨c, hs'⟩, by rw [h1]; exact hcn⟩ :
              ↥(Subgroup.normalizer (ψ.range : Set (OddQuot c)))) =
                ⟨Lemma52Proof.oddQuotSelf c, hcn⟩ := Subtype.ext h1
          rw [h2, hc1']
          exact Subgroup.one_mem _
      exact inducedImage_modOdd_closure_le hS ψ.range (inducedImage ψ.range A)
        (fun s hs => hgen s hs (hS hs))
    · refine inducedImage_mono ψ.range ?_
      rw [hA, Subgroup.closure_le]
      intro g hg'
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg'
      rcases hg' with rfl | rfl
      · exact oddQuotMk_mem_modOdd (hBgen ▸ Subgroup.subset_closure (by simp)) hbC
      · exact oddQuotMk_mem_modOdd (hBgen ▸ Subgroup.subset_closure (by simp)) huC
  ·
    have hG2 : D.tag j ≠ .G2 := fun h => hg (Or.inl h)
    have hD4 : D.tag j ≠ .trialityD4 := fun h => hg (Or.inr h)
    obtain ⟨hzC, R, R', x, x', hpair, hshape, hRM, hR'M, hψx⟩ := vertexTwin hp hq hΩ hc2 hB
      hcB hc1 hbB hbK.ne_one hbc hMK hMK' hcK hcK' hne D j hMj hmov hG2 hD4
    have hexp : D.exp j = f := (D.exp_eq j).resolve_right fun h => hD4 h.1
    have hq' : 5 ≤ p ^ D.exp j := by rw [hexp]; exact hq
    have hTI : TwinInnerAlpha p (D.exp j) (D.tag j) (D.rank j) :=
      twinInnerAlpha_of_shape hres hp hq' (D.admissible j) hshape
    have hsup' : oddQuotMk c ⟨d, huC⟩ ∈ R.map ψ ⊔ R'.map ψ := by
      rw [hRM, hR'M]
      exact hsup
    have hun : oddQuotMk c ⟨d, huC⟩ ∈ Subgroup.normalizer (ψ.range : Set (OddQuot c)) :=
      Subgroup.le_normalizer
        (sup_le (Subgroup.map_le_range ψ R) (Subgroup.map_le_range ψ R') hsup')
    have huz : oddQuotMk c ⟨d, huC⟩ ≠ ψ x := by
      rw [hψx]
      intro h
      exact hdb (eq_of_oddQuotMk_eq hB hdB hbB huC hzC h)
    have key := hTI (OddQuot c) ψ R R' x x' hpair (oddQuotMk c ⟨d, huC⟩) hun hsup' hu2 hu1 huz
    set T : Subgroup ↥(inducedAutOn ψ.range) := Subgroup.closure
      ({toInducedAutOn ψ.range ⟨oddQuotMk c ⟨d, huC⟩, hun⟩,
        toInducedAutOn ψ.range ⟨ψ x, hψnorm x⟩} : Set ↥(inducedAutOn ψ.range)) with hT
    have hbbar : oddQuotMk c ⟨b, hzC⟩ = ψ x := hψx.symm
    have hgen : ∀ s : G, s ∈ ({b, d, c} : Set G) → ∀ hs' : s ∈ Subgroup.centralizer ({c} : Set G),
        ∃ hn : oddQuotMk c ⟨s, hs'⟩ ∈ Subgroup.normalizer (ψ.range : Set (OddQuot c)),
          toInducedAutOn ψ.range ⟨oddQuotMk c ⟨s, hs'⟩, hn⟩ ∈ T := by
      intro s hs hs'
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
      rcases hs with hs | hs | hs
      · subst s
        refine ⟨by rw [hbbar]; exact hψnorm x, ?_⟩
        have h2 : (⟨oddQuotMk c ⟨b, hs'⟩, by rw [hbbar]; exact hψnorm x⟩ :
            ↥(Subgroup.normalizer (ψ.range : Set (OddQuot c)))) = ⟨ψ x, hψnorm x⟩ :=
          Subtype.ext hbbar
        rw [h2]
        exact Subgroup.subset_closure (by simp)
      · subst s
        exact ⟨hun, Subgroup.subset_closure (by simp)⟩
      · subst s
        obtain ⟨hcn, hc1'⟩ := oddQuotSelf_induced c ψ.range
        have h1 : oddQuotMk c ⟨c, hs'⟩ = Lemma52Proof.oddQuotSelf c := rfl
        refine ⟨by rw [h1]; exact hcn, ?_⟩
        have h2 : (⟨oddQuotMk c ⟨c, hs'⟩, by rw [h1]; exact hcn⟩ :
            ↥(Subgroup.normalizer (ψ.range : Set (OddQuot c)))) =
              ⟨Lemma52Proof.oddQuotSelf c, hcn⟩ := Subtype.ext h1
        rw [h2, hc1']
        exact T.one_mem
    have hψxB : ψ x ∈ modOdd c B := by
      rw [hψx]
      exact oddQuotMk_mem_modOdd hbB hzC
    rw [hBgen] at hψxB
    refine (congrArg alphaOf (le_antisymm ?_ ?_)).trans key
    · rw [hBgen]
      exact inducedImage_modOdd_closure_le hS ψ.range T (fun s hs => hgen s hs (hS hs))
    · refine (Subgroup.closure_le _).mpr ?_
      intro g hg'
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg'
      rcases hg' with hg' | hg'
      · rw [hg']
        exact ⟨⟨oddQuotMk c ⟨d, huC⟩, hun⟩,
          Subgroup.mem_subgroupOf.mpr (oddQuotMk_mem_modOdd hdB huC), rfl⟩
      · rw [hg']
        exact ⟨⟨ψ x, hψnorm x⟩, Subgroup.mem_subgroupOf.mpr (by rw [hBgen] at *; exact hψxB),
          rfl⟩

end CFSG.ClassicalInvolution.Asc77.T3CII.T3U
