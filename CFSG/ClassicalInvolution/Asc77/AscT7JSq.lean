module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15TwinU

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Disconnected
open CFSG.Open (IsElemAbelian classicalInvolutionOddCore)

section Model

@[expose] def TwinSqAlphaOn (t : StatedLieTag) (M : CFSG.LieType.Universal.LieUniversal) : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (ψ : M.K →* H) (R R' : Subgroup M.K) (x x' : M.K),
    TwinPairOn t M ψ R R' x x' → ∀ k ∈ R, ψ k * ψ k = ψ x →
      ∀ v : ↥(inducedAutOn ψ.range),
        (∀ r ∈ R, v * FrameVertex.innerHom ψ r = FrameVertex.innerHom ψ r * v) →
        (∀ r ∈ R', v * FrameVertex.innerHom ψ r = FrameVertex.innerHom ψ r * v) →
        v * v = FrameVertex.innerHom ψ x →
          alphaOf (Subgroup.closure ({FrameVertex.innerHom ψ k * v, FrameVertex.innerHom ψ x} :
            Set ↥(inducedAutOn ψ.range))) = ⊥

variable (p e : ℕ) [Fact p.Prime]

@[expose] def TwinSqAlpha (t : StatedLieTag) (n : ℕ) : Prop :=
  TwinSqAlphaOn t (CFSG.ClassicalInvolution.Generic.modelUniv t n p e Fact.out)

variable {e}

@[expose] def TwinSqAlphaRows : Prop :=
  p ≠ 2 → ∀ e : ℕ, 5 ≤ p ^ e → ∀ (t : StatedLieTag) (n : ℕ), StatedLieAdmissible t n p e →
    TwinShape t n → TwinSqAlpha p e t n

structure TwinSqRows : Prop where
  psp : p ≠ 2 → ∀ e, 5 ≤ p ^ e → StatedLieAdmissible .PSp 2 p e → TwinSqAlpha p e .PSp 2
  psl : p ≠ 2 → ∀ e, 5 ≤ p ^ e → StatedLieAdmissible .PSL 4 p e → TwinSqAlpha p e .PSL 4
  psu : p ≠ 2 → ∀ e, 5 ≤ p ^ e → StatedLieAdmissible .PSU 4 p e → TwinSqAlpha p e .PSU 4
  odd : p ≠ 2 → ∀ e, 5 ≤ p ^ e → ∀ n, 3 ≤ n → StatedLieAdmissible .POmegaOdd n p e →
    TwinSqAlpha p e .POmegaOdd n
  plus : p ≠ 2 → ∀ e, 5 ≤ p ^ e → ∀ n, 4 ≤ n → StatedLieAdmissible .POmegaPlus n p e →
    TwinSqAlpha p e .POmegaPlus n
  minus : p ≠ 2 → ∀ e, 5 ≤ p ^ e → ∀ n, 4 ≤ n → StatedLieAdmissible .POmegaMinus n p e →
    TwinSqAlpha p e .POmegaMinus n

theorem twinSqAlphaRows_of_rows (h : TwinSqRows p) : TwinSqAlphaRows p := by
  intro hp e hq t n hadm hsh
  rcases hsh with ⟨rfl, hn⟩ | ⟨rfl, hn⟩ | ⟨rfl, hn⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact h.odd hp e hq n hn hadm
  · exact h.plus hp e hq n hn hadm
  · exact h.minus hp e hq n hn hadm
  · exact h.psp hp e hq hadm
  · exact h.psl hp e hq hadm
  · exact h.psu hp e hq hadm

end Model

section Moved

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem alpha_of_twinSq (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hex : G2D4VertexExcl p f) (hA : ∀ M ∈ Ω, AEmpty Ω M) (hres : TwinSqAlphaRows p)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) {B : Subgroup G} (hB : IsElemAbelian 2 B)
    (hcB : c ∈ B) (hc1 : c ≠ 1) {z : G} (hzB : z ∈ B) (hz1 : z ≠ 1) (hzc : z ≠ c)
    {M M' : Subgroup G} (hM : M ∈ tqMembers Ω c) (hM' : M' ∈ tqMembers Ω c)
    (hMz : IsClassicalMember p f M z) (hM'z : IsClassicalMember p f M' z) (hne : M' ≠ M)
    {a m : G} (haC : a ∈ Subgroup.centralizer ({c} : Set G)) (ha2 : a * a = z)
    (haM : a ∈ trivialOnQuot M) (haM' : a ∈ trivialOnQuot M')
    (hm : m ∈ exactCore c M) (hm2 : m * m = z) (hamB : a * m ∈ B)
    (hBle : B ≤ Subgroup.closure ({c, z, a * m} : Set G))
    (D : LocalLieSystemAt p f (exactFamily Ω c) c) (j : Fin D.card)
    (hMj : modOdd c (exactCore c M) ≤
      (secComponentHom (normalizesLayer_exactFamily hΩ.conjInvariant) D j).range)
    (hmov : MovedByAll B c
      (secComponentHom (normalizesLayer_exactFamily hΩ.conjInvariant) D j).range)
    (hLcomp : CFSG.IsComponent
      (secComponentHom (normalizesLayer_exactFamily hΩ.conjInvariant) D j).range) :
    alphaOf (inducedImage
      (secComponentHom (normalizesLayer_exactFamily hΩ.conjInvariant) D j).range
      (modOdd c B)) = ⊥ := by
  have hM'j := vertexTwin_mem hΩ hc2 hB hcB hc1 hzB hz1 hzc hM hM' hM'z D j hmov
  have hG2 : D.tag j ≠ .G2 := fun h =>
    hex G Ω hΩ hA c hc2 D j (Or.inl h) M M' z hM hM' hMz hM'z hne hMj hM'j
  have hD4 : D.tag j ≠ .trialityD4 := fun h =>
    hex G Ω hΩ hA c hc2 D j (Or.inr h) M M' z hM hM' hMz hM'z hne hMj hM'j
  obtain ⟨hzC, R, R', x₁, x₁', hpair, hshape, hRM, hR'M, hψx₁⟩ := vertexTwin hp hq hΩ hc2 hB hcB
    hc1 hzB hz1 hzc hM hM' hMz hM'z hne D j hMj hmov hG2 hD4
  set ψ := secComponentHom (normalizesLayer_exactFamily hΩ.conjInvariant) D j with hψdef
  have hexp : D.exp j = f := (D.exp_eq j).resolve_right fun h => hD4 h.1
  have hq' : 5 ≤ p ^ D.exp j := by rw [hexp]; exact hq
  have hTO : TwinSqAlpha p (D.exp j) (D.tag j) (D.rank j) :=
    hres hp (D.exp j) hq' (D.tag j) (D.rank j) (D.admissible j) hshape
  have hnA1 := hshape.not_A1
  have hker := secComponentHom_ker_le_center (normalizesLayer_exactFamily hΩ.conjInvariant) D j
  have hqs : ∀ R₀ : Subgroup (compModel D j).K,
      R₀ ∈ fundamentalSubgroups (D.tag j) (compModel D j).D →
        CFSG.Open.IsQuasisimple ↥(R₀.map ψ) := fun R₀ hR₀ =>
    isQuasisimple_map_of_ker_le_center ψ hker
      (fundQuasisimple_core hp (D.isFundTag j) (D.admissible j) (by omega) R₀ hR₀)
  have hqM : CFSG.Open.IsQuasisimple ↥(modOdd c (exactCore c M)) := by
    rw [← hRM]
    exact hqs R hpair.mem
  have hqM' : CFSG.Open.IsQuasisimple ↥(modOdd c (exactCore c M')) := by
    rw [← hR'M]
    exact hqs R' hpair.mem'
  have hcommM := oddQuotMk_centralizes_modOdd_exactCore hMz hc2 hM.2 haM haC hqM
  have hcommM' := oddQuotMk_centralizes_modOdd_exactCore hM'z hc2 hM'.2 haM' haC hqM'
  have haz : a * z = z * a := by rw [← ha2]; group
  have hx₁nc : ¬ ∀ y ∈ ψ.range, ψ x₁ * y = y * ψ x₁ := by
    intro hall
    have hcen : ∀ w : (compModel D j).K,
        x₁ * w * x₁⁻¹ * w⁻¹ ∈ Subgroup.center (compModel D j).K := by
      intro w
      apply hker
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv]
      have h1 := hall (ψ w) ⟨w, rfl⟩
      calc ψ x₁ * ψ w * (ψ x₁)⁻¹ * (ψ w)⁻¹ = (ψ x₁ * ψ w) * (ψ x₁)⁻¹ * (ψ w)⁻¹ := rfl
        _ = (ψ w * ψ x₁) * (ψ x₁)⁻¹ * (ψ w)⁻¹ := by rw [h1]
        _ = 1 := by group
    exact hpair.hx1 (CFSG.ClassicalInvolution.ModelFacts.fundNoncentral_generic p (D.tag j)
      (D.rank j) (D.exp j) (D.isFundTag j) (D.admissible j) hnA1 R hpair.mem x₁ hpair.hx hcen)
  have hn : oddQuotMk c ⟨a, haC⟩ ∈ Subgroup.normalizer (ψ.range : Set (OddQuot c)) :=
    mem_normalizer_of_commute_noncentral hLcomp ⟨x₁, rfl⟩ hx₁nc
      (g := oddQuotMk c ⟨a, haC⟩) (by
        rw [hψx₁, ← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext haz)
  have hψnorm : ∀ w : (compModel D j).K,
      ψ w ∈ Subgroup.normalizer (ψ.range : Set (OddQuot c)) :=
    FrameVertex.mem_normalizer_range ψ
  set v : ↥(inducedAutOn ψ.range) :=
    toInducedAutOn ψ.range ⟨oddQuotMk c ⟨a, haC⟩, hn⟩ with hv
  have hvR : ∀ r ∈ R, v * FrameVertex.innerHom ψ r = FrameVertex.innerHom ψ r * v := by
    intro r hr
    rw [FrameVertex.innerHom_apply, hv, ← map_mul, ← map_mul]
    have hr' : ψ r ∈ modOdd c (exactCore c M) := hRM ▸ Subgroup.mem_map_of_mem ψ hr
    congr 1
    exact Subtype.ext (hcommM (ψ r) hr')
  have hvR' : ∀ r ∈ R', v * FrameVertex.innerHom ψ r = FrameVertex.innerHom ψ r * v := by
    intro r hr
    rw [FrameVertex.innerHom_apply, hv, ← map_mul, ← map_mul]
    have hr' : ψ r ∈ modOdd c (exactCore c M') := hR'M ▸ Subgroup.mem_map_of_mem ψ hr
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
  have hmC : m ∈ Subgroup.centralizer ({c} : Set G) := exactCore_le_centralizer c M hm
  have hmMod : oddQuotMk c ⟨m, hmC⟩ ∈ modOdd c (exactCore c M) :=
    oddQuotMk_mem_modOdd hm hmC
  obtain ⟨k, hkR, hk⟩ : ∃ k ∈ R, ψ k = oddQuotMk c ⟨m, hmC⟩ := by
    have : oddQuotMk c ⟨m, hmC⟩ ∈ R.map ψ := by
      rw [hRM]
      exact hmMod
    exact Subgroup.mem_map.mp this
  have hkk : ψ k * ψ k = ψ x₁ := by
    rw [hk, hψx₁, ← map_mul]
    congr 1
    exact Subtype.ext hm2
  have key := hTO (OddQuot c) ψ R R' x₁ x₁' hpair k hkR hkk v hvR hvR' hvx
  set T : Subgroup ↥(inducedAutOn ψ.range) :=
    Subgroup.closure ({FrameVertex.innerHom ψ k * v, FrameVertex.innerHom ψ x₁} :
      Set ↥(inducedAutOn ψ.range)) with hT
  have hcB' : c ∈ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hamC : a * m ∈ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.mul_mem _ haC hmC
  have hmn : oddQuotMk c ⟨m, hmC⟩ ∈ Subgroup.normalizer (ψ.range : Set (OddQuot c)) := by
    rw [← hk]
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
      _ = ψ k * oddQuotMk c ⟨a, haC⟩ := by rw [hk]
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
  have hgen : ∀ s : G, s ∈ ({c, z, a * m} : Set G) → ∀ hs' : s ∈ Subgroup.centralizer ({c} : Set G),
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

end Moved

end CFSG.ClassicalInvolution.Asc77
