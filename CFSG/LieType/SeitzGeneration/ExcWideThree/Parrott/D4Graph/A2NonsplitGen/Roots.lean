module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2Split.Orbit

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2NonsplitGen

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.CTP
  CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Lang.D4Three
  CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

local notation "𝕩" => xPar (rootOperatorFamily Tag.D4)

@[expose] def rootF0 : Fin Tag.D4.rank → ℤ := ![1, 0, 1, 0]

@[expose] def rootF1 : Fin Tag.D4.rank → ℤ := ![0, 1, 1, 0]

@[expose] def rootF3 : Fin Tag.D4.rank → ℤ := ![0, 0, 1, 1]

@[expose] def rootB1 : Fin Tag.D4.rank → ℤ := ![1, 1, 1, 0]

@[expose] def rootB2 : Fin Tag.D4.rank → ℤ := ![1, 0, 1, 1]

@[expose] def rootB3 : Fin Tag.D4.rank → ℤ := ![0, 1, 1, 1]

section Comm


variable {K : Type} [Field K]

theorem eq_one_of_isRoot_nsmul_add_nsmul {γ δ : Fin Tag.D4.rank → ℤ} (hγ : IsRoot Tag.D4 γ)
    (hδ : IsRoot Tag.D4 δ) (hne : γ ≠ δ) (hne' : γ ≠ -δ) {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (h : IsRoot Tag.D4 (m • γ + n • δ)) : m = 1 ∧ n = 1 := by
  have h2 : ∀ {ε : Fin Tag.D4.rank → ℤ}, IsRoot Tag.D4 ε → iform ε ε = 2 := fun hε => by
    obtain ⟨k, hk⟩ := iform_self_of_isRoot hε
    rw [hk]
    clear hk
    revert k
    decide
  rcases exponent_pair_cases (τ := Tag.D4) CFSG.LieType.Steinberg.TwistedD4.noG2_D4 hγ hδ hne hne'
    hm hn h with h' | ⟨-, -, h4, -⟩ | ⟨-, -, -, h4, -⟩
  · exact h'
  · rw [h2 hγ] at h4
    omega
  · rw [h2 hδ] at h4
    omega

theorem commutator_xPar_mem_rootGroup {γ δ : Fin Tag.D4.rank → ℤ} (hγ : IsRoot Tag.D4 γ)
    (hδ : IsRoot Tag.D4 δ) (hne : γ ≠ -δ) (a b : K) :
    ⁅𝕩 γ a, 𝕩 δ b⁆ ∈ rootGroup (rootOperatorFamily Tag.D4) K (γ + δ) := by
  by_cases hγδ : γ = δ
  · subst hγδ
    have hc : Commute (𝕩 γ a) (𝕩 γ b) := by
      rw [Commute, SemiconjBy, ← xPar_add, ← xPar_add, add_comm]
    rw [commutatorElement_eq_one_iff_commute.2 hc]
    exact Subgroup.one_mem _
  have hlin : CFSG.LieType.Steinberg.LinIndepPair γ δ := by
    by_contra h
    rcases CFSG.LieType.Steinberg.TagRoots.eq_or_eq_neg_of_not_linIndepPair hγ hδ h with h' | h'
    exacts [hγδ h', hne h']
  have key := commutator_mem_openCone_of_linIndepPair hγ hδ hlin (xPar_mem hγ a) (xPar_mem hδ b)
  have hle : (⨆ ε ∈ CFSG.LieType.Steinberg.openCone
      (adjDatum (rootOperatorFamily Tag.D4) K).roots γ δ,
        (adjDatum (rootOperatorFamily Tag.D4) K).rootGroup ε) ≤
      rootGroup (rootOperatorFamily Tag.D4) K (γ + δ) := by
    refine iSup₂_le fun ε hε => ?_
    obtain ⟨hεr, m, n, hm, hn, hεe⟩ := hε
    rw [mem_adjDatum_roots, hεe] at hεr
    obtain ⟨rfl, rfl⟩ := eq_one_of_isRoot_nsmul_add_nsmul hγ hδ hγδ hne hm hn hεr
    rw [hεe, one_smul, one_smul]
  exact hle key

theorem exists_commutator_xPar_eq {γ δ : Fin Tag.D4.rank → ℤ} (hγ : IsRoot Tag.D4 γ)
    (hδ : IsRoot Tag.D4 δ) (hne : γ ≠ -δ) (hsum : IsRoot Tag.D4 (γ + δ)) (a b : K) :
    ∃ d : K, ⁅𝕩 γ a, 𝕩 δ b⁆ = 𝕩 (γ + δ) d := by
  obtain ⟨d, hd⟩ := (mem_rootGroup_iff hsum _).1 (commutator_xPar_mem_rootGroup hγ hδ hne a b)
  exact ⟨d, hd.symm⟩

theorem commutator_xPar_eq_one {γ δ : Fin Tag.D4.rank → ℤ} (hγ : IsRoot Tag.D4 γ)
    (hδ : IsRoot Tag.D4 δ) (hne : γ ≠ -δ) (hsum : ¬IsRoot Tag.D4 (γ + δ)) (a b : K) :
    ⁅𝕩 γ a, 𝕩 δ b⁆ = 1 := by
  have h := commutator_xPar_mem_rootGroup hγ hδ hne a b
  rwa [rootGroup_of_not_isRoot hsum, Subgroup.mem_bot] at h

theorem commute_xPar_of_not_isRoot {γ δ : Fin Tag.D4.rank → ℤ} (hγ : IsRoot Tag.D4 γ)
    (hδ : IsRoot Tag.D4 δ) (hne : γ ≠ -δ) (hsum : ¬IsRoot Tag.D4 (γ + δ)) (a b : K) :
    Commute (𝕩 γ a) (𝕩 δ b) :=
  commutatorElement_eq_one_iff_commute.1 (commutator_xPar_eq_one hγ hδ hne hsum a b)

theorem xPar_pow (γ : Fin Tag.D4.rank → ℤ) (c : K) (n : ℕ) : 𝕩 γ c ^ n = 𝕩 γ (n * c) := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero, zero_mul, xPar_zero]
  | succ n ih => rw [pow_succ, ih, ← xPar_add, Nat.cast_succ, add_one_mul]

theorem commutator_eq_of_repCheck {a b g : ℕ} {C : ℤ} {γ δ ε : Fin Tag.D4.rank → ℤ}
    (hγ : (Tag.rootCertificate Tag.D4).root a = γ) (hδ : (Tag.rootCertificate Tag.D4).root b = δ)
    (hε : (Tag.rootCertificate Tag.D4).root g = ε)
    (h : RootOps.repCheck Tag.D4 a b [(1, 1, g, C)] = true) (s t : K) :
    ⁅𝕩 γ s, 𝕩 δ t⁆ = 𝕩 ε (C * s * t) := by
  have key := CFSG.Timmesfeld.RankTwo.commutator_xPar_of_repCheck (τ := Tag.D4) (K := K) h s t
  rw [hγ, hδ] at key
  rw [key]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pow_one, hε]

theorem xPar_mem_of_repCheck {H : Subgroup ↥(adjointGroup Tag.D4 K)} {a b g : ℕ} {C : ℤ}
    {γ δ ε : Fin Tag.D4.rank → ℤ} (hγ : (Tag.rootCertificate Tag.D4).root a = γ)
    (hδ : (Tag.rootCertificate Tag.D4).root b = δ) (hε : (Tag.rootCertificate Tag.D4).root g = ε)
    (hC : C = 1 ∨ C = -1) (h : RootOps.repCheck Tag.D4 a b [(1, 1, g, C)] = true)
    (hγH : ∀ c, 𝕩 γ c ∈ H) (hδH : ∀ c, 𝕩 δ c ∈ H) (c : K) : 𝕩 ε c ∈ H := by
  have hmem : ⁅𝕩 γ (C * c), 𝕩 δ 1⁆ ∈ H := by
    rw [commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem (hγH _) (hδH _)) (H.inv_mem (hγH _))) (H.inv_mem (hδH _))
  rw [commutator_eq_of_repCheck hγ hδ hε h] at hmem
  have e : (C : K) * ((C : K) * c) * 1 = c := by
    rcases hC with rfl | rfl <;> push_cast <;> ring
  rwa [e] at hmem

variable (K) in
@[expose] noncomputable def spanRoots (S : List (Fin Tag.D4.rank → ℤ)) :
    Subgroup ↥(adjointGroup Tag.D4 K) :=
  Subgroup.closure {g | ∃ s ∈ S, ∃ c : K, g = 𝕩 s c}

theorem xPar_mem_spanRoots {S : List (Fin Tag.D4.rank → ℤ)} {s : Fin Tag.D4.rank → ℤ}
    (hs : s ∈ S) (c : K) : 𝕩 s c ∈ spanRoots K S :=
  Subgroup.subset_closure ⟨s, hs, c, rfl⟩

theorem spanRoots_le {S : List (Fin Tag.D4.rank → ℤ)} {H : Subgroup ↥(adjointGroup Tag.D4 K)}
    (h : ∀ s ∈ S, ∀ c : K, 𝕩 s c ∈ H) : spanRoots K S ≤ H := by
  rw [spanRoots, Subgroup.closure_le]
  rintro _ ⟨s, hs, c, rfl⟩
  exact h s hs c

theorem spanRoots_mono {S S' : List (Fin Tag.D4.rank → ℤ)} (h : ∀ s ∈ S, s ∈ S') :
    spanRoots K S ≤ spanRoots K S' :=
  spanRoots_le fun s hs c => xPar_mem_spanRoots (h s hs) c

theorem commutator_xPar_mem_spanRoots {r s : Fin Tag.D4.rank → ℤ} {S : List (Fin Tag.D4.rank → ℤ)}
    (hr : IsRoot Tag.D4 r) (hs : IsRoot Tag.D4 s) (hne : r ≠ -s)
    (hsum : IsRoot Tag.D4 (r + s) → r + s ∈ S) (a b : K) : ⁅𝕩 r a, 𝕩 s b⁆ ∈ spanRoots K S := by
  by_cases h : IsRoot Tag.D4 (r + s)
  · obtain ⟨d, hd⟩ := exists_commutator_xPar_eq hr hs hne h a b
    rw [hd]
    exact xPar_mem_spanRoots (hsum h) d
  · rw [commutator_xPar_eq_one hr hs hne h]
    exact Subgroup.one_mem _

theorem conj_xPar_mem_spanRoots {r s : Fin Tag.D4.rank → ℤ} {S : List (Fin Tag.D4.rank → ℤ)}
    (hr : IsRoot Tag.D4 r) (hs : IsRoot Tag.D4 s) (hsS : s ∈ S) (hne : r ≠ -s)
    (hsum : IsRoot Tag.D4 (r + s) → r + s ∈ S) (t c : K) :
    𝕩 r t * 𝕩 s c * (𝕩 r t)⁻¹ ∈ spanRoots K S := by
  have e : 𝕩 r t * 𝕩 s c * (𝕩 r t)⁻¹ = ⁅𝕩 r t, 𝕩 s c⁆ * 𝕩 s c := by
    rw [commutatorElement_def]
    group
  rw [e]
  exact (spanRoots K S).mul_mem (commutator_xPar_mem_spanRoots hr hs hne hsum t c)
    (xPar_mem_spanRoots hsS c)

theorem conj_mem_spanRoots {r : Fin Tag.D4.rank → ℤ} {S : List (Fin Tag.D4.rank → ℤ)}
    (hr : IsRoot Tag.D4 r)
    (hS : ∀ s ∈ S, IsRoot Tag.D4 s ∧ r ≠ -s ∧ (IsRoot Tag.D4 (r + s) → r + s ∈ S)) (t : K)
    {g : ↥(adjointGroup Tag.D4 K)} (hg : g ∈ spanRoots K S) :
    𝕩 r t * g * (𝕩 r t)⁻¹ ∈ spanRoots K S := by
  have h : (spanRoots K S).map (MulAut.conj (𝕩 r t)).toMonoidHom ≤ spanRoots K S := by
    rw [spanRoots, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨s, hs, c, rfl⟩, rfl⟩
    obtain ⟨hsr, hne, hsum⟩ := hS s hs
    exact conj_xPar_mem_spanRoots hr hsr hs hne hsum t c
  exact h ⟨g, hg, rfl⟩

theorem xPar_mem_normalizer_spanRoots {r : Fin Tag.D4.rank → ℤ} {S : List (Fin Tag.D4.rank → ℤ)}
    (hr : IsRoot Tag.D4 r)
    (hS : ∀ s ∈ S, IsRoot Tag.D4 s ∧ r ≠ -s ∧ (IsRoot Tag.D4 (r + s) → r + s ∈ S)) (t : K) :
    𝕩 r t ∈ Subgroup.normalizer (spanRoots K S : Set ↥(adjointGroup Tag.D4 K)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨fun hg => conj_mem_spanRoots hr hS t hg, fun hg => ?_⟩
  have e : g = 𝕩 r (-t) * (𝕩 r t * g * (𝕩 r t)⁻¹) * (𝕩 r (-t))⁻¹ := by
    rw [← xPar_neg]
    group
  rw [e]
  exact conj_mem_spanRoots hr hS (-t) hg

end Comm

section Graph


variable {K : Type} [Field K]

theorem sl2At_two_mem_normalizer {H : Subgroup ↥(adjointGroup Tag.D4 K)}
    (h1 : ∀ t : K, 𝕩 (Pi.single ⟨2, by decide⟩ 1) t ∈
      Subgroup.normalizer (H : Set ↥(adjointGroup Tag.D4 K)))
    (h2 : ∀ t : K, 𝕩 (-Pi.single ⟨2, by decide⟩ 1) t ∈
      Subgroup.normalizer (H : Set ↥(adjointGroup Tag.D4 K))) (A : SL2 K) :
    sl2At K ⟨2, by decide⟩ A ∈ Subgroup.normalizer (H : Set ↥(adjointGroup Tag.D4 K)) := by
  set N := (Subgroup.normalizer (H : Set ↥(adjointGroup Tag.D4 K))).comap (sl2At K ⟨2, by decide⟩)
  have hN : N = ⊤ := by
    rw [eq_top_iff, ← sl2_closure_upper_lower, Subgroup.closure_le]
    rintro _ (⟨t, rfl⟩ | ⟨t, rfl⟩)
    · show sl2At K ⟨2, by decide⟩ (uSL t) ∈ Subgroup.normalizer (H : Set ↥(adjointGroup Tag.D4 K))
      rw [← xPar_single_eq_sl2At]
      exact h1 t
    · show sl2At K ⟨2, by decide⟩ (vSL t) ∈ Subgroup.normalizer (H : Set ↥(adjointGroup Tag.D4 K))
      rw [← xPar_neg_single_eq_sl2At]
      exact h2 t
  have hA : A ∈ N := by
    rw [hN]
    trivial
  exact hA

theorem d4Graph_one_mem_spanRoots {S S' : List (Fin Tag.D4.rank → ℤ)}
    (hS : ∀ s ∈ S, IsRoot Tag.D4 s ∧ rhoL s ∈ S') {g : ↥(adjointGroup Tag.D4 K)}
    (hg : g ∈ spanRoots K S) : d4Graph K 1 g ∈ spanRoots K S' := by
  have h : (spanRoots K S).map (d4Graph K 1).toMonoidHom ≤ spanRoots K S' := by
    rw [spanRoots, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨s, hs, c, rfl⟩, rfl⟩
    obtain ⟨hsr, hρ⟩ := hS s hs
    obtain ⟨ε, -, hε⟩ := d4Graph_one_xPar (K := K) hsr
    show d4Graph K 1 (𝕩 s c) ∈ _
    rw [hε]
    exact xPar_mem_spanRoots hρ _
  exact h ⟨g, hg, rfl⟩

theorem gammaP_mem_spanRoots {B : SL2 K} {S S' : List (Fin Tag.D4.rank → ℤ)}
    (hS : ∀ s ∈ S, IsRoot Tag.D4 s ∧ rhoL s ∈ S')
    (hN : sl2At K ⟨2, by decide⟩ B ∈
      Subgroup.normalizer (spanRoots K S' : Set ↥(adjointGroup Tag.D4 K)))
    {g : ↥(adjointGroup Tag.D4 K)} (hg : g ∈ spanRoots K S) : gammaP K B g ∈ spanRoots K S' := by
  rw [gammaP, MulAut.mul_apply, MulAut.conj_apply]
  exact (Subgroup.mem_normalizer_iff.1 hN _).1 (d4Graph_one_mem_spanRoots hS hg)

end Graph

end CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2NonsplitGen
