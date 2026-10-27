module

public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.F4TwoKernel

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSF4Std

open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus

set_option maxRecDepth 100000
set_option linter.unusedSectionVars false

abbrev hubP (k0 k1 k2 k3 : ℕ) : Prop :=
  (∀ γ ∈ rts, ∀ γ'' ∈ rts, kdL k0 k1 k2 k3 γ % 3 = 0 → kdL k0 k1 k2 k3 γ'' % 3 = 0 →
      ipL γ γ'' ≠ 0 ∨ ∃ γ' ∈ rts, kdL k0 k1 k2 k3 γ' % 3 = 0 ∧ ipL γ γ' ≠ 0 ∧ ipL γ' γ'' ≠ 0) ∧
    (rts.filter (fun γ => kdL k0 k1 k2 k3 γ % 3 = 0)).length = 18

abbrev a2a2P (k0 k1 k2 k3 : ℕ) : Prop :=
  (∀ γ ∈ rts, ∀ γ' ∈ rts, kdL k0 k1 k2 k3 γ % 3 = 0 → kdL k0 k1 k2 k3 γ' % 3 = 0 →
      ipL γ γ = ipL γ' γ' → ipL γ γ' ≠ 0) ∧
   (∀ γ ∈ rts, ∀ γ' ∈ rts, kdL k0 k1 k2 k3 γ % 3 = 0 → kdL k0 k1 k2 k3 γ' % 3 = 0 →
      ipL γ γ ≠ ipL γ' γ' → ipL γ γ' = 0) ∧
   (rts.filter (fun γ => kdL k0 k1 k2 k3 γ % 3 = 0 ∧ ipL γ γ = 4)).length = 6 ∧
   (rts.filter (fun γ => kdL k0 k1 k2 k3 γ % 3 = 0 ∧ ipL γ γ = 2)).length = 6

theorem classify2_all : ∀ k0 ∈ [0, 1, 2], ∀ k1 ∈ [0, 1, 2], ∀ k2 ∈ [0, 1, 2], ∀ k3 ∈ [0, 1, 2],
    (k0 ≠ 0 ∨ k1 ≠ 0 ∨ k2 ≠ 0 ∨ k3 ≠ 0) → a2a2P k0 k1 k2 k3 ∨ hubP k0 k1 k2 k3 := by
  decide +kernel

structure KernelB (k : Fin Tag.F4.rank → ℕ) : Prop where
  conn : ∀ γ γ'' : V4, IsRoot Tag.F4 γ → IsRoot Tag.F4 γ'' → kdot k γ % 3 = 0 →
    kdot k γ'' % 3 = 0 → ipF4 γ γ'' ≠ 0 ∨
      ∃ γ' : V4, IsRoot Tag.F4 γ' ∧ kdot k γ' % 3 = 0 ∧ ipF4 γ γ' ≠ 0 ∧ ipF4 γ' γ'' ≠ 0
  card : {γ : V4 | IsRoot Tag.F4 γ ∧ kdot k γ % 3 = 0}.ncard = 18


theorem classify_kernel2 (k : Fin Tag.F4.rank → ℕ) (hk3 : ∀ i, k i < 3) (hk0 : ∃ i, k i ≠ 0) :
    KernelB k ∨ KernelA2A2 k := by
  have hne := exists_ne_zero_idx hk0
  have hm : ∀ n : ℕ, n < 3 → n ∈ [0, 1, 2] := fun n hn => by simp; omega
  have h := classify2_all (k (idx 0)) (hm _ (hk3 _)) (k (idx 1)) (hm _ (hk3 _)) (k (idx 2))
    (hm _ (hk3 _)) (k (idx 3)) (hm _ (hk3 _)) hne
  rcases h with ⟨hsame, hdiff, hlong, hshort⟩ | ⟨hconn, hcard⟩
  · right
    refine ⟨fun γ γ' hγ hγ' hk hk' hlen => ?_, fun γ γ' hγ hγ' hk hk' hlen => ?_, ?_, ?_⟩
    · obtain ⟨l, hl, rfl⟩ := (mem_rts_iff γ).1 hγ
      obtain ⟨l', hl', rfl⟩ := (mem_rts_iff γ').1 hγ'
      rw [kdot_vec4] at hk hk'
      rw [ipF4_vec4, ipF4_vec4] at hlen
      rw [ipF4_vec4]
      exact hsame l hl l' hl' hk hk' hlen
    · obtain ⟨l, hl, rfl⟩ := (mem_rts_iff γ).1 hγ
      obtain ⟨l', hl', rfl⟩ := (mem_rts_iff γ').1 hγ'
      rw [kdot_vec4] at hk hk'
      rw [ipF4_vec4, ipF4_vec4] at hlen
      rw [ipF4_vec4]
      exact hdiff l hl l' hl' hk hk' hlen
    · rw [ncard_roots_filter (fun γ : V4 => kdot k γ % 3 = 0 ∧ ipF4 γ γ = 4)]
      exact hlong
    · rw [ncard_roots_filter (fun γ : V4 => kdot k γ % 3 = 0 ∧ ipF4 γ γ = 2)]
      exact hshort
  · left
    refine ⟨fun γ γ'' hγ hγ'' hk hk'' => ?_, ?_⟩
    · obtain ⟨l, hl, rfl⟩ := (mem_rts_iff γ).1 hγ
      obtain ⟨l'', hl'', rfl⟩ := (mem_rts_iff γ'').1 hγ''
      rw [kdot_vec4] at hk hk''
      rcases hconn l hl l'' hl'' hk hk'' with h | ⟨l', hl', hk', h1, h2⟩
      · left
        rw [ipF4_vec4]
        exact h
      · right
        refine ⟨vec4 l', (mem_rts_iff _).2 ⟨l', hl', rfl⟩, by rwa [kdot_vec4], ?_, ?_⟩
        · rw [ipF4_vec4]
          exact h1
        · rw [ipF4_vec4]
          exact h2
    · rw [ncard_roots_filter (fun γ : V4 => kdot k γ % 3 = 0)]
      exact hcard

section Classes

variable {L : Type} [Field L] {a : Fin Tag.F4.rank → Lˣ} {ω : Lˣ} {k : Fin Tag.F4.rank → ℕ}

theorem eq_of_kernelB (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) (hak : ∀ i, a i = ω ^ k i)
    (hk : KernelB k) (i j : KernelComponent (rootCharHom a)) : i = j := by
  have hker : ∀ γ ∈ kernelRoots (rootCharHom a), kdot k γ % 3 = 0 := fun γ hγ =>
    (rootChar_eq_one_iff hω3 hω1 hak γ).1 hγ.2
  obtain ⟨α, rfl⟩ := Quotient.exists_rep i
  obtain ⟨β, rfl⟩ := Quotient.exists_rep j
  rcases hk.conn α β α.2.1 β.2.1 (hker α α.2) (hker β β.2) with h | ⟨γ', hγ', hkγ', h1, h2⟩
  · exact mk_eq_of_iform_ne_zero (α := α) (β := β) (by
      show iform (α : V4) β ≠ 0
      rw [iform_F4]
      exact h)
  · have hγ'mem : γ' ∈ kernelRoots (rootCharHom a) :=
      ⟨hγ', (rootChar_eq_one_iff hω3 hω1 hak γ').2 hkγ'⟩
    refine (mk_eq_of_iform_ne_zero (α := α) (β := ⟨γ', hγ'mem⟩) (by
      show iform (α : V4) γ' ≠ 0
      rw [iform_F4]
      exact h1)).trans (mk_eq_of_iform_ne_zero (α := ⟨γ', hγ'mem⟩) (β := β) (by
      show iform γ' (β : V4) ≠ 0
      rw [iform_F4]
      exact h2))

theorem componentRoots_eq_kernelRoots_of_kernelB (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    (hak : ∀ i, a i = ω ^ k i) (hk : KernelB k) (i : KernelComponent (rootCharHom a)) :
    componentRoots (rootCharHom a) i = kernelRoots (rootCharHom a) := by
  ext γ
  constructor
  · rintro ⟨hγ, -⟩
    exact hγ
  · intro hγ
    exact ⟨hγ, eq_of_kernelB hω3 hω1 hak hk _ i⟩

theorem kernelRoots_eq (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) (hak : ∀ i, a i = ω ^ k i) :
    kernelRoots (rootCharHom a) = {γ : V4 | IsRoot Tag.F4 γ ∧ kdot k γ % 3 = 0} := by
  ext γ
  exact and_congr_right fun _ => rootChar_eq_one_iff hω3 hω1 hak γ

theorem ncard_componentRoots_of_kernelB (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    (hak : ∀ i, a i = ω ^ k i) (hk : KernelB k) (i : KernelComponent (rootCharHom a)) :
    (componentRoots (rootCharHom a) i).ncard = 18 := by
  rw [componentRoots_eq_kernelRoots_of_kernelB hω3 hω1 hak hk i, kernelRoots_eq hω3 hω1 hak]
  exact hk.card

end Classes

section Rho

variable
  {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}

theorem rho_image_eq_of_kernelB (S : LangSetup Tag.F4 L p₀) {a : Fin Tag.F4.rank → Lˣ}
    (hT : rootDiagUnit Tag.F4 a ∈ S.D.torus) {ω : Lˣ} {k : Fin Tag.F4.rank → ℕ}
    (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) (hak : ∀ i, a i = ω ^ k i) (hk : KernelB k)
    (i : KernelComponent (rootCharHom a)) :
    (S.ρ : V4 → V4) '' componentRoots (rootCharHom a) i = componentRoots (rootCharHom a) i := by
  rw [componentRoots_eq_kernelRoots_of_kernelB hω3 hω1 hak hk i]
  have hfin : (kernelRoots (rootCharHom a)).Finite := by
    rw [kernelRoots_eq hω3 hω1 hak]
    exact Set.finite_of_ncard_ne_zero (by rw [hk.card]; norm_num)
  have hsub : (S.ρ : V4 → V4) '' kernelRoots (rootCharHom a) ⊆ kernelRoots (rootCharHom a) := by
    rintro _ ⟨γ, hγ, rfl⟩
    exact outer_rho_mem_kernelRoots S hT hγ
  refine Set.eq_of_subset_of_ncard_le hsub ?_ hfin
  rw [Set.ncard_image_of_injective _ S.ρ.injective]

end Rho

end KSF4Std

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

end
