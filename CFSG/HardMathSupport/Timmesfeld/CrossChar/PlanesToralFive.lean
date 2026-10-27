module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToral
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralWeylFive

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.Torality

variable {τ : Tag}

variable (τ) in
@[expose] def ChainBlockToral (n : ℕ) : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L], ringChar L ≠ n + 1 →
    ∀ β : Fin n → Fin τ.rank → ℤ, IsAChain β →
      ∃ m ∈ rootSpan τ L (aChainRoots β), ∃ hm : m ∈ monomialSubgroup τ L,
        weylQuotientHom τ L ⟨m, hm⟩ = chainRefl β ∧
        ∀ t ∈ torusGroup τ L, ∃ y ∈ rootSpan τ L (aChainRoots β),
          y * (m * t) * y⁻¹ ∈ torusGroup τ L

theorem exists_conj_mem_torusGroup_of_chains (hSL : ∀ γ, IsRoot τ γ → iform γ γ = 2) {k : ℕ}
    (hblk : ChainBlockToral τ k) {L : Type} [Field L] [IsAlgClosed L] (hL : ringChar L ≠ k + 1) :
    ∀ B : List (Fin k → Fin τ.rank → ℤ), (∀ β ∈ B, IsAChain β) →
      B.Pairwise ChainsStrOrth → ∀ (n : ModGL τ L) (hn : n ∈ monomialSubgroup τ L),
        weylQuotientHom τ L ⟨n, hn⟩ = (B.map chainRefl).prod →
        ∃ g ∈ Subgroup.closure (⋃ β ∈ B, (rootSpan τ L (aChainRoots β) : Set (ModGL τ L))),
          g * n * g⁻¹ ∈ torusGroup τ L := by
  intro B
  induction B with
  | nil =>
    intro _ _ n hn hπ
    refine ⟨1, one_mem _, ?_⟩
    rw [one_mul, inv_one, mul_one]
    exact mem_torusGroup_of_weylQuotientHom_eq_one hn (by simpa using hπ)
  | cons β B' ih =>
    intro hch hpair n hn hπ
    have hβ := hch β List.mem_cons_self
    obtain ⟨m, hmS, hmN, hmρ, hmt⟩ := hblk L hL β hβ
    set n' := m⁻¹ * n with hn'def
    have hn' : n' ∈ monomialSubgroup τ L := mul_mem (inv_mem hmN) hn
    have hπ' : weylQuotientHom τ L ⟨n', hn'⟩ = (B'.map chainRefl).prod := by
      have e : (⟨n', hn'⟩ : monomialSubgroup τ L) = (⟨m, hmN⟩)⁻¹ * ⟨n, hn⟩ := rfl
      rw [e, map_mul, map_inv, hmρ, hπ, List.map_cons, List.prod_cons, inv_mul_cancel_left]
    obtain ⟨g', hg', hg'n⟩ := ih (fun γ hγ => hch γ (List.mem_cons_of_mem _ hγ))
      (List.Pairwise.of_cons hpair) n' hn' hπ'
    have hcomm : g' * m = m * g' := by
      have hall : ∀ x ∈ (⋃ γ ∈ B', (rootSpan τ L (aChainRoots γ) : Set (ModGL τ L))),
          ∀ y ∈ ((rootSpan τ L (aChainRoots β) : Subgroup (ModGL τ L)) : Set (ModGL τ L)),
            x * y = y * x := by
        intro x hx y hy
        simp only [Set.mem_iUnion] at hx
        obtain ⟨γ, hγ, hx⟩ := hx
        have hβγ := List.rel_of_pairwise_cons hpair hγ
        exact (commute_rootSpan_of_strOrth (mem_aChainRoots_isRoot hSL hβ)
          (mem_aChainRoots_isRoot hSL (hch γ (List.mem_cons_of_mem _ hγ))) hβγ y hy x hx).symm
      exact closure_commute hall g' hg' m (Subgroup.subset_closure hmS)
    obtain ⟨y, hy, hyt⟩ := hmt _ hg'n
    refine ⟨y * g', mul_mem (Subgroup.subset_closure (Set.mem_biUnion List.mem_cons_self hy))
      (Subgroup.closure_mono (Set.biUnion_subset_biUnion_left fun γ hγ =>
        List.mem_cons_of_mem _ hγ) hg'), ?_⟩
    have e : y * g' * n * (y * g')⁻¹ = y * (m * (g' * n' * g'⁻¹)) * y⁻¹ := by
      have hn : n = m * n' := by rw [hn'def]; group
      calc y * g' * n * (y * g')⁻¹ = y * (g' * m) * n' * g'⁻¹ * y⁻¹ := by rw [hn]; group
        _ = y * (m * (g' * n' * g'⁻¹)) * y⁻¹ := by rw [hcomm]; group
    rw [e]
    exact hyt

theorem monomialToralAt_five_of_chainBlock (hSL : ∀ γ, IsRoot τ γ → iform γ γ = 2)
    (hblk : ChainBlockToral τ 4) : MonomialToralAt τ 5 := by
  intro L _ _ hL M _ χ n hn hw h5
  obtain ⟨B, hB, hpair, hprod⟩ := exists_a4Blocks hSL hw h5
  obtain ⟨g, hg, hgn⟩ := exists_conj_mem_torusGroup_of_chains hSL hblk hL B
    (fun β hβ => (hB β hβ).1) hpair n hn hprod
  refine ⟨g, ?_, hgn⟩
  refine (Subgroup.closure_le _).2 ?_ hg
  intro x hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨β, hβ, hx⟩ := hx
  exact iSup₂_le (fun γ hγ => le_iSup₂_of_le (f := fun δ (_ : δ ∈ kernelRoots χ) =>
    rootSubgroup τ L δ) γ ((hB β hβ).2 hγ) le_rfl) hx

theorem planesToralBar_five_of_chainBlock (hSL : ∀ γ, IsRoot τ γ → iform γ γ = 2)
    (hblk : ChainBlockToral τ 4)
    (hstab : ∀ (L : Type) [Field L] (a : Fin τ.rank → Lˣ), (∀ i, a i ^ 5 = 1) →
      rootCharStabilizerSubgroup a ≤ kernelReflectionGroup a) :
    PlanesToralBar τ 5 :=
  planesToralBar_of_monomialToral (by norm_num) (monomialToralAt_five_of_chainBlock hSL hblk)
    hstab

end CFSG.HardMathSupport.Timmesfeld.CrossChar
