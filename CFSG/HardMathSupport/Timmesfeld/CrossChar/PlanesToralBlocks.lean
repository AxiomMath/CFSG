module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralWeyl
public import CFSG.LieType.Chevalley.LangStronglyOrthogonalCommute

public noncomputable section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

variable {τ : Tag}

section


variable (τ) in
@[expose] def A2BlockToral : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L], ringChar L ≠ 3 →
    ∀ α β : Fin τ.rank → ℤ, IsA2Pair α β →
      ∃ m ∈ rootSpan τ L (a2Roots α β), ∃ hm : m ∈ monomialSubgroup τ L,
        weylQuotientHom τ L ⟨m, hm⟩ = rootReflection α * rootReflection β ∧
        ∀ t ∈ torusGroup τ L, ∃ y ∈ rootSpan τ L (a2Roots α β),
          y * (m * t) * y⁻¹ ∈ torusGroup τ L

theorem commute_rootSpan_of_strOrth {L : Type} [Field L] {S T : Set (Fin τ.rank → ℤ)}
    (hS : ∀ γ ∈ S, IsRoot τ γ) (hT : ∀ δ ∈ T, IsRoot τ δ)
    (h : ∀ γ ∈ S, ∀ δ ∈ T, StrOrth γ δ) :
    ∀ x ∈ rootSpan τ L S, ∀ y ∈ rootSpan τ L T, x * y = y * x := by
  have h1 : ∀ γ ∈ S, rootSpan τ L T ≤
      Subgroup.centralizer (rootSubgroup τ L γ : Set (ModGL τ L)) := by
    intro γ hγ
    refine iSup₂_le fun δ hδ => fun y hy => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hx
    obtain ⟨d, rfl⟩ := mem_rootSubgroup.1 hy
    exact pinnedX_commute_of_iform_eq_zero L (hS γ hγ) (hT δ hδ) (h γ hγ δ hδ).1
      (h γ hγ δ hδ).2.1 c d
  have h2 : rootSpan τ L S ≤ Subgroup.centralizer (rootSpan τ L T : Set (ModGL τ L)) :=
    iSup₂_le fun γ hγ => Subgroup.le_centralizer_iff.2 (h1 γ hγ)
  intro x hx y hy
  exact ((Subgroup.mem_centralizer_iff.1 (h2 hx)) y hy).symm

theorem mem_torusGroup_of_weylQuotientHom_eq_one {L : Type} [Field L] {n : ModGL τ L}
    (hn : n ∈ monomialSubgroup τ L) (h1 : weylQuotientHom τ L ⟨n, hn⟩ = 1) :
    n ∈ torusGroup τ L := by
  obtain ⟨w₀, h, hh, he⟩ := monomialSubgroup_le_torusWeylCosets hn
  have hw₀ : weylQuotientHom τ L ⟨n, hn⟩ = w₀ := weylQuotientHom_eq (by
    change MapsRootLines n w₀
    rw [he]
    simpa using (mapsRootLines_of_mem_torusGroup hh).mul (mapsRootLines_canonicalRep w₀))
  rw [h1] at hw₀
  rw [he, ← hw₀, canonicalRep_one, mul_one]
  exact hh

theorem exists_conj_mem_torusGroup_of_blocks (hblk : A2BlockToral τ) {L : Type} [Field L]
    [IsAlgClosed L] (hL : ringChar L ≠ 3) :
    ∀ B : List ((Fin τ.rank → ℤ) × (Fin τ.rank → ℤ)), (∀ p ∈ B, IsA2Pair p.1 p.2) →
      B.Pairwise PairsStrOrth → ∀ (n : ModGL τ L) (hn : n ∈ monomialSubgroup τ L),
        weylQuotientHom τ L ⟨n, hn⟩ = (B.map pairRefl).prod →
        ∃ g ∈ Subgroup.closure (⋃ p ∈ B, (rootSpan τ L (a2Roots p.1 p.2) : Set (ModGL τ L))),
          g * n * g⁻¹ ∈ torusGroup τ L := by
  intro B
  induction B with
  | nil =>
    intro _ _ n hn hπ
    refine ⟨1, one_mem _, ?_⟩
    rw [one_mul, inv_one, mul_one]
    exact mem_torusGroup_of_weylQuotientHom_eq_one hn (by simpa using hπ)
  | cons p B' ih =>
    intro hA2 hpair n hn hπ
    have hp := hA2 p List.mem_cons_self
    obtain ⟨m, hmS, hmN, hmρ, hmt⟩ := hblk L hL p.1 p.2 hp
    set n' := m⁻¹ * n with hn'def
    have hn' : n' ∈ monomialSubgroup τ L := mul_mem (inv_mem hmN) hn
    have hπ' : weylQuotientHom τ L ⟨n', hn'⟩ = (B'.map pairRefl).prod := by
      have e : (⟨n', hn'⟩ : monomialSubgroup τ L) = (⟨m, hmN⟩)⁻¹ * ⟨n, hn⟩ := rfl
      rw [e, map_mul, map_inv, hmρ, hπ, List.map_cons, List.prod_cons, ← pairRefl,
        inv_mul_cancel_left]
    obtain ⟨g', hg', hg'n⟩ := ih (fun q hq => hA2 q (List.mem_cons_of_mem _ hq))
      (List.Pairwise.of_cons hpair) n' hn' hπ'
    have hcomm : g' * m = m * g' := by
      have hall : ∀ x ∈ (⋃ q ∈ B', (rootSpan τ L (a2Roots q.1 q.2) : Set (ModGL τ L))),
          ∀ y ∈ ((rootSpan τ L (a2Roots p.1 p.2) : Subgroup (ModGL τ L)) : Set (ModGL τ L)),
            x * y = y * x := by
        intro x hx y hy
        simp only [Set.mem_iUnion] at hx
        obtain ⟨q, hq, hx⟩ := hx
        have hpq := List.rel_of_pairwise_cons hpair hq
        exact (commute_rootSpan_of_strOrth (a2Roots_isRoot hp)
          (a2Roots_isRoot (hA2 q (List.mem_cons_of_mem _ hq))) hpq y hy x hx).symm
      have := closure_commute hall g' hg' m (Subgroup.subset_closure hmS)
      exact this
    obtain ⟨y, hy, hyt⟩ := hmt _ hg'n
    refine ⟨y * g', mul_mem (Subgroup.subset_closure (Set.mem_biUnion List.mem_cons_self hy))
      (Subgroup.closure_mono (Set.biUnion_subset_biUnion_left fun q hq =>
        List.mem_cons_of_mem _ hq) hg'), ?_⟩
    have e : y * g' * n * (y * g')⁻¹ = y * (m * (g' * n' * g'⁻¹)) * y⁻¹ := by
      have hn : n = m * n' := by rw [hn'def]; group
      calc y * g' * n * (y * g')⁻¹ = y * (g' * m) * n' * g'⁻¹ * y⁻¹ := by rw [hn]; group
        _ = y * (m * (g' * n' * g'⁻¹)) * y⁻¹ := by rw [hcomm]; group
    rw [e]
    exact hyt

theorem exists_conj_mem_torusGroup_of_kernelWeylGroup (hblk : A2BlockToral τ) {L : Type}
    [Field L] [IsAlgClosed L] (hL : ringChar L ≠ 3) {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {n : ModGL τ L} (hn : n ∈ monomialSubgroup τ L)
    (hw : weylQuotientHom τ L ⟨n, hn⟩ ∈ kernelWeylGroup χ)
    (h3 : weylQuotientHom τ L ⟨n, hn⟩ ^ 3 = 1) :
    ∃ g ∈ rootSpan τ L (kernelRoots χ), g * n * g⁻¹ ∈ torusGroup τ L := by
  obtain ⟨B, hB, hpair, hprod⟩ := exists_a2Blocks hw h3
  obtain ⟨g, hg, hgn⟩ := exists_conj_mem_torusGroup_of_blocks hblk hL B
    (fun p hp => (hB p hp).1) hpair n hn hprod
  refine ⟨g, ?_, hgn⟩
  refine (Subgroup.closure_le _).2 ?_ hg
  intro x hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨p, hp, hx⟩ := hx
  exact iSup₂_le (fun γ hγ => le_iSup₂_of_le (f := fun δ (_ : δ ∈ kernelRoots χ) =>
    rootSubgroup τ L δ) γ ((hB p hp).2 hγ) le_rfl) hx

end

end CFSG.HardMathSupport.Timmesfeld.CrossChar
