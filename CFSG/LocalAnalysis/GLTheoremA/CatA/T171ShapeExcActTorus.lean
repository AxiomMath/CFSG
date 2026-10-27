module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.F4ThreeGraphTorus
public import CFSG.HardMathSupport.Timmesfeld.Proving.SimpleRootsCartan
public import CFSG.HardMathSupport.Timmesfeld.RootAut.Count

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.RootAut CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.Proving
open scoped Pointwise


theorem rootDiagUnit_graphTorusChar_mem_componentRootSpan
    {τ : Tag} {L : Type} [Field L] {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} (i : KernelComponent χ)
    {r : ℕ} (γ : Fin r → Fin τ.rank → ℤ)
    (hγ : ∀ j, γ j ∈ componentRoots χ i) (u : Fin r → Lˣ) :
    rootDiagUnit τ (graphTorusChar γ u) ∈ componentRootSpan L χ i := by
  classical
  have hγr : ∀ j, IsRoot τ (γ j) := fun j => isRoot_of_mem_componentRoots (hγ j)
  have hneg : ∀ j, -γ j ∈ componentRoots χ i := fun j =>
    (isRootComponent_componentRoots i).neg_mem _ (hγ j)
  set u' : Fin r → (⊤ : Subgroup Lˣ) := fun j => ⟨u j, Subgroup.mem_top _⟩ with hu'
  have hprod := graphTorusHom_eq_prod (γ := γ) (hγ := hγr) (G := ⊤) (z := 1) u'
  have hleft : graphTorusHom γ ⊤ 1 u' = rootDiagUnit τ (graphTorusChar γ u) := by
    rw [graphTorusHom_apply]
    have hcoe : (fun j => ((u' j : (⊤ : Subgroup Lˣ)) : Lˣ)) = u := rfl
    rw [hcoe]
    simp
  rw [hleft] at hprod
  rw [hprod]
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
  have hmem : rootSL2 τ L (γ j) (HSL (u j)) ∈ rootSpan τ L {γ j, -γ j} :=
    rootSL2_mem_rootSpan_pair (hγr j) (HSL (u j))
  exact rootSpan_mono (by
    intro δ hδ
    rcases hδ with rfl | rfl
    · exact hγ j
    · exact hneg j) hmem

section Interpolation

private theorem exists_torus_char_interpolation
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} (i : KernelComponent χ)
    (l : Fin τ.rank → Lˣ) :
    ∃ t : Fin (simpleRoots (componentRoots χ i)).card → Lˣ,
      ∀ α ∈ componentRoots χ i,
        rootChar (graphTorusChar
          (fun k => ((simpleRoots (componentRoots χ i)).equivFin.symm k : Fin τ.rank → ℤ)) t) α =
          rootChar l α := by
  classical
  set Ψ := componentRoots χ i with hΨdef
  set Δ := simpleRoots Ψ with hΔdef
  have hΨ : IsRootComponent Ψ := isRootComponent_componentRoots i
  set e : Fin Δ.card ≃ Δ := Δ.equivFin.symm with he
  set ν : Fin Δ.card → Fin τ.rank → ℤ := fun k => (e k : Fin τ.rank → ℤ) with hν
  set B : Matrix Δ Δ ℤ := fun β γ => corootPair (β : Fin τ.rank → ℤ) (γ : Fin τ.rank → ℤ) with hB
  have hBfin : TauCeti.IsFiniteType B := isFiniteType_simpleRoots_corootPair hΨ
  set A : Matrix (Fin Δ.card) (Fin Δ.card) ℤ := fun i j => B (e j) (e i) with hA
  have hAeq : A = (B.submatrix e e).transpose := by
    ext i j
    rfl
  have hdetA : A.det ≠ 0 := by
    rw [hAeq, Matrix.det_transpose, Matrix.det_submatrix_equiv_self]
    exact hBfin.det_ne_zero
  have hli : LinearIndependent ℚ (fun i : Fin Δ.card => fun j : Fin Δ.card => (A i j : ℚ)) := by
    have hdetAq : ((A.map (fun x : ℤ => (x : ℚ))) :
        Matrix (Fin Δ.card) (Fin Δ.card) ℚ).det ≠ 0 := by
      rw [← Int.cast_det]
      exact Int.cast_ne_zero.mpr hdetA
    exact Matrix.linearIndependent_rows_of_det_ne_zero hdetAq
  obtain ⟨t, ht⟩ := algebraically_closed_lattice_character_interpolation L Δ.card Δ.card
    (fun i j => A i j) hli (fun i => rootChar l (ν i))
  refine ⟨t, fun α hα => ?_⟩
  obtain ⟨c, hc⟩ := exists_coords hΨ hα
  have hsum : α = ∑ k : Fin Δ.card, c (ν k) • ν k := by
    rw [hc, ← Finset.sum_coe_sort Δ]
    exact Fintype.sum_equiv Δ.equivFin (fun i : Δ => c i • (i : Fin τ.rank → ℤ))
      (fun k => c (ν k) • ν k) (fun i => by simp [ν, e])
  have hsum' : ∀ j : Fin Δ.card, corootPair (ν j) α =
      ∑ k : Fin Δ.card, c (ν k) * corootPair (ν j) (ν k) := by
    intro j
    have h := corootPair_sum (β := ν j) (simpleRoots_isRoot (e j).2) Finset.univ
      (fun k => c (ν k)) ν
    rw [hsum]
    simpa using h
  rw [rootChar_graphTorusChar (γ := ν) (u := t) (v := α)
    (hγ := fun j => simpleRoots_isRoot (e j).2)]
  calc ∏ j, t j ^ corootPair (ν j) α
      = ∏ j, t j ^ (∑ k : Fin Δ.card, c (ν k) * corootPair (ν j) (ν k)) := by
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [hsum' j]
    _ = ∏ j, ∏ k : Fin Δ.card, (t j ^ corootPair (ν j) (ν k)) ^ c (ν k) := by
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [← Finset.prod_zpow_eq_zpow_sum]
        refine Finset.prod_congr rfl fun k _ => ?_
        rw [mul_comm, zpow_mul]
    _ = ∏ k : Fin Δ.card, ∏ j : Fin Δ.card, (t j ^ corootPair (ν j) (ν k)) ^ c (ν k) :=
        Finset.prod_comm
    _ = ∏ k : Fin Δ.card, (rootChar l (ν k)) ^ c (ν k) := by
        refine Finset.prod_congr rfl fun k _ => ?_
        rw [Finset.prod_zpow, ht k]
    _ = rootChar l α := by
        rw [hsum, rootChar_sum]
        refine Finset.prod_congr rfl fun k _ => ?_
        rw [rootChar_zsmul]


section Unipotent

private theorem exists_mem_componentRootSpan_conj_eq_of_mem_rootSpan
    {τ : Tag} {L : Type} [Field L] {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} (i : KernelComponent χ)
    {u : ModGL τ L} (hu : u ∈ rootSpan τ L (kernelRoots χ)) :
    ∃ g ∈ componentRootSpan L χ i, ∀ x ∈ componentRootSpan L χ i,
      u * x * u⁻¹ = g * x * g⁻¹ := by
  classical
  set S := componentRootSpan L χ i with hS
  let H : Subgroup (ModGL τ L) :=
    { carrier := {u | ∃ g ∈ S, ∀ x ∈ S, u * x * u⁻¹ = g * x * g⁻¹}
      one_mem' := ⟨1, one_mem S, by intro x _; simp⟩
      mul_mem' := by
        rintro u₁ u₂ ⟨g₁, hg₁, h₁⟩ ⟨g₂, hg₂, h₂⟩
        refine ⟨g₁ * g₂, mul_mem hg₁ hg₂, fun x hx => ?_⟩
        have hx₂ : u₂ * x * u₂⁻¹ ∈ S := by
          rw [h₂ x hx]
          exact mul_mem (mul_mem hg₂ hx) (inv_mem hg₂)
        calc (u₁ * u₂) * x * (u₁ * u₂)⁻¹
            = u₁ * (u₂ * x * u₂⁻¹) * u₁⁻¹ := by group
          _ = g₁ * (u₂ * x * u₂⁻¹) * g₁⁻¹ := h₁ _ hx₂
          _ = g₁ * (g₂ * x * g₂⁻¹) * g₁⁻¹ := by rw [h₂ x hx]
          _ = (g₁ * g₂) * x * (g₁ * g₂)⁻¹ := by group
      inv_mem' := by
        rintro u ⟨g, hg, h⟩
        refine ⟨g⁻¹, inv_mem hg, fun x hx => ?_⟩
        have hy : g⁻¹ * x * g ∈ S := mul_mem (mul_mem (inv_mem hg) hx) hg
        have hux : u * (g⁻¹ * x * g) * u⁻¹ = x := by
          rw [h _ hy]
          group
        calc u⁻¹ * x * u = u⁻¹ * (u * (g⁻¹ * x * g) * u⁻¹) * u := by rw [hux]
          _ = g⁻¹ * x * g := by group }
  have hgen : ∀ α ∈ kernelRoots χ, rootSubgroup τ L α ≤ H := by
    intro α hα z hz
    obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hz
    by_cases hαi : α ∈ componentRoots χ i
    · exact ⟨pinnedX τ L α c, pinnedX_mem_rootSpan hαi c, fun x _ => rfl⟩
    · have hclass : (⟦⟨α, hα⟩⟧ : KernelComponent χ) ≠ i := fun h =>
        hαi ⟨hα, h⟩
      have hmem : pinnedX τ L α c ∈ componentRootSpan L χ ⟦⟨α, hα⟩⟧ :=
        rootSubgroup_le_componentRootSpan (K := L) ⟨α, hα⟩
          (Subgroup.subset_closure ⟨c, rfl⟩)
      have hcomm : ∀ x ∈ S, pinnedX τ L α c * x = x * pinnedX τ L α c :=
        fun x hx => (Subgroup.mem_centralizer_iff.1
          (componentRootSpan_le_centralizer L hclass hmem) x hx).symm
      refine ⟨1, one_mem S, fun x hx => ?_⟩
      rw [hcomm x hx]
      group
  have hrootSpan_le : rootSpan τ L (kernelRoots χ) ≤ H := by
    rw [rootSpan]
    exact iSup₂_le hgen
  exact hrootSpan_le hu

end Unipotent


section TorusSplit

private theorem exists_mem_componentRootSpan_conj_eq_of_mem_torusGroup
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} (i : KernelComponent χ)
    {y : ModGL τ L} (hy : y ∈ torusGroup τ L) :
    ∃ g ∈ componentRootSpan L χ i, ∀ x ∈ componentRootSpan L χ i,
      y * x * y⁻¹ = g * x * g⁻¹ := by
  classical
  set Ψ := componentRoots χ i with hΨdef
  set Δ := simpleRoots Ψ with hΔdef
  set e : Fin Δ.card ≃ Δ := Δ.equivFin.symm with he
  set ν : Fin Δ.card → Fin τ.rank → ℤ := fun k => (e k : Fin τ.rank → ℤ) with hν
  obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hy
  obtain ⟨t, ht⟩ := exists_torus_char_interpolation (L := L) i l
  refine ⟨rootDiagUnit τ (graphTorusChar ν t),
    rootDiagUnit_graphTorusChar_mem_componentRootSpan i ν (fun j => simpleRoots_subset (e j).2) t,
    fun x hx => ?_⟩
  have hK : componentRootSpan L χ i ≤
      (MulAut.conj (rootDiagUnit τ l)).toMonoidHom.eqLocus
        (MulAut.conj (rootDiagUnit τ (graphTorusChar ν t))).toMonoidHom := by
    rw [componentRootSpan]
    refine iSup₂_le fun α hα => ?_
    intro z hz
    obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hz
    have hαr : IsRoot τ α := isRoot_of_mem_componentRoots hα
    have h1 := rootDiagUnit_conj_pinnedX l hαr c
    have h2 := rootDiagUnit_conj_pinnedX (graphTorusChar ν t) hαr c
    have hchar : rootChar (graphTorusChar ν t) α = rootChar l α := by
      have ht' := ht α hα
      simpa [ν, e] using ht'
    change rootDiagUnit τ l * pinnedX τ L α c * (rootDiagUnit τ l)⁻¹ =
      rootDiagUnit τ (graphTorusChar ν t) * pinnedX τ L α c *
        (rootDiagUnit τ (graphTorusChar ν t))⁻¹
    rw [h1, h2, hchar]
  exact hK hx


theorem exists_mem_rootSpan_conj_eq_of_mem_Z
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {a : Fin τ.rank → Lˣ}
    (i : KernelComponent (rootCharHom a)) {y : ModGL τ L}
    (hy : y ∈ torusGroup τ L ⊔ rootSpan τ L (kernelRoots (rootCharHom a))) :
    ∃ g ∈ unionRootSpan L (rootCharHom a)
        ({i} : Set (KernelComponent (rootCharHom a))),
      ∀ x ∈ rootSpan τ L (componentRoots (rootCharHom a) i), y * x * y⁻¹ = g * x * g⁻¹ := by
  classical
  have hnorm : torusGroup τ L ≤ Subgroup.normalizer
      (rootSpan τ L (kernelRoots (rootCharHom a)) : Set (ModGL τ L)) :=
    torusGroup_le_normalizer_rootSpan (K := L) (fun _ hα => hα.1)
  have hcoe : (↑(torusGroup τ L ⊔ rootSpan τ L (kernelRoots (rootCharHom a))) :
      Set (ModGL τ L)) =
      (torusGroup τ L : Set (ModGL τ L)) *
        (rootSpan τ L (kernelRoots (rootCharHom a)) : Set (ModGL τ L)) :=
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnorm
  have hy' : y ∈ (torusGroup τ L : Set (ModGL τ L)) *
      (rootSpan τ L (kernelRoots (rootCharHom a)) : Set (ModGL τ L)) := by
    rw [← hcoe]
    exact hy
  obtain ⟨t, ht, u, hu, rfl⟩ := Set.mem_mul.1 hy'
  obtain ⟨gt, hgt, hgt'⟩ := exists_mem_componentRootSpan_conj_eq_of_mem_torusGroup
    (χ := rootCharHom a) i ht
  obtain ⟨gu, hgu, hgu'⟩ := exists_mem_componentRootSpan_conj_eq_of_mem_rootSpan
    (χ := rootCharHom a) i hu
  refine ⟨gt * gu, ?_, fun x hx => ?_⟩
  · change gt * gu ∈ rootSpan τ L (componentRoots (rootCharHom a) i)
    exact mul_mem hgt hgu
  · have hx' : gu * x * gu⁻¹ ∈ componentRootSpan L (rootCharHom a) i :=
      mul_mem (mul_mem hgu hx) (inv_mem hgu)
    calc t * u * x * (t * u)⁻¹
        = t * (u * x * u⁻¹) * t⁻¹ := by group
      _ = t * (gu * x * gu⁻¹) * t⁻¹ := by rw [hgu' x hx]
      _ = gt * (gu * x * gu⁻¹) * gt⁻¹ := hgt' _ hx'
      _ = (gt * gu) * x * (gt * gu)⁻¹ := by group

end TorusSplit

end Interpolation

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
