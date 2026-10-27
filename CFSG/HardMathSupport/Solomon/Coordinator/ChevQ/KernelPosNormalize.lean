module

public import CFSG.LieType.Chevalley.SignKernelStabilizer

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KernelPos

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint


variable {τ : Tag} {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}

section Descent

variable {G : Type*} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]

open Classical in
private def negFun (χ : Multiplicative (Fin τ.rank → ℤ) →* M) (f : (Fin τ.rank → ℤ) →+ G)
    (ρ : WeylGroup τ) : Finset (Fin τ.rank → ℤ) :=
  (rootFinset τ).filter fun γ => γ ∈ posRoots (kernelRoots χ) ∧ f (ρ • γ) < 0

private theorem mem_negFun {f : (Fin τ.rank → ℤ) →+ G} {ρ : WeylGroup τ}
    {γ : Fin τ.rank → ℤ} :
    γ ∈ negFun χ f ρ ↔ γ ∈ posRoots (kernelRoots χ) ∧ f (ρ • γ) < 0 := by
  classical
  rw [negFun, Finset.mem_filter, mem_rootFinset]
  exact ⟨fun h => h.2, fun h => ⟨h.1.1.1, h⟩⟩

theorem exists_kernelWeyl_smul_pos (f : (Fin τ.rank → ℤ) →+ G)
    (hf : ∀ γ ∈ kernelRoots χ, f γ ≠ 0) :
    ∃ ρ ∈ kernelWeylGroup χ, ∀ γ ∈ posRoots (kernelRoots χ), 0 < f (ρ • γ) := by
  classical
  suffices h : ∀ n : ℕ, ∀ ρ ∈ kernelWeylGroup χ, (negFun χ f ρ).card = n →
      ∃ ρ' ∈ kernelWeylGroup χ, ∀ γ ∈ posRoots (kernelRoots χ), 0 < f (ρ' • γ) from
    h _ 1 (one_mem _) rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro ρ hρ hn
    have hreg : ∀ γ ∈ kernelRoots χ, f (ρ • γ) ≠ 0 := fun γ hγ =>
      hf _ (smul_mem_kernelRoots (kernelWeylGroup_le hρ) hγ)
    by_cases hall : ∀ β ∈ simpleRoots (kernelRoots χ), 0 < f (ρ • β)
    · refine ⟨ρ, hρ, fun γ hγ => ?_⟩
      obtain ⟨c, hc, e⟩ := exists_nonneg_coords_kernel hγ
      have hsum : f (ρ • γ) = ∑ β ∈ simpleRoots (kernelRoots χ), c β • f (ρ • β) := by
        rw [e, Finset.smul_sum, map_sum]
        refine Finset.sum_congr rfl fun β _ => ?_
        rw [smul_comm ρ (c β) β, map_zsmul]
      refine lt_of_le_of_ne ?_ (hreg γ hγ.1).symm
      rw [hsum]
      exact Finset.sum_nonneg fun β hβ => zsmul_nonneg (hall β hβ).le (hc β hβ)
    push Not at hall
    obtain ⟨β, hβ, hneg⟩ := hall
    have hβk := simpleRoots_kernelRoots_mem hβ
    have hβr := hβk.1
    have hβpos : β ∈ posRoots (kernelRoots χ) := (mem_simpleRoots.1 hβ).2.1
    have hneg' : f (ρ • β) < 0 := lt_of_le_of_ne hneg (hreg β hβk)
    have hρ' : ρ * rootReflection β ∈ kernelWeylGroup χ :=
      mul_mem hρ (rootReflection_mem_kernelWeylGroup hβk)
    have hsub : negFun χ f (ρ * rootReflection β) ⊆
        ((negFun χ f ρ).erase β).image (rootReflection β • ·) := by
      intro α hα
      obtain ⟨hαpos, hαneg⟩ := mem_negFun.1 hα
      have hne : α ≠ β := by
        rintro rfl
        rw [mul_smul, rootReflection_smul_self hβr, smul_neg, map_neg] at hαneg
        exact lt_asymm hneg' (neg_lt_zero.1 hαneg)
      obtain ⟨h1, h2⟩ := rootReflection_mem_posRoots_kernel hβ hαpos hne
      refine Finset.mem_image.2 ⟨rootReflection β • α, Finset.mem_erase.2 ⟨h2,
        mem_negFun.2 ⟨h1, by rwa [mul_smul] at hαneg⟩⟩, ?_⟩
      simp only [smul_smul, rootReflection_mul_self hβr, one_smul]
    have hβmem : β ∈ negFun χ f ρ := mem_negFun.2 ⟨hβpos, hneg'⟩
    have hlt : (negFun χ f (ρ * rootReflection β)).card < n := by
      calc (negFun χ f (ρ * rootReflection β)).card
          ≤ (((negFun χ f ρ).erase β).image (rootReflection β • ·)).card :=
            Finset.card_le_card hsub
        _ ≤ ((negFun χ f ρ).erase β).card := Finset.card_image_le
        _ < (negFun χ f ρ).card := Finset.card_erase_lt_of_mem hβmem
        _ = n := hn
    exact ih _ hlt _ hρ' rfl

end Descent

theorem neg_mem_kernelRoots {δ : Fin τ.rank → ℤ} (hδ : δ ∈ kernelRoots χ) :
    -δ ∈ kernelRoots χ := by
  rw [← rootReflection_smul_self hδ.1]
  exact smul_mem_kernelRoots (rootReflection_mem_charStabilizer hδ) hδ

theorem mem_posRoots_of_neg {δ : Fin τ.rank → ℤ} (hδ : δ ∈ kernelRoots χ)
    (h : ¬ 0 < height δ) : -δ ∈ posRoots (kernelRoots χ) :=
  ⟨neg_mem_kernelRoots hδ, by
    rw [height_neg]
    exact neg_pos.2 (lt_of_le_of_ne (not_lt.1 h) hδ.1.height_ne_zero)⟩

section Moves

theorem exists_mul_smul_mem_posRoots {x : WeylGroup τ}
    (hx : (fun α => x • α) '' kernelRoots χ = kernelRoots χ) :
    ∃ ρ ∈ kernelWeylGroup χ, ∀ γ ∈ posRoots (kernelRoots χ),
      (ρ * x) • γ ∈ posRoots (kernelRoots χ) := by
  let f : (Fin τ.rank → ℤ) →+ ℤ :=
    { toFun := fun μ => height (x⁻¹ • μ)
      map_zero' := by simp [height]
      map_add' := fun u v => by rw [smul_add, height_add] }
  obtain ⟨ρ₀, hρ₀, hpos⟩ := exists_kernelWeyl_smul_pos (χ := χ) f
    (fun γ hγ => (IsRoot.smul hγ.1 x⁻¹).height_ne_zero)
  have hxinv : ∀ δ ∈ kernelRoots χ, x⁻¹ • δ ∈ kernelRoots χ := fun δ hδ => by
    have hδ' : δ ∈ (fun α => x • α) '' kernelRoots χ := by rw [hx]; exact hδ
    obtain ⟨ε, hε, hεδ⟩ := hδ'
    have : x⁻¹ • δ = ε := by rw [← hεδ]; simp
    rw [this]
    exact hε
  have hmaps : Set.MapsTo ((x⁻¹ * ρ₀) • ·) (posRoots (kernelRoots χ))
      (posRoots (kernelRoots χ)) := by
    intro γ hγ
    show (x⁻¹ * ρ₀) • γ ∈ posRoots (kernelRoots χ)
    rw [mul_smul]
    exact ⟨hxinv _ (smul_mem_kernelRoots (kernelWeylGroup_le hρ₀) hγ.1), hpos γ hγ⟩
  have hfin : (posRoots (kernelRoots χ)).Finite :=
    (finite_setOf_isRoot τ).subset fun α (hα : α ∈ posRoots (kernelRoots χ)) => hα.1.1
  have hinj : Set.InjOn ((x⁻¹ * ρ₀) • ·) (posRoots (kernelRoots χ)) :=
    fun a _ b _ h => smul_left_cancel _ h
  have hsurj := ((Set.Finite.injOn_iff_bijOn_of_mapsTo hfin hmaps).1 hinj).surjOn
  refine ⟨ρ₀⁻¹, inv_mem hρ₀, fun γ hγ => ?_⟩
  obtain ⟨γ', hγ', e⟩ := hsurj hγ
  have : (ρ₀⁻¹ * x) • γ = γ' := by
    rw [← e]
    simp [smul_smul, mul_assoc]
  rw [this]
  exact hγ'

def orbitFunctional (c : Fin τ.rank → ℚ) (u : WeylGroup τ) : (Fin τ.rank → ℤ) →+ ℚ where
  toFun μ := ∑ i, c i * ((μ + u • μ + (u ^ 2) • μ) i : ℚ)
  map_zero' := by simp
  map_add' x y := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [smul_add, Pi.add_apply, Int.cast_add]
    ring

theorem orbitFunctional_smul {u : WeylGroup τ} (hu3 : u ^ 3 = 1) (c : Fin τ.rank → ℚ)
    (μ : Fin τ.rank → ℤ) : orbitFunctional c u (u • μ) = orbitFunctional c u μ := by
  have h2 : u • (u • μ) = (u ^ 2) • μ := by rw [smul_smul, sq]
  have h3 : (u ^ 2) • (u • μ) = μ := by
    have : u ^ 2 * u = 1 := by rw [← pow_succ]; exact hu3
    rw [smul_smul, this, one_smul]
  show ∑ i, c i * (((u • μ) + u • (u • μ) + (u ^ 2) • (u • μ)) i : ℚ) =
    ∑ i, c i * ((μ + u • μ + (u ^ 2) • μ) i : ℚ)
  rw [h2, h3]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.add_apply, Int.cast_add]
  ring

theorem exists_rat_dotProduct_ne_zero {n : ℕ} {S : Set (Fin n → ℤ)} (hS : S.Finite)
    (h0 : ∀ s ∈ S, s ≠ 0) : ∃ c : Fin n → ℚ, ∀ s ∈ S, ∑ i, c i * (s i : ℚ) ≠ 0 := by
  haveI : Finite S := hS.to_subtype
  let f : S → Module.Dual ℚ (Fin n → ℚ) := fun s =>
    (dotProductEquiv ℚ (Fin n)) (fun i => (s.1 i : ℚ))
  have h : ∀ s : S, ∃ x, f s x ≠ 0 := by
    intro s
    obtain ⟨i, hi⟩ := Function.ne_iff.1 (h0 s.1 s.2)
    refine ⟨Pi.single i 1, ?_⟩
    simpa [f] using hi
  obtain ⟨x, hx⟩ := Module.Dual.exists_forall_ne_zero_of_forall_exists f h
  refine ⟨x, fun s hs => ?_⟩
  have := hx ⟨s, hs⟩
  simpa [f, dotProduct, mul_comm] using this

theorem orbitSum_ne_zero_of_fixed_or_orth {u : WeylGroup τ} (hu3 : u ^ 3 = 1)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (h : u • γ = γ ∨ iform γ (u • γ) = 0) :
    γ + u • γ + (u ^ 2) • γ ≠ 0 := by
  have hpos := iform_self_pos_of_isRoot hγ
  have h3 : u • ((u ^ 2) • γ) = γ := by
    have : u * u ^ 2 = 1 := by rw [← pow_succ']; exact hu3
    rw [smul_smul, this, one_smul]
  have key : 0 < iform γ (γ + u • γ + (u ^ 2) • γ) := by
    rw [iform_add_right, iform_add_right]
    rcases h with h | h
    · have h2 : (u ^ 2) • γ = γ := by rw [sq, mul_smul, h, h]
      rw [h, h2]
      omega
    · have h2 : iform γ ((u ^ 2) • γ) = 0 := by
        rw [← iform_smul u γ ((u ^ 2) • γ), h3, iform_comm, h]
      rw [h, h2]
      omega
  intro hs
  rw [hs] at key
  simp [iform] at key

theorem exists_conj_smul_mem_posRoots {u : WeylGroup τ}
    (hustab : ∀ γ ∈ kernelRoots χ, u • γ ∈ kernelRoots χ) (hu3 : u ^ 3 = 1)
    (hsum : ∀ γ ∈ kernelRoots χ, γ + u • γ + (u ^ 2) • γ ≠ 0) :
    ∃ ρ ∈ kernelWeylGroup χ, ∀ γ ∈ posRoots (kernelRoots χ),
      (ρ * u * ρ⁻¹) • γ ∈ posRoots (kernelRoots χ) := by
  have hfin : (kernelRoots χ).Finite := (finite_setOf_isRoot τ).subset fun α hα => hα.1
  obtain ⟨c, hc⟩ := exists_rat_dotProduct_ne_zero
    (hfin.image fun γ => γ + u • γ + (u ^ 2) • γ)
    (by rintro _ ⟨γ, hγ, rfl⟩; exact hsum γ hγ)
  obtain ⟨ρ₀, hρ₀, hpos⟩ := exists_kernelWeyl_smul_pos (χ := χ) (orbitFunctional c u)
    (fun γ hγ => hc _ ⟨γ, hγ, rfl⟩)
  refine ⟨ρ₀⁻¹, inv_mem hρ₀, fun γ hγ => ?_⟩
  have hχ := kernelWeylGroup_le hρ₀
  have hmem : (ρ₀⁻¹ * u * ρ₀⁻¹⁻¹) • γ ∈ kernelRoots χ := by
    rw [inv_inv, mul_assoc, mul_smul, mul_smul]
    exact smul_mem_kernelRoots ((charStabilizer χ).inv_mem hχ)
      (hustab _ (smul_mem_kernelRoots hχ hγ.1))
  refine ⟨hmem, ?_⟩
  by_contra hneg
  have h1 := hpos _ (mem_posRoots_of_neg hmem hneg)
  have h2 : ρ₀ • (ρ₀⁻¹ * u * ρ₀⁻¹⁻¹) • γ = u • ρ₀ • γ := by
    rw [inv_inv]
    simp [smul_smul, mul_assoc]
  rw [smul_neg, map_neg, h2, orbitFunctional_smul hu3] at h1
  exact lt_asymm (hpos γ hγ) (neg_pos.1 h1)

end Moves

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KernelPos

end
