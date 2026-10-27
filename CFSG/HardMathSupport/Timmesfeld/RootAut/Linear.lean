module

public import CFSG.LieType.Chevalley.KernelComponentRoots

public noncomputable section

namespace CFSG.HardMathSupport.Timmesfeld.RootAut

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

variable {τ : Tag}

structure IsIsometry (Ψ : Set (Fin τ.rank → ℤ)) (f : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ) :
    Prop where
  bijOn : Set.BijOn f Ψ Ψ
  iform_eq : ∀ γ ∈ Ψ, ∀ δ ∈ Ψ, iform (f γ) (f δ) = iform γ δ
  neg : ∀ γ ∈ Ψ, f (-γ) = -f γ


theorem iform_sum_smul_left {ι : Type*} (s : Finset ι) (c : ι → ℤ) (u : ι → Fin τ.rank → ℤ)
    (y : Fin τ.rank → ℤ) : iform (∑ i ∈ s, c i • u i) y = ∑ i ∈ s, c i * iform (u i) y := by
  rw [iform_finset_sum_left]
  simp only [iform_smul_left]

theorem iform_sum_smul_right {ι : Type*} (x : Fin τ.rank → ℤ) (s : Finset ι) (c : ι → ℤ)
    (u : ι → Fin τ.rank → ℤ) : iform x (∑ i ∈ s, c i • u i) = ∑ i ∈ s, c i * iform x (u i) := by
  rw [iform_finset_sum_right]
  simp only [iform_smul_right]

theorem iform_sum_smul_sum_smul {ι : Type*} (s : Finset ι) (c : ι → ℤ)
    (u : ι → Fin τ.rank → ℤ) :
    iform (∑ i ∈ s, c i • u i) (∑ i ∈ s, c i • u i) =
      ∑ i ∈ s, ∑ j ∈ s, c i * c j * iform (u i) (u j) := by
  rw [iform_sum_smul_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iform_sum_smul_right, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem iform_sub_sum_self {ι : Type*} (v : Fin τ.rank → ℤ) (s : Finset ι) (c : ι → ℤ)
    (u : ι → Fin τ.rank → ℤ) :
    iform (v - ∑ i ∈ s, c i • u i) (v - ∑ i ∈ s, c i • u i) =
      iform v v - ∑ i ∈ s, c i * iform v (u i) - ∑ i ∈ s, c i * iform (u i) v +
        ∑ i ∈ s, ∑ j ∈ s, c i * c j * iform (u i) (u j) := by
  have h1 := iform_sum_smul_left s c u v
  have h2 := iform_sum_smul_right v s c u
  have h3 := iform_sum_smul_sum_smul s c u
  rw [iform_sub_left, iform_sub_right, iform_sub_right, h3, h1, h2]
  ring

theorem iform_sub_sub_self (c a b : Fin τ.rank → ℤ) :
    iform (c - a - b) (c - a - b) =
      iform c c + iform a a + iform b b - 2 * iform c a - 2 * iform c b + 2 * iform a b := by
  simp only [iform_sub_left, iform_sub_right]
  rw [iform_comm a c, iform_comm b c, iform_comm b a]
  ring

theorem iform_self_eq_zero_of_zero : iform (0 : Fin τ.rank → ℤ) 0 = 0 := by
  simp [iform]

theorem eq_zero_of_iform_self_eq_zero {x : Fin τ.rank → ℤ} (h : iform x x = 0) : x = 0 := by
  by_contra hx
  have := iform_self_pos hx
  omega

variable {Ψ : Set (Fin τ.rank → ℤ)} {f : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ}

theorem apply_eq_sum_of_iform (hf : ∀ γ ∈ Ψ, ∀ δ ∈ Ψ, iform (f γ) (f δ) = iform γ δ)
    {s : Finset (Fin τ.rank → ℤ)} (hs : ∀ β ∈ s, β ∈ Ψ) {γ : Fin τ.rank → ℤ} (hγ : γ ∈ Ψ)
    {c : (Fin τ.rank → ℤ) → ℤ} (e : γ = ∑ β ∈ s, c β • β) :
    f γ = ∑ β ∈ s, c β • f β := by
  have h1 := iform_sub_sum_self (f γ) s c f
  have h2 := iform_sub_sum_self γ s c fun β => β
  rw [← e, sub_self, iform_self_eq_zero_of_zero] at h2
  have t1 : ∑ β ∈ s, c β * iform (f γ) (f β) = ∑ β ∈ s, c β * iform γ β :=
    Finset.sum_congr rfl fun β hβ => by rw [hf γ hγ β (hs β hβ)]
  have t2 : ∑ β ∈ s, c β * iform (f β) (f γ) = ∑ β ∈ s, c β * iform β γ :=
    Finset.sum_congr rfl fun β hβ => by rw [hf β (hs β hβ) γ hγ]
  have t3 : ∑ β ∈ s, ∑ β' ∈ s, c β * c β' * iform (f β) (f β') =
      ∑ β ∈ s, ∑ β' ∈ s, c β * c β' * iform β β' :=
    Finset.sum_congr rfl fun β hβ => Finset.sum_congr rfl fun β' hβ' => by
      rw [hf β (hs β hβ) β' (hs β' hβ')]
  have h3 : iform (f γ - ∑ β ∈ s, c β • f β) (f γ - ∑ β ∈ s, c β • f β) = 0 := by
    rw [h1, hf γ hγ γ hγ, t1, t2, t3]
    exact h2.symm
  exact sub_eq_zero.1 (eq_zero_of_iform_self_eq_zero h3)

theorem eq_add_iff_of_iform (hf : ∀ γ ∈ Ψ, ∀ δ ∈ Ψ, iform (f γ) (f δ) = iform γ δ)
    {a b c : Fin τ.rank → ℤ} (ha : a ∈ Ψ) (hb : b ∈ Ψ) (hc : c ∈ Ψ) :
    f c = f a + f b ↔ c = a + b := by
  have e : iform (f c - f a - f b) (f c - f a - f b) = iform (c - a - b) (c - a - b) := by
    rw [iform_sub_sub_self, iform_sub_sub_self, hf c hc c hc, hf a ha a ha, hf b hb b hb,
      hf c hc a ha, hf c hc b hb, hf a ha b hb]
  constructor
  · intro h
    have h0 : iform (c - a - b) (c - a - b) = 0 := by
      rw [← e, h, add_sub_cancel_left, sub_self, iform_self_eq_zero_of_zero]
    have := eq_zero_of_iform_self_eq_zero h0
    rw [sub_sub, sub_eq_zero] at this
    exact this
  · intro h
    have h0 : iform (f c - f a - f b) (f c - f a - f b) = 0 := by
      rw [e, h, add_sub_cancel_left, sub_self, iform_self_eq_zero_of_zero]
    have := eq_zero_of_iform_self_eq_zero h0
    rw [sub_sub, sub_eq_zero] at this
    exact this

theorem IsIsometry.comp_smul (hΨ : IsRootComponent Ψ) (hf : IsIsometry Ψ f) {w : WeylGroup τ}
    (hw : w ∈ componentWeylGroup Ψ) : IsIsometry Ψ (fun γ => f (w • γ)) := by
  have hmaps : Set.MapsTo (w • ·) Ψ Ψ := fun γ hγ => smul_mem_of_mem_componentWeylGroup hΨ hw γ hγ
  have hmaps' : Set.MapsTo (w⁻¹ • ·) Ψ Ψ := fun γ hγ =>
    smul_mem_of_mem_componentWeylGroup hΨ (inv_mem hw) γ hγ
  have hbij : Set.BijOn (w • ·) Ψ Ψ :=
    Set.InvOn.bijOn ⟨fun γ _ => inv_smul_smul w γ, fun γ _ => smul_inv_smul w γ⟩ hmaps hmaps'
  refine ⟨hf.bijOn.comp hbij, fun γ hγ δ hδ => ?_, fun γ hγ => ?_⟩
  · rw [hf.iform_eq _ (hmaps hγ) _ (hmaps hδ), iform_smul]
  · show f (w • -γ) = -f (w • γ)
    rw [smul_neg, hf.neg _ (hmaps hγ)]

theorem posRoots_subset : posRoots Ψ ⊆ Ψ := fun _ h => h.1

theorem negRoots_subset (hΨ : IsRootComponent Ψ) : negRoots Ψ ⊆ Ψ := fun _ h =>
  ((mem_negRoots_iff hΨ).1 h).1

theorem neg_mem_posRoots_iff {α : Fin τ.rank → ℤ} : -α ∈ posRoots Ψ ↔ α ∈ negRoots Ψ :=
  Iff.rfl

theorem IsIsometry.mem_negRoots (hΨ : IsRootComponent Ψ) (hf : IsIsometry Ψ f)
    (hpos : ∀ γ ∈ posRoots Ψ, f γ ∈ posRoots Ψ) {γ : Fin τ.rank → ℤ} (hγ : γ ∈ negRoots Ψ) :
    f γ ∈ negRoots Ψ := by
  have h1 : -γ ∈ posRoots Ψ := hγ
  have h2 := hpos _ h1
  rw [hf.neg γ (negRoots_subset hΨ hγ)] at h2
  exact h2

theorem IsIsometry.exists_posRoots (hΨ : IsRootComponent Ψ) (hf : IsIsometry Ψ f)
    (hpos : ∀ γ ∈ posRoots Ψ, f γ ∈ posRoots Ψ) {γ : Fin τ.rank → ℤ} (hγ : γ ∈ posRoots Ψ) :
    ∃ a ∈ posRoots Ψ, f a = γ := by
  obtain ⟨a, ha, rfl⟩ := hf.bijOn.surjOn hγ.1
  refine ⟨a, ?_, rfl⟩
  rcases mem_posRoots_or_mem_negRoots hΨ ha with h | h
  · exact h
  · exact absurd (hf.mem_negRoots hΨ hpos h) (not_mem_negRoots_of_mem_posRoots hγ)

theorem IsIsometry.apply_mem_simpleRoots (hΨ : IsRootComponent Ψ) (hf : IsIsometry Ψ f)
    (hpos : ∀ γ ∈ posRoots Ψ, f γ ∈ posRoots Ψ) {β : Fin τ.rank → ℤ}
    (hβ : β ∈ simpleRoots Ψ) : f β ∈ simpleRoots Ψ := by
  have hβΨ := simpleRoots_subset hβ
  have hfβ := hpos β (simpleRoot_mem_posRoots hβ)
  rw [CFSG.LieType.Chevalley.mem_simpleRoots]
  refine ⟨hΨ.isRoot _ hfβ.1, hfβ, fun γ hγ δ hδ e => ?_⟩
  obtain ⟨a, ha, rfl⟩ := hf.exists_posRoots hΨ hpos hγ
  obtain ⟨b, hb, rfl⟩ := hf.exists_posRoots hΨ hpos hδ
  have h := (eq_add_iff_of_iform hf.iform_eq ha.1 hb.1 hβΨ).1 e
  exact (CFSG.LieType.Chevalley.mem_simpleRoots.1 hβ).2.2 a ha b hb h

theorem IsIsometry.mem_posRoots_of_simpleRoots (hΨ : IsRootComponent Ψ) (hf : IsIsometry Ψ f)
    (hΔ : ∀ β ∈ simpleRoots Ψ, f β ∈ posRoots Ψ) {γ : Fin τ.rank → ℤ}
    (hγ : γ ∈ posRoots Ψ) : f γ ∈ posRoots Ψ := by
  classical
  obtain ⟨c, hc, e⟩ := exists_nonneg_coords hΨ hγ
  have hfγ := apply_eq_sum_of_iform hf.iform_eq (fun β hβ => simpleRoots_subset hβ) hγ.1 e
  have hd : ∀ β ∈ simpleRoots Ψ, ∃ d : (Fin τ.rank → ℤ) → ℤ,
      (∀ δ ∈ simpleRoots Ψ, 0 ≤ d δ) ∧ f β = ∑ δ ∈ simpleRoots Ψ, d δ • δ :=
    fun β hβ => exists_nonneg_coords hΨ (hΔ β hβ)
  choose! d hd0 hde using hd
  have hsum : f γ = ∑ δ ∈ simpleRoots Ψ, (∑ β ∈ simpleRoots Ψ, c β * d β δ) • δ := by
    rw [hfγ]
    calc ∑ β ∈ simpleRoots Ψ, c β • f β
        = ∑ β ∈ simpleRoots Ψ, c β • ∑ δ ∈ simpleRoots Ψ, d β δ • δ :=
          Finset.sum_congr rfl fun β hβ => by rw [hde β hβ]
      _ = ∑ β ∈ simpleRoots Ψ, ∑ δ ∈ simpleRoots Ψ, (c β * d β δ) • δ := by
          refine Finset.sum_congr rfl fun β _ => ?_
          rw [Finset.smul_sum]
          exact Finset.sum_congr rfl fun δ _ => by rw [smul_smul]
      _ = ∑ δ ∈ simpleRoots Ψ, (∑ β ∈ simpleRoots Ψ, c β * d β δ) • δ := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun δ _ => by rw [Finset.sum_smul]
  have hmem : f γ ∈ Ψ := hf.bijOn.mapsTo hγ.1
  refine (coords_nonneg_iff hΨ hmem hsum).1 fun δ hδ => ?_
  exact Finset.sum_nonneg fun β hβ => mul_nonneg (hc β hβ) (hd0 β hβ δ hδ)

@[expose] def negSet (Ψ : Set (Fin τ.rank → ℤ)) (f : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ) :
    Set (Fin τ.rank → ℤ) :=
  {γ | γ ∈ posRoots Ψ ∧ f γ ∈ negRoots Ψ}

theorem negSet_finite (hΨ : IsRootComponent Ψ) : (negSet Ψ f).Finite :=
  (finite_setOf_isRoot τ).subset fun γ hγ => hΨ.isRoot γ hγ.1.1

theorem ncard_negSet_comp_lt (hΨ : IsRootComponent Ψ) (hf : IsIsometry Ψ f)
    {β : Fin τ.rank → ℤ} (hβ : β ∈ simpleRoots Ψ) (hfβ : f β ∈ negRoots Ψ) :
    (negSet Ψ fun γ => f (rootReflection β • γ)).ncard < (negSet Ψ f).ncard := by
  have hβr := simpleRoots_isRoot hβ
  have hβΨ := simpleRoots_subset hβ
  have hsub : (negSet Ψ fun γ => f (rootReflection β • γ)) ⊆
      (rootReflection β • ·) '' (negSet Ψ f \ {β}) := by
    rintro γ ⟨hγ, hfγ⟩
    change f (rootReflection β • γ) ∈ negRoots Ψ at hfγ
    have hne : γ ≠ β := by
      rintro rfl
      have h1 : f (rootReflection γ • γ) = -f γ := by
        rw [rootReflection_smul_self hβr, hf.neg γ hβΨ]
      rw [h1] at hfγ
      have h2 : -f γ ∈ posRoots Ψ := neg_mem_posRoots_iff.2 hfβ
      exact not_mem_negRoots_of_mem_posRoots h2 hfγ
    obtain ⟨hpos, hne'⟩ := rootReflection_mem_posRoots hΨ hβ hγ hne
    refine ⟨rootReflection β • γ, ⟨⟨hpos, hfγ⟩, hne'⟩, ?_⟩
    show rootReflection β • rootReflection β • γ = γ
    rw [smul_smul, rootReflection_mul_self hβr, one_smul]
  have hfin := negSet_finite (f := f) hΨ
  calc (negSet Ψ fun γ => f (rootReflection β • γ)).ncard
      ≤ ((rootReflection β • ·) '' (negSet Ψ f \ {β})).ncard :=
        Set.ncard_le_ncard hsub (hfin.sdiff.image _)
    _ ≤ (negSet Ψ f \ {β}).ncard := Set.ncard_image_le hfin.sdiff
    _ < (negSet Ψ f).ncard :=
        Set.ncard_sdiff_singleton_lt_of_mem ⟨simpleRoot_mem_posRoots hβ, hfβ⟩ hfin

theorem exists_mem_componentWeylGroup_posRoots (hΨ : IsRootComponent Ψ) (hf : IsIsometry Ψ f) :
    ∃ w ∈ componentWeylGroup Ψ, ∀ γ ∈ posRoots Ψ, f (w • γ) ∈ posRoots Ψ := by
  suffices h : ∀ n : ℕ, ∀ w ∈ componentWeylGroup Ψ,
      (negSet Ψ fun γ => f (w • γ)).ncard = n →
      ∃ w' ∈ componentWeylGroup Ψ, ∀ γ ∈ posRoots Ψ, f (w' • γ) ∈ posRoots Ψ from
    h _ 1 (one_mem _) rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro w hw hn
    have hfw := hf.comp_smul hΨ hw
    by_cases hΔ : ∀ β ∈ simpleRoots Ψ, f (w • β) ∈ posRoots Ψ
    · exact ⟨w, hw, fun γ hγ => hfw.mem_posRoots_of_simpleRoots hΨ hΔ hγ⟩
    · push Not at hΔ
      obtain ⟨β, hβ, hfβ⟩ := hΔ
      have hfβ' : f (w • β) ∈ negRoots Ψ := by
        rcases mem_posRoots_or_mem_negRoots hΨ (hfw.bijOn.mapsTo (simpleRoots_subset hβ)) with
          h | h
        · exact absurd h hfβ
        · exact h
      have hlt := ncard_negSet_comp_lt hΨ hfw hβ hfβ'
      have hw' : w * rootReflection β ∈ componentWeylGroup Ψ :=
        mul_mem hw (rootReflection_mem_componentWeylGroup hβ)
      refine ih _ (hn ▸ hlt) (w * rootReflection β) hw' ?_
      simp only [mul_smul]

theorem IsIsometry.eq_self_of_simpleRoots (hΨ : IsRootComponent Ψ) (hf : IsIsometry Ψ f)
    (hfix : ∀ β ∈ simpleRoots Ψ, f β = β) {γ : Fin τ.rank → ℤ} (hγ : γ ∈ Ψ) : f γ = γ := by
  obtain ⟨c, e⟩ := exists_coords hΨ hγ
  rw [apply_eq_sum_of_iform hf.iform_eq (fun β hβ => simpleRoots_subset hβ) hγ e, e]
  exact Finset.sum_congr rfl fun β hβ => by rw [hfix β hβ]

theorem exists_smul_eq_of_isIsometry (hΨ : IsRootComponent Ψ) (hf : IsIsometry Ψ f)
    {w : WeylGroup τ} (hw : w ∈ componentWeylGroup Ψ)
    (hfix : ∀ β ∈ simpleRoots Ψ, f (w • β) = β) :
    ∃ u ∈ componentWeylGroup Ψ, ∀ γ ∈ Ψ, f γ = u • γ := by
  refine ⟨w⁻¹, inv_mem hw, fun γ hγ => ?_⟩
  have hγ' : w⁻¹ • γ ∈ Ψ := smul_mem_of_mem_componentWeylGroup hΨ (inv_mem hw) γ hγ
  have h := (hf.comp_smul hΨ hw).eq_self_of_simpleRoots hΨ hfix hγ'
  simp only [smul_inv_smul] at h
  exact h

end CFSG.HardMathSupport.Timmesfeld.RootAut
