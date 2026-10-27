module

public import CFSG.ClassicalInvolution.Generic.Weyl

public section

namespace CFSG.ClassicalInvolution.Generic

variable {F : Type*} [Field F] {G : Type*} [Group G] {Ω : Set (Subgroup G)} {E : Subgroup G}
  {S : Set (Subgroup G)}

@[expose] def reflSet {ι W : Type*} [Group W] (s : ι → W) : Set W :=
  {r | ∃ (w : W) (i : ι), r = w * s i * w⁻¹}

theorem conj_mem_reflSet {ι W : Type*} [Group W] {s : ι → W} {r : W} (hr : r ∈ reflSet s) (w : W) :
    w * r * w⁻¹ ∈ reflSet s := by
  obtain ⟨u, i, rfl⟩ := hr
  exact ⟨w * u, i, by group⟩

theorem simple_mem_reflSet {ι W : Type*} [Group W] (s : ι → W) (i : ι) : s i ∈ reflSet s :=
  ⟨1, i, by simp⟩

theorem iSup_subgroupOf_self {ι : Type*} (U : ι → Subgroup G) :
    ⨆ i, (U i).subgroupOf (⨆ i, U i) = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨x, hx⟩ -
  induction hx using Subgroup.iSup_induction' with
  | hp i x hx =>
    exact Subgroup.mem_iSup_of_mem i ((Subgroup.mem_subgroupOf).mpr hx)
  | h1 => exact one_mem _
  | hmul x y hx hy hx' hy' => exact mul_mem hx' hy'

variable [Finite F]

theorem ToralFrame.rho_le_of_le (Fr : ToralFrame F Ω E S) {J : Subgroup G} {L M : ↥S}
    (hL : (L : Subgroup G) ≤ J) (hM : (M : Subgroup G) ≤ J) :
    (Fr.rho L M : Subgroup G) ≤ J := by
  have hw : Fr.w L ∈ J := hL (normPart_le_left _ _ (Fr.w_mem L))
  rintro _ ⟨y, hy, rfl⟩
  have := J.mul_mem (J.mul_mem hw (hM hy)) (J.inv_mem hw)
  simpa using this

structure WeylData (Fr : ToralFrame F Ω E S) (ι : Type*) (W : Type*) [Group W] where
  s : ι → W
  gen : Subgroup.closure (Set.range s) = ⊤
  β : ↥S ≃ ↥(reflSet s)
  comm_iff : ∀ K L : ↥S, K ≠ L →
    (Commutes (K : Subgroup G) (L : Subgroup G) ↔ (β K : W) * β L = β L * β K)
  rho_eq : ∀ K L : ↥S, ((β (Fr.rho K L) : ↥(reflSet s)) : W) =
    (β K : W) * (β L : W) * (β K : W)⁻¹

namespace WeylData

variable {Fr : ToralFrame F Ω E S} {ι W : Type*} [Group W] (WD : WeylData Fr ι W)

@[expose] noncomputable def base (i : ι) : ↥S := WD.β.symm ⟨WD.s i, simple_mem_reflSet WD.s i⟩

theorem β_base (i : ι) : ((WD.β (WD.base i) : ↥(reflSet WD.s)) : W) = WD.s i := by
  rw [base, Equiv.apply_symm_apply]

@[expose] noncomputable def span : Subgroup G := ⨆ i, (WD.base i : Subgroup G)

theorem base_le_span (i : ι) : (WD.base i : Subgroup G) ≤ WD.span :=
  le_iSup (fun i => (WD.base i : Subgroup G)) i

theorem le_span (K : ↥S) : (K : Subgroup G) ≤ WD.span := by
  have key : ∀ w : W, w ∈ Subgroup.closure (Set.range WD.s) → ∀ M M' : ↥S,
      ((WD.β M' : ↥(reflSet WD.s)) : W) = w * WD.β M * w⁻¹ →
      ((M : Subgroup G) ≤ WD.span ↔ (M' : Subgroup G) ≤ WD.span) := by
    intro w hw
    induction hw using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      intro M M' hM'
      have h1 : M' = Fr.rho (WD.base j) M := by
        apply WD.β.injective
        apply Subtype.ext
        rw [WD.rho_eq, WD.β_base, hM']
      subst h1
      have hL := WD.base_le_span j
      refine ⟨fun hM => Fr.rho_le_of_le hL hM, fun hM' => ?_⟩
      have h2 : Fr.rho (WD.base j) (Fr.rho (WD.base j) M) = M := by
        have := congrArg (fun π : Equiv.Perm ↥S => π M) (Fr.rho_mul_self (WD.base j))
        simpa using this
      rw [← h2]
      exact Fr.rho_le_of_le hL hM'
    | one =>
      intro M M' h
      have : M' = M := by
        apply WD.β.injective
        apply Subtype.ext
        simpa using h
      subst this
      exact Iff.rfl
    | mul x y _ _ hx hy =>
      intro M M' hM'
      have hmem : y * ((WD.β M : ↥(reflSet WD.s)) : W) * y⁻¹ ∈ reflSet WD.s :=
        conj_mem_reflSet (WD.β M).2 y
      set M'' : ↥S := WD.β.symm ⟨_, hmem⟩ with hM''def
      have hM'' : ((WD.β M'' : ↥(reflSet WD.s)) : W) = y * WD.β M * y⁻¹ := by
        rw [hM''def, Equiv.apply_symm_apply]
      refine (hy M M'' hM'').trans (hx M'' M' ?_)
      rw [hM'', hM']
      group
    | inv x _ hx =>
      intro M M' h
      refine (hx M' M ?_).symm
      rw [h]
      group
  obtain ⟨u, i, hu⟩ := (WD.β K).2
  have hu' : u ∈ Subgroup.closure (Set.range WD.s) := by
    rw [WD.gen]
    exact Subgroup.mem_top u
  have := key u hu' (WD.base i) K (by rw [WD.β_base]; exact hu)
  exact this.mp (WD.base_le_span i)

@[expose] noncomputable def wBase (j : ι) : Subgroup.normalizer (E : Set G) :=
  ⟨Fr.w (WD.base j), Fr.w_mem_normalizer (WD.base j)⟩

theorem exists_conj (K : ↥S) : ∃ (i : ι) (g : Subgroup.normalizer (E : Set G)),
    g ∈ Subgroup.closure (Set.range WD.wBase) ∧ Fr.act g (WD.base i) = K := by
  have key : ∀ w : W, w ∈ Subgroup.closure (Set.range WD.s) → ∀ M M' : ↥S,
      ((WD.β M' : ↥(reflSet WD.s)) : W) = w * WD.β M * w⁻¹ →
      ∃ g ∈ Subgroup.closure (Set.range WD.wBase), Fr.act g M = M' := by
    intro w hw
    induction hw using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      intro M M' hM'
      have h1 : M' = Fr.rho (WD.base j) M := by
        apply WD.β.injective
        apply Subtype.ext
        rw [WD.rho_eq, WD.β_base, hM']
      exact ⟨WD.wBase j, Subgroup.subset_closure ⟨j, rfl⟩, h1.symm⟩
    | one =>
      intro M M' h
      have : M' = M := by
        apply WD.β.injective
        apply Subtype.ext
        simpa using h
      exact ⟨1, one_mem _, by rw [map_one]; exact this.symm⟩
    | mul x y _ _ hx hy =>
      intro M M' hM'
      have hmem : y * ((WD.β M : ↥(reflSet WD.s)) : W) * y⁻¹ ∈ reflSet WD.s :=
        conj_mem_reflSet (WD.β M).2 y
      set M'' : ↥S := WD.β.symm ⟨_, hmem⟩ with hM''def
      have hM'' : ((WD.β M'' : ↥(reflSet WD.s)) : W) = y * WD.β M * y⁻¹ := by
        rw [hM''def, Equiv.apply_symm_apply]
      obtain ⟨g₂, hg₂, h₂⟩ := hy M M'' hM''
      obtain ⟨g₁, hg₁, h₁⟩ := hx M'' M' (by rw [hM'', hM']; group)
      refine ⟨g₁ * g₂, mul_mem hg₁ hg₂, ?_⟩
      rw [map_mul, Equiv.Perm.mul_apply, h₂, h₁]
    | inv x _ hx =>
      intro M M' h
      obtain ⟨g, hg, hgM⟩ := hx M' M (by rw [h]; group)
      refine ⟨g⁻¹, inv_mem hg, ?_⟩
      rw [map_inv, Equiv.Perm.inv_eq_iff_eq]
      exact hgM.symm
  obtain ⟨u, i, hu⟩ := (WD.β K).2
  have hu' : u ∈ Subgroup.closure (Set.range WD.s) := by
    rw [WD.gen]
    exact Subgroup.mem_top u
  obtain ⟨g, hg, hgK⟩ := key u hu' (WD.base i) K (by rw [WD.β_base]; exact hu)
  exact ⟨i, g, hg, hgK⟩

theorem span_eq_sSup : WD.span = sSup S := by
  refine le_antisymm (iSup_le fun i => le_sSup (WD.base i).2) (sSup_le fun K hK => ?_)
  exact WD.le_span ⟨K, hK⟩

theorem base_commutes (hs : Function.Injective WD.s) {i j : ι} (hij : i ≠ j)
    (h : WD.s i * WD.s j = WD.s j * WD.s i) :
    Commutes (WD.base i : Subgroup G) (WD.base j : Subgroup G) := by
  have hne : WD.base i ≠ WD.base j := fun h' => hij (hs (by rw [← WD.β_base i, ← WD.β_base j, h']))
  exact (WD.comm_iff _ _ hne).mpr (by rw [WD.β_base, WD.β_base]; exact h)

theorem base_not_commutes {i j : ι} (h : WD.s i * WD.s j ≠ WD.s j * WD.s i) :
    WD.base i ≠ WD.base j ∧ ¬ Commutes (WD.base i : Subgroup G) (WD.base j : Subgroup G) := by
  have hne : WD.base i ≠ WD.base j := by
    intro h'
    apply h
    have := congrArg (fun K => ((WD.β K : ↥(reflSet WD.s)) : W)) h'
    simp only [WD.β_base] at this
    rw [this]
  exact ⟨hne, fun hc => h (by
    have := (WD.comm_iff _ _ hne).mp hc
    rwa [WD.β_base, WD.β_base] at this)⟩

@[expose] noncomputable def baseIn (i : ι) : Subgroup ↥WD.span :=
  (WD.base i : Subgroup G).subgroupOf WD.span

theorem iSup_baseIn : ⨆ i, WD.baseIn i = ⊤ :=
  iSup_subgroupOf_self (fun i => (WD.base i : Subgroup G))

theorem baseIn_commute {i j : ι} (h : Commutes (WD.base i : Subgroup G) (WD.base j : Subgroup G)) :
    ∀ a ∈ WD.baseIn i, ∀ b ∈ WD.baseIn j, a * b = b * a :=
  fun a ha b hb => Subtype.ext (h a.1 ha b.1 hb)

end WeylData

end CFSG.ClassicalInvolution.Generic
