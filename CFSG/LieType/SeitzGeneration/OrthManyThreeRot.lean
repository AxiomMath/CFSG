module

public import CFSG.LieType.SeitzGeneration.OrthManyTwo

public section

namespace CFSG.LieType.SeitzGeneration

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.PartOne.CTP
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical CFSG.Open OrthNS OrthBlk
open CFSG.RankThree.Classical2 (orthDerived)

section Gram

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem manyThree_polar_comb {e₁ e₂ f₁ f₂ : V} (h11 : polar Q e₁ e₁ = polar Q f₁ f₁)
    (h12 : polar Q e₁ e₂ = polar Q f₁ f₂) (h22 : polar Q e₂ e₂ = polar Q f₂ f₂)
    (α β α' β' : K) :
    polar Q (α • e₁ + β • e₂) (α' • e₁ + β' • e₂) =
      polar Q (α • f₁ + β • f₂) (α' • f₁ + β' • f₂) := by
  have h21e : polar Q e₂ e₁ = polar Q e₁ e₂ := polar_comm Q e₂ e₁
  have h21f : polar Q f₂ f₁ = polar Q f₁ f₂ := polar_comm Q f₂ f₁
  simp only [polar_add_left, polar_add_right, polar_smul_left_eq, polar_smul_right_eq, h11, h12,
    h22, h21e, h21f]

theorem manyThree_span_pair_eq [FiniteDimensional K V] {g : V ≃ₗ[K] V}
    {P : Submodule K V} (hd : Module.finrank K P = 2) {u : V} (hu : u ∈ P) (hgu : g u ∈ P)
    (hli : LinearIndependent K ![u, g u]) : Submodule.span K {u, g u} = P := by
  refine Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.mpr ?_) ?_
  · rintro x (rfl | rfl)
    exacts [hu, hgu]
  · have hr : Set.range ![u, g u] = {u, g u} := by
      ext x
      simp only [Set.mem_range, Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Set.mem_insert_iff, Set.mem_singleton_iff]
      exact ⟨fun h => h.imp Eq.symm Eq.symm, fun h => h.imp Eq.symm Eq.symm⟩
    have := finrank_span_eq_card hli
    rw [hr] at this
    rw [hd, this]
    simp

end Gram

section Rot

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem rot_mem_orthCentralizerSpan (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) {E : Subgroup (orthDerived Q)}
    {x : orthDerived Q} (hxE : x ∈ E) (hx1 : x ≠ 1) {p : ℕ} (hp : Odd p)
    (hxp : ((x : orthDerived Q) : V ≃ₗ[K] V) ^ p = 1) {A : Submodule K V}
    (hA : PolarNondegOn Q A) (h1 : ∀ u ∈ A, ((x : orthDerived Q) : V ≃ₗ[K] V) u ∈ A)
    (h2 : ∀ u ∈ A, ((x : orthDerived Q) : V ≃ₗ[K] V).symm u ∈ A)
    (hmove : ∃ u ∈ A, ((x : orthDerived Q) : V ≃ₗ[K] V) u ≠ u) :
    extendId hA ((x : orthDerived Q) : V ≃ₗ[K] V) h1 h2 ∈ orthCentralizerSpan Q E := by
  set g : V ≃ₗ[K] V := ((x : orthDerived Q) : V ≃ₗ[K] V) with hg
  have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := orthDerived_mem_orthogonalGroup
  have hb := extendId_isBlock hA hgO hxp h1 h2 hmove
  have hmem : extendId hA g h1 h2 ∈ orthDerived Q :=
    mem_orthDerived_of_odd_pow hQ hT hp hb.mem hb.pow
  refine mem_orthCentralizerSpan_of_commute hmem hxE hx1 ?_
  refine LinearEquiv.ext fun v => ?_
  obtain ⟨u, hu, r, hr, rfl⟩ := Submodule.mem_sup.mp ((isCompl_perp hA).sup_eq_top ▸
    Submodule.mem_top (x := v))
  have hgr : g r ∈ perp Q A := mem_perp.mpr fun a ha => by
    have := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hgO (g.symm a) r
    rw [LinearEquiv.apply_symm_apply] at this
    rw [this]
    exact mem_perp.mp hr _ (h2 a ha)
  show extendId hA g h1 h2 (g (u + r)) = g (extendId hA g h1 h2 (u + r))
  rw [map_add g u r, extendId_apply hA h1 h2 (h1 u hu) hgr, extendId_apply hA h1 h2 hu hr,
    map_add]

end Rot

section Mixed

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem exists_mixed_vector_rot {H : Subgroup (V ≃ₗ[K] V)}
    (hH : H ≤ TauCeti.QuadraticMap.orthogonalGroup Q) {g : V ≃ₗ[K] V}
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hrot : ∀ (A : Submodule K V) (hA : PolarNondegOn Q A) (h1 : ∀ u ∈ A, g u ∈ A)
      (h2 : ∀ u ∈ A, g.symm u ∈ A), (∃ u ∈ A, g u ≠ u) → extendId hA g h1 h2 ∈ H)
    {τ : K} (hτ : τ ≠ 0) (hnoroot : ∀ r : K, r ^ 2 - τ * r + 1 ≠ 0)
    {P₁ P₂ P₃ Y : Submodule K V} (hP₁ : PolarNondegOn Q P₁) (hP₃ : PolarNondegOn Q P₃)
    (h12 : OrthSep Q P₁ P₂) (h13 : OrthSep Q P₁ P₃) (h23 : OrthSep Q P₂ P₃)
    (hd₁ : finrank K P₁ = 2) (hd₃ : finrank K P₃ = 2) (ha₂ : ∀ t ∈ P₂, Q t = 0 → t = 0)
    (hg₁ : ∀ u ∈ P₁, g u ∈ P₁) (hg₂ : ∀ u ∈ P₂, g u ∈ P₂) (hg₃ : ∀ u ∈ P₃, g u ∈ P₃)
    (hr₁ : ∀ u ∈ P₁, g (g u) = τ • g u - u) (hr₂ : ∀ u ∈ P₂, g (g u) = τ • g u - u)
    (hr₃ : ∀ u ∈ P₃, g (g u) = τ • g u - u) (hY : P₃ ≤ Y) (hYP : OrthSep Q Y (P₁ ⊔ P₂))
    {s : V} (hs : s ∈ P₁ ⊔ P₂) (hs0 : s ≠ 0) (hsQ : Q s = 0)
    (hrel : ∀ w ∈ P₁ ⊔ P₂, polar Q s w = 0 → w ∈ rootSet Q H s) :
    ∃ w ∈ rootSet Q H s, ∃ y ∈ Y, ∃ r : V, w = y + r ∧ (∀ z ∈ Y, polar Q z r = 0) ∧ y ≠ 0 := by
  classical
  have hP₃ne : P₃ ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hd₃
    omega
  have hXg : ∀ u ∈ P₁ ⊔ P₂, g u ∈ P₁ ⊔ P₂ := fun u hu => by
    obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Submodule.mem_sup.mp hu
    rw [map_add]
    exact Submodule.add_mem_sup (hg₁ u₁ hu₁) (hg₂ u₂ hu₂)
  have hXr : ∀ u ∈ P₁ ⊔ P₂, g (g u) = τ • g u - u := manyTwo_sqRel_sup hr₁ hr₂
  have hXP₃ : OrthSep Q (P₁ ⊔ P₂) P₃ := manyTwo_orthSep_sup_left h13 h23
  have hUg : ∀ u ∈ P₁ ⊔ P₂ ⊔ P₃, g u ∈ P₁ ⊔ P₂ ⊔ P₃ := fun u hu => by
    obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Submodule.mem_sup.mp hu
    rw [map_add]
    exact Submodule.add_mem_sup (hXg u₁ hu₁) (hg₃ u₂ hu₂)
  have hUr : ∀ u ∈ P₁ ⊔ P₂ ⊔ P₃, g (g u) = τ • g u - u := manyTwo_sqRel_sup hXr hr₃
  have hτ2 : τ ≠ 2 := fun h => hnoroot 1 (by rw [h]; norm_num)
  have hfix : ∀ u ∈ P₁ ⊔ P₂ ⊔ P₃, g u = u → u = 0 := fun u hu h => by
    have h1 := hUr u hu
    rw [h, h] at h1
    have h3 : (2 - τ) • u = 0 := by linear_combination (norm := module) h1
    exact (smul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr (Ne.symm hτ2))
  obtain ⟨s₁, hs₁, s₂, hs₂, hsum⟩ := Submodule.mem_sup.mp hs
  have hs₁0 : s₁ ≠ 0 := by
    rintro rfl
    rw [zero_add] at hsum
    exact hs0 (hsum.symm.trans (ha₂ s₂ hs₂ (by rw [hsum]; exact hsQ)))
  obtain ⟨v₃, hv₃P, hv₃0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP₃ne
  obtain ⟨v, hvdef⟩ : ∃ v : V, v = s + v₃ := ⟨_, rfl⟩
  have hvU : v ∈ P₁ ⊔ P₂ ⊔ P₃ := by rw [hvdef]; exact Submodule.add_mem_sup hs hv₃P
  have hgvU : g v ∈ P₁ ⊔ P₂ ⊔ P₃ := hUg v hvU
  have hsv₃ : polar Q s v₃ = 0 := hXP₃ s hs v₃ hv₃P
  have hsgv₃ : polar Q s (g v₃) = 0 := hXP₃ s hs _ (hg₃ v₃ hv₃P)
  have hgsv₃ : polar Q (g s) v₃ = 0 := hXP₃ _ (hXg s hs) v₃ hv₃P
  have hss : polar Q s s = 0 := polar_self_eq_zero hsQ
  have hsgs : polar Q s (g s) = 0 := polar_self_apply_eq_zero hgO hτ (hXr s hs) hsQ
  have hG00 : polar Q v₃ v₃ = polar Q v v := by
    rw [hvdef]
    simp only [polar_add_left, polar_add_right, hss, hsv₃, polar_comm Q v₃ s, zero_add, add_zero]
  have hG01 : polar Q v₃ (g v₃) = polar Q v (g v) := by
    rw [hvdef, map_add]
    simp only [polar_add_left, polar_add_right, hsgs, hsgv₃, polar_comm Q v₃ (g s), hgsv₃,
      zero_add, add_zero]
  have hG11 : polar Q (g v₃) (g v₃) = polar Q (g v) (g v) := by
    rw [TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hgO v v, ← hG00,
      TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hgO v₃ v₃]
  have hli₃ : LinearIndependent K ![v₃, g v₃] :=
    manyTwo_linearIndependent_pair hv₃0 (hr₃ v₃ hv₃P) hnoroot
  have hspan₃ : Submodule.span K {v₃, g v₃} = P₃ :=
    manyThree_span_pair_eq hd₃ hv₃P (hg₃ v₃ hv₃P) hli₃
  have hv0 : v ≠ 0 := by
    intro h0
    have h3 : v₃ ∈ P₁ ⊔ P₂ := by
      have : v₃ = -s := eq_neg_of_add_eq_zero_right (hvdef ▸ h0)
      rw [this]
      exact Submodule.neg_mem _ hs
    exact hv₃0 (hP₃ v₃ hv₃P fun y hy => hXP₃ v₃ h3 y hy)
  have hrv : g (g v) = τ • g v - v := hUr v hvU
  obtain ⟨A, hAdef⟩ : ∃ A : Submodule K V, A = Submodule.span K {v, g v} := ⟨_, rfl⟩
  have hvA : v ∈ A := hAdef ▸ Submodule.subset_span (Set.mem_insert _ _)
  have hgvA : g v ∈ A := hAdef ▸ Submodule.subset_span (by simp)
  have hAU : A ≤ P₁ ⊔ P₂ ⊔ P₃ := by
    rw [hAdef]
    exact Submodule.span_le.mpr (by rintro x (rfl | rfl); exacts [hvU, hgvU])
  have hmemA : ∀ a, a ∈ A ↔ ∃ α β : K, α • v + β • g v = a := fun a => by
    rw [hAdef]
    exact Submodule.mem_span_pair
  have h1 : ∀ u ∈ A, g u ∈ A := by
    intro u hu
    obtain ⟨α, β, rfl⟩ := (hmemA u).mp hu
    refine (hmemA _).mpr ⟨-β, α + β * τ, ?_⟩
    rw [map_add, map_smul, map_smul, hrv]
    module
  have h2 : ∀ u ∈ A, g.symm u ∈ A := by
    intro u hu
    have key : ∀ w ∈ P₁ ⊔ P₂ ⊔ P₃, g.symm w = τ • w - g w := fun w hw =>
      (LinearEquiv.symm_apply_eq g).mpr (by rw [map_sub, map_smul, hUr w hw]; module)
    rw [key u (hAU hu)]
    exact A.sub_mem (A.smul_mem _ hu) (h1 u hu)
  have hA : PolarNondegOn Q A := by
    intro a ha hperp
    obtain ⟨α, β, rfl⟩ := (hmemA a).mp ha
    have h3 : α • v₃ + β • g v₃ = 0 := by
      refine hP₃ _ (P₃.add_mem (P₃.smul_mem _ hv₃P) (P₃.smul_mem _ (hg₃ _ hv₃P))) fun y hy => ?_
      rw [← hspan₃] at hy
      obtain ⟨α', β', rfl⟩ := Submodule.mem_span_pair.mp hy
      rw [manyThree_polar_comb hG00 hG01 hG11]
      exact hperp _ ((hmemA _).mpr ⟨α', β', rfl⟩)
    obtain ⟨hα, hβ⟩ := LinearIndependent.pair_iff.mp hli₃ α β h3
    rw [hα, hβ]
    simp
  have hr : extendId hA g h1 h2 ∈ H :=
    hrot A hA h1 h2 ⟨v, hvA, fun h => hv0 (hfix v hvU h)⟩
  obtain ⟨R, hRdef⟩ : ∃ R : V ≃ₗ[K] V, R = extendId hA g h1 h2 := ⟨_, rfl⟩
  rw [← hRdef] at hr
  have hsA : s ∈ perp Q A := by
    rw [mem_perp]
    intro a ha
    obtain ⟨α, β, rfl⟩ := (hmemA a).mp ha
    have e1 : polar Q v s = 0 := by
      rw [hvdef, polar_add_left, hss, polar_comm Q v₃ s, hsv₃, add_zero]
    have e2 : polar Q (g v) s = 0 := by
      rw [hvdef, map_add, polar_add_left, polar_comm Q (g s) s, hsgs, polar_comm Q (g v₃) s,
        hsgv₃, add_zero]
    rw [polar_add_left, polar_smul_left_eq, polar_smul_left_eq, e1, e2]
    ring
  have hRs : R s = s := by
    have := extendId_apply hA h1 h2 (zero_mem A) hsA
    rw [zero_add, map_zero, zero_add] at this
    rw [hRdef]
    exact this
  have hli₁ : LinearIndependent K ![s₁, g s₁] :=
    manyTwo_linearIndependent_pair hs₁0 (hr₁ s₁ hs₁) hnoroot
  have hspan₁ : Submodule.span K {s₁, g s₁} = P₁ :=
    manyThree_span_pair_eq hd₁ hs₁ (hg₁ s₁ hs₁) hli₁
  obtain ⟨f, hfP, hf0, hfs₁⟩ :=
    manyTwo_exists_ne_zero_polar_eq_zero (Q := Q) (P := P₁) hd₁.ge s₁
  have hgf : polar Q (g s₁) f ≠ 0 := by
    intro h0
    refine hf0 (hP₁ f hfP fun y hy => ?_)
    rw [← hspan₁] at hy
    obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hy
    rw [polar_add_right, polar_smul_right_eq, polar_smul_right_eq, polar_comm Q f s₁, hfs₁,
      polar_comm Q f (g s₁), h0]
    ring
  have hsf : polar Q s f = 0 := by
    rw [← hsum, polar_add_left, hfs₁, polar_comm Q s₂ f, h12 f hfP s₂ hs₂, add_zero]
  have hgsf : polar Q (g s) f = polar Q (g s₁) f := by
    rw [← hsum, map_add, polar_add_left, polar_comm Q (g s₂) f, h12 f hfP _ (hg₂ s₂ hs₂),
      add_zero]
  have hgvf : polar Q (g v) f ≠ 0 := by
    rw [hvdef, map_add, polar_add_left, hgsf, polar_comm Q (g v₃) f,
      h13 f hfP _ (hg₃ v₃ hv₃P), add_zero]
    exact hgf
  have hfR : f ∈ rootSet Q H s := hrel f (Submodule.mem_sup_left hfP) hsf
  have hRf := rootSet_map hH hr hfR
  rw [hRs] at hRf
  have hy := AddSubgroup.sub_mem _ hRf hfR
  obtain ⟨α, hαA, β', hβ'P, hdec⟩ := Submodule.mem_sup.mp
    ((isCompl_perp hA).sup_eq_top ▸ Submodule.mem_top (x := f))
  have hRf' : R f = g α + β' := by
    rw [hRdef, ← hdec]
    exact extendId_apply hA h1 h2 hαA hβ'P
  have hyA : R f - f = g α - α := by
    rw [hRf', ← hdec]
    abel
  have hy0 : R f - f ≠ 0 := by
    intro h0
    rw [hyA, sub_eq_zero] at h0
    have hα0 : α = 0 := hfix α (hAU hαA) h0
    rw [hα0, zero_add] at hdec
    exact hgvf (by rw [← hdec]; exact mem_perp.mp hβ'P _ hgvA)
  have hyA' : R f - f ∈ A := by
    rw [hyA]
    exact A.sub_mem (h1 α hαA) hαA
  obtain ⟨d₁, d₂, hd⟩ := (hmemA _).mp hyA'
  refine ⟨R f - f, hy, d₁ • v₃ + d₂ • g v₃, ?_, d₁ • s + d₂ • g s, ?_, ?_, ?_⟩
  · exact hY (P₃.add_mem (P₃.smul_mem _ hv₃P) (P₃.smul_mem _ (hg₃ _ hv₃P)))
  · rw [← hd, hvdef, map_add]
    module
  · intro z hz
    exact hYP z hz _ (Submodule.add_mem _ (Submodule.smul_mem _ _ hs)
      (Submodule.smul_mem _ _ (hXg s hs)))
  · intro h0
    obtain ⟨hd₁0, hd₂0⟩ := LinearIndependent.pair_iff.mp hli₃ d₁ d₂ h0
    apply hy0
    rw [← hd, hd₁0, hd₂0]
    simp

end Mixed

end CFSG.LieType.SeitzGeneration
