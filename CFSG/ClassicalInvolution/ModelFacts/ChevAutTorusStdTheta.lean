module

public import CFSG.ClassicalInvolution.ModelFacts.ChevAutTorusAct

public section

namespace CFSG.ClassicalInvolution.ModelFacts.ChevAut

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.ClassicalInvolution.ModelFacts

section Zfix

variable {K : Type*} [Group K]

@[expose] def Zfix (α : K →* K) : Subgroup K :=
  MonoidHom.eqLocus ((QuotientGroup.mk' (Subgroup.center K)).comp α)
    (QuotientGroup.mk' (Subgroup.center K))

theorem mem_Zfix {α : K →* K} {t : K} : t ∈ Zfix α ↔ α t * t⁻¹ ∈ Subgroup.center K := by
  change (QuotientGroup.mk (α t) : K ⧸ Subgroup.center K) = QuotientGroup.mk t ↔ _
  rw [QuotientGroup.eq]
  constructor
  · intro h
    have e : α t * t⁻¹ = t * ((α t)⁻¹ * t)⁻¹ * t⁻¹ := by group
    have hc := Subgroup.mem_center_iff.1 (inv_mem h) t
    rw [e, hc]
    simpa using inv_mem h
  · intro h
    have e : (α t)⁻¹ * t = t⁻¹ * (α t * t⁻¹)⁻¹ * t := by group
    have hc := Subgroup.mem_center_iff.1 (inv_mem h) t⁻¹
    rw [e, hc, inv_mul_cancel_right]
    exact inv_mem h

theorem center_le_Zfix (α : K ≃* K) : Subgroup.center K ≤ Zfix α.toMonoidHom := by
  intro z hz
  rw [mem_Zfix]
  have hαz : α z ∈ Subgroup.center K := by
    rw [Subgroup.mem_center_iff]
    intro k
    obtain ⟨k', rfl⟩ := α.surjective k
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz k']
  exact mul_mem hαz (inv_mem hz)

end Zfix

section Tact

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {F : Type} [Field F]
  {x : (Fin D.rank → ℤ) → F → K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}
  {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
  {O : CommOrder (RootSystem.ofCartan D.isFiniteType D.divisible)}

theorem mem_center_of_tact_eq (hS : TorusSetup D x n H) {t₁ t₂ : K}
    (h : ∀ γ ∈ D.roots, ∃ l : Fˣ, TAct x t₁ γ l ∧ TAct x t₂ γ l) :
    t₁⁻¹ * t₂ ∈ Subgroup.center K := by
  obtain ⟨C, O, hE⟩ := hS.chev
  set u := t₁⁻¹ * t₂ with hu
  have hle : (⨆ γ ∈ D.roots, D.rootGroup γ) ≤ Subgroup.centralizer {u} := by
    refine iSup₂_le fun γ hγ y hy => ?_
    obtain ⟨c, rfl⟩ := ((hE.param γ hγ).1 y).1 hy
    obtain ⟨l, h1, h2⟩ := h γ hγ
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    rw [Set.mem_singleton_iff] at hv
    subst hv
    have e1 : t₁ * x γ c * t₁⁻¹ = x γ ((l : F) * c) := h1 c
    have e2 : t₂ * x γ c * t₂⁻¹ = x γ ((l : F) * c) := h2 c
    have e3 : t₂ * x γ c * t₂⁻¹ = t₁ * x γ c * t₁⁻¹ := by rw [e1, e2]
    calc (t₁⁻¹ * t₂) * x γ c = t₁⁻¹ * (t₂ * x γ c * t₂⁻¹) * t₂ := by group
      _ = t₁⁻¹ * (t₁ * x γ c * t₁⁻¹) * t₂ := by rw [e3]
      _ = x γ c * (t₁⁻¹ * t₂) := by group
  rw [hS.ct.iSup_eq_top] at hle
  rw [Subgroup.mem_center_iff]
  intro g
  have := Subgroup.mem_centralizer_iff.1 (hle (Subgroup.mem_top g)) u (Set.mem_singleton u)
  exact this.symm

theorem tact_list_prod (hE : ChevalleyExtras D F x C O) (L : List (Fin D.rank)) (hL : L.Nodup)
    (u : Fin D.rank → Fˣ) {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots) :
    TAct x ((L.map fun j => torusGen x j (u j)).prod) γ
      (∏ j ∈ L.toFinset, u j ^ pair D.cartan γ j) := by
  induction L with
  | nil =>
    simpa using TAct.one γ
  | cons j L ih =>
    rw [List.nodup_cons] at hL
    rw [List.map_cons, List.prod_cons, List.toFinset_cons, Finset.prod_insert
      (by simpa using hL.1)]
    exact (torusGen_act hE hγ j (u j)).mul (ih hL.2)

end Tact



section Form

variable {r : ℕ} {A : Matrix (Fin r) (Fin r) ℤ} (hA : TauCeti.IsFiniteType A)
  (hlong : ∀ k, IsLongest hA ∅ (Pi.single k 1))

include hlong

theorem pair_weylAction_inv_eq (θ : Fin r → ℤ) (w₀ : (coxeterMatrix hA).Group) (i₀ : Fin r)
    (hθ : θ = weylAction hA w₀ (Pi.single i₀ 1)) (γ : Fin r → ℤ) :
    pair A (weylAction hA w₀⁻¹ γ) i₀ = ∑ j, θ j * pair A γ j := by
  have hd := symmetrizer_pos hA i₀
  have hsym : ∀ l, symmetrizer hA l = symmetrizer hA i₀ := fun l => symmetrizer_const hA hlong l i₀
  have h1 := form_single_right_int hA (weylAction hA w₀⁻¹ γ) i₀
  have h2 : form hA (toRat (weylAction hA w₀⁻¹ γ)) (toRat (Pi.single i₀ 1)) =
      form hA (toRat γ) (toRat θ) := by
    have := form_weylAction hA w₀ (weylAction hA w₀⁻¹ γ) (Pi.single i₀ 1)
    rw [weylAction_apply_inv_apply, ← hθ] at this
    exact this.symm
  have h3 : form hA (toRat γ) (toRat θ) =
      symmetrizer hA i₀ * ∑ j, (θ j : ℚ) * (pair A γ j : ℚ) := by
    rw [form_eq_sum]
    simp only [toRat_apply]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← toRat_single, form_single_right_int hA γ j, hsym j]
    ring
  have h4 : symmetrizer hA i₀ * (pair A (weylAction hA w₀⁻¹ γ) i₀ : ℚ) =
      symmetrizer hA i₀ * ∑ j, (θ j : ℚ) * (pair A γ j : ℚ) := by
    rw [← h1, h2, h3]
  have h5 := mul_left_cancel₀ hd.ne' h4
  exact_mod_cast h5

end Form


section Theta

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {F : Type} [Field F]
  {x : (Fin D.rank → ℤ) → F → K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}

@[expose] noncomputable def thetaTorus (hS : TorusSetup D x n H)
    (w₀ : (coxeterMatrix D.isFiniteType).Group) (i₀ : Fin D.rank) (s : Fˣ) : K :=
  nrep hS.ct w₀ * torusGen x i₀ s * (nrep hS.ct w₀)⁻¹

theorem thetaTorus_mem (hS : TorusSetup D x n H) (w₀ : (coxeterMatrix D.isFiniteType).Group)
    (i₀ : Fin D.rank) (s : Fˣ) : thetaTorus hS w₀ i₀ s ∈ ⨆ i, H i :=
  conj_mem_iSup_of_mem_weylN hS.ct (nrep_mem_weylN hS.ct w₀) (hS.torusGen_mem i₀ s)

theorem thetaTorus_mem_rankOne (hS : TorusSetup D x n H)
    (w₀ : (coxeterMatrix D.isFiniteType).Group) (i₀ : Fin D.rank) (s : Fˣ)
    {θ : Fin D.rank → ℤ} (hθ : θ = weylAction D.isFiniteType w₀ (Pi.single i₀ 1)) :
    thetaTorus hS w₀ i₀ s ∈ D.rootGroup θ ⊔ D.rootGroup (-θ) := by
  obtain ⟨C, O, hE⟩ := hS.chev
  have hα : (Pi.single i₀ 1 : Fin D.rank → ℤ) ∈ D.roots :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i₀
  have hαn : -(Pi.single i₀ 1 : Fin D.rank → ℤ) ∈ D.roots :=
    CFSG.LieType.Steinberg.OfCartan.neg_mem_roots D.isFiniteType hα
  have hθr : θ ∈ D.roots := by
    rw [hθ]
    exact weylAction_mem_roots D.isFiniteType w₀ hα
  have hθn : -θ ∈ D.roots := CFSG.LieType.Steinberg.OfCartan.neg_mem_roots D.isFiniteType hθr
  obtain ⟨ε, hε, hεc⟩ := signConj_nrep hE hS.ct hS.n_eq w₀ _ hα
  obtain ⟨ε', hε', hεc'⟩ := signConj_nrep hE hS.ct hS.n_eq w₀ _ hαn
  rw [← hθ] at hεc
  rw [map_neg, ← hθ] at hεc'
  have hX : ∀ c : F, nrep hS.ct w₀ * x (Pi.single i₀ 1) c * (nrep hS.ct w₀)⁻¹ ∈
      D.rootGroup θ ⊔ D.rootGroup (-θ) := fun c => by
    rw [hεc c]
    exact Subgroup.mem_sup_left (((hE.param θ hθr).1 _).2 ⟨_, rfl⟩)
  have hY : ∀ c : F, nrep hS.ct w₀ * x (-Pi.single i₀ 1) c * (nrep hS.ct w₀)⁻¹ ∈
      D.rootGroup θ ⊔ D.rootGroup (-θ) := fun c => by
    rw [hεc' c]
    exact Subgroup.mem_sup_right (((hE.param (-θ) hθn).1 _).2 ⟨_, rfl⟩)
  have hW : ∀ t : Fˣ, nrep hS.ct w₀ * weylElement x i₀ t * (nrep hS.ct w₀)⁻¹ ∈
      D.rootGroup θ ⊔ D.rootGroup (-θ) := fun t => by
    have e : nrep hS.ct w₀ * weylElement x i₀ t * (nrep hS.ct w₀)⁻¹ =
        (nrep hS.ct w₀ * x (Pi.single i₀ 1) t * (nrep hS.ct w₀)⁻¹) *
          (nrep hS.ct w₀ * x (-Pi.single i₀ 1) (-((t⁻¹ : Fˣ) : F)) * (nrep hS.ct w₀)⁻¹) *
            (nrep hS.ct w₀ * x (Pi.single i₀ 1) t * (nrep hS.ct w₀)⁻¹) := by
      unfold weylElement
      group
    rw [e]
    exact mul_mem (mul_mem (hX _) (hY _)) (hX _)
  have e : thetaTorus hS w₀ i₀ s =
      (nrep hS.ct w₀ * weylElement x i₀ s * (nrep hS.ct w₀)⁻¹) *
        (nrep hS.ct w₀ * weylElement x i₀ 1 * (nrep hS.ct w₀)⁻¹)⁻¹ := by
    unfold thetaTorus torusGen
    group
  rw [e]
  exact mul_mem (hW s) (inv_mem (hW 1))

theorem tact_thetaTorus (hS : TorusSetup D x n H) (w₀ : (coxeterMatrix D.isFiniteType).Group)
    (i₀ : Fin D.rank) (s : Fˣ) {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots) :
    TAct x (thetaTorus hS w₀ i₀ s) γ
      (s ^ pair D.cartan (weylAction D.isFiniteType w₀⁻¹ γ) i₀) := by
  obtain ⟨C, O, hE⟩ := hS.chev
  have hδ : weylAction D.isFiniteType w₀⁻¹ γ ∈ D.roots :=
    weylAction_mem_roots D.isFiniteType w₀⁻¹ hγ
  obtain ⟨ε, hε, hεc⟩ := signConj_nrep hE hS.ct hS.n_eq w₀ _ hδ
  have hy : ∀ c : F, nrep hS.ct w₀ * x (weylAction D.isFiniteType w₀⁻¹ γ) c *
      (nrep hS.ct w₀)⁻¹ = x γ ((ε : F) * c) := fun c => by
    have := hεc c
    rwa [weylAction_apply_inv_apply] at this
  exact TAct.conj_of_sign hε hy (torusGen_act hE hδ i₀ s)

end Theta


section FixSub

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {F : Type} [Field F]
  {x : (Fin D.rank → ℤ) → F → K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}

theorem torusGen_sq_mem_Zfix (hS : TorusSetup D x n H)
    (hlong : ∀ k, IsLongest D.isFiniteType ∅ (Pi.single k 1)) (ν : Fin D.rank)
    (θ : Fin D.rank → ℤ) (hθr : θ ∈ D.roots) (hθ2 : θ ν = 2) (α : K ≃* K)
    (H2 : ∀ j, j ≠ ν → ∀ s, torusGen x j s ∈ Zfix α.toMonoidHom)
    (H1 : ∀ y ∈ D.rootGroup θ ⊔ D.rootGroup (-θ), y ∈ Zfix α.toMonoidHom) (s : Fˣ) :
    torusGen x ν (s ^ 2) ∈ Zfix α.toMonoidHom := by
  obtain ⟨C, O, hE⟩ := hS.chev
  have hθ0 : θ ∈ roots D.isFiniteType D.divisible := hθr
  obtain ⟨w₀, i₀, hw₀⟩ : ∃ (w₀ : (coxeterMatrix D.isFiniteType).Group) (i₀ : Fin D.rank),
      θ = weylAction D.isFiniteType w₀ (Pi.single i₀ 1) := by
    rcases hθ0 with ⟨w, i, h⟩ | ⟨w, i, hi, -⟩
    · exact ⟨w, i, h⟩
    · rw [hS.div] at hi
      exact absurd hi (Set.notMem_empty _)
  set L : List (Fin D.rank) := (List.finRange D.rank).erase ν with hLdef
  have hL : L.Nodup := (List.nodup_finRange D.rank).erase ν
  have hLmem : ∀ j, j ∈ L ↔ j ≠ ν := fun j => by
    rw [hLdef, (List.nodup_finRange D.rank).mem_erase_iff]
    simp
  have hLfin : L.toFinset = Finset.univ.erase ν := by
    ext j
    simp [hLmem]
  set P : K := (L.map fun j => torusGen x j (s ^ θ j)).prod with hP
  have hPmem : P ∈ Zfix α.toMonoidHom := by
    refine Subgroup.list_prod_mem _ fun t ht => ?_
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 ht
    exact H2 j ((hLmem j).1 hj) _
  have hHθ : thetaTorus hS w₀ i₀ s ∈ Zfix α.toMonoidHom :=
    H1 _ (thetaTorus_mem_rankOne hS w₀ i₀ s hw₀)
  have hR : thetaTorus hS w₀ i₀ s * P⁻¹ ∈ Zfix α.toMonoidHom := mul_mem hHθ (inv_mem hPmem)
  have hcen : (torusGen x ν (s ^ 2))⁻¹ * (thetaTorus hS w₀ i₀ s * P⁻¹) ∈ Subgroup.center K := by
    refine mem_center_of_tact_eq hS fun γ hγ => ⟨(s ^ 2) ^ pair D.cartan γ ν, ?_, ?_⟩
    · exact torusGen_act hE hγ ν (s ^ 2)
    · have h1 := tact_thetaTorus hS w₀ i₀ s hγ
      rw [pair_weylAction_inv_eq D.isFiniteType (hlong) θ w₀ i₀ hw₀] at h1
      have h2 := tact_list_prod hE L hL (fun j => s ^ θ j) hγ
      have h3 := h1.mul h2.inv
      convert h3 using 1
      rw [hLfin]
      have e1 : s ^ (∑ j, θ j * pair D.cartan γ j) =
          (∏ j ∈ Finset.univ.erase ν, (s ^ θ j) ^ pair D.cartan γ j) *
            (s ^ θ ν) ^ pair D.cartan γ ν := by
        rw [← Finset.prod_zpow_eq_zpow_sum,
          ← Finset.prod_erase_mul Finset.univ _ (Finset.mem_univ ν)]
        simp only [zpow_mul]
      have e2 : s ^ θ ν = s ^ 2 := by
        rw [hθ2]
        simp
      rw [e1, e2, mul_comm (∏ j ∈ Finset.univ.erase ν, (s ^ θ j) ^ pair D.cartan γ j),
        mul_inv_cancel_right]
  have e : torusGen x ν (s ^ 2) = (thetaTorus hS w₀ i₀ s * P⁻¹) *
      ((torusGen x ν (s ^ 2))⁻¹ * (thetaTorus hS w₀ i₀ s * P⁻¹))⁻¹ := by group
  rw [e]
  exact mul_mem hR (center_le_Zfix α (inv_mem hcen))

end FixSub

end CFSG.ClassicalInvolution.ModelFacts.ChevAut
