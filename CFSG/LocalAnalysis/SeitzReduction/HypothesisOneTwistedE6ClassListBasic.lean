module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassD4
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6TwoRoots

public section

namespace CFSG.SeitzReduction

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Steinberg.Adjoint
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {K : Type} [Field K]

@[expose] def twistedE6Cascade : List (Fin TwistTag.E6.tag.rank → ℤ) :=
  [(![1, 2, 2, 3, 2, 1] : Fin 6 → ℤ), ![1, 0, 1, 1, 1, 1], ![0, 0, 1, 1, 1, 0],
    ![0, 0, 0, 1, 0, 0]]

theorem twistedE6Cascade_facts :
    twistedE6Cascade.Nodup ∧
      (∀ γ ∈ twistedE6Cascade, permLattice TwistTag.E6.perm γ = γ ∧ 0 < height γ ∧
        iform γ γ = 2) ∧
      twistedE6Cascade.Pairwise fun γ δ => iform γ δ = 0 := by
  decide

theorem isRoot_of_mem_twistedE6Cascade
    {γ : Fin TwistTag.E6.tag.rank → ℤ} (hγ : γ ∈ twistedE6Cascade) : IsRoot TwistTag.E6.tag γ := by
  have h : ∀ δ ∈ twistedE6Cascade, twistedE6TwoRootB δ = true := by decide
  exact isRoot_iff_twistedE6TwoRootB.2 (h γ hγ)

theorem conj_list_prod_map {G ι : Type*} [Group G] (g : G) (L : List ι) (f : ι → G) :
    g * (L.map f).prod * g⁻¹ = (L.map fun i => g * f i * g⁻¹).prod := by
  have h := map_list_prod (MulAut.conj g) (L.map f)
  simp only [MulAut.conj_apply, List.map_map] at h
  exact h


theorem twistedE6_weylElt_conj_pinnedX [CharP K 2] (i : Fin TwistTag.E6.tag.rank)
    {β : Fin TwistTag.E6.tag.rank → ℤ} (hβ : IsRoot TwistTag.E6.tag β) (c : K) :
    weylElt TwistTag.E6.tag K i 1 * pinnedX TwistTag.E6.tag K β c *
        (weylElt TwistTag.E6.tag K i 1)⁻¹ = pinnedX TwistTag.E6.tag K (reflect TwistTag.E6.tag i β) c := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  obtain ⟨ε, hε, h⟩ := weylElt_mul_pinnedX_mul_inv K i hβ
  have hε1 : ε = 1 := by
    have hsq : (ε - 1) ^ 2 = 0 := by linear_combination hε - (ε - 1) * h2
    exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hsq)
  rw [h, hε1, one_mul]

theorem twistedE6_list_weylElt_conj_pinnedX [CharP K 2] (ω : List (Fin TwistTag.E6.tag.rank)) :
    ∀ {β : Fin TwistTag.E6.tag.rank → ℤ}, IsRoot TwistTag.E6.tag β → ∀ c : K,
      (ω.map fun i => weylElt TwistTag.E6.tag K i 1).prod * pinnedX TwistTag.E6.tag K β c *
          ((ω.map fun i => weylElt TwistTag.E6.tag K i 1).prod)⁻¹ =
        pinnedX TwistTag.E6.tag K (ω.foldr (fun i v => reflect TwistTag.E6.tag i v) β) c := by
  induction ω with
  | nil => intro β _ c; simp
  | cons i ω ih =>
    intro β hβ c
    have hr : IsRoot TwistTag.E6.tag (ω.foldr (fun i v => reflect TwistTag.E6.tag i v) β) := by
      clear ih
      induction ω with
      | nil => exact hβ
      | cons j ω ih' => exact IsRoot.reflect j ih'
    rw [List.map_cons, List.prod_cons, List.foldr_cons,
      ← twistedE6_weylElt_conj_pinnedX i hr c, ← ih hβ c]
    group

variable (K) in
@[expose] noncomputable def twistedE6RelWeyl (ω : List (Fin TwistTag.E6.foldedTag.rank)) :
    ModGL TwistTag.E6.tag K :=
  ((ω.flatMap fun a => TwistTag.E6.orbitWord a).map fun j => weylElt TwistTag.E6.tag K j 1).prod

@[expose] def twistedE6RelAct (ω : List (Fin TwistTag.E6.foldedTag.rank))
    (β : Fin TwistTag.E6.tag.rank → ℤ) : Fin TwistTag.E6.tag.rank → ℤ :=
  (ω.flatMap fun a => TwistTag.E6.orbitWord a).foldr (fun i v => reflect TwistTag.E6.tag i v) β

theorem IsRoot.twistedE6RelAct {β : Fin TwistTag.E6.tag.rank → ℤ}
    (hβ : IsRoot TwistTag.E6.tag β) (ω : List (Fin TwistTag.E6.foldedTag.rank)) :
    IsRoot TwistTag.E6.tag (twistedE6RelAct ω β) := by
  unfold CFSG.SeitzReduction.twistedE6RelAct
  induction (ω.flatMap fun a => TwistTag.E6.orbitWord a) with
  | nil => exact hβ
  | cons j l ih => exact IsRoot.reflect j ih

theorem twistedE6RelWeyl_mem (σ : K →+* K) (ω : List (Fin TwistTag.E6.foldedTag.rank)) :
    twistedE6RelWeyl K ω ∈ graphFixedRootGroup TwistTag.E6 K σ := by
  induction ω with
  | nil => exact one_mem _
  | cons a ω ih =>
    rw [twistedE6RelWeyl, List.flatMap_cons, List.map_append, List.prod_append]
    refine mul_mem ?_ ih
    rw [← canonicalRep_orbitReflection]
    exact canonicalRep_mem_graphFixedRootGroup (TwistTag.E6.orbitReflection_mem a)

theorem twistedE6RelWeyl_conj_pinnedX [CharP K 2] (ω : List (Fin TwistTag.E6.foldedTag.rank))
    {β : Fin TwistTag.E6.tag.rank → ℤ} (hβ : IsRoot TwistTag.E6.tag β) (c : K) :
    twistedE6RelWeyl K ω * pinnedX TwistTag.E6.tag K β c * (twistedE6RelWeyl K ω)⁻¹ =
      pinnedX TwistTag.E6.tag K (twistedE6RelAct ω β) c :=
  twistedE6_list_weylElt_conj_pinnedX _ hβ c

theorem twistedE6RelWeyl_conj_list_prod [CharP K 2] (ω : List (Fin TwistTag.E6.foldedTag.rank))
    {F : List (Fin TwistTag.E6.tag.rank → ℤ)} (hF : ∀ β ∈ F, IsRoot TwistTag.E6.tag β)
    (e : (Fin TwistTag.E6.tag.rank → ℤ) → K) :
    twistedE6RelWeyl K ω * (F.map fun β => pinnedX TwistTag.E6.tag K β (e β)).prod *
        (twistedE6RelWeyl K ω)⁻¹ =
      (F.map fun β => pinnedX TwistTag.E6.tag K (twistedE6RelAct ω β) (e β)).prod := by
  rw [conj_list_prod_map]
  exact congrArg List.prod (List.map_congr_left fun β hβ =>
    twistedE6RelWeyl_conj_pinnedX ω (hF β hβ) (e β))

theorem frameTorusElt_mem_graphFixedRootGroup (σ : K →+* K)
    {γ : Fin TwistTag.E6.tag.rank → ℤ} (hγ : permLattice TwistTag.E6.perm γ = γ) {a : Kˣ}
    (ha : Units.map σ.toMonoidHom a = a) :
    frameTorusElt TwistTag.E6.tag K γ a ∈ graphFixedRootGroup TwistTag.E6 K σ := by
  have hs : ∀ i : Fin TwistTag.E6.tag.rank, TwistTag.E6.tag.symmetrizer i i = 1 := by decide
  have hγi : ∀ i : Fin TwistTag.E6.tag.rank, γ (TwistTag.E6.perm i) = γ i := fun i => by
    have h := congrFun hγ (TwistTag.E6.perm i)
    simp only [permLattice, Function.comp_apply, twistedE6_perm_symm_apply,
      twistedE6_perm_perm] at h
    exact h.symm
  have hc : ∀ i : Fin TwistTag.E6.tag.rank,
      (fun j => a ^ γ j) (TwistTag.E6.perm i) = Units.map σ.toMonoidHom ((fun j => a ^ γ j) i) :=
    fun i => by simp only [map_zpow, ha, hγi]
  obtain ⟨w, hw⟩ := exists_compatDiag_eq (t := TwistTag.E6) (σ := σ) (b := fun j => a ^ γ j) hc
  have e : frameTorusElt TwistTag.E6.tag K γ a =
      ((List.finRange TwistTag.E6.foldedTag.rank).map fun b =>
        (orbitH TwistTag.E6 K σ b (w b) : ModGL TwistTag.E6.tag K)).prod := by
    rw [list_prod_orbitH_eq_rootDiagUnit, hw, ← list_prod_torusElt_eq_rootDiagUnit,
      frameTorusElt]
    simp only [hs, one_mul]
  rw [e]
  exact list_prod_mem fun x hx => by
    obtain ⟨b, -, rfl⟩ := List.mem_map.1 hx
    exact orbitH_mem_graphFixedRootGroup TwistTag.E6 σ b (w b)

theorem exists_sq_eq_of_sigma_fixed [Finite K] [CharP K 2] (σ : K →+* K) {u : Kˣ}
    (hu : Units.map σ.toMonoidHom u = u) :
    ∃ a : Kˣ, a ^ 2 = u ∧ Units.map σ.toMonoidHom a = a := by
  obtain ⟨a, ha⟩ := frameTorus_exists_sq_eq u
  refine ⟨a, ha, ?_⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine Units.ext (frobenius_inj K 2 ?_)
  rw [frobenius_def, frobenius_def, Units.coe_map]
  change (σ (a : K)) ^ 2 = (a : K) ^ 2
  rw [← map_pow, ← Units.val_pow_eq_pow_val, ha]
  exact congrArg Units.val hu

theorem exists_twistedE6_torus_conj_frame_prod [Finite K] [CharP K 2] (σ : K →+* K)
    {F : List (Fin TwistTag.E6.tag.rank → ℤ)}
    (hF : ∀ γ ∈ F, IsRoot TwistTag.E6.tag γ ∧ permLattice TwistTag.E6.perm γ = γ)
    (horth : F.Pairwise fun γ δ => iform γ δ = 0) (c : (Fin TwistTag.E6.tag.rank → ℤ) → K)
    (hc : ∀ γ ∈ F, c γ ≠ 0 ∧ σ (c γ) = c γ) :
    ∃ h ∈ graphFixedRootGroup TwistTag.E6 K σ,
      (∀ δ, IsRoot TwistTag.E6.tag δ → (∀ γ ∈ F, iform γ δ = 0) → ∀ e : K,
        h * pinnedX TwistTag.E6.tag K δ e * h⁻¹ = pinnedX TwistTag.E6.tag K δ e) ∧
      h * (F.map fun γ => pinnedX TwistTag.E6.tag K γ (c γ)).prod * h⁻¹ =
        (F.map fun γ => pinnedX TwistTag.E6.tag K γ 1).prod := by
  induction F with
  | nil =>
    exact ⟨1, one_mem _, fun δ _ _ e => by rw [one_mul, inv_one, mul_one], by simp⟩
  | cons γ F ih =>
    obtain ⟨hγF, hFF⟩ := List.pairwise_cons.1 horth
    obtain ⟨h', hC', hfix', hprod'⟩ := ih (fun δ h => hF δ (List.mem_cons_of_mem _ h)) hFF
      fun δ h => hc δ (List.mem_cons_of_mem _ h)
    obtain ⟨hγr, hγρ⟩ := hF γ List.mem_cons_self
    obtain ⟨hc0, hcσ⟩ := hc γ List.mem_cons_self
    have hγγ : iform γ γ = 2 := classD4_iform_self (Or.inr (Or.inl rfl)) hγr
    obtain ⟨a, ha, haσ⟩ := exists_sq_eq_of_sigma_fixed σ (u := (Units.mk0 (c γ) hc0)⁻¹)
      (Units.ext (by simp [hcσ]))
    set A := frameTorusElt TwistTag.E6.tag K γ a with hA
    have hfixA : ∀ δ, IsRoot TwistTag.E6.tag δ → iform γ δ = 0 → ∀ e : K,
        A * pinnedX TwistTag.E6.tag K δ e * A⁻¹ = pinnedX TwistTag.E6.tag K δ e :=
      fun δ hδ h0 e => by
        rw [hA, frameTorusElt_conj_pinnedX _ _ hδ, h0, zpow_zero, Units.val_one, one_mul]
    refine ⟨A * h', mul_mem (frameTorusElt_mem_graphFixedRootGroup σ hγρ haσ) hC',
      fun δ hδ hδF e => ?_, ?_⟩
    · rw [show A * h' * pinnedX TwistTag.E6.tag K δ e * (A * h')⁻¹ =
          A * (h' * pinnedX TwistTag.E6.tag K δ e * h'⁻¹) * A⁻¹ by group,
        hfix' δ hδ (fun γ' h => hδF γ' (List.mem_cons_of_mem _ h)) e,
        hfixA δ hδ (hδF γ List.mem_cons_self) e]
    · have hγ' : ∀ δ ∈ F, iform δ γ = 0 := fun δ h => by rw [iform_comm]; exact hγF δ h
      rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons,
        show A * h' * (pinnedX TwistTag.E6.tag K γ (c γ) *
            (F.map fun γ => pinnedX TwistTag.E6.tag K γ (c γ)).prod) * (A * h')⁻¹ =
          A * (h' * pinnedX TwistTag.E6.tag K γ (c γ) * h'⁻¹) * A⁻¹ *
            (A * (h' * (F.map fun γ => pinnedX TwistTag.E6.tag K γ (c γ)).prod * h'⁻¹) * A⁻¹)
          by group,
        hfix' γ hγr hγ' (c γ), hprod', frameTorusElt_conj_pinnedX _ _ hγr, hγγ,
        show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, ha]
      have hcoef : (((Units.mk0 (c γ) hc0)⁻¹ : Kˣ) : K) * c γ = 1 := by
        simp only [Units.val_inv_eq_inv_val, Units.val_mk0]
        exact inv_mul_cancel₀ hc0
      rw [hcoef, frameTorus_conj_list_prod_of_forall A _ fun x hx => ?_]
      obtain ⟨δ, hδF, rfl⟩ := List.mem_map.1 hx
      exact hfixA δ (hF δ (List.mem_cons_of_mem _ hδF)).1 (hγF δ hδF) 1

theorem exists_conj_mem_graphFixedPosUnipotent_of_sq_eq_one [Finite K] [CharP K 2]
    (σ : K ≃+* K) {x : graphFixedRootGroup TwistTag.E6 K σ.toRingHom} (hx : x ^ 2 = 1) :
    ∃ g : graphFixedRootGroup TwistTag.E6 K σ.toRingHom,
      ((g * x * g⁻¹ : graphFixedRootGroup TwistTag.E6 K σ.toRingHom) : ModGL TwistTag.E6.tag K) ∈
        graphFixedPosUnipotent TwistTag.E6 K σ.toRingHom := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := finite_modGL (τ := TwistTag.E6.tag) (K := K)
  obtain ⟨w₀, hw₀⟩ :=
    Finite.exists_max fun w : WeylGroup TwistTag.E6.tag => (coxeterSystem TwistTag.E6.tag).length w
  obtain ⟨P, hP⟩ := (exceptional_fixed_Sylow_opposition TwistTag.E6 K 2 σ w₀ hw₀).1
  have hto : orderOf x ∣ 2 ^ 1 := by simpa using orderOf_dvd_of_pow_eq_one hx
  obtain ⟨l, -, hl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hto
  have htp : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := l) (by rw [Nat.card_zpowers, hl])
  obtain ⟨Q, hQ⟩ := htp.exists_le_sylow
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) P Q
  have hxQ : x ∈ (Q : Subgroup (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) :=
    hQ (Subgroup.mem_zpowers x)
  rw [← ha, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, hP,
    MulAut.smul_def, MulAut.conj_inv_apply] at hxQ
  refine ⟨a⁻¹, ?_⟩
  rw [inv_inv]
  exact Subgroup.mem_subgroupOf.1 hxQ

end CFSG.SeitzReduction
