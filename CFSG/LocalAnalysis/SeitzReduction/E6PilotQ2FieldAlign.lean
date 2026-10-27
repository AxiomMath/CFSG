module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotQ2FieldCore
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotQ2FieldSL2

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Open CFSG.EvenSmallLie CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley CFSG.Timmesfeld.LieEmbed CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg
open CFSG.Quasithin (perfectCore perfectCore_le perfectCore_mono le_perfectCore_of_perfect)
open CFSG.SeitzReduction.F4Pilot (F4Work QuadraticFrobenius centralizerPerfectCore)

local instance e6PilotQ2FieldAlignNeZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩

section Words


variable (K : Type) [Field K]

noncomputable abbrev q2WordElt (ω : List (Fin (Tag.rank .E6))) : ModGL .E6 K :=
  (ω.map fun i => weylElt .E6 K i 1).prod

variable {K}

theorem q2WordElt_append (ω₁ ω₂ : List (Fin (Tag.rank .E6))) :
    q2WordElt K (ω₁ ++ ω₂) = q2WordElt K ω₁ * q2WordElt K ω₂ := by
  simp [q2WordElt, List.prod_append]

theorem q2WordElt_cons (i : Fin (Tag.rank .E6)) (ω : List (Fin (Tag.rank .E6))) :
    q2WordElt K (i :: ω) = weylElt .E6 K i 1 * q2WordElt K ω := by
  simp [q2WordElt]

theorem q2WordElt_singleton (i : Fin (Tag.rank .E6)) :
    q2WordElt K [i] = weylElt .E6 K i 1 := by
  simp [q2WordElt]

theorem q2WordElt_mem_adjointGroup (ω : List (Fin (Tag.rank .E6))) :
    q2WordElt K ω ∈ adjointGroup .E6 K :=
  Subgroup.list_prod_mem _ fun g hg => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
    exact weylElt_mem_adjointGroup i 1


theorem baseChangeGL_q2WordElt {k : Type} [Field k] (ι : k →+* K)
    (ω : List (Fin (Tag.rank .E6))) : baseChangeGL ι (q2WordElt k ω) = q2WordElt K ω := by
  rw [q2WordElt, map_list_prod, List.map_map]
  congr 1
  exact List.map_congr_left fun i _ => baseChangeGL_weylElt_one_E6 ι i

theorem weylElt_one_mul_self_E6 [CharP K 2] (i : Fin (Tag.rank .E6)) :
    weylElt .E6 K i 1 * weylElt .E6 K i 1 = 1 := by
  rw [CFSG.LieType.Chevalley.weylElt_one_mul_self,
    show (-1 : Kˣ) = 1 from Units.ext (CharTwo.neg_eq 1), torusElt_one]

theorem q2WordElt_reverse [CharP K 2] (ω : List (Fin (Tag.rank .E6))) :
    q2WordElt K ω.reverse = (q2WordElt K ω)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  induction ω with
  | nil => simp [q2WordElt]
  | cons i ω ih =>
    rw [List.reverse_cons, q2WordElt_append, q2WordElt_singleton, q2WordElt_cons]
    calc q2WordElt K ω.reverse * weylElt .E6 K i 1 * (weylElt .E6 K i 1 * q2WordElt K ω) =
        q2WordElt K ω.reverse * (weylElt .E6 K i 1 * weylElt .E6 K i 1) * q2WordElt K ω := by
          group
      _ = 1 := by rw [weylElt_one_mul_self_E6, mul_one, ih]

theorem weylElt_mem_rootSpan_E6 {S : Set (Fin (Tag.rank .E6) → ℤ)} {i : Fin (Tag.rank .E6)}
    (h1 : (Pi.single i 1 : Fin (Tag.rank .E6) → ℤ) ∈ S) (h2 : -Pi.single i 1 ∈ S) :
    weylElt .E6 K i 1 ∈ rootSpan .E6 K S := by
  have hx : ∀ c : K, xUnit .E6 K i c ∈ rootSpan .E6 K S := fun c => by
    rw [← pinnedX_single]
    exact le_iSup₂_of_le (f := fun α (_ : α ∈ S) => rootSubgroup .E6 K α) _ h1 le_rfl
      (subset_closure ⟨c, rfl⟩)
  have hy : ∀ c : K, yUnit .E6 K i c ∈ rootSpan .E6 K S := fun c => by
    rw [← pinnedX_neg_single]
    exact le_iSup₂_of_le (f := fun α (_ : α ∈ S) => rootSubgroup .E6 K α) _ h2 le_rfl
      (subset_closure ⟨c, rfl⟩)
  rw [CFSG.Blueprint.Chevalley.weylElt_eq_xUnit_mul]
  exact mul_mem (mul_mem (hx _) (hy _)) (hx _)

theorem q2WordElt_mem_rootSpan {S : Set (Fin (Tag.rank .E6) → ℤ)} {ω : List (Fin (Tag.rank .E6))}
    (h : ∀ i ∈ ω, (Pi.single i 1 : Fin (Tag.rank .E6) → ℤ) ∈ S ∧ -Pi.single i 1 ∈ S) :
    q2WordElt K ω ∈ rootSpan .E6 K S :=
  list_prod_mem fun x hx => by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    exact weylElt_mem_rootSpan_E6 (h i hi).1 (h i hi).2

end Words

section Conj


variable {K : Type} [Field K] [CharP K 2]

theorem weylElt_conj_pinnedX_E6 (i : Fin (Tag.rank .E6)) {δ : Fin (Tag.rank .E6) → ℤ}
    (hδ : IsRoot .E6 δ) (c : K) :
    weylElt .E6 K i 1 * pinnedX .E6 K δ c * (weylElt .E6 K i 1)⁻¹ =
      pinnedX .E6 K (reflect .E6 i δ) c := by
  obtain ⟨ε, hε, h⟩ := weylElt_mul_pinnedX_mul_inv K i hδ
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hε1 : ε = 1 := by
    have hsq : (ε - 1) ^ 2 = 0 := by linear_combination hε - (ε - 1) * h2
    exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hsq)
  rw [h, hε1, one_mul]

theorem q2WordElt_conj_pinnedX (ω : List (Fin (Tag.rank .E6))) {δ : Fin (Tag.rank .E6) → ℤ}
    (hδ : IsRoot .E6 δ) (c : K) :
    q2WordElt K ω * pinnedX .E6 K δ c * (q2WordElt K ω)⁻¹ =
      pinnedX .E6 K ((coxeterSystem .E6).wordProd ω • δ) c := by
  induction ω with
  | nil => simp [q2WordElt]
  | cons i ω ih =>
    rw [q2WordElt_cons, (coxeterSystem .E6).wordProd_cons, mul_smul, simple_smul]
    calc weylElt .E6 K i 1 * q2WordElt K ω * pinnedX .E6 K δ c *
          (weylElt .E6 K i 1 * q2WordElt K ω)⁻¹ =
        weylElt .E6 K i 1 * (q2WordElt K ω * pinnedX .E6 K δ c * (q2WordElt K ω)⁻¹) *
          (weylElt .E6 K i 1)⁻¹ := by group
      _ = _ := by rw [ih, weylElt_conj_pinnedX_E6 i (IsRoot.smul hδ _)]

theorem q2WordElt_reflWord_mem_rootSpan {S : Set (Fin (Tag.rank .E6) → ℤ)}
    (v : List (Fin (Tag.rank .E6))) (i : Fin (Tag.rank .E6))
    (h1 : (coxeterSystem .E6).wordProd v • (Pi.single i 1 : Fin (Tag.rank .E6) → ℤ) ∈ S)
    (h2 : -((coxeterSystem .E6).wordProd v • (Pi.single i 1 : Fin (Tag.rank .E6) → ℤ)) ∈ S) :
    q2WordElt K (v ++ [i] ++ v.reverse) ∈ rootSpan .E6 K S := by
  rw [q2WordElt_append, q2WordElt_append, q2WordElt_singleton, q2WordElt_reverse]
  have hmem : weylElt .E6 K i 1 ∈ rootSpan .E6 K {Pi.single i 1, -Pi.single i 1} :=
    weylElt_mem_rootSpan_E6 (by simp) (by simp)
  have hconj : (rootSpan .E6 K {Pi.single i 1, -Pi.single i 1}).map
      (MulAut.conj (q2WordElt K v)).toMonoidHom ≤ rootSpan .E6 K S := by
    simp only [rootSpan, Subgroup.map_iSup]
    refine iSup₂_le fun α hα => ?_
    rcases hα with rfl | hα
    · rw [map_conj_prod_weylElt_rootSubgroup K v (isRoot_single _ i)]
      exact le_iSup₂_of_le (f := fun α (_ : α ∈ S) => rootSubgroup .E6 K α) _ h1 le_rfl
    · rw [Set.mem_singleton_iff] at hα
      rw [hα, map_conj_prod_weylElt_rootSubgroup K v (isRoot_neg_single _ i), smul_neg]
      exact le_iSup₂_of_le (f := fun α (_ : α ∈ S) => rootSubgroup .E6 K α) _ h2 le_rfl
  exact hconj ⟨_, hmem, rfl⟩

end Conj

section Twist


variable {K : Type} [Field K] {σ : K ≃+* K} {G : Type} [Group G] [Finite G] {L : Subgroup G}
  {e : L ≃* adjointGroup .E6 (fixSubfield σ)}

omit [Finite G] in
theorem pinnedX_mem_rootSpan_orthRoots_E6 {F : Type} [Field F] {N : E6Neighbour}
    {γ : Fin (Tag.rank .E6) → ℤ} (hγ : γ ∈ orthRoots N.root) (a : F) :
    pinnedX .E6 F γ a ∈ rootSpan .E6 F (orthRoots N.root) :=
  le_iSup₂_of_le (f := fun α (_ : α ∈ orthRoots N.root) => rootSubgroup .E6 F α) γ hγ le_rfl
    (subset_closure ⟨a, rfl⟩)

omit [Finite G] in
@[expose] noncomputable def q2LeviRootElt {F : Type} [Field F] (N : E6Neighbour)
    {γ : Fin (Tag.rank .E6) → ℤ} (hγ : γ ∈ orthRoots N.root) (a : F) : N.levi F :=
  ⟨⟨pinnedX .E6 F γ a, pinnedX_mem_adjointGroup γ a⟩,
    mem_subgroupOf.2 (pinnedX_mem_rootSpan_orthRoots_E6 hγ a)⟩

omit [Finite G] in
theorem coe_q2LeviRootElt {F : Type} [Field F] (N : E6Neighbour) {γ : Fin (Tag.rank .E6) → ℤ}
    (hγ : γ ∈ orthRoots N.root) (a : F) :
    (((q2LeviRootElt N hγ a : N.levi F) : adjointGroup .E6 F) : ModGL .E6 F) =
      pinnedX .E6 F γ a :=
  rfl

omit [Finite G] in
theorem q2LeviRootElt_mul_self {F : Type} [Field F] [CharP F 2] (N : E6Neighbour)
    {γ : Fin (Tag.rank .E6) → ℤ} (hγ : γ ∈ orthRoots N.root) (a : F) :
    q2LeviRootElt N hγ a * q2LeviRootElt N hγ a = 1 := by
  refine Subtype.ext (Subtype.ext ?_)
  simp only [Subgroup.coe_mul, coe_q2LeviRootElt, OneMemClass.coe_one]
  rw [← pinnedX_add, CharTwo.add_self_eq_zero, pinnedX_zero]

omit [Finite G] in
theorem leviInclusion_q2LeviRootElt {N : E6Neighbour} {γ : Fin (Tag.rank .E6) → ℤ}
    (hγ : γ ∈ orthRoots N.root) (c : fixSubfield σ) :
    leviInclusion σ N (q2LeviRootElt N hγ c) = q2LeviRootElt N hγ (c : K) :=
  Subtype.ext (Subtype.ext (baseChangeGL_pinnedX _ γ c))

@[expose] def TwoCover.TwistAt {N N' : E6Neighbour} {E E' : Subgroup G} (h : TwoCover σ e N E)
    (h' : TwoCover σ e N' E') (ρ : K ≃+* K) (γ : Fin (Tag.rank .E6) → ℤ) : Prop :=
  ∀ (hγ : γ ∈ orthRoots N.root) (hγ' : γ ∈ orthRoots N'.root) (a : K) (g g' : G),
    h.IsLift (q2LeviRootElt N hγ a) g → h'.IsLift (q2LeviRootElt N' hγ' (ρ a)) g' → g = g'

theorem TwoCover.isLift_q2LeviRootElt_fix [CharP K 2] {N : E6Neighbour} {E : Subgroup G}
    (h : TwoCover σ e N E) {γ : Fin (Tag.rank .E6) → ℤ} (hγ : γ ∈ orthRoots N.root)
    (c : fixSubfield σ) :
    h.IsLift (q2LeviRootElt N hγ (c : K))
      ((e.symm ((q2LeviRootElt N hγ c : N.levi (fixSubfield σ)) :
        adjointGroup .E6 (fixSubfield σ)) : L) : G) := by
  rw [← leviInclusion_q2LeviRootElt]
  refine h.isLift_leviInclusion _ (leviBaseChange_injective (fixSubfield σ).subtype N ?_)
  change leviInclusion σ N _ = leviInclusion σ N 1
  rw [map_mul, leviInclusion_q2LeviRootElt, q2LeviRootElt_mul_self, map_one]

theorem TwoCover.isLift_of_section' {N : E6Neighbour} {E : Subgroup G} (h : TwoCover σ e N E)
    {H : Subgroup (adjointGroup .E6 K)} (s : H →* E)
    (hs : ∀ y, ((h.p (s y) : N.levi K) : adjointGroup .E6 K) = y) (y : H) (u : N.levi K)
    (hyu : (y : adjointGroup .E6 K) = u) (hu : u * u = 1) : h.IsLift u (s y : G) := by
  refine ⟨s y, rfl, Subtype.ext ((hs y).trans hyu), ?_⟩
  have hyy : y * y = 1 := Subtype.ext (by
    rw [Subgroup.coe_mul, hyu, OneMemClass.coe_one, ← Subgroup.coe_mul, hu, OneMemClass.coe_one])
  rw [← map_mul, hyy, map_one]

end Twist

section Transfer


variable {K : Type} [Field K] [CharP K 2] {σ : K ≃+* K} {G : Type} [Group G] [Finite G]
  {L : Subgroup G} {e : L ≃* adjointGroup .E6 (fixSubfield σ)}

theorem TwoCover.TwistAt.conj_word {N N' : E6Neighbour} {E E' : Subgroup G}
    {h : TwoCover σ e N E} {h' : TwoCover σ e N' E'} {ρ : K ≃+* K}
    {γ : Fin (Tag.rank .E6) → ℤ} (hT : h.TwistAt h' ρ γ) (hγN : γ ∈ orthRoots N.root)
    (hγN' : γ ∈ orthRoots N'.root) (ω : List (Fin (Tag.rank .E6)))
    (hωN : q2WordElt (fixSubfield σ) ω ∈ rootSpan .E6 (fixSubfield σ) (orthRoots N.root))
    (hωN' : q2WordElt (fixSubfield σ) ω ∈ rootSpan .E6 (fixSubfield σ) (orthRoots N'.root)) :
    h.TwistAt h' ρ ((coxeterSystem .E6).wordProd ω • γ) := by
  intro hδ hδ' a g g' hg hg'
  set n : adjointGroup .E6 (fixSubfield σ) :=
    ⟨q2WordElt (fixSubfield σ) ω, q2WordElt_mem_adjointGroup ω⟩ with hn
  set y : N.levi (fixSubfield σ) := ⟨n, mem_subgroupOf.2 hωN⟩ with hy
  set y' : N'.levi (fixSubfield σ) := ⟨n, mem_subgroupOf.2 hωN'⟩ with hy'
  have hc : ∀ (M : E6Neighbour) (z : M.levi (fixSubfield σ)),
      (z : adjointGroup .E6 (fixSubfield σ)) = n →
      ∀ (hγM : γ ∈ orthRoots M.root) (hδM : (coxeterSystem .E6).wordProd ω • γ ∈ orthRoots M.root)
        (b : K), leviInclusion σ M z * q2LeviRootElt M hγM b * (leviInclusion σ M z)⁻¹ =
          q2LeviRootElt M hδM b := by
    intro M z hz hγM hδM b
    refine Subtype.ext (Subtype.ext ?_)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_leviInclusion, coe_q2LeviRootElt, hz, hn]
    rw [baseChangeGL_q2WordElt, q2WordElt_conj_pinnedX ω hγM.1]
  obtain ⟨g₀, hg₀⟩ := h.exists_isLift (q2LeviRootElt_mul_self N hγN a)
  obtain ⟨g₀', hg₀'⟩ := h'.exists_isLift (q2LeviRootElt_mul_self N' hγN' (ρ a))
  have heq := hT hγN hγN' a g₀ g₀' hg₀ hg₀'
  have h1 := hg₀.conj y
  rw [hc N y rfl hγN hδ a] at h1
  have h2 := hg₀'.conj y'
  rw [hc N' y' rfl hγN' hδ' (ρ a)] at h2
  rw [hg.eq h1, hg'.eq h2, heq]

theorem TwoCover.twist_cocycle {N₁ N₂ N₃ : E6Neighbour} {E₁ E₂ E₃ : Subgroup G}
    {h₁ : TwoCover σ e N₁ E₁} {h₂ : TwoCover σ e N₂ E₂} {h₃ : TwoCover σ e N₃ E₃}
    {γ : Fin (Tag.rank .E6) → ℤ} (hγ₁ : γ ∈ orthRoots N₁.root) (hγ₂ : γ ∈ orthRoots N₂.root)
    (hγ₃ : γ ∈ orthRoots N₃.root) {ρ₁₂ ρ₂₃ ρ₁₃ : K ≃+* K} (h12 : h₁.TwistAt h₂ ρ₁₂ γ)
    (h23 : h₂.TwistAt h₃ ρ₂₃ γ) (h13 : h₁.TwistAt h₃ ρ₁₃ γ) : ρ₁₃ = ρ₁₂.trans ρ₂₃ := by
  ext a
  obtain ⟨g₁, hg₁⟩ := h₁.exists_isLift (q2LeviRootElt_mul_self N₁ hγ₁ a)
  obtain ⟨g₂, hg₂⟩ := h₂.exists_isLift (q2LeviRootElt_mul_self N₂ hγ₂ (ρ₁₂ a))
  obtain ⟨g₃, hg₃⟩ := h₃.exists_isLift (q2LeviRootElt_mul_self N₃ hγ₃ (ρ₂₃ (ρ₁₂ a)))
  obtain ⟨g₃', hg₃'⟩ := h₃.exists_isLift (q2LeviRootElt_mul_self N₃ hγ₃ (ρ₁₃ a))
  have e1 := h12 hγ₁ hγ₂ a g₁ g₂ hg₁ hg₂
  have e2 := h23 hγ₂ hγ₃ (ρ₁₂ a) g₂ g₃ hg₂ hg₃
  have e3 := h13 hγ₁ hγ₃ a g₁ g₃' hg₁ hg₃'
  obtain ⟨y, rfl, hpy, -⟩ := hg₃
  obtain ⟨y', rfl, hpy', -⟩ := hg₃'
  have hyy : y = y' := Subtype.ext (e2.symm.trans (e1.symm.trans e3))
  rw [hyy, hpy'] at hpy
  have h4 := congrArg (fun z : N₃.levi K => ((z : adjointGroup .E6 K) : ModGL .E6 K)) hpy
  simp only [coe_q2LeviRootElt] at h4
  rw [RingEquiv.trans_apply]
  exact pinnedX_injective (τ := .E6) (R := K) _ h4

end Transfer

section Renormalize


variable {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {G : Type} [Group G] [Finite G]
  {L : Subgroup G} {e : L ≃* adjointGroup .E6 (fixSubfield σ)}

@[expose] noncomputable def TwoCover.twist {N : E6Neighbour} {E : Subgroup G}
    (h : TwoCover σ e N E) (ρ : K ≃+* K) (hρ : ∀ c : fixSubfield σ, ρ c = c) :
    TwoCover σ e N E where
  p := (neighbourLeviEntrywiseEquiv ρ N).symm.toMonoidHom.comp h.p
  surjective := (neighbourLeviEntrywiseEquiv ρ N).symm.surjective.comp h.surjective
  ker_le_center := by
    have hk : ((neighbourLeviEntrywiseEquiv ρ N).symm.toMonoidHom.comp h.p).ker = h.p.ker := by
      ext y
      simp [MonoidHom.mem_ker]
    rw [hk]
    exact h.ker_le_center
  odd_card_ker := by
    have hk : ((neighbourLeviEntrywiseEquiv ρ N).symm.toMonoidHom.comp h.p).ker = h.p.ker := by
      ext y
      simp [MonoidHom.mem_ker]
    rw [hk]
    exact h.odd_card_ker
  fix x := by
    obtain ⟨y, hy, hpy⟩ := h.fix x
    refine ⟨y, hy, ?_⟩
    have hx : neighbourLeviEntrywiseEquiv ρ N (leviInclusion σ N x) = leviInclusion σ N x := by
      refine Subtype.ext (Subtype.ext ?_)
      have hcomp : (ρ : K →+* K).comp (fixSubfield σ).subtype = (fixSubfield σ).subtype :=
        RingHom.ext fun c => hρ c
      rw [coe_neighbourLeviEntrywiseEquiv, coe_leviInclusion, F4Pilot.baseChangeGL_baseChangeGL,
        hcomp]
    rw [MonoidHom.comp_apply, hpy, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_eq, hx]

theorem TwoCover.isLift_twist_iff {N : E6Neighbour} {E : Subgroup G} (h : TwoCover σ e N E)
    (ρ : K ≃+* K) (hρ : ∀ c : fixSubfield σ, ρ c = c) (u : N.levi K) (g : G) :
    (h.twist ρ hρ).IsLift u g ↔ h.IsLift (neighbourLeviEntrywiseEquiv ρ N u) g := by
  constructor
  · rintro ⟨y, rfl, hpy, hyy⟩
    refine ⟨y, rfl, ?_, hyy⟩
    have : (neighbourLeviEntrywiseEquiv ρ N).symm (h.p y) = u := hpy
    rw [← this, MulEquiv.apply_symm_apply]
  · rintro ⟨y, rfl, hpy, hyy⟩
    refine ⟨y, rfl, ?_, hyy⟩
    change (neighbourLeviEntrywiseEquiv ρ N).symm (h.p y) = u
    rw [hpy, MulEquiv.symm_apply_apply]

theorem neighbourLeviEntrywiseEquiv_q2LeviRootElt (ρ : K ≃+* K) {N : E6Neighbour}
    {γ : Fin (Tag.rank .E6) → ℤ} (hγ : γ ∈ orthRoots N.root) (a : K) :
    neighbourLeviEntrywiseEquiv ρ N (q2LeviRootElt N hγ a) = q2LeviRootElt N hγ (ρ a) :=
  Subtype.ext (Subtype.ext (by rw [coe_neighbourLeviEntrywiseEquiv, coe_q2LeviRootElt,
    coe_q2LeviRootElt, baseChangeGL_pinnedX]; rfl))

theorem TwoCover.TwistAt.twist_twist {N N' : E6Neighbour} {E E' : Subgroup G}
    {h : TwoCover σ e N E} {h' : TwoCover σ e N' E'} {ρ₁ ρ₂ ρ₃ : K ≃+* K}
    {γ : Fin (Tag.rank .E6) → ℤ} (hT : h.TwistAt h' ρ₃ γ) (hρ₁ : ∀ c : fixSubfield σ, ρ₁ c = c)
    (hρ₂ : ∀ c : fixSubfield σ, ρ₂ c = c) (hcoc : ρ₂ = ρ₁.trans ρ₃) :
    (h.twist ρ₁ hρ₁).TwistAt (h'.twist ρ₂ hρ₂) 1 γ := by
  intro hγ hγ' a g g' hg hg'
  rw [TwoCover.isLift_twist_iff, neighbourLeviEntrywiseEquiv_q2LeviRootElt] at hg hg'
  rw [RingAut.one_apply, hcoc, RingEquiv.trans_apply] at hg'
  exact hT hγ hγ' (ρ₁ a) g g' hg hg'

theorem TwoCover.TwistAt.twist {N N' : E6Neighbour} {E E' : Subgroup G}
    {h : TwoCover σ e N E} {h' : TwoCover σ e N' E'} {ρ : K ≃+* K}
    {γ : Fin (Tag.rank .E6) → ℤ} (hT : h.TwistAt h' ρ γ) (hρ : ∀ c : fixSubfield σ, ρ c = c) :
    h.TwistAt (h'.twist ρ hρ) 1 γ := by
  intro hγ hγ' a g g' hg hg'
  rw [TwoCover.isLift_twist_iff, neighbourLeviEntrywiseEquiv_q2LeviRootElt,
    RingAut.one_apply] at hg'
  exact hT hγ hγ' a g g' hg hg'

end Renormalize

section RankOne


variable {K : Type} [Field K] [Finite K] [CharP K 2] {σ : K ≃+* K} {G : Type} [Group G]
  [Finite G] {L : Subgroup G} {e : L ≃* adjointGroup .E6 (fixSubfield σ)}

theorem TwoCover.exists_twistAt_tripleRoot {N N' : E6Neighbour} {E E' : Subgroup G}
    (h : TwoCover σ e N E) (h' : TwoCover σ e N' E') (s : tripleRootSL2 K →* E)
    (hs : ∀ y, ((h.p (s y) : N.levi K) : adjointGroup .E6 K) = y) (s' : tripleRootSL2 K →* E')
    (hs' : ∀ y, ((h'.p (s' y) : N'.levi K) : adjointGroup .E6 K) = y)
    (hrange : s.range.map E.subtype = s'.range.map E'.subtype) :
    ∃ ρ : K ≃+* K, (∀ c : fixSubfield σ, ρ c = c) ∧ h.TwistAt h' ρ tripleRoot ∧
      h.TwistAt h' ρ (-tripleRoot) := by
  obtain ⟨hRinj, hrangeR, -, hgen, -⟩ :=
    CFSG.RankThree.Chevalley.even_Chevalley_pinned_root_SL2_maps .E6 K isRoot_tripleRoot
  set R := rootSL2 .E6 K tripleRoot with hR
  have hRmem : ∀ A, R A ∈ rootSpan .E6 K {tripleRoot, -tripleRoot} := fun A => by
    rw [rootSpan_pair_E6, ← hrangeR]
    exact ⟨A, rfl⟩
  have hRC : ∀ A, R A ∈ adjointGroup .E6 K := fun A => rootSpan_le_adjointGroup_E6 _ (hRmem A)
  set ψ : SL2 K →* tripleRootSL2 K := (R.codRestrict (adjointGroup .E6 K) hRC).codRestrict
    (tripleRootSL2 K) fun A => mem_subgroupOf.2 (hRmem A) with hψdef
  have hψ : ∀ A, (((ψ A : tripleRootSL2 K) : adjointGroup .E6 K) : ModGL .E6 K) = R A :=
    fun _ => rfl
  have hψinj : Function.Injective ψ := fun A B hAB =>
    hRinj (by rw [← hψ A, ← hψ B, hAB])
  have hψsurj : Function.Surjective ψ := by
    rintro ⟨y, hy⟩
    have hy' : (y : ModGL .E6 K) ∈ R.range := by
      rw [hrangeR, ← rootSpan_pair_E6]
      exact mem_subgroupOf.1 hy
    obtain ⟨A, hA⟩ := hy'
    exact ⟨A, Subtype.ext (Subtype.ext hA)⟩
  have hsinj : Function.Injective s := fun y₁ y₂ h12 =>
    Subtype.ext (by rw [← hs y₁, ← hs y₂, h12])
  have hs'inj : Function.Injective s' := fun y₁ y₂ h12 =>
    Subtype.ext (by rw [← hs' y₁, ← hs' y₂, h12])
  set ε := E.subtype.comp (s.comp ψ) with hε
  set ε' := E'.subtype.comp (s'.comp ψ) with hε'
  have hεinj : Function.Injective ε := Subtype.val_injective.comp (hsinj.comp hψinj)
  have hε'inj : Function.Injective ε' := Subtype.val_injective.comp (hs'inj.comp hψinj)
  have hrng : ∀ {F : Subgroup G} (t : tripleRootSL2 K →* F),
      (F.subtype.comp (t.comp ψ)).range = t.range.map F.subtype := by
    intro F t
    ext g
    constructor
    · rintro ⟨A, rfl⟩
      exact ⟨t (ψ A), ⟨ψ A, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
      obtain ⟨A, rfl⟩ := hψsurj y
      exact ⟨A, rfl⟩
  have hεrange : ε.range = ε'.range := by rw [hε, hε', hrng, hrng, hrange]
  set θ : MulAut (SL2 K) := ((MonoidHom.ofInjective hεinj).trans
    (MulEquiv.subgroupCongr hεrange)).trans (MonoidHom.ofInjective hε'inj).symm with hθdef
  have hθ : ∀ A, ε' (θ A) = ε A := by
    intro A
    have h1 := (MonoidHom.ofInjective hε'inj).apply_symm_apply
      (MulEquiv.subgroupCongr hεrange (MonoidHom.ofInjective hεinj A))
    have h2 := congrArg Subtype.val h1
    rw [MonoidHom.ofInjective_apply] at h2
    exact h2
  have hN := tripleRoot_mem_orthRoots N
  have hN' := tripleRoot_mem_orthRoots N'
  have hNn := neg_tripleRoot_mem_orthRoots N
  have hN'n := neg_tripleRoot_mem_orthRoots N'
  have hεU : ∀ a : K, h.IsLift (q2LeviRootElt N hN a) (ε (sl2Upper a)) := fun a =>
    h.isLift_of_section' s hs _ _ (Subtype.ext (hgen a).1) (q2LeviRootElt_mul_self N hN a)
  have hε'U : ∀ a : K, h'.IsLift (q2LeviRootElt N' hN' a) (ε' (sl2Upper a)) := fun a =>
    h'.isLift_of_section' s' hs' _ _ (Subtype.ext (hgen a).1) (q2LeviRootElt_mul_self N' hN' a)
  have hεL : ∀ a : K, h.IsLift (q2LeviRootElt N hNn a) (ε (sl2Lower a)) := fun a =>
    h.isLift_of_section' s hs _ _ (Subtype.ext (hgen a).2) (q2LeviRootElt_mul_self N hNn a)
  have hε'L : ∀ a : K, h'.IsLift (q2LeviRootElt N' hN'n a) (ε' (sl2Lower a)) := fun a =>
    h'.isLift_of_section' s' hs' _ _ (Subtype.ext (hgen a).2) (q2LeviRootElt_mul_self N' hN'n a)
  have hfixU : ∀ c : fixSubfield σ, θ (sl2Upper ((fixSubfield σ).subtype c)) =
      sl2Upper ((fixSubfield σ).subtype c) := by
    intro c
    apply hε'inj
    rw [hθ]
    exact ((hεU c).eq (h.isLift_q2LeviRootElt_fix hN c)).trans
      ((hε'U c).eq (h'.isLift_q2LeviRootElt_fix hN' c)).symm
  have hfixL : ∀ c : fixSubfield σ, θ (sl2Lower ((fixSubfield σ).subtype c)) =
      sl2Lower ((fixSubfield σ).subtype c) := by
    intro c
    apply hε'inj
    rw [hθ]
    exact ((hεL c).eq (h.isLift_q2LeviRootElt_fix hNn c)).trans
      ((hε'L c).eq (h'.isLift_q2LeviRootElt_fix hN'n c)).symm
  obtain ⟨ρ, hρ, hθρ⟩ := E8Pilot.exists_ringEquiv_of_forall_sl2_of_charTwo (fixSubfield σ).subtype θ
    hfixU hfixL
  refine ⟨ρ, hρ, ?_, ?_⟩
  · intro hγ hγ' a g g' hg hg'
    rw [(hεU a).eq hg |>.symm, (hε'U (ρ a)).eq hg' |>.symm, ← (hθρ a).1, hθ]
  · intro hγ hγ' a g g' hg hg'
    rw [(hεL a).eq hg |>.symm, (hε'L (ρ a)).eq hg' |>.symm, ← (hθρ a).2, hθ]

end RankOne

theorem wordProd_23_tripleRoot :
    (coxeterSystem .E6).wordProd [2, 3] • tripleRoot = Pi.single 0 1 := by
  simp only [CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_nil, mul_one, mul_smul,
    simple_smul]
  exact List.ofFn_injective (by decide +kernel)

theorem wordProd_pair_single_E6 {a b : Fin (Tag.rank .E6)}
    (hab : (a, b) = (0, 2) ∨ (a, b) = (2, 3) ∨ (a, b) = (4, 5)) :
    (coxeterSystem .E6).wordProd [a, b] • (Pi.single a 1 : Fin (Tag.rank .E6) → ℤ) =
      Pi.single b 1 := by
  rcases hab with hab | hab | hab <;> obtain ⟨rfl, rfl⟩ := Prod.mk.inj hab <;>
    simp only [CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_nil, mul_one, mul_smul,
      simple_smul] <;> exact List.ofFn_injective (by decide +kernel)

theorem wordProd_02_single_three :
    (coxeterSystem .E6).wordProd [0, 2] • (Pi.single 3 1 : Fin (Tag.rank .E6) → ℤ) =
      tripleRoot := by
  simp only [CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_nil, mul_one, mul_smul,
    simple_smul]
  exact List.ofFn_injective (by decide +kernel)

theorem wordProd_wHT_tripleRoot :
    (coxeterSystem .E6).wordProd ([0, 2] ++ [3] ++ [0, 2].reverse ++ [4]) • tripleRoot =
      Pi.single 4 1 := by
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_nil, mul_one,
    mul_smul, simple_smul]
  exact List.ofFn_injective (by decide +kernel)

theorem wordProd_wST_tripleRoot :
    (coxeterSystem .E6).wordProd ([0, 2] ++ [3] ++ [0, 2].reverse ++ [1]) • tripleRoot =
      Pi.single 1 1 := by
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_nil, mul_one,
    mul_smul, simple_smul]
  exact List.ofFn_injective (by decide +kernel)

section Overlaps


variable {K : Type} [Field K] [CharP K 2] {σ : K ≃+* K} {G : Type} [Group G] [Finite G]
  {L : Subgroup G} {e : L ≃* adjointGroup .E6 (fixSubfield σ)}

theorem single_mem_orthRoots_E6 {N : E6Neighbour} {j : Fin (Tag.rank .E6)} (hj : j ∈ N.nodes) :
    (Pi.single j 1 : Fin (Tag.rank .E6) → ℤ) ∈ orthRoots N.root :=
  ⟨isRoot_single _ j, (N.iform_root_single_eq_zero_iff j).2 hj⟩

theorem neg_mem_orthRoots_E6 {N : E6Neighbour} {γ : Fin (Tag.rank .E6) → ℤ}
    (hγ : γ ∈ orthRoots N.root) : -γ ∈ orthRoots N.root :=
  ⟨IsRoot.neg hγ.1, by rw [iform_neg_right_E6, hγ.2, neg_zero]⟩

theorem q2WordElt_mem_of_nodes {F : Type} [Field F] {N : E6Neighbour}
    {ω : List (Fin (Tag.rank .E6))} (h : ∀ i ∈ ω, i ∈ N.nodes) :
    q2WordElt F ω ∈ rootSpan .E6 F (orthRoots N.root) :=
  q2WordElt_mem_rootSpan fun i hi =>
    ⟨single_mem_orthRoots_E6 (h i hi), neg_mem_orthRoots_E6 (single_mem_orthRoots_E6 (h i hi))⟩

theorem q2WordElt_refl_append_mem {F : Type} [Field F] [CharP F 2] {N : E6Neighbour}
    {j : Fin (Tag.rank .E6)} (hj : j ∈ N.nodes) :
    q2WordElt F ([0, 2] ++ [3] ++ [0, 2].reverse ++ [j]) ∈ rootSpan .E6 F (orthRoots N.root) := by
  rw [q2WordElt_append]
  refine mul_mem (q2WordElt_reflWord_mem_rootSpan [0, 2] 3 ?_ ?_)
    (q2WordElt_mem_of_nodes fun i hi => by
      rw [List.mem_singleton] at hi
      rw [hi]
      exact hj)
  · rw [wordProd_02_single_three]
    exact tripleRoot_mem_orthRoots N
  · rw [wordProd_02_single_three]
    exact neg_tripleRoot_mem_orthRoots N

@[expose] def TwoCover.TwistOn {N N' : E6Neighbour} {E E' : Subgroup G} (h : TwoCover σ e N E)
    (h' : TwoCover σ e N' E') (ρ : K ≃+* K) (S : Finset (Fin (Tag.rank .E6))) : Prop :=
  ∀ j ∈ S, h.TwistAt h' ρ (Pi.single j 1) ∧ h.TwistAt h' ρ (-Pi.single j 1)

theorem TwoCover.TwistAt.transfer {N N' : E6Neighbour} {E E' : Subgroup G}
    {h : TwoCover σ e N E} {h' : TwoCover σ e N' E'} {ρ : K ≃+* K}
    {β β' : Fin (Tag.rank .E6) → ℤ} (hT : h.TwistAt h' ρ β ∧ h.TwistAt h' ρ (-β))
    (hβN : β ∈ orthRoots N.root) (hβN' : β ∈ orthRoots N'.root) (ω : List (Fin (Tag.rank .E6)))
    (hω : (coxeterSystem .E6).wordProd ω • β = β')
    (hωN : q2WordElt (fixSubfield σ) ω ∈ rootSpan .E6 (fixSubfield σ) (orthRoots N.root))
    (hωN' : q2WordElt (fixSubfield σ) ω ∈ rootSpan .E6 (fixSubfield σ) (orthRoots N'.root)) :
    h.TwistAt h' ρ β' ∧ h.TwistAt h' ρ (-β') := by
  refine ⟨?_, ?_⟩
  · have h1 := hT.1.conj_word hβN hβN' ω hωN hωN'
    rwa [hω] at h1
  · have h1 := hT.2.conj_word (neg_mem_orthRoots_E6 hβN) (neg_mem_orthRoots_E6 hβN') ω hωN hωN'
    rwa [smul_neg, hω] at h1

theorem TwoCover.twistOn_high_six {E E' : Subgroup G} {hX : TwoCover σ e .high E}
    {hY : TwoCover σ e .six E'} {ρ : K ≃+* K}
    (h0 : hX.TwistAt hY ρ tripleRoot ∧ hX.TwistAt hY ρ (-tripleRoot)) :
    hX.TwistOn hY ρ {0, 2, 3} := by
  have hmem : ∀ (ω : List (Fin (Tag.rank .E6))), (∀ i ∈ ω, i = 0 ∨ i = 2 ∨ i = 3) →
      ∀ N : E6Neighbour, N = .high ∨ N = .six →
        q2WordElt (fixSubfield σ) ω ∈ rootSpan .E6 (fixSubfield σ) (orthRoots N.root) :=
    fun ω hω N hN => q2WordElt_mem_of_nodes fun i hi => by
      rcases hN with rfl | rfl <;> rcases hω i hi with rfl | rfl | rfl <;> decide
  have h1 := TwoCover.TwistAt.transfer h0 (tripleRoot_mem_orthRoots _)
    (tripleRoot_mem_orthRoots _) [2, 3] wordProd_23_tripleRoot
    (hmem _ (by simp) _ (Or.inl rfl)) (hmem _ (by simp) _ (Or.inr rfl))
  have h2 := TwoCover.TwistAt.transfer h1 (single_mem_orthRoots_E6 (by decide))
    (single_mem_orthRoots_E6 (by decide)) [0, 2] (wordProd_pair_single_E6 (Or.inl rfl))
    (hmem _ (by simp) _ (Or.inl rfl)) (hmem _ (by simp) _ (Or.inr rfl))
  have h3 := TwoCover.TwistAt.transfer h2 (single_mem_orthRoots_E6 (by decide))
    (single_mem_orthRoots_E6 (by decide)) [2, 3] (wordProd_pair_single_E6 (Or.inr (Or.inl rfl)))
    (hmem _ (by simp) _ (Or.inl rfl)) (hmem _ (by simp) _ (Or.inr rfl))
  intro j hj
  simp only [Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with rfl | rfl | rfl
  exacts [h1, h2, h3]

theorem TwoCover.twistOn_high_three {E E' : Subgroup G} {hX : TwoCover σ e .high E}
    {hZ : TwoCover σ e .three E'} {ρ : K ≃+* K}
    (h0 : hX.TwistAt hZ ρ tripleRoot ∧ hX.TwistAt hZ ρ (-tripleRoot)) :
    hX.TwistOn hZ ρ {4, 5} := by
  have hw : ∀ N : E6Neighbour, N = .high ∨ N = .three →
      q2WordElt (fixSubfield σ) ([0, 2] ++ [3] ++ [0, 2].reverse ++ [4]) ∈
        rootSpan .E6 (fixSubfield σ) (orthRoots N.root) := fun N hN =>
    q2WordElt_refl_append_mem (by rcases hN with rfl | rfl <;> decide)
  have hmem : ∀ N : E6Neighbour, N = .high ∨ N = .three →
      q2WordElt (fixSubfield σ) [4, 5] ∈ rootSpan .E6 (fixSubfield σ) (orthRoots N.root) :=
    fun N hN => q2WordElt_mem_of_nodes fun i hi => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hN with rfl | rfl <;> rcases hi with rfl | rfl <;> decide
  have h4 := TwoCover.TwistAt.transfer h0 (tripleRoot_mem_orthRoots _)
    (tripleRoot_mem_orthRoots _) _ wordProd_wHT_tripleRoot (hw _ (Or.inl rfl)) (hw _ (Or.inr rfl))
  have h5 := TwoCover.TwistAt.transfer h4 (single_mem_orthRoots_E6 (by decide))
    (single_mem_orthRoots_E6 (by decide)) [4, 5] (wordProd_pair_single_E6 (Or.inr (Or.inr rfl)))
    (hmem _ (Or.inl rfl)) (hmem _ (Or.inr rfl))
  intro j hj
  simp only [Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with rfl | rfl
  exacts [h4, h5]

theorem TwoCover.twistOn_six_three {E E' : Subgroup G} {hY : TwoCover σ e .six E}
    {hZ : TwoCover σ e .three E'} {ρ : K ≃+* K}
    (h0 : hY.TwistAt hZ ρ tripleRoot ∧ hY.TwistAt hZ ρ (-tripleRoot)) :
    hY.TwistOn hZ ρ {1} := by
  have hw : ∀ N : E6Neighbour, N = .six ∨ N = .three →
      q2WordElt (fixSubfield σ) ([0, 2] ++ [3] ++ [0, 2].reverse ++ [1]) ∈
        rootSpan .E6 (fixSubfield σ) (orthRoots N.root) := fun N hN =>
    q2WordElt_refl_append_mem (by rcases hN with rfl | rfl <;> decide)
  have h1 := TwoCover.TwistAt.transfer h0 (tripleRoot_mem_orthRoots _)
    (tripleRoot_mem_orthRoots _) _ wordProd_wST_tripleRoot (hw _ (Or.inl rfl)) (hw _ (Or.inr rfl))
  intro j hj
  rw [Finset.mem_singleton] at hj
  rw [hj]
  exact h1

variable [Finite K]

theorem exists_aligned_twoCover {E₁ E₂ E₃ : Subgroup G} (hX : TwoCover σ e .high E₁)
    (hY : TwoCover σ e .six E₂) (hZ : TwoCover σ e .three E₃) {ρhs ρht ρst : K ≃+* K}
    (hρhs : ∀ c : fixSubfield σ, ρhs c = c) (hρht : ∀ c : fixSubfield σ, ρht c = c)
    (h1 : hX.TwistAt hY ρhs tripleRoot ∧ hX.TwistAt hY ρhs (-tripleRoot))
    (h2 : hX.TwistAt hZ ρht tripleRoot ∧ hX.TwistAt hZ ρht (-tripleRoot))
    (h3 : hY.TwistAt hZ ρst tripleRoot ∧ hY.TwistAt hZ ρst (-tripleRoot)) :
    hX.TwistOn (hY.twist ρhs hρhs) 1 {0, 2, 3} ∧ hX.TwistOn (hZ.twist ρht hρht) 1 {4, 5} ∧
      (hY.twist ρhs hρhs).TwistOn (hZ.twist ρht hρht) 1 {1} := by
  have hTs := TwoCover.twistOn_high_six h1
  have hTt := TwoCover.twistOn_high_three h2
  have hTst := TwoCover.twistOn_six_three h3
  have hcoc := TwoCover.twist_cocycle (tripleRoot_mem_orthRoots .high)
    (tripleRoot_mem_orthRoots .six) (tripleRoot_mem_orthRoots .three) h1.1 h3.1 h2.1
  refine ⟨fun j hj => ⟨(hTs j hj).1.twist hρhs, (hTs j hj).2.twist hρhs⟩,
    fun j hj => ⟨(hTt j hj).1.twist hρht, (hTt j hj).2.twist hρht⟩, fun j hj => ?_⟩
  exact ⟨(hTst j hj).1.twist_twist hρhs hρht hcoc, (hTst j hj).2.twist_twist hρhs hρht hcoc⟩

end Overlaps

end CFSG.SeitzReduction.E6Pilot
