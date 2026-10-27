module

public import CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3.LayerRoots
public import CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3.D4Comm

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Lang.Triality CFSG.HardMathSupport.Lang.E27Lie
open CFSG.HardMathSupport.Solomon.Coordinator
open scoped commutatorElement

namespace CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3


section CoordC

variable {K : Type} [Field K] [Finite K]

abbrev rootsGe2 : Set (Fin TwistTag.D4.tag.rank → ℤ) :=
  {γ | IsRoot TwistTag.D4.tag γ ∧ 0 < height γ ∧ 2 ≤ height γ}

abbrev rootsGe2NeC : Set (Fin TwistTag.D4.tag.rank → ℤ) :=
  {γ | IsRoot TwistTag.D4.tag γ ∧ 0 < height γ ∧ 2 ≤ height γ ∧ γ ≠ rootC}

private theorem rootsGe2NeC_sub : rootsGe2NeC ⊆ rootsGe2 := fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩

private theorem rootC_mem_rootsGe2 : rootC ∈ rootsGe2 := ⟨isRoot_rootC, by decide, by decide⟩

private theorem height_two_roots_add_ne_rootC :
    ∀ α ∈ rootFinset TwistTag.D4.tag, ∀ β ∈ rootFinset TwistTag.D4.tag,
      height α = 2 → height β = 2 → α + β ≠ rootC := by
  decide +kernel

private theorem rootB_add_imp_rootC :
    ∀ β ∈ rootFinset TwistTag.D4.tag, 2 ≤ height β →
      rootB + β ∈ rootFinset TwistTag.D4.tag → β = rootC := by
  decide +kernel

private theorem rootB_add_rootC : rootB + rootC = rootD := by decide

private theorem height_neg_vec {τ : Tag} (v : Fin τ.rank → ℤ) : height (-v) = -height v := by
  unfold height
  simp [Finset.sum_neg_distrib]

private theorem rootsGe2NeC_comb {α β : Fin TwistTag.D4.tag.rank → ℤ} (hα : α ∈ rootsGe2)
    (hβ : β ∈ rootsGe2) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hr : IsRoot TwistTag.D4.tag (a • α + b • β)) : a • α + b • β ∈ rootsGe2NeC := by
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  have hα2 : (2 : ℤ) ≤ height α := hα.2.2
  have hβ2 : (2 : ℤ) ≤ height β := hβ.2.2
  have hht : height (a • α + b • β) = a * height α + b * height β :=
    height_nsmul_add_nsmul a b α β
  have hprod := mul_nonneg (sub_nonneg.2 ha') (sub_nonneg.2 hα2)
  have hprod' := mul_nonneg (sub_nonneg.2 hb') (sub_nonneg.2 hβ2)
  have h4 : (4 : ℤ) ≤ height (a • α + b • β) := by
    rw [hht]
    nlinarith
  refine ⟨hr, by linarith, by linarith, fun heq => ?_⟩
  have h4' : height (a • α + b • β) = 4 := by rw [heq, height_rootC]
  rw [hht] at h4'
  have ha1 : (a : ℤ) = 1 := le_antisymm (by nlinarith) ha'
  have hb1 : (b : ℤ) = 1 := le_antisymm (by nlinarith) hb'
  have ha1' : a = 1 := by exact_mod_cast ha1
  have hb1' : b = 1 := by exact_mod_cast hb1
  subst ha1'
  subst hb1'
  simp only [Nat.cast_one, one_mul] at h4'
  rw [one_smul, one_smul] at heq
  exact height_two_roots_add_ne_rootC α (mem_rootFinset.2 hα.1) β (mem_rootFinset.2 hβ.1)
    (by linarith) (by linarith) heq

private theorem rootsGe2NeC_closed :
    ∀ α ∈ rootsGe2NeC, ∀ β ∈ rootsGe2NeC, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      IsRoot TwistTag.D4.tag (a • α + b • β) → a • α + b • β ∈ rootsGe2NeC :=
  fun _ hα _ hβ _ _ ha hb hr => rootsGe2NeC_comb (rootsGe2NeC_sub hα) (rootsGe2NeC_sub hβ) ha hb hr

private theorem rootsGe2_closed :
    ∀ α ∈ rootsGe2, ∀ β ∈ rootsGe2, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      IsRoot TwistTag.D4.tag (a • α + b • β) → a • α + b • β ∈ rootsGe2 := by
  intro α hα β hβ a b ha hb hr
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  have hα2 : (2 : ℤ) ≤ height α := hα.2.2
  have hβ2 : (2 : ℤ) ≤ height β := hβ.2.2
  have hprod := mul_nonneg (sub_nonneg.2 ha') (sub_nonneg.2 hα2)
  have hprod' := mul_nonneg (sub_nonneg.2 hb') (sub_nonneg.2 hβ2)
  have hht : height (a • α + b • β) = a * height α + b * height β :=
    height_nsmul_add_nsmul a b α β
  refine ⟨hr, ?_, ?_⟩
  · rw [hht]; nlinarith
  · rw [hht]; nlinarith

private theorem rootsGe2_finite : rootsGe2.Finite :=
  finite_of_forall_isRoot_pos fun _ h => ⟨h.1, h.2.1⟩

private theorem rootsGe2_ncard : rootsGe2.ncard = rootsGe2NeC.ncard + 1 := by
  have hset : rootsGe2 = insert rootC rootsGe2NeC := by
    ext γ
    constructor
    · intro h
      by_cases hγ : γ = rootC
      · exact Or.inl hγ
      · exact Or.inr ⟨h.1, h.2.1, h.2.2, hγ⟩
    · rintro (rfl | h)
      · exact rootC_mem_rootsGe2
      · exact rootsGe2NeC_sub h
  have hnot : rootC ∉ rootsGe2NeC := fun h => h.2.2.2 rfl
  rw [hset, Set.ncard_insert_of_notMem hnot (rootsGe2_finite.subset rootsGe2NeC_sub)]

private theorem card_heightSeries_two :
    Nat.card (heightSeries TwistTag.D4.tag K 2) =
      Nat.card K * Nat.card (rootSpan TwistTag.D4.tag K rootsGe2NeC) := by
  calc Nat.card (heightSeries TwistTag.D4.tag K 2)
      = Nat.card K ^ rootsGe2.ncard :=
        card_rootSpan (K := K) (fun _ h => ⟨h.1, h.2.1⟩) rootsGe2_closed
    _ = Nat.card K ^ (rootsGe2NeC.ncard + 1) := by rw [rootsGe2_ncard]
    _ = Nat.card K * Nat.card K ^ rootsGe2NeC.ncard := pow_succ' _ _
    _ = Nat.card K * Nat.card (rootSpan TwistTag.D4.tag K rootsGe2NeC) := by
        rw [card_rootSpan (K := K) (fun _ h => ⟨h.1, h.2.1⟩) rootsGe2NeC_closed]

private theorem pinnedX_mem_heightSeries {γ : Fin TwistTag.D4.tag.rank → ℤ}
    (hγ : IsRoot TwistTag.D4.tag γ) (h2 : 2 ≤ height γ) (c : K) :
    pinnedX TwistTag.D4.tag K γ c ∈ heightSeries TwistTag.D4.tag K 2 :=
  pinnedX_mem_rootSpan (S := rootsGe2) ⟨hγ, by linarith, h2⟩ c

noncomputable abbrev coordKer : Subgroup (heightSeries TwistTag.D4.tag K 2) :=
  (rootSpan TwistTag.D4.tag K rootsGe2NeC).subgroupOf (heightSeries TwistTag.D4.tag K 2)

instance coordKer_normal : (coordKer (K := K)).Normal :=
  (positive_root_ideal_normality TwistTag.D4.tag K (J := rootsGe2NeC) (S := rootsGe2)
    rootsGe2NeC_sub (fun α hα => ⟨hα.1, hα.2.1⟩)
    (fun _ hα _ hβ _ _ ha hb hr => rootsGe2NeC_comb hα (rootsGe2NeC_sub hβ) ha hb hr)).2

private noncomputable def coordCHom :
    Multiplicative K →* heightSeries TwistTag.D4.tag K 2 ⧸ coordKer (K := K) where
  toFun c := QuotientGroup.mk
    ⟨pinnedX TwistTag.D4.tag K rootC c.toAdd, pinnedX_mem_heightSeries isRoot_rootC (by decide) _⟩
  map_one' := by
    rw [← QuotientGroup.mk_one]
    exact congrArg QuotientGroup.mk (Subtype.ext (pinnedX_zero TwistTag.D4.tag K rootC))
  map_mul' c d := by
    rw [← QuotientGroup.mk_mul]
    exact congrArg QuotientGroup.mk
      (Subtype.ext (pinnedX_add TwistTag.D4.tag K rootC c.toAdd d.toAdd))

private theorem coordCHom_surjective : Function.Surjective (coordCHom (K := K)) := by
  have hM : heightSeries TwistTag.D4.tag K 2 = Subgroup.closure
      {g : ModGL TwistTag.D4.tag K | ∃ β ∈ rootsGe2, ∃ c : K, pinnedX TwistTag.D4.tag K β c = g} :=
    rootSpan_eq_closure K rootsGe2
  have key : ∀ g (hg : g ∈ Subgroup.closure
      {g : ModGL TwistTag.D4.tag K | ∃ β ∈ rootsGe2, ∃ c : K, pinnedX TwistTag.D4.tag K β c = g}),
      ∃ c : Multiplicative K, coordCHom c =
        QuotientGroup.mk (⟨g, hM ▸ hg⟩ : heightSeries TwistTag.D4.tag K 2) := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨β, hβ, c, rfl⟩ := hg
      by_cases hβC : β = rootC
      · subst hβC
        exact ⟨Multiplicative.ofAdd c, rfl⟩
      · refine ⟨1, ?_⟩
        rw [map_one, eq_comm, QuotientGroup.eq_one_iff]
        exact Subgroup.mem_subgroupOf.2
          (pinnedX_mem_rootSpan (S := rootsGe2NeC) ⟨hβ.1, hβ.2.1, hβ.2.2, hβC⟩ c)
    | one => exact ⟨1, by rw [map_one]; rfl⟩
    | mul x y hx hy ihx ihy =>
      obtain ⟨u, hu⟩ := ihx
      obtain ⟨v, hv⟩ := ihy
      refine ⟨u * v, ?_⟩
      rw [map_mul, hu, hv, ← QuotientGroup.mk_mul]
      rfl
    | inv x hx ihx =>
      obtain ⟨u, hu⟩ := ihx
      refine ⟨u⁻¹, ?_⟩
      rw [map_inv, hu, ← QuotientGroup.mk_inv]
      rfl
  intro y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  exact key x (hM ▸ x.2)

private theorem card_coordKer_quot :
    Nat.card (heightSeries TwistTag.D4.tag K 2 ⧸ coordKer (K := K)) = Nat.card K := by
  have hle : rootSpan TwistTag.D4.tag K rootsGe2NeC ≤ heightSeries TwistTag.D4.tag K 2 :=
    rootSpan_mono rootsGe2NeC_sub
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (coordKer (K := K))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, card_heightSeries_two] at h1
  have hpos : 0 < Nat.card (rootSpan TwistTag.D4.tag K rootsGe2NeC) := by
    rw [card_rootSpan (K := K) (fun _ h => ⟨h.1, h.2.1⟩) rootsGe2NeC_closed]
    exact pow_pos Nat.card_pos _
  exact (Nat.eq_of_mul_eq_mul_right hpos h1).symm

private theorem coordCHom_bijective : Function.Bijective (coordCHom (K := K)) :=
  coordCHom_surjective.bijective_of_nat_card_le
    ((Nat.card_congr Multiplicative.toAdd).trans card_coordKer_quot.symm).le

open scoped Classical in
private noncomputable def coordCFun (x : ModGL TwistTag.D4.tag K) : K :=
  if hx : x ∈ heightSeries TwistTag.D4.tag K 2 then
    ((MulEquiv.ofBijective (coordCHom (K := K)) coordCHom_bijective).symm
      (QuotientGroup.mk ⟨x, hx⟩)).toAdd
  else 0

private theorem coordCFun_eq {x : ModGL TwistTag.D4.tag K}
    (hx : x ∈ heightSeries TwistTag.D4.tag K 2) {c : K}
    (h : QuotientGroup.mk ⟨x, hx⟩ = coordCHom (Multiplicative.ofAdd c)) :
    coordCFun x = c := by
  have h' : (MulEquiv.ofBijective (coordCHom (K := K)) coordCHom_bijective).symm
      (QuotientGroup.mk ⟨x, hx⟩) = Multiplicative.ofAdd c := by
    rw [MulEquiv.symm_apply_eq]
    exact h
  rw [coordCFun, dif_pos hx, h', toAdd_ofAdd]

private theorem coordCHom_coordCFun {x : ModGL TwistTag.D4.tag K}
    (hx : x ∈ heightSeries TwistTag.D4.tag K 2) :
    coordCHom (Multiplicative.ofAdd (coordCFun x)) = QuotientGroup.mk ⟨x, hx⟩ := by
  rw [coordCFun, dif_pos hx, ofAdd_toAdd]
  exact (MulEquiv.ofBijective _ coordCHom_bijective).apply_symm_apply _

private theorem coordCFun_mul {x y : ModGL TwistTag.D4.tag K}
    (hx : x ∈ heightSeries TwistTag.D4.tag K 2) (hy : y ∈ heightSeries TwistTag.D4.tag K 2) :
    coordCFun (x * y) = coordCFun x + coordCFun y := by
  refine coordCFun_eq (mul_mem hx hy) ?_
  rw [ofAdd_add, map_mul, coordCHom_coordCFun hx, coordCHom_coordCFun hy,
    ← QuotientGroup.mk_mul]
  rfl

private theorem coordCFun_pinnedX_rootC (c : K) :
    coordCFun (pinnedX TwistTag.D4.tag K rootC c) = c :=
  coordCFun_eq (pinnedX_mem_heightSeries isRoot_rootC (by decide) c) rfl

private theorem coordCFun_pinnedX_of_ne {γ : Fin TwistTag.D4.tag.rank → ℤ}
    (hγ : IsRoot TwistTag.D4.tag γ) (h2 : 2 ≤ height γ) (hC : γ ≠ rootC) (c : K) :
    coordCFun (pinnedX TwistTag.D4.tag K γ c) = 0 := by
  refine coordCFun_eq (pinnedX_mem_heightSeries hγ h2 c) ?_
  rw [ofAdd_zero, map_one, QuotientGroup.eq_one_iff]
  exact Subgroup.mem_subgroupOf.2
    (pinnedX_mem_rootSpan (S := rootsGe2NeC) ⟨hγ, by linarith, h2, hC⟩ c)

theorem exists_coordC : ∃ π : ModGL TwistTag.D4.tag K → K,
    (∀ x ∈ heightSeries TwistTag.D4.tag K 2, ∀ y ∈ heightSeries TwistTag.D4.tag K 2,
      π (x * y) = π x + π y) ∧
    (∀ (γ : Fin TwistTag.D4.tag.rank → ℤ), IsRoot TwistTag.D4.tag γ → 2 ≤ height γ → ∀ c : K,
      π (pinnedX TwistTag.D4.tag K γ c) = if γ = rootC then c else 0) := by
  refine ⟨coordCFun, fun x hx y hy => coordCFun_mul hx hy, fun γ hγ h2 c => ?_⟩
  by_cases hC : γ = rootC
  · subst hC
    rw [if_pos rfl]
    exact coordCFun_pinnedX_rootC c
  · rw [if_neg hC]
    exact coordCFun_pinnedX_of_ne hγ h2 hC c

noncomputable def coordC : ModGL TwistTag.D4.tag K → K := (exists_coordC (K := K)).choose

theorem coordC_mul {x y : ModGL TwistTag.D4.tag K} (hx : x ∈ heightSeries TwistTag.D4.tag K 2)
    (hy : y ∈ heightSeries TwistTag.D4.tag K 2) : coordC (x * y) = coordC x + coordC y :=
  (exists_coordC (K := K)).choose_spec.1 x hx y hy

theorem coordC_pinnedX {γ : Fin TwistTag.D4.tag.rank → ℤ} (hγ : IsRoot TwistTag.D4.tag γ)
    (h2 : 2 ≤ height γ) (c : K) :
    coordC (pinnedX TwistTag.D4.tag K γ c) = if γ = rootC then c else 0 :=
  (exists_coordC (K := K)).choose_spec.2 γ hγ h2 c

private theorem coordC_one : coordC (1 : ModGL TwistTag.D4.tag K) = 0 := by
  have h := coordC_mul (K := K) (x := 1) (y := 1) (one_mem _) (one_mem _)
  rw [mul_one] at h
  linear_combination -h

private theorem coordC_inv {x : ModGL TwistTag.D4.tag K}
    (hx : x ∈ heightSeries TwistTag.D4.tag K 2) : coordC x⁻¹ = -coordC x := by
  have h := coordC_mul (K := K) hx (inv_mem hx)
  rw [mul_inv_cancel, coordC_one] at h
  linear_combination -h

private theorem coordC_eq_zero_of_mem {y : ModGL TwistTag.D4.tag K}
    (hy : y ∈ rootSpan TwistTag.D4.tag K rootsGe2NeC) : coordC y = 0 := by
  have key : ∀ z : ModGL TwistTag.D4.tag K, z ∈ rootSpan TwistTag.D4.tag K rootsGe2NeC →
      z ∈ heightSeries TwistTag.D4.tag K 2 ∧ coordC z = 0 := by
    intro z hz
    rw [rootSpan_eq_closure K rootsGe2NeC] at hz
    induction hz using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨β, hβ, c, rfl⟩ := hg
      exact ⟨pinnedX_mem_heightSeries hβ.1 hβ.2.2.1 c,
        by rw [coordC_pinnedX hβ.1 hβ.2.2.1 c, if_neg hβ.2.2.2]⟩
    | one => exact ⟨one_mem _, coordC_one⟩
    | mul x y hx hy ihx ihy =>
      exact ⟨mul_mem ihx.1 ihy.1, by rw [coordC_mul ihx.1 ihy.1, ihx.2, ihy.2, add_zero]⟩
    | inv x hx ihx =>
      exact ⟨inv_mem ihx.1, by rw [coordC_inv ihx.1, ihx.2, neg_zero]⟩
  exact (key y hy).2

private theorem coordC_semilinear_of_gen (F : ModGL TwistTag.D4.tag K →* ModGL TwistTag.D4.tag K)
    (σ : K →+* K)
    (hgen : ∀ β : Fin TwistTag.D4.tag.rank → ℤ, IsRoot TwistTag.D4.tag β → 2 ≤ height β →
      ∀ c : K, F (pinnedX TwistTag.D4.tag K β c) ∈ heightSeries TwistTag.D4.tag K 2 ∧
        coordC (F (pinnedX TwistTag.D4.tag K β c)) = σ (coordC (pinnedX TwistTag.D4.tag K β c)))
    {x : ModGL TwistTag.D4.tag K} (hx : x ∈ heightSeries TwistTag.D4.tag K 2) :
    F x ∈ heightSeries TwistTag.D4.tag K 2 ∧ coordC (F x) = σ (coordC x) := by
  have hcl : heightSeries TwistTag.D4.tag K 2 = Subgroup.closure
      {g : ModGL TwistTag.D4.tag K | ∃ β ∈ rootsGe2, ∃ c : K, pinnedX TwistTag.D4.tag K β c = g} :=
    rootSpan_eq_closure K rootsGe2
  have key : ∀ y : ModGL TwistTag.D4.tag K, y ∈ Subgroup.closure
      {g : ModGL TwistTag.D4.tag K | ∃ β ∈ rootsGe2, ∃ c : K, pinnedX TwistTag.D4.tag K β c = g} →
      y ∈ heightSeries TwistTag.D4.tag K 2 ∧ F y ∈ heightSeries TwistTag.D4.tag K 2 ∧
        coordC (F y) = σ (coordC y) := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨β, hβ, c, rfl⟩ := hg
      exact ⟨pinnedX_mem_heightSeries hβ.1 hβ.2.2 c, (hgen β hβ.1 hβ.2.2 c).1,
        (hgen β hβ.1 hβ.2.2 c).2⟩
    | one =>
      refine ⟨one_mem _, ?_, ?_⟩
      · rw [map_one]; exact one_mem _
      · rw [map_one, coordC_one, map_zero]
    | mul x y hx hy ihx ihy =>
      refine ⟨mul_mem ihx.1 ihy.1, ?_, ?_⟩
      · rw [map_mul]; exact mul_mem ihx.2.1 ihy.2.1
      · rw [map_mul, coordC_mul ihx.2.1 ihy.2.1, ihx.2.2, ihy.2.2, coordC_mul ihx.1 ihy.1, map_add]
    | inv x hx ihx =>
      refine ⟨inv_mem ihx.1, ?_, ?_⟩
      · rw [map_inv]; exact inv_mem ihx.2.1
      · rw [map_inv, coordC_inv ihx.2.1, coordC_inv ihx.1, ihx.2.2, map_neg]
  have := key x (hcl ▸ hx)
  exact ⟨this.2.1, this.2.2⟩

theorem coordC_entrywise (σ : K →+* K) {x : ModGL TwistTag.D4.tag K}
    (hx : x ∈ heightSeries TwistTag.D4.tag K 2) :
    coordC (Units.map (entrywiseHom σ) x) = σ (coordC x) := by
  refine (coordC_semilinear_of_gen (Units.map (entrywiseHom σ)) σ ?_ hx).2
  intro β hβ h2 c
  have e : Units.map (entrywiseHom σ) (pinnedX TwistTag.D4.tag K β c) =
      pinnedX TwistTag.D4.tag K β (σ c) := Units.ext (entrywise_pinnedX σ β c)
  rw [e]
  refine ⟨pinnedX_mem_heightSeries hβ h2 (σ c), ?_⟩
  rw [coordC_pinnedX hβ h2 (σ c), coordC_pinnedX hβ h2 c]
  split_ifs <;> simp

private theorem permLattice_injective_vec {τ : Tag} (π : Equiv.Perm (Fin τ.rank)) :
    Function.Injective (permLattice π) := by
  intro v w h
  funext j
  have := congrFun h (π j)
  simpa [permLattice] using this

private theorem height_permLattice_eq {τ : Tag} (π : Equiv.Perm (Fin τ.rank))
    (v : Fin τ.rank → ℤ) : height (permLattice π v) = height v := by
  unfold height permLattice
  exact Equiv.sum_comp π.symm v

private theorem permLattice_rootC : permLattice TwistTag.D4.perm rootC = rootC := by decide

private theorem perm_ne_rootC_of_ne {β : Fin TwistTag.D4.tag.rank → ℤ} (h : β ≠ rootC) :
    permLattice TwistTag.D4.perm β ≠ rootC := by
  intro he
  apply h
  apply permLattice_injective_vec TwistTag.D4.perm
  rw [he, permLattice_rootC]

private theorem coordC_twist_semilinear {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    [CharP K 3] (hK : Nat.card K = (3 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (3 ^ f))
    {x : ModGL TwistTag.D4.tag K} (hx : x ∈ heightSeries TwistTag.D4.tag K 2) :
    twistHom TwistTag.D4 K σ.toRingHom x ∈ heightSeries TwistTag.D4.tag K 2 ∧
      coordC (twistHom TwistTag.D4 K σ.toRingHom x) = σ (coordC x) := by
  refine coordC_semilinear_of_gen (twistHom TwistTag.D4 K σ.toRingHom) σ.toRingHom ?_ hx
  intro β hβ h2 c
  by_cases hC : β = rootC
  · subst hC
    have hfix := twistHom_pinnedX_of_fixedRoot hf hK σ hσ isRoot_rootC permLattice_rootC c
    rw [hfix]
    refine ⟨pinnedX_mem_heightSeries isRoot_rootC (by decide) (σ c), ?_⟩
    rw [coordC_pinnedX isRoot_rootC (by decide) (σ c), coordC_pinnedX isRoot_rootC (by decide) c]
    simp
  · obtain ⟨ε, -, hε⟩ := diagramMap_conj_pinnedX (K := K) TwistTag.D4 hβ
    have h1 : twistHom TwistTag.D4 K σ.toRingHom (pinnedX TwistTag.D4.tag K β c) =
        diagramMap TwistTag.D4 K * Units.map (entrywiseHom σ.toRingHom)
          (pinnedX TwistTag.D4.tag K β c) * (diagramMap TwistTag.D4 K)⁻¹ := rfl
    have e : Units.map (entrywiseHom σ.toRingHom) (pinnedX TwistTag.D4.tag K β c) =
        pinnedX TwistTag.D4.tag K β (σ c) := Units.ext (entrywise_pinnedX σ.toRingHom β c)
    have hF : twistHom TwistTag.D4 K σ.toRingHom (pinnedX TwistTag.D4.tag K β c) =
        pinnedX TwistTag.D4.tag K (permLattice TwistTag.D4.perm β) (ε * σ c) := by
      rw [h1, e, hε]
    have hρβ : IsRoot TwistTag.D4.tag (permLattice TwistTag.D4.perm β) :=
      IsRoot.permLattice (TwistTag.cartan_perm TwistTag.D4) hβ
    have h2' : 2 ≤ height (permLattice TwistTag.D4.perm β) := by
      rw [height_permLattice_eq]; exact h2
    rw [hF]
    refine ⟨pinnedX_mem_heightSeries hρβ h2' _, ?_⟩
    rw [coordC_pinnedX hρβ h2' _, if_neg (perm_ne_rootC_of_ne hC), coordC_pinnedX hβ h2 c,
      if_neg hC, map_zero]

theorem coordC_fieldActor {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] [CharP K 3]
    (hK : Nat.card K = (3 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (3 ^ f))
    (w : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hw : (w : ModGL TwistTag.D4.tag K) ∈ heightSeries TwistTag.D4.tag K 2) :
    coordC (((fieldActor (t := TwistTag.D4) σ σ w : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
      ModGL TwistTag.D4.tag K)) = coordC (w : ModGL TwistTag.D4.tag K) := by
  have hfix : twistHom TwistTag.D4 K σ.toRingHom (w : ModGL TwistTag.D4.tag K) = w :=
    ((mem_twistedFixedGroup_iff_twistHom TwistTag.D4 K σ.toRingHom).1
      (graphFixedRootGroup_le TwistTag.D4 K σ.toRingHom w.2)).2
  have hsemi := coordC_twist_semilinear hf hK σ hσ hw
  rw [hfix] at hsemi
  rw [coe_fieldActor σ σ w, coordC_entrywise σ.toRingHom hw]
  exact hsemi.2.symm

theorem coordC_conj_rootB (s : K) {x : ModGL TwistTag.D4.tag K}
    (hx : x ∈ heightSeries TwistTag.D4.tag K 2) :
    coordC (pinnedX TwistTag.D4.tag K rootB s * x * (pinnedX TwistTag.D4.tag K rootB s)⁻¹) =
      coordC x := by
  have hle : rootSpan TwistTag.D4.tag K rootsGe2NeC ≤ heightSeries TwistTag.D4.tag K 2 :=
    rootSpan_mono rootsGe2NeC_sub
  have hgen : ∀ β : Fin TwistTag.D4.tag.rank → ℤ, IsRoot TwistTag.D4.tag β → 2 ≤ height β →
      ∀ c : K,
      (MulAut.conj (pinnedX TwistTag.D4.tag K rootB s)).toMonoidHom
          (pinnedX TwistTag.D4.tag K β c) ∈ heightSeries TwistTag.D4.tag K 2 ∧
        coordC ((MulAut.conj (pinnedX TwistTag.D4.tag K rootB s)).toMonoidHom
          (pinnedX TwistTag.D4.tag K β c)) =
          (RingHom.id K) (coordC (pinnedX TwistTag.D4.tag K β c)) := by
    intro β hβ h2 c
    have hne : rootB ≠ β := by
      rintro rfl
      rw [height_rootB] at h2
      norm_num at h2
    have hne' : rootB ≠ -β := by
      intro h
      have h1 := congrArg height h
      rw [height_rootB, height_neg_vec] at h1
      linarith
    have hcomm : ⁅pinnedX TwistTag.D4.tag K rootB s, pinnedX TwistTag.D4.tag K β c⁆ ∈
        rootSpan TwistTag.D4.tag K rootsGe2NeC := by
      by_cases hn : IsRoot TwistTag.D4.tag (rootB + β)
      · have hβC : β = rootC :=
          rootB_add_imp_rootC β (mem_rootFinset.2 hβ) h2 (mem_rootFinset.2 hn)
        subst hβC
        obtain ⟨ε, -, hε⟩ := exists_commutator_pinnedX_of_sum (K := K) isRoot_rootB isRoot_rootC
          hne hne' rootB_add_rootC isRoot_rootD
        rw [hε s c]
        exact pinnedX_mem_rootSpan (S := rootsGe2NeC)
          ⟨isRoot_rootD, by decide, by decide, by decide⟩ _
      · have hcomm' := commute_pinnedX_of_not_isRoot_add (K := K) isRoot_rootB hβ hne hne' hn s c
        rw [commutatorElement_eq_one_iff_mul_comm.2 hcomm']
        exact one_mem _
    have hF : (MulAut.conj (pinnedX TwistTag.D4.tag K rootB s)).toMonoidHom
          (pinnedX TwistTag.D4.tag K β c) =
        ⁅pinnedX TwistTag.D4.tag K rootB s, pinnedX TwistTag.D4.tag K β c⁆ *
          pinnedX TwistTag.D4.tag K β c := by
      rw [commutatorElement_def]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [hF]
    refine ⟨mul_mem (hle hcomm) (pinnedX_mem_heightSeries hβ h2 c), ?_⟩
    rw [coordC_mul (hle hcomm) (pinnedX_mem_heightSeries hβ h2 c), coordC_eq_zero_of_mem hcomm,
      zero_add, RingHom.id_apply]
  exact (coordC_semilinear_of_gen (MulAut.conj (pinnedX TwistTag.D4.tag K rootB s)).toMonoidHom
    (RingHom.id K) hgen hx).2

end CoordC

end CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3
