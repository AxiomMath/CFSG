module

public import CFSG.LieType.AlgebraicGroups.ToralRootCoverWords
public import CFSG.LieType.Chevalley.SignKernelComponentBruhat

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint WithConv
open scoped Pointwise

theorem ofFn_prod_mul_eq {G : Type*} [Group G] :
    ∀ {n : ℕ} (t y : Fin n → G), (∀ l l', l ≠ l' → Commute (t l) (y l')) →
      (List.ofFn fun l => t l * y l).prod = (List.ofFn t).prod * (List.ofFn y).prod
  | 0, _, _, _ => by simp
  | n + 1, t, y, h => by
    rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons,
      List.prod_cons, ofFn_prod_mul_eq (fun l => t l.succ) (fun l => y l.succ)
        fun l l' hne => h _ _ fun e => hne (Fin.succ_injective _ e)]
    have hc : Commute (y 0) (List.ofFn fun l => t l.succ).prod :=
      Commute.list_prod_right _ _ fun x hx => by
        obtain ⟨l, rfl⟩ := List.mem_ofFn.1 hx
        exact (h l.succ 0 (Fin.succ_ne_zero l)).symm
    rw [mul_assoc (t 0), ← mul_assoc (y 0), hc.eq]
    group

theorem ofFn_prod_mul_mul_eq {G : Type*} [Group G] {n : ℕ} (x y z : Fin n → G)
    (hxy : ∀ l l', l ≠ l' → Commute (x l) (y l')) (hxz : ∀ l l', l ≠ l' → Commute (x l) (z l'))
    (hyz : ∀ l l', l ≠ l' → Commute (y l) (z l')) :
    (List.ofFn fun l => x l * y l * z l).prod =
      (List.ofFn x).prod * (List.ofFn y).prod * (List.ofFn z).prod := by
  simp only [mul_assoc]
  rw [ofFn_prod_mul_eq x (fun l => y l * z l) fun l l' h => (hxy l l' h).mul_right (hxz l l' h),
    ofFn_prod_mul_eq y z hyz]

theorem ofFn_prod_ite_eq {G : Type*} [Monoid G] :
    ∀ {n : ℕ} (l₀ : Fin n) (g : G), (List.ofFn fun l => if l = l₀ then g else 1).prod = g
  | 0, l₀, _ => l₀.elim0
  | n + 1, l₀, g => by
    rw [List.ofFn_succ, List.prod_cons]
    refine Fin.cases ?_ (fun l₁ => ?_) l₀
    · have : (fun l : Fin n => if l.succ = (0 : Fin (n + 1)) then g else 1) = fun _ => 1 :=
        funext fun l => by simp [Fin.succ_ne_zero l]
      simp only [↓reduceIte]
      rw [this, List.ofFn_const, List.prod_replicate, one_pow, mul_one]
    · have : (fun l : Fin n => if l.succ = l₁.succ then g else 1) =
          fun l => if l = l₁ then g else 1 :=
        funext fun l => by simp only [Fin.succ_inj]
      have h0 : (if (0 : Fin (n + 1)) = l₁.succ then g else 1) = 1 := by
        simp [(Fin.succ_ne_zero l₁).symm]
      rw [h0, one_mul, this]
      exact ofFn_prod_ite_eq l₁ g

variable {τ : Tag} {k : Type} [Field k] {M : Type*} [CommGroup M]
  {χ : Multiplicative (Fin τ.rank → ℤ) →* M}

theorem commute_of_mem_componentRootSpan
    {i i' : KernelComponent χ} (h : i ≠ i')
    {x y : ModGL τ k} (hx : x ∈ componentRootSpan k χ i) (hy : y ∈ componentRootSpan k χ i') :
    Commute x y := by
  have h1 := (root_character_kernel_orthogonal_central_product τ k χ).2.2.1 i i' h
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h1
  exact (Subgroup.mem_centralizer_iff.1 (h1 hx) y hy).symm

theorem exists_ofFn_eq_of_mem_rootSpan
    {nI : ℕ} {κ : Fin nI → KernelComponent χ}
    (hκ : Function.Bijective κ) {s : ModGL τ k} (hs : s ∈ rootSpan τ k (kernelRoots χ)) :
    ∃ f : Fin nI → ModGL τ k, (∀ l, f l ∈ componentRootSpan k χ (κ l)) ∧
      (List.ofFn f).prod = s := by
  classical
  have hcomm : ∀ {f f' : Fin nI → ModGL τ k}, (∀ l, f l ∈ componentRootSpan k χ (κ l)) →
      (∀ l, f' l ∈ componentRootSpan k χ (κ l)) → ∀ l l', l ≠ l' → Commute (f l) (f' l') :=
    fun hf hf' l l' h => commute_of_mem_componentRootSpan (fun e => h (hκ.1 e)) (hf l) (hf' l')
  let P : Subgroup (ModGL τ k) :=
    { carrier := {g | ∃ f : Fin nI → ModGL τ k, (∀ l, f l ∈ componentRootSpan k χ (κ l)) ∧
        (List.ofFn f).prod = g}
      one_mem' := ⟨fun _ => 1, fun _ => one_mem _, by
        rw [List.ofFn_const, List.prod_replicate, one_pow]⟩
      mul_mem' := by
        rintro _ _ ⟨f, hf, rfl⟩ ⟨f', hf', rfl⟩
        exact ⟨fun l => f l * f' l, fun l => mul_mem (hf l) (hf' l),
          ofFn_prod_mul_eq f f' (hcomm hf hf')⟩
      inv_mem' := by
        rintro _ ⟨f, hf, rfl⟩
        refine ⟨fun l => (f l)⁻¹, fun l => inv_mem (hf l), eq_inv_of_mul_eq_one_right ?_⟩
        rw [← ofFn_prod_mul_eq f (fun l => (f l)⁻¹)
          (hcomm hf fun l => inv_mem (hf l))]
        simp only [mul_inv_cancel, List.ofFn_const, List.prod_replicate, one_pow] }
  have hle : rootSpan τ k (kernelRoots χ) ≤ P := by
    refine iSup₂_le fun α hα => ?_
    intro x hx
    obtain ⟨l₀, hl₀⟩ := hκ.2 (⟦⟨α, hα⟩⟧ : KernelComponent χ)
    refine ⟨fun l => if l = l₀ then x else 1, fun l => ?_, ofFn_prod_ite_eq l₀ x⟩
    by_cases hl : l = l₀
    · subst hl
      simp only [↓reduceIte]
      exact le_iSup₂_of_le (f := fun β (_ : β ∈ componentRoots χ (κ l)) => rootSubgroup τ k β) α
        ⟨hα, hl₀.symm⟩ le_rfl hx
    · simp only [hl, ↓reduceIte]
      exact one_mem _
  exact hle hs

section Lifts

variable
    {i : KernelComponent χ} {v : (Fin τ.rank → ℤ) → WeylGroup τ}
  {j : (Fin τ.rank → ℤ) → Fin τ.rank}
  (hvj : ∀ β ∈ simpleRoots (componentRoots χ i), v β • (Pi.single (j β) 1 : Fin τ.rank → ℤ) = β)
include hvj

theorem list_prod_componentWeylElt_mem_componentLifts
    {ω : List (Fin τ.rank → ℤ)}
    (hω : IsComponentWord (componentRoots χ i) ω) :
    (ω.map (componentWeylElt k v j)).prod ∈
      componentLifts k χ i v j (reflectionWordProd ω) := by
  refine mem_componentLifts.2 ⟨Subgroup.list_prod_mem _ fun x hx => ?_, ?_⟩
  · obtain ⟨β, hβ, rfl⟩ := List.mem_map.1 hx
    exact componentWeylElt_mem_componentMonomial (hω β hβ)
  · induction ω with
    | nil => exact mapsRootLines_one
    | cons β ω ih =>
      rw [List.map_cons, List.prod_cons, reflectionWordProd, List.map_cons, List.prod_cons]
      exact (mapsRootLines_componentWeylElt (hvj β (hω β List.mem_cons_self))).mul
        (ih fun γ hγ => hω γ (List.mem_cons_of_mem β hγ))

theorem exists_eq_mul_lift_mul_of_mem_componentRootSpan
    {ω : WeylGroup τ → List (Fin τ.rank → ℤ)}
    (hω : ∀ w ∈ componentWeylGroup (componentRoots χ i),
      IsComponentWord (componentRoots χ i) (ω w) ∧ reflectionWordProd (ω w) = w)
    {s : ModGL τ k} (hs : s ∈ componentRootSpan k χ i) :
    ∃ w ∈ componentWeylGroup (componentRoots χ i), ∃ t ∈ componentTorus k χ i,
      ∃ u ∈ componentUnipotent k χ i, ∃ u' ∈ componentUnipotent k χ i,
        s = t * u * ((ω w).map (componentWeylElt k v j)).prod * u' := by
  rw [← SetLike.mem_coe, coe_componentRootSpan_eq_iUnion hvj, Set.mem_iUnion₂] at hs
  obtain ⟨w, hw, hs⟩ := hs
  have hlift := list_prod_componentWeylElt_mem_componentLifts (k := k) hvj (hω w hw).1
  rw [(hω w hw).2] at hlift
  rw [← doubleCoset_eq_componentCell hvj hlift] at hs
  obtain ⟨_, ⟨b, hb, _, rfl, rfl⟩, b', hb', rfl⟩ := hs
  rw [SetLike.mem_coe, ← SetLike.mem_coe, coe_componentBorel] at hb hb'
  obtain ⟨t₁, ht₁, u₁, hu₁, rfl⟩ := hb
  obtain ⟨t₂, ht₂, u₂, hu₂, rfl⟩ := hb'
  set g := ((ω w).map (componentWeylElt k v j)).prod
  have ht₃ : g * t₂ * g⁻¹ ∈ componentTorus k χ i :=
    conj_mem_componentTorus hvj (mem_componentLifts.1 hlift).1 ht₂
  have hu₁' : (g * t₂ * g⁻¹)⁻¹ * u₁ * (g * t₂ * g⁻¹) ∈ componentUnipotent k χ i := by
    have hN := componentTorus_le_normalizer (inv_mem ht₃)
    have := (Subgroup.mem_normalizer_iff.1 hN u₁).1 hu₁
    simpa using this
  refine ⟨w, hw, t₁ * (g * t₂ * g⁻¹), mul_mem ht₁ ht₃, _, hu₁', u₂, hu₂, ?_⟩
  simp only [g]
  group

end Lifts

section Cover

variable
    {nI : ℕ} {κ : Fin nI → KernelComponent χ} {m : Fin nI → ℕ}
  {α : (l : Fin nI) → Fin (m l) → Fin τ.rank → ℤ} {v : (Fin τ.rank → ℤ) → WeylGroup τ}
  {j : (Fin τ.rank → ℤ) → Fin τ.rank} {ω : KernelComponent χ → WeylGroup τ → List (Fin τ.rank → ℤ)}

theorem componentRootSpan_le_rootSpan
    (i : KernelComponent χ) :
    componentRootSpan k χ i ≤ rootSpan τ k (kernelRoots χ) :=
  rootSpan_mono fun _ h => h.1

theorem ofFn_pinnedX_mem_componentUnipotent
    {l : Fin nI}
    (hαr : Set.range (α l) = posRoots (componentRoots χ (κ l))) (c : Fin (m l) → k) :
    (List.ofFn fun p => pinnedX τ k (α l p) (c p)).prod ∈ componentUnipotent k χ (κ l) := by
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨p, rfl⟩ := List.mem_ofFn.1 hx
  have hp : α l p ∈ posRoots (componentRoots χ (κ l)) := hαr ▸ ⟨p, rfl⟩
  exact le_iSup₂_of_le (f := fun β (_ : β ∈ posRoots (componentRoots χ (κ l))) =>
    rootSubgroup τ k β) (α l p) hp le_rfl (Subgroup.subset_closure ⟨c p, rfl⟩)

variable
    (hvj : ∀ i, ∀ β ∈ simpleRoots (componentRoots χ i),
    v β • (Pi.single (j β) 1 : Fin τ.rank → ℤ) = β)
  (hω : ∀ i, ∀ w ∈ componentWeylGroup (componentRoots χ i),
    IsComponentWord (componentRoots χ i) (ω i w) ∧ reflectionWordProd (ω i w) = w)
  (hαr : ∀ l, Set.range (α l) = posRoots (componentRoots χ (κ l)))

include hvj hω hαr in
theorem cover_factor_mem
    {w : Fin nI → WeylGroup τ}
    (hw : ∀ l, w l ∈ componentWeylGroup (componentRoots χ (κ l))) (l : Fin nI)
    (c d : Fin (m l) → k) :
    (List.ofFn fun p => pinnedX τ k (α l p) (c p)).prod ∈ componentRootSpan k χ (κ l) ∧
      ((ω (κ l) (w l)).map (componentWeylElt k v j)).prod ∈ componentRootSpan k χ (κ l) ∧
      (List.ofFn fun p => pinnedX τ k (α l p) (d p)).prod ∈ componentRootSpan k χ (κ l) :=
  ⟨componentUnipotent_le_componentRootSpan (ofFn_pinnedX_mem_componentUnipotent (hαr l) c),
    componentMonomial_le_componentRootSpan (hvj (κ l))
      (mem_componentLifts.1 (list_prod_componentWeylElt_mem_componentLifts (k := k) (hvj (κ l))
        (hω (κ l) (w l) (hw l)).1)).1,
    componentUnipotent_le_componentRootSpan (ofFn_pinnedX_mem_componentUnipotent (hαr l) d)⟩

include hvj hω hαr in
theorem toralCoverElt_mem
    {w : Fin nI → WeylGroup τ}
    (hw : ∀ l, w l ∈ componentWeylGroup (componentRoots χ (κ l))) (t : Fin τ.rank → kˣ)
    (c d : (l : Fin nI) → Fin (m l) → k) :
    toralCoverElt τ k α v j (fun l => ω (κ l) (w l)) t c d ∈
      torusGroup τ k ⊔ rootSpan τ k (kernelRoots χ) := by
  refine mul_mem (Subgroup.mem_sup_left ?_) (Subgroup.mem_sup_right ?_)
  · rw [← torusProdHom_apply, ← range_torusProdHom]
    exact ⟨t, rfl⟩
  · refine Subgroup.list_prod_mem _ fun x hx => ?_
    obtain ⟨l, rfl⟩ := List.mem_ofFn.1 hx
    obtain ⟨h1, h2, h3⟩ := cover_factor_mem hvj hω hαr hw l (c l) (d l)
    exact componentRootSpan_le_rootSpan _ (mul_mem (mul_mem h1 h2) h3)

include hvj hω hαr in
theorem exists_toralCoverElt_eq
    (hκ : Function.Bijective κ) (hα : ∀ l, Function.Injective (α l))
    {g : ModGL τ k} (hg : g ∈ torusGroup τ k ⊔ rootSpan τ k (kernelRoots χ)) :
    ∃ w : Fin nI → WeylGroup τ, (∀ l, w l ∈ componentWeylGroup (componentRoots χ (κ l))) ∧
      ∃ t c d, toralCoverElt τ k α v j (fun l => ω (κ l) (w l)) t c d = g := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _
    (torusGroup_le_normalizer_rootSpan (K := k) fun β h => h.1)] at hg
  obtain ⟨h, hh, s, hs, rfl⟩ := hg
  obtain ⟨f, hf, rfl⟩ := exists_ofFn_eq_of_mem_rootSpan hκ hs
  choose w hw t ht u hu u' hu' hfe using fun l =>
    exists_eq_mul_lift_mul_of_mem_componentRootSpan (hvj (κ l)) (hω (κ l)) (hf l)
  have hcol : ∀ l, ∀ x ∈ componentUnipotent k χ (κ l), ∃ c : Fin (m l) → k,
      (List.ofFn fun p => pinnedX τ k (α l p) (c p)).prod = x := fun l x hx => by
    obtain ⟨c, -, hc⟩ := ((positive_root_collection τ k).1 (posRoots (componentRoots χ (κ l)))
      (fun β hβ => isRoot_height_pos_of_mem_posRoots hβ)
      (fun β hβ γ hγ a b ha hb hr => mem_posRoots_of_nsmul_add hβ hγ a b ha hb hr) (α l) (hα l)
      (hαr l)).2.2 hx
    exact ⟨c, hc⟩
  choose c hc using fun l => hcol l (u l) (hu l)
  choose d hd using fun l => hcol l (u' l) (hu' l)
  have htor : h * (List.ofFn t).prod ∈ (torusProdHom τ k).range := by
    rw [range_torusProdHom]
    refine mul_mem hh (Subgroup.list_prod_mem _ fun x hx => ?_)
    obtain ⟨l, rfl⟩ := List.mem_ofFn.1 hx
    exact componentTorus_le_torusGroup k χ (κ l) (ht l)
  obtain ⟨t₀, ht₀⟩ := htor
  refine ⟨w, hw, t₀, c, d, ?_⟩
  have hsplit : (List.ofFn f).prod = (List.ofFn t).prod *
      (List.ofFn fun l => u l * ((ω (κ l) (w l)).map (componentWeylElt k v j)).prod *
        u' l).prod := by
    rw [← ofFn_prod_mul_eq]
    · refine congrArg (fun F : Fin nI → ModGL τ k => (List.ofFn F).prod) (funext fun l => ?_)
      rw [hfe l]
      group
    · intro l l' hne
      refine commute_of_mem_componentRootSpan (fun e => hne (hκ.1 e))
        (componentTorus_le_componentRootSpan k χ (κ l) (ht l)) ?_
      exact mul_mem (mul_mem (componentUnipotent_le_componentRootSpan (hu l'))
        (cover_factor_mem hvj hω hαr hw l' (c l') (d l')).2.1)
        (componentUnipotent_le_componentRootSpan (hu' l'))
  rw [toralCoverElt, ← torusProdHom_apply, ht₀, hsplit, mul_assoc]
  congr 2
  refine congrArg (fun F : Fin nI → ModGL τ k => (List.ofFn F).prod) (funext fun l => ?_)
  rw [hc l, hd l]

theorem mapsRootLines_ofFn_prod :
    ∀ {n : ℕ} (g : Fin n → ModGL τ k) (w : Fin n → WeylGroup τ),
      (∀ l, MapsRootLines (g l) (w l)) → MapsRootLines (List.ofFn g).prod (List.ofFn w).prod
  | 0, _, _, _ => by simpa using mapsRootLines_one
  | n + 1, g, w, h => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons]
    exact (h 0).mul (mapsRootLines_ofFn_prod (fun l => g l.succ) (fun l => w l.succ)
      fun l => h l.succ)

include hvj hω hαr in
theorem toralCoverElt_mem_bruhatCell
    (hκ : Function.Injective κ) {w : Fin nI → WeylGroup τ}
    (hw : ∀ l, w l ∈ componentWeylGroup (componentRoots χ (κ l))) (t : Fin τ.rank → kˣ)
    (c d : (l : Fin nI) → Fin (m l) → k) :
    toralCoverElt τ k α v j (fun l => ω (κ l) (w l)) t c d ∈
      bruhatCell τ k (List.ofFn w).prod := by
  have hfac := fun l => cover_factor_mem hvj hω hαr hw l (c l) (d l)
  let x : Fin nI → ModGL τ k := fun l => (List.ofFn fun p => pinnedX τ k (α l p) (c l p)).prod
  let y : Fin nI → ModGL τ k := fun l => ((ω (κ l) (w l)).map (componentWeylElt k v j)).prod
  let z : Fin nI → ModGL τ k := fun l => (List.ofFn fun p => pinnedX τ k (α l p) (d l p)).prod
  have hcomm : ∀ {a b : Fin nI → ModGL τ k}, (∀ l, a l ∈ componentRootSpan k χ (κ l)) →
      (∀ l, b l ∈ componentRootSpan k χ (κ l)) → ∀ l l', l ≠ l' → Commute (a l) (b l') :=
    fun ha hb l l' h => commute_of_mem_componentRootSpan (fun e => h (hκ e)) (ha l) (hb l')
  have hre : (List.ofFn fun l => x l * y l * z l).prod =
      (List.ofFn x).prod * (List.ofFn y).prod * (List.ofFn z).prod :=
    ofFn_prod_mul_mul_eq x y z (hcomm (fun l => (hfac l).1) fun l => (hfac l).2.1)
      (hcomm (fun l => (hfac l).1) fun l => (hfac l).2.2)
      (hcomm (fun l => (hfac l).2.1) fun l => (hfac l).2.2)
  have hlift : ∀ l, y l ∈ componentLifts k χ (κ l) v j (w l) := fun l => by
    have h := list_prod_componentWeylElt_mem_componentLifts (k := k) (hvj (κ l))
      (hω (κ l) (w l) (hw l)).1
    rwa [(hω (κ l) (w l) (hw l)).2] at h
  have hyM : (List.ofFn y).prod ∈ monomialSubgroup τ k := by
    refine Subgroup.list_prod_mem _ fun g hg => ?_
    obtain ⟨l, rfl⟩ := List.mem_ofFn.1 hg
    exact componentMonomial_le_monomialSubgroup k χ (κ l) v j (mem_componentLifts.1 (hlift l)).1
  have hyw : MapsRootLines (List.ofFn y).prod (List.ofFn w).prod :=
    mapsRootLines_ofFn_prod y w fun l => (mem_componentLifts.1 (hlift l)).2
  obtain ⟨w', k₀, hk₀, hk₀e⟩ := monomialSubgroup_le_torusWeylCosets hyM
  have hmaps : MapsRootLines (k₀ * canonicalRep (coxeterSystem τ) k w') w' := by
    simpa using (mapsRootLines_of_mem_torusGroup hk₀).mul (mapsRootLines_canonicalRep w')
  rw [hk₀e] at hyw
  have hww : (List.ofFn w).prod = w' := hyw.unique hmaps
  have hxU : (List.ofFn x).prod ∈ posUnipotent τ k := by
    refine Subgroup.list_prod_mem _ fun g hg => ?_
    obtain ⟨l, rfl⟩ := List.mem_ofFn.1 hg
    exact componentUnipotent_le_posUnipotent (ofFn_pinnedX_mem_componentUnipotent (hαr l) (c l))
  have hzU : (List.ofFn z).prod ∈ posUnipotent τ k := by
    refine Subgroup.list_prod_mem _ fun g hg => ?_
    obtain ⟨l, rfl⟩ := List.mem_ofFn.1 hg
    exact componentUnipotent_le_posUnipotent (ofFn_pinnedX_mem_componentUnipotent (hαr l) (d l))
  have htor : (List.ofFn fun i => torusElt τ k i (t i)).prod ∈ torusGroup τ k := by
    rw [← torusProdHom_apply, ← range_torusProdHom]
    exact ⟨t, rfl⟩
  have he : toralCoverElt τ k α v j (fun l => ω (κ l) (w l)) t c d =
      ((List.ofFn fun i => torusElt τ k i (t i)).prod * (List.ofFn x).prod * k₀) *
        canonicalRep (coxeterSystem τ) k w' * (List.ofFn z).prod := by
    rw [toralCoverElt, show (List.ofFn fun l => (List.ofFn fun p => pinnedX τ k (α l p)
      (c l p)).prod * ((ω (κ l) (w l)).map (componentWeylElt k v j)).prod *
      (List.ofFn fun p => pinnedX τ k (α l p) (d l p)).prod).prod =
        (List.ofFn fun l => x l * y l * z l).prod from rfl, hre, hk₀e]
    group
  rw [he, hww]
  refine mem_bruhatCell.2 ⟨_, ?_, _, Subgroup.mem_sup_right hzU, rfl⟩
  exact mul_mem (mul_mem (Subgroup.mem_sup_left htor) (Subgroup.mem_sup_right hxU))
    (Subgroup.mem_sup_left hk₀)

end Cover

theorem closure_rootReflection_kernelRoots :
    Subgroup.closure (rootReflection '' kernelRoots χ) =
      ⨆ i, componentWeylGroup (componentRoots χ i) := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ ⟨β, hβ, rfl⟩
    have hβi : β ∈ componentRoots χ (⟦⟨β, hβ⟩⟧ : KernelComponent χ) := ⟨hβ, rfl⟩
    obtain ⟨u, hu, γ, hγ, rfl⟩ := exists_smul_simpleRoot (isRootComponent_componentRoots _) hβi
    rw [SetLike.mem_coe, rootReflection_smul_root u (simpleRoots_isRoot hγ)]
    exact Subgroup.mem_iSup_of_mem _
      (mul_mem (mul_mem hu (rootReflection_mem_componentWeylGroup hγ)) (inv_mem hu))
  · refine iSup_le fun i => (Subgroup.closure_le _).2 ?_
    rintro _ ⟨β, hβ, rfl⟩
    exact Subgroup.subset_closure ⟨β, (simpleRoots_subset hβ).1, rfl⟩

end CFSG.LieType.AlgebraicGroups
