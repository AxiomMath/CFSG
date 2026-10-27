module

public import CFSG.LieType.Chevalley.SignKernelComponentBruhat
public import CFSG.LieType.Chevalley.SignKernelComponentPerfect
public import CFSG.LieType.Chevalley.OppositeBorel
public import CFSG.LieType.TitsSimplicity.Simplicity

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint
open scoped Pointwise

theorem exists_edge_of_reflTransGen {α : Type*} {r : α → α → Prop} {P : α → Prop} {a b : α}
    (h : Relation.ReflTransGen r a b) (ha : P a) (hb : ¬ P b) :
    ∃ x y, r x y ∧ P x ∧ ¬ P y := by
  induction h with
  | refl => exact absurd ha hb
  | @tail c d _ hcd ih =>
    by_cases hc : P c
    · exact ⟨c, d, hcd, hc, hb⟩
    · exact ih hc

variable {τ : Tag} {K : Type} [Field K] {G : Type*} [CommGroup G]
  {χ : Multiplicative (Fin τ.rank → ℤ) →* G} {i : KernelComponent χ}

section Lengths

variable {Ψ : Set (Fin τ.rank → ℤ)}

theorem componentLength_rootReflection
    (hΨ : IsRootComponent Ψ) {β : Fin τ.rank → ℤ}
    (hβ : β ∈ simpleRoots Ψ) : componentLength Ψ (rootReflection β) = 1 := by
  have := (componentLength_mul_rootReflection hΨ hβ (one_mem _)).2 (by
    rw [one_smul]
    exact not_mem_negRoots_of_mem_posRoots (simpleRoot_mem_posRoots hβ))
  rwa [one_mul, componentLength_one] at this

theorem componentLength_rootReflection_mul_rootReflection
    (hΨ : IsRootComponent Ψ)
    {β γ : Fin τ.rank → ℤ} (hβ : β ∈ simpleRoots Ψ) (hγ : γ ∈ simpleRoots Ψ) (hne : β ≠ γ) :
    componentLength Ψ (rootReflection γ * rootReflection β) = 2 := by
  have hrγβ : rootReflection γ • β ∈ posRoots Ψ :=
    (rootReflection_mem_posRoots hΨ hγ (simpleRoot_mem_posRoots hβ) hne).1
  have := (componentLength_mul_rootReflection hΨ hβ (rootReflection_mem_componentWeylGroup hγ)).2
    (not_mem_negRoots_of_mem_posRoots hrγβ)
  rw [this, componentLength_rootReflection hΨ hγ]

end Lengths

variable (χ i) in
theorem exists_componentWeylChoice
    : ∃ (v : (Fin τ.rank → ℤ) → WeylGroup τ)
    (j : (Fin τ.rank → ℤ) → Fin τ.rank), ∀ β ∈ simpleRoots (componentRoots χ i),
      v β • (Pi.single (j β) 1 : Fin τ.rank → ℤ) = β := by
  have h : ∀ β : Fin τ.rank → ℤ, ∃ (w : WeylGroup τ) (k : Fin τ.rank),
      IsRoot τ β → w • (Pi.single k 1 : Fin τ.rank → ℤ) = β := fun β => by
    by_cases hβ : IsRoot τ β
    · obtain ⟨w, k, h⟩ := isRoot_iff_exists_smul_single.1 hβ
      exact ⟨w, k, fun _ => h⟩
    · exact ⟨1, ⟨0, τ.rank_pos⟩, fun h => absurd h hβ⟩
  choose v j hvj using h
  exact ⟨v, j, fun β hβ => hvj β (simpleRoots_isRoot hβ)⟩

theorem normalCore_componentBorel_le_center :
    ((componentBorel K χ i).subgroupOf (componentRootSpan K χ i)).normalCore ≤
      Subgroup.center (componentRootSpan K χ i) := by
  obtain ⟨v, j, hvj⟩ := exists_componentWeylChoice χ i
  have hΨ := isRootComponent_componentRoots i
  set S := componentRootSpan K χ i
  set R := ((componentBorel K χ i).subgroupOf S).normalCore
  obtain ⟨w₀, hw₀, himg⟩ := exists_longest hΨ
  obtain ⟨g₀, hg₀N, hg₀w⟩ := exists_mem_componentMonomial_mapsRootLines (K := K) hvj hw₀
  have hg₀S : g₀ ∈ S := componentMonomial_le_componentRootSpan hvj hg₀N
  have hg₀M : g₀ ∈ monomialSubgroup τ K := componentMonomial_le_monomialSubgroup K χ i v j hg₀N
  have himg' : (fun α => w₀⁻¹ • α) '' negRoots (componentRoots χ i) =
      posRoots (componentRoots χ i) := by
    rw [← himg, Set.image_image]
    simp
  have hnegroot : ∀ α ∈ negRoots (componentRoots χ i), IsRoot τ α ∧ height α < 0 := fun α hα =>
    ⟨hΨ.isRoot α ((mem_negRoots_iff hΨ).1 hα).1, ((mem_negRoots_iff hΨ).1 hα).2⟩
  have hconjU : ∀ u ∈ componentUnipotent K χ i,
      g₀ * u * g₀⁻¹ ∈ rootSpan τ K (negRoots (componentRoots χ i)) := fun u hu => by
    have h := conj_mem_rootSpan_of_mapsRootLines hg₀M hg₀w (S := posRoots (componentRoots χ i))
      (fun α hα => hΨ.isRoot α hα.1) hu
    rwa [himg] at h
  have hconjV : ∀ z ∈ rootSpan τ K (negRoots (componentRoots χ i)),
      g₀⁻¹ * z * g₀ ∈ componentUnipotent K χ i := fun z hz => by
    have h := conj_mem_rootSpan_of_mapsRootLines (inv_mem hg₀M) hg₀w.inv
      (S := negRoots (componentRoots χ i)) (fun α hα => (hnegroot α hα).1) hz
    rwa [inv_inv, himg'] at h
  have hRT : ∀ x ∈ R, (x : ModGL τ K) ∈ componentTorus K χ i := by
    intro x hx
    have hxB : (x : ModGL τ K) ∈ componentBorel K χ i :=
      Subgroup.mem_subgroupOf.1 (Subgroup.normalCore_le _ hx)
    have hx' : g₀⁻¹ * (x : ModGL τ K) * g₀ ∈ componentBorel K χ i := by
      have h := hx (⟨g₀, hg₀S⟩ : S)⁻¹
      rw [Subgroup.mem_subgroupOf] at h
      simpa using h
    have hxopp : (x : ModGL τ K) ∈ torusGroup τ K ⊔ negUnipotent τ K := by
      rw [← SetLike.mem_coe, coe_componentBorel] at hx'
      obtain ⟨t, ht, u, hu, htu⟩ := hx'
      have e : (x : ModGL τ K) = (g₀ * t * g₀⁻¹) * (g₀ * u * g₀⁻¹) := by
        calc (x : ModGL τ K) = g₀ * (g₀⁻¹ * (x : ModGL τ K) * g₀) * g₀⁻¹ := by group
          _ = _ := by rw [← htu]; group
      rw [e]
      exact mul_mem (Subgroup.mem_sup_left (componentTorus_le_torusGroup K χ i
        (conj_mem_componentTorus hvj hg₀N ht)))
        (Subgroup.mem_sup_right (rootSpan_le_negUnipotent hnegroot (hconjU u hu)))
    obtain ⟨w₁, hw₁, -⟩ := weyl_longest_element τ
    have hH : (x : ModGL τ K) ∈ torusGroup τ K := by
      rw [← (opposite_Borel_intersection τ K w₁ hw₁).2.2.1]
      exact Subgroup.mem_inf.2 ⟨componentBorel_le_borelGroup hxB, hxopp⟩
    exact Subgroup.mem_inf.2 ⟨x.2, hH⟩
  have hRU : ∀ x ∈ R, ∀ u ∈ componentUnipotent K χ i, (x : ModGL τ K) * u = u * x := by
    intro x hx u hu
    have huS : u ∈ S := componentUnipotent_le_componentRootSpan hu
    have h1 : (x : ModGL τ K) * u * (x : ModGL τ K)⁻¹ * u⁻¹ ∈ componentUnipotent K χ i :=
      mul_mem ((Subgroup.mem_normalizer_iff.1 (componentTorus_le_normalizer (hRT x hx)) u).1 hu)
        (inv_mem hu)
    have h2 : (x : ModGL τ K) * u * (x : ModGL τ K)⁻¹ * u⁻¹ ∈ componentTorus K χ i := by
      have hc : x * ((⟨u, huS⟩ : S) * x⁻¹ * (⟨u, huS⟩ : S)⁻¹) ∈ R :=
        mul_mem hx ((Subgroup.normalCore_normal _).conj_mem _ (inv_mem hx) _)
      have h := hRT _ hc
      simpa [mul_assoc] using h
    have h3 : (x : ModGL τ K) * u * (x : ModGL τ K)⁻¹ * u⁻¹ = 1 := by
      have h := Subgroup.mem_inf.2 ⟨h2, h1⟩
      rwa [componentTorus_inf_componentUnipotent, Subgroup.mem_bot] at h
    calc (x : ModGL τ K) * u = ((x : ModGL τ K) * u * (x : ModGL τ K)⁻¹ * u⁻¹) * (u * x) := by
          group
      _ = u * x := by rw [h3, one_mul]
  have hRV : ∀ x ∈ R, ∀ z ∈ rootSpan τ K (negRoots (componentRoots χ i)),
      (x : ModGL τ K) * z = z * x := by
    intro x hx z hz
    have hy : (⟨g₀, hg₀S⟩ : S)⁻¹ * x * (⟨g₀, hg₀S⟩ : S)⁻¹⁻¹ ∈ R :=
      (Subgroup.normalCore_normal _).conj_mem x hx _
    have h := hRU _ hy _ (hconjV z hz)
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv, inv_inv] at h
    calc (x : ModGL τ K) * z = g₀ * ((g₀⁻¹ * x * g₀) * (g₀⁻¹ * z * g₀)) * g₀⁻¹ := by group
      _ = g₀ * ((g₀⁻¹ * z * g₀) * (g₀⁻¹ * x * g₀)) * g₀⁻¹ := by rw [h]
      _ = z * x := by group
  intro x hx
  have hcent : S ≤ Subgroup.centralizer {(x : ModGL τ K)} := by
    refine iSup₂_le fun α hα => ?_
    intro z hz
    rw [Subgroup.mem_centralizer_singleton_iff]
    rcases mem_posRoots_or_mem_negRoots hΨ hα with hp | hn
    · exact (hRU x hx z ((le_iSup₂_of_le α hp le_rfl :
        rootSubgroup τ K α ≤ componentUnipotent K χ i) hz)).symm
    · exact (hRV x hx z ((le_iSup₂_of_le α hn le_rfl :
        rootSubgroup τ K α ≤ rootSpan τ K (negRoots (componentRoots χ i))) hz)).symm
  rw [Subgroup.mem_center_iff]
  intro s
  exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (hcent s.2))

variable
    {v : (Fin τ.rank → ℤ) → WeylGroup τ} {j : (Fin τ.rank → ℤ) → Fin τ.rank}

theorem componentWeylElt_eq_mul
    (β : Fin τ.rank → ℤ) :
    componentWeylElt K v j β = componentXElt K v j β 1 * componentYElt K v j β (-1) *
      componentXElt K v j β 1 := by
  have e : weylElt τ K (j β) 1 =
      xUnit τ K (j β) 1 * yUnit τ K (j β) (-1) * xUnit τ K (j β) 1 := by
    have h : weylElt τ K (j β) 1 = xUnit τ K (j β) ((1 : Kˣ) : K) *
        yUnit τ K (j β) (-(((1 : Kˣ)⁻¹ : Kˣ) : K)) * xUnit τ K (j β) ((1 : Kˣ) : K) :=
      Units.ext rfl
    simpa using h
  simp only [componentWeylElt, componentXElt, componentYElt, e]
  group

theorem mem_componentCell_of_mem_componentLifts
    {w : WeylGroup τ} {g : ModGL τ K}
    (hg : g ∈ componentLifts K χ i v j w) : g ∈ componentCell K χ i v j w :=
  mem_componentCell.2 ⟨1, one_mem _, g, hg, 1, one_mem _, by group⟩

theorem inv_mem_componentCell
    {w : WeylGroup τ} {x : ModGL τ K}
    (hx : x ∈ componentCell K χ i v j w) : x⁻¹ ∈ componentCell K χ i v j w⁻¹ := by
  obtain ⟨b, hb, g, hg, b', hb', rfl⟩ := mem_componentCell.1 hx
  exact mem_componentCell.2 ⟨b'⁻¹, inv_mem hb', g⁻¹, inv_mem_componentLifts hg, b⁻¹, inv_mem hb,
    by group⟩

variable (hvj : ∀ β ∈ simpleRoots (componentRoots χ i),
  v β • (Pi.single (j β) 1 : Fin τ.rank → ℤ) = β)
include hvj

theorem componentWeylElt_mem_of_lift_mem
    {A : Subgroup (ModGL τ K)}
    (hBA : componentBorel K χ i ≤ A) {w : WeylGroup τ} {g : ModGL τ K}
    (hg : g ∈ componentLifts K χ i v j w) (hgA : g ∈ A) {β : Fin τ.rank → ℤ}
    (hβ : β ∈ simpleRoots (componentRoots χ i))
    (hneg : w⁻¹ • β ∈ negRoots (componentRoots χ i)) : componentWeylElt K v j β ∈ A := by
  have hx : ∀ c, componentXElt K v j β c ∈ A := fun c =>
    hBA (componentUnipotent_le_componentBorel (rootSpan_mono
      (Set.singleton_subset_iff.2 (simpleRoot_mem_posRoots hβ)) (componentXElt_mem (hvj β hβ) c)))
  have hy : ∀ c, componentYElt K v j β c ∈ A := fun c => by
    have hpos : w⁻¹ • (-β) ∈ posRoots (componentRoots χ i) := by
      rw [smul_neg]
      exact hneg
    obtain ⟨b, hb, e⟩ := exists_mul_eq_mul_of_mem_componentLifts hg
      (IsRoot.neg (simpleRoots_isRoot hβ)) hpos (componentYElt_mem (hvj β hβ) c)
    have e' : componentYElt K v j β c = g * b * g⁻¹ := by
      rw [← e]
      group
    rw [e']
    exact mul_mem (mul_mem hgA (hBA hb)) (inv_mem hgA)
  rw [componentWeylElt_eq_mul]
  exact mul_mem (mul_mem (hx 1) (hy (-1))) (hx 1)

omit hvj

theorem sup_componentBorel_eq_top
    {M : Subgroup (componentRootSpan K χ i)} (hM : M.Normal)
    (hMZ : ¬ M ≤ Subgroup.center (componentRootSpan K χ i)) :
    M ⊔ (componentBorel K χ i).subgroupOf (componentRootSpan K χ i) = ⊤ := by
  obtain ⟨v, j, hvj⟩ := exists_componentWeylChoice χ i
  have hΨ := isRootComponent_componentRoots i
  set B := componentBorel K χ i
  set M₀ := M.map (componentRootSpan K χ i).subtype
  have hM₀S : M₀ ≤ componentRootSpan K χ i := by
    rintro _ ⟨m, -, rfl⟩
    exact m.2
  have hconj : ∀ s ∈ componentRootSpan K χ i, ∀ m ∈ M₀, s * m * s⁻¹ ∈ M₀ := by
    rintro s hs _ ⟨m, hm, rfl⟩
    exact ⟨⟨s, hs⟩ * m * ⟨s, hs⟩⁻¹, hM.conj_mem m hm ⟨s, hs⟩, rfl⟩
  obtain ⟨m, hmM, hmB⟩ : ∃ m ∈ M₀, m ∉ B := by
    by_contra! h
    apply hMZ
    intro x hx
    refine normalCore_componentBorel_le_center (fun b => ?_)
    rw [Subgroup.mem_subgroupOf]
    exact h _ ⟨b * x * b⁻¹, hM.conj_mem x hx b, rfl⟩
  set E := M₀ ⊔ B
  have hBE : B ≤ E := le_sup_right
  have hME : M₀ ≤ E := le_sup_left
  have hBnorm : B ≤ Subgroup.normalizer (M₀ : Set (ModGL τ K)) :=
    fun b hb => Subgroup.mem_normalizer_iff.2 fun y =>
      ⟨fun hy => hconj b (componentBorel_le_componentRootSpan hb) y hy, fun hy => by
        have h := hconj b⁻¹ (inv_mem (componentBorel_le_componentRootSpan hb)) _ hy
        rwa [show b⁻¹ * (b * y * b⁻¹) * b⁻¹⁻¹ = y by group] at h⟩
  have hEset : (E : Set (ModGL τ K)) = (M₀ : Set (ModGL τ K)) * (B : Set (ModGL τ K)) :=
    Subgroup.coe_mul_of_right_le_normalizer_left _ _ hBnorm
  have hmU : m ∈ ⋃ w ∈ componentWeylGroup (componentRoots χ i), componentCell K χ i v j w := by
    rw [← coe_componentRootSpan_eq_iUnion hvj]
    exact hM₀S hmM
  obtain ⟨w, hw, hmw⟩ := Set.mem_iUnion₂.1 hmU
  obtain ⟨b, hb, g, hg, b', hb', hbgb⟩ := mem_componentCell.1 hmw
  have hgE : g ∈ E := by
    have e : g = b⁻¹ * m * b'⁻¹ := by
      rw [← hbgb]
      group
    rw [e]
    exact mul_mem (mul_mem (inv_mem (hBE hb)) (hME hmM)) (inv_mem (hBE hb'))
  have hw1 : w ≠ 1 := by
    rintro rfl
    apply hmB
    have hT : g ∈ componentTorus K χ i := by
      have h := inv_mul_mem_componentTorus hvj one_mem_componentLifts hg
      rwa [inv_one, one_mul] at h
    rw [← hbgb]
    exact mul_mem (mul_mem hb (componentTorus_le_componentBorel hT)) hb'
  obtain ⟨β₀, hβ₀, hβ₀neg⟩ := exists_smul_mem_negRoots hΨ (inv_mem hw) (inv_ne_one.2 hw1)
  have hβ₀E := componentWeylElt_mem_of_lift_mem hvj hBE hg hgE hβ₀ hβ₀neg
  have hall : ∀ β ∈ simpleRoots (componentRoots χ i), componentWeylElt K v j β ∈ E := by
    by_contra! hnot
    obtain ⟨γ₀, hγ₀, hγ₀E⟩ := hnot
    obtain ⟨β, γ, ⟨hβ, hγ, hβγ⟩, hβE, hγE⟩ := exists_edge_of_reflTransGen
      (P := fun x => componentWeylElt K v j x ∈ E) (simpleRoots_connected hΨ hβ₀ hγ₀) hβ₀E hγ₀E
    have hne : β ≠ γ := by
      rintro rfl
      exact hγE hβE
    apply hγE
    have hβE' : componentWeylElt K v j β ∈ (M₀ : Set (ModGL τ K)) * (B : Set (ModGL τ K)) := by
      rw [← hEset]
      exact hβE
    obtain ⟨m₁, hm₁, b₁, hb₁, hmb⟩ := hβE'
    have hnβ := componentWeylElt_mem_componentLifts hvj hβ (K := K)
    have hnγ := componentWeylElt_mem_componentLifts hvj hγ (K := K)
    have hrβ := rootReflection_mem_componentWeylGroup hβ
    have hrγ := rootReflection_mem_componentWeylGroup hγ
    have hβr := simpleRoots_isRoot hβ
    have hγr := simpleRoots_isRoot hγ
    have l1 := componentLength_rootReflection hΨ hβ
    have l2 := componentLength_rootReflection_mul_rootReflection hΨ hβ hγ hne
    have l2' := componentLength_rootReflection_mul_rootReflection hΨ hγ hβ hne.symm
    have l3 := componentLength_braid hΨ hβ hγ hne hβγ
    have hm₁cell : m₁⁻¹ ∈ componentCell K χ i v j (rootReflection β) := by
      have e : m₁⁻¹ = b₁ * (componentWeylElt K v j β)⁻¹ := by
        rw [← hmb]
        group
      have hl : (componentWeylElt K v j β)⁻¹ ∈ componentLifts K χ i v j (rootReflection β) := by
        have h := inv_mem_componentLifts hnβ
        rwa [rootReflection_inv hβr] at h
      rw [e]
      exact mem_componentCell.2 ⟨b₁, hb₁, _, hl, 1, one_mem _, by group⟩
    have h1 : componentWeylElt K v j γ * m₁⁻¹ ∈
        componentCell K χ i v j (rootReflection γ * rootReflection β) := by
      rw [← componentCell_mul_of_length_eq_add_one hvj hγ hrβ (by rw [l2, l1])]
      exact Set.mul_mem_mul (mem_componentCell_of_mem_componentLifts hnγ) hm₁cell
    have h2 : m₁ * (componentWeylElt K v j γ)⁻¹ ∈
        componentCell K χ i v j (rootReflection β * rootReflection γ) := by
      have h := inv_mem_componentCell h1
      simpa only [mul_inv_rev, inv_inv, rootReflection_inv hβr, rootReflection_inv hγr] using h
    have h3 : componentWeylElt K v j γ * m₁ * (componentWeylElt K v j γ)⁻¹ ∈
        componentCell K χ i v j (rootReflection γ * (rootReflection β * rootReflection γ)) := by
      rw [← componentCell_mul_of_length_eq_add_one hvj hγ (mul_mem hrβ hrγ)
        (by rw [← mul_assoc, l3, l2']), mul_assoc]
      exact Set.mul_mem_mul (mem_componentCell_of_mem_componentLifts hnγ) h2
    obtain ⟨c₁, hc₁, h, hh, c₂, hc₂, hc⟩ := mem_componentCell.1 h3
    have hhE : h ∈ E := by
      have e : h = c₁⁻¹ * (componentWeylElt K v j γ * m₁ * (componentWeylElt K v j γ)⁻¹) *
          c₂⁻¹ := by
        rw [← hc]
        group
      rw [e]
      exact mul_mem (mul_mem (inv_mem (hBE hc₁)) (hME (hconj _
        (componentWeylElt_mem_componentRootSpan (hvj γ hγ) (simpleRoots_subset hγ)) m₁ hm₁)))
        (inv_mem (hBE hc₂))
    have hdesc : (rootReflection γ * (rootReflection β * rootReflection γ))⁻¹ • γ ∈
        negRoots (componentRoots χ i) := by
      refine (componentLength_rootReflection_mul hΨ hγ (mul_mem hrγ (mul_mem hrβ hrγ))).1.1 ?_
      rw [← mul_assoc (rootReflection γ) (rootReflection γ), rootReflection_mul_self hγr, one_mul,
        ← mul_assoc, l3, l2']
    exact componentWeylElt_mem_of_lift_mem hvj hBE hh hhE hγ hdesc
  have hSE : componentRootSpan K χ i ≤ E := componentRootSpan_le_of hvj hBE
    ((Subgroup.closure_le _).2 (Set.union_subset
      (fun t ht => hBE (componentTorus_le_componentBorel ht)) (by
        rintro _ ⟨β, hβ, rfl⟩
        exact hall β hβ)))
  rw [eq_top_iff]
  intro s _
  have hs : (s : ModGL τ K) ∈ (M₀ : Set (ModGL τ K)) * (B : Set (ModGL τ K)) := by
    rw [← hEset]
    exact hSE s.2
  obtain ⟨m', hm', b₀, hb₀, hmb⟩ := hs
  obtain ⟨m'', hm'', rfl⟩ := hm'
  simp only [Subgroup.coe_subtype] at hmb
  have hb₀S : b₀ ∈ componentRootSpan K χ i := by
    have e : b₀ = (m'' : ModGL τ K)⁻¹ * s := by
      rw [← hmb]
      group
    rw [e]
    exact mul_mem (inv_mem m''.2) s.2
  have hs' : s = m'' * ⟨b₀, hb₀S⟩ := Subtype.ext hmb.symm
  rw [hs']
  exact mul_mem (Subgroup.mem_sup_left hm'')
    (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.2 hb₀))

theorem commutator_mem_componentUnipotent
    {x y : ModGL τ K} (hx : x ∈ componentBorel K χ i)
    (hy : y ∈ componentBorel K χ i) : x * y * x⁻¹ * y⁻¹ ∈ componentUnipotent K χ i := by
  rw [← SetLike.mem_coe, coe_componentBorel] at hx hy
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  obtain ⟨c, hc, d, hd, rfl⟩ := hy
  have hNa := componentTorus_le_normalizer ha
  have hNc := componentTorus_le_normalizer hc
  have e : a * b * (c * d) * (a * b)⁻¹ * (c * d)⁻¹ = (a * b * a⁻¹) *
      ((a * c) * (d * b⁻¹) * (a * c)⁻¹) * (a * c * a⁻¹ * c⁻¹) * (c * d⁻¹ * c⁻¹) := by
    group
  rw [e, show a * c * a⁻¹ * c⁻¹ = 1 by
    rw [mul_comm_of_mem_componentTorus ha hc]
    group, mul_one]
  exact mul_mem (mul_mem ((Subgroup.mem_normalizer_iff.1 hNa b).1 hb)
    ((Subgroup.mem_normalizer_iff.1 (mul_mem hNa hNc) _).1 (mul_mem hd (inv_mem hb))))
    ((Subgroup.mem_normalizer_iff.1 hNc _).1 (inv_mem hd))

theorem isSolvable_componentBorel
    : Group.IsSolvable (componentBorel K χ i) := by
  set U' := (componentUnipotent K χ i).subgroupOf (componentBorel K χ i)
  have : U'.Normal := componentUnipotent_subgroupOf_normal
  have : Group.IsNilpotent U' := (Group.isNilpotent_congr (Subgroup.subgroupOfEquivOfLe
    componentUnipotent_le_componentBorel)).2 isNilpotent_componentUnipotent
  have : Group.IsSolvable (componentBorel K χ i ⧸ U') := Group.isSolvable_of_comm fun x y => by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have e : ((x * y)⁻¹ * (y * x) : componentBorel K χ i) = y⁻¹ * x⁻¹ * y⁻¹⁻¹ * x⁻¹⁻¹ := by
      group
    rw [e]
    exact commutator_mem_componentUnipotent (inv_mem y.2) (inv_mem x.2)
  exact Group.isSolvable_of_ker_le_range U'.subtype (QuotientGroup.mk' U')
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

theorem isSolvable_componentBorel_subgroupOf :
    Group.IsSolvable ((componentBorel K χ i).subgroupOf (componentRootSpan K χ i)) := by
  have := isSolvable_componentBorel (K := K) (χ := χ) (i := i)
  exact Group.isSolvable_of_surjective
    (f := (Subgroup.subgroupOfEquivOfLe componentBorel_le_componentRootSpan).symm.toMonoidHom)
    (Subgroup.subgroupOfEquivOfLe componentBorel_le_componentRootSpan).symm.surjective

theorem isSolvable_quotient_of_not_le_center
    {M : Subgroup (componentRootSpan K χ i)}
    (hM : M.Normal) (hMZ : ¬ M ≤ Subgroup.center (componentRootSpan K χ i)) :
    Group.IsSolvable (componentRootSpan K χ i ⧸ M) := by
  have htop := sup_componentBorel_eq_top hM hMZ
  have := isSolvable_componentBorel_subgroupOf (K := K) (χ := χ) (i := i)
  have hsurj : Function.Surjective ((QuotientGroup.mk' M).comp
      ((componentBorel K χ i).subgroupOf (componentRootSpan K χ i)).subtype) := by
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective M y
    have hg : g ∈ M ⊔ (componentBorel K χ i).subgroupOf (componentRootSpan K χ i) :=
      htop ▸ Subgroup.mem_top g
    rw [← SetLike.mem_coe, Subgroup.normal_mul, Set.mem_mul] at hg
    obtain ⟨m, hm, b, hb, rfl⟩ := hg
    refine ⟨⟨b, hb⟩, ?_⟩
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply]
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff m).2 hm, one_mul]
  exact Group.isSolvable_of_surjective hsurj

theorem isQuasisimple_componentRootSpan
    (hK : ringChar K ≠ 2)
    {χ : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ} {i : KernelComponent χ}
    (hi : 2 < (componentRoots χ i).ncard) : CFSG.IsQuasisimple (componentRootSpan K χ i) := by
  have hperf : Group.IsPerfect (componentRootSpan K χ i) :=
    Subgroup.isPerfect_iff.2 (odd_sign_kernel_nonrankone_root_component_perfect τ K hK χ i hi).2
  obtain ⟨α, hα⟩ : (componentRoots χ i).Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
  have : Nontrivial (componentRootSpan K χ i) := by
    refine (Subgroup.nontrivial_iff_ne_bot _).2 fun h => ?_
    have h1 : pinnedX τ K α 1 ∈ componentRootSpan K χ i := pinnedX_mem_rootSpan hα 1
    rw [h, Subgroup.mem_bot, ← pinnedX_zero τ K α] at h1
    exact one_ne_zero (pinnedX_injective τ K α h1)
  refine CFSG.LieType.TitsSimplicity.isQuasisimple_of_forall hperf fun M hM => ?_
  by_cases hZ : M ≤ Subgroup.center (componentRootSpan K χ i)
  · exact Or.inl hZ
  · have := hM
    exact Or.inr (CFSG.LieType.TitsSimplicity.eq_top_of_sup_eq_top hperf
      isSolvable_componentBorel_subgroupOf (sup_componentBorel_eq_top hM hZ))

theorem odd_sign_root_component_quasisimple
    (τ : Tag) (K : Type) [Field K]
    (χ : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ) (i : KernelComponent χ) :
    ((componentBorel K χ i).subgroupOf (componentRootSpan K χ i)).normalCore ≤
        Subgroup.center (componentRootSpan K χ i) ∧
    (∀ (M : Subgroup (componentRootSpan K χ i)) [M.Normal],
      ¬ M ≤ Subgroup.center (componentRootSpan K χ i) →
        (M : Set (componentRootSpan K χ i)) *
            ((componentBorel K χ i).subgroupOf (componentRootSpan K χ i) :
              Set (componentRootSpan K χ i)) = Set.univ ∧
        M ⊔ (componentBorel K χ i).subgroupOf (componentRootSpan K χ i) = ⊤ ∧
        Group.IsSolvable (componentRootSpan K χ i ⧸ M)) ∧
    (ringChar K ≠ 2 → 2 < (componentRoots χ i).ncard →
      CFSG.IsQuasisimple (componentRootSpan K χ i)) := by
  refine ⟨normalCore_componentBorel_le_center, fun M hM hMZ => ?_,
    fun hK hi => isQuasisimple_componentRootSpan hK hi⟩
  have htop := sup_componentBorel_eq_top hM hMZ
  refine ⟨?_, htop, isSolvable_quotient_of_not_le_center hM hMZ⟩
  rw [← Subgroup.normal_mul, htop, Subgroup.coe_top]

end CFSG.LieType.Chevalley
