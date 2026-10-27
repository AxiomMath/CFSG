module

public import CFSG.LieType.Chevalley.TwistedE6EvenCoverTorus

public noncomputable section

namespace CFSG.LieType.Chevalley.TwistedE6Cover

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Chevalley.ExceptionalCover

variable {K : Type} [Field K] (σ : K →+* K)

@[expose] def orbitGroup
    (α : Fin TwistTag.E6.tag.rank → ℤ) : Subgroup (ModGL TwistTag.E6.tag K) :=
  rootSpan TwistTag.E6.tag K (TwistTag.E6.diagramOrbit α : Set (Fin TwistTag.E6.tag.rank → ℤ)) ⊓
    twistedFixedGroup TwistTag.E6 K σ

@[expose] def conjX
    (w : WeylGroup TwistTag.E6.tag) (a : Fin TwistTag.E6.foldedTag.rank)
    (c : orbitField TwistTag.E6 K σ a) : ModGL TwistTag.E6.tag K :=
  canonicalRep (coxeterSystem TwistTag.E6.tag) K w *
    (orbitX TwistTag.E6 K σ a c : ModGL TwistTag.E6.tag K) *
    (canonicalRep (coxeterSystem TwistTag.E6.tag) K w)⁻¹

variable {σ}

theorem conjX_add
    (w : WeylGroup TwistTag.E6.tag) (a : Fin TwistTag.E6.foldedTag.rank)
    (c c' : orbitField TwistTag.E6 K σ a) :
    conjX σ w a (c + c') = conjX σ w a c * conjX σ w a c' := by
  simp only [conjX, orbitX_add, Subgroup.coe_mul]
  group

theorem orbitGroup_congr
    {α β : Fin TwistTag.E6.tag.rank → ℤ}
    (h : TwistTag.E6.diagramOrbit α = TwistTag.E6.diagramOrbit β) :
    orbitGroup σ α = orbitGroup σ β := by
  rw [orbitGroup, orbitGroup, h]

theorem orbitGroup_eq_of_diagramOrbit_eq
    {α : Fin TwistTag.E6.tag.rank → ℤ}
    {w : WeylGroup TwistTag.E6.tag} {a : Fin TwistTag.E6.foldedTag.rank}
    (hO : TwistTag.E6.diagramOrbit α =
      (TwistTag.E6.orbit a).image fun i => w • (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ)) :
    orbitGroup σ α = rootSpan TwistTag.E6.tag K
      ((fun i => w • (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ)) '' ↑(TwistTag.E6.orbit a)) ⊓
        twistedFixedGroup TwistTag.E6 K σ := by
  rw [orbitGroup, hO, Finset.coe_image]

theorem conjX_mem_orbitGroup
    {α : Fin TwistTag.E6.tag.rank → ℤ} {w : WeylGroup TwistTag.E6.tag}
    (hw : w ∈ relWeylTwist TwistTag.E6) {a : Fin TwistTag.E6.foldedTag.rank}
    (hO : TwistTag.E6.diagramOrbit α =
      (TwistTag.E6.orbit a).image fun i => w • (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ))
    (c : orbitField TwistTag.E6 K σ a) : conjX σ w a c ∈ orbitGroup σ α := by
  rw [orbitGroup_eq_of_diagramOrbit_eq hO]
  exact canonicalRep_conj_orbitX_mem TwistTag.E6 σ a hw c

theorem exists_conjX_eq
    {α : Fin TwistTag.E6.tag.rank → ℤ} {w : WeylGroup TwistTag.E6.tag}
    (hw : w ∈ relWeylTwist TwistTag.E6) {a : Fin TwistTag.E6.foldedTag.rank}
    (hO : TwistTag.E6.diagramOrbit α =
      (TwistTag.E6.orbit a).image fun i => w • (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ))
    {x : ModGL TwistTag.E6.tag K} (hx : x ∈ orbitGroup σ α) :
    ∃ c : orbitField TwistTag.E6 K σ a, conjX σ w a c = x := by
  rw [orbitGroup_eq_of_diagramOrbit_eq hO] at hx
  obtain ⟨c, hc⟩ := (orbitConjHom_bijective TwistTag.E6 σ a hw).2 ⟨x, hx⟩
  exact ⟨c.toAdd, congrArg Subtype.val hc⟩

theorem orbitGroup_le_of_subset
    {S : Set (Fin TwistTag.E6.tag.rank → ℤ)}
    (hSρ : ∀ α ∈ S, permLattice TwistTag.E6.perm α ∈ S) {α : Fin TwistTag.E6.tag.rank → ℤ}
    (hα : α ∈ S) :
    orbitGroup σ α ≤ rootSpan TwistTag.E6.tag K S ⊓ twistedFixedGroup TwistTag.E6 K σ :=
  inf_le_inf_right _ (rootSpan_mono (diagramOrbit_subset hSρ hα))

theorem exists_ordering_orbits
    (S : Set (Fin TwistTag.E6.tag.rank → ℤ)) :
    ∃ (k : ℕ) (O : Fin k → Finset (Fin TwistTag.E6.tag.rank → ℤ)), Function.Injective O ∧
      Set.range O = {O' | O' ∈ TwistTag.E6.diagramRootOrbits ∧
        (O' : Set (Fin TwistTag.E6.tag.rank → ℤ)) ⊆ S} := by
  have hfin : {O' | O' ∈ TwistTag.E6.diagramRootOrbits ∧
      (O' : Set (Fin TwistTag.E6.tag.rank → ℤ)) ⊆ S}.Finite :=
    ((finite_setOf_isRoot TwistTag.E6.tag).image TwistTag.E6.diagramOrbit).subset
      fun O' ⟨⟨α, hα, hαO⟩, _⟩ => ⟨α, hα, hαO⟩
  obtain ⟨k, O, hO⟩ := hfin.fin_embedding
  exact ⟨k, O, O.injective, hO⟩

theorem rootSpan_inf_le_closure
    (hσ : Function.Surjective σ)
    {S : Set (Fin TwistTag.E6.tag.rank → ℤ)}
    (hS : ∀ α ∈ S, IsRoot TwistTag.E6.tag α ∧ 0 < height α)
    (hSρ : ∀ α ∈ S, permLattice TwistTag.E6.perm α ∈ S)
    (hclosed : ∀ α ∈ S, ∀ β ∈ S, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot TwistTag.E6.tag (a • α + b • β) →
      a • α + b • β ∈ S) :
    rootSpan TwistTag.E6.tag K S ⊓ twistedFixedGroup TwistTag.E6 K σ ≤
      Subgroup.closure {g | ∃ α ∈ S, g ∈ orbitGroup σ α} := by
  obtain ⟨k, O, hO, hrange⟩ := exists_ordering_orbits S
  have hbij := bijOn_prod_graphFixed (K := K) hσ hS hSρ hclosed O hO hrange
  intro g hg
  obtain ⟨u, -, rfl⟩ := hbij.surjOn hg
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
  have hOj : O j ∈ Set.range O := Set.mem_range_self j
  rw [hrange] at hOj
  obtain ⟨⟨α, -, hα⟩, hsub⟩ := hOj
  refine Subgroup.subset_closure ⟨α, hsub (hα ▸ TwistTag.E6.self_mem_diagramOrbit α), ?_⟩
  rw [orbitGroup, hα]
  exact (u j).2

theorem closure_le_rootSpan_inf
    {S : Set (Fin TwistTag.E6.tag.rank → ℤ)}
    (hSρ : ∀ α ∈ S, permLattice TwistTag.E6.perm α ∈ S) :
    Subgroup.closure {g | ∃ α ∈ S, g ∈ orbitGroup σ α} ≤
      rootSpan TwistTag.E6.tag K S ⊓ twistedFixedGroup TwistTag.E6 K σ :=
  (Subgroup.closure_le _).2 fun _ ⟨_, hα, hg⟩ => orbitGroup_le_of_subset hSρ hα hg

theorem form_eq_zero_of_orbitPairs
    (hσ : Function.Surjective σ)
    {S S' : Set (Fin TwistTag.E6.tag.rank → ℤ)}
    (hS : ∀ α ∈ S, IsRoot TwistTag.E6.tag α ∧ 0 < height α)
    (hSρ : ∀ α ∈ S, permLattice TwistTag.E6.perm α ∈ S)
    (hclosed : ∀ α ∈ S, ∀ β ∈ S, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot TwistTag.E6.tag (a • α + b • β) →
      a • α + b • β ∈ S)
    (hS' : ∀ α ∈ S', IsRoot TwistTag.E6.tag α ∧ 0 < height α)
    (hSρ' : ∀ α ∈ S', permLattice TwistTag.E6.perm α ∈ S')
    (hclosed' : ∀ α ∈ S', ∀ β ∈ S', ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      IsRoot TwistTag.E6.tag (a • α + b • β) → a • α + b • β ∈ S')
    (b : ModGL TwistTag.E6.tag K → ModGL TwistTag.E6.tag K → ZMod 2)
    (hb₁ : ∀ x ∈ rootSpan TwistTag.E6.tag K S ⊓ twistedFixedGroup TwistTag.E6 K σ,
      ∀ x' ∈ rootSpan TwistTag.E6.tag K S ⊓ twistedFixedGroup TwistTag.E6 K σ,
      ∀ y ∈ rootSpan TwistTag.E6.tag K S' ⊓ twistedFixedGroup TwistTag.E6 K σ,
        b (x * x') y = b x y + b x' y)
    (hb₂ : ∀ x ∈ rootSpan TwistTag.E6.tag K S ⊓ twistedFixedGroup TwistTag.E6 K σ,
      ∀ y ∈ rootSpan TwistTag.E6.tag K S' ⊓ twistedFixedGroup TwistTag.E6 K σ,
      ∀ y' ∈ rootSpan TwistTag.E6.tag K S' ⊓ twistedFixedGroup TwistTag.E6 K σ,
        b x (y * y') = b x y + b x y')
    (hpair : ∀ α ∈ S, ∀ β ∈ S', ∀ x ∈ orbitGroup σ α, ∀ y ∈ orbitGroup σ β, b x y = 0) :
    ∀ x ∈ rootSpan TwistTag.E6.tag K S ⊓ twistedFixedGroup TwistTag.E6 K σ,
      ∀ y ∈ rootSpan TwistTag.E6.tag K S' ⊓ twistedFixedGroup TwistTag.E6 K σ, b x y = 0 := by
  have hcl := closure_le_rootSpan_inf (σ := σ) hSρ
  have hcl' := closure_le_rootSpan_inf (σ := σ) hSρ'
  have hleft : ∀ α ∈ S, ∀ x ∈ orbitGroup σ α,
      ∀ y ∈ rootSpan TwistTag.E6.tag K S' ⊓ twistedFixedGroup TwistTag.E6 K σ, b x y = 0 := by
    intro α hα x hx y hy
    have hxS := orbitGroup_le_of_subset hSρ hα hx
    refine eq_zero_of_closure (b x) (fun y hy y' hy' => hb₂ x hxS y (hcl' hy) y' (hcl' hy'))
      ?_ y (rootSpan_inf_le_closure hσ hS' hSρ' hclosed' hy)
    rintro _ ⟨β, hβ, hy⟩
    exact hpair α hα β hβ x hx _ hy
  intro x hx y hy
  refine eq_zero_of_closure (fun x => b x y) (fun x hx x' hx' => hb₁ x (hcl hx) x' (hcl hx') y hy)
    ?_ x (rootSpan_inf_le_closure hσ hS hSρ hclosed hx)
  rintro _ ⟨α, hα, hx⟩
  exact hleft α hα _ hx y hy

variable [Finite K] [CharP K 2]

theorem form_conjX_eq_zero
    {f : ℕ} (hf : 2 ≤ f) (hk : Nat.card (fixField σ) = 2 ^ f)
    {w w' : WeylGroup TwistTag.E6.tag} {a a' : Fin TwistTag.E6.foldedTag.rank}
    (harith : ∀ i j : ℕ, i < f → j < f → ¬ ∀ l, (2 ^ f - 1 : ℤ) ∣
      2 ^ i * foldCoord (w • Pi.single (TwistTag.E6.orbitMin a) 1) l +
        2 ^ j * foldCoord (w' • Pi.single (TwistTag.E6.orbitMin a') 1) l)
    (F : orbitField TwistTag.E6 K σ a → orbitField TwistTag.E6 K σ a' → ZMod 2)
    (hF₁ : ∀ c₁ c₂ d, F (c₁ + c₂) d = F c₁ d + F c₂ d)
    (hF₂ : ∀ c d₁ d₂, F c (d₁ + d₂) = F c d₁ + F c d₂)
    (hFT : ∀ t c d, F (Subfield.inclusion (fixField_le_orbitField a)
        (foldChar σ (w • Pi.single (TwistTag.E6.orbitMin a) 1) t : fixField σ) * c)
      (Subfield.inclusion (fixField_le_orbitField a')
        (foldChar σ (w' • Pi.single (TwistTag.E6.orbitMin a') 1) t : fixField σ) * d) = F c d) :
    ∀ c d, F c d = 0 := by
  intro c₀ d₀
  set ι := Subfield.inclusion (fixField_le_orbitField (σ := σ) a)
  set ι' := Subfield.inclusion (fixField_le_orbitField (σ := σ) a')
  let G : fixField σ → fixField σ → ZMod 2 := fun x y => F (ι x * c₀) (ι' y * d₀)
  have hG := form_eq_zero_of_chars (by omega) hk
    (foldChar σ (w • Pi.single (TwistTag.E6.orbitMin a) 1))
    (foldChar σ (w' • Pi.single (TwistTag.E6.orbitMin a') 1))
    (fun i j hi hj => exists_foldChar_pow_mul_ne_one hk harith i j hi hj) G
    (fun x₁ x₂ y => by simp only [G, map_add, add_mul, hF₁])
    (fun x y₁ y₂ => by simp only [G, map_add, add_mul, hF₂])
    (fun t x y => by
      simp only [G, map_mul, mul_assoc]
      exact hFT t _ _)
  have h := hG 1 1
  simp only [G, map_one, one_mul] at h
  exact h

theorem form_orbit_eq_zero
    {f : ℕ} (hf : 2 ≤ f) (hk : Nat.card (fixField σ) = 2 ^ f)
    {α β : Fin TwistTag.E6.tag.rank → ℤ} (hα : IsRoot TwistTag.E6.tag α) (hαp : 0 < height α)
    (hβ : IsRoot TwistTag.E6.tag β) (hβp : 0 < height β)
    (hne : β ∉ TwistTag.E6.diagramOrbit α)
    (b : ModGL TwistTag.E6.tag K → ModGL TwistTag.E6.tag K → ZMod 2)
    (hb₁ : ∀ x ∈ orbitGroup σ α, ∀ x' ∈ orbitGroup σ α, ∀ y ∈ orbitGroup σ β,
      b (x * x') y = b x y + b x' y)
    (hb₂ : ∀ x ∈ orbitGroup σ α, ∀ y ∈ orbitGroup σ β, ∀ y' ∈ orbitGroup σ β,
      b x (y * y') = b x y + b x y')
    (hbT : ∀ t, ∀ x ∈ orbitGroup σ α, ∀ y ∈ orbitGroup σ β,
      b (fixedTorus σ t * x * (fixedTorus σ t)⁻¹) (fixedTorus σ t * y * (fixedTorus σ t)⁻¹) =
        b x y) :
    ∀ x ∈ orbitGroup σ α, ∀ y ∈ orbitGroup σ β, b x y = 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨w, hw, a, hO⟩ := TwistTag.E6.exists_diagramOrbit_eq hα
  obtain ⟨w', hw', a', hO'⟩ := TwistTag.E6.exists_diagramOrbit_eq hβ
  set α₀ : Fin TwistTag.E6.tag.rank → ℤ := w • Pi.single (TwistTag.E6.orbitMin a) 1
  set β₀ : Fin TwistTag.E6.tag.rank → ℤ := w' • Pi.single (TwistTag.E6.orbitMin a') 1
  have hα₀ : α₀ ∈ TwistTag.E6.diagramOrbit α := by
    rw [hO]
    exact Finset.mem_image_of_mem _ (TwistTag.E6.orbitMin_mem a)
  have hβ₀ : β₀ ∈ TwistTag.E6.diagramOrbit β := by
    rw [hO']
    exact Finset.mem_image_of_mem _ (TwistTag.E6.orbitMin_mem a')
  have harith : ∀ i j : ℕ, i < f → j < f → ¬ ∀ l, (2 ^ f - 1 : ℤ) ∣
      2 ^ i * foldCoord α₀ l + 2 ^ j * foldCoord β₀ l := by
    refine fold_pair_not_dvd hf (TwistTag.E6.isRoot_of_mem_diagramOrbit hα hα₀)
      (by rw [TwistTag.E6.height_of_mem_diagramOrbit hα₀]; exact hαp)
      (TwistTag.E6.isRoot_of_mem_diagramOrbit hβ hβ₀)
      (by rw [TwistTag.E6.height_of_mem_diagramOrbit hβ₀]; exact hβp) fun hmem => hne ?_
    have e1 := TwistTag.E6.diagramOrbit_eq_of_mem hmem
    have e2 := TwistTag.E6.diagramOrbit_eq_of_mem hα₀
    have e3 := TwistTag.E6.diagramOrbit_eq_of_mem hβ₀
    rw [← e2, ← e1, e3]
    exact TwistTag.E6.self_mem_diagramOrbit β
  have hF := form_conjX_eq_zero hf hk harith
    (fun c d => b (conjX σ w a c) (conjX σ w' a' d))
    (fun c₁ c₂ d => by
      rw [conjX_add]
      exact hb₁ _ (conjX_mem_orbitGroup hw hO c₁) _ (conjX_mem_orbitGroup hw hO c₂) _
        (conjX_mem_orbitGroup hw' hO' d))
    (fun c d₁ d₂ => by
      rw [conjX_add]
      exact hb₂ _ (conjX_mem_orbitGroup hw hO c) _ (conjX_mem_orbitGroup hw' hO' d₁) _
        (conjX_mem_orbitGroup hw' hO' d₂))
    (fun t c d => by
      rw [conjX, conjX, ← fixedTorus_conj_orbitConj h2 hw, ← fixedTorus_conj_orbitConj h2 hw']
      exact hbT t _ (conjX_mem_orbitGroup hw hO c) _ (conjX_mem_orbitGroup hw' hO' d))
  intro x hx y hy
  obtain ⟨c, rfl⟩ := exists_conjX_eq hw hO hx
  obtain ⟨d, rfl⟩ := exists_conjX_eq hw' hO' hy
  exact hF c d

end CFSG.LieType.Chevalley.TwistedE6Cover
