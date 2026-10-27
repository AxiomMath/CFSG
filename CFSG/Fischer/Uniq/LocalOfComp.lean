module

public import CFSG.Fischer.Uniq.F23Local

public section

namespace CFSG.Fischer

open CFSG.Blueprint.Fischer SimpleGraph

variable {X Y Z : Type} [Group X] [Group Y] [Group Z] {E : Set X} {F : Set Y} {D : Set Z}

section Generic

variable (hF : Pair Y F) (hQ : Pair Z D) (hcm : ∃ e f, e ∈ D ∧ f ∈ D ∧ e ≠ f ∧ e * f = f * e)
  (hiso : ∀ d (hd : d ∈ D), ∃ ι : compGraph D d ≃g commGraph F, ∀ e f : compSet D d,
    ((ι ⟨tauE hQ e f, Pair.tauE_mem_compSet hQ hd e.2 f.2⟩ : F) : Y) =
      ((ι e : F) : Y) * (ι f : F) * (ι e : F))
include hF hQ hcm hiso

theorem connected_of_compIso (hNFP : HasFixedPointProperty hF) : (commGraph D).Connected := by
  by_contra hc
  obtain ⟨C₁, C₂, x, f, -, -, -, -, hbij, hinv, -, hfix⟩ :=
    Pair.exists_fixedPointFree_of_not_connected hQ hc hcm
  obtain ⟨y₀, hy₀⟩ := Quot.exists_rep C₂
  have hcomp : ∀ y : D, y ∈ compSet D (y₀ : Z) ↔ y ∈ C₂.supp := by
    intro y
    rw [Pair.mem_compSet_iff_reachable hQ y₀.2, ConnectedComponent.mem_supp_iff, ← hy₀]
    exact ⟨fun h => ConnectedComponent.sound h.symm, fun h => (ConnectedComponent.exact h).symm⟩
  obtain ⟨ι, hιτ⟩ := hiso _ y₀.2
  set g : D → D := fun y => tauE hQ x (tauE hQ f y) with hg
  have hgK : ∀ y : compSet D (y₀ : Z), g y ∈ compSet D (y₀ : Z) := fun y =>
    (hcomp _).2 (hbij.mapsTo ((hcomp _).1 y.2))
  let gK : compSet D (y₀ : Z) → compSet D (y₀ : Z) := fun y => ⟨g y, hgK y⟩
  have hgKinv : Function.Involutive gK := fun y => Subtype.ext (hinv y)
  let gF : Equiv.Perm F := ι.symm.toEquiv.trans ((hgKinv.toPerm gK).trans ι.toEquiv)
  have hgF : ∀ u, gF u = ι (gK (ι.symm u)) := fun u => rfl
  have hgconj : ∀ y : D, (g y : Z) = (x : Z) * f * y * ((x : Z) * f)⁻¹ := by
    intro y
    rw [hg]
    simp only [Pair.tauE_tauE_eq_conjPerm, Pair.conjPerm_apply]
  have hιτ' : ∀ e f : compSet D (y₀ : Z),
      ι ⟨tauE hQ e f, Pair.tauE_mem_compSet hQ y₀.2 e.2 f.2⟩ = tauE hF (ι e) (ι f) :=
    fun e f => Subtype.ext (hιτ e f)
  have hcommF : ∀ u v : F, (u : Y) * v = v * u ↔ (gF u : Y) * gF v = gF v * gF u := by
    intro u v
    set a := ι.symm u
    set b := ι.symm v
    have e1 : (u : Y) * v = v * u ↔ ((a : D) : Z) * b = b * a := by
      have := commute_iff_of_compIso ι a b
      rw [RelIso.apply_symm_apply, RelIso.apply_symm_apply] at this
      exact this.symm
    have e2 : ((a : D) : Z) * b = b * a ↔
        ((gK a : D) : Z) * (gK b : D) = (gK b : D) * (gK a : D) := by
      show _ ↔ (g a : Z) * g b = g b * g a
      rw [hgconj, hgconj, conj_commute_iff]
    rw [hgF, hgF, e1, e2]
    exact commute_iff_of_compIso ι (gK a) (gK b)
  have htauF : ∀ u v : F, gF (tauE hF u v) = tauE hF (gF u) (gF v) := by
    intro u v
    have h1 : ι.symm (tauE hF u v) = ⟨tauE hQ (ι.symm u) (ι.symm v),
        Pair.tauE_mem_compSet hQ y₀.2 (ι.symm u).2 (ι.symm v).2⟩ := by
      apply ι.injective
      rw [RelIso.apply_symm_apply, hιτ', RelIso.apply_symm_apply, RelIso.apply_symm_apply]
    have h2 : gK ⟨tauE hQ (ι.symm u) (ι.symm v),
        Pair.tauE_mem_compSet hQ y₀.2 (ι.symm u).2 (ι.symm v).2⟩ =
        ⟨tauE hQ (gK (ι.symm u)) (gK (ι.symm v)),
          Pair.tauE_mem_compSet hQ y₀.2 (gK _).2 (gK _).2⟩ :=
      Subtype.ext (Pair.tauE_tauE_tauE hQ x f _ _)
    rw [hgF, hgF, hgF, h1, h2, hιτ']
  obtain ⟨u, hu⟩ := hNFP gF (fun u => by simp [hgF, hgKinv _]) hcommF htauF
  have h1 : gK (ι.symm u) = ι.symm u := by
    apply ι.injective
    rw [← hgF, hu, RelIso.apply_symm_apply]
  exact hfix _ ((hcomp _).1 (ι.symm u).2) (congrArg Subtype.val h1)

theorem exists_graphIso_of_compIso (hNFP : HasFixedPointProperty hF) :
    ∃ β : commGraph D ≃g commGraph F, ∀ a b : D, β (tauE hQ a b) = tauE hF (β a) (β b) := by
  have hconnQ := connected_of_compIso hF hQ hcm hiso hNFP
  obtain ⟨q, hq⟩ := hQ.2.1
  have hq' : q ∈ D := by rw [hq]; exact IsConj.refl q
  obtain ⟨ι, hιτ⟩ := hiso q hq'
  have huQ : compSet D q = Set.univ :=
    compSet_eq_univ fun c hc hcd => Pair.muSet_nonempty hQ hconnQ hq' hc hcd
  refine ⟨(compGraphIsoTop huQ).symm.trans ι, fun a b => Subtype.ext ?_⟩
  exact hιτ ⟨a, by rw [huQ]; trivial⟩ ⟨b, by rw [huQ]; trivial⟩

end Generic

theorem nonempty_localPoints_of_compIso (hF : Pair Y F) (hNFP : HasFixedPointProperty hF)
    (hE : Pair X E) {e : X} (hQ : Pair (LocalQuotient E e) (LocalImages E e))
    (hcm : ∃ a b, a ∈ LocalImages E e ∧ b ∈ LocalImages E e ∧ a ≠ b ∧ a * b = b * a)
    (hiso : ∀ d (hd : d ∈ LocalImages E e), ∃ ι : compGraph (LocalImages E e) d ≃g commGraph F,
      ∀ a b : compSet (LocalImages E e) d,
        ((ι ⟨tauE hQ a b, Pair.tauE_mem_compSet hQ hd a.2 b.2⟩ : F) : Y) =
          ((ι a : F) : Y) * (ι b : F) * (ι a : F)) :
    Nonempty (LocalPoints (pairModel hF) E e) := by
  obtain ⟨β, hβτ⟩ := exists_graphIso_of_compIso hF hQ hcm hiso hNFP
  have hone : (1 : LocalQuotient E e) ∉ LocalImages E e := by
    intro h
    have := hQ.2.2.1 1 h
    rw [orderOf_one] at this
    exact absurd this (by norm_num)
  have hinj := Pair.starImage_injective_of_one_notMem hE hone
  have hmem : ∀ f : LocalClass E e, starImage E e f ∈ LocalImages E e := fun f => by
    rw [← range_starImage]; exact ⟨f, rfl⟩
  let σ : LocalClass E e ≃ LocalImages E e := Equiv.ofBijective
    (fun f => ⟨starImage E e f, hmem f⟩)
    ⟨fun f g h => hinj (congrArg Subtype.val h), fun q => by
      have hq : (q : LocalQuotient E e) ∈ Set.range (starImage E e) := by
        rw [range_starImage]; exact q.2
      obtain ⟨f, hf⟩ := hq
      exact ⟨f, Subtype.ext hf⟩⟩
  have hσ : ∀ f, (σ f : LocalQuotient E e) = starImage E e f := fun f => rfl
  refine ⟨⟨σ.trans β.toEquiv, fun f g => ?_, fun f g h => ?_⟩⟩
  · show (f : X) * g = g * f ↔ ((β (σ f) : F) : Y) * β (σ g) = β (σ g) * β (σ f)
    rw [← commute_iff_of_graphIso β (σ f) (σ g), hσ, hσ, ← commute_iff_eq, ← commute_iff_eq,
      Pair.starImage_commute_iff hE]
  · show β (σ ⟨_, h⟩) = tauE hF (β (σ f)) (β (σ g))
    have : σ ⟨_, h⟩ = tauE hQ (σ f) (σ g) := Subtype.ext (starImage_conj f g h)
    rw [this, hβτ]

end CFSG.Fischer
