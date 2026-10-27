module

public import CFSG.Fischer.Uniq.F22Uniq
public import CFSG.Fischer.Uniq.LocalHyperoval
public import CFSG.Fischer.Uniq.Triality
public import CFSG.Fischer.Uniq.CompTau

public section

namespace CFSG.Fischer

open CFSG.Blueprint.Fischer SimpleGraph

variable {X Y Z : Type} [Group X] [Group Y] [Group Z] {E : Set X} {F : Set Y} {D : Set Z}

@[expose] def HasFixedPointProperty (hF : Pair Y F) : Prop :=
  ∀ g : Equiv.Perm F, (∀ x, g (g x) = x) →
    (∀ x y : F, (x : Y) * y = y * x ↔ (g x : Y) * g y = g y * g x) →
    (∀ x y : F, g (tauE hF x y) = tauE hF (g x) (g y)) → ∃ x, g x = x

theorem commute_iff_of_compIso {d : Z} (ι : compGraph D d ≃g commGraph F) (a b : compSet D d) :
    ((a : D) : Z) * b = b * a ↔ ((ι a : F) : Y) * ι b = ι b * ι a := by
  by_cases hab : a = b
  · rw [hab]; exact iff_of_true rfl rfl
  · have h1 : ((a : D) : Z) ≠ b := fun h => hab (Subtype.ext (Subtype.ext h))
    have h2 : ((ι a : F) : Y) ≠ ι b := fun h => hab (ι.injective (Subtype.ext h))
    have := ι.map_adj_iff (v := a) (w := b)
    rw [compGraph_adj, commGraph_adj_iff] at this
    constructor
    · intro h; exact (this.2 ⟨h1, h⟩).2
    · intro h; exact (this.1 ⟨h2, h⟩).2

theorem commute_iff_of_graphIso (β : commGraph D ≃g commGraph F) (a b : D) :
    (a : Z) * b = b * a ↔ ((β a : F) : Y) * β b = β b * β a := by
  by_cases hab : a = b
  · rw [hab]; exact iff_of_true rfl rfl
  · have h1 : (a : Z) ≠ b := fun h => hab (Subtype.ext h)
    have h2 : ((β a : F) : Y) ≠ β b := fun h => hab (β.injective (Subtype.ext h))
    have := β.map_adj_iff (v := a) (w := b)
    rw [commGraph_adj_iff, commGraph_adj_iff] at this
    constructor
    · intro h; exact (this.2 ⟨h1, h⟩).2
    · intro h; exact (this.1 ⟨h2, h⟩).2

theorem F22.exists_commute
    (hQ : F22 Z D) : ∃ e f, e ∈ D ∧ f ∈ D ∧ e ≠ f ∧ e * f = f * e := by
  obtain ⟨e₀, he₀⟩ := hQ.1.2.1
  have hd : e₀ ∈ D := by rw [he₀]; exact IsConj.refl e₀
  obtain ⟨L⟩ := F22.nonempty_localPoints hQ hd
  exact ⟨e₀, L.χ.symm 0, hd, (L.χ.symm 0).2.1, (L.χ.symm 0).2.2.1.symm,
    (L.χ.symm 0).2.2.2.symm⟩

theorem F22.ySet_subset_of_connected
    (hPF : PolarFacts) (hF : F22 Y F)
    (hconnF : (commGraph F).Connected) :
    ∀ e x : Y, e ∈ F → x ∈ F → e * x ≠ x * e → ySet F e x ⊆ {e, x, e * x * e} :=
  fun _ _ he hx hex => Pair.ySet_subset_of_polar hPF hF.1
    (fun _ hf => F22.nonempty_localPoints hF hf) he hx hex
    (Pair.muSet_nonempty hF.1 hconnF he hx fun h => hex h.symm)

section Connected

variable (hPF : PolarFacts) (hF : F22 Y F) (hconnF : (commGraph F).Connected)
include hPF hF hconnF

theorem F22.exists_compIso (hQ : F22 Z D) {d : Z} (hd : d ∈ D) :
    ∃ ι : compGraph D d ≃g commGraph F, ∀ e f : compSet D d,
      ((ι ⟨tauE hQ.1 e f, Pair.tauE_mem_compSet hQ.1 hd e.2 f.2⟩ : F) : Y) =
        ((ι e : F) : Y) * (ι f : F) * (ι e : F) := by
  obtain ⟨a, ha⟩ := hF.1.2.1
  have ha' : a ∈ F := by rw [ha]; exact IsConj.refl a
  have huF : compSet F a = Set.univ :=
    compSet_eq_univ fun c hc hcd => Pair.muSet_nonempty hF.1 hconnF ha' hc hcd
  obtain ⟨ι₀⟩ := F22.nonempty_compGraphIso hPF hQ hF hd ha'
  refine ⟨ι₀.trans (compGraphIsoTop huF), fun e f => ?_⟩
  exact Pair.tau_of_compGraphIso hQ.1 hF.1 hd ha' ι₀
    (F22.ySet_subset_of_connected hPF hF hconnF) e f

theorem F22.connected_of_fixedPointProperty (hNFP : HasFixedPointProperty hF.1) (hQ : F22 Z D) :
    (commGraph D).Connected := by
  by_contra hc
  obtain ⟨C₁, C₂, x, f, -, -, -, -, hbij, hinv, -, hfix⟩ :=
    Pair.exists_fixedPointFree_of_not_connected hQ.1 hc (F22.exists_commute hQ)
  obtain ⟨y₀, hy₀⟩ := Quot.exists_rep C₂
  have hcomp : ∀ y : D, y ∈ compSet D (y₀ : Z) ↔ y ∈ C₂.supp := by
    intro y
    rw [Pair.mem_compSet_iff_reachable hQ.1 y₀.2, ConnectedComponent.mem_supp_iff, ← hy₀]
    exact ⟨fun h => ConnectedComponent.sound h.symm, fun h => (ConnectedComponent.exact h).symm⟩
  obtain ⟨ι, hιτ⟩ := F22.exists_compIso hPF hF hconnF hQ y₀.2
  set g : D → D := fun y => tauE hQ.1 x (tauE hQ.1 f y) with hg
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
      ι ⟨tauE hQ.1 e f, Pair.tauE_mem_compSet hQ.1 y₀.2 e.2 f.2⟩ = tauE hF.1 (ι e) (ι f) :=
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
  have htauF : ∀ u v : F, gF (tauE hF.1 u v) = tauE hF.1 (gF u) (gF v) := by
    intro u v
    have h1 : ι.symm (tauE hF.1 u v) = ⟨tauE hQ.1 (ι.symm u) (ι.symm v),
        Pair.tauE_mem_compSet hQ.1 y₀.2 (ι.symm u).2 (ι.symm v).2⟩ := by
      apply ι.injective
      rw [RelIso.apply_symm_apply, hιτ', RelIso.apply_symm_apply, RelIso.apply_symm_apply]
    have h2 : gK ⟨tauE hQ.1 (ι.symm u) (ι.symm v),
        Pair.tauE_mem_compSet hQ.1 y₀.2 (ι.symm u).2 (ι.symm v).2⟩ =
        ⟨tauE hQ.1 (gK (ι.symm u)) (gK (ι.symm v)),
          Pair.tauE_mem_compSet hQ.1 y₀.2 (gK _).2 (gK _).2⟩ :=
      Subtype.ext (Pair.tauE_tauE_tauE hQ.1 x f _ _)
    rw [hgF, hgF, hgF, h1, h2, hιτ']
  obtain ⟨u, hu⟩ := hNFP gF (fun u => by simp [hgF, hgKinv _]) hcommF htauF
  have h1 : gK (ι.symm u) = ι.symm u := by
    apply ι.injective
    rw [← hgF, hu, RelIso.apply_symm_apply]
  exact hfix _ ((hcomp _).1 (ι.symm u).2) (congrArg Subtype.val h1)

theorem F22.exists_graphIso (hNFP : HasFixedPointProperty hF.1) (hQ : F22 Z D) :
    ∃ β : commGraph D ≃g commGraph F, ∀ a b : D, β (tauE hQ.1 a b) = tauE hF.1 (β a) (β b) := by
  have hconnQ := F22.connected_of_fixedPointProperty hPF hF hconnF hNFP hQ
  obtain ⟨q, hq⟩ := hQ.1.2.1
  have hq' : q ∈ D := by rw [hq]; exact IsConj.refl q
  obtain ⟨ι, hιτ⟩ := F22.exists_compIso hPF hF hconnF hQ hq'
  have huQ : compSet D q = Set.univ :=
    compSet_eq_univ fun c hc hcd => Pair.muSet_nonempty hQ.1 hconnQ hq' hc hcd
  refine ⟨(compGraphIsoTop huQ).symm.trans ι, fun a b => Subtype.ext ?_⟩
  exact hιτ ⟨a, by rw [huQ]; trivial⟩ ⟨b, by rw [huQ]; trivial⟩

theorem F23.nonempty_localPoints (hNFP : HasFixedPointProperty hF.1) (hE : F23 X E) {e : X}
    (he : e ∈ E) : Nonempty (LocalPoints (pairModel hF.1) E e) := by
  have hQ := F23_local hE he
  obtain ⟨β, hβτ⟩ := F22.exists_graphIso hPF hF hconnF hNFP hQ
  have hone : (1 : LocalQuotient E e) ∉ LocalImages E e := by
    intro h
    have := hQ.1.2.2.1 1 h
    rw [orderOf_one] at this
    exact absurd this (by norm_num)
  have hinj := Pair.starImage_injective_of_one_notMem hE.1 hone
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
      Pair.starImage_commute_iff hE.1]
  · show β (σ ⟨_, h⟩) = tauE hF.1 (β (σ f)) (β (σ g))
    have : σ ⟨_, h⟩ = tauE hQ.1 (σ f) (σ g) := Subtype.ext (starImage_conj f g h)
    rw [this, hβτ]

end Connected

end CFSG.Fischer
