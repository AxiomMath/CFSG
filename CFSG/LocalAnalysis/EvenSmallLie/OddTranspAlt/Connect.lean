module

public import CFSG.LocalAnalysis.EvenSmallLie.OddTranspAlt.Setup
public import CFSG.LocalAnalysis.EvenSmallLie.OddTranspAlt.PermSwap
public import CFSG.LocalAnalysis.EvenSmallLie.OddTranspAlt.PermAut
public import CFSG.LocalAnalysis.EvenSmallLie.ThreeTransposition.Section24Connected

public section

namespace CFSG.EvenSmallLie.OddTranspAlt

open Equiv Equiv.Perm CFSG.Fischer CFSG.EvenSmallLie.ThreeTransposition

private theorem exists_swap_commute_two {m : ℕ} (hm : 6 ≤ m) {σ σ' : Perm (Fin m)}
    (hσ : σ.IsSwap) (hσ' : σ'.IsSwap) :
    ∃ τ : Perm (Fin m), τ.IsSwap ∧ τ * σ = σ * τ ∧ τ * σ' = σ' * τ := by
  classical
  obtain ⟨a, b, -, rfl⟩ := hσ
  obtain ⟨c, d, -, rfl⟩ := hσ'
  have hcard : 1 < (({a, b, c, d} : Finset (Fin m))ᶜ).card := by
    rw [Finset.card_compl, Fintype.card_fin]
    have := Finset.card_le_four (a := a) (b := b) (c := c) (d := d)
    omega
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.1 hcard
  simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at hp hq
  have hdisj : ∀ {u v : Fin m}, p ≠ u → p ≠ v → q ≠ u → q ≠ v →
      (swap p q).Disjoint (swap u v) := by
    intro u v hpu hpv hqu hqv x
    by_cases hxp : x = p
    · subst hxp
      exact Or.inr (swap_apply_of_ne_of_ne hpu hpv)
    · by_cases hxq : x = q
      · subst hxq
        exact Or.inr (swap_apply_of_ne_of_ne hqu hqv)
      · exact Or.inl (swap_apply_of_ne_of_ne hxp hxq)
  exact ⟨swap p q, ⟨p, q, hpq, rfl⟩, (hdisj hp.1 hp.2.1 hq.1 hq.2.1).commute.eq,
    (hdisj hp.2.2.1 hp.2.2.2 hq.2.2.1 hq.2.2.2).commute.eq⟩

private def sw {m : ℕ} (hm : 8 ≤ m) (i : Fin 4) : Perm (Fin m) :=
  swap ⟨2 * i, by have := i.isLt; omega⟩ ⟨2 * i + 1, by have := i.isLt; omega⟩

section Sw

variable {m : ℕ} (hm : 8 ≤ m)

private theorem sw_isSwap (i : Fin 4) : (sw hm i).IsSwap :=
  ⟨_, _, by rw [Ne, Fin.mk.injEq]; omega, rfl⟩

private theorem sw_mul_self (i : Fin 4) : sw hm i * sw hm i = 1 :=
  swap_mul_self _ _

private theorem sw_apply_of_ne {i j : Fin 4} (hij : i ≠ j) (x : Fin m)
    (hx : (x : ℕ) = 2 * i ∨ (x : ℕ) = 2 * i + 1) : sw hm j x = x := by
  have hij' : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
  apply swap_apply_of_ne_of_ne <;> rw [Ne, Fin.ext_iff] <;> simp only <;> omega

private theorem sw_disjoint {i j : Fin 4} (hij : i ≠ j) : (sw hm i).Disjoint (sw hm j) := by
  intro x
  by_cases hx : (x : ℕ) = 2 * i ∨ (x : ℕ) = 2 * i + 1
  · exact Or.inr (sw_apply_of_ne hm hij x hx)
  · left
    apply swap_apply_of_ne_of_ne <;> rw [Ne, Fin.ext_iff] <;> simp only <;> omega

private theorem sw_commute (i j : Fin 4) : sw hm i * sw hm j = sw hm j * sw hm i := by
  by_cases hij : i = j
  · rw [hij]
  · exact (sw_disjoint hm hij).commute.eq

private theorem sw_injective : Function.Injective (sw hm) := by
  intro i j hij
  by_contra hne
  have h1 : sw hm i ⟨2 * i, by have := i.isLt; omega⟩ = ⟨2 * i + 1, by have := i.isLt; omega⟩ :=
    swap_apply_left _ _
  rw [hij, sw_apply_of_ne hm hne _ (Or.inl rfl)] at h1
  rw [Fin.mk.injEq] at h1
  omega

end Sw

private theorem exists_ne_three {α β : Type*} [Fintype α] {f : α → β}
    (hf : Function.Injective f) (hα : 4 ≤ Fintype.card α) (a b c : β) :
    ∃ i, f i ≠ a ∧ f i ≠ b ∧ f i ≠ c := by
  classical
  by_contra h
  push Not at h
  have hmaps : Set.MapsTo f (Finset.univ : Finset α) ({a, b, c} : Finset β) := by
    intro i _
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    by_cases ha : f i = a
    · exact Or.inl ha
    · by_cases hb : f i = b
      · exact Or.inr (Or.inl hb)
      · exact Or.inr (Or.inr (h i ha hb))
  have h4 := Finset.card_le_card_of_injOn f hmaps hf.injOn
  have h3 := Finset.card_le_three (a := a) (b := b) (c := c)
  rw [Finset.card_univ] at h4
  omega

private theorem mem_of_reachable {X : Type} [Group X] {E P : Set X}
    (hP : ∀ u v : E, (commGraph E).Adj u v → (u : X) ∈ P → (v : X) ∈ P) {u v : E}
    (h : (commGraph E).Reachable u v) (hu : (u : X) ∈ P) : (v : X) ∈ P := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact hu
  | cons hadj _ ih => exact ih (hP _ _ hadj hu)

section Group

variable {G : Type} [Group G] {t : G} {m : ℕ}

private theorem orderOf_of_mem_cls {x : G} (hx : x ∈ cls t) : orderOf x = orderOf t := by
  obtain ⟨e, rfl⟩ := hx
  exact (SemiconjBy.orderOf_eq e (by rw [SemiconjBy]; group)).symm

private theorem compSet_eq_swaps (hm : 6 ≤ m) (ψ : Perm (Fin m) →* G)
    (hsw : ∀ σ : Perm (Fin m), σ.IsSwap → ψ σ ∈ cls t)
    (hnb : ∀ σ : Perm (Fin m), σ.IsSwap → ∀ e ∈ cls t, e ≠ ψ σ → ψ σ * e = e * ψ σ →
      ∃ τ : Perm (Fin m), τ.IsSwap ∧ ψ τ = e) {σ₀ : Perm (Fin m)} (hσ₀ : σ₀.IsSwap) :
    compSet (cls t) (ψ σ₀) = {x | ∃ σ : Perm (Fin m), σ.IsSwap ∧ ψ σ = x} := by
  ext y
  constructor
  · rintro ⟨_, _, hr⟩
    refine mem_of_reachable (P := {x | ∃ σ : Perm (Fin m), σ.IsSwap ∧ ψ σ = x}) ?_ hr
      ⟨σ₀, hσ₀, rfl⟩
    rintro ⟨_, _⟩ ⟨v, hv⟩ huv ⟨σ, hσ, rfl⟩
    rw [commGraph_adj_iff] at huv
    exact hnb σ hσ v hv (Ne.symm huv.1) huv.2
  · rintro ⟨σ, hσ, rfl⟩
    obtain ⟨τ, hτ, h₀, h₁⟩ := exists_swap_commute_two hm hσ₀ hσ
    have e₀ : ψ σ₀ * ψ τ = ψ τ * ψ σ₀ := by rw [← map_mul, ← map_mul, h₀]
    have e₁ : ψ τ * ψ σ = ψ σ * ψ τ := by rw [← map_mul, ← map_mul, h₁]
    exact ⟨hsw σ₀ hσ₀, hsw σ hσ,
      (commGraph_reachable_of_commute (a := ⟨ψ σ₀, hsw σ₀ hσ₀⟩) (b := ⟨ψ τ, hsw τ hτ⟩) e₀).trans
        (commGraph_reachable_of_commute (a := ⟨ψ τ, hsw τ hτ⟩) (b := ⟨ψ σ, hsw σ hσ⟩) e₁)⟩

private theorem exists_swap_conj_eq (hm : 7 ≤ m) (ψ : Perm (Fin m) →* G)
    (hψ : Function.Injective ψ) {x : G} (hx : x * x = 1)
    (hxR : ∀ σ : Perm (Fin m), σ.IsSwap → ∃ τ : Perm (Fin m), ψ τ = x * ψ σ * x⁻¹) :
    ∃ σ : Perm (Fin m), σ.IsSwap ∧ x * ψ σ * x⁻¹ = ψ σ := by
  have hall : ∀ π : Perm (Fin m), ∃ τ : Perm (Fin m), ψ τ = x * ψ π * x⁻¹ := by
    intro π
    have hπ : π ∈ Subgroup.closure {σ : Perm (Fin m) | σ.IsSwap} := by
      rw [closure_isSwap]
      exact Subgroup.mem_top π
    induction hπ using Subgroup.closure_induction with
    | mem σ hσ => exact hxR σ hσ
    | one => exact ⟨1, by simp⟩
    | mul a b _ _ iha ihb =>
      obtain ⟨τa, ha⟩ := iha
      obtain ⟨τb, hb⟩ := ihb
      exact ⟨τa * τb, by rw [map_mul, ha, hb, map_mul]; group⟩
    | inv a _ ih =>
      obtain ⟨τ, h⟩ := ih
      exact ⟨τ⁻¹, by rw [map_inv, h, map_inv]; group⟩
  choose α hα using hall
  have hαα : ∀ π, α (α π) = π := by
    intro π
    apply hψ
    rw [hα, hα]
    calc x * (x * ψ π * x⁻¹) * x⁻¹ = (x * x) * ψ π * (x * x)⁻¹ := by group
      _ = ψ π := by rw [hx]; group
  have hαmul : ∀ π₁ π₂, α (π₁ * π₂) = α π₁ * α π₂ := by
    intro π₁ π₂
    apply hψ
    simp only [map_mul, hα]
    group
  let αE : MulAut (Perm (Fin m)) :=
    { toFun := α, invFun := α, left_inv := hαα, right_inv := hαα, map_mul' := hαmul }
  obtain ⟨π, hπ⟩ := perm_aut_inner hm αE
  have hπα : ∀ σ, α σ = π * σ * π⁻¹ := hπ
  have hππ : π * π = 1 := by
    apply perm_center_trivial (by omega) (π * π)
    intro σ
    have h := hαα σ
    rw [hπα, hπα] at h
    calc π * π * σ = π * (π * σ * π⁻¹) * π⁻¹ * (π * π) := by group
      _ = σ * (π * π) := by rw [h]
  obtain ⟨σ, hσ, hπσ⟩ := exists_swap_commute_of_sq_eq_one (by omega) π hππ
  refine ⟨σ, hσ, ?_⟩
  rw [← hα, hπα, hπσ, mul_inv_cancel_right]

private theorem not_mem_closure_diff (ψ : Perm (Fin m) →* G) (hψ : Function.Injective ψ)
    {S : Set G} (hS : ∀ x ∈ S, ∃ σ : Perm (Fin m), σ.IsSwap ∧ ψ σ = x)
    (hSc : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) {w : G} (hw : w ∈ S) :
    w ∉ Subgroup.closure (S \ {w}) := by
  obtain ⟨σ, hσ, rfl⟩ := hS w hw
  obtain ⟨p, q, hpq, hσpq⟩ := hσ
  have hle : Subgroup.closure (S \ {ψ σ}) ≤ (MulAction.stabilizer (Perm (Fin m)) p).map ψ := by
    rw [Subgroup.closure_le]
    rintro x ⟨hxS, hxw⟩
    obtain ⟨τ, hτ, rfl⟩ := hS x hxS
    refine Subgroup.mem_map.2 ⟨τ, ?_, rfl⟩
    rw [MulAction.mem_stabilizer_iff, Perm.smul_def]
    have hne : τ ≠ σ := fun h => hxw (by rw [h]; exact Set.mem_singleton _)
    have hc : τ * σ = σ * τ := hψ (by rw [map_mul, map_mul]; exact hSc _ hxS _ hw)
    rcases (isSwap_commute_iff hτ ⟨p, q, hpq, hσpq⟩).1 hc with h | h
    · exact absurd h hne
    · rcases h p with h | h
      · exact h
      · rw [hσpq, swap_apply_left] at h
        exact absurd h.symm hpq
  intro hmem
  obtain ⟨τ, hτ, hτσ⟩ := Subgroup.mem_map.1 (hle hmem)
  rw [hψ hτσ, MulAction.mem_stabilizer_iff, Perm.smul_def, hσpq, swap_apply_left] at hτ
  exact hpq hτ.symm

private theorem h1_of (ψ : Perm (Fin m) →* G) (hψ : Function.Injective ψ)
    (hnb : ∀ σ : Perm (Fin m), σ.IsSwap → ∀ e ∈ cls t, e ≠ ψ σ → ψ σ * e = e * ψ σ →
      ∃ τ : Perm (Fin m), τ.IsSwap ∧ ψ τ = e)
    {S : Set G} (hS : S ⊆ cls t) {σ₁ σ₂ : Perm (Fin m)} (h₁ : σ₁.IsSwap) (h₂ : σ₂.IsSwap)
    (hne : σ₁ ≠ σ₂) (hc : σ₁ * σ₂ = σ₂ * σ₁) (hS₁ : ψ σ₁ ∈ S) (hS₂ : ψ σ₂ ∈ S) :
    {x | x ∈ Subgroup.closure S ∧ x ≠ 1} ≠ S := by
  intro heq
  have hsign : sign (σ₁ * σ₂) = 1 := by
    rw [Perm.sign_mul, h₁.sign_eq, h₂.sign_eq]
    decide
  have hx1 : ψ (σ₁ * σ₂) ≠ 1 := by
    intro h
    have h' : σ₁ * σ₂ = 1 := hψ (h.trans (map_one ψ).symm)
    obtain ⟨p, q, -, rfl⟩ := h₁
    exact hne (by rw [← swap_inv, ← eq_inv_of_mul_eq_one_right h'])
  have hmem : ψ (σ₁ * σ₂) ∈ S := by
    rw [← heq]
    refine ⟨?_, hx1⟩
    rw [map_mul]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure hS₁) (Subgroup.subset_closure hS₂)
  obtain ⟨τ, hτ, hτe⟩ := hnb σ₁ h₁ _ (hS hmem) (fun h => by
    have h' := congrArg sign (hψ h)
    rw [hsign, h₁.sign_eq] at h'
    exact absurd h' (by decide)) (by rw [← map_mul, ← map_mul, mul_assoc σ₁ σ₂ σ₁, ← hc])
  have h' := congrArg sign (hψ hτe)
  rw [hsign, hτ.sign_eq] at h'
  exact absurd h' (by decide)

private theorem h2_of {S : Set G} (hS2 : ∀ x ∈ S, x * x = 1)
    (hSc : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x)
    (hS4 : ∀ a b c : G, ∃ w ∈ S, w ≠ a ∧ w ≠ b ∧ w ≠ c)
    (hInd : ∀ w ∈ S, w ∉ Subgroup.closure (S \ {w})) :
    ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ¬ ∀ e ∈ S, ∀ f ∈ S,
      ∃ g ∈ Subgroup.normalizer S ⊓ Subgroup.centralizer {a * b * c}, g * e * g⁻¹ = f := by
  intro a ha b hb c hc htr
  have hfix : ∀ d ∈ S, a * b * c = d → False := by
    intro d hd hd'
    obtain ⟨w, hw, hwd, -, -⟩ := hS4 d d d
    obtain ⟨g, hg, hgw⟩ := htr d hd w hw
    have hgc : g * d = d * g := by
      have := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hg).2
      rw [hd'] at this
      exact this
    apply hwd
    rw [← hgw, hgc, mul_inv_cancel_right]
  by_cases hab : a = b
  · exact hfix c hc (by rw [← hab, hS2 a ha, one_mul])
  by_cases hac : a = c
  · exact hfix b hb (by rw [← hac, hSc a ha b hb, mul_assoc, hS2 a ha, mul_one])
  by_cases hbc : b = c
  · exact hfix a ha (by rw [← hbc, mul_assoc, hS2 b hb, mul_one])
  obtain ⟨w, hw, hwa, hwb, hwc⟩ := hS4 a b c
  obtain ⟨g, hg, hgw⟩ := htr a ha w hw
  obtain ⟨hgN, hgC⟩ := Subgroup.mem_inf.1 hg
  have hN := Subgroup.mem_set_normalizer_iff.1 hgN
  have hb' : g * b * g⁻¹ ∈ S := (hN b).1 hb
  have hc' : g * c * g⁻¹ ∈ S := (hN c).1 hc
  have hb'w : g * b * g⁻¹ ≠ w := fun h => hab (conj_injective (h.trans hgw.symm)).symm
  have hc'w : g * c * g⁻¹ ≠ w := fun h => hac (conj_injective (h.trans hgw.symm)).symm
  have hgabc : g * (a * b * c) * g⁻¹ = a * b * c := by
    rw [Subgroup.mem_centralizer_singleton_iff.1 hgC, mul_inv_cancel_right]
  have e1 : w * (g * b * g⁻¹) * (g * c * g⁻¹) = a * b * c := by
    rw [← hgw, ← hgabc]
    group
  have hb'i : (g * b * g⁻¹)⁻¹ = g * b * g⁻¹ := inv_eq_of_mul_eq_one_right (hS2 _ hb')
  have hc'i : (g * c * g⁻¹)⁻¹ = g * c * g⁻¹ := inv_eq_of_mul_eq_one_right (hS2 _ hc')
  have hweq : w = a * b * c * (g * c * g⁻¹) * (g * b * g⁻¹) := by
    calc w = w * (g * b * g⁻¹) * (g * c * g⁻¹) * (g * c * g⁻¹)⁻¹ * (g * b * g⁻¹)⁻¹ := by group
      _ = a * b * c * (g * c * g⁻¹) * (g * b * g⁻¹) := by rw [e1, hb'i, hc'i]
  have hmem : ∀ x ∈ S, x ≠ w → x ∈ Subgroup.closure (S \ {w}) :=
    fun x hx hxw => Subgroup.subset_closure ⟨hx, hxw⟩
  have hprod : a * b * c * (g * c * g⁻¹) * (g * b * g⁻¹) ∈ Subgroup.closure (S \ {w}) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
      (hmem a ha (Ne.symm hwa)) (hmem b hb (Ne.symm hwb))) (hmem c hc (Ne.symm hwc)))
      (hmem _ hc' hc'w)) (hmem _ hb' hb'w)
  rw [← hweq] at hprod
  exact hInd w hw hprod

private theorem h3_of (hm : 7 ≤ m) (ψ : Perm (Fin m) →* G) (hψ : Function.Injective ψ)
    (hsw : ∀ σ : Perm (Fin m), σ.IsSwap → ψ σ ∈ cls t)
    (hnb : ∀ σ : Perm (Fin m), σ.IsSwap → ∀ e ∈ cls t, e ≠ ψ σ → ψ σ * e = e * ψ σ →
      ∃ τ : Perm (Fin m), τ.IsSwap ∧ ψ τ = e) :
    ∀ Δ : (commGraph (cls t)).ConnectedComponent,
      ∀ x ∈ Subgroup.normalizer (Subtype.val '' Δ.supp), orderOf x = 2 →
        ∃ f ∈ Subtype.val '' Δ.supp, x * f * x⁻¹ = f := by
  intro Δ
  induction Δ using SimpleGraph.ConnectedComponent.ind with
  | h v =>
    obtain ⟨v, hv⟩ := v
    rw [image_supp_connectedComponentMk hv]
    intro x hxN hx2
    obtain ⟨σ₀, hσ₀⟩ : ∃ σ₀ : Perm (Fin m), σ₀.IsSwap :=
      ⟨swap ⟨0, by omega⟩ ⟨1, by omega⟩, _, _, by rw [Ne, Fin.mk.injEq]; omega, rfl⟩
    obtain ⟨h, rfl⟩ : ∃ h : G, v = h * ψ σ₀ * h⁻¹ := by
      obtain ⟨e₁, he₁⟩ := hv
      obtain ⟨e₀, he₀⟩ := hsw _ hσ₀
      exact ⟨e₁ * e₀⁻¹, by rw [he₁, he₀]; group⟩
    let ψ' : Perm (Fin m) →* G :=
      { toFun := fun σ => h * ψ σ * h⁻¹
        map_one' := by simp
        map_mul' := fun a b => by simp only [map_mul]; group }
    have hψ' : Function.Injective ψ' := fun a b hab =>
      hψ (conj_injective (hab : h * ψ a * h⁻¹ = h * ψ b * h⁻¹))
    have hsw' : ∀ σ : Perm (Fin m), σ.IsSwap → ψ' σ ∈ cls t :=
      fun σ hσ => conj_mem_cls (hsw σ hσ) h
    have hnb' : ∀ σ : Perm (Fin m), σ.IsSwap → ∀ e ∈ cls t, e ≠ ψ' σ → ψ' σ * e = e * ψ' σ →
        ∃ τ : Perm (Fin m), τ.IsSwap ∧ ψ' τ = e := by
      intro σ hσ e he hne hc
      change h * ψ σ * h⁻¹ * e = e * (h * ψ σ * h⁻¹) at hc
      have he' : h⁻¹ * e * h ∈ cls t := by
        have := conj_mem_cls he h⁻¹
        rwa [inv_inv] at this
      obtain ⟨τ, hτ, hτe⟩ := hnb σ hσ _ he' (fun h' => hne (by
        change e = h * ψ σ * h⁻¹
        rw [← h']
        group)) (by
        calc ψ σ * (h⁻¹ * e * h) = h⁻¹ * (h * ψ σ * h⁻¹ * e) * h := by group
          _ = h⁻¹ * (e * (h * ψ σ * h⁻¹)) * h := by rw [hc]
          _ = h⁻¹ * e * h * ψ σ := by group)
      refine ⟨τ, hτ, ?_⟩
      change h * ψ τ * h⁻¹ = e
      rw [hτe]
      group
    have hA : compSet (cls t) (h * ψ σ₀ * h⁻¹) = {x | ∃ σ : Perm (Fin m), σ.IsSwap ∧ ψ' σ = x} :=
      compSet_eq_swaps (by omega) ψ' hsw' hnb' hσ₀
    rw [hA] at hxN ⊢
    obtain ⟨σ, hσ, hfix⟩ := exists_swap_conj_eq hm ψ' hψ' (mul_self_of_orderOf hx2)
      (fun σ hσ => by
        obtain ⟨τ, -, hτ⟩ := (Subgroup.mem_set_normalizer_iff.1 hxN (ψ' σ)).1 ⟨σ, hσ, rfl⟩
        exact ⟨τ, hτ⟩)
    exact ⟨ψ' σ, ⟨σ, hσ, rfl⟩, hfix⟩

end Group

theorem cls_subset_of_nbr {G : Type} [Group G] [Finite G] {t : G} (ht : orderOf t = 2)
    (ot : ∀ x ∈ cls t, ∀ y ∈ cls t, Odd (orderOf (x * y)) ∨ orderOf (x * y) = 2)
    {m : ℕ} (hm : 9 ≤ m) (ψ : Perm (Fin m) →* G) (hψ : Function.Injective ψ)
    (hsw : ∀ σ : Perm (Fin m), σ.IsSwap → ψ σ ∈ cls t)
    (hnb : ∀ σ : Perm (Fin m), σ.IsSwap → ∀ e ∈ cls t, e ≠ ψ σ → ψ σ * e = e * ψ σ →
      ∃ τ : Perm (Fin m), τ.IsSwap ∧ ψ τ = e) :
    ∀ e ∈ cls t, ∃ τ : Perm (Fin m), τ.IsSwap ∧ ψ τ = e := by
  have hm8 : 8 ≤ m := by omega
  have hD2 : ∀ x ∈ cls t, orderOf x = 2 := fun x hx => (orderOf_of_mem_cls hx).trans ht
  have hDinv : ∀ g : G, ∀ x ∈ cls t, g * x * g⁻¹ ∈ cls t := fun g x hx => conj_mem_cls hx g
  have hodd : IsOddTranspositionSet (cls t) := ot
  obtain ⟨T, hT⟩ := exists_sylow_of_pairwise (S := Set.range fun i => ψ (sw hm8 i))
    (by
      rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
      simp only [← map_mul, sw_commute])
    (by
      rintro _ ⟨i, rfl⟩
      simp only [← map_mul, sw_mul_self, map_one])
  have hdS : ∀ i, ψ (sw hm8 i) ∈ (T : Set G) ∩ cls t :=
    fun i => ⟨hT ⟨i, rfl⟩, hsw _ (sw_isSwap hm8 i)⟩
  have hSc : ∀ x ∈ (T : Set G) ∩ cls t, ∀ y ∈ (T : Set G) ∩ cls t, x * y = y * x :=
    fun x hx y hy => hodd.commute_of_mem_pGroup hD2 T.isPGroup' hx.2 hx.1 hy.2 hy.1
  have hA := compSet_eq_swaps (by omega) ψ hsw hnb (sw_isSwap hm8 0)
  have hS0 : ∀ x ∈ (T : Set G) ∩ cls t, ∃ σ : Perm (Fin m), σ.IsSwap ∧ ψ σ = x := by
    intro x hx
    have hx' : x ∈ compSet (cls t) (ψ (sw hm8 0)) :=
      mem_compSet_of_commute (hsw _ (sw_isSwap hm8 0)) hx.2 (hSc _ (hdS 0) x hx)
    rw [hA] at hx'
    exact hx'
  have hS4 : ∀ a b c : G, ∃ w ∈ (T : Set G) ∩ cls t, w ≠ a ∧ w ≠ b ∧ w ≠ c := by
    intro a b c
    obtain ⟨i, hi⟩ := exists_ne_three (f := fun i => ψ (sw hm8 i))
      (hψ.comp (sw_injective hm8)) (by simp) a b c
    exact ⟨_, hdS i, hi⟩
  have hconn := hodd.connected_of_sylow hDinv hD2 T
    (h1_of ψ hψ hnb Set.inter_subset_right (sw_isSwap hm8 0) (sw_isSwap hm8 1)
      (fun h => absurd (sw_injective hm8 h) (by decide)) (sw_commute hm8 0 1) (hdS 0) (hdS 1))
    (h2_of (fun x hx => mul_self_of_orderOf (hD2 x hx.2)) hSc hS4
      (fun w hw => not_mem_closure_diff ψ hψ hS0 hSc hw))
    (h3_of (by omega) ψ hψ hsw hnb)
  intro e he
  have he' : e ∈ compSet (cls t) (ψ (sw hm8 0)) :=
    ⟨hsw _ (sw_isSwap hm8 0), he, hconn.preconnected _ _⟩
  rw [hA] at he'
  exact he'

end CFSG.EvenSmallLie.OddTranspAlt
