module

public import CFSG.GH74.Generic.S45.LAltDefs
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.GH74.Generic.S45.LAlt

open Equiv Equiv.Perm Subgroup
open scoped commutatorElement

variable {n : ℕ}

section CaseI

variable {σ : Perm (Fin n)}

theorem fix_iff {l : Perm (Fin n)} (hl : l * σ = σ * l) (x : Fin n) :
    σ (l x) = l x ↔ σ x = x := by
  have h : l (σ x) = σ (l x) := congrArg (fun p : Perm (Fin n) => p x) hl
  constructor
  · intro hx
    apply l.injective
    rw [h, hx]
  · intro hx
    rw [← h, hx]

theorem five_le_card_fix {Lb : Subgroup (Perm (Fin n))} (hLb : ∀ l ∈ Lb, l * σ = σ * l)
    (hperf : ⁅Lb, Lb⁆ = Lb) {v₀ : Perm (Fin n)} (hv₀ : v₀ ∈ Lb) (hv₀1 : v₀ ≠ 1)
    (hfix : ∀ l ∈ Lb, ∀ x, σ x ≠ x → l x = x) : 5 ≤ Nat.card {x : Fin n // σ x = x} := by
  by_contra hlt
  push Not at hlt
  have h4 : Nat.card {x : Fin n // σ x = x} ≤ 4 := by omega
  let ρ : ↥Lb →* Perm {x : Fin n // σ x = x} :=
    { toFun := fun l => (l : Perm (Fin n)).subtypePerm (fun x => fix_iff (hLb l l.2) x)
      map_one' := Equiv.ext fun x => Subtype.ext rfl
      map_mul' := fun a b => Equiv.ext fun x => Subtype.ext rfl }
  have hinj : Function.Injective ρ := by
    intro a b hab
    apply Subtype.ext
    refine Equiv.ext fun x => ?_
    by_cases hx : σ x = x
    · have := congrArg (fun p : Perm {x : Fin n // σ x = x} => (p ⟨x, hx⟩ : Fin n)) hab
      exact this
    · rw [hfix a a.2 x hx, hfix b b.2 x hx]
  have : Group.IsSolvable (Perm {x : Fin n // σ x = x}) := Equiv.Perm.isSolvable h4
  have : Group.IsSolvable ↥Lb := Group.isSolvable_of_isSolvable_injective hinj
  have : Nontrivial ↥Lb := ⟨⟨⟨v₀, hv₀⟩, 1, fun h => hv₀1 (congrArg Subtype.val h)⟩⟩
  have : Group.IsPerfect ↥Lb := Subgroup.isPerfect_iff.2 hperf
  exact (Group.IsSolvable.commutator_lt_top_of_nontrivial ↥Lb).ne Group.IsPerfect.commutator_eq_top

theorem badCent_of_fixes (hσ : σ * σ = 1) (hσ1 : σ ≠ 1) {Lb : Subgroup (Perm (Fin n))}
    (hLb : Lb ≤ centAlt σ) (hperf : ⁅Lb, Lb⁆ = Lb) {v₀ : Perm (Fin n)} (hv₀ : v₀ ∈ Lb)
    (hv₀1 : v₀ ≠ 1) (hfix : ∀ l ∈ Lb, ∀ x, σ x ≠ x → l x = x) : BadCent σ := by
  have hLb' : ∀ l ∈ Lb, l * σ = σ * l := fun l hl => (mem_centAlt.1 (hLb hl)).2
  have h5 := five_le_card_fix hLb' hperf hv₀ hv₀1 hfix
  have h5' : 5 ≤ Fintype.card {x : Fin n // σ x = x} := by
    rw [← Nat.card_eq_fintype_card]
    exact h5
  obtain ⟨e⟩ : Nonempty (Fin 5 ↪ {x : Fin n // σ x = x}) :=
    Function.Embedding.nonempty_of_card_le (by simpa using h5')
  obtain ⟨ω, hω⟩ : ∃ ω, σ ω ≠ ω := by
    by_contra h
    push Not at h
    exact hσ1 (Equiv.ext h)
  set a : Fin 5 → Fin n := fun i => (e i : Fin n) with ha_def
  have ha : ∀ i, σ (a i) = a i := fun i => (e i).2
  have ha_inj : Function.Injective a := fun i j h => e.injective (Subtype.ext h)
  have hσσ : σ (σ ω) = ω := sigma_sq_apply hσ ω
  let l : List (Fin n) := [a 0, a 1, a 2, a 3]
  have hnd : l.Nodup := by
    have : l = ([0, 1, 2, 3] : List (Fin 5)).map a := rfl
    rw [this]
    exact List.Nodup.map ha_inj (by decide)
  let c4 : Perm (Fin n) := l.formPerm
  have hc4cyc : c4.IsCycle := List.isCycle_formPerm hnd (by simp [l])
  have hsupp : c4.support = l.toFinset :=
    List.support_formPerm_of_nodup l hnd (by intro x h; simp [l] at h)
  have hcard : c4.support.card = 4 := by
    rw [hsupp, List.toFinset_card_of_nodup hnd]
    rfl
  have hc4ord : orderOf c4 = 4 := by rw [hc4cyc.orderOf, hcard]
  have hc4sign : Perm.sign c4 = -1 := by
    rw [hc4cyc.sign, hcard]
    decide
  have hlfix : ∀ x ∈ l, σ x = x := by
    intro x hx
    simp only [l, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> exact ha _
  have hdisj_σ : c4.Disjoint σ := fun x => by
    by_cases hx : x ∈ l
    · exact Or.inr (hlfix x hx)
    · exact Or.inl (List.formPerm_apply_of_notMem hx)
  let τ : Perm (Fin n) := swap ω (σ ω)
  have hτ_sign : Perm.sign τ = -1 := Perm.sign_swap (Ne.symm hω)
  have hτ_ord : orderOf τ = 2 :=
    Equiv.Perm.IsSwap.orderOf (⟨ω, σ ω, Ne.symm hω, rfl⟩ : Equiv.Perm.IsSwap τ)
  have hdisj_τ : c4.Disjoint τ := fun x => by
    by_cases hx : x ∈ l
    · right
      have hxσ := hlfix x hx
      refine swap_apply_of_ne_of_ne ?_ ?_
      · rintro rfl
        exact hω hxσ
      · intro h
        rw [h, hσσ] at hxσ
        exact hω hxσ.symm
    · exact Or.inl (List.formPerm_apply_of_notMem hx)
  have hτσ : τ * σ = σ * τ := by
    have h1 := swap_apply_apply σ ω (σ ω)
    rw [hσσ, swap_comm] at h1
    have h2 : τ = σ * τ * σ⁻¹ := h1
    calc τ * σ = (σ * τ * σ⁻¹) * σ := by rw [← h2]
      _ = σ * τ := by group
  have hc4σ : c4 * σ = σ * c4 := hdisj_σ.commute.eq
  have hg_alt : c4 * τ ∈ alternatingGroup (Fin n) := by
    rw [Perm.mem_alternatingGroup, Perm.sign_mul, hc4sign, hτ_sign]
    norm_num
  have hg_comm : (c4 * τ) * σ = σ * (c4 * τ) := by
    have c1 : Commute c4 σ := hc4σ
    have c2 : Commute τ σ := hτσ
    exact (c1.mul_left c2).eq
  have hg_ord : orderOf (c4 * τ) = 4 := by
    rw [hdisj_τ.orderOf, hc4ord, hτ_ord]
    norm_num
  have hg_mem : c4 * τ ∈ centAlt σ := mem_centAlt.2 ⟨hg_alt, hg_comm⟩
  let p : Fin n → Prop := fun x => σ x = x
  let X : Subgroup (Perm (Fin n)) :=
    (alternatingGroup (Subtype p)).map (Equiv.Perm.ofSubtype : Perm (Subtype p) →* Perm (Fin n))
  have hXle : X ≤ centAlt σ := by
    rintro _ ⟨h, hh, rfl⟩
    refine mem_centAlt.2 ⟨?_, ?_⟩
    · rw [Perm.mem_alternatingGroup, sign_ofSubtype]
      exact Perm.mem_alternatingGroup.1 hh
    · refine Equiv.ext fun x => ?_
      rw [Perm.mul_apply, Perm.mul_apply]
      by_cases hx : p x
      · have hx' : σ x = x := hx
        rw [hx', Equiv.Perm.ofSubtype_apply_of_mem h hx]
        exact ((h ⟨x, hx⟩).2).symm
      · have hx' : ¬ p (σ x) := by
          intro h'
          apply hx
          have : σ (σ x) = σ x := h'
          rw [sigma_sq_apply hσ x] at this
          exact this.symm
        rw [Equiv.Perm.ofSubtype_apply_of_not_mem h hx, Equiv.Perm.ofSubtype_apply_of_not_mem h hx']
  have h5'' : 5 ≤ Nat.card (Subtype p) := h5
  have hXperf : ⁅X, X⁆ = X := by
    rw [← Subgroup.map_commutator, commutator_alternatingGroup_eq_self h5'']
  have h01 : e 0 ≠ e 1 := fun h => by simpa using e.injective h
  have h23 : e 2 ≠ e 3 := fun h => by simpa using e.injective h
  have hdX : swap (a 0) (a 1) * swap (a 2) (a 3) ∈ X := by
    refine ⟨swap (e 0) (e 1) * swap (e 2) (e 3), ?_, ?_⟩
    · rw [SetLike.mem_coe, Perm.mem_alternatingGroup, Perm.sign_mul, Perm.sign_swap h01,
        Perm.sign_swap h23]
      norm_num
    · rw [map_mul, Equiv.Perm.ofSubtype_swap_eq, Equiv.Perm.ofSubtype_swap_eq]
  have hd : IsDblTransp (swap (a 0) (a 1) * swap (a 2) (a 3)) := by
    have hne : ∀ i j : Fin 5, i ≠ j → a i ≠ a j := fun i j h h' => h (ha_inj h')
    exact ⟨a 0, a 1, a 2, a 3, hne _ _ (by decide), hne _ _ (by decide), hne _ _ (by decide),
      hne _ _ (by decide), hne _ _ (by decide), hne _ _ (by decide), rfl⟩
  exact ⟨⟨c4 * τ, hg_mem, hg_ord⟩, X, hXle, hXperf, _, hdX, Or.inr hd⟩

end CaseI

end CFSG.GH74.Generic.S45.LAlt
