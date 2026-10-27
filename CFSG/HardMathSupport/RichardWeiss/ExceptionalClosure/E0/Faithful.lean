module

public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0.Quad
public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0.Formula

public section

namespace CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0

open CFSG.RankThree.PartTwo CFSG.QuasithinUnique CFSG.HardMathSupport.Cooperstein.Coordinator
  CFSG.HardMathSupport.Cooperstein.AlternatingGeometry Equiv Equiv.Perm Classical

variable {N : ℕ} {W : Type*} [AddCommGroup W] {M : Type*} [Group M]
variable {θ : M →* Perm (Fin N)} {ρ : M →* AddMonoid.End W} {U : AddSubgroup W}
  {π : U →+ altHeart N} {L S : Subgroup M} {P : Subgroup (Perm (Fin N))} {ω : Perm (Fin N)}
  {Δ₀ : Finset (Fin N)} {Y : AddSubgroup W}

namespace E0Frame

variable (E : E0Frame θ ρ U π L S P ω Δ₀ Y)
include E

theorem exists_P_ne (a b : Perm (Fin N)) :
    ∃ c ∈ P, c ≠ a ∧ c ≠ b := by
  by_contra hcon
  push Not at hcon
  have hsub : (P : Set (Perm (Fin N))) ⊆ {a, b} := by
    intro c hc
    by_cases h1 : c = a
    · exact Or.inl h1
    · exact Or.inr (hcon c hc h1)
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : ({a, b} : Set (Perm (Fin N))).ncard ≤ 2 := by
    refine (Set.ncard_insert_le _ _).trans ?_
    rw [Set.ncard_singleton]
  have h3 : (P : Set (Perm (Fin N))).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]
    exact E.shape.Pcard
  omega

theorem exists_two_nontriv : ∃ h ∈ P, ∃ p ∈ P, h ≠ 1 ∧ p ≠ 1 ∧ p ≠ h := by
  obtain ⟨h, hh, h1, -⟩ := E.exists_P_ne 1 1
  obtain ⟨p, hp, hp1, hph⟩ := E.exists_P_ne 1 h
  exact ⟨h, hh, p, hp, h1, hp1, hph⟩

theorem comm_nonzero_pi :
    ∃ u ∈ Y, ∃ (s : M) (hs : s ∈ S), π ⟨ρ s u - u, E.F.sTriv s hs u⟩ ≠ 0 := by
  obtain ⟨h, hh, p, hp, hh1, hp1, hph⟩ := E.exists_two_nontriv
  obtain ⟨a, ha⟩ := E.exists_in
  obtain ⟨x₀, hx₀⟩ := E.exists_off
  obtain ⟨u, huY, hu, hπu⟩ := E.exists_u (a := a) hx₀ hh
  obtain ⟨s, hs, hθs⟩ := (E.img p).2 (E0Shape.P_le_E0grp hp)
  refine ⟨u, huY, s, hs, fun hzero => ?_⟩
  have := E.F.pi_sub s ⟨u, hu⟩
  rw [hzero, hθs, hπu] at this
  exact E.quad_ne_zero ha hx₀ hh hp hh1 hp1 hph (ε := p) (fun _ _ => rfl) this.symm

theorem comm_nonzero : ∃ u ∈ Y, ∃ s ∈ S, ρ s u ≠ u := by
  obtain ⟨u, huY, s, hs, hne⟩ := E.comm_nonzero_pi
  refine ⟨u, huY, s, hs, fun heq => hne ?_⟩
  have : (⟨ρ s u - u, E.F.sTriv s hs u⟩ : U) = 0 := by
    apply Subtype.ext
    simp [heq]
  rw [this, map_zero]

theorem faithful_of_det_pi (hD : ∃ y₀ ∈ Y, ∃ x₀, x₀ ∉ Δ₀ ∧ E.Det y₀ x₀) :
    ∀ (s : M) (hs : s ∈ S), (∀ y ∈ Y, π ⟨ρ s y - y, E.F.sTriv s hs y⟩ = 0) → θ s = 1 := by
  intro s hs hfix
  by_contra hne
  have hε := (E.img (θ s)).1 ⟨s, hs, rfl⟩
  obtain ⟨⟨p, hp, hpx⟩, hpair⟩ := E0Shape.mem_E0grp_prop E.shape hε
  obtain ⟨a, ha⟩ := E.exists_in
  obtain ⟨x₀, hx₀⟩ := E.exists_off
  by_cases hp1 : p = 1
  · have hPP : PairPerm ω Δ₀ (θ s) := ⟨fun y hy => by rw [hpx y hy, hp1]; rfl, hpair⟩
    obtain ⟨x, hx⟩ : ∃ x, θ s x ≠ x := by
      by_contra hcon
      push Not at hcon
      exact hne (by ext z; simp [hcon z])
    obtain ⟨hxΔ, -, -⟩ := E0Shape.PairPerm.moved E.shape hPP hx
    obtain ⟨y₀, hy₀, x₁, hx₁, hdet⟩ := hD
    obtain ⟨y, hy, hdy⟩ := E.det_exists_all hy₀ hx₁ hdet hxΔ
    have hform := E.pairs_formula ha (Finset.univ.filter fun z => θ s z ≠ z).card s hs (θ s)
      rfl hPP le_rfl y x
    rw [hfix y hy] at hform
    simp only [map_zero] at hform
    have hcond : (x ∉ Δ₀ ∧ θ s x ≠ x) ∧ E.Det y x := ⟨⟨hxΔ, hx⟩, hdy⟩
    split_ifs at hform
    simp at hform
  · obtain ⟨h, hh, hh1, hhp⟩ := E.exists_P_ne 1 p
    obtain ⟨u, huY, hu, hπu⟩ := E.exists_u (a := a) hx₀ hh
    have hzero : π ⟨ρ s u - u, E.F.sub_mem_U s hu⟩ = 0 := hfix u huY
    have := E.F.pi_sub s ⟨u, hu⟩
    rw [hzero, hπu] at this
    exact E.quad_ne_zero ha hx₀ hh hp hh1 hp1 (Ne.symm hhp) (ε := θ s) hpx this.symm

theorem faithful_of_det (hD : ∃ y₀ ∈ Y, ∃ x₀, x₀ ∉ Δ₀ ∧ E.Det y₀ x₀) :
    ∀ s ∈ S, (∀ y ∈ Y, ρ s y = y) → θ s = 1 := by
  intro s hs hfix
  refine E.faithful_of_det_pi hD s hs fun y hy => ?_
  have : (⟨ρ s y - y, E.F.sTriv s hs y⟩ : U) = 0 := by
    apply Subtype.ext
    simp [hfix y hy]
  rw [this, map_zero]

end E0Frame

end CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0
