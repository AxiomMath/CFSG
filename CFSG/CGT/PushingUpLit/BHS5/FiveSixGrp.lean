module

public import CFSG.CGT.PushingUpLit.BHS.TwoSixteen
public import CFSG.CGT.PushingUpLit.BHS5.SymGlue

public section

namespace CFSG.CGT.PushingUpLit.BHS5

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit.BHS
open scoped commutatorElement

theorem eq_of_perfect_of_pow_mem' {G : Type} [Group G] [Finite G] {X N : Subgroup G}
    (hX : ⁅X, X⁆ = X) (hNX : N ≤ X) (hN : (N.subgroupOf X).Normal)
    (hpow : ∀ x ∈ X, ∃ k : ℕ, x ^ 2 ^ k ∈ N) : N = X := by
  have : Group.IsPerfect X := Subgroup.isPerfect_iff.mpr hX
  have := hN
  have hp : IsPGroup 2 (↥X ⧸ N.subgroupOf X) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      obtain ⟨k, hk⟩ := hpow x x.2
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact hk
  have : Group.IsNilpotent (↥X ⧸ N.subgroupOf X) := hp.isNilpotent
  have hsub : Subsingleton (↥X ⧸ N.subgroupOf X) := by
    by_contra hns
    have : Nontrivial (↥X ⧸ N.subgroupOf X) := not_subsingleton_iff_nontrivial.mp hns
    exact Group.IsPerfect.not_isNilpotent (↥X ⧸ N.subgroupOf X) inferInstance
  refine le_antisymm hNX fun x hx => ?_
  have h1 : (QuotientGroup.mk (⟨x, hx⟩ : X) : ↥X ⧸ N.subgroupOf X) = QuotientGroup.mk 1 :=
    Subsingleton.elim _ _
  rw [QuotientGroup.eq] at h1
  simpa [Subgroup.mem_subgroupOf] using h1

theorem opResidual_eq_of_perfect' {G : Type} [Group G] [Finite G] {X : Subgroup G}
    (hX : ⁅X, X⁆ = X) : opResidual 2 X = X :=
  eq_of_perfect_of_pow_mem' hX (opResidual_le 2 X) (opResidual_normal 2 X)
    fun _ hx => exists_pow_mem_opResidual hx

theorem exists_noncomm_of_isQuasisimple {G : Type*} [Group G] (h : CFSG.Open.IsQuasisimple G) :
    ∃ a b : G, a * b ≠ b * a := by
  have := h.2
  obtain ⟨x, hx⟩ := exists_ne (1 : G ⧸ Subgroup.center G)
  induction x using QuotientGroup.induction_on with
  | H g =>
    have hg : g ∉ Subgroup.center G := fun hc => hx ((QuotientGroup.eq_one_iff g).2 hc)
    rw [Subgroup.mem_center_iff] at hg
    push Not at hg
    obtain ⟨b, hb⟩ := hg
    exact ⟨b, g, hb⟩

variable {V : Type} [CommGroup V]

theorem IsSLNatSection.isQuasisimple {E : Subgroup (MulAut V)} {P Z : Subgroup V} {n : ℕ}
    (hn : 2 ≤ n) (h : IsSLNatSection E P Z n) : CFSG.Open.IsQuasisimple ↥E := by
  obtain ⟨-, θ, -⟩ := h
  exact isQuasisimple_of_mulEquiv' θ.symm
    (isQuasisimple_special_linear_two (exists_finset_card_four_galoisField hn))

theorem IsSLNatSection.perfect {E : Subgroup (MulAut V)} {P Z : Subgroup V} {n : ℕ} (hn : 2 ≤ n)
    (h : IsSLNatSection E P Z n) : ⁅E, E⁆ = E := by
  have hEq := IsSLNatSection.isQuasisimple hn h
  have htop : (⊤ : Subgroup ↥E).map E.subtype = E := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have h1 := Subgroup.map_commutator (H₁ := (⊤ : Subgroup ↥E)) (H₂ := ⊤) E.subtype
  rw [htop] at h1
  rw [← h1, ← commutator_def, hEq.1, htop]

theorem IsSLNatSection.opResidual_eq {E : Subgroup (MulAut V)} {P Z : Subgroup V} {n : ℕ}
    [Finite V] (hn : 2 ≤ n) (h : IsSLNatSection E P Z n) : opResidual 2 E = E :=
  opResidual_eq_of_perfect' (IsSLNatSection.perfect hn h)

theorem IsSLNatSection.exists_noncomm {E : Subgroup (MulAut V)} {P Z : Subgroup V} {n : ℕ}
    (hn : 2 ≤ n) (h : IsSLNatSection E P Z n) : ∃ a ∈ E, ∃ b ∈ E, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := exists_noncomm_of_isQuasisimple (IsSLNatSection.isQuasisimple hn h)
  exact ⟨a, a.2, b, b.2, fun h' => hab (Subtype.ext h')⟩

theorem exists_noncomm_altOf {E : Subgroup (MulAut V)} {m : ℕ} (hm : 5 ≤ m)
    (θ : ↥E ≃* Equiv.Perm (Fin m)) : ∃ a ∈ altOf θ, ∃ b ∈ altOf θ, a * b ≠ b * a := by
  have hq : CFSG.Open.IsQuasisimple ↥(altOf θ) :=
    isQuasisimple_of_mulEquiv' (altEquiv θ).symm (isQuasisimple_alternatingGroup hm)
  obtain ⟨a, b, hab⟩ := exists_noncomm_of_isQuasisimple hq
  exact ⟨a, a.2, b, b.2, fun h' => hab (Subtype.ext h')⟩

end CFSG.CGT.PushingUpLit.BHS5
