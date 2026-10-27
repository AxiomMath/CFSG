module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19TabClass8Basic

public section

namespace CFSG.QuasithinUnique.DoubleA3.A8Perm

open Equiv

variable {Γ : Type} [Group Γ]

@[expose] def fixSub (ι : Γ →* Perm (Fin 8)) (ω : Fin 8) : Subgroup Γ :=
  (MulAction.stabilizer (Perm (Fin 8)) ω).comap ι

theorem mem_fixSub {ι : Γ →* Perm (Fin 8)} {ω : Fin 8} {g : Γ} :
    g ∈ fixSub ι ω ↔ ι g ω = ω := Iff.rfl

theorem card_le_eight_of_fix [Finite Γ] (ι : Γ →* Perm (Fin 8))
    (hι : Function.Injective ι) (hev : ∀ g, Perm.sign (ι g) = 1) {X : Subgroup Γ}
    (hX : IsPGroup 2 X) (ω : Fin 8) (hfix : ∀ g ∈ X, ι g ω = ω) : Nat.card X ≤ 8 := by
  classical
  have hperm : ∀ g : X, ∀ y : Fin 8, ι g y ≠ ω ↔ y ≠ ω := fun g y => by
    constructor
    · intro hy h
      apply hy
      rw [h]
      exact hfix g g.2
    · intro hy h
      apply hy
      apply (ι g).injective
      rw [h, hfix g g.2]
  let φ : X →* alternatingGroup {y : Fin 8 // y ≠ ω} :=
    { toFun := fun g => ⟨(ι g).subtypePerm (p := fun y => y ≠ ω) (hperm g), by
        rw [Perm.mem_alternatingGroup,
          Perm.sign_subtypePerm (ι g) (p := fun y => y ≠ ω) (hperm g)]
        · exact hev g
        · intro y hy h
          apply hy
          rw [h]
          exact hfix g g.2⟩
      map_one' := by
        apply Subtype.ext
        apply Equiv.ext
        intro y
        apply Subtype.ext
        simp
      map_mul' := fun g h => by
        apply Subtype.ext
        apply Equiv.ext
        intro y
        apply Subtype.ext
        show ι ((g * h : X) : Γ) y.1 = ι g (ι h y.1)
        rw [Subgroup.coe_mul, map_mul]
        rfl }
  have hφ : Function.Injective φ := by
    intro g h hgh
    apply Subtype.ext
    apply hι
    apply Equiv.ext
    intro y
    by_cases hy : y = ω
    · rw [hy, hfix g g.2, hfix h h.2]
    · have := congrArg (fun a : alternatingGroup {y : Fin 8 // y ≠ ω} =>
        ((a : Perm {y : Fin 8 // y ≠ ω}) ⟨y, hy⟩ : Fin 8)) hgh
      exact this
  have h7 : Fintype.card {y : Fin 8 // y ≠ ω} = 7 := by
    rw [Fintype.card_subtype_compl]
    simp
  have : Nontrivial {y : Fin 8 // y ≠ ω} :=
    Fintype.one_lt_card_iff_nontrivial.mp (by rw [h7]; norm_num)
  have hcard : Nat.card (alternatingGroup {y : Fin 8 // y ≠ ω}) = 2 ^ 3 * 315 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, h7]
    norm_num [Nat.factorial]
  have := CFSG.QuasithinUnique.Id2519.Tab.Class8.card_le_of_injective hX φ hφ (e := 3) (u := 315)
    (by norm_num) hcard
  simpa using this

theorem orbit_ncard_mul_stab_card [Finite Γ] (ι : Γ →* Perm (Fin 8)) (X : Subgroup Γ) (ω : Fin 8) :
    Set.ncard {ω' : Fin 8 | ∃ p ∈ X, ι p ω = ω'} * Nat.card ↥(X ⊓ fixSub ι ω) = Nat.card X := by
  let inst : MulAction X (Fin 8) := MulAction.compHom (Fin 8) (ι.comp X.subtype)
  have h1 := Subgroup.card_mul_index (MulAction.stabilizer X ω)
  rw [MulAction.index_stabilizer] at h1
  have h2 : MulAction.orbit X ω = {ω' : Fin 8 | ∃ p ∈ X, ι p ω = ω'} := by
    ext y
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨g, g.2, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨⟨p, hp⟩, rfl⟩
  have h3 : Nat.card ↥(MulAction.stabilizer X ω) = Nat.card ↥(X ⊓ fixSub ι ω) := by
    have : (MulAction.stabilizer X ω).map X.subtype = X ⊓ fixSub ι ω := by
      ext g
      rw [Subgroup.mem_map, Subgroup.mem_inf, mem_fixSub]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y.2, MulAction.mem_stabilizer_iff.mp hy⟩
      · rintro ⟨hgX, hg⟩
        exact ⟨⟨g, hgX⟩, MulAction.mem_stabilizer_iff.mpr hg, rfl⟩
    rw [← this, Subgroup.card_map_of_injective X.subtype_injective]
  rw [h2, h3] at h1
  rw [mul_comm]
  exact h1

theorem exists_mem_of_card_ge [Finite Γ] (ι : Γ →* Perm (Fin 8)) (hι : Function.Injective ι)
    (hev : ∀ g, Perm.sign (ι g) = 1) {P : Subgroup Γ} (hP : IsPGroup 2 P)
    (h64 : 64 ≤ Nat.card P) (ω ω' : Fin 8) : ∃ p ∈ P, ι p ω = ω' := by
  have hos := orbit_ncard_mul_stab_card ι P ω
  have hA : IsPGroup 2 ↥(P ⊓ fixSub ι ω) :=
    hP.of_injective (Subgroup.inclusion inf_le_left) (Subgroup.inclusion_injective _)
  have hstab : Nat.card ↥(P ⊓ fixSub ι ω) ≤ 8 :=
    card_le_eight_of_fix ι hι hev hA ω (fun g hg => hg.2)
  have horb : 8 ≤ Set.ncard {ω' : Fin 8 | ∃ p ∈ P, ι p ω = ω'} := by
    by_contra hlt
    push Not at hlt
    nlinarith
  have hfin : (Set.univ : Set (Fin 8)).Finite := Set.finite_univ
  have hall : {ω' : Fin 8 | ∃ p ∈ P, ι p ω = ω'} = Set.univ :=
    Set.eq_of_subset_of_ncard_le (Set.subset_univ _) (by simpa using horb) hfin
  have hmem : ω' ∈ {ω' : Fin 8 | ∃ p ∈ P, ι p ω = ω'} := by rw [hall]; trivial
  exact hmem

theorem fixed_point_free_of_commute (ι : Γ →* Perm (Fin 8)) (hι : Function.Injective ι)
    {P : Subgroup Γ} (htrans : ∀ ω ω' : Fin 8, ∃ p ∈ P, ι p ω = ω') {z : Γ} (hz1 : z ≠ 1)
    (hz : ∀ p ∈ P, p * z = z * p) (ω : Fin 8) : ι z ω ≠ ω := by
  intro h
  apply hz1
  apply hι
  rw [map_one]
  apply Equiv.ext
  intro y
  obtain ⟨p, hp, rfl⟩ := htrans ω y
  have h1 : ι z (ι p ω) = ι p (ι z ω) := by
    have := congrArg (fun g => ι g ω) (hz p hp)
    simpa [map_mul] using this.symm
  rw [h1, h]
  rfl

end CFSG.QuasithinUnique.DoubleA3.A8Perm
