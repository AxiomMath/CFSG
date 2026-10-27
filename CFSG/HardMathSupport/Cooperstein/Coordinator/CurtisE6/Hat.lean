module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6.Lift

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6

theorem exists_hat {G' G L : Type} [Group G'] [Finite G'] [Group G] [Group L] [Finite L]
    (πI : G' →* G) (f : L →* G) (hf : Function.Surjective f) (hfk : f.ker ≤ Subgroup.center L)
    (hperf : commutator L = ⊤)
    (hsec : ∀ (E : Type) [Group E] [Finite E] (p : E →* G'), Function.Surjective p →
      p.ker ≤ Subgroup.center E → ∃ s : G' →* E, ∀ g, p (s g) = g) (hI : Function.Surjective πI) :
    ∃ π : G' →* L, Function.Surjective π ∧ ∀ x, f (π x) = πI x := by
  classical
  let P : Subgroup (G' × L) :=
    MonoidHom.eqLocus (πI.comp (MonoidHom.fst G' L)) (f.comp (MonoidHom.snd G' L))
  let p : P →* G' := (MonoidHom.fst G' L).comp P.subtype
  have hp : Function.Surjective p := by
    intro x
    obtain ⟨l, hl⟩ := hf (πI x)
    exact ⟨⟨(x, l), hl.symm⟩, rfl⟩
  have hpker : p.ker ≤ Subgroup.center P := by
    rintro ⟨⟨x, l⟩, hx⟩ hk
    have hx1 : x = 1 := hk
    subst hx1
    have h1 : πI 1 = f l := hx
    have hlk : l ∈ f.ker := by
      rw [MonoidHom.mem_ker, ← h1, map_one]
    rw [Subgroup.mem_center_iff]
    rintro ⟨⟨y, y'⟩, -⟩
    apply Subtype.ext
    change (y * 1, y' * l) = (1 * y, l * y')
    rw [mul_one, one_mul, Subgroup.mem_center_iff.1 (hfk hlk) y']
  obtain ⟨s, hs⟩ := hsec P p hp hpker
  let π : G' →* L := (MonoidHom.snd G' L).comp (P.subtype.comp s)
  have hπ : ∀ x, f (π x) = πI x := by
    intro x
    have h1 : πI (s x : G' × L).1 = f (s x : G' × L).2 := (s x).2
    have h2 : (s x : G' × L).1 = x := hs x
    change f (s x : G' × L).2 = _
    rw [← h1, h2]
  refine ⟨π, ?_, hπ⟩
  have hmapped : π.range ⊔ f.ker = ⊤ := by
    rw [eq_top_iff]
    intro g _
    obtain ⟨x, hx⟩ := hI (f g)
    have h1 : f (π x) = f g := by rw [hπ, hx]
    have hmem : π x * ((π x)⁻¹ * g) = g := by group
    rw [← hmem]
    refine mul_mem (Subgroup.mem_sup_left ⟨x, rfl⟩) (Subgroup.mem_sup_right ?_)
    rw [MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel]
  exact MonoidHom.range_eq_top.1 (top_of_sup_central π.range f.ker hfk hmapped hperf)

theorem exists_two_lift {G' L : Type} [Group G'] [Finite G'] [Group L] (π : G' →* L)
    (hsurj : Function.Surjective π)
    (hodd : ∀ x ∈ π.ker, ∀ j : ℕ, x ^ (2 ^ j) = 1 → x = 1)
    (E : Subgroup L) (hE : ∀ x ∈ E, x ^ 2 = 1) :
    ∃ A : Subgroup G', A.map π = E ∧ (∀ a ∈ A, a ^ 2 = 1) ∧ Nat.card A = Nat.card E := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let H : Subgroup G' := E.comap π
  let P : Sylow 2 H := Classical.arbitrary _
  let A : Subgroup G' := (P : Subgroup H).map H.subtype
  have hAH : ∀ a ∈ A, a ∈ H := by
    rintro a ⟨x, -, rfl⟩
    exact x.2
  have hApow : ∀ a ∈ A, ∃ j : ℕ, a ^ (2 ^ j) = 1 := by
    rintro a ⟨x, hx, rfl⟩
    obtain ⟨j, hj⟩ := P.isPGroup' ⟨x, hx⟩
    refine ⟨j, ?_⟩
    have h2 : (x : H) ^ (2 ^ j) = 1 := by
      have := congrArg (fun z : (P : Subgroup H) => (z : H)) hj
      simpa using this
    show H.subtype x ^ (2 ^ j) = 1
    rw [← map_pow, h2, map_one]
  have hsq : ∀ a ∈ A, a ^ 2 = 1 := by
    intro a ha
    obtain ⟨j, hj⟩ := hApow a ha
    have hπa : π a ∈ E := hAH a ha
    refine hodd (a ^ 2) ?_ j ?_
    · rw [MonoidHom.mem_ker, map_pow]; exact hE _ hπa
    · rw [← pow_mul, mul_comm, pow_mul, hj, one_pow]
  have hinj : Function.Injective (π.comp A.subtype) := by
    intro a b hab
    have hab' : π a = π b := hab
    apply Subtype.ext
    have h1 : (a : G')⁻¹ * b ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hab', inv_mul_cancel]
    obtain ⟨j, hj⟩ := hApow ((a : G')⁻¹ * b) (mul_mem (inv_mem a.2) b.2)
    have := hodd _ h1 j hj
    exact inv_mul_eq_one.1 this
  have hmapE : A.map π = E := by
    refine le_antisymm ?_ ?_
    · rintro x ⟨a, ha, rfl⟩; exact hAH a ha
    · let f' : H →* E :=
        { toFun := fun h => ⟨π h, h.2⟩
          map_one' := Subtype.ext (map_one π)
          map_mul' := fun a b => Subtype.ext (map_mul π (a : G') (b : G')) }
      have hf' : Function.Surjective f' := by
        rintro ⟨x, hx⟩
        obtain ⟨g, hg⟩ := hsurj x
        exact ⟨⟨g, by simp [H, hg, hx]⟩, Subtype.ext hg⟩
      have hEp : IsPGroup 2 (⊤ : Subgroup E) := fun g => ⟨1, by
        apply Subtype.ext
        apply Subtype.ext
        simpa using hE g.1.1 g.1.2⟩
      let P' : Sylow 2 E := P.mapSurjective hf'
      have htop : (P' : Subgroup E) = ⊤ := (P'.is_maximal' (Q := ⊤) hEp le_top).symm
      have hP' : (P' : Subgroup E) = (P : Subgroup H).map f' := Sylow.coe_mapSurjective hf' P
      intro x hx
      have hx' : (⟨x, hx⟩ : E) ∈ (P : Subgroup H).map f' := by rw [← hP', htop]; trivial
      obtain ⟨h, hh, hh'⟩ := hx'
      exact ⟨h.1, ⟨h, hh, rfl⟩, congrArg Subtype.val hh'⟩
  refine ⟨A, hmapE, hsq, ?_⟩
  have hr : (π.comp A.subtype).range = A.map π := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← hmapE, ← hr]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv)

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6
