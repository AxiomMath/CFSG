module

public import CFSG.RankThree.PartTwo.Census.TransitiveLift

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.RankThree.PartTwo.Sec4.Census

theorem exists_hom_of_central_cover {X H G : Type} [Group X] [Finite X] [Group H] [Finite H]
    [Group G] {φ : X →* G} {ρ : H →* G} (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center X)
    (hsec : ∀ (E : Type) [Group E] [Finite E] (π : E →* H), Function.Surjective π →
      π.ker ≤ Subgroup.center E → ∃ s : H →* E, ∀ g, π (s g) = g) :
    ∃ t : H →* X, ∀ h, φ (t h) = ρ h := by
  let P : Subgroup (X × H) :=
    MonoidHom.eqLocus (φ.comp (MonoidHom.fst X H)) (ρ.comp (MonoidHom.snd X H))
  let π : P →* H := (MonoidHom.snd X H).comp P.subtype
  have hπ : Function.Surjective π := by
    intro h
    obtain ⟨x, hx⟩ := hφ (ρ h)
    exact ⟨⟨(x, h), hx⟩, rfl⟩
  have hcen : π.ker ≤ Subgroup.center P := by
    intro e he
    have h1 : e.1.2 = 1 := he
    have h2 : φ e.1.1 = 1 := by
      have h3 : φ e.1.1 = ρ e.1.2 := e.2
      rw [h3, h1, map_one]
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    apply Prod.ext
    · exact Subgroup.mem_center_iff.mp (hker h2) g.1.1
    · show g.1.2 * e.1.2 = e.1.2 * g.1.2
      rw [h1, mul_one, one_mul]
  obtain ⟨s, hs⟩ := hsec P π hπ hcen
  refine ⟨(MonoidHom.fst X H).comp (P.subtype.comp s), fun h => ?_⟩
  have h1 : φ (s h).1.1 = ρ (s h).1.2 := (s h).2
  have h2 : (s h).1.2 = h := hs h
  rw [h2] at h1
  exact h1

theorem three_le_pRank_of_section {X H G : Type} [Group X] [Finite X] [Group H] [Finite H]
    [Group G] {φ : X →* G} {ρ : H →* G} (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center X)
    (hsec : ∀ (E : Type) [Group E] [Finite E] (π : E →* H), Function.Surjective π →
      π.ker ≤ Subgroup.center E → ∃ s : H →* E, ∀ g, π (s g) = g)
    {E : Subgroup H} (hE2 : ∀ x ∈ E, x * x = 1) (hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hE8 : 8 ≤ Nat.card E) (hinj : ∀ x ∈ E, ρ x = 1 → x = 1) : 3 ≤ CFSG.pRank 2 X := by
  obtain ⟨t, ht⟩ := exists_hom_of_central_cover (ρ := ρ) hφ hker hsec
  have htinj : Function.Injective (t.comp E.subtype) := by
    rw [injective_iff_map_eq_one]
    intro e he
    have h1 : t (e : H) = 1 := he
    have h2 : ρ (e : H) = 1 := by rw [← ht, h1, map_one]
    exact Subtype.ext (hinj _ e.2 h2)
  let A : Subgroup X := (t.comp E.subtype).range
  have hAcard : Nat.card A = Nat.card E :=
    (Nat.card_congr (MonoidHom.ofInjective htinj).toEquiv).symm
  have hA : CFSG.IsElementaryAbelian 2 A :=
    { toIsMulCommutative := ⟨⟨fun a b => by
        obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 a.2
        obtain ⟨y, hy⟩ := MonoidHom.mem_range.1 b.2
        apply Subtype.ext
        change (a : X) * b = b * a
        rw [← hx, ← hy, ← map_mul, ← map_mul]
        exact congrArg (fun z => (t.comp E.subtype) z) (Subtype.ext (hEc x x.2 y y.2))⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a => by
        obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 a.2
        apply Subtype.ext
        change (a : X) ^ 2 = 1
        rw [← hx, ← map_pow, pow_two]
        have : x * x = 1 := Subtype.ext (hE2 x x.2)
        rw [this, map_one] }
  refine TransitiveLift.le_pRank_of_card hA (k := 3) ?_
  rw [hAcard]
  calc 2 ^ 3 = 8 := by norm_num
    _ ≤ Nat.card E := hE8

end CFSG.EvenSporadicStandard.Induction
