module

public import CFSG.LocalAnalysis.ComponentInitial.EvenRankOneCover
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverHigher
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryEvenCover
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryOddCover
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryEvenCoverLarge
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryOddCoverLarge
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryFiveCover
public import CFSG.LieType.Steinberg.CentralExt.PerfectCover

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup CFSG.Assembly.LowTwoRank

universe u

theorem odd_card_ker_of_two_cover_trivial {T : Type*} [Group T] {E : Type u} [Group E] [Finite E]
    [Group.IsPerfect E] (η : E →* T) (hη : Function.Surjective η) (hC : η.ker ≤ center E)
    (H : ∀ {E' : Type u} [Group E'] [Finite E'] [Group.IsPerfect E'] (θ : E' →* T),
      Function.Surjective θ → θ.ker ≤ center E' → IsPGroup 2 θ.ker → θ.ker = ⊥) :
    Odd (Nat.card η.ker) := by
  set N := CFSG.LieType.Steinberg.oddPart η.ker hC
  have hN : N ≤ η.ker := fun _ hc => hc.1
  set η' : E ⧸ N →* T := QuotientGroup.lift N η hN
  have hη'mk : ∀ x : E, η' (x : E ⧸ N) = η x := fun x => QuotientGroup.lift_mk _ _ _
  have hη' : Function.Surjective η' := by
    intro q
    obtain ⟨x, rfl⟩ := hη q
    exact ⟨x, hη'mk x⟩
  have hker' : η'.ker = η.ker.map (QuotientGroup.mk' N) := QuotientGroup.ker_lift N η hN
  have hcen' : η'.ker ≤ center (E ⧸ N) := by
    rw [hker']
    rintro _ ⟨c, hc, rfl⟩
    rw [mem_center_iff]
    intro g
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
    exact congrArg (QuotientGroup.mk (s := N)) (mem_center_iff.1 (hC hc) g)
  have h2' : IsPGroup 2 η'.ker := by
    rintro ⟨x, hx⟩
    rw [hker'] at hx
    obtain ⟨c, hc, rfl⟩ := hx
    obtain ⟨a, ha⟩ := CFSG.LieType.Steinberg.exists_pow_two_pow_mem_oddPart hC hc
    refine ⟨a, Subtype.ext ?_⟩
    change (QuotientGroup.mk' N c) ^ 2 ^ a = 1
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact ha
  have : Group.IsPerfect (E ⧸ N) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
  have hbot := H η' hη' hcen' h2'
  have hodd : ∀ c ∈ η.ker, Odd (orderOf c) := by
    intro c hc
    have hmem : (c : E ⧸ N) ∈ η'.ker := by
      rw [MonoidHom.mem_ker, hη'mk]
      exact hc
    rw [hbot, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hmem
    exact hmem.2
  rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
  intro h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hx' : orderOf ((x : η.ker) : E) = 2 := by rw [Subgroup.orderOf_coe, hx]
  have := hodd _ x.2
  rw [hx'] at this
  exact (Nat.not_even_iff_odd.2 this) even_two

theorem even_higher_linear_unitary_perfect_central_kernel_odd_off_five_boundaries {E : Type*}
    {T : Type} [Group E] [Group T] [Finite E] [Finite T] [Group.IsPerfect E] (η : E →* T)
    (hη : Function.Surjective η) (hC : η.ker ≤ center E) {τ : StatedLieTag}
    (hτ : τ = .PSL ∨ τ = .PSU) {n f : ℕ} (hn : 3 ≤ n) (hf : 1 ≤ f)
    (hT : StatedClassicalModel T τ n 2 f)
    (hoff : (τ, n, f) ∉ [(.PSL, 3, 1), (.PSL, 3, 2), (.PSL, 4, 1), (.PSU, 4, 1), (.PSU, 6, 1)]) :
    Odd (Nat.card η.ker) := by
  have hL : CFSG.Blueprint.LieModel T τ n 2 f :=
    Or.inl ⟨by rcases hτ with rfl | rfl <;> decide, hT⟩
  refine odd_card_ker_of_two_cover_trivial η hη hC fun θ hθ hθC h2 => ?_
  rcases hτ with rfl | rfl
  ·
    rcases (show n = 3 ∨ 4 ≤ n by omega) with rfl | hn4
    · have hf3 : 3 ≤ f := by
        by_contra h
        interval_cases f <;> exact hoff (by simp)
      exact (LinearCover.even_linear_three_large_field_catalog_central_two_cover_trivial θ hθ hθC
        h2 hf3 hL).1
    · rcases (show f = 1 ∨ 2 ≤ f by omega) with rfl | hf2
      · have hn5 : 5 ≤ n := by
          by_contra h
          obtain rfl : n = 4 := by omega
          exact hoff (by simp)
        exact (LinearCover.even_higher_linear_prime_field_central_two_cover_trivial θ hθ hθC h2
          hn5 hL).1
      · exact (LinearCover.even_higher_linear_catalog_perfect_central_two_cover_trivial θ hθ hθC
          h2 hn4 hf2 hL).1
  ·
    rcases (show n = 3 ∨ 4 ≤ n by omega) with rfl | hn4
    ·
      have hf2 : 2 ≤ f := by
        obtain ⟨-, -, -, hne⟩ := hT.1
        by_contra h
        obtain rfl : f = 1 := by omega
        exact hne rfl
      exact (even_linear_unitary_rank_one_catalog_central_two_cover_trivial θ hθ h2 hθC
        (Or.inr ⟨f, hf2, hL⟩)).1
    · obtain ⟨r, rfl | rfl⟩ := Nat.even_or_odd' n
      ·
        rcases (show f = 1 ∨ 2 ≤ f by omega) with rfl | hf2
        · have hr : 4 ≤ r := by
            by_contra h
            interval_cases r <;> first | omega | exact hoff (by simp)
          exact (even_even_dimensional_unitary_prime_field_central_two_cover_trivial θ hθ hθC h2
            hr hL).1
        · exact (even_even_dimensional_unitary_catalog_perfect_central_two_cover_trivial θ hθ
            hθC h2 (by omega) hf2 hL).1
      ·
        rcases (show f = 1 ∨ 2 ≤ f by omega) with rfl | hf2
        · rcases (show r = 2 ∨ 3 ≤ r by omega) with rfl | hr
          · exact (even_unitary_five_prime_field_central_two_cover_trivial θ hθ hθC h2 hL).1
          · exact (even_odd_dimensional_unitary_prime_field_central_two_cover_trivial θ hθ hθC h2
              hr hL).1
        · exact (even_odd_dimensional_unitary_catalog_perfect_central_two_cover_trivial θ hθ hθC
            h2 (by omega) hf2 hL).1

end CFSG.LocalAnalysis.ComponentInitial
