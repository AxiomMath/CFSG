module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.PrimeDivisorSubgroup
public import CFSG.LocalAnalysis.RankThreeUC.Section5.CentralHyperplaneWitness
public import CFSG.LocalAnalysis.RankThreeUC.Section5.RalphaExtraspecial
public import CFSG.LocalAnalysis.RankThreeUC.Section5.PbarDimension
public import CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialTwoOrderWidth
public import CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialTwoOddAutomizerWidth
public import CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialTwoFaithfulDimensionBound

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5.DimensionChain

open CFSG.LocalAnalysis.RankThreeUC.Section5

open CFSG.LocalAnalysis.RankThreeUC.Section5.Local

open CFSG.LocalAnalysis.RankThreeUC.ProofSupport

variable {G : Type} [Group G] [Finite G]

theorem exists_width_bound {p : ℕ} {P T B : Subgroup G} {e : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (hc : ExtraspecialBinaryActionCounterexample G p P T B e ρ) (n : ℕ) (hn : Nat.card ↥P = p ^ (1 + 2 * n)) :
    ∃ w : ℕ, e ≤ 2 * w ∧ 2 ^ w ≤ 2 * n := by
  haveI : Fact p.Prime := ⟨hc.oddPrimeClassTwoAction.setting.prime⟩
  haveI : Fact (⁅⁅P, P⁆, P⁆ = ⊥) := ⟨hc.oddPrimeClassTwoAction.setting.class_le_two⟩
  haveI : Fact (Monoid.exponent ↥P = p) := ⟨hc.oddPrimeClassTwoAction.setting.exponent⟩
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact absurd hc.oddPrimeClassTwoAction.setting.odd (by decide)
  obtain ⟨q, hq, hqd, hdq, A, hAB, hA⟩ := PrimeDivisorSubgroup.exists_prime_subgroup hc
  obtain ⟨H, hH, hind, hQ, r, hr, v, hv, hrv⟩ :=
    CentralHyperplaneWitness.exists_hyperplane hc hq hAB hA
  set hinv := QInvariant.invariant hc hH with hinv_def
  have hRne : Ralpha p P T B A H hinv ≠ ⊥ := by
    intro hbot
    have hrK : r ∈ K P T B :=
      ((RstarCoprime.R_le hc hAB).trans le_sup_left) hr
    have hmem : beta p P T B H hinv ⟨r, hrK⟩ ∈ Ralpha p P T B A H hinv :=
      ⟨⟨r, hrK⟩, hr, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    apply hrv
    have := congrArg (fun f => ((f ⟨v, hv⟩ : Q p P T B H) : W P)) hmem
    simpa [beta_apply_coe] using this
  set J := Ralpha p P T B A H hinv with hJ
  obtain ⟨hE, C, hC⟩ := RalphaExtraspecial.extraspecial_and_automizer hc hq hAB hA hH hind hRne
  haveI : Finite (Q p P T B H ≃ₗ[ZMod p] Q p P T B H) :=
    Finite.of_injective (fun f : Q p P T B H ≃ₗ[ZMod p] Q p P T B H => (f : Q p P T B H → Q p P T B H))
      (fun f g h => LinearEquiv.ext fun x => congrFun h x)
  haveI : Finite J := inferInstanceAs (Finite ↥(Ralpha p P T B A H hinv))
  obtain ⟨w, -, hw⟩ := CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialTwoOrderWidth.exists_width J hE
  have hcard : Nat.card J = 2 ^ (1 + 2 * w) := by rw [hw]; ring_nf
  have hq2 : q ≠ 2 := by
    rintro rfl
    have he := hc.oddPrimeClassTwoAction.two_lt
    have h1 : 1 ≤ e / 2 := by omega
    have : 2 ∣ 2 ^ (e / 2) := dvd_pow_self 2 (by omega)
    have h3 : 2 ∣ 1 := (Nat.dvd_add_right this).1 hqd
    omega
  have hord := CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialTwoOddAutomizerWidth.order_le_twice_width hE hcard hq hq2 C hC
  refine ⟨w, ?_, ?_⟩
  · rw [← hdq, binaryMultiplicativeOrder_eq_orderOf]; exact hord
  · have hF : (2 : ZMod p) ≠ 0 := by
      intro h
      have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
      rw [ZMod.natCast_eq_zero_iff] at this
      exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).1 this)
    haveI : Module.Finite (ZMod p) (Q p P T B H) := Module.Finite.of_finite
    haveI : Module.Finite (ZMod p) (W P) := Module.Finite.of_finite
    let ι : Representation (ZMod p) J (Q p P T B H) :=
      { toFun := fun x => ((x : Q p P T B H ≃ₗ[ZMod p] Q p P T B H) :
          Q p P T B H →ₗ[ZMod p] Q p P T B H)
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hι : Function.Injective ι := by
      intro x y hxy
      apply Subtype.ext
      apply LinearEquiv.ext
      intro u
      exact congrArg (fun f => f u) hxy
    have h1 := CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialTwoFaithfulDimensionBound.dimension_lower_bound hF hE hcard ι hι
    have h2 : Module.finrank (ZMod p) (Q p P T B H) ≤ Module.finrank (ZMod p) (W P) :=
      Submodule.finrank_le _
    have h3 : Module.finrank (ZMod p) (W P) = 2 * n := PbarDimension.finrank_eq hc n hn
    omega

end CFSG.LocalAnalysis.RankThreeUC.Section5.DimensionChain
