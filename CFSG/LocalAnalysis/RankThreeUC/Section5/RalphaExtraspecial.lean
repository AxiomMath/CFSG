module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.RstarSpecial
public import CFSG.LocalAnalysis.RankThreeUC.Section5.RalphaSpecial
public import CFSG.LocalAnalysis.RankThreeUC.Section5.CentralImageOrder
public import CFSG.LocalAnalysis.RankThreeUC.Section3.CoprimeSpecialGroups.CommPowPow
import all CFSG.LocalAnalysis.RankThreeUC.Section3.CoprimeSpecialGroups.CommPowPow

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5.RalphaExtraspecial

open CFSG.LocalAnalysis.RankThreeUC.Section5

open CFSG.LocalAnalysis.RankThreeUC.Section5.Local

open CFSG.LocalAnalysis.RankThreeUC.Section5.Quotient

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem extraspecial_and_automizer {p : ℕ} {P T B : Subgroup G} {e : ℕ} {V : Type}
    [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (hc : ExtraspecialBinaryActionCounterexample G p P T B e ρ) {q : ℕ} (hq : q.Prime) {A : Subgroup G}
    (hAB : A ≤ B) (hA : Nat.card A = q) {H : Subgroup (MulAut ↥P)} (hH : H ≤ Z P T B)
    (hindex : (H.subgroupOf (Z P T B)).index = 2)
    (hRne : haveI : Fact p.Prime := ⟨hc.oddPrimeClassTwoAction.setting.prime⟩
      haveI : Fact (⁅⁅P, P⁆, P⁆ = ⊥) := ⟨hc.oddPrimeClassTwoAction.setting.class_le_two⟩
      haveI : Fact (Monoid.exponent ↥P = p) := ⟨hc.oddPrimeClassTwoAction.setting.exponent⟩
      Ralpha p P T B A H (QInvariant.invariant hc hH) ≠ ⊥) :
    haveI : Fact p.Prime := ⟨hc.oddPrimeClassTwoAction.setting.prime⟩
    haveI : Fact (⁅⁅P, P⁆, P⁆ = ⊥) := ⟨hc.oddPrimeClassTwoAction.setting.class_le_two⟩
    haveI : Fact (Monoid.exponent ↥P = p) := ⟨hc.oddPrimeClassTwoAction.setting.exponent⟩
    CFSG.IsExtraspecialPGroup 2
        ↥(Ralpha p P T B A H (QInvariant.invariant hc hH)) ∧
      ∃ C : Subgroup (MulAut ↥(Ralpha p P T B A H (QInvariant.invariant hc hH))),
        Nat.card C = q := by
  haveI : Fact p.Prime := ⟨hc.oddPrimeClassTwoAction.setting.prime⟩
  haveI : Fact (⁅⁅P, P⁆, P⁆ = ⊥) := ⟨hc.oddPrimeClassTwoAction.setting.class_le_two⟩
  haveI : Fact (Monoid.exponent ↥P = p) := ⟨hc.oddPrimeClassTwoAction.setting.exponent⟩
  obtain ⟨hsp, hnab, hDE, hcardA, hnorm⟩ := RalphaSpecial.«structure» hc hq hAB hA hH hRne
  obtain ⟨_, _, hRZ⟩ := RstarSpecial.structure hc hq hAB hA
  set hinv := QInvariant.invariant hc hH with hinv_def
  set J := Ralpha p P T B A H hinv with hJ
  set Aa := Aalpha p P T B A H hinv with hAa
  have hAB' : Bstar P A ≤ K P T B := (RstarCoprime.Bstar_mono hAB).trans le_sup_right
  have hRK : R P T B A ≤ K P T B :=
    (RstarCoprime.R_le hc hAB).trans le_sup_left
  set β := beta p P T B H hinv with hβ
  set E := (R P T B A).subgroupOf (K P T B) with hE
  have hZK := CentralImageOrder.Z_le_K P T B
  have hcard2 := CentralImageOrder.card_le_two hc hH hindex
  have hRR : ⁅R P T B A, R P T B A⁆ ≤ Z P T B := by
    rw [← Subgroup.map_subtype_commutator]; exact hRZ
  haveI : Finite (Q p P T B H) := by
    haveI : Finite P := inferInstance
    haveI : Finite (Pbar P) := inferInstanceAs (Finite (P ⧸ _))
    haveI : Finite (W P) := inferInstanceAs (Finite (Additive (Pbar P)))
    infer_instance
  haveI : Finite (Q p P T B H ≃ₗ[ZMod p] Q p P T B H) := by
    refine Finite.of_injective (fun f : Q p P T B H ≃ₗ[ZMod p] Q p P T B H => (f : _ → _))
      (fun f g h => LinearEquiv.ext (fun x => congrFun h x))
  have hJ2 : IsPGroup 2 J :=
    ((RstarCoprime.isPGroup hc hAB).comap_subtype (K := K P T B)).map β
  have hcommJ : ⁅J, J⁆ ≤ ((Z P T B).subgroupOf (K P T B)).map β := by
    have h1 : ⁅J, J⁆ = (⁅E, E⁆).map β := by
      rw [hJ, Ralpha, Subgroup.map_commutator]
    rw [h1]
    refine Subgroup.map_mono ?_
    intro x hx
    have : (x : MulAut ↥P) ∈ ⁅R P T B A, R P T B A⁆ := by
      have hmap : ⁅E, E⁆.map (K P T B).subtype = ⁅R P T B A, R P T B A⁆ := by
        rw [Subgroup.map_commutator, hE, Subgroup.map_subgroupOf_eq_of_le hRK]
      rw [← hmap]; exact ⟨x, hx, rfl⟩
    exact hRR this
  have hCle2 : Nat.card (⁅J, J⁆ : Subgroup _) ≤ 2 := (Subgroup.card_le_of_le hcommJ).trans hcard2
  have hCne : ⁅J, J⁆ ≠ ⊥ := by
    intro h
    apply hnab
    refine ⟨⟨fun a b => ?_⟩⟩
    have h1 := Subgroup.commutator_mem_commutator a.2 b.2
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact Subtype.ext h1
  have hC2 : Nat.card (⁅J, J⁆ : Subgroup _) = 2 := by
    have := (Subgroup.one_lt_card_iff_ne_bot (⁅J, J⁆ : Subgroup _)).mpr hCne
    omega
  have hinjJ := J.subtype_injective
  obtain ⟨hs1, hs2⟩ : _ ∧ _ := hsp
  have hcc : (Subgroup.center ↥J) = commutator ↥J := Subgroup.map_injective hinjJ hs1
  have hcf : (Subgroup.center ↥J) = frattini ↥J := Subgroup.map_injective hinjJ hs2
  refine ⟨⟨hJ2, hcc.symm, hcf.symm, ?_⟩, ?_⟩
  · rw [hcc, Nat.card_congr ((commutator ↥J).equivMapOfInjective _ hinjJ).toEquiv,
      Subgroup.map_subtype_commutator]
    exact hC2
  · haveI : Fact (Nat.card Aa).Prime := ⟨hcardA ▸ hq⟩
    let φ : Aa →* MulAut ↥J :=
      (Subgroup.normalizerMonoidHom J).comp (Subgroup.inclusion hnorm)
    have hker : φ.ker = ⊥ := by
      rcases φ.ker.eq_bot_or_eq_top_of_prime_card with h | h
      · exact h
      · exfalso
        apply hRne
        have : ⁅J, Aa⁆ = ⊥ := by
          rw [eq_bot_iff, Subgroup.commutator_le]
          intro g hg a ha
          have h1 : (⟨a, ha⟩ : Aa) ∈ φ.ker := by rw [h]; trivial
          rw [MonoidHom.mem_ker] at h1
          have h2 := congrArg (fun f : MulAut ↥J => (f ⟨g, hg⟩ : J).1) h1
          simp [φ] at h2
          rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
          exact (mul_inv_eq_iff_eq_mul.1 h2).symm
        exact hDE.symm.trans this
    have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).1 hker
    refine ⟨φ.range, ?_⟩
    rw [← hcardA]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

end CFSG.LocalAnalysis.RankThreeUC.Section5.RalphaExtraspecial
