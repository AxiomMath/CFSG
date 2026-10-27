module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.QInvariant

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5.RalphaSpecial

open CFSG.LocalAnalysis.RankThreeUC.Section5

open CFSG.LocalAnalysis.RankThreeUC.Section5.Local

open CFSG.LocalAnalysis.RankThreeUC.Section5.Quotient

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem «structure» {p : ℕ} {P T B : Subgroup G} {e : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (hc : ExtraspecialBinaryActionCounterexample G p P T B e ρ) {q : ℕ} (hq : q.Prime) {A : Subgroup G}
    (hAB : A ≤ B) (hA : Nat.card A = q) {H : Subgroup (MulAut ↥P)} (hH : H ≤ Z P T B)
    (hRne : haveI : Fact p.Prime := ⟨hc.oddPrimeClassTwoAction.setting.prime⟩
      haveI : Fact (⁅⁅P, P⁆, P⁆ = ⊥) := ⟨hc.oddPrimeClassTwoAction.setting.class_le_two⟩
      haveI : Fact (Monoid.exponent ↥P = p) := ⟨hc.oddPrimeClassTwoAction.setting.exponent⟩
      Ralpha p P T B A H (QInvariant.invariant hc hH) ≠ ⊥) :
    haveI : Fact p.Prime := ⟨hc.oddPrimeClassTwoAction.setting.prime⟩
    haveI : Fact (⁅⁅P, P⁆, P⁆ = ⊥) := ⟨hc.oddPrimeClassTwoAction.setting.class_le_two⟩
    haveI : Fact (Monoid.exponent ↥P = p) := ⟨hc.oddPrimeClassTwoAction.setting.exponent⟩
    Section3.CoprimeSpecialGroups.IsSpecialPGroup (Ralpha p P T B A H (QInvariant.invariant hc hH)) ∧
    ¬ IsMulCommutative (Ralpha p P T B A H (QInvariant.invariant hc hH)) ∧
    ⁅Ralpha p P T B A H (QInvariant.invariant hc hH),
      Aalpha p P T B A H (QInvariant.invariant hc hH)⁆ =
      Ralpha p P T B A H (QInvariant.invariant hc hH) ∧
    Nat.card (Aalpha p P T B A H (QInvariant.invariant hc hH)) = q ∧
    Aalpha p P T B A H (QInvariant.invariant hc hH) ≤
      Subgroup.normalizer (Ralpha p P T B A H (QInvariant.invariant hc hH) :
        Set (Q p P T B H ≃ₗ[ZMod p] Q p P T B H)) := by
  haveI : Fact p.Prime := ⟨hc.oddPrimeClassTwoAction.setting.prime⟩
  haveI : Fact (⁅⁅P, P⁆, P⁆ = ⊥) := ⟨hc.oddPrimeClassTwoAction.setting.class_le_two⟩
  haveI : Fact (Monoid.exponent ↥P = p) := ⟨hc.oddPrimeClassTwoAction.setting.exponent⟩
  set hinv := QInvariant.invariant hc hH with hinv_def
  have hqp : q ≠ p := PrimeActionFixedFree.q_ne_p hc hq hAB hA
  have hq2 : q ≠ 2 := PrimeActionFixedFree.q_ne_two hc hAB hA
  have hp2 : p ≠ 2 := by
    have := hc.oddPrimeClassTwoAction.setting.odd
    rintro rfl
    exact absurd this (by decide)
  have hKle : Subgroup.normalizer (P : Set G) = ⊤ :=
    Subgroup.normalizer_eq_top_iff.mpr hc.faithfulBinaryIrreducibleAction.normal
  haveI : Finite (Q p P T B H) := by
    haveI : Finite P := inferInstance
    haveI : Finite (Pbar P) := inferInstanceAs (Finite (P ⧸ _))
    haveI : Finite (W P) := inferInstanceAs (Finite (Additive (Pbar P)))
    infer_instance
  haveI : Finite (Q p P T B H ≃ₗ[ZMod p] Q p P T B H) := by
    refine Finite.of_injective (fun f : Q p P T B H ≃ₗ[ZMod p] Q p P T B H => (f : _ → _))
      (fun f g h => LinearEquiv.ext (fun x => congrFun h x))
  set ρ' : Representation (ZMod p) (Q p P T B H ≃ₗ[ZMod p] Q p P T B H) (Q p P T B H) :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom with hρ'
  have hρinj : Function.Injective ρ' := fun f g h => LinearEquiv.ext (fun x => by
    have := congrArg (fun φ : Q p P T B H →ₗ[ZMod p] Q p P T B H => φ x) h
    simpa [hρ'] using this)
  set β := beta p P T B H hinv with hβ
  have hAK : Bstar P A ≤ K P T B :=
    (RstarCoprime.Bstar_mono hAB).trans le_sup_right
  have hRK : R P T B A ≤ K P T B :=
    (RstarCoprime.R_le hc hAB).trans le_sup_left
  set A' := (Bstar P A).subgroupOf (K P T B) with hA'
  set R' := (R P T B A).subgroupOf (K P T B) with hR'
  have hcardA' : Nat.card A' = q := by
    rw [hA']
    rw [← PrimeActionFixedFree.card_image hc hq hAB hA]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAK).toEquiv
  have hβfix : ∀ k : K P T B, ∀ v : Q p P T B H, ρ' (β k) v = betaRep p P T B H hinv k v := by
    intro k v
    apply Subtype.ext
    exact beta_apply_coe p P T B H hinv k v
  have hfix := QInvariant.fixedSpace_eq_bot hc hq hAB hA hH
  have hCV : (⨅ d ∈ Aalpha p P T B A H hinv, LinearMap.ker (ρ' d - LinearMap.id)) =
      (⊥ : Submodule (ZMod p) (Q p P T B H)) := by
    rw [eq_bot_iff, ← hfix]
    intro v hv
    rw [Submodule.mem_iInf] at hv
    rw [BinaryRepresentations.mem_fixedSpace_iff]
    intro k hk
    have := hv (β k)
    rw [Submodule.mem_iInf] at this
    have h2 := this ⟨k, hk, rfl⟩
    rw [LinearMap.mem_ker] at h2
    have h3 : ρ' (β k) v = v := by simpa [hρ', sub_eq_zero] using h2
    rw [← hβfix]; exact h3
  have hAne : Aalpha p P T B A H hinv ≠ ⊥ := by
    intro hbot
    apply hRne
    have hsub : Subsingleton (Q p P T B H) := by
      refine ⟨fun x y => ?_⟩
      have hz : ∀ v : Q p P T B H, v = 0 := by
        intro v
        have : v ∈ BinaryRepresentations.fixedSpace (betaRep p P T B H hinv) A' := by
          rw [BinaryRepresentations.mem_fixedSpace_iff]
          intro k hk
          have hmem : β k ∈ Aalpha p P T B A H hinv := ⟨k, hk, rfl⟩
          rw [hbot, Subgroup.mem_bot] at hmem
          rw [← hβfix, hmem]
          rfl
        rw [hfix] at this
        exact (Submodule.mem_bot _).1 this
      rw [hz x, hz y]
    haveI : Subsingleton (Q p P T B H ≃ₗ[ZMod p] Q p P T B H) :=
      ⟨fun f g => LinearEquiv.ext (fun x => Subsingleton.elim _ _)⟩
    exact Subgroup.eq_bot_of_subsingleton _
  have hcardA : Nat.card (Aalpha p P T B A H hinv) = q := by
    have hd : Nat.card (Aalpha p P T B A H hinv) ∣ q := by
      rw [← hcardA']
      exact Subgroup.card_map_dvd _ _
    rcases (Nat.dvd_prime hq).1 hd with h | h
    · exfalso; apply hAne
      exact (Subgroup.card_eq_one).1 h
    · exact h
  have hRq : IsPGroup 2 (Ralpha p P T B A H hinv) :=
    ((RstarCoprime.isPGroup hc hAB).comap_subtype (K := K P T B)).map β
  have hcomm' : ⁅R', A'⁆ = R' := by
    apply Subgroup.map_injective (K P T B).subtype_injective
    rw [Subgroup.map_commutator, hR', hA', Subgroup.map_subgroupOf_eq_of_le hRK,
      Subgroup.map_subgroupOf_eq_of_le hAK]
    exact RstarCoprime.generated hc hq hAB hA
  have hDE : ⁅Aalpha p P T B A H hinv, Ralpha p P T B A H hinv⁆ =
      Ralpha p P T B A H hinv := by
    rw [Subgroup.commutator_comm]
    unfold Ralpha Aalpha
    rw [← Subgroup.map_commutator, hcomm']
  obtain ⟨n, hn⟩ := hRq.exists_card_eq
  have hpF : ∀ m : ℕ, m.Prime → m ≠ p → (m : ZMod p) ≠ 0 := by
    intro m hm hmp h0
    rw [ZMod.natCast_eq_zero_iff] at h0
    exact hmp ((Nat.prime_dvd_prime_iff_eq (Fact.out) hm).1 h0).symm
  have hEF : ((Nat.card (Ralpha p P T B A H hinv) : ℕ) : ZMod p) ≠ 0 := by
    rw [hn]
    push_cast
    exact pow_ne_zero _ (by exact_mod_cast hpF 2 Nat.prime_two (Ne.symm hp2))
  have hrF : ((q : ℕ) : ZMod p) ≠ 0 := hpF q hq hqp
  obtain ⟨hsp, _⟩ := CFSG.GroupTheory.CoprimeActionSupport.FixedFreePrimeGeneratedPGroupSpecial.special_and_center
    ρ' hρinj Nat.prime_two hq (Ne.symm hq2) _ hcardA hCV _ hRne hRq hEF hrF hDE
  refine ⟨hsp, ?_, ?_, hcardA, ?_⟩
  · exact CFSG.GroupTheory.CoprimeActionSupport.FixedFreePrimeGeneratedPGroupSpecial.nonabelian
      ρ' hρinj Nat.prime_two hq (Ne.symm hq2) _ hcardA hCV _ hRne hRq hEF hrF hDE
  · exact (Subgroup.commutator_comm _ _).trans hDE
  · rw [Subgroup.le_normalizer_iff_commutator_le_right, hDE]

end CFSG.LocalAnalysis.RankThreeUC.Section5.RalphaSpecial
