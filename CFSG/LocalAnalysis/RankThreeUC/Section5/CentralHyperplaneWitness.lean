module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.RstarSpecial
public import CFSG.LocalAnalysis.RankThreeUC.Section5.CenterElementary
public import CFSG.LocalAnalysis.RankThreeUC.ProofSupport.CentralActionDetection.CentralActionDetection

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5.CentralHyperplaneWitness

open CFSG.LocalAnalysis.RankThreeUC.Section5

open CFSG.LocalAnalysis.RankThreeUC.Section5.Local

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_hyperplane {p : ℕ} {P T B : Subgroup G} {e : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (hc : ExtraspecialBinaryActionCounterexample G p P T B e ρ) {q : ℕ} (hq : q.Prime) {A : Subgroup G}
    (hAB : A ≤ B) (hA : Nat.card A = q) :
    haveI : Fact p.Prime := ⟨hc.oddPrimeClassTwoAction.setting.prime⟩
    haveI : Fact (⁅⁅P, P⁆, P⁆ = ⊥) := ⟨hc.oddPrimeClassTwoAction.setting.class_le_two⟩
    haveI : Fact (Monoid.exponent ↥P = p) := ⟨hc.oddPrimeClassTwoAction.setting.exponent⟩
    ∃ H : Subgroup (MulAut ↥P), H ≤ Z P T B ∧ (H.subgroupOf (Z P T B)).index = 2 ∧
      Q p P T B H ≠ ⊥ ∧ ∃ r ∈ R P T B A, ∃ v ∈ Q p P T B H, sigma p P r v ≠ v := by
  haveI : Fact p.Prime := ⟨hc.oddPrimeClassTwoAction.setting.prime⟩
  haveI : Fact (⁅⁅P, P⁆, P⁆ = ⊥) := ⟨hc.oddPrimeClassTwoAction.setting.class_le_two⟩
  haveI : Fact (Monoid.exponent ↥P = p) := ⟨hc.oddPrimeClassTwoAction.setting.exponent⟩
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact absurd hc.oddPrimeClassTwoAction.setting.odd (by decide)
  obtain ⟨_, hnab, hcomm⟩ := RstarSpecial.structure hc hq hAB hA
  have hne : commutator (R P T B A) ≠ ⊥ := by
    intro h
    apply hnab
    refine ⟨⟨fun a b => ?_⟩⟩
    have : ⁅a, b⁆ ∈ commutator (R P T B A) :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this
  obtain ⟨⟨z, hzc⟩, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  replace hz1 : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hzZ : (z : MulAut ↥P) ∈ Z P T B := hcomm ⟨z, hzc, rfl⟩
  have hz1' : (z : MulAut ↥P) ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hnt : ∃ v, sigma p P (z : MulAut ↥P) v ≠ v := by
    by_contra hcon
    push Not at hcon
    apply hz1'
    have hinj := SstarQuotientFaithful.injective hc
    have hzS : (z : MulAut ↥P) ∈ Sstar P T B := by
      obtain ⟨c, _, hc'⟩ := hzZ
      rw [← hc']; exact c.2
    have h1 : (CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialOddQuotientAutFaithfulness.quotientHom ↥P).comp
        (Sstar P T B).subtype ⟨_, hzS⟩ = 1 := by
      ext x
      have := hcon (Additive.ofMul x)
      rw [sigma_apply] at this
      exact congrArg Additive.toMul this
    have := hinj (h1.trans (map_one _).symm)
    exact congrArg Subtype.val this
  obtain ⟨H, hH, v, hv, hzv⟩ := CFSG.LocalAnalysis.RankThreeUC.ProofSupport.CentralActionDetection.exists_hyperplane
    (G := MulAut ↥P) hp2 (sigma p P) (Z P T B) (CenterElementary.isElemAbelian hc) hzZ hnt
  refine ⟨H, hH.1, hH.2, ?_, z, ?_, v, hv, hzv⟩
  · intro hbot
    apply hzv
    have : v = 0 := by
      have : v ∈ Q p P T B H := hv
      rw [hbot] at this
      exact this
    rw [this, map_zero]
  · exact z.2

end CFSG.LocalAnalysis.RankThreeUC.Section5.CentralHyperplaneWitness
