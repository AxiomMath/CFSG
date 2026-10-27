module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.SpecialCommutatorCenterEqCentralizerAndExponentPowerTwo
public import CFSG.LinearAlgebra.CoprimeActions.CommSpaceSubrepresentation
public import CFSG.LocalAnalysis.RankThreeUC.Section5.RstarCoprime

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5.QInvariant

open CFSG.LocalAnalysis.RankThreeUC.Section5

open CFSG.LocalAnalysis.RankThreeUC.Section5.Local

open CFSG.LinearAlgebra.CoprimeActions.CommSpaceSubrepresentation

variable {G : Type} [Group G] [Finite G]

theorem K_centralizes_Z {p : ℕ} {P T B : Subgroup G} {e : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (hc : ExtraspecialBinaryActionCounterexample G p P T B e ρ) :
    ∀ k ∈ K P T B, ∀ z ∈ Z P T B, k * z = z * k := by
  have h513 := (special_commutator_center_eq_centralizer_and_exponent_power_two hc).1.2
  intro k hk z hz
  have hle : K P T B ≤ Subgroup.centralizer (Z P T B : Set (MulAut ↥P)) := by
    refine sup_le ?_ ?_
    · intro s hs z hz
      obtain ⟨c, hc', rfl⟩ := hz
      have := Subgroup.mem_center_iff.mp hc' ⟨s, hs⟩
      exact (congrArg Subtype.val this).symm
    · intro b hb z hz
      have hz' : z ∈ Sstar P T B ⊓ Subgroup.centralizer (Bstar P B : Set (MulAut ↥P)) := by
        rw [← h513]; exact hz
      exact ((Subgroup.mem_centralizer_iff.mp hz'.2) b hb).symm
  exact (Subgroup.mem_centralizer_iff.mp (hle hk) z hz).symm

theorem invariant {p : ℕ} {P T B : Subgroup G} {e : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (hc : ExtraspecialBinaryActionCounterexample G p P T B e ρ) {H : Subgroup (MulAut ↥P)} (hH : H ≤ Z P T B) :
    haveI : Fact p.Prime := ⟨hc.oddPrimeClassTwoAction.setting.prime⟩
    haveI : Fact (⁅⁅P, P⁆, P⁆ = ⊥) := ⟨hc.oddPrimeClassTwoAction.setting.class_le_two⟩
    haveI : Fact (Monoid.exponent ↥P = p) := ⟨hc.oddPrimeClassTwoAction.setting.exponent⟩
    ∀ k ∈ K P T B, ∀ v ∈ Q p P T B H, sigma p P k v ∈ Q p P T B H := by
  haveI : Fact p.Prime := ⟨hc.oddPrimeClassTwoAction.setting.prime⟩
  haveI : Fact (⁅⁅P, P⁆, P⁆ = ⊥) := ⟨hc.oddPrimeClassTwoAction.setting.class_le_two⟩
  haveI : Fact (Monoid.exponent ↥P = p) := ⟨hc.oddPrimeClassTwoAction.setting.exponent⟩
  intro k hk v hv
  rw [mem_Q] at hv ⊢
  refine ⟨commSpace_invariant (sigma p P) (Z P T B) (K_centralizes_Z hc k hk) hv.1, ?_⟩
  rw [BinaryRepresentations.mem_fixedSpace_iff] at hv ⊢
  intro h hh
  have hcomm := K_centralizes_Z hc k hk h (hH hh)
  have := hv.2 h hh
  calc sigma p P h (sigma p P k v) = sigma p P (h * k) v := by rw [map_mul]; rfl
    _ = sigma p P (k * h) v := by rw [hcomm]
    _ = sigma p P k (sigma p P h v) := by rw [map_mul]; rfl
    _ = sigma p P k v := by rw [this]

theorem fixedSpace_eq_bot {p : ℕ} {P T B : Subgroup G} {e : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (hc : ExtraspecialBinaryActionCounterexample G p P T B e ρ) {q : ℕ} (hq : q.Prime) {A : Subgroup G}
    (hAB : A ≤ B) (hA : Nat.card A = q) {H : Subgroup (MulAut ↥P)} (hH : H ≤ Z P T B) :
    haveI : Fact p.Prime := ⟨hc.oddPrimeClassTwoAction.setting.prime⟩
    haveI : Fact (⁅⁅P, P⁆, P⁆ = ⊥) := ⟨hc.oddPrimeClassTwoAction.setting.class_le_two⟩
    haveI : Fact (Monoid.exponent ↥P = p) := ⟨hc.oddPrimeClassTwoAction.setting.exponent⟩
    BinaryRepresentations.fixedSpace (betaRep p P T B H (invariant hc hH))
      ((Bstar P A).subgroupOf (K P T B)) = ⊥ := by
  haveI : Fact p.Prime := ⟨hc.oddPrimeClassTwoAction.setting.prime⟩
  haveI : Fact (⁅⁅P, P⁆, P⁆ = ⊥) := ⟨hc.oddPrimeClassTwoAction.setting.class_le_two⟩
  haveI : Fact (Monoid.exponent ↥P = p) := ⟨hc.oddPrimeClassTwoAction.setting.exponent⟩
  have hfree := PrimeActionFixedFree.fixedSpace_eq_bot hc hq hAB hA
  have hAK : Bstar P A ≤ K P T B :=
    (RstarCoprime.Bstar_mono hAB).trans le_sup_right
  rw [eq_bot_iff]
  intro v hv
  rw [Submodule.mem_bot]
  rw [BinaryRepresentations.mem_fixedSpace_iff] at hv
  have hv' : (v : W P) ∈ BinaryRepresentations.fixedSpace (sigma p P) (Bstar P A) := by
    rw [BinaryRepresentations.mem_fixedSpace_iff]
    intro a ha
    have := congrArg Subtype.val (hv ⟨a, hAK ha⟩ (Subgroup.mem_subgroupOf.mpr ha))
    exact this
  rw [hfree, Submodule.mem_bot] at hv'
  exact Subtype.ext hv'

end CFSG.LocalAnalysis.RankThreeUC.Section5.QInvariant
