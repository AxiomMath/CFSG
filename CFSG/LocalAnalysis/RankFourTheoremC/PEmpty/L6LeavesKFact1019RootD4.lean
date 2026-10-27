module

public import CFSG.LieType.Steinberg.TwistedD4.Local
public import CFSG.LieType.Steinberg.TwistedD4.Perfect
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd.Basic
public import CFSG.Blueprint.ChevalleyRoots
public import CFSG.LocalAnalysis.SectionRank.CentralLift

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Fact1019

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.TwistedD4

section Certified


theorem exists_isElemAbelian_twistedRootGroup {K : Type} [Field K] [Finite K] {p : ℕ}
    [Fact p.Prime] [CharP K p] {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c) {k : ℕ} (hk : 3 ≤ k)
    (hcard : Nat.card K = p ^ k) :
    ∃ E ≤ twistedRootGroup σ
        (Pi.single ⟨0, by decide⟩ 1 + 2 • Pi.single ⟨1, by decide⟩ 1 : Fin (Tag.rank .G2) → ℤ),
      IsElemAbelian p E ∧ p ^ 3 ≤ Nat.card E := by
  set β : Fin (Tag.rank .G2) → ℤ :=
    Pi.single ⟨0, by decide⟩ 1 + 2 • Pi.single ⟨1, by decide⟩ 1 with hβdef
  set γ : Fin d4.rank → ℤ := Pi.single (nd 2) 1 + Pi.single (nd 0) 1 + Pi.single (nd 1) 1
    with hγdef
  have hγ : IsRoot d4 γ := mem_rootFinset.1 (by decide +kernel)
  have hne : rho γ ≠ γ := by decide +kernel
  have hproj : proj γ = β := by decide +kernel
  have hβ : IsRoot .G2 β := mem_rootFinset.1 (by decide +kernel)
  have hmem : ∀ c : K, xOrbit σ γ c ∈ twistedRootSubgroupD4 σ β := fun c => by
    rw [← hproj]
    exact xOrbit_mem hσ hγ hne c
  let φ : Multiplicative K →* ↥(twistedGroup σ) :=
    MonoidHom.mk' (fun c => ⟨xOrbit σ γ c.toAdd,
      twistedRootSubgroupD4_le_twistedGroup σ hβ (hmem c.toAdd)⟩) fun a b =>
        Subtype.ext (by
          change xOrbit σ γ (a * b).toAdd = xOrbit σ γ a.toAdd * xOrbit σ γ b.toAdd
          rw [toAdd_mul]
          exact xOrbit_add σ hγ hne _ _)
  have hφinj : Function.Injective φ := fun a b h =>
    Multiplicative.toAdd.injective (xOrbit_injective σ hγ hne (congrArg Subtype.val h))
  refine ⟨φ.range, ?_, ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
  · rintro _ ⟨c, rfl⟩
    exact mem_twistedRootGroup σ |>.2 (hmem c.toAdd)
  · obtain ⟨a, ha⟩ := x.2
    obtain ⟨b, hb⟩ := y.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← ha, ← hb, ← map_mul, ← map_mul, mul_comm]
  · obtain ⟨a, rfl⟩ := MonoidHom.mem_range.1 hx
    rw [← map_pow, CFSG.SectionRank.ClassicalOdd.pow_char_eq_one (K := K) (p := p) a, map_one]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv, Nat.card_congr Multiplicative.toAdd,
      hcard]
    exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos hk

end Certified

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Fact1019
