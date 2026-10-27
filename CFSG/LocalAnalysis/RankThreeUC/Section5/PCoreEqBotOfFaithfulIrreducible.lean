module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import Mathlib.RepresentationTheory.Irreducible
import TauCeti.RepresentationTheory.Irreducible
import TauCeti.RepresentationTheory.PGroupInvariants

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5

theorem pCore_eq_bot_of_faithful_irreducible {k G V : Type*} [Field k] [Group G] [Finite G]
    [AddCommGroup V] [Module k V] (p : ℕ) [Fact p.Prime] [CharP k p] (ρ : Representation k G V)
    (hρ : Function.Injective ρ) (hirr : ρ.IsIrreducible) : CFSG.pCore p G = ⊥ := by
  haveI : Nontrivial V := hirr.nontrivial
  have hNp : IsPGroup p (CFSG.pCore p G) := CFSG.pCore_isPGroup
  have hfix : Representation.invariants (ρ.comp (CFSG.pCore p G).subtype) ≠ ⊥ :=
    Representation.invariants_ne_bot_of_forall_pow_eq_one p (ρ.comp (CFSG.pCore p G).subtype)
      fun g => by
        obtain ⟨n, hn⟩ := hNp g
        refine ⟨n, ?_⟩
        rw [← map_pow]
        have h1 : g ^ p ^ n = 1 := hn
        simp [h1]
  let R : Subrepresentation ρ :=
    ⟨Representation.invariants (ρ.comp (CFSG.pCore p G).subtype), fun g v hv => by
      rw [Representation.mem_invariants] at hv ⊢
      intro n
      have hn' : g⁻¹ * (n : G) * g ∈ CFSG.pCore p G := by
        have := (CFSG.pCore_normal (p := p) (G := G)).conj_mem n n.2 g⁻¹
        simpa using this
      have h1 : ρ n (ρ g v) = ρ g (ρ (g⁻¹ * (n : G) * g) v) := by
        rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
        congr 2
        group
      show ρ (n : G) (ρ g v) = ρ g v
      rw [h1]
      have := hv ⟨g⁻¹ * (n : G) * g, hn'⟩
      change ρ (g⁻¹ * (n : G) * g) v = v at this
      rw [this]⟩
  rcases hirr.eq_bot_or_eq_top R with hbot | htop
  · exact absurd (congrArg Subrepresentation.toSubmodule hbot) hfix
  · have htop' : Representation.invariants (ρ.comp (CFSG.pCore p G).subtype) = ⊤ :=
      congrArg Subrepresentation.toSubmodule htop
    rw [eq_bot_iff]
    intro n hn
    rw [Subgroup.mem_bot]
    apply hρ
    rw [map_one]
    ext v
    have hv : v ∈ Representation.invariants (ρ.comp (CFSG.pCore p G).subtype) := by
      rw [htop']
      trivial
    rw [Representation.mem_invariants] at hv
    exact hv ⟨n, hn⟩

end CFSG.LocalAnalysis.RankThreeUC.Section5
