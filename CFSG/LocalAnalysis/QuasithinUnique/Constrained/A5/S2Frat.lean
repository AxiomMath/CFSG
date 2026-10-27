module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S2Basic
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.QuasithinUnique.A5.S2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3
open scoped commutatorElement

variable {G : Type} [Group G]

theorem cj_inf (g : G) (A B : Subgroup G) : cj g (A ⊓ B) = cj g A ⊓ cj g B :=
  map_equiv_inf (MulAut.conj g) A B

theorem cj_centralizer (g : G) (K : Subgroup G) :
    cj g (Subgroup.centralizer (K : Set G)) = Subgroup.centralizer (cj g K : Set G) :=
  (centralizer_map_equiv (MulAut.conj g) K).symm

theorem cj_frattiniOf (g : G) (X : Subgroup G) :
    cj g (frattiniOf X) = frattiniOf (cj g X) := by
  let e : ↥X ≃* ↥(cj g X) := (MulAut.conj g).subgroupMap X
  have h1 : (frattini ↥X).map e.toMonoidHom = frattini ↥(cj g X) :=
    CFSG.QuasithinUnique.Setup.Campbell.frattini_map_equiv e
  calc cj g (frattiniOf X)
      = (frattini ↥X).map ((MulAut.conj g).toMonoidHom.comp X.subtype) := by
        show ((frattini ↥X).map X.subtype).map (MulAut.conj g).toMonoidHom = _
        rw [Subgroup.map_map]
    _ = (frattini ↥X).map ((cj g X).subtype.comp e.toMonoidHom) :=
        congrArg (fun φ => (frattini ↥X).map φ) (MonoidHom.ext fun x => rfl)
    _ = ((frattini ↥X).map e.toMonoidHom).map (cj g X).subtype := (Subgroup.map_map _ _ _).symm
    _ = frattiniOf (cj g X) := by rw [h1]; rfl

theorem mem_normalizer_centralizer {g : G} {X : Subgroup G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) :
    g ∈ Subgroup.normalizer (Subgroup.centralizer (X : Set G) : Set G) := by
  rw [mem_normalizer_iff_cj, cj_centralizer, mem_normalizer_iff_cj.1 hg]

theorem frat_le_of_forall [Finite G] {P N : Subgroup G}
    (hcomm : ∀ x ∈ P, ∀ y ∈ P, x * y * x⁻¹ * y⁻¹ ∈ N) (hsq : ∀ x ∈ P, x ^ 2 ∈ N) :
    frattiniOf P ≤ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnorm : (N.subgroupOf P).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have h1 : (g : G) * (n : G) * (g : G)⁻¹ * (n : G)⁻¹ ∈ N := hcomm g g.2 n n.2
    have e : ((g * n * g⁻¹ : P) : G) = ((g : G) * (n : G) * (g : G)⁻¹ * (n : G)⁻¹) * (n : G) := by
      simp [mul_assoc]
    rw [e]
    exact N.mul_mem h1 hn⟩
  have h1 : frattini ↥P ≤ N.subgroupOf P :=
    CFSG.SectionRank.Ccomm.frattini_le_of_commutator_pow_mem (p := 2) (N.subgroupOf P)
      (fun a b => by
        rw [Subgroup.mem_subgroupOf]
        have e : ((⁅a, b⁆ : P) : G) = ⁅(a : G), (b : G)⁆ := map_commutatorElement P.subtype a b
        rw [e]
        exact hcomm a a.2 b b.2)
      (fun a => by
        rw [Subgroup.mem_subgroupOf]
        have e : ((a ^ 2 : P) : G) = (a : G) ^ 2 := by simp
        rw [e]
        exact hsq a a.2)
  rintro _ ⟨f, hf, rfl⟩
  exact Subgroup.mem_subgroupOf.mp (h1 hf)

end CFSG.QuasithinUnique.A5.S2
