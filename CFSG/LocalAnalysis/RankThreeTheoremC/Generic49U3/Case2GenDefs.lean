module

import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.PSU3.Aut
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.PSU3.BorelTorus
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.PSU3.Torus
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Unitary
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Config

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def TypeTStruct {G : Type} [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (x : G)
    (J : Subgroup G) : Prop :=
  Nat.card (u3T P x J) = p ^ 3 ∧ (∀ t ∈ u3T P x J, t ^ p = 1) ∧ ¬ IsMulCommutative (u3T P x J) ∧ x ∉ J

@[expose] def TypeSDecomp {G : Type} [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (x : G)
    (J : Subgroup G) : Prop :=
  ∃ Z : Subgroup G, IsCyclic Z ∧ x ∈ Z ∧ Z ≤ u3S P x ∧
    (∀ z ∈ Z, ∀ t ∈ u3T P x J, z * t = t * z) ∧ u3T P x J ⊓ Z = ⊥ ∧
    u3T P x J ⊔ Z = u3S P x

@[expose] def TypeAutPCard (Typ : ℕ → ∀ (Q : Type) [Group Q], Prop) (p : ℕ) : Prop :=
  ∀ (K : Type) [Group K] [Finite K], Typ p K → Subgroup.center K = ⊥ →
    ∀ S : Subgroup (MulAut K), IsPGroup p S → Nat.card S ∣ p ^ 3

@[expose] def TypeTorusIrred (Typ : ℕ → ∀ (Q : Type) [Group Q], Prop) (p : ℕ) : Prop :=
  ∀ (K : Type) [Group K] [Finite K], Typ p K → ∀ T : Sylow p K, ∀ A : Subgroup K,
    A ≤ (T : Subgroup K) →
    (T : Subgroup K) ⊓ Subgroup.centralizer ((T : Subgroup K) : Set K) ≤ A →
    (∀ n ∈ Subgroup.normalizer ((T : Subgroup K) : Set K), ∀ a ∈ A, n * a * n⁻¹ ∈ A) →
    A = (T : Subgroup K) ⊓ Subgroup.centralizer ((T : Subgroup K) : Set K) ∨ A = (T : Subgroup K)

@[expose] def TypeTorusFpf (Typ : ℕ → ∀ (Q : Type) [Group Q], Prop) (p : ℕ) : Prop :=
  ∀ (K : Type) [Group K] [Finite K], Typ p K → ∀ T : Sylow p K, ∀ t ∈ (T : Subgroup K),
    (∀ n ∈ Subgroup.normalizer ((T : Subgroup K) : Set K),
      n * t * n⁻¹ * t⁻¹ ∈ (T : Subgroup K) ⊓ Subgroup.centralizer ((T : Subgroup K) : Set K)) →
    t ∈ (T : Subgroup K) ⊓ Subgroup.centralizer ((T : Subgroup K) : Set K)

@[expose] def TypeTorusOnCenter (Typ : ℕ → ∀ (Q : Type) [Group Q], Prop) (p : ℕ) : Prop :=
  ∀ (K : Type) [Group K] [Finite K], Typ p K → ∀ T : Sylow p K, ∀ c ∈ (T : Subgroup K),
    c ∈ Subgroup.centralizer ((T : Subgroup K) : Set K) → c ≠ 1 → ∀ k : ℤ, ¬ (p : ℤ) ∣ k →
      ∃ n ∈ Subgroup.normalizer ((T : Subgroup K) : Set K), n * c * n⁻¹ = c ^ k

@[expose] def TypeBorelMax (Typ : ℕ → ∀ (Q : Type) [Group Q], Prop) (p : ℕ) : Prop :=
  ∀ (K : Type) [Group K] [Finite K], Typ p K → ∀ S : Sylow p K, ∀ H : Subgroup K,
    Subgroup.normalizer ((S : Subgroup K) : Set K) ≤ H →
      H = Subgroup.normalizer ((S : Subgroup K) : Set K) ∨ H = ⊤

theorem typeAutPCard_u3 {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) :
    TypeAutPCard (fun p K _ => IsU3Pred p K) p :=
  fun _ _ _ hK _ S hS => u3_aut_pgroup_card hp5 hK S hS

theorem typeTorusIrred_u3 {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) :
    TypeTorusIrred (fun p K _ => IsU3Pred p K) p :=
  fun _ _ _ hK T _ h1 h2 h3 => u3_torus_irreducible hp5 hK T h1 h2 h3

theorem typeTorusFpf_u3 {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) :
    TypeTorusFpf (fun p K _ => IsU3Pred p K) p :=
  fun _ _ _ hK T _ ht h => u3_torus_fpf hp5 hK T ht h

theorem typeTorusOnCenter_u3 {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) :
    TypeTorusOnCenter (fun p K _ => IsU3Pred p K) p :=
  fun _ _ _ hK T _ hcT hcZ hc1 k hk => u3_torus_on_center hp5 hK T hcT hcZ hc1 k hk

theorem typeBorelMax_u3 {p : ℕ} [Fact p.Prime] :
    TypeBorelMax (fun p K _ => IsU3Pred p K) p := by
  intro K _ _ hK S H hH
  obtain ⟨d, hd, -, he⟩ := u3Sylow_index_of_isU3Pred hK
  have hco : IsCoatom (Subgroup.normalizer ((S : Subgroup K) : Set K)) :=
    CFSG.AGLEmbedding.kFactUnitaryBorelMaximal K p d hd he S
  rcases hco.le_iff.mp hH with h | h
  · exact Or.inr h
  · exact Or.inl h

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3
