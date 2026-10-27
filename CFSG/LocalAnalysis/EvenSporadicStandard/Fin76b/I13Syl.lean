module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def sylowOfMax {Θ P : Subgroup G} (hPΘ : P ≤ Θ) (hP : IsPGroup 2 P)
    (hmax : ∀ R : Subgroup G, IsPGroup 2 R → R ≤ Θ → P ≤ R → R ≤ P) : Sylow 2 ↥Θ :=
  ⟨P.subgroupOf Θ, hP.comap_subtype, fun {Q} hQ hle => by
    have hQp : IsPGroup 2 (Q.map Θ.subtype) := hQ.map _
    have hQΘ : Q.map Θ.subtype ≤ Θ := by
      rintro _ ⟨q, -, rfl⟩
      exact q.2
    have hPQ : P ≤ Q.map Θ.subtype := by
      intro s hs
      exact ⟨⟨s, hPΘ hs⟩, hle (mem_subgroupOf.2 hs), rfl⟩
    have hQP : Q.map Θ.subtype ≤ P := hmax _ hQp hQΘ hPQ
    exact le_antisymm (fun q hq => mem_subgroupOf.2 (hQP ⟨q, hq, rfl⟩)) hle⟩

omit [Finite G] in
theorem mem_sylowOfMax {Θ P : Subgroup G} (hPΘ : P ≤ Θ) (hP : IsPGroup 2 P)
    (hmax : ∀ R : Subgroup G, IsPGroup 2 R → R ≤ Θ → P ≤ R → R ≤ P) {x : ↥Θ} :
    x ∈ (sylowOfMax hPΘ hP hmax : Subgroup ↥Θ) ↔ (x : G) ∈ P := mem_subgroupOf

theorem not_two_dvd_relIndex_of_max {Θ P : Subgroup G} (hPΘ : P ≤ Θ) (hP : IsPGroup 2 P)
    (hmax : ∀ R : Subgroup G, IsPGroup 2 R → R ≤ Θ → P ≤ R → R ≤ P) :
    ¬ 2 ∣ P.relIndex Θ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (sylowOfMax hPΘ hP hmax).not_dvd_index

theorem sylow_conj {Θ P Q : Subgroup G} (hPΘ : P ≤ Θ) (hQΘ : Q ≤ Θ) (hP : IsPGroup 2 P)
    (hQ : IsPGroup 2 Q) (hPmax : ∀ R : Subgroup G, IsPGroup 2 R → R ≤ Θ → P ≤ R → R ≤ P)
    (hQmax : ∀ R : Subgroup G, IsPGroup 2 R → R ≤ Θ → Q ≤ R → R ≤ Q) :
    ∃ g ∈ Θ, ∀ x : G, x ∈ Q ↔ g⁻¹ * x * g ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥Θ (sylowOfMax hPΘ hP hPmax)
    (sylowOfMax hQΘ hQ hQmax)
  have key : ∀ y : ↥Θ, y ∈ (sylowOfMax hQΘ hQ hQmax : Subgroup ↥Θ) ↔
      g⁻¹ * y * g ∈ (sylowOfMax hPΘ hP hPmax : Subgroup ↥Θ) := by
    intro y
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp [MulAut.smul_def]
  refine ⟨g, g.2, fun x => ?_⟩
  constructor
  · intro hx
    have hxΘ : x ∈ Θ := hQΘ hx
    have := (key ⟨x, hxΘ⟩).1 ((mem_sylowOfMax hQΘ hQ hQmax).2 hx)
    exact (mem_sylowOfMax hPΘ hP hPmax).1 this
  · intro hx
    have hxΘ : x ∈ Θ := by
      have h1 : (g : G)⁻¹ * x * g ∈ Θ := hPΘ hx
      have := mul_mem (mul_mem g.2 h1) (inv_mem g.2)
      simpa [mul_assoc] using this
    refine (mem_sylowOfMax hQΘ hQ hQmax).1 ((key ⟨x, hxΘ⟩).2 ?_)
    exact (mem_sylowOfMax hPΘ hP hPmax).2 hx

end CFSG.EvenSporadicStandard.Fin76b
