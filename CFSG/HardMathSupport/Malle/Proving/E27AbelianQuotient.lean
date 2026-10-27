module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.Data.Rat.Floor

public section

namespace CFSG.HardMathSupport.Malle.Proving

theorem card_le_card_inf_centralizer_of_hom_comm {G A : Type*} [Group G] [CommGroup A]
    {S : Subgroup G} [Finite S] (φ : S →* A) (hφ : Function.Surjective φ) {s : G} (hs : s ∈ S) :
    Nat.card A ≤ Nat.card ↥(S ⊓ Subgroup.centralizer ({s} : Set G)) := by
  have hr : Nat.card φ.range = Nat.card A := by
    rw [MonoidHom.range_eq_top_of_surjective φ hφ, Subgroup.card_top]
  have hsize : Nat.card φ.ker * Nat.card A = Nat.card S := by
    rw [← hr]
    exact Subgroup.card_ker_mul_card_range φ
  have horb : Nat.card (MulAction.orbit (ConjAct S) (⟨s, hs⟩ : S))
      * Nat.card (MulAction.stabilizer (ConjAct S) (⟨s, hs⟩ : S)) = Nat.card S := by
    rw [← Nat.card_prod]
    exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (ConjAct S) (⟨s, hs⟩ : S))
  have hker : ∀ t : ↥(MulAction.orbit (ConjAct S) (⟨s, hs⟩ : S)),
      t.1 * (⟨s, hs⟩ : S)⁻¹ ∈ φ.ker := by
    intro t
    obtain ⟨g, hg⟩ := (MulAction.mem_orbit_iff).mp t.2
    rw [ConjAct.smul_def] at hg
    rw [MonoidHom.mem_ker, ← hg, map_mul, map_mul, map_inv, map_inv]
    simp [mul_comm, mul_assoc]
  have horbK : Nat.card (MulAction.orbit (ConjAct S) (⟨s, hs⟩ : S)) ≤ Nat.card φ.ker := by
    refine Nat.card_le_card_of_injective
      (fun t => (⟨t.1 * (⟨s, hs⟩ : S)⁻¹, hker t⟩ : ↥φ.ker)) ?_
    intro t₁ t₂ h
    have h1 : t₁.1 * (⟨s, hs⟩ : S)⁻¹ = t₂.1 * (⟨s, hs⟩ : S)⁻¹ := congrArg Subtype.val h
    exact Subtype.ext (mul_right_cancel h1)
  have hmem : ∀ g : ↥(MulAction.stabilizer (ConjAct S) (⟨s, hs⟩ : S)),
      ((ConjAct.ofConjAct g.1 : S) : G) ∈ S ⊓ Subgroup.centralizer ({s} : Set G) := by
    intro g
    have hg : ConjAct.ofConjAct g.1 * (⟨s, hs⟩ : S) * (ConjAct.ofConjAct g.1)⁻¹
        = (⟨s, hs⟩ : S) := by
      have h := g.2
      rw [MulAction.mem_stabilizer_iff, ConjAct.smul_def] at h
      exact h
    have hc : ConjAct.ofConjAct g.1 * (⟨s, hs⟩ : S) = (⟨s, hs⟩ : S) * ConjAct.ofConjAct g.1 :=
      mul_inv_eq_iff_eq_mul.mp hg
    have hc' : ((ConjAct.ofConjAct g.1 : S) : G) * s = s * ((ConjAct.ofConjAct g.1 : S) : G) := by
      have h := congrArg Subtype.val hc
      simpa using h
    rw [Subgroup.mem_inf]
    refine ⟨(ConjAct.ofConjAct g.1 : S).2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact hc'.symm
  have hstab : Nat.card (MulAction.stabilizer (ConjAct S) (⟨s, hs⟩ : S))
      ≤ Nat.card ↥(S ⊓ Subgroup.centralizer ({s} : Set G)) := by
    have : Finite ↥(S ⊓ Subgroup.centralizer ({s} : Set G)) :=
      Finite.of_injective (fun z : ↥(S ⊓ Subgroup.centralizer ({s} : Set G)) =>
        (⟨z.1, (Subgroup.mem_inf.mp z.2).1⟩ : ↥S))
        (fun a b h => by
          have h' := congrArg Subtype.val h
          exact Subtype.ext h')
    refine Nat.card_le_card_of_injective
      (fun g => (⟨((ConjAct.ofConjAct g.1 : S) : G), hmem g⟩ :
        ↥(S ⊓ Subgroup.centralizer ({s} : Set G)))) ?_
    intro g₁ g₂ h
    have h1 := congrArg Subtype.val h
    have h2 : ConjAct.ofConjAct g₁.1 = ConjAct.ofConjAct g₂.1 := Subtype.ext h1
    exact Subtype.ext ((MulEquiv.injective ConjAct.ofConjAct) h2)
  have key : Nat.card φ.ker * Nat.card A
      ≤ Nat.card φ.ker * Nat.card (MulAction.stabilizer (ConjAct S) (⟨s, hs⟩ : S)) := by
    rw [hsize, ← horb]
    exact Nat.mul_le_mul_right _ horbK
  have hKpos : 0 < Nat.card φ.ker := Nat.card_pos
  exact (Nat.le_of_mul_le_mul_left key hKpos).trans hstab

theorem eighty_one_dvd_inf_centralizer_of_three_group {G A : Type*} [Group G] [CommGroup A]
    {S : Subgroup G} [Finite S] (hS : IsPGroup 3 S) (φ : S →* A) (hφ : Function.Surjective φ)
    {s : G} (hs : s ∈ S) (h81 : 81 ≤ Nat.card A) :
    81 ∣ Nat.card ↥(S ⊓ Subgroup.centralizer ({s} : Set G)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hle := card_le_card_inf_centralizer_of_hom_comm φ hφ hs
  have hfin : Finite ↥(S ⊓ Subgroup.centralizer ({s} : Set G)) :=
    Finite.of_injective (Subgroup.inclusion inf_le_left) (Subgroup.inclusion_injective _)
  have hC : IsPGroup 3 ↥(S ⊓ Subgroup.centralizer ({s} : Set G)) :=
    hS.of_injective (Subgroup.inclusion inf_le_left) (Subgroup.inclusion_injective _)
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hC
  have hC81 : 81 ≤ Nat.card ↥(S ⊓ Subgroup.centralizer ({s} : Set G)) := h81.trans hle
  have hn4 : 4 ≤ n := by
    by_contra hcon
    push Not at hcon
    rw [hn] at hC81
    have hle3 : 3 ^ n ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact absurd (hC81.trans hle3) (by norm_num)
  rw [hn, show (81 : ℕ) = 3 ^ 4 by norm_num]
  exact pow_dvd_pow 3 hn4

end CFSG.HardMathSupport.Malle.Proving

end
