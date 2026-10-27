module

public import CFSG.HardMathSupport.Solomon.Coordinator.B3Spor3Phi
public import CFSG.Assembly.RankThreeEvenDefs

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.ComponentClassification.OuterAutomorphisms

theorem b3SporPair_of_centralizer_phi {name : TauCeti.SporadicName} {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hOut : SporadicOuterLeTwo)
    (h : ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S],
      Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic name).Group) →
        ∀ s : S, orderOf s = p → B3Phi p (Subgroup.centralizer ({s} : Set S))) :
    B3SporPair name p := by
  intro S _ _ hs hnc he β hβ
  have := hs
  have : Fact p.Prime := ⟨hp⟩
  have hcen : Subgroup.center S = ⊥ := center_eq_bot_of_isSimpleGroup hnc
  have hout : Nat.card (Outer S) ≤ 2 := hOut S hs hnc name he
  obtain ⟨s, rfl, hsp⟩ := exists_conj_of_pow hp hp2 hcen hout β hβ
  by_cases hs1 : s = 1
  · subst hs1
    rw [map_one]
    exact layer_comm_one p
  · have hord : orderOf s = p := orderOf_eq_prime hsp hs1
    rw [fixSubgroup_conj]
    exact h S he s hord

theorem map_centralizer_mulEquiv {S M : Type*} [Group S] [Group M] (e : S ≃* M) (s : S) :
    (Subgroup.centralizer ({s} : Set S)).map e.toMonoidHom =
      Subgroup.centralizer ({e s} : Set M) := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [← map_mul, ← map_mul, hz]
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    apply e.injective
    rw [map_mul, map_mul, e.apply_symm_apply, hy]

theorem b3SporPair_of_model {name : TauCeti.SporadicName} (hOut : SporadicOuterLeTwo)
    (M : Type) [Group M] [Finite M]
    (hM : Nonempty (M ≃* (TauCeti.CFSGIndex.sporadic name).Group))
    (h : ∀ x : M, orderOf x = 3 → B3Phi 3 (Subgroup.centralizer ({x} : Set M))) :
    B3SporPair name 3 := by
  refine b3SporPair_of_centralizer_phi Nat.prime_three (by norm_num) hOut ?_
  intro S _ _ _ he s hs
  let e : S ≃* M := he.some.trans hM.some.symm
  have ho : orderOf (e s) = 3 := by simp [hs]
  have h1 := h (e s) ho
  rw [← map_centralizer_mulEquiv e s] at h1
  exact (b3Phi_map_iff Nat.prime_three e.toMonoidHom e.injective).1 h1

theorem map_centralizer_subtype {G : Type*} [Group G] (P : Subgroup G) (x : P) :
    (Subgroup.centralizer ({x} : Set P)).map P.subtype =
      Subgroup.centralizer ({(x : G)} : Set G) ⊓ P := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_inf,
    Subgroup.subtype_apply]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨congrArg Subtype.val hz, z.2⟩
  · rintro ⟨hy, hyP⟩
    exact ⟨⟨y, hyP⟩, Subtype.ext hy, rfl⟩

theorem b3Phi_centralizer_of_perm {G : Type*} [Group G] [Finite G] (P : Subgroup G)
    (h : ∀ x ∈ P, orderOf x = 3 → B3Phi 3 (Subgroup.centralizer ({x} : Set G) ⊓ P)) :
    ∀ x : P, orderOf x = 3 → B3Phi 3 (Subgroup.centralizer ({x} : Set P)) := by
  intro x hx
  rw [← b3Phi_map_iff Nat.prime_three P.subtype P.subtype_injective, map_centralizer_subtype]
  exact h x x.2 (by rw [Subgroup.orderOf_coe]; exact hx)

end CFSG.HardMathSupport.Solomon.Coordinator
