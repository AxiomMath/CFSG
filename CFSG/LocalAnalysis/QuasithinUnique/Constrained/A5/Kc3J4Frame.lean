module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyBinary
public import CFSG.Sporadic.J4.QT2LocCntProofBase

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT
  CFSG.Sporadic.J4.QT2

theorem exists_fixed_of_pgroup_odd {G X : Type*} [Group G] [MulAction G X] (V : Subgroup G)
    (hV : IsPGroup 2 V) (S : Set X) (hS : S.Finite) (hmap : ∀ v ∈ V, ∀ p ∈ S, v • p ∈ S)
    (hodd : ¬ 2 ∣ S.ncard) : ∃ p ∈ S, ∀ v ∈ V, v • p = p := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let T : SubMulAction ↥V X :=
    { carrier := S
      smul_mem' := fun v p hp => hmap v v.2 p hp }
  have : Finite ↥T := hS.to_subtype
  have hmod := IsPGroup.card_modEq_card_fixedPoints (p := 2) hV ↥T
  have hcard : Nat.card ↥T = S.ncard := Nat.card_coe_set_eq S
  have hne : (MulAction.fixedPoints ↥V ↥T).ncard ≠ 0 := by
    intro h0
    rw [hcard, Nat.card_coe_set_eq, h0] at hmod
    exact hodd (Nat.modEq_zero_iff_dvd.1 hmod)
  obtain ⟨q, hq⟩ := Set.nonempty_of_ncard_ne_zero hne
  refine ⟨(q : X), q.2, fun v hv => ?_⟩
  have h2 : (⟨v, hv⟩ : ↥V) • q = q := (MulAction.mem_fixedPoints.1 hq) ⟨v, hv⟩
  have h3 := congrArg Subtype.val h2
  exact h3

@[expose] def Pts : Set Row := {p | ∃ g : J, g • w₀ = p}

@[expose] def OmV (V : Subgroup J) : Set Row := {p | p ∈ Pts ∧ ∀ v ∈ V, v • p = p}

theorem smul_mem_pts {n : J} {p : Row} (hp : p ∈ Pts) : n • p ∈ Pts := by
  obtain ⟨g, rfl⟩ := hp
  exact ⟨n * g, mul_smul n g w₀⟩

theorem smul_mem_omV {V : Subgroup J} {n : J} (hn : n ∈ Subgroup.normalizer (V : Set J)) {p : Row}
    (hp : p ∈ OmV V) : n • p ∈ OmV V := by
  refine ⟨smul_mem_pts hp.1, fun v hv => ?_⟩
  have hv' : n⁻¹ * v * n ∈ V := by
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem hn) v).1 hv
    simpa using this
  calc v • (n • p) = (v * n) • p := (mul_smul v n p).symm
    _ = (n * (n⁻¹ * v * n)) • p := by rw [show v * n = n * (n⁻¹ * v * n) by group]
    _ = n • ((n⁻¹ * v * n) • p) := mul_smul _ _ _
    _ = n • p := by rw [hp.2 _ hv']

end CFSG.QuasithinUnique.A5
