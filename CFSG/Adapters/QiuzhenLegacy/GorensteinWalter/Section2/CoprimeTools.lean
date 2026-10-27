module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConj

public section

namespace GL83

universe u

open CFSG
open scoped commutatorElement

theorem commutator_double_eq_self {G : Type u} [Group G] [Finite G]
    (P K : Subgroup G) (hPK : P ≤ Subgroup.normalizer (K : Set G))
    (hcop : Nat.Coprime (Nat.card P) (Nat.card (↥K))) (hsolv : Group.IsSolvable K) :
    ⁅⁅K, P⁆, P⁆ = ⁅K, P⁆ := by
  classical
  let : Subgroup.Normalizes P K := ⟨hPK⟩
  let : MulDistribMulAction (↥P) (↥K) :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer P K hPK
  let C : Subgroup (↥K) := commutatorAction (A := ↥P) (G := ↥K)
  have hCmap : C.map K.subtype = ⁅K, P⁆ :=
    commutatorAction_subgroup_conj_map_eq_commutator K P hPK
  have hC2eq : commutatorAction₂ (A := ↥P) (G := ↥K) = C :=
    commutatorAction₂_eq_commutatorAction_of_solvable_coprime
      (G := ↥K) (A := ↥P) hsolv hcop
  have hXle : ⁅⁅K, P⁆, P⁆ ≤ ⁅K, P⁆ := by
    exact (Subgroup.le_normalizer_iff_commutator_le_left).mp
      (Subgroup.normalizer_commutator_ge_right K P)
  have hcomm₂_le :
      (commutatorAction₂ (A := ↥P) (G := ↥K)).map K.subtype ≤ ⁅⁅K, P⁆, P⁆ := by
    let S : Set (↥K) := {x : ↥K | ∃ a : ↥P, ∃ k : ↥K, k ∈ C ∧ x = k⁻¹ * (a • k)}
    calc
      (commutatorAction₂ (A := ↥P) (G := ↥K)).map K.subtype =
          (Subgroup.closure S).map K.subtype := by
            rfl
      _ = Subgroup.closure (K.subtype '' S) := by
            simpa using (MonoidHom.map_closure (f := K.subtype) S)
      _ ≤ ⁅⁅K, P⁆, P⁆ := by
            refine (Subgroup.closure_le (K := ⁅⁅K, P⁆, P⁆)).2 ?_
            rintro _ ⟨y, hy, rfl⟩
            rcases hy with ⟨a, k, hkC, rfl⟩
            have hkX : (k : G) ∈ ⁅K, P⁆ := by
              rw [← hCmap]
              exact Subgroup.mem_map.mpr ⟨k, hkC, rfl⟩
            have hgen : ⁅((k : ↥K) : G)⁻¹, (a : G)⁆ ∈ ⁅⁅K, P⁆, P⁆ :=
              Subgroup.commutator_mem_commutator (H₁ := ⁅K, P⁆) (H₂ := P)
                (Subgroup.inv_mem (H := ⁅K, P⁆) hkX) a.2
            simpa [commutatorElement_def,
              Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe,
              mul_assoc] using hgen
  apply le_antisymm hXle
  intro x hx
  have hx₂ : x ∈ (commutatorAction₂ (A := ↥P) (G := ↥K)).map K.subtype := by
    rw [hC2eq, hCmap]
    exact hx
  exact hcomm₂_le hx₂

end GL83
