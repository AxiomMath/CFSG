module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.FamilyJ1

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.OddIndex

open CFSG.Open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

theorem exists_noncomm_sylow_of_isLThreeTwo {X : Type} [Group X] [Finite X] (hX : IsLThreeTwo X)
    (S : Sylow 2 X) : ∃ a ∈ (S : Subgroup X), ∃ b ∈ (S : Subgroup X), a * b ≠ b * a := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, -, ⟨φ⟩⟩ := hasDihedralSylowTwo_of_isLThreeTwo hX S
  have hfac : (168 : ℕ).factorization 2 = 3 := by
    rw [Nat.factorization_def _ Nat.prime_two]; decide +kernel
  have hS : Nat.card (S : Subgroup X) = 8 := by
    rw [Sylow.card_eq_multiplicity, isLThreeTwo_card_eq hX, hfac]; norm_num
  have hm : 2 ^ m = 4 := by
    have h1 := Nat.card_congr φ.toEquiv
    rw [hS, DihedralGroup.nat_card] at h1
    omega
  generalize 2 ^ m = n at φ hm
  subst hm
  refine ⟨((φ.symm (DihedralGroup.r 1) : (S : Subgroup X)) : X), (φ.symm (DihedralGroup.r 1)).2,
    ((φ.symm (DihedralGroup.sr 0) : (S : Subgroup X)) : X), (φ.symm (DihedralGroup.sr 0)).2, ?_⟩
  intro h
  have h' : φ.symm (DihedralGroup.r 1) * φ.symm (DihedralGroup.sr 0) =
      φ.symm (DihedralGroup.sr 0) * φ.symm (DihedralGroup.r 1) := Subtype.ext h
  rw [← map_mul, ← map_mul] at h'
  have := φ.symm.injective h'
  revert this
  decide

theorem exists_noncomm_two_subgroup_of_isLThreeTwo {K : Type} [Group K] [Finite K]
    {Y : Subgroup K} (hY : IsLThreeTwo (↥Y ⧸ CFSG.pCore 2 ↥Y)) :
    ∃ R : Subgroup K, R ≤ Y ∧ IsPGroup 2 R ∧ ∃ a ∈ R, ∃ b ∈ R, a * b ≠ b * a := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  classical
  let S₀ : Sylow 2 (↥Y ⧸ CFSG.pCore 2 ↥Y) := default
  obtain ⟨a, ha, b, hb, hab⟩ := exists_noncomm_sylow_of_isLThreeTwo hY S₀
  obtain ⟨a', rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥Y) a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥Y) b
  have hker : IsPGroup 2 (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)).ker := by
    rw [QuotientGroup.ker_mk']
    exact CFSG.pCore_isPGroup
  have hR' : IsPGroup 2 ((S₀ : Subgroup (↥Y ⧸ CFSG.pCore 2 ↥Y)).comap
      (QuotientGroup.mk' (CFSG.pCore 2 ↥Y))) :=
    IsPGroup.comap_of_ker_isPGroup S₀.isPGroup' _ hker
  refine ⟨((S₀ : Subgroup (↥Y ⧸ CFSG.pCore 2 ↥Y)).comap
      (QuotientGroup.mk' (CFSG.pCore 2 ↥Y))).map Y.subtype, Subgroup.map_subtype_le _,
    hR'.map _, (a' : K), Subgroup.mem_map.mpr ⟨a', ha, rfl⟩, (b' : K),
    Subgroup.mem_map.mpr ⟨b', hb, rfl⟩, ?_⟩
  intro h
  apply hab
  have : a' * b' = b' * a' := Subtype.ext h
  rw [← map_mul, ← map_mul, this]

end CFSG.AGLEmbeddingD2.McLaughlin.OddIndex
