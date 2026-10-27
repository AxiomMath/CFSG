module

public import CFSG.ClassicalInvolution.ModelFacts.OddCover.Cover
public import CFSG.LieType.Steinberg.CentralExt.Families
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix

public section

namespace CFSG.ClassicalInvolution.Q3.Q3Z

open CFSG.ClassicalInvolution.ModelFacts.OddCover CFSG.LieType.Steinberg
  CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

universe u v

theorem exists_section_of_coprime {R : Type u} {H : Type v} [Group R] [Group H] [Finite R]
    (ρ : R →* H) (hρ : Function.Surjective ρ)
    (hcop : Nat.Coprime (Nat.card ρ.ker) (Nat.card H)) : ∃ s : H →* R, ∀ x, ρ (s x) = x := by
  have hidx : ρ.ker.index = Nat.card H := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hρ, Subgroup.card_top]
  obtain ⟨C, hC⟩ := Subgroup.exists_right_complement'_of_coprime (N := ρ.ker)
    (by rw [hidx]; exact hcop)
  let φ : C →* H := ρ.comp C.subtype
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro c hc
    exact Subtype.ext (Subgroup.disjoint_def.mp hC.disjoint hc c.2)
  have hsurj : Function.Surjective φ := by
    intro h
    obtain ⟨r, rfl⟩ := hρ h
    obtain ⟨⟨⟨n, hn⟩, c⟩, hnc⟩ := hC.2 r
    refine ⟨c, ?_⟩
    have hn1 : ρ n = 1 := hn
    have : r = n * (c : R) := hnc.symm
    change ρ (c : R) = ρ r
    rw [this, map_mul, hn1, one_mul]
  let e : C ≃* H := MulEquiv.ofBijective φ ⟨hinj, hsurj⟩
  refine ⟨C.subtype.comp e.symm.toMonoidHom, fun x => ?_⟩
  change φ (e.symm x) = x
  exact e.apply_symm_apply x

theorem exists_lift_of_coprime {H : Type v} [Group H] [Finite H] {E : Type u} [Group E] [Finite E]
    {G : Type*} [Group G] (π : E →* G) (hπ : Function.Surjective π)
    (hcop : Nat.Coprime (Nat.card π.ker) (Nat.card H)) (α : H →* G) :
    ∃ β : H →* E, π.comp β = α := by
  have hcop' : Nat.Coprime (Nat.card (pullbackFst α π).ker) (Nat.card H) :=
    Nat.Coprime.coprime_dvd_left (card_ker_pullbackFst_dvd α π) hcop
  obtain ⟨s, hs⟩ := exists_section_of_coprime (pullbackFst α π) (pullbackFst_surjective hπ) hcop'
  refine ⟨(MonoidHom.snd H E).comp ((pullback α π).subtype.comp s), ?_⟩
  ext x
  have h1 : ((s x : pullback α π) : H × E).1 = x := hs x
  have h2 := mem_pullback.1 (s x).2
  rw [h1] at h2
  exact h2.symm

private theorem card_sl2_three : Nat.card SL(2, GaloisField 3 1) = 24 := by
  have hF : Nat.card (GaloisField 3 1) = 3 := by
    rw [GaloisField.card 3 1 one_ne_zero]
    norm_num
  rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hF]
  norm_num

theorem isPerfect_sp4_three : Group.IsPerfect (StatedSp 2 (GaloisField 3 1)) := by
  have hF : Nat.card (GaloisField 3 1) = 3 := by
    rw [GaloisField.card 3 1 one_ne_zero]
    norm_num
  exact (CFSG.LieType.Universal.Symplectic.isQuasisimple 2 (GaloisField 3 1) (by norm_num)
    (Or.inr (Or.inl ⟨hF, le_rfl⟩))).1

theorem sp4_three_noCover :
    NoCover.{0} (fun n => Odd n ∧ ¬ 3 ∣ n) (StatedSp 2 (GaloisField 3 1)) := by
  intro E _ _ _ π hπ hcen ⟨hodd, h3⟩
  have hcop : Nat.Coprime (Nat.card π.ker) (Nat.card SL(2, GaloisField 3 1)) := by
    rw [card_sl2_three, show (24 : ℕ) = 2 ^ 3 * 3 by norm_num]
    refine Nat.Coprime.mul_right (Nat.Coprime.pow_right 3 ?_) ?_
    · exact Nat.coprime_two_right.mpr hodd
    · exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3).symm
  have hlift : ∀ ρ : SL(2, GaloisField 3 1) →* StatedSp 2 (GaloisField 3 1),
      ∃ ρ' : SL(2, GaloisField 3 1) →* E, ∀ g, π (ρ' g) = ρ g := fun ρ => by
    obtain ⟨β, hβ⟩ := exists_lift_of_coprime π hπ hcop ρ
    exact ⟨β, fun g => DFunLike.congr_fun hβ g⟩
  obtain ⟨σ, hσ, -⟩ := sp_existsUnique_section_of_sl2_lift 2 hπ hcen h3 hlift
  have htop : σ.range = ⊤ := by
    refine eq_top_of_perfect_of_central hcen (S := σ.range) (Z := π.ker) fun e => ?_
    refine ⟨σ (π e), ⟨_, rfl⟩, (σ (π e))⁻¹ * e, ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hσ, inv_mul_cancel]
  rw [eq_bot_iff]
  intro c hc
  obtain ⟨x, rfl⟩ : c ∈ σ.range := by rw [htop]; trivial
  rw [MonoidHom.mem_ker, hσ] at hc
  rw [hc, map_one]
  exact Subgroup.one_mem _

end CFSG.ClassicalInvolution.Q3.Q3Z
