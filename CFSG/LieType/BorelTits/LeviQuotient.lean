module

public import CFSG.LieType.BorelTits.CentralQuotient
import CFSG.Open.StatedAPI

public section

namespace CFSG.LieType.BorelTits

open CFSG.Open

theorem card_map_dvd_card_inf_map_mul {G G' : Type*} [Group G] [Group G'] [Finite G]
    (π : G →* G') {T O : Subgroup G} {X : ℕ}
    (hT : Nat.card ↥⁅T, T⁆ ∣ Nat.card ↥(⁅T, T⁆ ⊓ O) * X)
    (hS : commutator ↥(T.map π) = ⊤) :
    Nat.card ↥(T.map π) ∣ Nat.card ↥(T.map π ⊓ O.map π) * X := by
  let D : Subgroup G := ⁅T, T⁆
  let S : Subgroup G' := T.map π
  let R : Subgroup G' := O.map π
  let M : Subgroup G := D ⊓ R.comap π
  let L : Subgroup G := D ⊓ π.ker
  change Nat.card D ∣ Nat.card ↥(D ⊓ O) * X at hT
  change Nat.card S ∣ Nat.card ↥(S ⊓ R) * X
  have hSD : D.map π = S := by
    have hSS : ⁅S, S⁆ = S := by
      rw [← Subgroup.map_subtype_commutator S, hS, Subgroup.map_top, Subgroup.range_subtype]
    simpa only [D, S, Subgroup.map_commutator] using hSS
  have hMR : M.map π = S ⊓ R := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨by rw [← hSD]; exact Subgroup.mem_map_of_mem π hx.1,
        Subgroup.mem_comap.mp hx.2⟩
    · rintro ⟨hyS, hyO⟩
      rw [← hSD] at hyS
      obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hyS
      exact ⟨x, ⟨hx, Subgroup.mem_comap.mpr (by simpa [hxy] using hyO)⟩, hxy⟩
  have hker_le : π.ker ≤ R.comap π := by
    intro x hx
    rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hx]
    exact R.one_mem
  have hLM : L ≤ M := fun x hx => ⟨hx.1, hker_le hx.2⟩
  have hle : D ⊓ O ≤ M := by
    intro x hx
    exact ⟨hx.1, Subgroup.mem_comap.mpr (Subgroup.mem_map_of_mem π hx.2)⟩
  have hL_eq : L = π.ker ⊓ M := by
    dsimp only [L, M]
    rw [← inf_assoc, inf_eq_left.mpr (inf_le_left.trans hker_le)]
    exact inf_comm _ _
  have hL' : L = π.ker ⊓ D := by
    dsimp only [L]
    exact inf_comm _ _
  have hLD : L.relIndex D = Nat.card S := by
    rw [hL', Subgroup.inf_relIndex_right (H := π.ker) (K := D),
      Subgroup.relIndex_ker (f := π), hSD]
  have hLMrel : L.relIndex M = Nat.card ↥(S ⊓ R) := by
    rw [hL_eq, Subgroup.inf_relIndex_right (H := π.ker) (K := M),
      Subgroup.relIndex_ker (f := π), hMR]
  have hcardS : Nat.card S = Nat.card ↥(S ⊓ R) * M.relIndex D := by
    rw [← hLD, ← Subgroup.relIndex_mul_relIndex L M D hLM inf_le_left, hLMrel]
  have hMD : M.relIndex D ∣ X := by
    have h1 : M.relIndex D ∣ (D ⊓ O).relIndex D :=
      Subgroup.relIndex_dvd_of_le_left (L := D) hle
    refine h1.trans ?_
    have hcard : Nat.card D = Nat.card ↥(D ⊓ O) * (D ⊓ O).relIndex D := by
      have h := Subgroup.relIndex_mul_card (H := D ⊓ O) (K := D)
      rw [inf_eq_left.mpr inf_le_left, mul_comm] at h
      exact h.symm
    rw [hcard] at hT
    exact Nat.dvd_of_mul_dvd_mul_left (Nat.card_pos (α := ↥(D ⊓ O))) hT
  rw [hcardS]
  exact Nat.mul_dvd_mul_left _ hMD

theorem statedScalars_subgroupOf_coprime_card {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Finite K] {r : ℕ} [Fact r.Prime] [CharP K r] (H : Subgroup (GL ι K)) :
    Nat.Coprime (Nat.card ((StatedScalars ι K).subgroupOf H)) r := by
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Fact.out]
  intro hdvd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' r hdvd
  have hxr : x ^ r = 1 := hx ▸ pow_orderOf_eq_one x
  obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.mp x.2
  have hcr : Matrix.GeneralLinearGroup.scalar ι c ^ r = 1 := by
    rw [hc]
    simpa using congrArg (fun y : (StatedScalars ι K).subgroupOf H => ((y : H) : GL ι K)) hxr
  have hx1 : x = 1 := Subtype.ext (Subtype.ext (hc ▸ scalar_eq_one_of_pow_eq_one c hcr))
  rw [hx1, orderOf_one] at hx
  exact (Fact.out : r.Prime).one_lt.ne hx

theorem exists_isPGroup_map_eq_statedProj {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Finite K] {r : ℕ} [Fact r.Prime] [CharP K r] (H : Subgroup (GL ι K))
    {A : Subgroup (StatedProj H)} (hA : IsPGroup r A) :
    ∃ A₀ : Subgroup ↥H, IsPGroup r A₀ ∧
      A₀.map (QuotientGroup.mk' ((StatedScalars ι K).subgroupOf H)) = A ∧
      Subgroup.normalizer (A₀ : Set ↥H) =
        (Subgroup.normalizer (A : Set (StatedProj H))).comap
          (QuotientGroup.mk' ((StatedScalars ι K).subgroupOf H)) := by
  obtain ⟨A₀, hA₀, hmap⟩ :=
    exists_isPGroup_map_eq ((StatedScalars ι K).subgroupOf H) hA
  refine ⟨A₀, hA₀, hmap, ?_⟩
  rw [normalizer_eq_comap_normalizer_map ((StatedScalars ι K).subgroupOf H)
    (CFSG.Open.StatedAPI.statedScalars_subgroupOf_le_center H)
    (statedScalars_subgroupOf_coprime_card H) hA₀, hmap]

end CFSG.LieType.BorelTits
