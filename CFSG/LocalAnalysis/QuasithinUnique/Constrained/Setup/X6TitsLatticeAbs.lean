module

public import CFSG.Certificates.InvariantMerge
public import CFSG.CharacterTheory.Burnside
public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.QuasithinUnique.Setup.X6.TitsLat

open CFSG.Certificates

section Generic

variable {G Ω : Type*} [Group G]

theorem perm_inv_apply_self {Ω : Type*} (f : Equiv.Perm Ω) (x : Ω) : f⁻¹ (f x) = x := by simp

theorem phi_inv_apply {G Ω : Type*} [Group G] (φ : G →* Equiv.Perm Ω) (g : G) (x : Ω) :
    φ g⁻¹ (φ g x) = x := by
  rw [map_inv, perm_inv_apply_self]

abbrev stabAt (φ : G →* Equiv.Perm Ω) (b : Ω) : Subgroup G :=
  (MulAction.stabilizer (Equiv.Perm Ω) b).comap φ

theorem mem_stabAt {φ : G →* Equiv.Perm Ω} {b : Ω} {g : G} : g ∈ stabAt φ b ↔ φ g b = b :=
  Iff.rfl

def Delta (φ : G →* Equiv.Perm Ω) (b : Ω) (M : Subgroup G) : Set Ω := {x | ∃ m ∈ M, φ m b = x}

variable {φ : G →* Equiv.Perm Ω} {b : Ω} {M : Subgroup G}

theorem base_mem_Delta (φ : G →* Equiv.Perm Ω) (b : Ω) (M : Subgroup G) : b ∈ Delta φ b M :=
  ⟨1, M.one_mem, by simp⟩

theorem mem_iff_apply_mem (hM : stabAt φ b ≤ M) (g : G) : g ∈ M ↔ φ g b ∈ Delta φ b M := by
  constructor
  · intro hg
    exact ⟨g, hg, rfl⟩
  · rintro ⟨m, hm, hmg⟩
    have h : m⁻¹ * g ∈ stabAt φ b := by
      rw [mem_stabAt, map_mul, Equiv.Perm.mul_apply, ← hmg]
      exact phi_inv_apply φ m b
    have := M.mul_mem hm (hM h)
    simpa using this

theorem Delta_stable (hM : stabAt φ b ≤ M) {x : Ω} (hx : x ∈ Delta φ b M) {s : G}
    (hs : s ∈ stabAt φ b) : φ s x ∈ Delta φ b M := by
  obtain ⟨m, hm, rfl⟩ := hx
  exact ⟨s * m, M.mul_mem (hM hs) hm, by rw [map_mul, Equiv.Perm.mul_apply]⟩

theorem Delta_ncard : (Delta φ b M).ncard = (stabAt φ b).relIndex M := by
  let _ : MulAction M Ω := MulAction.compHom Ω (φ.comp M.subtype)
  have hst : MulAction.stabilizer M b = (stabAt φ b).subgroupOf M := by
    ext m
    exact Iff.rfl
  have horb : MulAction.orbit M b = Delta φ b M := by
    ext x
    constructor
    · rintro ⟨m, rfl⟩
      exact ⟨m, m.2, rfl⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨⟨m, hm⟩, rfl⟩
  rw [← horb, ← MulAction.index_stabilizer, hst]
  rfl

theorem ncard_Delta_dvd (hM : stabAt φ b ≤ M) : (Delta φ b M).ncard ∣ (stabAt φ b).index := by
  rw [Delta_ncard]
  exact Dvd.intro _ (Subgroup.relIndex_mul_index hM)

end Generic

section Solvable

theorem index_three_two_subgroup_solvable {P : Type*} [Group P] [Finite P] (Q : Subgroup P)
    (hQ : IsPGroup 2 Q) (hidx : Q.index = 3) : Group.IsSolvable P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ := MulAction.toPermHom P (P ⧸ Q) with hφ
  have hker : φ.ker ≤ Q := by
    rw [hφ, ← Subgroup.normalCore_eq_ker]
    exact Subgroup.normalCore_le Q
  have hK2 : IsPGroup 2 φ.ker := hQ.to_le hker
  have : Group.IsSolvable φ.ker := @IsNilpotent.to_isSolvable _ _ hK2.isNilpotent
  have hcardQ : Nat.card (P ⧸ Q) = 3 := by rw [← Subgroup.index_eq_card, hidx]
  have hperm : Nat.card (Equiv.Perm (P ⧸ Q)) = 2 ^ 1 * 3 ^ 1 := by
    rw [Nat.card_perm, hcardQ]
    rfl
  have : Group.IsSolvable (Equiv.Perm (P ⧸ Q)) := by
    let _ : Fintype (Equiv.Perm (P ⧸ Q)) := Fintype.ofFinite _
    exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
      Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card]; exact hperm)
  have : Group.IsSolvable φ.range := Group.isSolvable_of_isSolvable_injective (Subgroup.subtype_injective _)
  exact Group.isSolvable_of_ker_le_range φ.ker.subtype φ.rangeRestrict
    (by rw [MonoidHom.ker_rangeRestrict, Subgroup.range_subtype])

end Solvable

end CFSG.QuasithinUnique.Setup.X6.TitsLat
