module

public import CFSG.ClassicalInvolution.Generic.SL2Anticommute
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19Q

open CFSG.ClassicalInvolution.Generic
open scoped MatrixGroups

variable {G : Type} [Group G]

def cosetStab (N : Subgroup G) (l : G) : Subgroup G where
  carrier := {b | b ∈ Subgroup.normalizer (N : Set G) ∧ l⁻¹ * (b * l * b⁻¹) ∈ N}
  one_mem' := ⟨Subgroup.one_mem _, by simp⟩
  mul_mem' := by
    rintro b₁ b₂ ⟨hb₁N, hb₁⟩ ⟨hb₂N, hb₂⟩
    refine ⟨Subgroup.mul_mem _ hb₁N hb₂N, ?_⟩
    have h2 : b₁ * (l⁻¹ * (b₂ * l * b₂⁻¹)) * b₁⁻¹ ∈ N :=
      (Subgroup.mem_normalizer_iff.mp hb₁N _).mp hb₂
    have e : l⁻¹ * (b₁ * b₂ * l * (b₁ * b₂)⁻¹) =
        (l⁻¹ * (b₁ * l * b₁⁻¹)) * (b₁ * (l⁻¹ * (b₂ * l * b₂⁻¹)) * b₁⁻¹) := by group
    rw [e]
    exact N.mul_mem hb₁ h2
  inv_mem' := by
    rintro b ⟨hbN, hb⟩
    refine ⟨Subgroup.inv_mem _ hbN, ?_⟩
    have h2 : b⁻¹ * (l⁻¹ * (b * l * b⁻¹)) * b⁻¹⁻¹ ∈ N :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hbN) _).mp hb
    have e : l⁻¹ * (b⁻¹ * l * b⁻¹⁻¹) = (b⁻¹ * (l⁻¹ * (b * l * b⁻¹)) * b⁻¹⁻¹)⁻¹ := by group
    rw [e]
    exact N.inv_mem h2

theorem exists_mul_mem_centralizer_of_odd {N : Subgroup G} (hN : Odd (Nat.card N)) {y l : G}
    (hy2 : IsPGroup 2 (Subgroup.zpowers y)) (hyN : y ∈ Subgroup.normalizer (N : Set G))
    (hl : l⁻¹ * (y * l * y⁻¹) ∈ N) : ∃ o ∈ N, y * (l * o) = (l * o) * y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hB : Subgroup.zpowers y ≤ cosetStab N l := Subgroup.zpowers_le.mpr ⟨hyN, hl⟩
  have hact : ∀ b ∈ Subgroup.zpowers y, ∀ o ∈ N, l⁻¹ * (b * (l * o) * b⁻¹) ∈ N := by
    intro b hb o ho
    obtain ⟨hbN, hbl⟩ := hB hb
    have e : l⁻¹ * (b * (l * o) * b⁻¹) = (l⁻¹ * (b * l * b⁻¹)) * (b * o * b⁻¹) := by group
    rw [e]
    exact N.mul_mem hbl ((Subgroup.mem_normalizer_iff.mp hbN o).mp ho)
  let : MulAction ↥(Subgroup.zpowers y) ↥N :=
    { smul := fun b o => ⟨l⁻¹ * ((b : G) * (l * (o : G)) * (b : G)⁻¹), hact b b.2 o o.2⟩
      one_smul := fun o => Subtype.ext (by
        change l⁻¹ * ((1 : G) * (l * (o : G)) * (1 : G)⁻¹) = (o : G)
        group)
      mul_smul := fun b₁ b₂ o => Subtype.ext (by
        change l⁻¹ * (((b₁ : G) * (b₂ : G)) * (l * (o : G)) * ((b₁ : G) * (b₂ : G))⁻¹) =
          l⁻¹ * ((b₁ : G) * (l * (l⁻¹ * ((b₂ : G) * (l * (o : G)) * (b₂ : G)⁻¹))) *
            (b₁ : G)⁻¹)
        group) }
  have hodd : ¬ 2 ∣ Nat.card ↥N := by
    obtain ⟨k, hk⟩ := hN
    rintro ⟨m, hm⟩
    omega
  obtain ⟨o₀, ho₀⟩ := hy2.nonempty_fixed_point_of_prime_not_dvd_card ↥N hodd
  refine ⟨o₀, o₀.2, ?_⟩
  have h1 : l⁻¹ * (y * (l * (o₀ : G)) * y⁻¹) = (o₀ : G) :=
    congrArg Subtype.val (ho₀ ⟨y, Subgroup.mem_zpowers y⟩)
  calc y * (l * (o₀ : G)) = l * (l⁻¹ * (y * (l * (o₀ : G)) * y⁻¹)) * y := by group
    _ = l * (o₀ : G) * y := by rw [h1]

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19Q
