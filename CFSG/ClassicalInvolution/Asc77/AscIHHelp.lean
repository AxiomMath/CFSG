module

public import CFSG.ClassicalInvolution.Asc77.AscIHLie
public import CFSG.ClassicalInvolution.ModelFacts.FundNoncentralMain

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

variable {p f : ℕ} [Fact p.Prime]

section Transfer

variable {M G : Type*} [Group M] [Group G]

theorem map_conj_eq_conjSub_map (ψ : M →* G) (g : M) (R : Subgroup M) :
    (R.map (MulAut.conj g).toMonoidHom).map ψ = conjSub (ψ g) (R.map ψ) := by
  unfold conjSub
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, map_mul, map_inv]

theorem injOn_of_ker_le_center {ψ : M →* G} (hker : ψ.ker ≤ Subgroup.center M) {R : Subgroup M}
    (hR : ∀ r ∈ R, (∀ y : M, r * y * r⁻¹ * y⁻¹ ∈ Subgroup.center M) → r = 1) :
    ∀ x ∈ R, ψ x = 1 → x = 1 := by
  intro x hx h1
  refine hR x hx fun y => ?_
  have hxc : x ∈ Subgroup.center M := hker h1
  have : x * y * x⁻¹ * y⁻¹ = 1 := by
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
    exact (Subgroup.mem_center_iff.mp hxc y).symm
  rw [this]
  exact Subgroup.one_mem _

theorem natCard_map_of_injOn (ψ : M →* G) {R : Subgroup M} (hinj : ∀ x ∈ R, ψ x = 1 → x = 1) :
    Nat.card (R.map ψ) = Nat.card R := by
  let e₀ : ↥R →* ↥(R.map ψ) :=
    (ψ.comp R.subtype).codRestrict (R.map ψ) (fun x => Subgroup.mem_map_of_mem ψ x.2)
  have he₀inj : Function.Injective e₀ := by
    intro x y hxy
    have hxy' : ψ x = ψ y := congrArg Subtype.val hxy
    have h1 : ψ ((x : M)⁻¹ * y) = 1 := by simp [map_mul, map_inv, hxy']
    exact Subtype.ext (inv_mul_eq_one.mp (hinj _ (R.mul_mem (R.inv_mem x.2) y.2) h1))
  have he₀surj : Function.Surjective e₀ := by
    rintro ⟨_, r, hr, rfl⟩
    exact ⟨⟨r, hr⟩, rfl⟩
  exact (Nat.card_congr (Equiv.ofBijective e₀ ⟨he₀inj, he₀surj⟩)).symm

theorem isPerfect_of_map (ψ : M →* G) {R : Subgroup M} (hinj : ∀ x ∈ R, ψ x = 1 → x = 1)
    (hperf : Group.IsPerfect (R.map ψ)) : Group.IsPerfect R := by
  rw [Subgroup.isPerfect_iff]
  refine le_antisymm ?_ ?_
  · rw [Subgroup.commutator_le]
    intro a ha b hb
    simp only [commutatorElement_def]
    exact R.mul_mem (R.mul_mem (R.mul_mem ha hb) (R.inv_mem ha)) (R.inv_mem hb)
  · intro x hx
    have h1 := (Subgroup.isPerfect_iff.mp hperf).symm
    rw [← Subgroup.map_commutator] at h1
    have h2 : ψ x ∈ ⁅R, R⁆.map ψ := h1 ▸ Subgroup.mem_map_of_mem ψ hx
    obtain ⟨y, hy, hyx⟩ := h2
    have hyR : y ∈ R := by
      have : ⁅R, R⁆ ≤ R := by
        rw [Subgroup.commutator_le]
        intro a ha b hb
        simp only [commutatorElement_def]
        exact R.mul_mem (R.mul_mem (R.mul_mem ha hb) (R.inv_mem ha)) (R.inv_mem hb)
      exact this hy
    have : x⁻¹ * y = 1 := hinj _ (R.mul_mem (R.inv_mem hx) hyR) (by simp [map_mul, map_inv, hyx])
    have hxy : x = y := inv_mul_eq_one.mp this
    exact hxy ▸ hy

end Transfer

section Conj

variable {X : Type*} [Group X]

theorem conjSub_rel_trans {A B C : Subgroup X} (h₁ : ∃ g, conjSub g A = B)
    (h₂ : ∃ g, conjSub g B = C) :
    ∃ g, conjSub g A = C := by
  obtain ⟨a, rfl⟩ := h₁
  obtain ⟨b, rfl⟩ := h₂
  exact ⟨b * a, conjSub_mul b a A⟩

theorem conjSub_rel_symm {A B : Subgroup X} (h : ∃ g, conjSub g A = B) : ∃ g, conjSub g B = A := by
  obtain ⟨a, rfl⟩ := h
  exact ⟨a⁻¹, conjSub_inv_conjSub a A⟩

end Conj

namespace OmegaLie

variable {G : Type} [Group G] {Ω : Set (Subgroup G)} (D : OmegaLie p f Ω)

theorem injOn_fund (i : Fin D.card) (hne : ¬ (D.tag i = .PSL ∧ D.rank i = 2))
    {T : Subgroup (D.model i).K}
    (hT : T ∈ fundamentalSubgroups (D.tag i) (D.model i).D) :
    ∀ x ∈ T, D.hom i x = 1 → x = 1 :=
  injOn_of_ker_le_center (D.ker_le_center i) fun r hr hcen =>
    ModelFacts.fundNoncentral_generic p (D.tag i) (D.rank i) (D.exp i) (D.isFundTag i)
      (D.admissible i) hne T hT r hr hcen

end OmegaLie

end CFSG.ClassicalInvolution.Asc77
