module

public import CFSG.GH74.Generic.S3.OnlyInvT1
import CFSG.GH74.Generic.S3.PumpDiag

public section

namespace CFSG.GH74.Generic.S3

open Subgroup CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThreeCoreUniqueness.Helpers (perfectResidual perfectResidualOf
  finite_perfectResidualOf_isPerfect finite_perfectResidual_surjects_to_perfect_image)
open scoped commutatorElement

theorem exists_l3Cover_of_diag {X : Type} [Group X] [Finite X] {L : Subgroup X} {s : X}
    (hAB : ⁅L, conjSub s⁻¹ L⁆ = ⊥) {Q : Subgroup X} (hQperf : ⁅Q, Q⁆ = Q)
    (hQle : Q ≤ (swapDiag hAB).range) {K₀ : Type} [Group K₀] {p f : ℕ}
    (hc : IsL3Cover ↥Q K₀ p f) :
    ∃ E : Subgroup ↥L, IsL3Cover ↥E K₀ p f := by
  obtain ⟨π₀, hπ₀, hπ₀c⟩ := hc.cover
  set D : ↥L →* X := swapDiag hAB
  have hQperf' : Group.IsPerfect ↥Q := Subgroup.isPerfect_iff.mpr hQperf
  set E₀ : Subgroup ↥L := Q.comap D with hE₀
  let φ : ↥E₀ →* ↥Q := (D.comp E₀.subtype).codRestrict Q fun a => a.2
  have hφ : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    obtain ⟨a, ha⟩ := hQle hy
    exact ⟨⟨a, by rw [hE₀, Subgroup.mem_comap, ha]; exact hy⟩, Subtype.ext ha⟩
  have hφE : (perfectResidual ↥E₀).map φ = ⊤ :=
    finite_perfectResidual_surjects_to_perfect_image φ hφ
  set E : Subgroup ↥L := perfectResidualOf E₀
  have hEperf : Group.IsPerfect ↥E := finite_perfectResidualOf_isPerfect E₀
  have hEE₀ : E ≤ E₀ := Subgroup.map_subtype_le _
  have hEQ : ∀ e : ↥E, D (e : ↥L) ∈ Q := fun e => hEE₀ e.2
  let ψ₀ : ↥E →* ↥Q := (D.comp E.subtype).codRestrict Q hEQ
  have hψ₀ : Function.Surjective ψ₀ := by
    intro y
    have hy : y ∈ (perfectResidual ↥E₀).map φ := by rw [hφE]; trivial
    obtain ⟨a, ha, rfl⟩ := hy
    exact ⟨⟨(a : ↥L), ⟨a, ha, rfl⟩⟩, rfl⟩
  have hψ₀D : ∀ e : ↥E, ((ψ₀ e : ↥Q) : X) = D (e : ↥L) := fun e => rfl
  refine ⟨E, ⟨hc.prime, hc.ne_two, hc.big, hEperf, hc.model, π₀.comp ψ₀, hπ₀.comp hψ₀, ?_⟩⟩
  intro e he
  have hcen : ψ₀ e ∈ center ↥Q := hπ₀c he
  apply mem_center_of_perfect_of_commutator_mem_center hEperf
  intro b
  rw [Subgroup.mem_center_iff]
  intro g
  have hd1 : ψ₀ (e * b * e⁻¹ * b⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← Subgroup.mem_center_iff.1 hcen (ψ₀ b)]
    group
  have hDker : ((e * b * e⁻¹ * b⁻¹ : ↥E) : ↥L) ∈ D.ker := by
    rw [MonoidHom.mem_ker]
    simpa [hψ₀D] using congrArg (fun y : ↥Q => (y : X)) hd1
  exact Subtype.ext
    (Subgroup.mem_center_iff.1 (ker_swapDiag_le_center hAB hDker) (g : ↥L))

end CFSG.GH74.Generic.S3
