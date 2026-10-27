module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Suz
public import CFSG.Sporadic.Recognition.CoverTransfer

public section

namespace CFSG.EvenSporadicStandard.TwoSuz

open Subgroup
open CFSG.Sporadic.SuzOddCore (suzM suzT suzInv)
open CFSG.EvenSporadicStandard.HypOne.Suz (autEquiv autEquiv_apply cover_outer)
open CFSG.Sporadic.Recognition.CoverTransfer (sq_eq_sq_of_conj eq_of_mem_commutator)

section Induced

variable {L : Type} [Group L]

noncomputable def inducedHom (q : L →* suzM) (hq : Function.Surjective q) (φ : MulAut L)
    (hle : q.ker ≤ (q.comp φ.toMonoidHom).ker) : suzM →* suzM :=
  MonoidHom.liftOfSurjective q hq ⟨q.comp φ.toMonoidHom, hle⟩

theorem inducedHom_apply (q : L →* suzM) (hq : Function.Surjective q) (φ : MulAut L)
    (hle : q.ker ≤ (q.comp φ.toMonoidHom).ker) (l : L) :
    inducedHom q hq φ hle (q l) = q (φ l) :=
  MonoidHom.liftOfRightInverse_comp_apply q _ (Function.rightInverse_surjInv hq) _ l

end Induced

section Main


theorem foursGroupCondition_of_witness {L : Type} [Group L] [Finite L] [Group.IsPerfect L]
    (q : L →* suzM) (hq : Function.Surjective q) {t : L} (ht : t * t = 1)
    (hker : q.ker = zpowers t) (hcenter : center L = zpowers t) {x₁ : L} (hx₁ : x₁ * x₁ = 1)
    (hx₁q : q x₁ ≠ 1)
    (hw : ∀ i : ℕ, (i = 2 ∨ i = 3) → ∃ l c : suzM,
      (l : Equiv.Perm (Fin 1782)) * suzInv i * (l : Equiv.Perm (Fin 1782))⁻¹ * (suzInv i)⁻¹ =
        (c : Equiv.Perm (Fin 1782)) * (q x₁ : Equiv.Perm (Fin 1782)) *
          (c : Equiv.Perm (Fin 1782))⁻¹) :
    CFSG.EvenSmallLie.FoursGroupCondition L := by
  intro φ hφ2 hφout
  have hker_center : q.ker ≤ center L := hker ▸ hcenter.symm.le
  have hexp : ∀ c ∈ q.ker, c ^ 2 = 1 := by
    intro c hc
    rw [hker] at hc
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hc
    have ht2 : t ^ 2 = 1 := by rw [sq]; exact ht
    calc (t ^ k) ^ 2 = (t ^ 2) ^ k := by
          rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
      _ = 1 := by rw [ht2, one_zpow]
  have hφφ : ∀ l : L, φ (φ l) = l := fun l => by
    have := congrArg (fun ψ : MulAut L => ψ l) hφ2
    simpa using this
  have hφcenter : ∀ l ∈ center L, φ l ∈ center L := by
    intro l hl
    rw [mem_center_iff] at hl ⊢
    intro m
    obtain ⟨m', rfl⟩ := φ.surjective m
    rw [← map_mul, ← map_mul, hl m']
  have hle : q.ker ≤ (q.comp φ.toMonoidHom).ker := by
    intro l hl
    have h1 : φ l ∈ q.ker := by
      rw [hker, ← hcenter]
      exact hφcenter l (hker_center hl)
    exact h1
  have hα : ∀ l, inducedHom q hq φ hle (q l) = q (φ l) := inducedHom_apply q hq φ hle
  have hαα : ∀ m, inducedHom q hq φ hle (inducedHom q hq φ hle m) = m := by
    intro m
    obtain ⟨l, rfl⟩ := hq m
    rw [hα, hα, hφφ]
  let α : MulAut suzM := MonoidHom.toMulEquiv (inducedHom q hq φ hle) (inducedHom q hq φ hle)
    (MonoidHom.ext hαα) (MonoidHom.ext hαα)
  have hαapply : ∀ l, α (q l) = q (φ l) := hα
  obtain ⟨τ, hτ⟩ := autEquiv.surjective α
  have hτapply : ∀ l : L, ((q (φ l) : suzM) : Equiv.Perm (Fin 1782)) =
      (τ : Equiv.Perm (Fin 1782)) * (q l : Equiv.Perm (Fin 1782)) *
        (τ : Equiv.Perm (Fin 1782))⁻¹ := fun l => by
    rw [← hαapply l, ← hτ]
    exact autEquiv_apply τ (q l)
  have hττ : τ * τ = 1 := by
    refine autEquiv.injective ?_
    rw [map_mul, hτ, map_one]
    refine MulEquiv.ext fun m => ?_
    exact hαα m
  have hτM : (τ : Equiv.Perm (Fin 1782)) ∉ suzM := by
    intro hτM
    obtain ⟨l₀, hl₀⟩ := hq ⟨(τ : Equiv.Perm (Fin 1782)), hτM⟩
    refine hφout l₀ (MulEquiv.ext fun x => ?_)
    have hc : ∀ x : L, ((MulAut.conj l₀).toMonoidHom x)⁻¹ * φ.toMonoidHom x ∈ center L := by
      intro x
      rw [hcenter, ← hker]
      rw [MonoidHom.mem_ker, map_mul, map_inv]
      refine inv_mul_eq_one.2 ?_
      refine Subtype.ext ?_
      simp only [MulAut.conj_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, map_mul,
        map_inv, hl₀, Subgroup.coe_mul, Subgroup.coe_inv]
      exact (hτapply x).symm
    have := eq_of_mem_commutator (MulAut.conj l₀).toMonoidHom φ.toMonoidHom hc
      (x := x) (by rw [Group.isPerfect_def.1 inferInstance]; trivial)
    exact this.symm
  have hτT : (τ : Equiv.Perm (Fin 1782)) ∈ suzT := τ.2
  have hτ1 : (τ : Equiv.Perm (Fin 1782)) ≠ 1 := fun h => hτM (h ▸ one_mem _)
  have hord : orderOf (τ : Equiv.Perm (Fin 1782)) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime ?_ hτ1
    rw [pow_two]
    exact congrArg Subtype.val hττ
  obtain ⟨i, hi, g, hg, hτg⟩ := cover_outer hτT hord hτM
  obtain ⟨lb, cb, hlc⟩ := hw i hi
  set Lbar : suzM := ⟨g, hg⟩ * lb * ⟨g, hg⟩⁻¹ with hLbar
  obtain ⟨l, hl⟩ := hq Lbar
  have hqv : q (l * (φ l)⁻¹) = (⟨g, hg⟩ * cb) * q x₁ * (⟨g, hg⟩ * cb)⁻¹ := by
    refine Subtype.ext ?_
    have e1 := hτapply l
    rw [hl] at e1
    simp only [map_mul, map_inv, hl, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [e1]
    have e2 : (Lbar : Equiv.Perm (Fin 1782)) = g * (lb : Equiv.Perm (Fin 1782)) * g⁻¹ := rfl
    rw [e2, hτg]
    calc g * ↑lb * g⁻¹ * (g * suzInv i * g⁻¹ * (g * ↑lb * g⁻¹) * (g * suzInv i * g⁻¹)⁻¹)⁻¹ =
        g * (↑lb * suzInv i * (↑lb)⁻¹ * (suzInv i)⁻¹) * g⁻¹ := by group
      _ = g * (↑cb * ↑(q x₁) * (↑cb)⁻¹) * g⁻¹ := by rw [hlc]
      _ = g * ↑cb * ↑(q x₁) * (g * ↑cb)⁻¹ := by group
  refine ⟨l, ?_, ?_⟩
  · have hsq := sq_eq_sq_of_conj q hq hker_center hexp hqv (by rw [← map_pow, sq, hx₁, map_one])
    rw [hsq, sq, hx₁]
  · intro hv
    rw [hcenter, ← hker, MonoidHom.mem_ker, hqv] at hv
    have h1 : q x₁ = (⟨g, hg⟩ * cb)⁻¹ * ((⟨g, hg⟩ * cb) * q x₁ * (⟨g, hg⟩ * cb)⁻¹) *
        (⟨g, hg⟩ * cb) := by group
    rw [hv] at h1
    exact hx₁q (by simpa using h1)

end Main

end CFSG.EvenSporadicStandard.TwoSuz
