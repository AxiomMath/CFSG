module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk95LinGlue
public import CFSG.GH74.Generic.S1.KL3L2

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG
open scoped MatrixGroups commutatorElement

section CentralQuot

variable {k : Type} [Field k] {m : ℕ} {J : Type} [Group J] {π : SL(m, k) →* J}

theorem ivk95x_isCentralQuot_of_equiv (e : J ≃* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL m k) :
    IsCentralQuot (e.symm.toMonoidHom.comp (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj m k)) := by
  refine ⟨fun j => ?_, fun x => ?_⟩
  · obtain ⟨x, hx⟩ := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj_surjective m k (e j)
    exact ⟨x, by simp [hx]⟩
  · have h1 : (e.symm.toMonoidHom.comp (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj m k)) x = 1 ↔
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj m k x = 1 := by simp
    rw [h1, CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj_eq_one_iff,
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center]

theorem IsCentralQuot.solvable_centralizer (hπ : IsCentralQuot π) {g : SL(m, k)}
    (hN : Group.IsSolvable ↥(Subgroup.centralizer ({g} : Set SL(m, k)))) :
    Group.IsSolvable ↥(Subgroup.centralizer ({π g} : Set J)) := by
  set C := Subgroup.centralizer ({π g} : Set J) with hC
  set N := Subgroup.centralizer ({g} : Set SL(m, k)) with hN'
  set Ĉ : Subgroup SL(m, k) := C.comap π with hĈ
  have hNĈ : N ≤ Ĉ := by
    intro n hn
    rw [hĈ, Subgroup.mem_comap, hC, Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    exact congrArg π (Subgroup.mem_centralizer_singleton_iff.1 hn)
  have hcen : ∀ x : ↥Ĉ, (x : SL(m, k)) * g * (x : SL(m, k))⁻¹ * g⁻¹ ∈ Subgroup.center SL(m, k) := by
    intro x
    rw [← hπ.ker_eq]
    have hx : π x ∈ C := x.2
    have hcomm : π x * π g = π g * π x := Subgroup.mem_centralizer_singleton_iff.1 hx
    simp only [map_mul, map_inv]
    calc π x * π g * (π x)⁻¹ * (π g)⁻¹ = (π g * π x) * (π x)⁻¹ * (π g)⁻¹ := by rw [hcomm]
      _ = 1 := by group
  let ψ : ↥Ĉ →* ↥(Subgroup.center SL(m, k)) :=
    { toFun := fun x => ⟨(x : SL(m, k)) * g * (x : SL(m, k))⁻¹ * g⁻¹, hcen x⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by
        have hty := Subgroup.mem_center_iff.1 (hcen y)
        change ((x : SL(m, k)) * y) * g * ((x : SL(m, k)) * y)⁻¹ * g⁻¹ =
          ((x : SL(m, k)) * g * (x : SL(m, k))⁻¹ * g⁻¹) * ((y : SL(m, k)) * g * (y : SL(m, k))⁻¹ * g⁻¹)
        have e1 : (y : SL(m, k)) * g * (y : SL(m, k))⁻¹ =
            ((y : SL(m, k)) * g * (y : SL(m, k))⁻¹ * g⁻¹) * g := by group
        calc ((x : SL(m, k)) * y) * g * ((x : SL(m, k)) * y)⁻¹ * g⁻¹
            = (x : SL(m, k)) * ((y : SL(m, k)) * g * (y : SL(m, k))⁻¹) * (x : SL(m, k))⁻¹ * g⁻¹ := by
              group
          _ = (x : SL(m, k)) * (((y : SL(m, k)) * g * (y : SL(m, k))⁻¹ * g⁻¹) * g) * (x : SL(m, k))⁻¹ *
                g⁻¹ := by rw [← e1]
          _ = ((x : SL(m, k)) * ((y : SL(m, k)) * g * (y : SL(m, k))⁻¹ * g⁻¹)) *
                (g * (x : SL(m, k))⁻¹ * g⁻¹) := by group
          _ = (((y : SL(m, k)) * g * (y : SL(m, k))⁻¹ * g⁻¹) * (x : SL(m, k))) *
                (g * (x : SL(m, k))⁻¹ * g⁻¹) := by rw [hty (x : SL(m, k))]
          _ = ((y : SL(m, k)) * g * (y : SL(m, k))⁻¹ * g⁻¹) *
                ((x : SL(m, k)) * g * (x : SL(m, k))⁻¹ * g⁻¹) := by group
          _ = ((x : SL(m, k)) * g * (x : SL(m, k))⁻¹ * g⁻¹) *
                ((y : SL(m, k)) * g * (y : SL(m, k))⁻¹ * g⁻¹) :=
              (hty ((x : SL(m, k)) * g * (x : SL(m, k))⁻¹ * g⁻¹)).symm) }
  have hZ : Group.IsSolvable ↥(Subgroup.center SL(m, k)) :=
    Group.isSolvable_of_comm (fun a b => Subtype.ext (Subgroup.mem_center_iff.1 b.2 a))
  have hĈsolv : Group.IsSolvable ↥Ĉ := by
    refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion hNĈ) ψ ?_
    intro x hx
    have h1 : (x : SL(m, k)) * g * (x : SL(m, k))⁻¹ * g⁻¹ = 1 := congrArg Subtype.val hx
    refine ⟨⟨x, ?_⟩, Subtype.ext rfl⟩
    rw [hN', Subgroup.mem_centralizer_singleton_iff]
    calc (x : SL(m, k)) * g = ((x : SL(m, k)) * g * (x : SL(m, k))⁻¹ * g⁻¹) * (g * (x : SL(m, k))) := by
          group
      _ = g * x := by rw [h1, one_mul]
  let φ : ↥Ĉ →* ↥C := (π.comp Ĉ.subtype).codRestrict C (fun x => x.2)
  have hφ : Function.Surjective φ := by
    intro c
    obtain ⟨h, hh⟩ := hπ.surj (c : J)
    refine ⟨⟨h, ?_⟩, Subtype.ext hh⟩
    rw [hĈ, Subgroup.mem_comap, hh]
    exact c.2
  exact Group.isSolvable_of_surjective hφ

theorem ivk95x_sl2_centralizer_solvable {g : SL(2, k)} (hg : g ∉ Subgroup.center SL(2, k)) :
    Group.IsSolvable ↥(Subgroup.centralizer ({g} : Set SL(2, k))) := by
  have hG : ∀ c : k, (g : Matrix (Fin 2) (Fin 2) k) ≠ c • (1 : Matrix (Fin 2) (Fin 2) k) := by
    intro c hc
    apply hg
    rw [Matrix.SpecialLinearGroup.mem_center_iff]
    refine ⟨c, ?_, ?_⟩
    · have hdet := g.2
      rw [hc, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at hdet
      exact hdet
    · rw [hc]
      ext i j
      by_cases hij : i = j <;> simp [Matrix.scalar_apply, hij]
  refine Group.isSolvable_of_comm (fun a b => Subtype.ext (Subtype.ext ?_))
  have ha := congrArg (fun x : SL(2, k) => (x : Matrix (Fin 2) (Fin 2) k))
    (Subgroup.mem_centralizer_singleton_iff.1 a.2)
  have hb := congrArg (fun x : SL(2, k) => (x : Matrix (Fin 2) (Fin 2) k))
    (Subgroup.mem_centralizer_singleton_iff.1 b.2)
  exact CFSG.GH74.Generic.S1.KL3L2.commute_of_commute_nonscalar hG ha hb

end CentralQuot


end CFSG.GH74.GLS.IVK.Proofs2
