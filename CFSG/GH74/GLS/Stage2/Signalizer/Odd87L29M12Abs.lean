module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29M12Ext
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29M12Gal
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29SL2Cent

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87.L29M12

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS

theorem twoNilp_centralizer_of_normal_L2 {Y : Type} [Group Y] [Finite Y] {J : Subgroup Y}
    [J.Normal] {F : Type} [Field F] [Finite F] (hF : IVK.L2Field F)
    (h8 : Nat.card F % 8 = 3 ∨ Nat.card F % 8 = 5) (e : ↥J ≃* IVK.L2 F) (ξ : Y)
    (hξ : ξ ∈ Subgroup.center Y)
    (hker : ∀ c ∈ centralizer (J : Set Y), (∃ m : ℕ, c ^ (2 ^ m) = 1) → c ∈ zpowers ξ)
    {v : Y} (hv2 : v * v = 1) (hv : v ∉ zpowers ξ) :
    TwoNilp ↥(centralizer ({v} : Set Y)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let ρ : Y →* MulAut ↥J := MulAut.conjNormal
  have hα2 : ρ v * ρ v = 1 := by rw [← map_mul, hv2, map_one]
  have hα1 : ρ v ≠ 1 := by
    intro h
    apply hv
    refine hker v ?_ ⟨1, by rw [pow_one, pow_two]; exact hv2⟩
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    have h1 : ((ρ v) ⟨j, hj⟩ : Y) = (⟨j, hj⟩ : ↥J) := by rw [h]; rfl
    rw [MulAut.conjNormal_apply] at h1
    show j * v = v * j
    calc j * v = (v * j * v⁻¹) * v := by rw [show v * j * v⁻¹ = j from h1]
      _ = v * j := by group
  have hinn := mem_innDiagSub_of_involution hF h8 e (ρ v) hα2
  have hα_ord : orderOf (ρ v) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hα2) hα1
  have hTN := twoNilp_centralizer_innDiag hF e hinn hα_ord
  let D : Subgroup Y := centralizer ({v} : Set Y)
  have hmaps : ∀ d : ↥D, (ρ.comp D.subtype) d ∈ centralizer ({ρ v} : Set (MulAut ↥J)) := by
    intro d
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hd : (d : Y) * v = v * d := Subgroup.mem_centralizer_singleton_iff.mp d.2
    show ρ d * ρ v = ρ v * ρ d
    rw [← map_mul, ← map_mul, hd]
  let f : ↥D →* ↥(centralizer ({ρ v} : Set (MulAut ↥J))) :=
    (ρ.comp D.subtype).codRestrict _ hmaps
  refine twoNilp_of_hom_central_two_kernel hTN f ?_
  intro d hd hd2
  have hρd : ρ (d : Y) = 1 := by
    have := congrArg Subtype.val (MonoidHom.mem_ker.mp hd)
    exact this
  have hdC : (d : Y) ∈ centralizer (J : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    have h1 : ((ρ d) ⟨j, hj⟩ : Y) = (⟨j, hj⟩ : ↥J) := by rw [hρd]; rfl
    rw [MulAut.conjNormal_apply] at h1
    show j * (d : Y) = (d : Y) * j
    calc j * (d : Y) = ((d : Y) * j * (d : Y)⁻¹) * (d : Y) := by
          rw [show (d : Y) * j * (d : Y)⁻¹ = j from h1]
      _ = (d : Y) * j := by group
  obtain ⟨m, hm⟩ := hd2
  have hdξ : (d : Y) ∈ zpowers ξ := hker d hdC ⟨m, by exact congrArg Subtype.val hm⟩
  have hcenter : (d : Y) ∈ Subgroup.center Y := (Subgroup.zpowers_le.mpr hξ) hdξ
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  exact Subgroup.mem_center_iff.mp hcenter g

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87.L29M12
