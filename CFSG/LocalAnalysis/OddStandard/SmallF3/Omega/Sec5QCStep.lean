module

import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5QCCore
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5QCCent
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5QCNorm
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5QCImg
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5QCHom
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2TrCover
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5CentDPull

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {hQ : Q.Nondegenerate}

theorem sec5qc_step {φ : ↥L →* omegaGroup hQ} (hoc : OddCentralCover φ)
    (hker : φ.ker = CFSG.oddCore ↥L) {z : G} (hzL : z ∈ L) (hz2 : orderOf z = 2)
    (D : Om6Par Q (sec5cdPhi φ ⟨z, hzL⟩)) {K₁ K₂ : Subgroup G}
    (h₁ : Sl23PocketIn L z K₁) (h₂ : Sl23PocketIn L z K₂)
    (hQ₁ : Nonempty (↥(twoCoreIn K₁) ≃* QuaternionGroup 2))
    (hcard : Nat.card ↥(twoCoreIn K₁ ⊔ twoCoreIn K₂) = 32)
    {x : G} (hxN : x ∈ normalizer (L : Set G)) (hxz : x ∈ centralizer ({z} : Set G))
    (hxQ : x ∈ centralizer ((twoCoreIn K₁ ⊔ twoCoreIn K₂ : Subgroup G) : Set G))
    {g : ↥L} (hg : Odd (orderOf g)) (hgz : g * ⟨z, hzL⟩ = ⟨z, hzL⟩ * g) :
    sec5cdPhi φ (L.normalizerMonoidHom ⟨x, hxN⟩ g) = sec5cdPhi φ g := by
  let f : ↥L →* OGroup Q := sec5cdPhi φ
  let zL : ↥L := ⟨z, hzL⟩
  let t : OGroup Q := f zL
  let ψ : MulAut ↥L := L.normalizerMonoidHom ⟨x, hxN⟩
  let f' : ↥L →* OGroup Q := f.comp ψ.toMonoidHom
  let P : Subgroup (OGroup Q) := D.L ⊔ D.R
  let Qb : Subgroup (OGroup Q) := twoCoreIn D.L ⊔ twoCoreIn D.R
  change f' g = f g
  have hker_conj : ∀ l : ↥L, f l = 1 → f' l = 1 := by
    intro l hl
    simpa [f', f, ψ] using sec5qc_ker_conj (φ := φ) hker hxN hl
  have hlift : ∀ q ∈ Qb, ∃ l : ↥L, f l = q ∧ f' l = q := by
    intro q hq
    have hq' : q ∈ ((twoCoreIn K₁ ⊔ twoCoreIn K₂).subgroupOf L).map (sec5cdPhi φ) :=
      sec5qc_img_le hoc hzL hz2 D h₁ h₂ hQ₁ hcard hq
    obtain ⟨l, hl, hfl⟩ := Subgroup.mem_map.mp hq'
    have hlG : (l : G) ∈ twoCoreIn K₁ ⊔ twoCoreIn K₂ := (Subgroup.mem_subgroupOf).mp hl
    have hlcomm : (l : G) * x = x * (l : G) :=
      (Subgroup.mem_centralizer_iff.mp hxQ) (l : G) hlG
    have hψl : ψ l = l := by
      apply Subtype.ext
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      calc x * (l : G) * x⁻¹ = (l : G) * x * x⁻¹ := by rw [hlcomm]
        _ = (l : G) := by rw [mul_assoc, mul_inv_cancel, mul_one]
    refine ⟨l, ?_, ?_⟩
    · simpa [f] using hfl
    · calc f' l = f (ψ l) := rfl
        _ = f l := by rw [hψl]
        _ = q := by simpa [f] using hfl
  have hnorm : ∀ p ∈ P, ∀ q ∈ Qb, p * q * p⁻¹ ∈ Qb := by
    intro p hp q hq
    exact sec5qc_norm D hp hq
  have hcent : ∀ c ∈ P, (∀ q ∈ Qb, c * q = q * c) → c = 1 ∨ c = t := by
    intro c hc h
    exact sec5qc_cent_q8Img D hc (fun q hq => h q (sec5qc_q8Img_le D hq))
  have hcomm_t : ∀ p ∈ P, p * t = t * p := by
    intro p hp
    exact Subgroup.mem_centralizer_singleton_iff.mp (D.le_omega_cent hp).2
  have hgP : f g ∈ P := by
    have hodd : Odd (orderOf (f g)) := Odd.of_dvd_nat hg (orderOf_map_dvd f g)
    have hc : f g ∈ Subgroup.centralizer ({t} : Set (OGroup Q)) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      simpa [f, zL, t, map_mul] using congrArg f hgz
    exact D.odd_mem hc hodd
  have hg'P : f' g ∈ P := by
    have hoddψ : Odd (orderOf (ψ g)) := by
      rw [MulEquiv.orderOf_eq ψ g]
      exact hg
    have hodd : Odd (orderOf (f (ψ g))) :=
      Odd.of_dvd_nat hoddψ (orderOf_map_dvd f (ψ g))
    have hc : f (ψ g) ∈ Subgroup.centralizer ({t} : Set (OGroup Q)) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hxz' : x * z = z * x := Subgroup.mem_centralizer_singleton_iff.mp hxz
      have hgz' : (g : G) * z = z * (g : G) := by
        simpa using congrArg Subtype.val hgz
      have hxinv : Commute x⁻¹ z := (show Commute x z from hxz').inv_left
      have hψz : ψ g * zL = zL * ψ g := by
        apply Subtype.ext
        show (ψ g : G) * (zL : G) = (zL : G) * (ψ g : G)
        rw [show (zL : G) = z from rfl, Subgroup.normalizerMonoidHom_apply_apply_coe]
        calc x * (g : G) * x⁻¹ * z = x * (g : G) * (x⁻¹ * z) := by group
          _ = x * (g : G) * (z * x⁻¹) := by rw [hxinv.eq]
          _ = x * ((g : G) * z) * x⁻¹ := by group
          _ = x * (z * (g : G)) * x⁻¹ := by rw [hgz']
          _ = (x * z) * (g : G) * x⁻¹ := by group
          _ = (z * x) * (g : G) * x⁻¹ := by rw [hxz']
          _ = z * (x * (g : G) * x⁻¹) := by group
      simpa [t, map_mul] using congrArg f hψz
    exact D.odd_mem hc hodd
  exact sec5qc_core f f' hker_conj P Qb t D.htt hlift hnorm hcent hcomm_t hg hgP hg'P

end CFSG.OddStandard.SmallF3.Omega
