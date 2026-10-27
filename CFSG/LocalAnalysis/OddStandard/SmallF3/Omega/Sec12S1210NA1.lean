module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12S1210NW2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12S1210NCnt
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L129JA5

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

theorem sec12N_alt1_false {D : Type} [Group D] [Finite D]
    (ρ : D →* ↥(alternatingGroup (Fin 5))) (hρ : Function.Surjective ρ)
    {N Θ : Type*} [Group N] [Finite N] [Group Θ] (φ : N →* WrZ2 D)
    (hφ : Function.Surjective φ) (β : N →* Θ)
    (hβ : ∀ n, β n = 1 ↔ φ n ∈ sec12W_base ρ.ker) {t : N} (ht2 : t * t = 1)
    (htr : (φ t).right = 1)
    (hC : Nat.card (Subgroup.centralizer ({β t} : Set Θ)) = 120) : False := by
  classical
  let K := (RegularWreathProduct.rightHom : WrZ2 D →* Multiplicative (ZMod 2)).ker
  let TK : K := ⟨φ t, MonoidHom.mem_ker.mpr htr⟩
  have hTK : TK * TK = 1 := Subtype.ext (by
    show φ t * φ t = 1
    rw [← map_mul, ht2, map_one])
  have hτ : ∀ x, sec12W_proj x TK * sec12W_proj x TK = 1 := fun x => by
    rw [← map_mul, hTK, map_one]
  let a : Multiplicative (ZMod 2) → ↥(alternatingGroup (Fin 5)) := fun x =>
    ρ (sec12W_proj x TK)
  have haa : ∀ x, a x * a x = 1 := fun x => by
    show ρ (sec12W_proj x TK) * ρ (sec12W_proj x TK) = 1
    rw [← map_mul, hτ x, map_one]
  let U : Multiplicative (ZMod 2) → Subgroup D := fun x =>
    (Subgroup.centralizer ({a x} : Set ↥(alternatingGroup (Fin 5)))).comap ρ
  have hker_le : ∀ x, ρ.ker ≤ U x := fun x g hg => by
    show ρ g ∈ Subgroup.centralizer ({a x} : Set ↥(alternatingGroup (Fin 5)))
    rw [MonoidHom.mem_ker.mp hg]
    exact Subgroup.one_mem _
  have hUcard : ∀ x, Nat.card (U x) = Nat.card ρ.ker *
      Nat.card (Subgroup.centralizer ({a x} : Set ↥(alternatingGroup (Fin 5)))) := fun x => by
    have h := sec12J_card_inf_ker_mul ρ (U x)
    rw [inf_eq_right.mpr (hker_le x), Subgroup.map_comap_eq_self_of_surjective hρ] at h
    exact h.symm
  let s : Multiplicative (ZMod 2) := Multiplicative.ofAdd 1
  let H : Subgroup (WrZ2 D) := sec12W_base2 (U 1) (U s)
  let B2 : Subgroup (WrZ2 D) := sec12W_base ρ.ker
  have hBH : B2 ≤ H := by
    rintro w ⟨hr, h⟩
    exact ⟨hr, hker_le 1 (h 1), hker_le s (h s)⟩
  have hcomm : ∀ w ∈ H, w * φ t * w⁻¹ * (φ t)⁻¹ ∈ B2 := by
    intro w hw
    obtain ⟨hwr, hw1, hws⟩ := hw
    let wK : K := ⟨w, MonoidHom.mem_ker.mpr hwr⟩
    have hwx : ∀ y, w.left y ∈ U y →
        sec12W_proj y (wK * TK * wK⁻¹ * TK⁻¹) ∈ ρ.ker := by
      intro y hy
      have hy' : ρ (w.left y) ∈ Subgroup.centralizer ({a y} : Set ↥(alternatingGroup (Fin 5))) :=
        hy
      have hcm : a y * ρ (w.left y) = ρ (w.left y) * a y :=
        Subgroup.mem_centralizer_iff.mp hy' (a y) rfl
      simp only [map_mul, map_inv, MonoidHom.mem_ker]
      exact mul_inv_eq_one.mpr (mul_inv_eq_iff_eq_mul.mpr hcm.symm)
    have hc : ((wK * TK * wK⁻¹ * TK⁻¹ : K) : WrZ2 D) = w * φ t * w⁻¹ * (φ t)⁻¹ := rfl
    rw [← hc]
    refine ⟨MonoidHom.mem_ker.mp (wK * TK * wK⁻¹ * TK⁻¹ : K).2, fun x => ?_⟩
    show sec12W_proj x (wK * TK * wK⁻¹ * TK⁻¹) ∈ ρ.ker
    rcases sec12W_two_pts x with rfl | rfl
    · exact hwx 1 hw1
    · exact hwx s hws
  have hdvd := sec12N_index_dvd φ hφ β hBH hβ hcomm
  rw [hC] at hdvd
  have hcardH : Nat.card H = Nat.card (U 1) * Nat.card (U s) := sec12W_base2_card _ _
  have hcardB : Nat.card B2 = Nat.card ρ.ker * Nat.card ρ.ker := by
    show Nat.card (sec12W_base ρ.ker) = _
    rw [sec12W_base_eq_base2]
    exact sec12W_base2_card _ _
  rw [hcardH, hcardB, hUcard, hUcard] at hdvd
  have hkpos : 0 < Nat.card ρ.ker := Nat.card_pos
  have hdvd' : (Nat.card ρ.ker * Nat.card ρ.ker) *
      (Nat.card (Subgroup.centralizer ({a 1} : Set ↥(alternatingGroup (Fin 5)))) *
        Nat.card (Subgroup.centralizer ({a s} : Set ↥(alternatingGroup (Fin 5))))) ∣
      (Nat.card ρ.ker * Nat.card ρ.ker) * 120 := by
    convert hdvd using 1
    ring
  have hdvd'' := Nat.dvd_of_mul_dvd_mul_left (Nat.mul_pos hkpos hkpos) hdvd'
  rcases sec12A5_cent_card (a 1) (haa 1) with h1 | h1 <;>
    rcases sec12A5_cent_card (a s) (haa s) with h2 | h2 <;>
      rw [h1, h2] at hdvd'' <;> revert hdvd'' <;> decide

end CFSG.OddStandard.SmallF3.Omega
