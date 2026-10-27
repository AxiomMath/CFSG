module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4S47RPts
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4S47RComb
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4S47RCoc

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z : G} {A B : Subgroup G}
  {φ : (Fin 7 → ZMod 2) → G}

theorem sec4S47R_inv_tau (h : Sec4FSetup t L S z A B φ) {y : G}
    (hyN : y ∈ normalizer (A : Set G)) (hρ : h.actHom ⟨y, hyN⟩ = sec4S47RTau)
    {v : Option (Fin 7) → ZMod 2} (hv : sec4S47RCoord t φ v = y * y) :
    ∃ ε : ZMod 2, ∀ r, v (sec4S47RTau.symm r) + v r = ε := by
  have hyR : Sec4MRealizes t φ y sec4S47RTau := by
    have := h.actHom_spec ⟨y, hyN⟩
    rwa [hρ] at this
  have hconj := sec4S47RCoord_conj h hyR v
  rw [hv] at hconj
  rw [show y * (y * y) * y⁻¹ = y * y by group] at hconj
  have heq : sec4S47RCoord t φ (v ∘ sec4S47RTau.symm) = sec4S47RCoord t φ v :=
    hconj.symm.trans hv.symm
  simpa only [Function.comp_apply] using
    (sec4S47RCoord_eq_iff h (v ∘ sec4S47RTau.symm) v).mp heq

theorem sec4S47R_inv_cycle (h : Sec4FSetup t L S z A B φ) {y : G}
    (hyN : y ∈ normalizer (A : Set G)) (hρ : h.actHom ⟨y, hyN⟩ = sec4S47RTau)
    {v : Option (Fin 7) → ZMod 2} (hv : sec4S47RCoord t φ v = y * y)
    {a b c : Option (Fin 7)} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (ha0 : a ≠ some 0) (ha1 : a ≠ some 1) (hb0 : b ≠ some 0) (hb1 : b ≠ some 1)
    (hc0 : c ≠ some 0) (hc1 : c ≠ some 1) :
    ∃ e ε : ZMod 2, ∀ r, v ((sec4S47RCyc a b c).symm r) + v r = e * sec4S47RInd r + ε := by
  have hπalt : sec4S47RCyc a b c ∈ alternatingGroup (Option (Fin 7)) := by
    rw [Equiv.Perm.mem_alternatingGroup]
    unfold sec4S47RCyc
    rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab, Equiv.Perm.sign_swap hbc,
      Int.units_mul_self]
  obtain ⟨m', hm'⟩ := MonoidHom.mem_range.mp (h.alt_le_range hπalt)
  have hπ0 : sec4S47RCyc a b c (some 0) = some 0 := by
    simp only [sec4S47RCyc, Equiv.Perm.mul_apply]
    rw [Equiv.swap_apply_of_ne_of_ne hb0.symm hc0.symm,
      Equiv.swap_apply_of_ne_of_ne ha0.symm hb0.symm]
  have hπ1 : sec4S47RCyc a b c (some 1) = some 1 := by
    simp only [sec4S47RCyc, Equiv.Perm.mul_apply]
    rw [Equiv.swap_apply_of_ne_of_ne hb1.symm hc1.symm,
      Equiv.swap_apply_of_ne_of_ne ha1.symm hb1.symm]
  have hcomm : sec4S47RCyc a b c * sec4S47RTau = sec4S47RTau * sec4S47RCyc a b c := by
    have hh := Equiv.mul_swap_eq_swap_mul (sec4S47RCyc a b c) (some 0) (some 1)
    rw [hπ0, hπ1] at hh
    simpa only [sec4S47RTau] using hh
  have hyR : Sec4MRealizes t φ y sec4S47RTau := by
    have := h.actHom_spec ⟨y, hyN⟩
    rwa [hρ] at this
  have hmR : Sec4MRealizes t φ (m' : G) (sec4S47RCyc a b c) := by
    have := h.actHom_spec m'
    rwa [hm'] at this
  let Y' : ↥(normalizer (A : Set G)) := m' * ⟨y, hyN⟩ * m'⁻¹
  have hY'val : (Y' : G) = (m' : G) * y * ((m' : G))⁻¹ := rfl
  have hY'act : h.actHom Y' = sec4S47RTau := by
    have h1 : h.actHom Y' =
        h.actHom m' * (h.actHom ⟨y, hyN⟩ * (h.actHom m')⁻¹) := by
      simp only [Y', map_mul, map_inv, mul_assoc]
    rw [h1, hm', hρ]
    calc sec4S47RCyc a b c * (sec4S47RTau * (sec4S47RCyc a b c)⁻¹)
        = (sec4S47RCyc a b c * sec4S47RTau) * (sec4S47RCyc a b c)⁻¹ := by group
      _ = (sec4S47RTau * sec4S47RCyc a b c) * (sec4S47RCyc a b c)⁻¹ := by rw [hcomm]
      _ = sec4S47RTau := by group
  have hdN : y⁻¹ * (Y' : G) ∈ normalizer (A : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hyN) Y'.2
  have hd : y⁻¹ * (Y' : G) ∈ centralizer (A : Set G) := by
    refine (h.actHom_eq_one_iff ⟨y⁻¹ * (Y' : G), hdN⟩).mp ?_
    have hsub : (⟨y⁻¹ * (Y' : G), hdN⟩ : ↥(normalizer (A : Set G))) =
        ⟨y, hyN⟩⁻¹ * Y' := by
      apply Subtype.ext
      rfl
    rw [hsub, map_mul, map_inv, hρ, hY'act]
    group
  have hyyA : y * y ∈ A := by
    rw [← hv]
    exact sec4S47RCoord_mem h v
  have hY'Y'A : (Y' : G) * (Y' : G) ∈ A := by
    have hconj : (m' : G) * (y * y) * ((m' : G))⁻¹ ∈ A :=
      (Subgroup.mem_set_normalizer_iff.mp m'.2 (y * y)).mp hyyA
    have hval : (Y' : G) * (Y' : G) = (m' : G) * (y * y) * ((m' : G))⁻¹ := by
      rw [hY'val]; group
    rw [hval]; exact hconj
  obtain ⟨a₀, ha₀, heq⟩ := sec4S47R_sq_conj h hyN hyyA hY'Y'A hd
  obtain ⟨w, hw⟩ := sec4S47R_exists_coord h ha₀
  have hsq : (Y' : G) * (Y' : G) = (m' : G) * (y * y) * ((m' : G))⁻¹ := by
    rw [hY'val]; group
  have h1 : (Y' : G) * (Y' : G) =
      sec4S47RCoord t φ (v ∘ (sec4S47RCyc a b c).symm) := by
    have hc := sec4S47RCoord_conj h hmR v
    rw [hv] at hc
    rw [← hsq] at hc
    exact hc
  have h2 : y⁻¹ * a₀ * y = sec4S47RCoord t φ (w ∘ sec4S47RTau) := by
    have hc := sec4S47RCoord_conj h (Sec4MRealizes.inv hyR) w
    rw [hw] at hc
    have hcomp : w ∘ (sec4S47RTau⁻¹).symm = w ∘ sec4S47RTau := by
      rw [Equiv.Perm.inv_def, Equiv.symm_symm]
    rw [hcomp, inv_inv] at hc
    exact hc
  have hcoord : sec4S47RCoord t φ (v ∘ (sec4S47RCyc a b c).symm) =
      sec4S47RCoord t φ v *
        (sec4S47RCoord t φ (w ∘ sec4S47RTau) * sec4S47RCoord t φ w) := by
    rw [h1.symm, heq, hv, h2, hw]
  have hcoord2 : sec4S47RCoord t φ (v ∘ (sec4S47RCyc a b c).symm) =
      sec4S47RCoord t φ (v + (w ∘ sec4S47RTau + w)) := by
    rw [sec4S47RCoord_add h v (w ∘ sec4S47RTau + w),
      sec4S47RCoord_add h (w ∘ sec4S47RTau) w]
    exact hcoord
  obtain ⟨ε, hε⟩ := (sec4S47RCoord_eq_iff h
    (v ∘ (sec4S47RCyc a b c).symm) (v + (w ∘ sec4S47RTau + w))).mp hcoord2
  refine ⟨w (some 0) + w (some 1), ε, fun r => ?_⟩
  have hh := hε r
  simp only [Pi.add_apply, Function.comp_apply] at hh
  rw [sec4S47R_swap_add w r] at hh
  have key : ∀ x y z ε : ZMod 2, x + (y + z) = ε → x + y = z + ε := by decide
  exact key _ _ _ _ hh

end CFSG.OddStandard.SmallF3.Omega
