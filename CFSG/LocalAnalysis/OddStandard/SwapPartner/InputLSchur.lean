module

public import CFSG.Alternating.Multipliers.Main

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Equiv Equiv.Perm Subgroup
open CFSG.Alternating.Multipliers.Spin CFSG.RankThree.PerfectCover
open scoped commutatorElement

private theorem klein_mul {α : Type*} [DecidableEq α] {a b c d : α}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    swap a b * swap c d * (swap a c * swap b d) = swap a d * swap b c := by
  ext i
  simp only [Perm.mul_apply, swap_apply_def]
  split_ifs <;> simp_all

private theorem commute_swap_mul_swap {α : Type*} [DecidableEq α] {a b c d : α}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    swap a b * swap c d * (swap a c * swap b d) =
      (swap a c * swap b d) * (swap a b * swap c d) := by
  calc swap a b * swap c d * (swap a c * swap b d)
      = swap a d * swap b c := klein_mul hab hac had hbc hbd hcd
    _ = (swap a c * swap b d) * (swap a b * swap c d) := by
        rw [klein_mul (b := c) (c := b) (hab := hac) (hac := hab) (had := had)
          (hbc := hbc.symm) (hbd := hcd) (hcd := hbd), swap_comm c b]

theorem commutator_ne_one_spin {m : ℕ} {a b c d : Fin (m + 2)}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    {x y : CFSG.Alternating.Multipliers.Spin.E (m + 2)}
    (hx : (CFSG.Alternating.Multipliers.Spin.psi x : Perm (Fin (m + 2))) = swap a b * swap c d)
    (hy : (CFSG.Alternating.Multipliers.Spin.psi y : Perm (Fin (m + 2))) =
      swap a c * swap b d) : ⁅x, y⁆ ≠ 1 := by
  let dx : H (m + 2) :=
    ⟨dd hab hcd, subset_closure (show dd hab hcd ∈ ddSet (m + 2) from ⟨a, b, c, d, hab, hcd, rfl⟩)⟩
  let dy : H (m + 2) :=
    ⟨dd hac hbd, subset_closure (show dd hac hbd ∈ ddSet (m + 2) from ⟨a, c, b, d, hac, hbd, rfl⟩)⟩
  have hdx : permH (n := m + 2) dx = swap a b * swap c d := by
    change perm (n := m + 2) (dd hab hcd) = swap a b * swap c d
    exact perm_dd hab hcd
  have hdy : permH (n := m + 2) dy = swap a c * swap b d := by
    change perm (n := m + 2) (dd hac hbd) = swap a c * swap b d
    exact perm_dd hac hbd
  have hxH : permH (n := m + 2) (x : H (m + 2)) = swap a b * swap c d := by
    rw [← hx]
    rfl
  have hyH : permH (n := m + 2) (y : H (m + 2)) = swap a c * swap b d := by
    rw [← hy]
    rfl
  have hz : dx⁻¹ * (x : H (m + 2)) ∈ (permH (n := m + 2)).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hdx, hxH, inv_mul_cancel]
  have hz' : dy⁻¹ * (y : H (m + 2)) ∈ (permH (n := m + 2)).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hdy, hyH, inv_mul_cancel]
  have hzc : dx⁻¹ * (x : H (m + 2)) ∈ center (H (m + 2)) := ker_permH_le_center hz
  have hzc' : dy⁻¹ * (y : H (m + 2)) ∈ center (H (m + 2)) := ker_permH_le_center hz'
  have hcomm : ⁅(x : H (m + 2)), (y : H (m + 2))⁆ = ⁅dx, dy⁆ := by
    have hxdec : (x : H (m + 2)) = dx * (dx⁻¹ * (x : H (m + 2))) := by group
    have hydec : (y : H (m + 2)) = dy * (dy⁻¹ * (y : H (m + 2))) := by group
    rw [hxdec, hydec, CFSG.SectionRank.commutatorElement_mul_mem_center dx dy hzc hzc']
  have hcomm_mono : ((⁅dx, dy⁆ : H (m + 2)) : monomial (m + 2)) = negOne := by
    rw [show ((⁅dx, dy⁆ : H (m + 2)) : monomial (m + 2)) =
        ⁅(dd hab hcd : monomial (m + 2)), (dd hac hbd : monomial (m + 2))⁆ from rfl]
    exact commutator_dd hab hac had hbc hbd hcd
  intro hxy
  apply negOne_ne_one
  have h1H : ((⁅x, y⁆ : E (m + 2)) : H (m + 2)) = 1 := by
    rw [hxy]
    rfl
  have h2H : ⁅(x : H (m + 2)), (y : H (m + 2))⁆ = 1 := by
    rw [← show ((⁅x, y⁆ : E (m + 2)) : H (m + 2)) =
      ⁅(x : H (m + 2)), (y : H (m + 2))⁆ from rfl]
    exact h1H
  rw [hcomm] at h2H
  have h3 : ((⁅dx, dy⁆ : H (m + 2)) : monomial (m + 2)) = 1 := congrArg Subtype.val h2H
  rw [hcomm_mono] at h3
  exact h3

theorem ker_eq_bot_of_commuting_lifts {K : Type*} [Group K] [Finite K] (hK : Group.IsPerfect K)
    {n : ℕ} (hn : 8 ≤ n) (q : K →* alternatingGroup (Fin n)) (hq : Function.Surjective q)
    (hker : q.ker ≤ Subgroup.center K) {a b c d : Fin n}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    {x y : K} (hx : (q x : Perm (Fin n)) = swap a b * swap c d)
    (hy : (q y : Perm (Fin n)) = swap a c * swap b d) (hxy : x * y = y * x) : q.ker = ⊥ := by
  obtain ⟨m', rfl⟩ : ∃ m', n = m' + 2 := ⟨n - 2, by omega⟩
  haveI : Group.IsPerfect K := hK
  let S := alternatingGroup (Fin (m' + 2))
  haveI : Group.IsPerfect S := ⟨commutator_alternatingGroup_eq_top (by simp; omega)⟩
  let xS : S :=
    ⟨swap a b * swap c d, CFSG.Alternating.Multipliers.swap_mul_swap_mem_alternatingGroup hab hcd⟩
  let yS : S :=
    ⟨swap a c * swap b d, CFSG.Alternating.Multipliers.swap_mul_swap_mem_alternatingGroup hac hbd⟩
  have hcommS : xS * yS = yS * xS := by
    apply Subtype.ext
    show (swap a b * swap c d) * (swap a c * swap b d) =
      (swap a c * swap b d) * (swap a b * swap c d)
    exact commute_swap_mul_swap hab hac had hbc hbd hcd
  obtain ⟨ux, hux⟩ := hopfCoverMap_surjective (S := S) xS
  obtain ⟨uy, huy⟩ := hopfCoverMap_surjective (S := S) yS
  let w : HopfCover S := ⁅ux, uy⁆
  have hwM : w ∈ hopfMultiplier S := by
    rw [MonoidHom.mem_ker]
    change hopfCoverMap S ⁅ux, uy⁆ = 1
    rw [map_commutatorElement, hux, huy]
    exact commutatorElement_eq_one_iff_mul_comm.mpr hcommS
  have hMcard : Nat.card (hopfMultiplier S) = 2 :=
    CFSG.Alternating.Multipliers.card_hopfMultiplier_alternatingGroup (n := m' + 2) hn
  let ε : HopfCover S →* E (m' + 2) :=
    hopfLift (S := S) (psi (m := m')) (psi_surjective (by omega)) (ker_psi_le_center (m := m'))
  have hcompε_eq : (psi (m := m')).comp ε = hopfCoverMap S := by
    change (psi (m := m')).comp
      (hopfLift (S := S) (psi (m := m')) (psi_surjective (by omega))
        (ker_psi_le_center (m := m'))) = hopfCoverMap S
    exact comp_hopfLift (S := S) (psi (m := m')) (psi_surjective (by omega))
      (ker_psi_le_center (m := m'))
  have hcompε : ∀ u : HopfCover S, psi (ε u) = hopfCoverMap S u := fun u =>
    DFunLike.congr_fun hcompε_eq u
  have hxE : (psi (ε ux) : Perm (Fin (m' + 2))) = swap a b * swap c d := by
    rw [hcompε ux, hux]
  have hyE : (psi (ε uy) : Perm (Fin (m' + 2))) = swap a c * swap b d := by
    rw [hcompε uy, huy]
  have hw_ne : w ≠ 1 := by
    have hne := commutator_ne_one_spin (m := m') hab hac had hbc hbd hcd
      (x := ε ux) (y := ε uy) hxE hyE
    have hwx : ε w = ⁅ε ux, ε uy⁆ := by
      change ε ⁅ux, uy⁆ = ⁅ε ux, ε uy⁆
      rw [map_commutatorElement]
    intro hw1
    apply hne
    rw [← hwx, hw1, map_one]
  let h : HopfCover S →* K := hopfLift (S := S) q hq hker
  have hcompq_eq : q.comp h = hopfCoverMap S := by
    change q.comp (hopfLift (S := S) q hq hker) = hopfCoverMap S
    exact comp_hopfLift (S := S) q hq hker
  have hcompq : ∀ u : HopfCover S, q (h u) = hopfCoverMap S u := fun u =>
    DFunLike.congr_fun hcompq_eq u
  have hq_x : q x = xS := Subtype.ext hx
  have hq_y : q y = yS := Subtype.ext hy
  have hq_hux : q (h ux) = xS := by rw [hcompq ux, hux]
  have hq_huy : q (h uy) = yS := by rw [hcompq uy, huy]
  let z : K := x⁻¹ * h ux
  have hzc : z ∈ center K := by
    apply hker
    rw [MonoidHom.mem_ker]
    change q (x⁻¹ * h ux) = 1
    rw [map_mul, map_inv, hq_x, hq_hux, inv_mul_cancel]
  let z' : K := y⁻¹ * h uy
  have hzc' : z' ∈ center K := by
    apply hker
    rw [MonoidHom.mem_ker]
    change q (y⁻¹ * h uy) = 1
    rw [map_mul, map_inv, hq_y, hq_huy, inv_mul_cancel]
  have hw_h : h w = 1 := by
    have hstep : ⁅h ux, h uy⁆ = ⁅x, y⁆ := by
      have e1 : h ux = x * z := by
        show h ux = x * (x⁻¹ * h ux)
        group
      have e2 : h uy = y * z' := by
        show h uy = y * (y⁻¹ * h uy)
        group
      rw [e1, e2]
      exact CFSG.SectionRank.commutatorElement_mul_mem_center x y hzc hzc'
    change h ⁅ux, uy⁆ = 1
    rw [map_commutatorElement, hstep, commutatorElement_eq_one_iff_mul_comm.mpr hxy]
  have hMle : hopfMultiplier S ≤ h.ker := by
    intro m hm
    rw [MonoidHom.mem_ker]
    obtain ⟨y₀, -, hy₀⟩ := (Nat.card_eq_two_iff' (1 : hopfMultiplier S)).1 hMcard
    have hw_ne' : (⟨w, hwM⟩ : hopfMultiplier S) ≠ 1 := by
      intro hcon
      exact hw_ne (congrArg Subtype.val hcon)
    have hyw : y₀ = ⟨w, hwM⟩ := (hy₀ ⟨w, hwM⟩ hw_ne').symm
    by_cases hm1 : (⟨m, hm⟩ : hopfMultiplier S) = 1
    · rw [show m = 1 from congrArg Subtype.val hm1]
      exact map_one h
    · have heq : (⟨m, hm⟩ : hopfMultiplier S) = ⟨w, hwM⟩ := (hy₀ ⟨m, hm⟩ hm1).trans hyw
      rw [show m = w from congrArg Subtype.val heq]
      exact hw_h
  have hmap : (hopfMultiplier S).map h = q.ker := by
    change (hopfMultiplier S).map (hopfLift (S := S) q hq hker) = q.ker
    exact map_hopfMultiplier_hopfLift (S := S) q hq hker
  rw [← hmap, Subgroup.map_eq_bot_iff]
  exact hMle

end CFSG.OddStandard.AltStdSec.SwapPartner
