module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.UHSZ
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.UProj
import CFSG.LocalAnalysis.OddStandard.SwapPartner.LemmaGCent
import CFSG.LocalAnalysis.OddStandard.SwapPartner.WpGTypes
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.UPerm

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup Equiv Equiv.Perm CFSG.OddStandard.AltStdSec.SwapPattern
open CFSG.Blueprint.NativeSporadic

variable {G : Type} [Group G] {z : G} {ι ιd : Perm (Fin 10) →* G} {Kh : Subgroup G}

theorem HSCtx.exists_involution_of_g (C : HSCtx z ι ιd Kh) [Finite G]
    (hg : ∀ k ∈ Kh, gElt ιd * k = k * gElt ιd) :
    z * ι τ₀ ∉ Kh ∧ ∃ b ∈ Kh, (b = ι (swap 0 1) ∨ b = (z * ι τ₀) * ι (swap 0 1)) ∧
      2880 ≤ Nat.card ↥(Kh ⊓ centralizer ({b} : Set G)) := by
  have hcenter : center ↥Kh = ⊥ := C.center_eq_bot_of_g hg
  have hHS : IsSporadic ↥Kh .HS := by
    have e : (↥Kh ⧸ center ↥Kh) ≃* ↥Kh :=
      (QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot
    exact C.khat.hs.map (fun f => e.symm.trans f)
  have hx2notKh : z * ι τ₀ ∉ Kh := by
    intro hx2
    have hmem : (⟨z * ι τ₀, hx2⟩ : ↥Kh) ∈ center ↥Kh := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      exact mem_centralizer_singleton_iff.mp (C.khat.le g.2)
    rw [hcenter] at hmem
    have h1 : (⟨z * ι τ₀, hx2⟩ : ↥Kh) = 1 := Subgroup.mem_bot.mp hmem
    exact C.frame.d8.x_ne (by simpa using congrArg Subtype.val h1)
  have hnorm : ∀ n ∈ Kh, z * n * z⁻¹ ∈ Kh :=
    fun n hn => C.conj_mem (z_mem_centralizer_x₂ C.frame.cent) hn
  have hzz : z * z = 1 := C.frame.cent.mul_self
  have hnc : ∃ n ∈ Kh, z * n ≠ n * z := by
    classical
    by_contra h
    exact C.not_centralizes_z fun n hn => by
      by_contra hne
      exact h ⟨n, hn, hne⟩
  have hBcard := C.facts.2.2.1 (Y := G) Kh hHS z hnorm hzz hnc
  have hAz : Agrp ι ≤ centralizer ({z} : Set G) :=
    Agrp_le_Siggrp.trans fun s hs =>
      (Subgroup.mem_inf.mp (Siggrp_le_CEgrp C.frame.cent hs)).1
  have hAB : Agrp ι ≤ Kh ⊓ centralizer ({z} : Set G) := le_inf C.khat.agrp_le hAz
  have hAle : 20160 ≤ Nat.card ↥(Kh ⊓ centralizer ({z} : Set G)) := by
    have h := Subgroup.card_le_of_le hAB
    rwa [card_Agrp C.frame] at h
  have hB40320 : Nat.card ↥(Kh ⊓ centralizer ({z} : Set G)) = 40320 := by
    rcases hBcard with h | h | h | h
    · rw [h] at hAle; norm_num at hAle
    · rw [h] at hAle; norm_num at hAle
    · exact h
    · rw [h] at hAle; norm_num at hAle
  have hzzx : z * (z * ι τ₀) = ι τ₀ := by rw [← mul_assoc, hzz, one_mul]
  have hBle : (Kh ⊓ centralizer ({z} : Set G)) ≤ CEgrp z ι := by
    intro b hb
    obtain ⟨hbKh, hbz⟩ := Subgroup.mem_inf.mp hb
    rw [CEgrp, Subgroup.mem_inf]
    refine ⟨hbz, mem_centralizer_singleton_iff.mpr ?_⟩
    have hbz' : Commute b z := mem_centralizer_singleton_iff.mp hbz
    have hbx2 : Commute b (z * ι τ₀) := mem_centralizer_singleton_iff.mp (C.khat.le hbKh)
    have h := hbz'.mul_right hbx2
    rwa [hzzx] at h
  have hgB : ∀ b ∈ (Kh ⊓ centralizer ({z} : Set G)), gElt ιd * b = b * gElt ιd :=
    fun b hb => hg b (Subgroup.mem_inf.mp hb).1
  have hx2B : z * ι τ₀ ∉ (Kh ⊓ centralizer ({z} : Set G)) :=
    fun hb => hx2notKh (Subgroup.mem_inf.mp hb).1
  obtain ⟨b, hbB, hbform⟩ :=
    exists_eq_mul_sigma_of_card_eq C.frame hBle hgB hx2B hB40320 (swap 0 1)
  have hbform' : b = ι (swap 0 1) ∨ b = (z * ι τ₀) * ι (swap 0 1) := by
    rcases hbform with h | h
    · left; rw [h, liftS8_swap_zero_one]
    · right; rw [h, liftS8_swap_zero_one]
  have hbKh : b ∈ Kh := (Subgroup.mem_inf.mp hbB).1
  have hdd : ι (swap 0 1) * ι (swap 0 1) = 1 := by
    rw [← map_mul, Equiv.swap_mul_self, map_one]
  have hbb : b * b = 1 := by
    rcases hbform' with h | h
    · rw [h, ← map_mul, Equiv.swap_mul_self, map_one]
    · rw [h]
      have hxd : Commute (z * ι τ₀) (ι (swap 0 1)) := by
        have hzd : Commute z (ι (swap 0 1)) := C.frame.cent.comm (swap 0 1)
        have hdisj : Disjoint (swap (8 : Fin 10) 9) (swap (0 : Fin 10) 1) :=
          disjoint_swap_swap (by decide)
        have hτd : Commute (ι τ₀) (ι (swap 0 1)) := by
          show ι τ₀ * ι (swap 0 1) = ι (swap 0 1) * ι τ₀
          rw [show τ₀ = swap 8 9 from rfl, ← map_mul, ← map_mul]
          exact congrArg ι hdisj.commute.eq
        exact hzd.mul_left hτd
      rw [hxd.symm.mul_mul_mul_comm (z * ι τ₀) (ι (swap 0 1)),
        C.frame.d8.x_sq, hdd, mul_one]
  have hbne : b ≠ 1 := by
    rcases hbform' with h | h
    · intro hb1
      have hsw : (swap (0 : Fin 10) 1) = 1 := by
        rw [h] at hb1
        exact C.frame.cent.inj (by rw [hb1, map_one])
      have h0 : (1 : Fin 10) = 0 := by
        simpa using congrArg (fun f : Perm (Fin 10) => f 0) hsw
      exact (by decide : (1 : Fin 10) ≠ 0) h0
    · intro hb1
      rw [h] at hb1
      have h1 : z * (ι τ₀ * ι (swap 0 1)) = 1 := by
        rw [← mul_assoc]
        exact hb1
      have hz : z = ι (swap 0 1 * τ₀) := by
        have h := (mul_eq_one_iff_eq_inv.mp h1)
        rw [mul_inv_rev, ← map_inv, ← map_inv, Equiv.swap_inv,
          inv_eq_of_mul_eq_one_right τ₀_mul_self, ← map_mul] at h
        exact h
      exact C.frame.cent.ne_z (swap 0 1 * τ₀) hz.symm
  have hord : orderOf (⟨b, hbKh⟩ : ↥Kh) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime (by rw [pow_two]; exact hbb) hbne
  have hcent := C.facts.2.1 hHS (⟨b, hbKh⟩ : ↥Kh) hord
  have hmap : (centralizer ({⟨b, hbKh⟩} : Set ↥Kh)).map Kh.subtype =
      Kh ⊓ centralizer ({b} : Set G) := by
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_map] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      rw [← hyx]
      refine Subgroup.mem_inf.mpr ⟨y.2, ?_⟩
      rw [mem_centralizer_singleton_iff]
      simpa using congrArg Subtype.val (mem_centralizer_singleton_iff.mp hy)
    · intro hx
      obtain ⟨hxKh, hxcent⟩ := Subgroup.mem_inf.mp hx
      rw [Subgroup.mem_map]
      refine ⟨⟨x, hxKh⟩, ?_, rfl⟩
      rw [mem_centralizer_singleton_iff]
      apply Subtype.ext
      simpa using (mem_centralizer_singleton_iff.mp hxcent : x * b = b * x)
  have hcard : Nat.card ↥(Kh ⊓ centralizer ({b} : Set G)) =
      Nat.card ↥(centralizer ({⟨b, hbKh⟩} : Set ↥Kh)) := by
    rw [← hmap, Subgroup.card_map_of_injective Kh.subtype_injective]
  have hbound : 2880 ≤ Nat.card ↥(Kh ⊓ centralizer ({b} : Set G)) := by
    rw [hcard]
    rcases hcent with h | h <;> rw [h] <;> norm_num
  exact ⟨hx2notKh, b, hbKh, hbform', hbound⟩

end CFSG.OddStandard.AltStdSec.SwapPartner
