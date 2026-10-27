module

public import CFSG.GH74.Uniqueness.SU.SU13TC2KI8
public import CFSG.GH74.Uniqueness.SU.SU13TC2Excl
public import CFSG.GH74.Uniqueness.SU.SU13TC2LL

public section

namespace CFSG.GH74.Uniqueness.SU.SU13

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.GH74.Uniqueness.SU.SU13.TB

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem zpowers_le_oc_cent {s : G} (hs : orderOf s = 3) : zpowers s ≤ oc (centralizer ({s} : Set G)) := by
  refine le_oc_of_normal_odd ((zpowers_le).mpr (mem_centralizer_singleton_iff.mpr rfl)) ?_ ?_
  · intro g hg n hn
    have hc : Commute g s := (mem_centralizer_singleton_iff.mp hg)
    have hcn : Commute g n := by
      obtain ⟨k, rfl⟩ := hn
      exact hc.zpow_right k
    have : g * n * g⁻¹ = n := by rw [hcn.eq]; group
    rw [this]; exact hn
  · rw [Nat.card_zpowers, hs]; decide

theorem oc_inf_cent_le (C : Subgroup G) (z : G) :
    oc C ⊓ centralizer ({z} : Set G) ≤ oc (C ⊓ centralizer ({z} : Set G)) := by
  refine le_oc_of_normal_odd (X := C ⊓ centralizer ({z} : Set G))
    (N := oc C ⊓ centralizer ({z} : Set G)) ?_ ?_ ?_
  · intro y hy
    obtain ⟨hy1, hy2⟩ := mem_inf.mp hy
    exact mem_inf.mpr ⟨oc_le _ hy1, hy2⟩
  · intro g hg n hn
    obtain ⟨hn1, hn2⟩ := mem_inf.mp hn
    obtain ⟨hgC, hgz⟩ := mem_inf.mp hg
    refine mem_inf.mpr ⟨conj_mem_oc hgC hn1, ?_⟩
    rw [mem_centralizer_singleton_iff] at hn2 hgz ⊢
    have hgi : g⁻¹ * z = z * g⁻¹ := (Commute.inv_left (show Commute g z from hgz)).eq
    calc g * n * g⁻¹ * z = g * n * (g⁻¹ * z) := by group
      _ = g * n * (z * g⁻¹) := by rw [hgi]
      _ = g * (n * z) * g⁻¹ := by group
      _ = g * (z * n) * g⁻¹ := by rw [hn2]
      _ = (g * z) * n * g⁻¹ := by group
      _ = (z * g) * n * g⁻¹ := by rw [hgz]
      _ = z * (g * n * g⁻¹) := by group
  · exact Odd.of_dvd_nat (odd_card_oc C) (Subgroup.card_dvd_of_le inf_le_left)

structure Lem233 (z : G) (e : Elts G z) (E : Subgroup G) : Prop where
  E_le : E ≤ oc (centralizer ({e.s₂} : Set G))
  Y_cent : oc (centralizer ({e.s₂} : Set G)) ⊓ centralizer ({z} : Set G) = E
  Y_card : Nat.card (oc (centralizer ({e.s₂} : Set G))) = 3 ^ 7
  C_card : Nat.card (centralizer ({e.s₂} : Set G)) = 3 ^ 7 * 12 ∨
    Nat.card (centralizer ({e.s₂} : Set G)) = 3 ^ 7 * 60
  cbar : CBarProps (Mbar (centralizer ({e.s₂} : Set G)))

theorem lemma233_nine (hKI8c : K.KI8c) {z : G} (hz : orderOf z = 2) (e : Elts G z) (l : Lem232 z e)
    {E : Subgroup G} (hm : MPart9 z e E) (hE_card : Nat.card E = 27) (hE3 : ∀ a ∈ E, a ^ 3 = 1)
    (hEab : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) : Lem233 z e E := by
  set C : Subgroup G := centralizer ({e.s₂} : Set G) with hC
  set M : Subgroup G := C ⊓ centralizer ({z} : Set G) with hM
  have hzC : z ∈ C := mem_centralizer_singleton_iff.mpr e.s₂_comm.symm
  have hone' : K.OneInvClass (Mbar C) :=
    oneInvClass_mbar (fun u v hu hv hu2 hv2 => by
      obtain ⟨c, hc, hcuv⟩ := l.one u v (mem_centralizer_singleton_iff.mp hu)
        (mem_centralizer_singleton_iff.mp hv) hu2 hv2
      exact ⟨c, mem_centralizer_singleton_iff.mpr hc, hcuv⟩)
  obtain ⟨R, hR, hzR, hRz⟩ := l.R
  have hs₂Y : zpowers e.s₂ ≤ oc C := zpowers_le_oc_cent e.s₂_ord
  have hEM : E ≤ M := hm.E_le
  have hEz : E ≤ centralizer ({z} : Set G) := hEM.trans inf_le_right
  have hYzE : oc C ⊓ centralizer ({z} : Set G) ≤ E := by
    have := oc_inf_cent_le C z
    rw [hm.oc_eq] at this
    exact this
  have hLL := lattice_card hz e l hm (N := oc C) le_rfl (fun c hc n hn => conj_mem_oc hc hn)
  rw [inf_eq_right.mpr hs₂Y, Nat.card_zpowers, e.s₂_ord] at hLL
  have hCq := Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥C)
  have hoc : Nat.card (oc C) = Nat.card (pPrimeCore 2 ↥C) :=
    Subgroup.card_map_of_injective C.subtype_injective
  rcases kI8c_out hKI8c hone' hzC hz hR hzR hRz hm.oc_eq hE3 hEab hm.kl with
    ⟨hEY, hmodel⟩ | ⟨hthree, hmodel⟩
  · have hYz : oc C ⊓ centralizer ({z} : Set G) = E := le_antisymm hYzE (le_inf hEY hEz)
    have hY : Nat.card (oc C) = 3 ^ 7 := by
      rw [hYz, hE_card] at hLL
      omega
    have hcb : CBarProps (Mbar C) := by
      rcases hmodel with h4 | hpsl
      · obtain ⟨e4⟩ := h4
        exact cbarProps_a4 e4
      · exact cbarProps_psl5 hpsl
    refine ⟨hEY, hYz, hY, ?_, hcb⟩
    have hCq' : Nat.card ↥C = Nat.card (Mbar C) * 3 ^ 7 := by
      rw [hCq, ← hoc, hY]
    rcases hcb.card with h | h
    · left; rw [hCq', h]; ring
    · right; rw [hCq', h]; ring
  · exfalso
    have h9 : Nat.card (E ⊓ oc C : Subgroup G) = 9 := by
      rw [hE_card] at hthree
      omega
    have hYz : oc C ⊓ centralizer ({z} : Set G) = E ⊓ oc C := by
      apply le_antisymm
      · intro x hx
        exact mem_inf.mpr ⟨hYzE hx, (mem_inf.mp hx).1⟩
      · intro x hx
        exact mem_inf.mpr ⟨(mem_inf.mp hx).2, hEz (mem_inf.mp hx).1⟩
    have hY : Nat.card (oc C) = 81 := by
      rw [hYz, h9] at hLL
      omega
    have hCs : ∀ c ∈ C, c * e.s₂ = e.s₂ * c := fun c hc => mem_centralizer_singleton_iff.mp hc
    have hlt : Nat.card (oc C ⊓ centralizer ({z} : Set G) : Subgroup G) < 81 := by
      rw [hYz, h9]; norm_num
    rcases hmodel with h11 | h13
    · obtain ⟨hs, hc⟩ := psl_data (p := 11) (by norm_num) (by norm_num) (by norm_num) h11
      exact false_of_simple_quotient hz hzC hCs e.s₂_ord (hs₂Y (mem_zpowers _)) (q := 5) (by norm_num)
        (by norm_num) (fun k hk hk3 => by interval_cases k <;> norm_num) hs
        (by rw [hc]; norm_num) hY hlt
    · obtain ⟨hs, hc⟩ := psl_data (p := 13) (by norm_num) (by norm_num) (by norm_num) h13
      exact false_of_simple_quotient hz hzC hCs e.s₂_ord (hs₂Y (mem_zpowers _)) (q := 7) (by norm_num)
        (by norm_num) (fun k hk hk3 => by interval_cases k <;> norm_num) hs
        (by rw [hc]; norm_num) hY hlt

end CFSG.GH74.Uniqueness.SU.SU13
