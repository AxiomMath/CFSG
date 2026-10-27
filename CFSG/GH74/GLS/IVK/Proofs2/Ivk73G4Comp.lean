module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4Fixed

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.ABGLocalTools Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

variable {N : Type} [Group N] [Finite N] {L K Q : Subgroup N}

omit [Finite N] in
theorem subgroupOf_centralizer_inf_eq (u : N) (hu : u ∈ L) :
    (centralizer ({u} : Set N) ⊓ L).subgroupOf L = centralizer ({(⟨u, hu⟩ : ↥L)} : Set ↥L) := by
  ext x
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨h1, -⟩
    exact Subtype.ext h1
  · intro h1
    exact ⟨congrArg Subtype.val h1, x.2⟩

theorem Ivk73Cfg.false_of_comp_mem
    (h : Ivk73Cfg N L K Q)
    (hOut : ∀ E : Subgroup (Outer ↥L), (∀ e ∈ E, e * e = 1) → Nat.card E ≤ 2 ^ 1)
    (hcomp : ∀ y : ↥L, y * y = 1 → y ≠ 1 → ∀ B : Subgroup ↥L,
      IsCompIn (centralizer ({y} : Set ↥L)) B → y ∈ B) : False := by
  obtain ⟨u, huQ, hu2, huL⟩ := h.exists_involution_mem_L hOut
  have huu : u * u = 1 := by
    have := pow_orderOf_eq_one u
    rwa [hu2, pow_two] at this
  let y : ↥L := ⟨u, huL⟩
  have hy2 : y * y = 1 := Subtype.ext huu
  have hy1 : y ≠ 1 := by
    intro h1
    have : u = 1 := congrArg Subtype.val h1
    rw [this, orderOf_one] at hu2
    omega
  have huC : u ∈ centralizer (K : Set N) := h.Q_sylow.le huQ
  have hterm := h.terminal u hu2 huC
  have hKM : K ≤ centralizer ({u} : Set N) ⊓ L := le_inf hterm.1 h.K_le
  have hM : IsCompIn (centralizer ({u} : Set N) ⊓ L) K :=
    LU.Local.isCompIn_mono' hterm hKM inf_le_left
  have hB : IsCompIn (centralizer ({y} : Set ↥L)) (K.subgroupOf L) := by
    rw [← subgroupOf_centralizer_inf_eq u huL]
    exact ⟨Subgroup.subgroupOf_mono L hKM,
      (LU.Local.isComponent_subgroupOf_iff' (K := K) (M := centralizer ({u} : Set N) ⊓ L) (H := L)
        inf_le_right).2 hM.2⟩
  have hyB : y ∈ K.subgroupOf L := hcomp y hy2 hy1 _ hB
  have huK : u ∈ K := hyB
  have hodd := odd_center_K h.kbar_cases
  let c : ↥(center ↥K) := ⟨⟨u, huK⟩, Subgroup.mem_center_iff.2 fun g =>
    Subtype.ext (Subgroup.mem_centralizer_iff.1 huC g g.2)⟩
  have hc2 : orderOf c = 2 := by
    have h1 : orderOf (⟨u, huK⟩ : ↥K) = 2 := by
      rw [Subgroup.orderOf_mk]
      exact hu2
    rw [← Subgroup.orderOf_coe c]
    exact h1
  have hdvd : orderOf c ∣ Nat.card (center ↥K) := orderOf_dvd_natCard c
  rw [hc2] at hdvd
  exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hdvd)

end CFSG.GH74.GLS.IVK
