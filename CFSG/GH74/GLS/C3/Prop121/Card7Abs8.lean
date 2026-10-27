module

public import CFSG.GH74.GLS.C3.Prop121.Card7Abs7
public import CFSG.GH74.GLS.C3.Prop121.Card7Abs6
public import CFSG.GH74.GLS.C3.Prop121.Card7Count

public section

namespace CFSG.GH74.GLS.C3.Prop121.Card7

open Subgroup Equiv Perm CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

namespace Ctx

variable {G : Type} [Group G] [Finite G] {C : Ctx G}

@[expose] def Y1.X' (Y : C.Y1) : Set H11 :=
  {h | ∃ (w : G) (hw : w * Y.y1 = Y.y1 * w), w ∈ C.Acl ∧ Y.psi w hw = h}

omit [Finite G] in
theorem Y1.mem_X'_iff (Y : C.Y1) (d : ↥(centralizer ({Y.y1} : Set G))) :
    C.Ψh Y.h1 d ∈ Y.X' ↔ (d : G) ∈ C.Acl := by
  constructor
  · rintro ⟨w, hw, hwA, hψ⟩
    have : (⟨w, mem_centralizer_singleton_iff.2 hw⟩ : ↥(centralizer ({Y.y1} : Set G))) = d :=
      (C.Ψh Y.h1).injective hψ
    rw [← congrArg Subtype.val this]
    exact hwA
  · intro hd
    exact ⟨d.1, mem_centralizer_singleton_iff.1 d.2, hd, rfl⟩

theorem Nx_eq (hF : FFacts) (hH : HFacts) (Y : C.Y1) (c0 : ℕ) :
    Nat.card {b : G // (∃ c ∈ centralizer ({C.s} : Set G), c * Y.y1 * c⁻¹ = b) ∧
        (C.x * b = b * C.x ∧ cc3 C.x C.s b = c0)} =
      Nat.card {b : F7 // b * f0 = f0 * b ∧ YF b ∧ ccard F7 f0 b = c0} := by
  refine card_transport_subtype (a := C.x) C.ι _ _ ?_ ?_
  · intro g hg
    exact mem_centralizer_singleton_iff.2 hg.2.1.symm
  · intro d
    have hcomm : (C.ι d * f0 = f0 * C.ι d) ↔ ((d : G) * C.s = C.s * (d : G)) := by
      rw [← C.hsF, ← map_mul, ← map_mul, C.ι.injective.eq_iff]
      exact ⟨fun h => congrArg Subtype.val h.symm |>.symm, fun h => Subtype.ext h⟩
    have hcc : cc3 C.x C.s (d : G) = ccard F7 f0 (C.ι d) := by
      have := cc3_eq_ccard (a := C.x) (u := C.s) (v := (d : G)) C.ι C.hs d.2
      rw [this, C.hsF]
    have hxd : C.x * (d : G) = (d : G) * C.x := (mem_centralizer_singleton_iff.1 d.2).symm
    rw [mem_Bcl_iff hF hH Y, hcc, hcomm, YF_iff hF]
    constructor
    · rintro ⟨⟨h1, h2, h3⟩, -, h4⟩
      exact ⟨h1, ⟨h2, h3⟩, h4⟩
    · rintro ⟨h1, ⟨h2, h3⟩, h4⟩
      exact ⟨⟨h1, h2, h3⟩, hxd, h4⟩

theorem Ny_eq (hF : FFacts) (hH : HFacts) (Y : C.Y1) (c0 : ℕ) :
    Nat.card {a : G // (∃ c ∈ centralizer ({C.s} : Set G), c * C.x * c⁻¹ = a) ∧
        (a * Y.y1 = Y.y1 * a ∧ cc3 a C.s Y.y1 = c0)} =
      Nat.card {b : H11 // b ∈ Y.X' ∧ ccard H11 tau1 b = c0} := by
  refine card_transport_subtype (a := Y.y1) (C.Ψh Y.h1) _ _ ?_ ?_
  · intro g hg
    exact mem_centralizer_singleton_iff.2 hg.2.1
  · intro d
    have hd : (d : G) * Y.y1 = Y.y1 * (d : G) := mem_centralizer_singleton_iff.1 d.2
    have hpsi : C.Ψh Y.h1 d = Y.psi (d : G) hd := rfl
    have hcc : ccard H11 tau1 (C.Ψh Y.h1 d) = cc3 (d : G) C.s Y.y1 := by
      rw [hpsi, Y.ccard_psi hH hd, cc3_swap13]
    rw [mem_Acl_iff hF hH Y, Y.mem_X'_iff, hcc]
    constructor
    · rintro ⟨h1, -, h2⟩
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, hd, h2⟩

theorem Ny_eq_two_Nx (hF : FFacts) (hH : HFacts) (Y : C.Y1) (c0 : ℕ) :
    Nat.card {b : H11 // b ∈ Y.X' ∧ ccard H11 tau1 b = c0} =
      2 * Nat.card {b : F7 // b * f0 = f0 * b ∧ YF b ∧ ccard F7 f0 b = c0} := by
  have hdc := double_count (centralizer ({C.s} : Set G)) C.x Y.y1
    (fun a b => a * b = b * a ∧ cc3 a C.s b = c0) (by
      intro c hc a b
      have hc' : c * C.s = C.s * c := mem_centralizer_singleton_iff.1 hc
      rw [cc3_conj a b C.s c hc']
      have hcomm : (c * a * c⁻¹) * (c * b * c⁻¹) = (c * b * c⁻¹) * (c * a * c⁻¹) ↔
          a * b = b * a := by
        have e1 : (c * a * c⁻¹) * (c * b * c⁻¹) = c * (a * b) * c⁻¹ := by group
        have e2 : (c * b * c⁻¹) * (c * a * c⁻¹) = c * (b * a) * c⁻¹ := by group
        rw [e1, e2]
        constructor
        · intro h
          exact mul_left_cancel (mul_right_cancel h)
        · intro h; rw [h]
      rw [hcomm])
  rw [Nx_eq hF hH Y c0, Ny_eq hF hH Y c0] at hdc
  have h1 := card_Acl_mul (C := C) hF
  have h2 := card_Bcl_mul hH Y
  have hpos : 0 < Nat.card ↥(centralizer ({C.s} : Set G)) := Nat.card_pos
  have hA : Nat.card {g : G // ∃ c ∈ centralizer ({C.s} : Set G), c * C.x * c⁻¹ = g} =
      2 * Nat.card {g : G // ∃ c ∈ centralizer ({C.s} : Set G), c * Y.y1 * c⁻¹ = g} := by omega
  have hBpos : 0 < Nat.card {g : G // ∃ c ∈ centralizer ({C.s} : Set G), c * Y.y1 * c⁻¹ = g} := by
    rcases Nat.eq_zero_or_pos
      (Nat.card {g : G // ∃ c ∈ centralizer ({C.s} : Set G), c * Y.y1 * c⁻¹ = g}) with h | h
    · rw [h] at h2; omega
    · exact h
  rw [hA] at hdc
  have : Nat.card {g : G // ∃ c ∈ centralizer ({C.s} : Set G), c * Y.y1 * c⁻¹ = g} *
      (2 * Nat.card {b : F7 // b * f0 = f0 * b ∧ YF b ∧ ccard F7 f0 b = c0}) =
      Nat.card {g : G // ∃ c ∈ centralizer ({C.s} : Set G), c * Y.y1 * c⁻¹ = g} *
      Nat.card {b : H11 // b ∈ Y.X' ∧ ccard H11 tau1 b = c0} := by
    rw [← hdc]; ring
  exact (Nat.eq_of_mul_eq_mul_left hBpos this).symm

end Ctx

end CFSG.GH74.GLS.C3.Prop121.Card7
