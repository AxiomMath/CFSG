module

public import CFSG.GH74.GLS.C3.Prop121.Card7Abs11
public import CFSG.GH74.ThompsonOrderFormula
public import CFSG.GH74.GLS.C3.Prop121.Card7Abs9
public import CFSG.GH74.GLS.C3.Prop121.Card7Pairs

public section

namespace CFSG.GH74.GLS.C3.Prop121.Card7

open Subgroup Equiv Perm CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model
open CFSG.ShultStronglyClosedTI.InvolutionCounting

namespace Ctx

variable {G : Type} [Group G] [Finite G] {C : Ctx G}

theorem r_x_eq (hF : FFacts) (hH : HFacts) (Y : C.Y1)
    (hpart : ∀ p ∈ thompsonPairs C.xG Y.yG C.xG, p.1 ∈ centralizer ({C.xG} : Set _) ∧
      p.2 ∈ centralizer ({C.xG} : Set _)) :
    Nat.card ↥(thompsonPairs C.xG Y.yG C.xG) = 27 := by
  rw [thompson_card_eq hF hH Y C.xG hpart]
  have hcomm : ∀ d : ↥(centralizer ({C.x} : Set G)),
      (C.ι d * f0 = f0 * C.ι d) ↔ ((d : G) * C.s = C.s * (d : G)) := by
    intro d
    rw [← C.hsF, ← map_mul, ← map_mul, C.ι.injective.eq_iff]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hPT := pair_count_transport (centralizer ({C.x} : Set G)) C.ι (· ∈ C.Acl) (· ∈ C.Bcl)
    (fun b : F7 => b * f0 = f0 * b ∧ XF b) (fun b : F7 => b * f0 = f0 * b ∧ YF b)
    (fun d => by
      show ((d : G) * C.s = C.s * (d : G) ∧ orderOf (d : G) = 2 ∧ IsConj C.x (d : G)) ↔ _
      rw [hcomm d, XF_iff d])
    (fun d => by
      show ((d : G) * C.s = C.s * (d : G) ∧ orderOf (d : G) = 2 ∧ ¬ IsConj C.x (d : G)) ↔ _
      rw [hcomm d, YF_iff hF d])
    ⟨C.x, mem_centralizer_singleton_iff.2 rfl⟩
  have hx0 : C.ι ⟨C.x, mem_centralizer_singleton_iff.2 rfl⟩ = x0F := C.hιx
  rw [hx0] at hPT
  change Nat.card {p : G × G // p.1 ∈ centralizer ({C.x} : Set G) ∧ p.2 ∈ centralizer ({C.x} : Set G) ∧
    p.1 ∈ C.Acl ∧ p.2 ∈ C.Bcl ∧ C.x ∈ zpowers (p.1 * p.2)} = 27
  rw [hPT, ← hF.rz]
  refine Nat.card_congr (Equiv.subtypeEquivRight (fun q => ?_))
  tauto

theorem r_y_eq (hF : FFacts) (hH : HFacts) (Y : C.Y1)
    (hpart : ∀ p ∈ thompsonPairs C.xG Y.yG Y.yG, p.1 ∈ centralizer ({Y.yG} : Set _) ∧
      p.2 ∈ centralizer ({Y.yG} : Set _)) :
    Nat.card ↥(thompsonPairs C.xG Y.yG Y.yG) = 156 := by
  rw [thompson_card_eq hF hH Y Y.yG hpart]
  have hX : ∀ d : ↥(centralizer ({Y.y1} : Set G)), ((d : G) ∈ C.Acl) ↔ C.Ψh Y.h1 d ∈ Y.X' :=
    fun d => (Y.mem_X'_iff d).symm
  have hY : ∀ d : ↥(centralizer ({Y.y1} : Set G)), ((d : G) ∈ C.Bcl) ↔
      (C.Ψh Y.h1 d * tau1 = tau1 * C.Ψh Y.h1 d ∧ IsInv (C.Ψh Y.h1 d) ∧ C.Ψh Y.h1 d ∉ Y.X') := by
    intro d
    constructor
    · rintro ⟨hs, h2, hx⟩
      refine ⟨(Y.comm_iff hH d).2 hs, ?_, ?_⟩
      · rw [isInv_iff_orderOf, MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
        exact h2
      · intro hmem
        exact hx ((Y.mem_X'_iff d).1 hmem).2.2
    · rintro ⟨hc, hi, hnx⟩
      have hs := (Y.comm_iff hH d).1 hc
      have h2 : orderOf (d : G) = 2 := by
        rw [Subgroup.orderOf_coe, ← MulEquiv.orderOf_eq (C.Ψh Y.h1), ← isInv_iff_orderOf]
        exact hi
      exact ⟨hs, h2, fun hx => hnx ((Y.mem_X'_iff d).2 ⟨hs, h2, hx⟩)⟩
  have hPT := pair_count_transport (centralizer ({Y.y1} : Set G)) (C.Ψh Y.h1) (· ∈ C.Acl)
    (· ∈ C.Bcl) (· ∈ Y.X') (fun b => b * tau1 = tau1 * b ∧ IsInv b ∧ b ∉ Y.X') hX hY
    ⟨Y.y1, Y.mem_self⟩
  have hv : C.Ψh Y.h1 ⟨Y.y1, Y.mem_self⟩ = ystar := Y.psi_y1 hH
  rw [hv] at hPT
  change Nat.card {p : G × G // p.1 ∈ centralizer ({Y.y1} : Set G) ∧
    p.2 ∈ centralizer ({Y.y1} : Set G) ∧ p.1 ∈ C.Acl ∧ p.2 ∈ C.Bcl ∧
    Y.y1 ∈ zpowers (p.1 * p.2)} = 156
  rw [hPT]
  exact hH.ry Y.X' (fun a ha => Y.X'_comm_inv hH ha) (Y.ystar_notMem_X' hH)
    (fun a ha g hg => Y.X'_closed hH ha g hg)
    (by rw [Ny_eq_two_Nx hF hH Y 96, hF.N96]) (by rw [Ny_eq_two_Nx hF hH Y 48, hF.N48])
    (Y.card_X' hF hH)

theorem card_centralizer_s (hF : FFacts) (hH : HFacts) :
    Nat.card ↥(centralizer ({C.s} : Set G)) = 60480 := by
  obtain ⟨Y⟩ := exists_Y1 (C := C) hF
  obtain ⟨hcard, hpart⟩ := CFSG.GH74.thompson_two_involution_class_order_formula
    (t := C.xG) (u := Y.yG) orderOf_xG (orderOf_yG Y) (not_isConj_xG_yG hF hH Y)
    (fun w hw => hcl_gamma hF hH Y w hw)
  have hx := hpart C.xG (Or.inl rfl)
  have hy := hpart Y.yG (Or.inr rfl)
  have e1 : Nat.card ↥(centralizer ({Y.yG} : Set ↥(centralizer ({C.s} : Set G)))) = 576 := by
    rw [Y1.yG, card_cent_gamma Y.y1 Y.y1_comm_s]
    exact (Y.tau_cases hH).2
  have e2 : Nat.card ↥(centralizer ({C.xG} : Set ↥(centralizer ({C.s} : Set G)))) = 288 := by
    rw [xG, card_cent_gamma C.x C.s_comm_x.symm]
    exact cc3_x_s_s hF
  unfold CFSG.ShultStronglyClosedTI.InvolutionCounting.thompsonPairCount at hcard
  rw [r_x_eq hF hH Y hx, r_y_eq hF hH Y hy, e1, e2] at hcard
  omega

end Ctx

end CFSG.GH74.GLS.C3.Prop121.Card7
