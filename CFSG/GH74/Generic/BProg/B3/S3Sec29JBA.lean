module

public import CFSG.GH74.Generic.BProg.B3.S3Sec29JBL1
public import CFSG.GH74.Generic.BProg.B3.S3Sec29C5

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.S3 CFSG.GH74.Generic.S45
  CFSG.GH74.Generic.BProg CFSG.GH74.Generic.BProg.B3 CFSG.Blueprint CFSG.ABGLocalTools
  CFSG.Assembly.LowTwoRank CFSG.LocalCores CFSG.ClassicalInvolution.Balance Subgroup
open scoped commutatorElement

namespace S3Sec29JB

variable {G : Type} [Group G] [Finite G] {x y : G} {K A B Q D J R : Subgroup G}

theorem exists_R_L (L : Subgroup G) (hQ : IsPGroup 2 ↥Q) :
    ∃ R : Subgroup G, IsSylowOf 2 R (Jss y L ⊔ Q ⊔ zpowers y) ∧ Q ≤ R :=
  S3Theta52.exists_isSylowOf_ge (le_sup_right.trans le_sup_left) hQ

theorem Jss_L1_sup_le_centralizer (h : Ctx29w G x K A B Q y y D J) :
    Jss y (L1 K y) ⊔ Q ⊔ zpowers y ≤ centralizer ({y} : Set G) :=
  sup_le (sup_le (S3Sec29D5.Jss_le_centralizer _) (S3Sec29D5.Q_le_centralizer_y h))
    (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 rfl))

theorem Jss_L1_sup_le_cSec (h : Ctx29w G x K A B Q y y D J) :
    Jss y (L1 K y) ⊔ Q ⊔ zpowers y ≤ cSec (L1 K y) :=
  sup_le (sup_le (S3Sec29D5.Jss_le_cSec _) (Q_le_cSec_L1 h))
    (Subgroup.zpowers_le.2 (y_mem_cSec_L1 K y))

theorem part_a_L1 (h : Ctx29w G x K A B Q y y D J)
    (hR : IsSylowOf 2 R (Jss y (L1 K y) ⊔ Q ⊔ zpowers y)) (hQR : Q ≤ R) :
    y ∈ R ⊓ centralizer ({x} : Set G) ∧ y ∉ Q ∧
      ∀ r ∈ R ⊓ centralizer ({x} : Set G), r * r ∈ Q → r ∈ Q ∨ r * y⁻¹ ∈ Q := by
  have hK : IsPCompIn 2 (centralizer ({x} : Set G)) K := h.circ.1.1.1.2.2
  have hRy : R ≤ centralizer ({y} : Set G) := hR.le.trans (Jss_L1_sup_le_centralizer h)
  have hyR : y ∈ R := S3Sec29C.mem_of_central_of_isSylowOf hR
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers y)) h.y_ord
    fun _ hm => Subgroup.mem_centralizer_singleton_iff.1 (Jss_L1_sup_le_centralizer h hm)
  have hRQ : R ⊓ CxK x K = Q :=
    h.Q_syl.eq_of_le (le_inf hQR h.Q_syl.le) inf_le_right hR.isPGroup.to_inf_left
  refine ⟨Subgroup.mem_inf.2 ⟨hyR, S3Sec29Cw.y_mem_CxK_left h⟩, fun hyQ =>
    S3Sec29Cw.y_not_mem_cSec h (Subgroup.mem_inf.1 (h.Q_syl.le hyQ)).2, ?_⟩
  intro r hr hrr
  have hPv : R ⊓ centralizer ({x} : Set G) ≤ centralizer ({x} : Set G) := inf_le_right
  have hPM : R ⊓ centralizer ({x} : Set G) ≤ normalizer (K : Set G) := fun r hr =>
    S3Sec29Cw.mem_normalizer_K h hr.2 (Subgroup.mem_centralizer_singleton_iff.1 (hRy hr.1))
  have hPLc : R ⊓ centralizer ({x} : Set G) ≤ cSec (Ly29 K y) := fun r hr =>
    mem_cSec_Ly_of_L1 (S3Ctx29Layer.mem_normalizer_pLayerOf_of_mem_normalizer
      (S3Ctx29Layer.mem_normalizer_inf_centralizer (hPM hr)
        (Subgroup.mem_centralizer_singleton_iff.1 (hRy hr.1))))
      (Jss_L1_sup_le_cSec h (hR.le hr.1))
  have hPL : S3Sec29C.FixesLayer x K y (R ⊓ centralizer ({x} : Set G)) :=
    S3Sec29C.fixesLayer_of_cSec hK h.y_ord hPv hPLc
  have hrrK : r * r ∈ cSec K := (Subgroup.mem_inf.1 (h.Q_syl.le hrr)).2
  rcases S3Sec29C.unique_involution hK h.shape.qShape3 (Subgroup.mem_inf.1 h.y_mem).2 h.y_ord hPv
    hPM hPL r hr hrrK with h1 | h2
  · left
    rw [← hRQ]
    exact Subgroup.mem_inf.2 ⟨hr.1, Subgroup.mem_inf.2 ⟨hr.2, h1⟩⟩
  · right
    rw [← hRQ]
    exact Subgroup.mem_inf.2 ⟨mul_mem hr.1 (inv_mem hyR),
      Subgroup.mem_inf.2 ⟨mul_mem hr.2 (inv_mem (S3Sec29Cw.y_mem_CxK_left h)), h2⟩⟩

end S3Sec29JB

end CFSG.GH74.Generic.BProg.B3
