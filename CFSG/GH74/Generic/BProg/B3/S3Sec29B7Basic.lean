module

public import CFSG.GH74.Generic.BProg.B3.S3Sec29BBasic
public import CFSG.GH74.Generic.BProg.B3.S3Sec29BConj
public import CFSG.GH74.Generic.BProg.B3.S3Sec29BLayer
public import CFSG.GH74.Generic.BProg.B3.S3Ctx29K26
public import CFSG.GH74.Generic.BProg.B3.S3Ctx29wDefs

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.LocalCores CFSG.ClassicalInvolution.Balance Subgroup
  CFSG.ABGLocalTools
open scoped commutatorElement

theorem Ctx29w.obs_data {G : Type} [Group G] [Finite G] {x y b : G} {K A B Q D J : Subgroup G}
    (h : Ctx29w G x K A B Q y b D J) :
    orderOf b = 2 ∧ IsPCompIn 2 (centralizer ({b} : Set G)) J ∧ b ∈ centralizer (B : Set G) := by
  rcases h.obs with hobs | ⟨hby, hobs32, -, -, -⟩
  · exact ⟨hobs.b_ord, hobs.comp, hobs.b_cent⟩
  · subst hby
    obtain ⟨hAB, -, -, hBel, -, -, -⟩ := h.ext
    have hbB : b ∈ B := h.b_mem
    refine ⟨h.y_ord, hobs32.comp, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact S3Sec29B.comm_of_isElementaryAbelian hBel z hz b hbB

theorem layer296w {G : Type} [Group G] [Finite G] {x y b e u : G} {K A B Q D J : Subgroup G}
    (h : Ctx29w G x K A B Q y b D J) (heAK : e ∈ A ⊓ K) (he1 : e ≠ 1) (hu : u ∈ B ⊓ cSec K)
    (hb : b = e * u) :
    IsPCompIn 2 (K ⊓ centralizer ({b} : Set G)) (Ly29 K b) ∧ e ∈ Ly29 K b ∧
      HasSL2Model (↥(Ly29 K b) ⧸ pPrimeCore 2 ↥(Ly29 K b)) (fun q => Odd q ∧ 5 ≤ q) := by
  have hK : IsPCompIn 2 (centralizer ({x} : Set G)) K := h.circ.1.2.2.1.2.2
  obtain ⟨heA, heK⟩ := Subgroup.mem_inf.1 heAK
  obtain ⟨hAB, -, -, hBel, -, -, -⟩ := h.ext
  have hBc : ∀ a ∈ B, ∀ c ∈ B, a * c = c * a := fun a ha c hc =>
    congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : ↥B) ⟨c, hc⟩)
  have heB : e ∈ B := hAB heA
  have hb2 : orderOf b = 2 := h.obs_data.1
  have he2 : orderOf e = 2 := by
    have hAel : CFSG.IsElementaryAbelian 2 ↥A := h.src.2.1
    have hsq : e ^ 2 = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := A) e heA
    exact orderOf_eq_prime hsq he1
  have heb : e * b = b * e := by
    rw [hb]
    calc e * (e * u) = e * (u * e) := by rw [hBc e heB u hu.1]
      _ = (e * u) * e := by group
  have hrange := S3Sec29BLayer.phiY_range_mul hK heK hb hb2 hu.2
  obtain ⟨hcen, hmodel⟩ := S3Ctx29K26.model_centerless_of_ctx hK h.shape.qShape3
  obtain ⟨F, hF, hFin, S, hS, -⟩ := S3Ctx29K26.exists_layerHyp' hK heK he2 hcen hmodel
  obtain ⟨L, hL, -⟩ := S3Sec29BLayer.exists_comp hS hrange
  have hLy : pLayerOf 2 (K ⊓ centralizer ({b} : Set G)) = L :=
    S3Sec29BLayer.pLayerOf_eq hS hrange hL
  have heL : e ∈ pLayerOf 2 (K ⊓ centralizer ({b} : Set G)) :=
    S3Sec29BLayer.mem_layer hS hrange he2 heb
  obtain ⟨ψ, hψs, hψk⟩ := S3Sec29BLayer.psi_data hS hrange hL
  rw [Ly29, hLy] at *
  refine ⟨hL, heL, ?_⟩
  obtain ⟨ee⟩ := hS.equiv
  refine ⟨F, hF, hFin, ⟨hS.odd, ?_⟩, ⟨?_⟩⟩
  · have h4 := hS.big
    obtain ⟨k, hk⟩ := hS.odd
    omega
  · exact ((QuotientGroup.quotientMulEquivOfEq hψk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψs)).trans
        (ee.trans (specialLinearGroupEquivStatedSL 2 F))

theorem Ctx29w.map_conj {G : Type} [Group G] [Finite G] {x y b g : G}
    {K A B Q D J : Subgroup G} (h : Ctx29w G x K A B Q y b D J) (hobs : Obs52 B b D J)
    (hg : g ∈ normalizer (B : Set G)) (hgb : g * b * g⁻¹ = y) :
    Ctx29w G x K A B Q y y (D.map (MulAut.conj g).toMonoidHom)
      (J.map (MulAut.conj g).toMonoidHom) :=
  { hyp := h.hyp
    noAlt := h.noAlt
    circ := h.circ
    shape := h.shape
    src := h.src
    ext := h.ext
    rankB := h.rankB
    C_rank := h.C_rank
    B0_le_C := h.B0_le_C
    Q_syl := h.Q_syl
    Q_cent := h.Q_cent
    B0_le_Q := h.B0_le_Q
    y_mem := h.y_mem
    y_ord := h.y_ord
    notG := h.notG
    b_mem := h.ext.1 (Subgroup.mem_inf.1 h.y_mem).1
    obs := Or.inl (S3Sec29BConj.obs52_map_conj hobs hg hgb) }

end CFSG.GH74.Generic.BProg.B3
