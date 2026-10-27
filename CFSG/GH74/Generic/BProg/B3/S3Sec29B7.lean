module

public import CFSG.GH74.Generic.BProg.B3.S3Sec29B7Diag

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.LocalCores CFSG.ClassicalInvolution.Balance Subgroup
  CFSG.ABGLocalTools
open scoped commutatorElement

theorem lemma296aw {G : Type} [Group G] [Finite G] {x y b : G} {K A B Q D J : Subgroup G}
    (h : Ctx29w G x K A B Q y b D J) (htype : IsA7Bar J ∨ IsL2OddW J)
    (hI : IsPCompIn 2 (K ⊓ centralizer ({b} : Set G)) (Ly29 K b))
    (hSL : HasSL2Model (↥(Ly29 K b) ⧸ pPrimeCore 2 ↥(Ly29 K b)) (fun q => Odd q ∧ 5 ≤ q))
    (h295 : B ⊓ cSec K ⊓ cSec J = ⊥) : Ly29 K b ≤ cSec J := by
  rcases htype with hA | ⟨r, m, hr, hr2, hm, hL | hS⟩
  · exact lemma296a (h.toCtx29 (Or.inl hA)) hI hSL
  · exact lemma296a (h.toCtx29 (Or.inr ⟨r, m, hr, hr2, hm, hL⟩)) hI hSL
  · have hm1 : 1 ≤ m := by
      obtain ⟨F, hF, hFin, hq, -⟩ := hS
      by_contra hm0
      have hm0' : m = 0 := by omega
      rw [hm0', pow_zero] at hq
      have : 1 < Nat.card F := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
      omega
    exact lemma296aw_sl2 h hI hSL (r := r ^ m) ⟨r, m, hr, hr2, hm1, rfl⟩ hS h295

theorem lemma296w_core {G : Type} [Group G] [Finite G] (hN : NTrans G)
    {x y b : G} {K A B Q D J : Subgroup G}
    (h : Ctx29w G x K A B Q y b D J) (htype : IsA7Bar J ∨ IsL2OddW J)
    (h295 : B ⊓ cSec K ⊓ cSec J = ⊥) :
    (b ∈ A ⊓ K ∧ b ≠ 1 ∧ b ∈ Ly29 K b ∧ Ly29 K b ≤ cSec J) ∧
      ∃ D' J' : Subgroup G, Ctx29w G x K A B Q y y D' J' ∧ (IsA7Bar J' ∨ IsL2OddW J') ∧
        B ⊓ cSec K ⊓ cSec J' = ⊥ := by
  obtain ⟨hb2, hJb, hbC⟩ := h.obs_data
  obtain ⟨E, hEK, hAE, hxE, hEel, hE4, hyE⟩ := h.exists_E
  obtain ⟨-, hBsup, -, -⟩ := h.B_decomp ⟨hEK, hAE, hEel, hE4⟩
  obtain ⟨hAB, -, -, hBel, -, -, -⟩ := h.ext
  have hEA : E ≤ A := hAE ▸ le_sup_left
  have hEB : E ≤ B := hEA.trans hAB
  have hBc : ∀ a ∈ B, ∀ c ∈ B, a * c = c * a := S3Sec29B.comm_of_isElementaryAbelian hBel
  have hcomm : ∀ e ∈ E, ∀ c ∈ B ⊓ cSec K, e * c = c * e := fun e he c hc =>
    hBc e (hEB he) c (Subgroup.mem_inf.1 hc).1
  have hbJ : b ∈ cSec J := S3Ctx29.mem_cSec_of_le_centralizer hJb.1
  have hbB0 : b ∉ B ⊓ cSec K := by
    intro hmem
    have h1 : b ∈ B ⊓ cSec K ⊓ cSec J := Subgroup.mem_inf.2 ⟨hmem, hbJ⟩
    rw [h295, Subgroup.mem_bot] at h1
    rw [h1, orderOf_one] at hb2
    omega
  have hbmem : b ∈ E ⊔ (B ⊓ cSec K) := hBsup ▸ h.b_mem
  obtain ⟨e, he, u, hu, hbeu⟩ := S3Theta52.exists_mul_of_mem_sup hcomm hbmem
  have he1 : e ≠ 1 := by
    intro he1
    apply hbB0
    rw [hbeu, he1, one_mul]
    exact hu
  have heAK : e ∈ A ⊓ K := Subgroup.mem_inf.2 ⟨hEA he, hEK he⟩
  obtain ⟨hI, heI, hSL⟩ := layer296w h heAK he1 hu hbeu
  have hIJ : Ly29 K b ≤ cSec J := lemma296aw h htype hI hSL h295
  have heJ : e ∈ cSec J := hIJ heI
  have hu1 : u = 1 := by
    have h1 : u ∈ cSec J := by
      have := (cSec J).mul_mem ((cSec J).inv_mem heJ) hbJ
      rwa [hbeu, inv_mul_cancel_left] at this
    have h2 : u ∈ B ⊓ cSec K ⊓ cSec J := Subgroup.mem_inf.2 ⟨hu, h1⟩
    rw [h295, Subgroup.mem_bot] at h2
    exact h2
  have hbe : b = e := by rw [hbeu, hu1, mul_one]
  subst hbe
  have hy1 : y ≠ 1 := by
    intro h1
    have := h.y_ord
    rw [h1, orderOf_one] at this
    omega
  refine ⟨⟨heAK, he1, heI, hIJ⟩, ?_⟩
  obtain ⟨g, hg, hgb⟩ := hN x K A B E y b h.circ.1.2.2 h.shape.qShape3 h.src h.ext h.rankB
    hEK hAE hEel hE4 hyE hy1 he he1
  rcases h.obs with hobs | ⟨hby, -, -, -, -⟩
  · have hgB : g ∈ normalizer (B : Set G) := (Subgroup.mem_inf.1 hg).2
    have hgK : g ∈ K := (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hg).1).1
    refine ⟨_, _, h.map_conj hobs hgB hgb, S3Boot293w.type_map_conj g htype, ?_⟩
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨⟨hzB, hzK⟩, hzJ⟩ := Subgroup.mem_inf.1 hz |>.imp_left Subgroup.mem_inf.1
    have hw : g⁻¹ * z * g⁻¹⁻¹ ∈ B ⊓ cSec K ⊓ cSec J := by
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨?_, ?_⟩, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.1 (inv_mem hgB) z).1 hzB
        simpa using this
      · exact Stage1.Thm2.Recip.cSec_conj K (inv_mem (Subgroup.le_normalizer hgK)) hzK
      · refine (S3Boot293.mem_cSec_map_conj_iff g (g⁻¹ * z * g⁻¹⁻¹) J).1 ?_
        rw [show g * (g⁻¹ * z * g⁻¹⁻¹) * g⁻¹ = z by group]
        exact hzJ
    rw [h295, Subgroup.mem_bot] at hw
    have : z = 1 := by
      have h2 : z = g * (g⁻¹ * z * g⁻¹⁻¹) * g⁻¹ := by group
      rw [h2, hw]
      group
    exact Subgroup.mem_bot.2 this
  · exact ⟨D, J, hby ▸ h, htype, h295⟩

theorem lemma296w {G : Type} [Group G] [Finite G] {x y b : G} {K A B Q D J : Subgroup G}
    (h : Ctx29w G x K A B Q y b D J) (htype : IsA7Bar J ∨ IsL2OddW J)
    (h295 : B ⊓ cSec K ⊓ cSec J = ⊥) :
    (b ∈ A ⊓ K ∧ b ≠ 1 ∧ b ∈ Ly29 K b ∧ Ly29 K b ≤ cSec J) ∧
      ∃ D' J' : Subgroup G, Ctx29w G x K A B Q y y D' J' ∧ (IsA7Bar J' ∨ IsL2OddW J') ∧
        B ⊓ cSec K ⊓ cSec J' = ⊥ ∧ Ly29 K y ≤ cSec J' := by
  obtain ⟨h1, D', J', h2, ht2, h3⟩ := lemma296w_core (ntrans_proved G) h htype h295
  exact ⟨h1, D', J', h2, ht2, h3, (lemma296w_core (ntrans_proved G) h2 ht2 h3).1.2.2.2⟩

end CFSG.GH74.Generic.BProg.B3
