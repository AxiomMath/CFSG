module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF0
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF5UCentLift
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF5UFix
import CFSG.LocalAnalysis.GLTheoremA.S12.Common

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265.SF5U

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA

variable {Ω : Type} [Group Ω] [Finite Ω] {S B T : Subgroup Ω} {x : Ω} {D K : Subgroup Ω}

theorem mem_of_pow_eq_one_of_forall_commute (h : QSNL 5 S B T x D K)
    (hF : catalogIs (PSimple 5 K) (tyFUni 5)) {g : Ω} (hg : g ^ 5 = 1)
    (hgB : ∀ b ∈ B, g * b = b * g) : g ∈ B := by
  obtain ⟨hDB, hDel, hDcard, -, hKL, -, hDK⟩ := h.cfg.std
  have hgD : g ∈ Subgroup.centralizer (D : Set Ω) :=
    Subgroup.mem_centralizer_iff.2 fun d hd => (hgB d (hDB hd)).symm
  have hgS : g ∈ Subgroup.normalizer (S : Set Ω) :=
    (Subgroup.normalizer_eq_top_iff.2 h.cfg.normal) ▸ Subgroup.mem_top g
  have hgN : g ∈ Subgroup.normalizer (K : Set Ω) := by
    rw [hKL]
    exact S12.mem_normalizer_glaLayer' (S12.mem_normalizer_inf' hgS (Subgroup.le_normalizer hgD))
  obtain ⟨b, hb, hc⟩ := exists_mem_inv_mul_mem_centralizer_of_pow h hF hgN (n := 1)
    (by rw [pow_one]; exact hg) fun b hb => by
      rw [hgB b hb, mul_inv_cancel_right, mul_inv_cancel]
      exact one_mem _
  have hDC : D ≤ Subgroup.centralizer (K : Set Ω) := by
    rw [hDK]
    exact inf_le_right
  have hgb : Commute g b := hgB b hb
  have hc5 : (g⁻¹ * b) ^ 5 = 1 := by
    rw [hgb.inv_left.mul_pow, inv_pow, hg, inv_one, one_mul, h.cfg.elem.2 b hb]
  have hcD : ∀ d ∈ D, Commute d (g⁻¹ * b) := fun d hd => by
    have hgd : Commute g d := hgB d (hDB hd)
    have hbd : Commute b d := h.cfg.elem.comm hb (hDB hd)
    exact (hgd.inv_left.mul_left hbd).symm
  have hEel : IsElemAbelian 5 (D ⊔ Subgroup.zpowers (g⁻¹ * b)) := by
    refine hDel.sup_of_commute (isElemAbelian_zpowers hc5) fun d hd z hz => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    exact ((hcD d hd).zpow_right k).eq
  have hEC : D ⊔ Subgroup.zpowers (g⁻¹ * b) ≤ Subgroup.centralizer (K : Set Ω) :=
    sup_le hDC (Subgroup.zpowers_le.2 hc)
  have hEq : D = D ⊔ Subgroup.zpowers (g⁻¹ * b) := Subgroup.eq_of_le_of_card_ge le_sup_left
    ((card_elemAbelian_le_of_le_centralizer h hF hEel hEC).trans hDcard.ge)
  have hcmem : g⁻¹ * b ∈ D := by
    rw [hEq]
    exact le_sup_right (a := D) (Subgroup.mem_zpowers _)
  have hgbc : g = b * (g⁻¹ * b)⁻¹ := by group
  rw [hgbc]
  exact B.mul_mem hb (B.inv_mem (hDB hcmem))

end CFSG.LocalAnalysis.GLTheoremA.S265.SF5U

end
