module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF0
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF1
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF6
import CFSG.LocalAnalysis.StandardType.GGInndiagNormalOtherUnitary
import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryTorus

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265.SF5U

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA

variable {Ω : Type} [Group Ω] [Finite Ω] {S B T : Subgroup Ω} {x : Ω} {D K : Subgroup Ω}

theorem card_eq_of_qsnl (h : QSNL 5 S B T x D K) (hF : catalogIs (PSimple 5 K) (tyFUni 5)) :
    Nat.card B = 5 ^ 4 := by
  obtain ⟨-, -, hDcard, -, -, hKcomp, -⟩ := h.cfg.std
  obtain ⟨m, F, _, hFd, hpm, -, -, ⟨θ⟩⟩ := SF.exists_psu_model hKcomp.2.2 hF
  obtain ⟨X, hX, hBX, hnl⟩ := SF.exists_aut_nl h θ
  have hq : 3 < 2 ^ m := by
    have := Nat.le_of_dvd (by positivity) hpm
    omega
  have hXc : Nat.card X ≤ 5 ^ 2 :=
    SF.card_le_of_nl_unitary hFd (by norm_num) Nat.prime_five hq hpm hX hnl
  refine le_antisymm ?_ h.cfg.big
  rw [hBX, hDcard]
  calc 5 ^ 2 * Nat.card X ≤ 5 ^ 2 * 5 ^ 2 := Nat.mul_le_mul_left _ hXc
    _ = 5 ^ 4 := by norm_num

section Cert


theorem card_elemAbelian_le_of_le_centralizer (h : QSNL 5 S B T x D K)
    (hF : catalogIs (PSimple 5 K) (tyFUni 5)) {E : Subgroup Ω} (hE : IsElemAbelian 5 E)
    (hEC : E ≤ Subgroup.centralizer (K : Set Ω)) : Nat.card E ≤ 5 ^ 2 := by
  obtain ⟨-, -, -, -, -, hKcomp, -⟩ := h.cfg.std
  obtain ⟨m, F, _, hFd, hpm, hp3, hq, ⟨θ⟩⟩ := SF.exists_psu_model hKcomp.2.2 hF
  haveI := hFd.finite
  have hT := CFSG.StandardType.ggTorusLift_unitary (K := F)
    (by rw [hFd.card, ← pow_mul, mul_comm]) hFd.one_le hp3 hq h.cfg.prime hpm
  have h1 := SF.pow_mul_card_le_of_torusLift h.cfg.prime hKcomp.2.2.1
    (θ.trans (CFSG.StandardType.InndiagSU.projEquiv hFd (by omega)).symm) hT hE hEC
  have hr : CFSG.StandardType.ggUnitaryTorusRank 5 5 = 2 := by
    simp [CFSG.StandardType.ggUnitaryTorusRank]
  rw [hr] at h1
  have h2 : 5 ^ 2 * Nat.card E ≤ 5 ^ 2 * 5 ^ 2 :=
    (h1.trans h.cfg.rank).trans (by rw [card_eq_of_qsnl h hF]; norm_num)
  exact Nat.le_of_mul_le_mul_left h2 (by norm_num)

theorem mem_of_inv_mul_mem_centralizer (h : QSNL 5 S B T x D K)
    (hF : catalogIs (PSimple 5 K) (tyFUni 5)) {a y : Ω} (ha : a ∈ B) (hy : y ∈ K)
    (hy5 : y ^ 5 = 1) (hc : y⁻¹ * a ∈ Subgroup.centralizer (K : Set Ω)) : y ∈ B := by
  obtain ⟨hDB, hDel, hDcard, -, -, -, hDK⟩ := h.cfg.std
  have hDC : D ≤ Subgroup.centralizer (K : Set Ω) := by
    rw [hDK]
    exact inf_le_right
  have hyc : y * (y⁻¹ * a) = y⁻¹ * a * y := Subgroup.mem_centralizer_iff.1 hc y hy
  have hay : Commute y a := by
    have h1 : a = y⁻¹ * a * y := by simpa [mul_assoc] using hyc
    calc y * a = y * (y⁻¹ * a * y) := by rw [← h1]
      _ = a * y := by group
  have hc5 : (y⁻¹ * a) ^ 5 = 1 := by
    rw [hay.inv_left.mul_pow, inv_pow, hy5, inv_one, one_mul, h.cfg.elem.2 a ha]
  have hcD : ∀ d ∈ D, Commute d (y⁻¹ * a) := fun d hd => by
    have hyd : Commute y d := Subgroup.mem_centralizer_iff.1 (hDC hd) y hy
    have had : Commute a d := h.cfg.elem.comm ha (hDB hd)
    exact (hyd.inv_left.mul_left had).symm
  have hEel : IsElemAbelian 5 (D ⊔ Subgroup.zpowers (y⁻¹ * a)) := by
    refine hDel.sup_of_commute (isElemAbelian_zpowers hc5) fun d hd z hz => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    exact ((hcD d hd).zpow_right k).eq
  have hEC : D ⊔ Subgroup.zpowers (y⁻¹ * a) ≤ Subgroup.centralizer (K : Set Ω) :=
    sup_le hDC (Subgroup.zpowers_le.2 hc)
  have hEq : D = D ⊔ Subgroup.zpowers (y⁻¹ * a) := Subgroup.eq_of_le_of_card_ge le_sup_left
    ((card_elemAbelian_le_of_le_centralizer h hF hEel hEC).trans hDcard.ge)
  have hcmem : y⁻¹ * a ∈ D := by
    rw [hEq]
    exact le_sup_right (a := D) (Subgroup.mem_zpowers _)
  have hya : y = a * (y⁻¹ * a)⁻¹ := by group
  rw [hya]
  exact B.mul_mem ha (B.inv_mem (hDB hcmem))

end Cert

end CFSG.LocalAnalysis.GLTheoremA.S265.SF5U

end
