module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ModelGenActPSimple
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ModelGenA
import CFSG.GH74.Uniqueness.SU.SU7Gen3
import CFSG.Walter.W67.W1Basic
import CFSG.CGT.T75P.SylowSplit
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA

variable {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}

theorem concA_of_actData_lift (hp : p.Prime) (hp2 : p ≠ 2) (hS : S.Normal) (hperf : ⁅S, S⁆ = S)
    (hcore : GLAPPrimeCore p ↥S = ⊥) (hB : IsElemAbelian p B) {X : Type} [Group X] [Finite X]
    (e : PSimple p S ≃* X) {Γ : Ω →* MulAut X}
    (hΓ : ∀ (b : Ω) (g : ↥S), Γ b (e (chevQuotHom p S g)) =
      e (chevQuotHom p S ⟨b * g * b⁻¹, hS.conj_mem _ g.2 _⟩))
    (hΓker : Γ.ker = centModSubgroup p S) {M : Subgroup Ω} (hM : IsElemAbelian p M)
    (hMker : Nat.card ↥(M ⊓ Γ.ker) = p) {b : Ω} (hbB : b ∈ B) (hbM : ∀ m ∈ M, b * m = m * b)
    (hbout : M.map Γ ⊓ Subgroup.zpowers (Γ b) = ⊥) (hbker : Subgroup.zpowers b ⊓ Γ.ker = ⊥)
    (hBle : Nat.card B ≤ Nat.card M * Nat.card (Subgroup.zpowers (Γ b))) {t : Ω} (ht1 : t ≠ 1)
    (ht2 : t ^ 2 = 1) (htM : ∀ m ∈ M, m * t = t * m) (htb : b * t = t * b)
    (hW : ActData p (M ⊔ Subgroup.zpowers b) fun x => Γ x) : S267ConcA p S B := by
  classical
  set Z := Subgroup.zpowers b with hZ
  set B' := M ⊔ Z with hB'
  have hZel : IsElemAbelian p Z := hB.mono ((Subgroup.zpowers_le).2 hbB)
  have hMZ : ∀ m ∈ M, ∀ y ∈ Z, m * y = y * m := by
    intro m hm y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact Commute.zpow_right (hbM m hm).symm n
  have hB'el : IsElemAbelian p B' := hM.sup_of_commute hZel hMZ
  have hZΓ : Z.map Γ = Subgroup.zpowers (Γ b) := by rw [hZ, MonoidHom.map_zpowers]
  have hcommV : ∀ f ∈ M.map Γ, ∀ g ∈ Subgroup.zpowers (Γ b), f * g = g * f := by
    rintro _ ⟨m, hm, rfl⟩ g hg
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    exact Commute.zpow_right (by rw [Commute, SemiconjBy, ← map_mul, ← map_mul, hbM m hm]) n
  have hcardV : Nat.card (B'.map Γ) = Nat.card (M.map Γ) * Nat.card (Subgroup.zpowers (Γ b)) := by
    rw [hB', Subgroup.map_sup, hZΓ, CFSG.CGT.T75P.card_sup_of_commute hcommV hbout]
  have hM' : Nat.card (M.map Γ) * p = Nat.card M := by
    rw [← hMker]
    exact CFSG.GH74.Uniqueness.SU.SU7.Gen.card_map_mul_card_inf_ker Γ M
  have hZc : Nat.card Z = Nat.card (Subgroup.zpowers (Γ b)) := by
    have h := CFSG.GH74.Uniqueness.SU.SU7.Gen.card_map_mul_card_inf_ker Γ Z
    rw [hbker, Subgroup.card_bot, mul_one, hZΓ] at h
    exact h.symm
  have hB'up : Nat.card B' ≤ Nat.card M * Nat.card (Subgroup.zpowers (Γ b)) := by
    have h := (CFSG.Walter.W67.card_sup_mul_card_inf_of_commute M Z hMZ).1
    rw [hZc] at h
    rw [← h]
    exact Nat.le_mul_of_pos_right _ Nat.card_pos
  have hpos : 0 < Nat.card (M.map Γ) * Nat.card (Subgroup.zpowers (Γ b)) :=
    Nat.mul_pos Nat.card_pos Nat.card_pos
  have hB'map := CFSG.GH74.Uniqueness.SU.SU7.Gen.card_map_mul_card_inf_ker Γ B'
  rw [hcardV] at hB'map
  have hB'ker : Nat.card ↥(B' ⊓ Γ.ker) = p := by
    have hle : Nat.card ↥(B' ⊓ Γ.ker) ≤ p := by
      refine Nat.le_of_mul_le_mul_left ?_ hpos
      rw [hB'map]
      calc Nat.card B' ≤ Nat.card M * Nat.card (Subgroup.zpowers (Γ b)) := hB'up
        _ = Nat.card (M.map Γ) * Nat.card (Subgroup.zpowers (Γ b)) * p := by rw [← hM']; ring
    have hge : p ≤ Nat.card ↥(B' ⊓ Γ.ker) := by
      rw [← hMker]
      exact Subgroup.card_le_of_le (inf_le_inf_right _ le_sup_left)
    omega
  have hB'c : Nat.card M * Nat.card (Subgroup.zpowers (Γ b)) ≤ Nat.card B' := by
    rw [← hB'map, hB'ker, ← hM']
    exact le_of_eq (by ring)
  have hconc : S267ConcA p S B' :=
    concA_of_actData_pSimple hp hp2 hS hperf hcore hB'el (by rw [← hΓker]; exact hB'ker) e
      (fun x => Γ x) (fun x g => (hΓ x g).symm) hW
  have hle : B' ≤ Subgroup.centralizer ({t} : Set Ω) :=
    sup_le (fun m hm => Subgroup.mem_centralizer_singleton_iff.2 (htM m hm))
      ((Subgroup.zpowers_le).2 (Subgroup.mem_centralizer_singleton_iff.2 htb))
  have hB'T : B' ≤ Subgroup.normalizer (Subgroup.zpowers t : Set Ω) := by
    intro g hg
    refine mem_normalizer_of_forall_comm fun k hk => ?_
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
    exact Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.1 (hle hg)) n
  obtain ⟨B'', D, J, hB'', hD, hor, hBC, t', ht'1, ht'2, ht'D, ht'J⟩ := hconc
  refine ⟨B'', D, J, hB'', hD, Or.inr ?_, hBC, t', ht'1, ht'2, ht'D, ht'J⟩
  rcases hor with rfl | ⟨hle', T', hT', hT'2, hN⟩
  · exact ⟨hBle.trans hB'c, Subgroup.zpowers t, zpowers_ne_bot_of_ne_one ht1,
      isPGroup_two_zpowers_of_sq ht2, hB'T⟩
  · exact ⟨(hBle.trans hB'c).trans hle', T', hT', hT'2, hN⟩

end CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen

end
