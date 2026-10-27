module

public import CFSG.GH74.KGroups.L33
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FHChk
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FHTransfer

public section

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.Blueprint CFSG.GH74.KGroups

theorem fh_fixedO3Free_L33 {Y : Type} [Group Y]
    (hY : LieModel Y .PSL 3 3 1) (hchk : fhO3Chk (elemsT L33.QA) (elemsT L33.QP) = true) :
    FHFixedO3Free Y := by
  intro σ hσ N hN3 hfix hnorm
  obtain ⟨e⟩ := L33.equiv_of_lieModel hY
  obtain ⟨M, hP, hA⟩ := L33.autModel e
  have hsound := fhO3Chk_sound L33.QA L33.QP L33.QA_ok L33.QP_ok hchk
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite Y := L33.finite_K e
  have hmemA : ∀ τ : Equiv.Perm (Fin 26), τ ∈ M.A → τ ∈ L33.QA.originalSubgroup := fun τ h => hA ▸ h
  have hmemP : ∀ p : Equiv.Perm (Fin 26), p ∈ M.P ↔ p ∈ L33.QP.originalSubgroup := fun p => by
    rw [hP]
  have hcardY : Nat.card Y = 5616 := by
    rw [Nat.card_congr e.toEquiv, card_group L33.QP L33.QP_ok, L33.QP_valid.2]
  by_contra hne
  obtain ⟨x, hxN, hx1⟩ : ∃ x ∈ N, x ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    exact hne ((Subgroup.eq_bot_iff_forall N).2 hcon)
  have h3x : 3 ∣ orderOf x := by
    have := hN3.dvd_orderOf (g := (⟨x, hxN⟩ : N)) fun h => hx1 (congrArg Subtype.val h)
    rwa [Subgroup.orderOf_mk] at this
  set u : Y := x ^ (orderOf x / 3) with hu
  have hu3 : orderOf u = 3 := orderOf_pow_orderOf_div (orderOf_pos x).ne' h3x
  have huN : u ∈ N := N.pow_mem hxN _
  have hu3' : u ^ 3 = 1 := by
    have := pow_orderOf_eq_one u
    rwa [hu3] at this
  have hu1 : u ≠ 1 := fun h => by
    rw [h, orderOf_one] at hu3
    exact absurd hu3 (by norm_num)
  have hτ2 : (M.Φ σ : Equiv.Perm (Fin 26)) ^ 2 = 1 := by
    have h := M.Φ_mul σ σ
    rw [hσ, M.Φ_one] at h
    rw [pow_two]
    exact h.symm
  have hu0P : (M.e u : Equiv.Perm (Fin 26)) ∈ L33.QP.originalSubgroup := (hmemP _).1 (M.e u).2
  have hu03 : (M.e u : Equiv.Perm (Fin 26)) ^ 3 = 1 := by
    have h : (M.e u) ^ 3 = 1 := by rw [← map_pow, hu3', map_one]
    simpa using congrArg Subtype.val h
  have hu01 : (M.e u : Equiv.Perm (Fin 26)) ≠ 1 := fun h =>
    hu1 (M.e.injective (Subtype.ext (by simpa using h)))
  have hτu : (M.Φ σ : Equiv.Perm (Fin 26)) * (M.e u : Equiv.Perm (Fin 26)) =
      (M.e u : Equiv.Perm (Fin 26)) * (M.Φ σ : Equiv.Perm (Fin 26)) := by
    have h := M.spec σ u
    rw [hfix u huN] at h
    calc (M.Φ σ : Equiv.Perm (Fin 26)) * (M.e u : Equiv.Perm (Fin 26))
        = ((M.Φ σ : Equiv.Perm (Fin 26)) * (M.e u : Equiv.Perm (Fin 26)) *
            (M.Φ σ : Equiv.Perm (Fin 26))⁻¹) * (M.Φ σ : Equiv.Perm (Fin 26)) := by group
      _ = (M.e u : Equiv.Perm (Fin 26)) * (M.Φ σ : Equiv.Perm (Fin 26)) := by rw [← h]
  obtain ⟨c, hcP, hcτ, hc27⟩ := hsound _ (hmemA _ (M.Φ σ).2) hτ2 _ hu0P hu03 hu01 hτu
  set y : Y := M.e.symm ⟨c, (hmemP c).2 hcP⟩ with hy
  have hyc : (M.e y : Equiv.Perm (Fin 26)) = c :=
    congrArg Subtype.val (M.e.apply_symm_apply ⟨c, (hmemP c).2 hcP⟩)
  have hσy : σ y = y := by
    apply M.e.injective
    apply Subtype.ext
    rw [M.spec σ y, hyc]
    calc (M.Φ σ : Equiv.Perm (Fin 26)) * c * (M.Φ σ : Equiv.Perm (Fin 26))⁻¹
        = c * (M.Φ σ : Equiv.Perm (Fin 26)) * (M.Φ σ : Equiv.Perm (Fin 26))⁻¹ := by rw [hcτ]
      _ = c := by group
  have hzz : u * (y * u * y⁻¹) ∈ N := N.mul_mem huN (hnorm y hσy u huN)
  have hz27 : (u * (y * u * y⁻¹)) ^ 27 = 1 := by
    obtain ⟨k, hk⟩ := hN3.exists_orderOf_eq_pow (⟨_, hzz⟩ : N)
    rw [Subgroup.orderOf_mk] at hk
    have hdvd : 3 ^ k ∣ 5616 := hk ▸ hcardY ▸ orderOf_dvd_natCard _
    have hk3 : k ≤ 3 := by
      by_contra hlt
      have h81 : 3 ^ 4 ∣ 3 ^ k := pow_dvd_pow 3 (by omega)
      have := h81.trans hdvd
      norm_num at this
    rw [← orderOf_dvd_iff_pow_eq_one, hk]
    exact (pow_dvd_pow 3 hk3 : 3 ^ k ∣ 3 ^ 3)
  apply hc27
  have h := congrArg (fun z : Y => ((M.e z : M.P) : Equiv.Perm (Fin 26))) hz27
  simp only [map_pow, map_mul, map_inv, Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_inv,
    hyc, map_one, Subgroup.coe_one] at h
  exact h

end CFSG.OddStandard.SmallF3.Omega
