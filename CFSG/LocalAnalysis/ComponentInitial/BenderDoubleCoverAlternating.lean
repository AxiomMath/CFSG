module

public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import CFSG.StronglyEmbedded.Catalog

public section

namespace CFSG.LocalAnalysis.ComponentInitial.BenderDoubleCover

open Equiv

set_option synthInstance.maxSize 2048 in
set_option synthInstance.maxHeartbeats 1000000 in
theorem exists_conj_eq_swap_mul_swap : ∀ x : Perm (Fin 5), x ^ 4 = 1 → x ≠ 1 →
    Perm.sign x = 1 → ∃ g : Perm (Fin 5), g * x * g⁻¹ = swap 0 1 * swap 2 3 := by
  decide +kernel

set_option synthInstance.maxSize 2048 in
set_option synthInstance.maxHeartbeats 1000000 in
theorem sign_eq_one_of_commute_swap_mul_swap : ∀ σ y : Perm (Fin 5), y ^ 4 = 1 → y ≠ 1 →
    Perm.sign y = 1 → y ≠ swap 0 1 * swap 2 3 → (y * (swap 0 1 * swap 2 3)) ^ 4 = 1 →
    σ * (swap 0 1 * swap 2 3) = swap 0 1 * swap 2 3 * σ → σ * y = y * σ →
    Perm.sign σ = 1 := by
  decide +kernel

theorem sign_conj (g a : Perm (Fin 5)) : Perm.sign (MulAut.conj g a) = Perm.sign a := by
  rw [MulAut.conj_apply, Perm.sign_mul, Perm.sign_mul, Perm.sign_inv, mul_right_comm,
    Int.units_mul_self, one_mul]

theorem sign_eq_one_of_commute {σ x y : Perm (Fin 5)} (hx4 : x ^ 4 = 1) (hx1 : x ≠ 1)
    (hxs : Perm.sign x = 1) (hy4 : y ^ 4 = 1) (hy1 : y ≠ 1) (hys : Perm.sign y = 1)
    (hxy : x ≠ y) (hyx : (y * x) ^ 4 = 1) (hσx : σ * x = x * σ) (hσy : σ * y = y * σ) :
    Perm.sign σ = 1 := by
  obtain ⟨g, hg⟩ := exists_conj_eq_swap_mul_swap x hx4 hx1 hxs
  set c := MulAut.conj g
  have hcx : c x = swap 0 1 * swap 2 3 := by rw [MulAut.conj_apply]; exact hg
  have h := sign_eq_one_of_commute_swap_mul_swap (c σ) (c y)
    (by rw [← map_pow, hy4, map_one]) (by rwa [ne_eq, map_eq_one_iff c c.injective])
    (by rw [sign_conj, hys]) (by rw [← hcx]; exact c.injective.ne hxy.symm)
    (by rw [← hcx, ← map_mul, ← map_pow, hyx, map_one])
    (by rw [← hcx, ← map_mul, ← map_mul, hσx]) (by rw [← map_mul, ← map_mul, hσy])
  rwa [sign_conj] at h

theorem pow_four_eq_one_of_mem_sylow {B : Type*} [Group B] [Finite B] (hB : Nat.card B = 60)
    (S : Sylow 2 B) {s : B} (hs : s ∈ (S : Subgroup B)) : s ^ 4 = 1 := by
  obtain ⟨k, hk⟩ := S.isPGroup' ⟨s, hs⟩
  have hk' : s ^ 2 ^ k = 1 := congrArg Subtype.val hk
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk')
  have h60 : orderOf s ∣ 60 := hB ▸ orderOf_dvd_natCard s
  have hj2 : j ≤ 2 := by
    by_contra hj3
    have h8 : 2 ^ 3 ∣ 60 := (Nat.pow_dvd_pow 2 (by omega)).trans (hj ▸ h60)
    norm_num at h8
  exact orderOf_dvd_iff_pow_eq_one.mp (hj ▸ Nat.pow_dvd_pow 2 hj2)

theorem exists_eq_conj_of_card_sixty {B : Type*} [Group B] [Finite B] [IsSimpleGroup B]
    (hB : Nat.card B = 60) (α : MulAut B) (S : Sylow 2 B)
    (hα : ∀ s ∈ (S : Subgroup B), α s = s) : ∃ b : B, α = MulAut.conj b := by
  obtain ⟨e⟩ := CFSG.BenderSuzuki.nonempty_mulEquiv_alternatingGroup_five hB
  obtain ⟨σ, hσ⟩ := (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5
    (by norm_num) (by norm_num)).2 ((e.symm.trans α).trans e)
  have hfix : ∀ s ∈ (S : Subgroup B), σ * (e s : Perm (Fin 5)) = (e s : Perm (Fin 5)) * σ := by
    intro s hs
    have h1 : MulAut.conjNormal σ (e s) = e s := by
      rw [hσ]
      change e (α (e.symm (e s))) = e s
      rw [e.symm_apply_apply, hα s hs]
    have h2 : σ * (e s : Perm (Fin 5)) * σ⁻¹ = e s := by
      rw [← MulAut.conjNormal_apply]
      exact congrArg Subtype.val h1
    calc σ * (e s : Perm (Fin 5)) = σ * (e s : Perm (Fin 5)) * σ⁻¹ * σ := by group
      _ = e s * σ := by rw [h2]
  have : Fintype S := Fintype.ofFinite S
  have h2 : 2 < Fintype.card S := by
    have h4 : 2 ^ 2 ∣ Nat.card S := S.pow_dvd_card_of_pow_dvd_card (by rw [hB]; norm_num)
    have h4' := Nat.le_of_dvd Nat.card_pos h4
    rw [Nat.card_eq_fintype_card] at h4'
    omega
  obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.mp h2
  obtain ⟨x, y, hx1, hy1, hxy⟩ : ∃ x y : S, x ≠ 1 ∧ y ≠ 1 ∧ x ≠ y := by
    by_cases ha : a = 1
    · exact ⟨b, c, fun h => hab (ha.trans h.symm), fun h => hac (ha.trans h.symm), hbc⟩
    by_cases hb : b = 1
    · exact ⟨a, c, ha, fun h => hbc (hb.trans h.symm), hac⟩
    exact ⟨a, b, ha, hb, hab⟩
  have hpow : ∀ s : S, ((e s : alternatingGroup (Fin 5)) : Perm (Fin 5)) ^ 4 = 1 := fun s => by
    rw [← Subgroup.coe_pow, ← map_pow, pow_four_eq_one_of_mem_sylow hB S s.2, map_one]
    rfl
  have hne : ∀ s : S, s ≠ 1 → ((e s : alternatingGroup (Fin 5)) : Perm (Fin 5)) ≠ 1 :=
    fun s hs h => hs (Subtype.ext (e.injective ((Subtype.ext h).trans (map_one e).symm)))
  have hsign : ∀ s : S, Perm.sign ((e s : alternatingGroup (Fin 5)) : Perm (Fin 5)) = 1 :=
    fun s => Perm.mem_alternatingGroup.mp (e s).2
  have hσs : Perm.sign σ = 1 := sign_eq_one_of_commute (x := e x) (y := e y) (hpow x) (hne x hx1)
    (hsign x) (hpow y) (hne y hy1) (hsign y)
    (fun h => hxy (Subtype.ext (e.injective (Subtype.ext h))))
    (by rw [← Subgroup.coe_mul, ← map_mul]; exact hpow ⟨_, (S : Subgroup B).mul_mem y.2 x.2⟩)
    (hfix x x.2) (hfix y y.2)
  refine ⟨e.symm ⟨σ, Perm.mem_alternatingGroup.mpr hσs⟩, MulEquiv.ext fun g => ?_⟩
  have h3 : e (α g) = MulAut.conjNormal σ (e g) := by
    rw [hσ]
    change e (α g) = e (α (e.symm (e g)))
    rw [e.symm_apply_apply]
  apply e.injective
  rw [h3, MulAut.conj_apply, map_mul, map_mul, map_inv, e.apply_symm_apply]
  exact Subtype.ext (MulAut.conjNormal_apply σ (e g))

end CFSG.LocalAnalysis.ComponentInitial.BenderDoubleCover
