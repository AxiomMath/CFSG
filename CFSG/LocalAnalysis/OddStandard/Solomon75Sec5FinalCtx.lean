module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5FinalGroup

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS

structure Sec5Ctx (X : Type) [Group X] [Finite X] (n : ℕ) (z : X) (N A : Subgroup X)
    (M : AhatModel X n A) : Prop where
  hn : 8 ≤ n
  hz : orderOf z = 2
  hNz : ∀ c ∈ N, z * c = c * z
  hAN : A ≤ N
  hNA : N ≤ normalizer (A : Set X)
  hzA : z ∈ A
  hQ : ∀ c (hc : c ∈ N), M.perm c (hNA hc) = 1 → c ∈ oddCoreOf N ⊔ zpowers z

namespace Sec5Ctx

variable {X : Type} [Group X] [Finite X] {n : ℕ} {z : X} {N A : Subgroup X} {M : AhatModel X n A}

@[expose] noncomputable def psi (h : Sec5Ctx X n z N A M) : ↥N →* Perm (Fin n) :=
  (M.permHom h.hn).comp (Subgroup.inclusion h.hNA)

theorem psi_apply (h : Sec5Ctx X n z N A M) (c : ↥N) :
    h.psi c = M.perm c (h.hNA c.2) := rfl

theorem psi_of_mem (h : Sec5Ctx X n z N A M) {a : X} (ha : a ∈ A) :
    h.psi ⟨a, h.hAN ha⟩ = M.C.ρ (M.e (QuotientGroup.mk (⟨a, ha⟩ : ↥A))) :=
  M.perm_of_mem h.hn ha

theorem exists_mem_psi_eq (h : Sec5Ctx X n z N A M) {σ : Perm (Fin n)} (hσ : sign σ = 1) :
    ∃ (a : X) (ha : a ∈ A), h.psi ⟨a, h.hAN ha⟩ = σ := by
  obtain ⟨k, hk⟩ := M.C.exists_ρ_eq hσ
  obtain ⟨a, rfl⟩ := M.surj_mk k
  exact ⟨a, a.2, by rw [h.psi_of_mem a.2]; exact hk⟩

theorem psi_eq_one_imp (h : Sec5Ctx X n z N A M) {c : X} (hc : c ∈ N)
    (h1 : h.psi ⟨c, hc⟩ = 1) : c ∈ oddCoreOf N ⊔ zpowers z :=
  h.hQ c hc h1

omit [Finite X] in
theorem exists_of_mem_sup_zpowers {P : Subgroup X} (hP : ∀ p ∈ P, z * p = p * z) {x : X}
    (hx : x ∈ P ⊔ zpowers z) : ∃ p ∈ P, ∃ m : ℤ, x = p * z ^ m := by
  let T : Subgroup X :=
    { carrier := {x | ∃ p ∈ P, ∃ m : ℤ, x = p * z ^ m}
      one_mem' := ⟨1, one_mem _, 0, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨p, hp, m, rfl⟩ ⟨q, hq, l, rfl⟩
        refine ⟨p * q, mul_mem hp hq, m + l, ?_⟩
        have hc : Commute (z ^ m) q := (Commute.zpow_left (hP q hq) m)
        calc p * z ^ m * (q * z ^ l) = p * (z ^ m * q) * z ^ l := by group
          _ = p * (q * z ^ m) * z ^ l := by rw [hc.eq]
          _ = p * q * z ^ (m + l) := by rw [zpow_add]; group
      inv_mem' := by
        rintro _ ⟨p, hp, m, rfl⟩
        refine ⟨p⁻¹, inv_mem hp, -m, ?_⟩
        have hc : Commute (z ^ m) p := (Commute.zpow_left (hP p hp) m)
        calc (p * z ^ m)⁻¹ = (z ^ m)⁻¹ * p⁻¹ := by rw [mul_inv_rev]
          _ = p⁻¹ * (z ^ m)⁻¹ := ((hc.inv_left.inv_right).eq)
          _ = p⁻¹ * z ^ (-m) := by rw [zpow_neg] }
  have hPT : P ≤ T := fun p hp => ⟨p, hp, 0, by simp⟩
  have hZT : zpowers z ≤ T := by
    rw [Subgroup.zpowers_le]
    exact ⟨1, one_mem _, 1, by simp⟩
  exact (sup_le hPT hZT) hx

theorem exists_decomp (h : Sec5Ctx X n z N A M) {w : X} (hwN : w ∈ N)
    (hw : sign (h.psi ⟨w, hwN⟩) = 1) :
    ∃ (a : X) (_ : a ∈ A), ∃ o ∈ oddCoreOf N, w = a * o := by
  obtain ⟨a, ha, hψa⟩ := h.exists_mem_psi_eq hw
  set q : X := a⁻¹ * w with hq
  have hqN : q ∈ N := mul_mem (inv_mem (h.hAN ha)) hwN
  have h1 : h.psi ⟨q, hqN⟩ = 1 := by
    have hmul : (⟨w, hwN⟩ : ↥N) = ⟨a, h.hAN ha⟩ * ⟨q, hqN⟩ := by
      apply Subtype.ext
      simp [hq]
    have h2 : h.psi ⟨w, hwN⟩ = h.psi ⟨a, h.hAN ha⟩ * h.psi ⟨q, hqN⟩ := by
      rw [← map_mul, ← hmul]
    rw [hψa] at h2
    exact mul_left_cancel (a := h.psi ⟨w, hwN⟩) (by rw [← h2, mul_one])
  obtain ⟨o, ho, m, hom⟩ := exists_of_mem_sup_zpowers
    (fun p hp => h.hNz p (oddCoreOf_le N hp)) (h.psi_eq_one_imp hqN h1)
  refine ⟨a * z ^ m, mul_mem ha (zpow_mem h.hzA m), o, ho, ?_⟩
  have hc : Commute (z ^ m) o := Commute.zpow_left (h.hNz o (oddCoreOf_le N ho)) m
  have hwq : w = a * q := by simp [hq]
  calc w = a * q := hwq
    _ = a * (o * z ^ m) := by rw [hom]
    _ = a * (z ^ m * o) := by rw [← hc.eq]
    _ = a * z ^ m * o := by group

theorem sq_z (h : Sec5Ctx X n z N A M) : z * z = 1 := by
  have := pow_orderOf_eq_one z
  rw [h.hz, sq] at this
  exact this

@[expose] noncomputable def zbar (h : Sec5Ctx X n z N A M) : M.K :=
  M.e (QuotientGroup.mk (⟨z, h.hzA⟩ : ↥A))

theorem zbar_mem_center (h : Sec5Ctx X n z N A M) : h.zbar ∈ center M.K := by
  rw [Subgroup.mem_center_iff]
  intro k
  obtain ⟨b, rfl⟩ := M.surj_mk k
  unfold zbar
  rw [← map_mul, ← map_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 2
  apply Subtype.ext
  exact (h.hNz b (h.hAN b.2)).symm

theorem zbar_ne_one (h : Sec5Ctx X n z N A M) : h.zbar ≠ 1 := by
  intro h1
  have h2 : (QuotientGroup.mk (⟨z, h.hzA⟩ : ↥A) : ↥A ⧸ pPrimeCore 2 ↥A) = 1 := by
    apply M.e.injective
    rw [map_one]
    exact h1
  have h3 := (QuotientGroup.eq_one_iff _).1 h2
  have h4 : z ∈ oddCoreOf A := mem_oddCoreOf_iff.2 ⟨h.hzA, h3⟩
  have h5 := eq_one_of_sq_eq_one_of_mem_odd (odd_card_oddCoreOf A) h4 h.sq_z
  have := h.hz
  rw [h5, orderOf_one] at this
  exact absurd this (by norm_num)

theorem eq_zbar_of_mem_center (h : Sec5Ctx X n z N A M) {k : M.K} (hk : k ∈ center M.K)
    (hk1 : k ≠ 1) : k = h.zbar :=
  M.C.center_eq_of_ne_one hk h.zbar_mem_center hk1 h.zbar_ne_one

theorem psi_z (h : Sec5Ctx X n z N A M) : h.psi ⟨z, h.hAN h.hzA⟩ = 1 := by
  rw [h.psi_of_mem h.hzA]
  exact (M.C.ρ_eq_one_iff).2 h.zbar_mem_center

theorem oddCoreOf_le_oddCoreOf (h : Sec5Ctx X n z N A M) : oddCoreOf A ≤ oddCoreOf N :=
  (oddCoreOf_eq_inf h.hAN h.hNA).le.trans inf_le_right

theorem exists_data_of_involution (h : Sec5Ctx X n z N A M) {w : X} (hwN : w ∈ N)
    (hw2 : w * w = 1) (hw1 : w ≠ 1) (hwz : w ≠ z) (hw : sign (h.psi ⟨w, hwN⟩) = 1) :
    ∃ (a : X) (ha : a ∈ A), (∃ o ∈ oddCoreOf N, w = a * o) ∧
      orderOf (M.e (QuotientGroup.mk (⟨a, ha⟩ : ↥A))) = 2 ∧
      M.e (QuotientGroup.mk (⟨a, ha⟩ : ↥A)) ∉ center M.K := by
  obtain ⟨a, ha, o, ho, hwao⟩ := h.exists_decomp hwN hw
  have hodd := odd_card_oddCoreOf N
  have hoN : o ∈ N := oddCoreOf_le N ho
  have haN : a ∈ N := h.hAN ha
  have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
  have haa : a * a ∈ oddCoreOf N := by
    have h1 : a * a = (w * o⁻¹ * w⁻¹) * o⁻¹ := by
      have : a = w * o⁻¹ := by rw [hwao]; group
      rw [hwi]
      nth_rewrite 1 [this]
      nth_rewrite 1 [this]
      group
    rw [h1]
    refine mul_mem ?_ (inv_mem ho)
    have := (Subgroup.mem_normalizer_iff.1 (le_normalizer_oddCoreOf N hwN)) o⁻¹
    exact this.1 (inv_mem ho)
  have haaA : a * a ∈ oddCoreOf A := by
    rw [oddCoreOf_eq_inf h.hAN h.hNA]
    exact ⟨mul_mem ha ha, haa⟩
  have hsqA : M.e (QuotientGroup.mk (⟨a, ha⟩ : ↥A)) *
      M.e (QuotientGroup.mk (⟨a, ha⟩ : ↥A)) = 1 := by
    rw [← map_mul, ← QuotientGroup.mk_mul, ← map_one M.e]
    congr 1
    rw [QuotientGroup.eq_one_iff]
    obtain ⟨_, hP⟩ := mem_oddCoreOf_iff.1 haaA
    exact hP
  have hne1 : M.e (QuotientGroup.mk (⟨a, ha⟩ : ↥A)) ≠ 1 := by
    intro h1
    have h2 : (QuotientGroup.mk (⟨a, ha⟩ : ↥A) : ↥A ⧸ pPrimeCore 2 ↥A) = 1 := by
      apply M.e.injective
      rw [map_one]
      exact h1
    have h3 := (QuotientGroup.eq_one_iff _).1 h2
    have h4 : a ∈ oddCoreOf A := mem_oddCoreOf_iff.2 ⟨ha, h3⟩
    have h5 : w ∈ oddCoreOf N := by
      rw [hwao]
      exact mul_mem (h.oddCoreOf_le_oddCoreOf h4) ho
    exact hw1 (eq_one_of_sq_eq_one_of_mem_odd hodd h5 hw2)
  refine ⟨a, ha, ⟨o, ho, hwao⟩, ?_, ?_⟩
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [sq]; exact hsqA) hne1
  · intro hc
    have h1 := h.eq_zbar_of_mem_center hc hne1
    unfold zbar at h1
    have h2 := M.e.injective h1
    have h3 := (QuotientGroup.eq).1 h2
    have h4 : z⁻¹ * a ∈ oddCoreOf A := by
      rw [mem_oddCoreOf_iff]
      refine ⟨mul_mem (inv_mem h.hzA) ha, ?_⟩
      have : (⟨z, h.hzA⟩ : ↥A)⁻¹ * ⟨a, ha⟩ = ⟨z⁻¹ * a, mul_mem (inv_mem h.hzA) ha⟩ := rfl
      rw [← this]
      exact (QuotientGroup.eq.1 h2.symm)
    have h5 : z⁻¹ * a ∈ oddCoreOf N := h.oddCoreOf_le_oddCoreOf h4
    set p := (z⁻¹ * a) * o with hp
    have hpO : p ∈ oddCoreOf N := mul_mem h5 ho
    have hwzp : w = z * p := by rw [hp, hwao]; group
    have hzp : z * p = p * z := h.hNz p (oddCoreOf_le N hpO)
    have hpp : p * p = 1 := by
      have h6 : (z * p) * (z * p) = 1 := by rw [← hwzp]; exact hw2
      calc p * p = (z * z) * (p * p) := by rw [h.sq_z, one_mul]
        _ = z * (z * p) * p := by group
        _ = z * (p * z) * p := by rw [hzp]
        _ = (z * p) * (z * p) := by group
        _ = 1 := h6
    have hp1 := eq_one_of_sq_eq_one_of_mem_odd hodd hpO hpp
    apply hwz
    rw [hwzp, hp1, mul_one]

theorem exists_conj_of_involutions (h : Sec5Ctx X n z N A M)
    (hone : ∀ u v : M.K, orderOf u = 2 → orderOf v = 2 → u ∉ center M.K → v ∉ center M.K →
      IsConj u v)
    {w s : X} (hwN : w ∈ N) (hsN : s ∈ N) (hw2 : w * w = 1) (hs2 : s * s = 1) (hw1 : w ≠ 1)
    (hs1 : s ≠ 1) (hwz : w ≠ z) (hsz : s ≠ z) (hw : sign (h.psi ⟨w, hwN⟩) = 1)
    (hs : sign (h.psi ⟨s, hsN⟩) = 1) : ∃ g : X, w = g⁻¹ * s * g := by
  obtain ⟨aw, haw, ⟨ow, how, hwao⟩, hord_w, hnc_w⟩ := h.exists_data_of_involution hwN hw2 hw1 hwz hw
  obtain ⟨as, has, ⟨os, hos, hsas⟩, hord_s, hnc_s⟩ := h.exists_data_of_involution hsN hs2 hs1 hsz hs
  obtain ⟨c, hc⟩ := isConj_iff.1 (hone _ _ hord_w hord_s hnc_w hnc_s)
  obtain ⟨κ, rfl⟩ := M.surj_mk c
  have h1 : M.e (QuotientGroup.mk (κ * ⟨aw, haw⟩ * κ⁻¹)) =
      M.e (QuotientGroup.mk (⟨as, has⟩ : ↥A)) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_mul, map_inv]
    exact hc
  have h3 := QuotientGroup.eq.1 (M.e.injective h1)
  have hodd := odd_card_oddCoreOf N
  set k : X := (κ : X) with hk
  have hkN : k ∈ N := h.hAN κ.2
  have hu : (k * aw * k⁻¹)⁻¹ * as ∈ oddCoreOf N := by
    have hmem : (k * aw * k⁻¹)⁻¹ * as ∈ A :=
      mul_mem (inv_mem (mul_mem (mul_mem κ.2 haw) (inv_mem κ.2))) has
    exact h.oddCoreOf_le_oddCoreOf (mem_oddCoreOf_iff.2 ⟨hmem, h3⟩)
  have hnorm : ∀ x ∈ oddCoreOf N, k * x * k⁻¹ ∈ oddCoreOf N := fun x hx =>
    (Subgroup.mem_normalizer_iff.1 (le_normalizer_oddCoreOf N hkN) x).1 hx
  set w' : X := k * w * k⁻¹ with hw'
  have hw'2 : w' * w' = 1 := by
    calc w' * w' = k * (w * w) * k⁻¹ := by rw [hw']; group
      _ = 1 := by rw [hw2]; group
  have hxy : s⁻¹ * w' ∈ oddCoreOf N := by
    have e1 : s⁻¹ * w' = os⁻¹ * ((k * aw * k⁻¹)⁻¹ * as)⁻¹ * (k * ow * k⁻¹) := by
      rw [hw', hwao, hsas]; group
    rw [e1]
    exact mul_mem (mul_mem (inv_mem hos) (inv_mem hu)) (hnorm ow how)
  obtain ⟨q, hq, hwq⟩ := exists_conj_of_inv_mul_mem_odd hodd hs2 hw'2 hxy
  refine ⟨q * k, ?_⟩
  have : w = k⁻¹ * w' * k := by rw [hw']; group
  rw [this, hwq]
  group

end Sec5Ctx

end CFSG.OddStandard.Solomon75
