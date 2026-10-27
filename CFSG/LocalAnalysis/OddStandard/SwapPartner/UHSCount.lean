module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.UBasic
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.UThompson
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.UD8B
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.UPerm

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup Equiv Equiv.Perm CFSG.OddStandard.AltStdSec.SwapPattern

variable {G : Type} [Group G] {z : G} {ι ιd : Perm (Fin 10) →* G}

private theorem u_inv_zpow_cases {H : Type*} [Group H] {x : H} (hx : x * x = 1) (i : ℤ) :
    x ^ i = 1 ∨ x ^ i = x := by
  have h2 : x ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hx
  rw [zpow_eq_zpow_emod i h2]
  rcases Int.emod_two_eq_zero_or_one i with h | h <;> rw [h] <;> simp

private theorem u_zpowers_inf_eq_bot {M : Type*} [Group M] {x y : M} (hx : x * x = 1)
    (hy : y * y = 1) (hx1 : x ≠ 1) (hxy : x ≠ y) :
    Subgroup.zpowers x ⊓ Subgroup.zpowers y = ⊥ := by
  apply le_antisymm _ bot_le
  intro w hw
  rw [Subgroup.mem_inf] at hw
  obtain ⟨hw1, hw2⟩ := hw
  rw [Subgroup.mem_bot]
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw1
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hw2
  rcases u_inv_zpow_cases hx m with hm | hm
  · exact hm
  · rw [hm]
    rcases u_inv_zpow_cases hy n with hn1 | hn1
    · rw [hn1, hm] at hn
      exact hn.symm
    · rw [hn1, hm] at hn
      exact absurd hn.symm hxy

private theorem u_two_mul_card_le_of_lt {M : Type*} [Group M] [Finite M] {Q P : Subgroup M}
    (hle : Q ≤ P) (hne : Q ≠ P) : 2 * Nat.card Q ≤ Nat.card P := by
  have hdvd : Nat.card Q ∣ Nat.card P := Subgroup.card_dvd_of_le hle
  obtain ⟨m, hm⟩ := hdvd
  haveI : Nonempty ↥P := ⟨1⟩
  have hPpos : 0 < Nat.card P := Nat.card_pos
  have hm0 : m ≠ 0 := by
    intro hm0
    rw [hm0, mul_zero] at hm
    omega
  have hm1 : m ≠ 1 := by
    intro hm1
    apply hne
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [hm, hm1, mul_one]
  have hm2 : 2 ≤ m := by omega
  calc 2 * Nat.card Q = Nat.card Q * 2 := Nat.mul_comm 2 _
    _ ≤ Nat.card Q * m := Nat.mul_le_mul_left _ hm2
    _ = Nat.card P := hm.symm

theorem four_mul_card_le_of_commute (F : UFrame z ι ιd) [Finite G] {C : Subgroup G}
    (hCx : ∀ c ∈ C, z * ι τ₀ * c = c * (z * ι τ₀))
    (hCg : ∀ c ∈ C, gElt ιd * c = c * gElt ιd)
    (hCd : ∀ c ∈ C, ι (swap 0 1) * c = c * ι (swap 0 1))
    (hx : z * ι τ₀ ∉ C) (hg : gElt ιd ∉ C) (hgx : gElt ιd * (z * ι τ₀) ∉ C) :
    4 * Nat.card ↥C ≤ 5760 := by
  classical
  have hd8 : D8Rel z (gElt ιd) (z * ι τ₀) := F.d8
  have hx2g : Commute (z * ι τ₀) (gElt ιd) := (commute_iff_eq _ _).mpr hd8.x_comm_g
  have hcomm_gen : ∀ a ∈ Subgroup.zpowers (z * ι τ₀), ∀ b ∈ Subgroup.zpowers (gElt ιd),
      a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (hx2g.zpow_zpow i j).eq
  have hx2_order : orderOf (z * ι τ₀) = 2 :=
    orderOf_eq_prime (p := 2) (by rw [pow_two]; exact hd8.x_sq) hd8.x_ne
  have hg_order : orderOf (gElt ιd) = 2 :=
    orderOf_eq_prime (p := 2) (by rw [pow_two]; exact hd8.g_sq) (D8Rel.u_g_ne_one hd8)
  have hdisj_inner : Subgroup.zpowers (z * ι τ₀) ⊓ Subgroup.zpowers (gElt ιd) = ⊥ :=
    u_zpowers_inf_eq_bot hd8.x_sq hd8.g_sq hd8.x_ne (D8Rel.u_g_ne_x hd8).symm
  set W : Subgroup G := Subgroup.zpowers (z * ι τ₀) ⊔ Subgroup.zpowers (gElt ιd) with hW
  set P : Subgroup G :=
    Subgroup.centralizer ({ι (swap 0 1)} : Set G) ⊓
      Subgroup.centralizer ({z * ι τ₀} : Set G) with hP
  set Q : Subgroup G := P ⊓ Subgroup.centralizer ({gElt ιd} : Set G) with hQ
  have hWcard : Nat.card W = 4 := by
    rw [hW, card_sup_of_commute (D := Subgroup.zpowers (z * ι τ₀))
      (Q := Subgroup.zpowers (gElt ιd)) hcomm_gen hdisj_inner,
      Nat.card_zpowers, Nat.card_zpowers, hx2_order, hg_order]
  have hx2_d : (z * ι τ₀) * ι (swap 0 1) = ι (swap 0 1) * (z * ι τ₀) := by
    have hτd : ι τ₀ * ι (swap 0 1) = ι (swap 0 1) * ι τ₀ := by
      rw [← map_mul, ← map_mul]
      congr 1
      decide
    calc (z * ι τ₀) * ι (swap 0 1)
        = z * (ι τ₀ * ι (swap 0 1)) := by group
      _ = z * (ι (swap 0 1) * ι τ₀) := by rw [hτd]
      _ = (z * ι (swap 0 1)) * ι τ₀ := by group
      _ = (ι (swap 0 1) * z) * ι τ₀ := by rw [F.cent.comm (swap 0 1)]
      _ = ι (swap 0 1) * (z * ι τ₀) := by group
  have hgg_d : gElt ιd * ι (swap 0 1) = ι (swap 0 1) * gElt ιd := by
    simpa [liftS8_swap_zero_one] using F.g_comm (swap 0 1)
  have hx2P : z * ι τ₀ ∈ P := by
    rw [hP, Subgroup.mem_inf]
    exact ⟨Subgroup.mem_centralizer_singleton_iff.mpr hx2_d,
      Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hggP : gElt ιd ∈ P := by
    rw [hP, Subgroup.mem_inf]
    exact ⟨Subgroup.mem_centralizer_singleton_iff.mpr hgg_d,
      Subgroup.mem_centralizer_singleton_iff.mpr hd8.x_comm_g.symm⟩
  have hWleP : W ≤ P := by
    rw [hW]
    apply sup_le
    · rw [Subgroup.zpowers_le]; exact hx2P
    · rw [Subgroup.zpowers_le]; exact hggP
  have hCLeP : C ≤ P := by
    intro c hc
    rw [hP, Subgroup.mem_inf]
    exact ⟨Subgroup.mem_centralizer_singleton_iff.mpr (hCd c hc).symm,
      Subgroup.mem_centralizer_singleton_iff.mpr (hCx c hc).symm⟩
  have hCWcomm : ∀ c ∈ C, ∀ w ∈ W, c * w = w * c := by
    intro c hc w hw
    have hWle : W ≤ Subgroup.centralizer ({c} : Set G) := by
      rw [hW]
      apply sup_le
      · rw [Subgroup.zpowers_le]
        exact Subgroup.mem_centralizer_singleton_iff.mpr (hCx c hc)
      · rw [Subgroup.zpowers_le]
        exact Subgroup.mem_centralizer_singleton_iff.mpr (hCg c hc)
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hWle hw)).symm
  have hCWdisj : C ⊓ W = ⊥ := by
    apply le_antisymm _ bot_le
    intro t ht
    rw [Subgroup.mem_inf] at ht
    obtain ⟨htC, htW⟩ := ht
    rw [Subgroup.mem_bot]
    rw [hW] at htW
    rw [mem_sup_iff_of_commute hcomm_gen] at htW
    obtain ⟨a, ha, b, hb, rfl⟩ := htW
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    rcases u_inv_zpow_cases hd8.x_sq i with hi | hi
    · rw [hi, one_mul]
      rcases u_inv_zpow_cases hd8.g_sq j with hj | hj
      · exact hj
      · rw [hj] at htC ⊢
        exact absurd (by simpa [hi] using htC) hg
    · rw [hi]
      rcases u_inv_zpow_cases hd8.g_sq j with hj | hj
      · rw [hj, mul_one] at htC ⊢
        exact absurd (by simpa [hi] using htC) hx
      · rw [hj] at htC ⊢
        exact absurd (hd8.x_comm_g ▸ (by simpa [hi] using htC)) hgx
  have hCleCent : C ≤ Subgroup.centralizer ({gElt ιd} : Set G) := fun c hc =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hCg c hc).symm
  have hWleCent : W ≤ Subgroup.centralizer ({gElt ιd} : Set G) := by
    rw [hW]
    apply sup_le
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_centralizer_singleton_iff.mpr hd8.x_comm_g
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hCsupW_le_Q : C ⊔ W ≤ Q := by
    rw [hQ]
    exact le_inf (sup_le hCLeP hWleP) (sup_le hCleCent hWleCent)
  have hzP : z ∈ P := by
    rw [hP, Subgroup.mem_inf]
    exact ⟨Subgroup.mem_centralizer_singleton_iff.mpr (F.cent.comm (swap 0 1)),
      Subgroup.mem_centralizer_singleton_iff.mpr (D8Rel.x_comm_z hd8).symm⟩
  have hznotQ : z ∉ Q := by
    rw [hQ, Subgroup.mem_inf]
    rintro ⟨_, hzcent⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hzcent
    have hzg : gElt ιd * z * gElt ιd = z := by
      calc gElt ιd * z * gElt ιd = (gElt ιd * z) * gElt ιd := by rw [mul_assoc]
        _ = (z * gElt ιd) * gElt ιd := by rw [hzcent.symm]
        _ = z * (gElt ιd * gElt ιd) := by rw [mul_assoc]
        _ = z := by rw [hd8.g_sq, mul_one]
    exact F.cent.ne_z τ₀ (by rw [← F.g_z_g]; exact hzg)
  have hQleP : Q ≤ P := by rw [hQ]; exact inf_le_left
  have hQneP : Q ≠ P := by
    intro heq
    rw [heq] at hznotQ
    exact hznotQ hzP
  have hPcard : Nat.card P = 11520 := by
    rw [hP]
    show pairOrder (ι (swap 0 1)) (z * ι τ₀) = 11520
    rw [F.pairOrder_d_x₂]
    norm_num [N10, Nat.factorial]
  have hcardQ_le : Nat.card Q ≤ 5760 := by
    have h := u_two_mul_card_le_of_lt hQleP hQneP
    rw [hPcard] at h
    omega
  have hcard_sup : Nat.card ↥(C ⊔ W) = Nat.card C * Nat.card W :=
    card_sup_of_commute hCWcomm hCWdisj
  calc 4 * Nat.card C = Nat.card C * 4 := Nat.mul_comm 4 _
    _ = Nat.card ↥(C ⊔ W) := by rw [hcard_sup, hWcard]
    _ ≤ Nat.card Q := Subgroup.card_le_of_le hCsupW_le_Q
    _ ≤ 5760 := hcardQ_le

end CFSG.OddStandard.AltStdSec.SwapPartner
