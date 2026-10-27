module

public import CFSG.CGT.Foote81L6.Bridge.CoreB
public import CFSG.CharacterTheory.BrauerLinearThree.CentralizerSylowBasic

public section

namespace CFSG.CGT.Foote81L6.Bridge

open Subgroup

variable {n : ℕ} (hn : 3 ≤ n)
include hn

theorem b₀T_mul_b₀T : b₀T hn * b₀T hn = 1 := by
  rw [← pow_two, ← orderOf_b₀T hn]; exact pow_orderOf_eq_one _

theorem b₁T_mul_b₁T : b₁T hn * b₁T hn = 1 := by
  rw [← pow_two, ← orderOf_b₁T hn]; exact pow_orderOf_eq_one _

theorem b₀T_mul_b₁T_ne_one : b₀T hn * b₁T hn ≠ 1 := by
  intro h
  apply b₀T_not_mem_B₁T hn
  rw [eq_inv_of_mul_eq_one_left h]
  exact inv_mem (b₁T_mem hn)

theorem hCT_pow_half : hCT hn ^ 2 ^ (n - 1) = b₀T hn * b₁T hn := by
  rw [show 2 ^ (n - 1) = 2 * 2 ^ (n - 2) by rw [← pow_succ']; congr 1; omega, pow_mul, pow_two,
    hCT_mul_hCT hn, ((commute_ρ₀T_ρ₁T hn).inv_inv).mul_pow, inv_pow, inv_pow, ← b₀T_eq hn,
    ← b₁T_eq hn, inv_eq_of_mul_eq_one_right (b₀T_mul_b₀T hn),
    inv_eq_of_mul_eq_one_right (b₁T_mul_b₁T hn)]

theorem orderOf_hCT : orderOf (hCT hn) = 2 ^ n := by
  have hb : Commute (b₀T hn) (b₁T hn) := B₀T_comm_B₁T hn _ (b₀T_mem hn) _ (b₁T_mem hn)
  have h := orderOf_eq_prime_pow (p := 2) (n := n - 1)
    (by rw [hCT_pow_half hn]; exact b₀T_mul_b₁T_ne_one hn)
    (by rw [pow_succ, pow_mul, hCT_pow_half hn, pow_two, hb.symm.mul_mul_mul_comm,
      b₀T_mul_b₀T hn, b₁T_mul_b₁T hn, one_mul])
  rwa [show n - 1 + 1 = n by omega] at h

theorem tCT_conj_hCT' : tCT n * hCT hn * (tCT n)⁻¹ = hCT hn ^ (2 ^ (n - 1) - 1) := by
  rw [tCT_conj_hCT hn, ← hCT_pow_half hn]
  obtain ⟨m, hm⟩ : ∃ m, 2 ^ (n - 1) = m + 1 := ⟨2 ^ (n - 1) - 1, by
    have : 1 ≤ 2 ^ (n - 1) := Nat.one_le_two_pow
    omega⟩
  rw [hm, Nat.add_sub_cancel, pow_succ', inv_mul_cancel_left]

theorem hCT_mem_BT : hCT hn ∈ BT hn :=
  mul_mem (mul_mem (mul_mem (B₀T_le_BT hn (κ₀T_mem_B₀T hn)) (B₁T_le_BT hn (κ₁T_mem_B₁T hn)))
    (B₁T_le_BT hn (b₁T_mem hn))) (sT_mem_BT hn)

theorem tCT_mem_BT : tCT n ∈ BT hn :=
  mul_mem (B₀T_le_BT hn (κ₀T_mem_B₀T hn)) (B₁T_le_BT hn (κ₁T_mem_B₁T hn))

theorem ρ₀T_mul_ρ₁T_eq : ρ₀T n * ρ₁T n = (hCT hn * hCT hn)⁻¹ := by
  rw [hCT_mul_hCT hn, mul_inv_rev, inv_inv, inv_inv, (commute_ρ₀T_ρ₁T hn).eq]

theorem mul_conj_tT_mem {u : TM n} (hu : u ∈ B₀T hn) :
    u * (tT n * u * (tT n)⁻¹) ∈ zpowers (hCT hn) ⊔ zpowers (tCT n) := by
  have hρ : ∀ k : ℕ, ρ₀T n ^ k * (tT n * ρ₀T n ^ k * (tT n)⁻¹) ∈
      zpowers (hCT hn) ⊔ zpowers (tCT n) := by
    intro k
    rw [← conj_pow, tT_conj_ρ₀T hn, ← (commute_ρ₀T_ρ₁T hn).mul_pow, ρ₀T_mul_ρ₁T_eq hn]
    exact mem_sup_left (pow_mem (inv_mem (mul_mem (mem_zpowers _) (mem_zpowers _))) _)
  obtain ⟨i, rfl | rfl⟩ := (mem_dihedralLift_range_iff _ _ _ _ _ _).1 hu
  · exact hρ i.val
  · have h : κ₀T n * ρ₀T n ^ i.val * (tT n * (κ₀T n * ρ₀T n ^ i.val) * (tT n)⁻¹) =
        tCT n * (ρ₀T n ^ i.val * (tT n * ρ₀T n ^ i.val * (tT n)⁻¹)) := by
      rw [show tT n * (κ₀T n * ρ₀T n ^ i.val) * (tT n)⁻¹ =
        (tT n * κ₀T n * (tT n)⁻¹) * (tT n * ρ₀T n ^ i.val * (tT n)⁻¹) by group, tT_conj_κ₀T hn,
        tCT, ← conj_pow, tT_conj_ρ₀T hn]
      have hc : ρ₀T n ^ i.val * κ₁T n = κ₁T n * ρ₀T n ^ i.val :=
        ((commute_ρ₀T_κ₁T hn).pow_left _).eq
      calc κ₀T n * ρ₀T n ^ i.val * (κ₁T n * ρ₁T n ^ i.val) =
          κ₀T n * (ρ₀T n ^ i.val * κ₁T n) * ρ₁T n ^ i.val := by group
        _ = κ₀T n * κ₁T n * (ρ₀T n ^ i.val * ρ₁T n ^ i.val) := by rw [hc]; group
    rw [h]
    exact mul_mem (mem_sup_right (mem_zpowers _)) (hρ i.val)

theorem mem_of_comm_tT {u v : TM n} (hu : u ∈ B₀T hn) (hv : v ∈ B₁T hn)
    (hc : u * v * tT n = tT n * (u * v)) : u * v ∈ zpowers (hCT hn) ⊔ zpowers (tCT n) := by
  have htu : tT n * u * (tT n)⁻¹ ∈ B₁T hn := conj_tT_mem_B₁T hn hu
  have htv : tT n * v * (tT n)⁻¹ ∈ B₀T hn := conj_tT_mem_B₀T hn hv
  have h1 : (tT n * v * (tT n)⁻¹) * (tT n * u * (tT n)⁻¹) = u * v := by
    rw [B₀T_comm_B₁T hn _ htv _ htu, conj_mul_conj_inv, ← hc, mul_inv_cancel_right]
  have h2 : u⁻¹ * (tT n * v * (tT n)⁻¹) = v * (tT n * u * (tT n)⁻¹)⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h1, mul_inv_cancel_right]
  have h3 : u⁻¹ * (tT n * v * (tT n)⁻¹) = 1 := by
    have hmem : u⁻¹ * (tT n * v * (tT n)⁻¹) ∈ B₀T hn ⊓ B₁T hn := by
      refine Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hu) htv, ?_⟩
      rw [h2]
      exact mul_mem hv (inv_mem htu)
    rw [B₀T_inf_B₁T hn, mem_bot] at hmem
    exact hmem
  have hv' : v = tT n * u * (tT n)⁻¹ := by
    have h4 : v * (tT n * u * (tT n)⁻¹)⁻¹ = 1 := h2 ▸ h3
    exact mul_inv_eq_one.1 h4
  rw [hv']
  exact mul_conj_tT_mem hn hu

theorem centralizer_eq :
    BT hn ⊓ centralizer ({tT n} : Set (TM n)) = zpowers (hCT hn) ⊔ zpowers (tCT n) := by
  apply le_antisymm
  · rintro x ⟨hx, hxt⟩
    have hxt' : x * tT n = tT n * x := mem_centralizer_singleton_iff.1 hxt
    rcases (mem_BT_iff hn).1 hx with ⟨u, hu, v, hv, rfl⟩ | ⟨u, hu, v, hv, rfl⟩
    · exact mem_of_comm_tT hn hu hv hxt'
    ·
      have hκ₀ := κ₀T_mem_B₀T hn
      have hκ₁ := κ₁T_mem_B₁T hn
      have hb₁ := b₁T_mem hn
      set u' := u * (κ₀T n)⁻¹ with hu'
      set v' := v * (b₁T hn)⁻¹ * (κ₁T n)⁻¹ with hv'
      have hu'm : u' ∈ B₀T hn := mul_mem hu (inv_mem hκ₀)
      have hv'm : v' ∈ B₁T hn := mul_mem (mul_mem hv (inv_mem hb₁)) (inv_mem hκ₁)
      have hcomm : (κ₀T n)⁻¹ * (v * (b₁T hn)⁻¹ * (κ₁T n)⁻¹) =
          v * (b₁T hn)⁻¹ * (κ₁T n)⁻¹ * (κ₀T n)⁻¹ :=
        B₀T_comm_B₁T hn _ (inv_mem hκ₀) _ (mul_mem (mul_mem hv (inv_mem hb₁)) (inv_mem hκ₁))
      have hx' : u * v * sT n = u' * v' * hCT hn := by
        rw [hu', hv', hCT]
        calc u * v * sT n = u * (v * (b₁T hn)⁻¹ * (κ₁T n)⁻¹) * (κ₀T n)⁻¹ *
              (κ₀T n * κ₁T n * b₁T hn * sT n) := by group
          _ = u * ((κ₀T n)⁻¹ * (v * (b₁T hn)⁻¹ * (κ₁T n)⁻¹)) *
              (κ₀T n * κ₁T n * b₁T hn * sT n) := by rw [hcomm]; group
          _ = u * (κ₀T n)⁻¹ * (v * (b₁T hn)⁻¹ * (κ₁T n)⁻¹) *
              (κ₀T n * κ₁T n * b₁T hn * sT n) := by group
      have hct := commute_tT_hCT hn
      have hc' : u' * v' * tT n = tT n * (u' * v') := by
        have h5 : u' * v' = u * v * sT n * (hCT hn)⁻¹ := by rw [hx', mul_inv_cancel_right]
        have h6 : (hCT hn)⁻¹ * tT n = tT n * (hCT hn)⁻¹ := (hct.inv_right).eq.symm
        calc u' * v' * tT n = u * v * sT n * ((hCT hn)⁻¹ * tT n) := by rw [h5]; group
          _ = u * v * sT n * tT n * (hCT hn)⁻¹ := by rw [h6]; group
          _ = tT n * (u * v * sT n) * (hCT hn)⁻¹ := by rw [hxt']
          _ = tT n * (u' * v') := by rw [h5]; group
      rw [hx']
      exact mul_mem (mem_of_comm_tT hn hu'm hv'm hc') (mem_sup_left (mem_zpowers _))
  · refine sup_le (zpowers_le.2 ⟨hCT_mem_BT hn, ?_⟩) (zpowers_le.2 ⟨tCT_mem_BT hn, ?_⟩)
    · exact mem_centralizer_singleton_iff.2 (commute_tT_hCT hn).eq.symm
    · exact mem_centralizer_singleton_iff.2 (commute_tT_tCT hn).eq.symm

theorem CBt_iso :
    Nonempty (↥(BT hn ⊓ centralizer ({tT n} : Set (TM n))) ≃*
      CFSG.Open.SemidihedralGroup (n + 1)) := by
  have hord : orderOf (hCT hn) = 2 ^ (n - 1 + 1) := by
    rw [orderOf_hCT hn, show n - 1 + 1 = n by omega]
  have hconj : tCT n * hCT hn * (tCT n)⁻¹ = hCT hn ^ (2 ^ (n - 1) - 1) := tCT_conj_hCT' hn
  have ht2 : tCT n ^ 2 = 1 := by rw [pow_two, tCT_mul_tCT hn]
  obtain ⟨-, e, -, -⟩ := CFSG.BrauerLinearThree.semidihedral_sup_zpowers (m := n - 1)
    (by omega) hord ht2 hconj
  rw [show n - 1 + 2 = n + 1 by omega] at e
  exact ⟨(MulEquiv.subgroupCongr (centralizer_eq hn)).trans e.symm⟩

end CFSG.CGT.Foote81L6.Bridge
