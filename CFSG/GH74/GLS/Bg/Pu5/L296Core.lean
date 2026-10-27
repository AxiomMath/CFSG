module

public import CFSG.GH74.GLS.Bg.Pu5.L296Basic
public import CFSG.GH74.GLS.Bg.Pu5.L295C

public section

namespace CFSG.GH74.GLS.Bg.Pu5

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.ABGLocalTools CFSG.GH74.GLS.Bg.Iii2 CFSG.GH74.GLS.Stage1.Thm3.Sec4
  CFSG.GH74.GLS.Stage1.Thm3.Sec6 CFSG.GH74.GLS.IVK.Lifted
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]


theorem claimM_core (h295 : L295) (h293 : L293) (h2A7 : II4_2A7) (h44 : II4_44)
    {z t : G} {S K U : Subgroup G} (h : Cfg295 G z t S K U) {L : Subgroup G}
    (hL : IsRigidRankOneComp t L) :
    ∃ u v t' : G, u ∈ U ∧ u ∉ zpowers z ∧ orderOf u = 2 ∧ v ∈ L ∧ z * v = v * z ∧
      IsPGroup 2 ↥(zpowers v) ∧ 4 ∣ orderOf v ∧ orderOf t' = 2 ∧ t' ∈ L ∧ z * t' = t' * z ∧
      ∃ n : ℕ, t' = (v * u * v⁻¹ * u⁻¹) ^ n := by
  have hG : IsKProperSimple G := h.cfg.simple
  have hz2 : orderOf z = 2 := h.cfg.hz
  have hzz : z * z = 1 := mul_self_eq_one_of_orderOf_eq_two hz2
  have hzU : z ∈ U := h.hzU
  obtain ⟨ha, hb, hc⟩ := h295 G z t S h.cfg K h.hK U h.hU h.hUle h.hzU h.hzi
  have hLn : U ≤ normalizer (L : Set G) := ha L hL
  obtain ⟨u, huU, huz⟩ : ∃ u ∈ U, u ∉ zpowers z := by
    by_contra hcon
    push Not at hcon
    have hle : U ≤ zpowers z := hcon
    have h1 := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, hz2, h.hU.2] at h1
    omega
  have hu1 : u ≠ 1 := fun h1 => huz (by rw [h1]; exact one_mem _)
  have hu2 : orderOf u = 2 := h.hU.orderOf_eq_two huU hu1
  have hzu : z * u = u * z := h.hU.mul_comm' hzU huU
  have hzuU : u * z ∈ U := mul_mem huU hzU
  have huz' : u * z ∉ zpowers z := fun hm => huz (by
    have := mul_mem hm (inv_mem (mem_zpowers z))
    simpa using this)
  have huz1 : u * z ≠ 1 := fun h1 => huz' (by rw [h1]; exact one_mem _)
  have huz2 : orderOf (u * z) = 2 := h.hU.orderOf_eq_two hzuU huz1
  have hbad : ∀ a ∈ U, orderOf a = 2 → a ∈ cSec L → False := fun a ha ha2 haL =>
    h293 G z t S h.cfg a ha2 (h.mem_cent_z ha) (h.mem_cent_t ha) K h.hK (h.mem_cSec ha) L hL haL
  have hzN : z ∈ normalizer (L : Set G) := hLn hzU
  have huN : u ∈ normalizer (L : Set G) := hLn huU
  have hO : HatOK (Hat L) := L295C.hatOK_of_rigid h44 hG hL
  have hphi : ∀ y (hy : y ∈ U), orderOf y = 2 →
      phi L y (hLn hy) * phi L y (hLn hy) = 1 ∧ phi L y (hLn hy) ≠ 1 ∧
        ¬ IsFAutomorphism (Hat L) (phi L y (hLn hy)) := by
    intro y hy hy2
    exact ⟨phi_mul_self L (hLn hy) (mul_self_eq_one_of_orderOf_eq_two hy2),
      fun h1 => hbad y hy hy2 ((phi_eq_one_iff L (hLn hy)).1 h1),
      fun hf => hb L hL y hy hy2 ⟨hLn hy, hf⟩⟩
  obtain ⟨hφz2, hφz1, hφzf⟩ := hphi z hzU hz2
  obtain ⟨hφu2, hφu1, hφuf⟩ := hphi u huU hu2
  obtain ⟨-, hφuz1, hφuzf⟩ := hphi (u * z) hzuU huz2
  have hcomm : phi L u huN * phi L z hzN = phi L z hzN * phi L u huN :=
    L295C.phi_comm_of_comm huN hzN hzu.symm
  have hphimul : phi L (u * z) (mul_mem huN hzN) = phi L u huN * phi L z hzN := phi_mul L huN hzN
  have hne : phi L u huN ≠ phi L z hzN := by
    intro heq
    apply hφuz1
    rw [hphimul, heq]
    exact hφz2
  have hφuzf' : ¬ IsFAutomorphism (Hat L) (phi L u huN * phi L z hzN) := by
    rw [← hphimul]
    exact hφuzf
  have hzin : phi L z hzN ∈ innOf (Hat L) := by
    rcases ii4_inner_involution h2A7 hO (phi L u huN) (phi L z hzN) hφu2 hφz2 hcomm hφu1 hφz1
      hne hφuf hφzf hφuzf' with hin | hin | hin
    · exact absurd ((phi_mem_inn_iff L huN).1 hin) (hc L hL u huU huz)
    · exact hin
    · rw [← hphimul] at hin
      exact absurd ((phi_mem_inn_iff L (mul_mem huN hzN)).1 hin) (hc L hL (u * z) hzuU huz')
  obtain ⟨w, hw4, hwz, hwu⟩ :=
    ii4_43f h2A7 hO (phi L u huN) (phi L z hzN) hφu2 hφz2 hcomm hφu1 hφz1 hne hφuf hφzf hzin
  obtain ⟨v₀, hv₀L, hv₀z, hv₀w⟩ :=
    Stage1.Thm2.Recip.BalanceSolv.exists_centralizer_lift_of_phi_fixed L hz2 hzN hwz
  obtain ⟨m, hm, hmP⟩ := exists_odd_pow_isPGroup v₀
  have hvL : v₀ ^ m ∈ L := pow_mem hv₀L m
  have hvz : z * v₀ ^ m = v₀ ^ m * z := ((show Commute z v₀ from hv₀z).pow_right m).eq
  have hvw : hatMk L ⟨v₀ ^ m, hvL⟩ = w ^ m := by
    have : (⟨v₀ ^ m, hvL⟩ : ↥L) = (⟨v₀, hv₀L⟩ : ↥L) ^ m := rfl
    rw [this, map_pow, hv₀w]
  have hw'4 : orderOf (w ^ m) = 4 := by
    rw [Nat.Coprime.orderOf_pow, hw4]
    rw [hw4]
    exact Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hm)
  have hwz' : phi L z hzN (w ^ m) = w ^ m := by rw [map_pow, hwz]
  have hwu' : phi L u huN (w ^ m) = (w ^ m)⁻¹ := by rw [map_pow, hwu, inv_pow]
  set v : G := v₀ ^ m with hvdef
  set w' : Hat L := w ^ m with hw'def
  have huvL : u * v⁻¹ * u⁻¹ ∈ L := (mem_normalizer_iff.mp huN v⁻¹).mp (inv_mem hvL)
  have hcL : v * u * v⁻¹ * u⁻¹ ∈ L := by
    have : v * u * v⁻¹ * u⁻¹ = v * (u * v⁻¹ * u⁻¹) := by group
    rw [this]
    exact mul_mem hvL huvL
  have hπc : hatMk L ⟨v * u * v⁻¹ * u⁻¹, hcL⟩ = w' * w' := by
    have e : (⟨v * u * v⁻¹ * u⁻¹, hcL⟩ : ↥L) = ⟨v, hvL⟩ * ⟨u * v⁻¹ * u⁻¹, huvL⟩ := by
      apply Subtype.ext
      show v * u * v⁻¹ * u⁻¹ = v * (u * v⁻¹ * u⁻¹)
      group
    have h2 : hatMk L ⟨u * v⁻¹ * u⁻¹, huvL⟩ = phi L u huN (hatMk L ⟨v⁻¹, inv_mem hvL⟩) :=
      (phi_mk L huN ⟨v⁻¹, inv_mem hvL⟩).symm
    have h3 : hatMk L ⟨v⁻¹, inv_mem hvL⟩ = w'⁻¹ := by
      have : (⟨v⁻¹, inv_mem hvL⟩ : ↥L) = (⟨v, hvL⟩ : ↥L)⁻¹ := rfl
      rw [this, map_inv, hvw]
    rw [e, map_mul, hvw, h2, h3, map_inv, hwu', inv_inv]
  have hw2 : orderOf (w' * w') = 2 := by
    have h1 : w' * w' = w' ^ 2 := (pow_two w').symm
    have h2 : orderOf (w' ^ 2) = orderOf w' / 2 :=
      orderOf_pow_of_dvd (by norm_num) (by rw [hw'4]; norm_num)
    rw [h1, h2, hw'4]
  have hcdvd : 2 ∣ orderOf (v * u * v⁻¹ * u⁻¹) := by
    have h1 : orderOf (hatMk L ⟨v * u * v⁻¹ * u⁻¹, hcL⟩) ∣ orderOf (⟨v * u * v⁻¹ * u⁻¹, hcL⟩ : ↥L) :=
      orderOf_map_dvd _ _
    rw [hπc, hw2, Subgroup.orderOf_mk] at h1
    exact h1
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = orderOf (v * u * v⁻¹ * u⁻¹) / 2 := ⟨_, rfl⟩
  have ht'2 : orderOf ((v * u * v⁻¹ * u⁻¹) ^ n) = 2 := by
    rw [hn]
    exact orderOf_pow_orderOf_div (orderOf_pos _).ne' hcdvd
  have hcz : Commute z (v * u * v⁻¹ * u⁻¹) := by
    have hzv : Commute z v := hvz
    have hzu' : Commute z u := hzu
    exact ((hzv.mul_right hzu').mul_right hzv.inv_right).mul_right hzu'.inv_right
  have h4v : 4 ∣ orderOf v := by
    have h1 : orderOf (hatMk L ⟨v, hvL⟩) ∣ orderOf (⟨v, hvL⟩ : ↥L) := orderOf_map_dvd _ _
    rw [hvw, hw'4, Subgroup.orderOf_mk] at h1
    exact h1
  exact ⟨u, v, (v * u * v⁻¹ * u⁻¹) ^ n, huU, huz, hu2, hvL, hvz, hmP, h4v, ht'2,
    pow_mem hcL n, (hcz.pow_right n).eq, n, rfl⟩

end CFSG.GH74.GLS.Bg.Pu5
