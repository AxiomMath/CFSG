module

public import CFSG.GH74.GLS.Bg.Pu5.L295Basic
public import CFSG.GH74.GLS.Bg.Pu5.II4Pack43a
public import CFSG.GH74.GLS.Bg.Pu5.Assembly
public import CFSG.GH74.GLS.Stage1.Thm2.Recip.BalanceSolv

public section

namespace CFSG.GH74.GLS.Bg.Pu5

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Bg.Iii2 CFSG.GH74.GLS.IVK.Lifted
open scoped commutatorElement

namespace L295C

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem phi_mem_innOf {L : Subgroup G} {u : G} (hu : u ∈ normalizer (L : Set G))
    (h : InducesInner u L) : phi L u hu ∈ innOf (Hat L) := by
  obtain ⟨k, hkL, hc⟩ := h
  have hcN : u * k⁻¹ ∈ normalizer (L : Set G) := hc.1
  have hkN : k ∈ normalizer (L : Set G) := le_normalizer hkL
  have h1 : phi L u hu = phi L (u * k⁻¹ * k) (mul_mem hcN hkN) :=
    phi_congr L (by group) hu _
  rw [h1, phi_mul L hcN hkN, (phi_eq_one_iff L hcN).2 hc, phi_of_mem L hkL, one_mul]
  exact ⟨hatMk L ⟨k, hkL⟩, rfl⟩

omit [Finite G] in
theorem phi_comm_of_comm {L : Subgroup G} {x y : G} (hx : x ∈ normalizer (L : Set G))
    (hy : y ∈ normalizer (L : Set G)) (hxy : x * y = y * x) :
    phi L x hx * phi L y hy = phi L y hy * phi L x hx := by
  rw [← phi_mul L hx hy, ← phi_mul L hy hx]
  exact phi_congr L hxy _ _

theorem hatOK_of_rigid (h44 : II4_44) (hG : IsKProperSimple G) {t : G} {L : Subgroup G}
    (hL : IsRigidRankOneComp t L) : HatOK (Hat L) := by
  have ht : orderOf t = 2 := rr_ord hL
  have hLc := rr_pcomp hL
  exact ⟨TwoThin.isQuasisimple_hat hLc, isKGroupNative_hat hG ht hLc.1,
    (pRank_hat L).trans hL.2, h44 G hG t ht L hLc hL.2⟩

end L295C

theorem l295c_of (hP0 : P0S) (hTP : L292TP) (h293 : L293) (h2A7 : II4_2A7) (h44 : II4_44) :
    L295cS := by
  intro G _ _ z t S K U hcfg hN hnf L hL u hu huz hind
  have hG : IsKProperSimple G := hcfg.cfg.simple
  have hz2 : orderOf z = 2 := hcfg.cfg.hz
  have hzz : z * z = 1 := mul_self_eq_one_of_orderOf_eq_two hz2
  have hzU : z ∈ U := hcfg.hzU
  have hu1 : u ≠ 1 := by
    intro h
    apply huz
    rw [h]
    exact one_mem _
  have hu2 : orderOf u = 2 := hcfg.hU.orderOf_eq_two hu hu1
  have huu : u * u = 1 := mul_self_eq_one_of_orderOf_eq_two hu2
  have hzu : z * u = u * z := hcfg.hU.mul_comm' hzU hu
  have hzuU : z * u ∈ U := mul_mem hzU hu
  have hzu1 : z * u ≠ 1 := by
    intro h
    apply huz
    have : u = z⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [this]
    exact inv_mem (mem_zpowers z)
  have hzu2 : orderOf (z * u) = 2 := hcfg.hU.orderOf_eq_two hzuU hzu1
  have hbad : ∀ a ∈ U, orderOf a = 2 → a ∈ cSec L → False := fun a ha ha2 haL =>
    h293 G z t S hcfg.cfg a ha2 (hcfg.mem_cent_z ha) (hcfg.mem_cent_t ha) K hcfg.hK
      (hcfg.mem_cSec ha) L hL haL
  have hLn := hN L hL
  have hzN : z ∈ normalizer (L : Set G) := hLn hzU
  have huN : u ∈ normalizer (L : Set G) := hLn hu
  have hzuN : z * u ∈ normalizer (L : Set G) := hLn hzuU
  have hO : HatOK (Hat L) := L295C.hatOK_of_rigid h44 hG hL
  have hφz2 : phi L z hzN * phi L z hzN = 1 := phi_mul_self L hzN hzz
  have hφu2 : phi L u huN * phi L u huN = 1 := phi_mul_self L huN huu
  have hcomm : phi L z hzN * phi L u huN = phi L u huN * phi L z hzN :=
    L295C.phi_comm_of_comm hzN huN hzu
  have hφz1 : phi L z hzN ≠ 1 := fun h => hbad z hzU hz2 ((phi_eq_one_iff L hzN).1 h)
  have hφu1 : phi L u huN ≠ 1 := fun h => hbad u hu hu2 ((phi_eq_one_iff L huN).1 h)
  have hne : phi L z hzN ≠ phi L u huN := by
    intro h
    have h1 : phi L (z * u) hzuN = 1 := by
      rw [phi_mul L hzN huN, ← h]
      exact hφz2
    exact hbad (z * u) hzuU hzu2 ((phi_eq_one_iff L hzuN).1 h1)
  have hφzf : ¬ IsFAutomorphism (Hat L) (phi L z hzN) := fun h => hnf L hL z hzU hz2 ⟨hzN, h⟩
  have hφuf : ¬ IsFAutomorphism (Hat L) (phi L u huN) := fun h => hnf L hL u hu hu2 ⟨huN, h⟩
  have hφuin : phi L u huN ∈ innOf (Hat L) := L295C.phi_mem_innOf huN hind
  obtain ⟨w, hw4, hwu, hwz⟩ :=
    ii4_43f h2A7 hO (phi L z hzN) (phi L u huN) hφz2 hφu2 hcomm hφz1 hφu1 hne hφzf hφuf hφuin
  obtain ⟨v, hvL, hvu, hvw⟩ :=
    Stage1.Thm2.Recip.BalanceSolv.exists_centralizer_lift_of_phi_fixed L hu2 huN hwu
  obtain ⟨c, hc⟩ : ∃ c : G, c = v * z * v⁻¹ * z⁻¹ := ⟨_, rfl⟩
  have hzvL : z * v⁻¹ * z⁻¹ ∈ L := (mem_normalizer_iff.mp hzN v⁻¹).mp (inv_mem hvL)
  have hcL : c ∈ L := by
    have : c = v * (z * v⁻¹ * z⁻¹) := by rw [hc]; group
    rw [this]
    exact mul_mem hvL hzvL
  have hπc : hatMk L ⟨c, hcL⟩ = w * w := by
    have e : (⟨c, hcL⟩ : ↥L) = ⟨v, hvL⟩ * ⟨z * v⁻¹ * z⁻¹, hzvL⟩ := by
      apply Subtype.ext
      show c = v * (z * v⁻¹ * z⁻¹)
      rw [hc]
      group
    have h2 : hatMk L ⟨z * v⁻¹ * z⁻¹, hzvL⟩ = phi L z hzN (hatMk L ⟨v⁻¹, inv_mem hvL⟩) :=
      (phi_mk L hzN ⟨v⁻¹, inv_mem hvL⟩).symm
    have h3 : hatMk L ⟨v⁻¹, inv_mem hvL⟩ = w⁻¹ := by
      have : (⟨v⁻¹, inv_mem hvL⟩ : ↥L) = (⟨v, hvL⟩ : ↥L)⁻¹ := rfl
      rw [this, map_inv, hvw]
    rw [e, map_mul, hvw, h2, h3, map_inv, hwz, inv_inv]
  have hw2 : orderOf (w * w) = 2 := by
    have h1 : w * w = w ^ 2 := (pow_two w).symm
    have h2 : orderOf (w ^ 2) = orderOf w / 2 :=
      orderOf_pow_of_dvd (by norm_num) (by rw [hw4]; norm_num)
    rw [h1, h2, hw4]
  have hcdvd : 2 ∣ orderOf c := by
    have h1 : orderOf (hatMk L ⟨c, hcL⟩) ∣ orderOf (⟨c, hcL⟩ : ↥L) := orderOf_map_dvd _ _
    rw [hπc, hw2, Subgroup.orderOf_mk] at h1
    exact h1
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = orderOf c / 2 := ⟨_, rfl⟩
  have ht'2 : orderOf (c ^ n) = 2 := by
    rw [hn]
    exact orderOf_pow_orderOf_div (orderOf_pos c).ne' hcdvd
  have ht'sq : c ^ n * c ^ n = 1 := by
    have := pow_orderOf_eq_one (c ^ n)
    rw [ht'2, pow_two] at this
    exact this
  have ht'L : c ^ n ∈ L := pow_mem hcL n
  have hcu : u * c = c * u := by
    have huv : Commute u v := hvu
    have huz' : Commute u z := hzu.symm
    have := ((huv.mul_right huz').mul_right huv.inv_right).mul_right huz'.inv_right
    rw [hc]
    exact this.eq
  have hzc : z * c * z⁻¹ = c⁻¹ := by
    have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
    have hzi2 : z⁻¹ * z⁻¹ = 1 := by rw [hzinv, hzz]
    have e : c⁻¹ = z * v * z⁻¹ * v⁻¹ := by rw [hc]; group
    calc z * c * z⁻¹ = z * v * z * v⁻¹ * (z⁻¹ * z⁻¹) := by rw [hc, hzinv]; group
      _ = z * v * z * v⁻¹ := by rw [hzi2, mul_one]
      _ = c⁻¹ := by rw [e, hzinv]
  have ht'zc : z * c ^ n * z⁻¹ = c ^ n := by
    calc z * c ^ n * z⁻¹ = (z * c * z⁻¹) ^ n := conj_pow.symm
      _ = (c⁻¹) ^ n := by rw [hzc]
      _ = (c ^ n)⁻¹ := inv_pow c n
      _ = c ^ n := inv_eq_of_mul_eq_one_right ht'sq
  have ht'Cz : c ^ n ∈ centralizer ({z} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    exact (mul_inv_eq_iff_eq_mul.mp ht'zc).symm
  have ht'Cu : c ^ n ∈ centralizer ({u} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    exact ((Commute.pow_left (show Commute c u from hcu.symm) n).eq)
  have ht'Ct : c ^ n ∈ centralizer ({t} : Set G) := (rr_pcomp hL).1 ht'L
  have hZ : z ∈ zStar (rigidProduct u) := hP0 G z t S K U hcfg u hu hu2
  have hvN : v ∈ normalizer ((zStar (rigidProduct u) : Subgroup G) : Set G) :=
    normalizes_zStar_rigidProduct (z := u) (c := v) (mem_centralizer_singleton_iff.2 hvu.symm)
  have hcZ : c ∈ zStar (rigidProduct u) := by
    have h1 : v * z * v⁻¹ ∈ zStar (rigidProduct u) := (mem_normalizer_iff.mp hvN z).mp hZ
    rw [hc]
    exact mul_mem h1 (inv_mem hZ)
  have ht'Z : c ^ n ∈ zStar (rigidProduct u) := pow_mem hcZ n
  have ht'cK : c ^ n ∈ cSec K :=
    hTP G hG hcfg.cfg.rank z u K hcfg.hK hu2 (hcfg.mem_cent_z hu) (hcfg.mem_cSec hu) (c ^ n) ht'2
      ht'Cz ht'Cu ht'Z
  have ht'cL : c ^ n ∈ cSec L := rr_inv_mem_cSec h44 hG hL ht'L ht'2
  exact h293 G z t S hcfg.cfg (c ^ n) ht'2 ht'Cz ht'Ct K hcfg.hK ht'cK L hL ht'cL

end CFSG.GH74.GLS.Bg.Pu5
