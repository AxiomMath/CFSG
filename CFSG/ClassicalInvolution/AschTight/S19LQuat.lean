module

public import CFSG.ClassicalInvolution.AschTight.S19LTr
public import CFSG.ClassicalInvolution.AschTight.S19QTSign

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19L

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77
open scoped Pointwise

variable {G : Type} [Group G]

theorem mul_pow_mul_inv_mem {N : Subgroup G} {o d : G} (ho : o ∈ N)
    (hd : d ∈ Subgroup.normalizer (N : Set G)) (n : ℕ) : (o * d) ^ n * (d ^ n)⁻¹ ∈ N := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hdn : d ^ n ∈ Subgroup.normalizer (N : Set G) := Subgroup.pow_mem _ hd n
    have h1 : d ^ n * o * (d ^ n)⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp hdn o).mp ho
    have e : (o * d) ^ (n + 1) * (d ^ (n + 1))⁻¹ =
        ((o * d) ^ n * (d ^ n)⁻¹) * (d ^ n * o * (d ^ n)⁻¹) := by
      rw [pow_succ, pow_succ]
      group
    rw [e]
    exact N.mul_mem ih h1

omit [Group G] in
theorem pow_four_eq {M : Type} [Monoid M] (d : M) : d ^ 4 = d * d * d * d := by
  simp [pow_succ]

variable [Finite G] {p f : ℕ} [Fact p.Prime] [IsSimpleGroup G]
  {K : Subgroup G} {z : G} {S : Sylow 2 G} {W L : Subgroup G} {t : G} {V : Subgroup G}

theorem sign_mem_or_of_nilpotent (hd : Sec19DataT p f K z S W L t V)
    (hY : sec19Y K z = oddCoreOf (sec19Y K z) ⊔ ((S : Subgroup G) ⊓ sec19Y K z)) {q : G}
    (hqinv : ∀ c ∈ W ⊓ sec19Y K z, q * c * q⁻¹ = c⁻¹) (hq2 : q * q = z)
    (hcoset : ∀ x ∈ (S : Subgroup G) ⊓ sec19Y K z, x ∉ W ⊓ sec19Y K z → q⁻¹ * x ∈ W ⊓ sec19Y K z)
    {ξ : G} (hξ : ξ ∈ W ⊓ sec19Y K z) (hξ4 : ξ ^ 4 = z) :
    ∀ x ∈ Subgroup.centralizer ({z} : Set G),
      x ∈ Subgroup.normalizer (oddCoreOf (sec19Y K z) : Set G) ∧
        ((ξ * ξ)⁻¹ * (x * (ξ * ξ) * x⁻¹) ∈ oddCoreOf (sec19Y K z) ∨
          (ξ * ξ) * (x * (ξ * ξ) * x⁻¹) ∈ oddCoreOf (sec19Y K z)) := by
  have hd0 := hd.toSec19Data
  have hNY := S1916.sd_centralizer_le_normalizer_Y hd0
  have hzZ := S1916.isUniqueInvolution_W_inf hd
  have hcomm := S1911.comm_of_mem hd0
  set O := oddCoreOf (sec19Y K z) with hO
  have hOY : O ≤ sec19Y K z := Subgroup.map_subtype_le _
  have hYN : ∀ y ∈ sec19Y K z, y ∈ Subgroup.normalizer (O : Set G) := fun y hy =>
    AschTight.mem_normalizer_oddCoreOf_of_mem_normalizer (Subgroup.le_normalizer hy)
  have hP2 : IsPGroup 2 ↥((S : Subgroup G) ⊓ sec19Y K z) := S.isPGroup'.to_le inf_le_left
  have hbot := S1916.inf_oddCoreOf_eq_bot hP2 (sec19Y K z)
  intro x hx
  refine ⟨AschTight.mem_normalizer_oddCoreOf_of_mem_normalizer (hNY hx), ?_⟩
  have hxz : x * z = z * x := Subgroup.mem_centralizer_singleton_iff.mp hx
  have hyY : x * ξ * x⁻¹ ∈ sec19Y K z := (Subgroup.mem_normalizer_iff.mp (hNY hx) ξ).mp hξ.2
  have hset := Subgroup.coe_mul_of_right_le_normalizer_left O ((S : Subgroup G) ⊓ sec19Y K z)
    (fun y hy => hYN y hy.2)
  have hyOP : x * ξ * x⁻¹ ∈ ((O : Set G) * (((S : Subgroup G) ⊓ sec19Y K z : Subgroup G) :
      Set G)) := by
    rw [← hset, ← hY]
    exact hyY
  obtain ⟨o, ho, d, hdP, hod⟩ := Set.mem_mul.mp hyOP
  have hdN := hYN d hdP.2
  have h4 : (o * d) ^ 4 = z := by
    rw [hod, ← MulAut.conj_apply, ← map_pow, hξ4, MulAut.conj_apply, hxz, mul_inv_cancel_right]
  have hd4 : d ^ 4 = z := by
    have h1 := mul_pow_mul_inv_mem ho hdN 4
    rw [h4] at h1
    have h2 : d ^ 4 * z⁻¹ ∈ (S : Subgroup G) ⊓ sec19Y K z ⊓ O := by
      refine ⟨Subgroup.mul_mem _ (Subgroup.pow_mem _ hdP 4) (Subgroup.inv_mem _ ⟨hd0.hWS hzZ.mem.1,
        hzZ.mem.2⟩), ?_⟩
      have e : d ^ 4 * z⁻¹ = (z * (d ^ 4)⁻¹)⁻¹ := by group
      rw [e]
      exact O.inv_mem h1
    rw [hbot, Subgroup.mem_bot] at h2
    calc d ^ 4 = d ^ 4 * z⁻¹ * z := by group
      _ = z := by rw [h2, one_mul]
  have hdC : d ∈ W ⊓ sec19Y K z := by
    by_contra hdC
    have hc := hcoset d hdP hdC
    have hzc := hcomm _ hc.1 z hzZ.mem.1
    have hsq : d * d = z := by
      have e : d = q * (q⁻¹ * d) := by group
      rw [e]
      calc q * (q⁻¹ * d) * (q * (q⁻¹ * d)) =
          (q * (q⁻¹ * d) * q⁻¹) * (q * q) * (q⁻¹ * d) := by group
        _ = (q⁻¹ * d)⁻¹ * z * (q⁻¹ * d) := by rw [hqinv _ hc, hq2]
        _ = z := by rw [mul_assoc, ← hzc]; group
    have : d ^ 4 = 1 := by
      rw [pow_four_eq, mul_assoc (d * d), hsq, hzZ.sq]
    rw [hd4] at this
    exact hzZ.ne_one this
  have hζ : ξ * ξ ∈ W ⊓ sec19Y K z := Subgroup.mul_mem _ hξ hξ
  have hζ2 : ξ * ξ * (ξ * ξ) = z := by rw [← hξ4, pow_four_eq]; group
  have hd2 : d * d * (d * d) = z := by rw [← hd4, pow_four_eq]; group
  have h2 := mul_pow_mul_inv_mem ho hdN 2
  have hxζ : x * (ξ * ξ) * x⁻¹ = (o * d) ^ 2 := by
    rw [hod, sq]
    group
  rcases S1916.eq_or_eq_inv_of_mul_self_eq hzZ (fun a ha b hb => hcomm a ha.1 b hb.1)
    (Subgroup.mul_mem _ hdC hdC) hζ hd2 hζ2 with h | h
  · left
    have e : (ξ * ξ)⁻¹ * (x * (ξ * ξ) * x⁻¹) =
        (ξ * ξ)⁻¹ * ((o * d) ^ 2 * (d ^ 2)⁻¹) * (ξ * ξ)⁻¹⁻¹ := by
      rw [hxζ, sq d, h]
      group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hYN _ hζ.2)) _).mp h2
  · right
    have e : (ξ * ξ) * (x * (ξ * ξ) * x⁻¹) =
        (ξ * ξ) * ((o * d) ^ 2 * (d ^ 2)⁻¹) * (ξ * ξ)⁻¹ := by
      rw [hxζ, sq d, h]
      group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hYN _ hζ.2) _).mp h2

theorem exists_pow_four_eq (hd : Sec19DataT p f K z S W L t V)
    (h8 : 8 ≤ Nat.card ↥(W ⊓ sec19Y K z)) : ∃ ξ ∈ W ⊓ sec19Y K z, ξ ^ 4 = z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ef := S1911.etaYForm p f G K z S W L t V hd
  have hzZ := S1916.isUniqueInvolution_W_inf hd
  have hC2 : IsPGroup 2 ↥(W ⊓ sec19Y K z) := S.isPGroup'.to_le (inf_le_left.trans hd.hWS)
  obtain ⟨g₀, hg₀⟩ := ef.cyclic.exists_generator
  have hgo : orderOf (g₀ : G) = Nat.card ↥(W ⊓ sec19Y K z) := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg₀]
  obtain ⟨k, hk⟩ := hC2.exists_card_eq
  have hk3 : 3 ≤ k := by
    by_contra h
    have : 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h8d : 8 ∣ orderOf (g₀ : G) := by
    rw [hgo, hk]
    exact (Nat.pow_dvd_pow 2 hk3 : 2 ^ 3 ∣ 2 ^ k)
  obtain ⟨m, hm⟩ := h8d
  have hge : 2 ≤ orderOf (g₀ : G) := by omega
  have hev : Even (orderOf (g₀ : G)) := ⟨4 * m, by omega⟩
  have hinv := Hall196.pow_half_mul_self hev
  have hne := Hall196.pow_half_ne_one hge
  have hzc : (g₀ : G) ^ (orderOf (g₀ : G) / 2) = z := by
    have hmem : (g₀ : G) ^ (orderOf (g₀ : G) / 2) ∈ W ⊓ sec19Y K z :=
      Subgroup.pow_mem _ g₀.2 _
    exact (hzZ.unique _ hmem hinv).resolve_left hne
  refine ⟨(g₀ : G) ^ m, Subgroup.pow_mem _ g₀.2 _, ?_⟩
  rw [← pow_mul, show m * 4 = orderOf (g₀ : G) / 2 by omega]
  exact hzc

theorem false_of_quat (h11b : C19_11bTmp p f) (hd : Sec19DataT p f K z S W L t V)
    (hY : sec19Y K z = oddCoreOf (sec19Y K z) ⊔ ((S : Subgroup G) ⊓ sec19Y K z)) {q : G}
    (hqP : q ∈ (S : Subgroup G) ⊓ sec19Y K z) (hqt : q * t * q⁻¹ = z * t)
    (hqinv : ∀ c ∈ W ⊓ sec19Y K z, q * c * q⁻¹ = c⁻¹) (hq2 : q * q = z)
    (hcoset : ∀ x ∈ (S : Subgroup G) ⊓ sec19Y K z, x ∉ W ⊓ sec19Y K z → q⁻¹ * x ∈ W ⊓ sec19Y K z)
    (h8 : 8 ≤ Nat.card ↥(W ⊓ sec19Y K z)) : False := by
  have hd0 := hd.toSec19Data
  have hSC := hd0.hSz
  have hzZ := S1916.isUniqueInvolution_W_inf hd
  have hcomm := S1911.comm_of_mem hd0
  obtain ⟨ξ, hξ, hξ4⟩ := exists_pow_four_eq hd h8
  have hP := sign_mem_or_of_nilpotent hd hY hqinv hq2 hcoset hξ hξ4
  have hζ : ξ * ξ ∈ W ⊓ sec19Y K z := Subgroup.mul_mem _ hξ hξ
  have hζO : ξ * ξ * (ξ * ξ) ∉ oddCoreOf (sec19Y K z) := by
    have e : ξ * ξ * (ξ * ξ) = z := by rw [← hξ4, pow_four_eq]; group
    rw [e]
    intro hz
    have hmem : z ∈ W ⊓ sec19Y K z ⊓ oddCoreOf (sec19Y K z) := ⟨hzZ.mem, hz⟩
    rw [S1916.inf_oddCoreOf_eq_bot (S.isPGroup'.to_le (inf_le_left.trans hd.hWS)) _,
      Subgroup.mem_bot] at hmem
    exact hzZ.ne_one hmem
  have hqR : ∀ r ∈ (S : Subgroup G) ⊓ K, q * r = r * q := fun r hr =>
    (S1916.sd_commute_R_Q hd0 r hr q hqP).symm
  have htz : z * t = t * z := hcomm z hzZ.mem.1 t (S1911.mem_W hd)
  obtain ⟨u, huS, hu2, huinv, huU⟩ :=
    S19Q.exists_involution_of_conj_eq_mul h11b hd hqP.1 hqR (by rw [hqt, htz])
  have huH := S19Q.not_mem_signSub_of_inv hζO (huinv _ hζ)
  have hS : ∀ d ∈ Subgroup.centralizer ({z} : Set G),
      d⁻¹ * u * d ∉ S19Q.signSub (oddCoreOf (sec19Y K z)) (ξ * ξ) := fun d hdz => by
    have := S19Q.conj_not_mem_signSub hP (Subgroup.inv_mem _ hdz) (hSC huS) huH
    rwa [inv_inv] at this
  refine false_of_transfer h11b hd (H := S19Q.signSub (oddCoreOf (sec19Y K z)) (ξ * ξ))
    (fun s hs x hx => S19Q.conj_mem_signSub hP (hSC hs) (hSC hx.1) hx.2)
    (fun a ha b hb haH hbH => S19Q.inv_mul_mem_signSub hP (hSC ha) (hSC hb) haH hbH) huS huH hu2
    huU (fun d hdz _ => hS d hdz) (fun d hdz hdW => hS d hdz ?_)
  have hdC : d⁻¹ * u * d ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hdz) (hSC huS)) hdz
  exact S19Q.mem_signSub_of_comm (hP _ hdC).1 (hcomm _ hdW _ hζ.1)

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19L
