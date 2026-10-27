module

public import CFSG.Certificates.Kernel.FiveStdKOrbSound

public section

namespace CFSG.KC.FiveStdK

open CFSG.GH74.GLS.LU.Local.FiveStd CFSG.GH74.GLS.LU.Local.Five

open scoped Pointwise

variable {Gp : Type} [Group Gp]

theorem conj_into_sub {ι : E → Gp} (hM : Model ι) (hK : Nat.card (vSub hM) = 28800) {p k : Nat}
    [hp : Fact p.Prime] {P : Subgroup Gp} (hPK : P ≤ vSub hM) (hPc : Nat.card P = p ^ k)
    (hidx : ¬ p ∣ 28800 / p ^ k) {g : E} (hg : validE g = true) {n : Nat}
    (hgo : orderOf (ι g) = p ^ n) : ∃ c, validE c = true ∧ ι (conjE c g) ∈ P := by
  set K := vSub hM with hKd
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have hcardP1 : Nat.card ↥(P.subgroupOf K) = p ^ k := by
    rw [Nat.card_congr (P.subgroupOfEquivOfLe hPK).toEquiv, hPc]
  have hP1p : IsPGroup p ↥(P.subgroupOf K) := IsPGroup.of_card hcardP1
  have hP1idx : ¬ p ∣ (P.subgroupOf K).index := by
    have hci := Subgroup.card_mul_index (P.subgroupOf K)
    rw [hcardP1, hK] at hci
    have hidx' : (P.subgroupOf K).index = 28800 / p ^ k := by
      rw [← hci, Nat.mul_div_cancel_left _ (pow_pos hp.out.pos k)]
    rw [hidx']
    exact hidx
  let PA : Sylow p K := hP1p.toSylow hP1idx
  let g' : K := ⟨ι g, g, hg, rfl⟩
  have hQ : IsPGroup p (Subgroup.zpowers g') := by
    apply IsPGroup.of_card (n := n)
    rw [Nat.card_zpowers, ← Subgroup.orderOf_coe]
    exact hgo
  obtain ⟨PQ, hQle⟩ := hQ.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq K PA PQ
  have hc' : (MulAut.conj c • (P.subgroupOf K) : Subgroup K) = (PQ : Subgroup K) := by
    have := congrArg (fun Q : Sylow p K => (Q : Subgroup K)) hc
    simpa [PA, Sylow.coe_subgroup_smul] using this
  have hmem : g' ∈ MulAut.conj c • (P.subgroupOf K) := by
    rw [hc']
    exact hQle (Subgroup.mem_zpowers g')
  obtain ⟨s, hs, hsr⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).1 hmem
  have hsP : (s : Gp) ∈ P := Subgroup.mem_subgroupOf.1 hs
  obtain ⟨cE, hcE, hcEe⟩ := (mem_vSub hM).1 c.2
  refine ⟨invE cE, hM.valid_inv _ hcE, ?_⟩
  rw [hM.map_conjE (hM.valid_inv _ hcE) hg, hM.map_inv _ hcE, hcEe, inv_inv]
  have h1 : ((c : Gp) * (s : Gp) * (c : Gp)⁻¹) = ι g := by
    have := congrArg Subtype.val hsr
    simpa using this
  rw [← h1]
  simpa [mul_assoc] using hsP

theorem pow_of_sub {ι : E → Gp} (hM : Model ι) (hK : Nat.card (vSub hM) = 28800) {p k : Nat}
    [hp : Fact p.Prime] {P : Subgroup Gp} (hPK : P ≤ vSub hM) (hPc : Nat.card P = p ^ k)
    (hidx : ¬ p ∣ 28800 / p ^ k) {e : Nat} (hPe : ∀ t ∈ P, t ^ e = 1) {g : E} (hg : validE g = true)
    {j : Nat} (hgj : ι g ^ (p ^ j) = 1) : ι g ^ e = 1 := by
  obtain ⟨n, -, hn⟩ := (Nat.dvd_prime_pow hp.out).1 (orderOf_dvd_of_pow_eq_one hgj)
  obtain ⟨c, hc, hcP⟩ := conj_into_sub hM hK hPK hPc hidx hg hn
  have h := hPe _ hcP
  rw [hM.map_conjE hc hg, conj_pow] at h
  exact conj_eq_one_iff.1 h

theorem pow240_of_parts (x : Gp) (h : x ^ 28800 = 1) (h2 : (x ^ 225) ^ 16 = 1) (h3 : (x ^ 3200) ^ 3 = 1)
    (h5 : (x ^ 1152) ^ 5 = 1) : x ^ 240 = 1 := by
  have e2 : x ^ (225 * 33 * 240) = 1 := by
    rw [show 225 * 33 * 240 = 225 * 16 * 495 by norm_num, pow_mul, pow_mul, h2, one_pow]
  have e3 : x ^ (3200 * 2 * 240) = 1 := by
    rw [show 3200 * 2 * 240 = 3200 * 3 * 160 by norm_num, pow_mul, pow_mul, h3, one_pow]
  have e5 : x ^ (1152 * 13 * 240) = 1 := by
    rw [show 1152 * 13 * 240 = 1152 * 5 * 624 by norm_num, pow_mul, pow_mul, h5, one_pow]
  calc x ^ 240 = x ^ (225 * 33 * 240) * x ^ (3200 * 2 * 240) * x ^ (1152 * 13 * 240) := by
        rw [← pow_add, ← pow_add,
          show 225 * 33 * 240 + 3200 * 2 * 240 + 1152 * 13 * 240 = 28800 * 240 + 240 by norm_num,
          pow_add, pow_mul, h, one_pow, one_mul]
    _ = 1 := by rw [e2, e3, e5, one_mul, one_mul]

end CFSG.KC.FiveStdK

end
