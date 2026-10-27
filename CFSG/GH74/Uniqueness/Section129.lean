module

public import CFSG.GH74.Uniqueness.Section128Arith
public import CFSG.GH74.Uniqueness.Section128Count

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X} {c : Ctx12 Z M} {n i : ℕ}

namespace Sec129

theorem false_of_ncard_omega
    (S : ZDSetup X Z M) (h : LData c n i)
    (hΩ : (omega M).ncard = 2 ^ n + 1) : False := by
  have hXM := S.prodDisc.ncard_omega_mul_card
  have hMD := S.ncard_omega_sub_one_mul_card c.htM
  rw [hΩ, Nat.add_sub_cancel] at hMD
  rw [hΩ] at hXM
  have hDN : c.D ≤ normalizer (c.L : Set X) := by
    intro d hd
    have : d ∈ ((normalizer (c.L : Set X) : Subgroup X) : Set X) := by
      rw [h.normalizer_eq]
      exact ⟨1, c.L.one_mem, d, hd, one_mul d⟩
    exact this
  have hprod := Sec128.card_sup_mul_card_inf_of_le_normalizer hDN
  have hLD : Nat.card ↥(c.L ⊓ c.D) = 2 ^ n - 1 := by
    rw [inf_comm]
    exact h.k_card
  rw [hLD] at hprod
  have hq : 2 ≤ 2 ^ n := Nat.one_lt_two_pow (by have := h.hn; omega)
  have heq : Nat.card ↥(c.L ⊔ c.D) = Nat.card X :=
    Sec128.arith_j1 hq Nat.card_pos h.hi hXM hMD hprod h.bender.card_eq
      (Subgroup.card_le_card_group _)
  have htop : c.L ⊔ c.D = ⊤ := Subgroup.eq_top_of_card_eq _ heq
  have hN : normalizer (c.L : Set X) = ⊤ :=
    top_le_iff.mp (htop ▸ sup_le Subgroup.le_normalizer hDN)
  have hLn : c.L.Normal := Subgroup.normalizer_eq_top_iff.mp hN
  have hsimple : IsSimpleGroup X := S.theorem1_unconditional.1
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal c.L with hb | ht
  · have hz : c.z ∈ c.L := c.z_mem_L
    rw [hb, mem_bot] at hz
    exact Sec128.ne_one_of_two (S.invariant.1 c.z c.hz) hz
  · exact c.hL ht

theorem false_of_unitary
    (S : ZDSetup X Z M) (h : LData c n i) {m : ℕ} (hm : 2 ≤ m)
    (hnm : n = 2 * m)
    (hΩ : (omega M).ncard * (2 ^ m + 1) =
      ((2 ^ m) ^ 3 + 1) * ((2 ^ m) ^ 3 * (2 ^ m - 1) + 2 ^ m + 1)) : False := by
  have hq2 : 2 ≤ 2 ^ m := Nat.one_lt_two_pow (by omega)
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (show 2 ^ m + 1 ≠ 1 by omega)
  have hp2 : p ≠ 2 := by
    rintro rfl
    have : 2 ∣ 2 ^ m := dvd_pow_self 2 (by omega)
    omega
  have hpz : p ∣ zNum Z M := by
    have hz : zNum Z M = 2 ^ n - 1 := by
      unfold zNum
      rw [Nat.card_coe_set_eq]
      exact A2.ncard_zM h
    have hsq : (2 ^ m) ^ 2 - 1 = (2 ^ m + 1) * (2 ^ m - 1) := by
      have := Nat.sq_sub_sq (2 ^ m) 1
      simpa using this
    rw [hz, hnm, pow_mul', hsq]
    exact Dvd.dvd.mul_right hpd _
  have : Fact p.Prime := ⟨hp⟩
  have hβ : conjugate M c.t ∈ omega M := ⟨c.t, rfl⟩
  have hβM : conjugate M c.t ≠ M := (S.prodDisc.conjugate_ne_iff (self_mem_omega M)).mpr c.htM
  let Q : Sylow p ↥(M ⊓ conjugate M c.t) := default
  have hP : ABGLocalTools.IsSylowOf p ((Q : Subgroup ↥(M ⊓ conjugate M c.t)).map
      (M ⊓ conjugate M c.t).subtype) (M ⊓ conjugate M c.t) := ⟨Q, rfl⟩
  obtain ⟨-, -, h3⟩ := S.corollary712 _ hβ hβM p hp hp2 _ hP
  obtain ⟨hΩP, -⟩ := h3 hpz
  have hPp : IsPGroup p ((Q : Subgroup ↥(M ⊓ conjugate M c.t)).map
      (M ⊓ conjugate M c.t).subtype) := Q.isPGroup'.map _
  have hmod := ncard_omega_modEq_ncard_omegaFix (M := M) hp hPp
  rw [hΩP] at hmod
  exact Sec128.arith_unitary hq2 hp hp2 hpd hmod hΩ

end Sec129

theorem ZDSetup.lemma129
    (S : ZDSetup X Z M) (h124 : Lemma124Stmt Z M) (h128 : Lemma128Stmt Z M) :
    Lemma129Stmt Z M := by
  intro c n i h u huD hu2
  obtain ⟨-, hb, ⟨m, j, e, hm2, hq, hB⟩, -, -⟩ := h124 c n i h u huD hu2
  have hcent : u ∈ centralizer (zHull Z M : Set X) := by
    by_contra hcent
    obtain ⟨-, hcase⟩ := h128 c n i h u huD hu2 m j e hB hq
    rcases hcase with ⟨hc, -, -⟩ | ⟨-, hnm, hΩ⟩
    · exact hcent hc
    · rcases hB.bender.cases' with ⟨rfl, -, -⟩ | ⟨rfl, -, a, -, rfl⟩ | ⟨rfl, -, -⟩
      · apply Sec129.false_of_ncard_omega S h
        rw [Sec128.arith_linear Nat.one_le_two_pow hΩ, hnm, pow_mul']
      · exact Sec128.arith_suzuki hΩ
      · exact Sec129.false_of_unitary S h hm2 hnm hΩ
  refine ⟨fun x hx => (mem_centralizer_iff.mp hcent x hx).symm, ?_⟩
  rcases hb with hcomm | ⟨-, k, hk2, hnk, hqk, -⟩
  · exact A2.L_le_cenHull S c (mem_centralizer_iff.mpr fun y hy => hcomm y hy)
  · exfalso
    have hqn : qU Z M u = 2 ^ n := by
      unfold qU
      rw [inf_eq_right.mpr (fun x hx =>
        mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hcent x hx)), h.m_card]
    have hkn : k = n := Nat.pow_right_injective le_rfl (hqk.symm.trans hqn)
    omega

end CFSG.GH74.Uniqueness
