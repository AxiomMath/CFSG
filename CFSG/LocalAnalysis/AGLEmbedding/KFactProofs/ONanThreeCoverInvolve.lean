module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CaseTwoLocalL28

public section

namespace CFSG.AGLEmbedding.KFactProofs.ThreeCover

open CFSG.Quasithin.F6.L28Res

theorem center_G8 : Subgroup.center G8 = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  have h1 : (MulAut.conj z : MulAut G8) = MulAut.conj 1 := by
    refine MulEquiv.ext fun h => ?_
    have := Subgroup.mem_center_iff.1 hz h
    calc (MulAut.conj z : MulAut G8) h = z * h * z⁻¹ := MulAut.conj_apply z h
      _ = h * z * z⁻¹ := by rw [← this]
      _ = h := by group
      _ = (MulAut.conj (1 : G8) : MulAut G8) h := by rw [MulAut.conj_apply]; group
  exact L28Local.conj_injective_G8 h1

theorem l28_facts {L : Type} [Group L] (hL : IsCaseTwoGroup 3 L) :
    Nat.card L = 504 ∧ Subgroup.center L = ⊥ ∧ ∃ y : L, orderOf y = 9 := by
  obtain ⟨e⟩ := L28Local.nonempty_equiv_G8 hL
  refine ⟨?_, ?_, e.symm g9, ?_⟩
  · rw [Nat.card_congr e.toEquiv]
    exact card_G8
  · rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    have hc : e z ∈ Subgroup.center G8 := by
      rw [Subgroup.mem_center_iff]
      intro h
      have := Subgroup.mem_center_iff.1 hz (e.symm h)
      simpa using congrArg e this
    rw [center_G8, Subgroup.mem_bot] at hc
    exact e.injective (by rw [hc, map_one])
  · rw [MulEquiv.orderOf_eq]
    exact L28Local.orderOf_g9

theorem exists_dvd_orderOf_quotient {K L : Type} [Group K] [Group L]
    (hL : Subgroup.center L = ⊥) (B : Subgroup K) (f : B →* L) (hf : Function.Surjective f)
    (y : L) : ∃ x : K ⧸ Subgroup.center K, orderOf y ∣ orderOf x := by
  obtain ⟨b, rfl⟩ := hf y
  refine ⟨QuotientGroup.mk (b : K), orderOf_dvd_of_pow_eq_one ?_⟩
  set m := orderOf (QuotientGroup.mk (b : K) : K ⧸ Subgroup.center K) with hm
  have hmem : (b : K) ^ m ∈ Subgroup.center K := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact pow_orderOf_eq_one _
  have hc : f (b ^ m) ∈ Subgroup.center L := by
    rw [Subgroup.mem_center_iff]
    intro l
    obtain ⟨b', rfl⟩ := hf l
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact Subgroup.mem_center_iff.1 hmem (b' : K)
  rw [hL, Subgroup.mem_bot, map_pow] at hc
  exact hc

theorem seven_dvd_card_quotient {K L : Type} [Group K] [Finite K] [Group L]
    (hZ : IsPGroup 3 (Subgroup.center K)) (B : Subgroup K) (f : B →* L)
    (hf : Function.Surjective f) (hL7 : 7 ∣ Nat.card L) : 7 ∣ Nat.card (K ⧸ Subgroup.center K) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h1 : Nat.card L ∣ Nat.card B := Subgroup.card_dvd_of_surjective hf
  have h2 : Nat.card B ∣ Nat.card K := Subgroup.card_subgroup_dvd_card B
  have h3 : Nat.card K = Nat.card (K ⧸ Subgroup.center K) * Nat.card (Subgroup.center K) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  obtain ⟨k, hk⟩ := hZ.exists_card_eq
  have h7 : 7 ∣ Nat.card (K ⧸ Subgroup.center K) * 3 ^ k := by
    rw [← hk, ← h3]
    exact hL7.trans (h1.trans h2)
  rcases (Nat.Prime.dvd_mul (by norm_num)).1 h7 with h | h
  · exact h
  · exfalso
    have := Nat.Prime.dvd_of_dvd_pow (by norm_num) h
    omega

theorem false_of_exponent_three {K L : Type} [Group K] [Finite K] [Group L]
    (hL : IsCaseTwoGroup 3 L)
    (hexp : ∀ x : K ⧸ Subgroup.center K, (∃ n : ℕ, x ^ 3 ^ n = 1) → x ^ 3 = 1)
    (B : Subgroup K) (f : B →* L) (hf : Function.Surjective f) : False := by
  obtain ⟨-, hc, y, hy⟩ := l28_facts hL
  obtain ⟨x, hx⟩ := exists_dvd_orderOf_quotient hc B f hf y
  rw [hy] at hx
  obtain ⟨m, hm⟩ := hx
  have hpos : 0 < orderOf x := orderOf_pos x
  have hm0 : m ≠ 0 := by
    rintro rfl
    omega
  have hord : orderOf (x ^ m) = 9 := by
    rw [orderOf_pow_of_dvd hm0 (Dvd.intro_left _ hm.symm), hm]
    exact Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)
  have h1 : (x ^ m) ^ 3 = 1 :=
    hexp _ ⟨2, by rw [show (3 : ℕ) ^ 2 = 9 by norm_num, ← hord]; exact pow_orderOf_eq_one _⟩
  have h2 : orderOf (x ^ m) ∣ 3 := orderOf_dvd_of_pow_eq_one h1
  rw [hord] at h2
  omega

theorem pow_eq_one_of_elemAbelian_index {S : Type} [Group S] [Finite S] {p : ℕ} [Fact p.Prime]
    {E : Subgroup S} (hE : Open.IsElemAbelian p E) (hidx : ¬ p ∣ E.index) (t : S)
    (ht : ∃ n : ℕ, t ^ p ^ n = 1) : t ^ p = 1 := by
  have hEp : IsPGroup p E := fun g => ⟨1, Subtype.ext (by simpa using hE.2 g g.2)⟩
  set T : Sylow p S := hEp.toSylow hidx with hT
  have hTE : (T : Subgroup S) = E := rfl
  obtain ⟨n, hn⟩ := ht
  have hpg : IsPGroup p (Subgroup.zpowers t) := by
    rw [IsPGroup.iff_card, Nat.card_zpowers]
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Fact.out).1 (orderOf_dvd_of_pow_eq_one hn)
    exact ⟨k, hk⟩
  obtain ⟨P, hP⟩ := hpg.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq S T P
  have htP : t ∈ (P : Subgroup S) := hP (Subgroup.mem_zpowers t)
  have h2 : ((g • T : Sylow p S) : Subgroup S) = (T : Subgroup S).map (MulAut.conj g).toMonoidHom :=
    by rw [Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def]; rfl
  rw [← hg, h2, Subgroup.mem_map] at htP
  obtain ⟨s, hs, rfl⟩ := htP
  have := hE.2 s (hTE ▸ hs)
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [conj_pow, this, mul_one, mul_inv_cancel]

end CFSG.AGLEmbedding.KFactProofs.ThreeCover
