module

public import CFSG.LocalAnalysis.EvenSporadicStandard.ReeStd.Local
public import CFSG.LocalAnalysis.EvenSporadicStandard.ReeStd.Basic
import CFSG.LocalAnalysis.EvenSporadicStandard.J1.DihedralPair
public import CFSG.LocalAnalysis.EvenSporadicStandard.ReeStd.Proj

public section

namespace CFSG.EvenSporadicStandard.ReeStd

open Subgroup

theorem eq_pow_of_sq_eq_one {K : Type*} [Group K] {a : K} (ha : a ^ 2 = 1) {j o : ℕ}
    (ho : Odd o) (h : (a * (a ^ j)⁻¹) ^ o = 1) : a = a ^ j := by
  have hcomm : Commute a (a ^ j)⁻¹ := ((Commute.refl a).pow_right j).inv_right
  have hj2 : (a ^ j) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul, ha, one_pow]
  have hc2 : (a * (a ^ j)⁻¹) ^ 2 = 1 := by
    rw [hcomm.mul_pow, ha, inv_pow, hj2, inv_one, one_mul]
  obtain ⟨m, rfl⟩ := ho
  rw [pow_succ, pow_mul, hc2, one_pow, one_mul] at h
  exact mul_inv_eq_one.1 h

variable {G : Type} [Group G] [Finite G] (H : Setting G)

namespace Setting

@[expose] noncomputable def actB : H.B →* MulAut H.E :=
  H.E.normalizerMonoidHom.comp (Subgroup.inclusion H.B_le_normalizer_E)

@[expose] noncomputable def actNL : H.NL →* MulAut H.E :=
  H.actB.comp (Subgroup.inclusion H.NL_le_B)

theorem actB_apply (b : H.B) (e : H.E) : ((H.actB b e : H.E) : G) = (b : G) * e * (b : G)⁻¹ := rfl

theorem actNL_apply (x : H.NL) (e : H.E) :
    ((H.actNL x e : H.E) : G) = (x : G) * e * (x : G)⁻¹ := rfl

theorem actNL_eq_one_iff (x : H.NL) : H.actNL x = 1 ↔ (x : G) ∈ H.E := by
  constructor
  · intro h1
    have hc : (x : G) ∈ centralizer (H.E : Set G) := by
      refine Subgroup.mem_centralizer_iff.2 fun e he => ?_
      have h2 : (x : G) * e * (x : G)⁻¹ = e := by
        have := congrArg (fun α : MulAut H.E => ((α ⟨e, he⟩ : H.E) : G)) h1
        simpa [actNL_apply] using this
      calc e * (x : G) = ((x : G) * e * (x : G)⁻¹) * (x : G) := by rw [h2]
        _ = (x : G) * e := by group
    rw [← H.centralizer_E]
    exact Subgroup.mem_inf.2 ⟨hc, (H.mem_NL_iff.1 x.2).1⟩
  · intro hx
    refine MulEquiv.ext fun e => Subtype.ext ?_
    rw [actNL_apply]
    have := H.E_comm hx e.2
    calc (x : G) * e * (x : G)⁻¹ = (e * (x : G)) * (x : G)⁻¹ := by rw [this]
      _ = e := by group

theorem card_ker_actNL : Nat.card H.actNL.ker = 8 := by
  have : Nat.card H.actNL.ker = Nat.card H.E := by
    refine Nat.card_congr ⟨fun x => ⟨(x.1 : G), (H.actNL_eq_one_iff x.1).1 x.2⟩,
      fun v => ⟨⟨v, H.mem_NL_iff.2 ⟨H.E_le v.2, le_normalizer v.2⟩⟩,
        (H.actNL_eq_one_iff _).2 v.2⟩, ?_, ?_⟩
    · intro x
      rfl
    · intro v
      rfl
  rw [this, H.card_E]

theorem card_mulAut_E : Nat.card (MulAut H.E) = 168 :=
  J1Std.card_mulAut_of_elemAbelian_eight H.card_E (fun a b => Subtype.ext (H.E_comm a.2 b.2))
    (fun a => Subtype.ext (H.sq_E a.1 a.2))

theorem card_range_actNL : Nat.card H.actNL.range = 21 := by
  have h1 := Subgroup.card_ker_mul_card_range H.actNL
  rw [H.card_ker_actNL, H.card_NL] at h1
  omega

theorem exists_NL_of_two_pow (b : H.B) {k : ℕ} (hk : b ^ 2 ^ k = 1) :
    ∃ x : H.NL, H.actNL x = H.actB b := by
  have hk' : (b : G) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hbz : (b : G) * H.z = H.z * b :=
    mem_centralizer_singleton_iff.1 (H.B_le_centralizer b.2)
  rcases H.mem_centralizer_iff.1 (H.B_le_centralizer b.2) with hm | hm
  · have hL : (b : G) ∈ H.L :=
      H.le_L_of_isPGroup (P := zpowers (b : G)) (zpowers_le.2 hm) (isPGroup_zpowers hk')
        (mem_zpowers _)
    exact ⟨⟨b, H.mem_NL_iff.2 ⟨hL, H.B_le_normalizer_E b.2⟩⟩, rfl⟩
  · have hcomm : Commute (b : G) H.z := hbz
    have h1 : (b : G) ^ 2 ^ (k + 1) = 1 := by rw [pow_succ, pow_mul, hk', one_pow]
    have h2 : H.z ^ 2 ^ (k + 1) = 1 := by rw [pow_succ', pow_mul, pow_two, H.z_mul_self, one_pow]
    have hbz2 : ((b : G) * H.z) ^ 2 ^ (k + 1) = 1 := by
      rw [hcomm.mul_pow, h1, h2, one_mul]
    have hL : (b : G) * H.z ∈ H.L :=
      H.le_L_of_isPGroup (P := zpowers ((b : G) * H.z)) (zpowers_le.2 hm) (isPGroup_zpowers hbz2)
        (mem_zpowers _)
    have hB : (b : G) * H.z ∈ H.B := mul_mem b.2 H.z_mem_B
    refine ⟨⟨(b : G) * H.z, H.mem_NL_iff.2 ⟨hL, H.B_le_normalizer_E hB⟩⟩, ?_⟩
    refine MulEquiv.ext fun e => Subtype.ext ?_
    rw [actNL_apply, actB_apply]
    have hze : H.z * (e : G) * H.z⁻¹ = e := by rw [← H.z_comm_E e.2]; group
    calc (b : G) * H.z * e * ((b : G) * H.z)⁻¹ = (b : G) * (H.z * e * H.z⁻¹) * (b : G)⁻¹ := by
          group
      _ = (b : G) * e * (b : G)⁻¹ := by rw [hze]

theorem card_range_B : Nat.card H.actB.range = 21 := by
  have hF : H.actNL.range ≤ H.actB.range := by
    rintro _ ⟨x, rfl⟩
    exact ⟨Subgroup.inclusion H.NL_le_B x, rfl⟩
  have hdvd : Nat.card H.actB.range ∣ 168 := by
    rw [← H.card_mulAut_E]
    exact Subgroup.card_subgroup_dvd_card _
  have hodd : Odd (Nat.card H.actB.range) := by
    rw [← Nat.not_even_iff_odd]
    intro hev
    have h2 : 2 ∣ Nat.card H.actB.range := even_iff_two_dvd.1 hev
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card' (G := H.actB.range) 2 h2
    obtain ⟨b, hb⟩ := q.2
    obtain ⟨j, ⟨k, hk⟩, o, ho, hc⟩ := exists_two_part b
    obtain ⟨x, hx⟩ := H.exists_NL_of_two_pow (b ^ j) hk
    have ha : orderOf (H.actB b) = 2 := by
      rw [hb, Subgroup.orderOf_coe]
      exact hq
    have ha2 : H.actB b ^ 2 = 1 := by
      rw [← ha]
      exact pow_orderOf_eq_one _
    have hcj : (H.actB b * (H.actB b ^ j)⁻¹) ^ o = 1 := by
      have := congrArg H.actB hc
      simpa only [map_pow, map_mul, map_inv, map_one] using this
    have heq : H.actB b = H.actB (b ^ j) := by
      rw [map_pow]
      exact eq_pow_of_sq_eq_one ha2 ho hcj
    have hmemF : H.actB b ∈ H.actNL.range := MonoidHom.mem_range.2 ⟨x, by rw [hx, heq]⟩
    have h21 : orderOf (H.actB b) ∣ 21 := by
      rw [← H.card_range_actNL, ← Subgroup.orderOf_mk (H.actB b) hmemF]
      exact orderOf_dvd_natCard _
    rw [ha] at h21
    exact absurd h21 (by norm_num)
  have h21 : 21 ∣ Nat.card H.actB.range := by
    rw [← H.card_range_actNL]
    exact Subgroup.card_dvd_of_le hF
  have hcop : Nat.Coprime (Nat.card H.actB.range) (2 ^ 3) :=
    (Nat.coprime_two_right.2 hodd).pow_right 3
  have hd21 : Nat.card H.actB.range ∣ 21 := by
    have : Nat.card H.actB.range ∣ 21 * 2 ^ 3 := hdvd
    exact hcop.dvd_of_dvd_mul_right this
  exact Nat.dvd_antisymm hd21 h21

end Setting

namespace LocalSetting

variable (L : LocalSetting (G := G))

theorem actB_pow_apply (b : L.B) (n : ℕ) (e : L.E) :
    ((((L.actB b) ^ n) e : L.E) : G) = (b : G) ^ n * e * ((b : G) ^ n)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', MulAut.mul_apply, L.actB_apply, ih]
    group

end LocalSetting

@[expose] noncomputable def Setting.toLocal (H : Setting G) : LocalSetting G :=
  let hB : BOf H.E H.z ≤ normalizer (H.E : Set G) := by
    simpa [BOf, Setting.B, Setting.V, VOf] using H.B_le_normalizer_E
  { z := H.z
    E := H.E
    simple := H.simple
    nonabelian := H.nonabelian
    order_z := H.order_z
    card_E := H.card_E
    sq_E := H.sq_E
    z_not_mem_E := H.z_not_mem_E
    z_comm_E := H.z_comm_E
    sylow := by
      intro P hP hPC
      obtain ⟨g, hgM, hg⟩ := H.exists_conj_le_V hP hPC
      refine ⟨g, ?_, ?_⟩
      · rw [mem_centralizer_singleton_iff]
        exact H.comm_z hgM
      · simpa [VOf, Setting.V] using hg
    hB_le := hB
    card_range_actB := by
      have hfun : actBOf H.E H.z hB = H.actB := by
        ext b e
        rfl
      rw [hfun]
      exact H.card_range_B }

@[simp] theorem Setting.toLocal_z (H : Setting G) : H.toLocal.z = H.z := rfl

@[simp] theorem Setting.toLocal_E (H : Setting G) : H.toLocal.E = H.E := rfl

noncomputable instance : Coe (Setting G) (LocalSetting G) := ⟨Setting.toLocal⟩

end CFSG.EvenSporadicStandard.ReeStd
