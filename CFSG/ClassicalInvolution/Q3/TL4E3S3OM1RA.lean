module

public import CFSG.ClassicalInvolution.Q3.TL4E3S3OM2A

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.Blueprint

namespace E3S3O

variable {W : Type} [Group W] [Finite W] {Φ : Set (Subgroup W)} {K K' : Subgroup W} {k k' : W}

omit [Finite W] in
theorem mul_sq_eq_one (h : TwinBase3 Φ K K' k k') : k * k' * (k * k') = 1 := by
  have hc := Subgroup.mem_center_iff.mp h.center k
  have hkk' : k * k' = k' * k := by
    calc k * k' = k⁻¹ * (k * (k * k')) := by group
      _ = k⁻¹ * (k * k' * k) := by rw [hc]
      _ = k' * k := by group
  calc k * k' * (k * k') = k * (k' * k) * k' := by group
    _ = k * (k * k') * k' := by rw [hkk']
    _ = k * k * (k' * k') := by group
    _ = 1 := by rw [h.invK.sq, h.invK'.sq, one_mul]

theorem isPGroup_ker_quotCenter (h : TwinBase3 Φ K K' k k') (N : Subgroup W) [N.Normal]
    (hN : N = Subgroup.zpowers (k * k')) :
    IsPGroup 2 ↥((QuotientGroup.mk' (Subgroup.center (W ⧸ N))).comp (QuotientGroup.mk' N)).ker := by
  have hZ2 := Vtx.isPGroup_center_of_oddFree h.odd
  have hNc : N ≤ Subgroup.center W := by
    rw [hN, Subgroup.zpowers_le]
    exact h.center
  have hN2 : ∀ n ∈ N, n * n = 1 := by
    intro n hn
    rw [hN] at hn
    obtain ⟨z, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    rw [← zpow_add, show z + z = 2 * z by ring, zpow_mul, zpow_two, mul_sq_eq_one h, one_zpow]
  intro g
  obtain ⟨a, m, hm, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (g : W)).ne'
  refine ⟨a, Subtype.ext ?_⟩
  rw [Subgroup.coe_pow, OneMemClass.coe_one]
  set q : W := (g : W) ^ 2 ^ a with hq
  have hqm : q ^ m = 1 := by rw [hq, ← pow_mul, ← hord, pow_orderOf_eq_one]
  have hqker : q ∈ ((QuotientGroup.mk' (Subgroup.center (W ⧸ N))).comp
      (QuotientGroup.mk' N)).ker := Subgroup.pow_mem _ g.2 _
  have h1 : (QuotientGroup.mk q : W ⧸ N) ∈ Subgroup.center (W ⧸ N) := by
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hqker
    exact hqker
  have hqZ : q ∈ Subgroup.center W := by
    rw [Subgroup.mem_center_iff]
    intro w
    set n := q⁻¹ * (w * q * w⁻¹) with hn
    have hnN : n ∈ N := by
      rw [← QuotientGroup.eq_one_iff, hn]
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rw [Subgroup.mem_center_iff.mp h1 (QuotientGroup.mk w), mul_inv_cancel_right,
        inv_mul_cancel]
    have hnZ := hNc hnN
    have hwq : w * q * w⁻¹ = q * n := by rw [hn]; group
    have hn1 : n = 1 := by
      have h2 : n ^ m = 1 := by
        have h3 : (w * q * w⁻¹) ^ m = 1 := by rw [conj_pow, hqm, mul_one, mul_inv_cancel]
        have hcomm : Commute q n := Subgroup.mem_center_iff.mp hnZ q
        rw [hwq, hcomm.mul_pow, hqm, one_mul] at h3
        exact h3
      have hd1 : orderOf n ∣ m := orderOf_dvd_of_pow_eq_one h2
      have hd2 : orderOf n ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hN2 n hnN)
      have hcop : Nat.Coprime 2 m := Nat.coprime_two_left.mpr hm
      have h4 := Nat.dvd_gcd hd2 hd1
      rw [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h4
      exact h4
    rw [hn1, mul_one] at hwq
    calc w * q = w * q * w⁻¹ * w := by group
      _ = q * w := by rw [hwq]
  obtain ⟨j, hj⟩ := hZ2 ⟨q, hqZ⟩
  have hj' : q ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
  have hcop : Nat.Coprime (2 ^ j) m := Nat.Coprime.pow_left j (Nat.coprime_two_left.mpr hm)
  have h4 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hj') (orderOf_dvd_of_pow_eq_one hqm)
  rw [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h4
  exact h4

variable {Q : Type} [Group Q]

theorem center_le_ker_of_simple (h : TwinBase3 Φ K K' k k') (f : W →* Q)
    (hf : Function.Surjective f) (hf2 : IsPGroup 2 ↥f.ker) (hs : IsSimpleGroup Q) :
    Subgroup.center W ≤ f.ker := by
  have hZ : Subgroup.center Q = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with hb | ht
    · exact hb
    · exfalso
      obtain ⟨S₀, hS₀, -⟩ := IsSylow2In.exists_ge (P := K) (IsPGroup.of_bot (p := 2)) bot_le
      obtain ⟨e⟩ := h.fam.quat K h.memK S₀ hS₀
      have e2 : ↥S₀ ≃* QuaternionGroup 2 := e
      set x : W := (e2.symm (QuaternionGroup.a 1) : W)
      set y : W := (e2.symm (QuaternionGroup.xa 0) : W)
      have hxy : x * y ≠ y * x := by
        intro hc
        have h1 : e2.symm (QuaternionGroup.a 1) * e2.symm (QuaternionGroup.xa 0) =
            e2.symm (QuaternionGroup.xa 0) * e2.symm (QuaternionGroup.a 1) := Subtype.ext hc
        rw [← map_mul, ← map_mul] at h1
        exact absurd (e2.symm.injective h1) (by decide)
      have hP := inf_eq_bot_of_not_mem h.invK hf2 (by simpa using not_mem_ker h f hf2 1)
      have hxK : x ∈ K := hS₀.1 (e2.symm _).2
      have hyK : y ∈ K := hS₀.1 (e2.symm _).2
      have hfxy : f (x * y) = f (y * x) := by
        have hc := Subgroup.mem_center_iff.mp (ht ▸ Subgroup.mem_top (f x)) (f y)
        rw [map_mul, map_mul, hc]
      have hmem : (y * x)⁻¹ * (x * y) ∈ K ⊓ f.ker := by
        refine ⟨K.mul_mem (K.inv_mem (K.mul_mem hyK hxK)) (K.mul_mem hxK hyK), ?_⟩
        show (y * x)⁻¹ * (x * y) ∈ f.ker
        rw [MonoidHom.mem_ker, map_mul, map_inv, hfxy, inv_mul_cancel]
      rw [hP, Subgroup.mem_bot] at hmem
      exact hxy (inv_mul_eq_one.mp hmem).symm
  intro z hz
  rw [MonoidHom.mem_ker]
  have hfz : f z ∈ Subgroup.center Q := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨w, rfl⟩ := hf q
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz w]
  rw [hZ] at hfz
  exact Subgroup.mem_bot.mp hfz

theorem ker_eq_center_of_simple (h : TwinBase3 Φ K K' k k') (f : W →* Q)
    (hf : Function.Surjective f) (hf2 : IsPGroup 2 ↥f.ker) (hs : IsSimpleGroup Q) :
    f.ker = Subgroup.center W :=
  le_antisymm (ker_le_center h f hf2) (center_le_ker_of_simple h f hf hf2 hs)

theorem isPGroup_conj_of_simple (h : TwinBase3 Φ K K' k k') (f : W →* Q)
    (hf : Function.Surjective f) (hf2 : IsPGroup 2 ↥f.ker) (hs : IsSimpleGroup Q)
    (hOS : Balance.oddCoreIn (Subgroup.centralizer ({f k} : Set Q)) = ⊥) (g : W) :
    IsPGroup 2 ↥(conjSub g K) := by
  have : Finite Q := Finite.of_surjective f hf
  have hker := ker_eq_center_of_simple h f hf hf2 hs
  let e : W ⧸ Subgroup.center W ≃* Q :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)
  have he : e (QuotientGroup.mk k) = f k := rfl
  have hle := Vtx.oddCent_le_center_of_mk
    (oddCoreIn_centralizer_eq_bot_of_mulEquiv e _ (by rw [he]; exact hOS))
  have hKC := h.fam.le_centralizer h.memK h.invK
  have hCN := h.fam.tight K h.memK k h.invK
  have hOK : oddCoreOf K ≤ oddCoreOf (Subgroup.centralizer ({k} : Set W)) :=
    le_oddCoreOf_of_normal_odd ((oddCoreOf_le_self K).trans hKC)
      (fun c hc => mem_normalizer_oddCore_of_mem_normalizer (hCN hc)) (oddCoreOf_odd_natCard K)
  have hZ2 := Vtx.isPGroup_center_of_oddFree h.odd
  have hO : oddCoreOf K = ⊥ := by
    rw [eq_bot_iff]
    intro o ho
    have hoZ : o ∈ Subgroup.center W := hle (hOK ho)
    exact Subgroup.mem_bot.mpr (eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard K) ho
      (hZ2.to_le (Subgroup.zpowers_le.mpr hoZ)))
  have h2 : IsPGroup 2 ↥K := by
    intro x
    obtain ⟨n, hn⟩ := h.fam.twoGroup K h.memK (QuotientGroup.mk x)
    refine ⟨n, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hn
    have hx : (x : W) ^ 2 ^ n ∈ oddCoreOf K := mem_oddCoreOf_iff.mpr ⟨_, hn⟩
    rw [hO, Subgroup.mem_bot] at hx
    exact Subtype.ext (by simpa using hx)
  exact (h2.map (MulAut.conj g).toMonoidHom : IsPGroup 2 ↥(conjSub g K))

end E3S3O

end CFSG.ClassicalInvolution.Q3.TL4
