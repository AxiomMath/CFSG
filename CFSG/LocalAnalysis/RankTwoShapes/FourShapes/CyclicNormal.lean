module

public import CFSG.LocalAnalysis.RankTwoShapes.FourShapes.SquareRoots
public import CFSG.LocalAnalysis.RankTwoShapes.FourShapes.CyclicCriterion
public import CFSG.LocalAnalysis.LargeEvenClassification.MaximalAbelian

public section

namespace CFSG.RankTwoShapes

open CFSG.LargeEvenClassification

noncomputable def autExponent (H : Type*) [Group H] [IsCyclic H] {n : ℕ} (hn : Nat.card H = n) :
    MulAut H →* (ZMod n)ˣ :=
  (MulDistribMulAction.toMonoidHomZModOfIsCyclic H (MulAut H) hn).toHomUnits

theorem autExponent_apply (H : Type*) [Group H] [IsCyclic H] {n : ℕ} [NeZero n]
    (hn : Nat.card H = n) (σ : MulAut H) (g : H) :
    σ g = g ^ ((autExponent H hn σ : ZMod n).val) := by
  have h := MulDistribMulAction.toMonoidHomZModOfIsCyclic_apply hn σ g
    ((autExponent H hn σ : ZMod n).val : ℤ) (by
      rw [Int.cast_natCast, ZMod.natCast_zmod_val]
      simp [autExponent])
  rw [MulAut.smul_def, zpow_natCast] at h
  exact h

theorem autExponent_injective (H : Type*) [Group H] [IsCyclic H] {n : ℕ} [NeZero n]
    (hn : Nat.card H = n) : Function.Injective (autExponent H hn) := by
  intro σ τ hστ
  ext g
  rw [autExponent_apply H hn σ g, autExponent_apply H hn τ g, hστ]

theorem mulAut_mul_comm_of_isCyclic {H : Type*} [Group H] [IsCyclic H] (σ τ : MulAut H) :
    σ * τ = τ * σ := by
  obtain ⟨m, hm⟩ := MonoidHom.map_cyclic σ.toMonoidHom
  obtain ⟨m', hm'⟩ := MonoidHom.map_cyclic τ.toMonoidHom
  have h1 : ∀ x, σ x = x ^ m := hm
  have h2 : ∀ x, τ x = x ^ m' := hm'
  ext g
  rw [MulAut.mul_apply, MulAut.mul_apply, h1, h2, h2, h1, ← zpow_mul, ← zpow_mul, mul_comm]

theorem one_add_two_pow_mul_self {a : ℕ} (ha : 2 ≤ a) :
    ((1 + 2 ^ (a - 1) : ZMod (2 ^ a))) * (1 + 2 ^ (a - 1)) = 1 := by
  have h0 : (2 : ZMod (2 ^ a)) ^ a = 0 := by
    exact_mod_cast ZMod.natCast_self (2 ^ a)
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 2 := ⟨a - 2, by omega⟩
  have e : (1 + (2 : ZMod (2 ^ (b + 2))) ^ (b + 2 - 1)) * (1 + 2 ^ (b + 2 - 1)) =
      1 + 2 ^ (b + 2) * (1 + 2 ^ b) := by
    rw [show b + 2 - 1 = b + 1 by omega]
    ring
  rw [e, h0, zero_mul, add_zero]

@[expose] def principalUnit (a : ℕ) (ha : 2 ≤ a) : (ZMod (2 ^ a))ˣ where
  val := 1 + 2 ^ (a - 1)
  inv := 1 + 2 ^ (a - 1)
  val_inv := one_add_two_pow_mul_self ha
  inv_val := one_add_two_pow_mul_self ha

@[simp] theorem principalUnit_val (a : ℕ) (ha : 2 ≤ a) :
    (principalUnit a ha : ZMod (2 ^ a)) = 1 + 2 ^ (a - 1) := rfl

theorem val_one_add_two_pow {a : ℕ} (ha : 2 ≤ a) :
    ((1 + 2 ^ (a - 1) : ZMod (2 ^ a))).val = 1 + 2 ^ (a - 1) := by
  have hc : ((1 + 2 ^ (a - 1) : ℕ) : ZMod (2 ^ a)) = 1 + 2 ^ (a - 1) := by push_cast; rfl
  rw [← hc, ZMod.val_natCast, Nat.mod_eq_of_lt]
  have e : 2 ^ a = 2 ^ (a - 1) * 2 := by rw [← pow_succ]; congr 1; omega
  have : 2 ≤ 2 ^ (a - 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (a - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem principalUnit_ne_one {a : ℕ} (ha : 2 ≤ a) : principalUnit a ha ≠ 1 := by
  have : Fact (1 < 2 ^ a) := ⟨Nat.one_lt_two_pow (by omega)⟩
  intro h
  have h' := congrArg (fun u : (ZMod (2 ^ a))ˣ => (u : ZMod (2 ^ a)).val) h
  simp only [principalUnit_val, Units.val_one] at h'
  rw [val_one_add_two_pow ha, ZMod.val_one] at h'
  have : 1 ≤ 2 ^ (a - 1) := Nat.one_le_two_pow
  omega

theorem orderOf_principalUnit {a : ℕ} (ha : 2 ≤ a) : orderOf (principalUnit a ha) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply orderOf_eq_prime _ (principalUnit_ne_one ha)
  rw [Units.ext_iff, Units.val_pow_eq_pow_val, principalUnit_val, Units.val_one, pow_two,
    one_add_two_pow_mul_self ha]

theorem principalUnit_mem {a : ℕ} (ha : 3 ≤ a) (S : Subgroup (ZMod (2 ^ a))ˣ)
    (hS : 2 < Nat.card S) : principalUnit a (by omega) ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h4 : 4 ∣ 2 ^ a := ⟨2 ^ (a - 2), by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega⟩
  let ρ : S →* (ZMod 4)ˣ := (ZMod.unitsMap h4).comp S.subtype
  have hrange : Nat.card ρ.range ≤ 2 := by
    calc Nat.card ρ.range ≤ Nat.card (ZMod 4)ˣ := Subgroup.card_le_card_group _
      _ = 2 := by
        rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
          show (4 : ℕ) = 2 ^ 2 by norm_num, Nat.totient_prime_pow Nat.prime_two (by norm_num)]
        norm_num
  have hmul : Nat.card ρ.ker * Nat.card ρ.range = Nat.card S := by
    rw [← Subgroup.index_ker]
    exact Subgroup.card_mul_index ρ.ker
  have hU : IsPGroup 2 (ZMod (2 ^ a))ˣ := by
    apply IsPGroup.of_card (n := a - 1)
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.totient_prime_pow Nat.prime_two (by omega)]
    norm_num
  have hKp : IsPGroup 2 ρ.ker := (hU.to_subgroup S).to_subgroup _
  obtain ⟨e, he⟩ := IsPGroup.iff_card.mp hKp
  have hker2 : 2 ≤ Nat.card ρ.ker := by
    by_contra hlt
    push Not at hlt
    have : Nat.card S ≤ 1 * 2 := by
      rw [← hmul]
      exact Nat.mul_le_mul (by omega) hrange
    omega
  have he0 : e ≠ 0 := by
    rintro rfl
    rw [he] at hker2
    norm_num at hker2
  obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' 2 (he ▸ dvd_pow_self 2 he0)
  obtain ⟨w, hw⟩ : ∃ w : (ZMod (2 ^ a))ˣ, w = ((k : S) : (ZMod (2 ^ a))ˣ) := ⟨_, rfl⟩
  have hwS : w ∈ S := hw ▸ (k : S).2
  have hw2 : w ^ 2 = 1 := by
    have h1 := pow_orderOf_eq_one k
    rw [hk] at h1
    have h2 := congrArg (fun x : ρ.ker => ((x : S) : (ZMod (2 ^ a))ˣ)) h1
    rw [hw]
    simpa using h2
  have hw1 : w ≠ 1 := by
    intro h1
    have : k = 1 := Subtype.ext (Subtype.ext (hw ▸ h1))
    rw [this, orderOf_one] at hk
    norm_num at hk
  have hρw : (ZMod.castHom h4 (ZMod 4)) (w : ZMod (2 ^ a)) = 1 := by
    have h1 : ρ k = 1 := k.2
    have h2 := congrArg (fun u : (ZMod 4)ˣ => (u : ZMod 4)) h1
    rw [hw]
    simpa [ρ, ZMod.unitsMap_def] using h2
  have hval2 : (w : ZMod (2 ^ a)) ^ 2 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hw2, Units.val_one]
  have hz4 : (2 : ZMod 4) ^ (a - 1) = 0 := by
    obtain ⟨c, hc⟩ : ∃ c, a - 1 = c + 2 := ⟨a - 3, by omega⟩
    rw [hc, pow_add, show (2 : ZMod 4) ^ 2 = 0 by decide, mul_zero]
  rcases zmod_sq_eq_one_two_pow ha _ hval2 with h | h | h | h
  · exact absurd (Units.ext h) hw1
  · rw [h, map_neg, map_one] at hρw
    exact absurd hρw (by decide)
  · have : w = principalUnit a (by omega) := Units.ext h
    rw [← this]
    exact hwS
  · rw [h, map_add, map_neg, map_one, map_pow, map_ofNat, hz4] at hρw
    exact absurd hρw (by decide)

theorem cyclic_two_large_automorphism_subgroup {H : Type*} [Group H] {a : ℕ} (ha : 3 ≤ a)
    (h : H) (hgen : Subgroup.zpowers h = ⊤) (hh : orderOf h = 2 ^ a)
    (Γ : Subgroup (MulAut H)) (hΓ : 2 < Nat.card Γ) :
    ∃ σ ∈ Γ, σ h = h ^ (1 + 2 ^ (a - 1)) ∧ orderOf σ = 2 := by
  have : IsCyclic H := isCyclic_iff_exists_zpowers_eq_top.mpr ⟨h, hgen⟩
  have hcard : Nat.card H = 2 ^ a := by
    rw [← hh, ← Nat.card_zpowers, hgen, Subgroup.card_top]
  have hinj := autExponent_injective H hcard
  have hS : 2 < Nat.card (Γ.map (autExponent H hcard)) := by
    rwa [Subgroup.card_map_of_injective hinj]
  obtain ⟨σ, hσΓ, hσ⟩ := Subgroup.mem_map.mp (principalUnit_mem ha _ hS)
  refine ⟨σ, hσΓ, ?_, ?_⟩
  · rw [autExponent_apply H hcard σ h, hσ, principalUnit_val, val_one_add_two_pow (by omega)]
  · rw [← orderOf_injective _ hinj σ, hσ, orderOf_principalUnit]

theorem pow_eq_one_or_of_two_pow_dvd {G : Type*} [Group G] {a : ℕ} (ha : 1 ≤ a) {h : G}
    (hh : orderOf h = 2 ^ a) {j : ℕ} (hj : 2 ^ (a - 1) ∣ j) :
    h ^ j = 1 ∨ h ^ j = h ^ 2 ^ (a - 1) := by
  obtain ⟨k, rfl⟩ := hj
  have hz2 : (h ^ 2 ^ (a - 1)) ^ 2 = 1 := by
    rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel ha, ← hh, pow_orderOf_eq_one]
  rcases Nat.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · left
    rw [pow_mul, ← two_mul, pow_mul, hz2, one_pow]
  · right
    rw [pow_mul, pow_add, pow_mul, hz2, one_pow, one_mul, pow_one]

theorem unipotent_extension_involutions {G : Type*} [Group G] {a : ℕ} (ha : 3 ≤ a) {h x : G}
    (hh : orderOf h = 2 ^ a) (hx2 : x ^ 2 ∈ Subgroup.zpowers h)
    (hconj : x * h * x⁻¹ = h ^ (1 + 2 ^ (a - 1))) :
    ∃ c : ℕ, (h ^ c * x) ^ 2 = 1 ∧
      (∀ g ∈ Subgroup.zpowers h, (g * (h ^ c * x)) ^ 2 = 1 → g = 1 ∨ g = h ^ 2 ^ (a - 1)) ∧
      (∀ g ∈ Subgroup.zpowers h, g ^ 2 = 1 → g = 1 ∨ g = h ^ 2 ^ (a - 1)) := by
  have hfin : IsOfFinOrder h := orderOf_pos_iff.mp (by rw [hh]; positivity)
  have hpow : ∀ g ∈ Subgroup.zpowers h, ∃ j : ℕ, h ^ j = g := fun g hg =>
    (Submonoid.mem_powers_iff g h).mp (hfin.mem_powers_iff_mem_zpowers.mpr hg)
  have hconjpow : ∀ j : ℕ, x * h ^ j * x⁻¹ = h ^ ((1 + 2 ^ (a - 1)) * j) := fun j => by
    rw [← conj_pow, hconj, ← pow_mul]
  have hpow_one : ∀ n : ℕ, h ^ n = 1 ↔ 2 ^ a ∣ n := fun n => by
    rw [← hh]
    exact orderOf_dvd_iff_pow_eq_one.symm
  have e3 : 2 ^ a = 2 * 2 ^ (a - 1) := by rw [← pow_succ']; congr 1; omega
  have e4 : 2 ^ (a - 1) = 2 * 2 ^ (a - 2) := by rw [← pow_succ']; congr 1; omega
  obtain ⟨b, hb⟩ := hpow _ hx2
  have hbeven : 2 ∣ b := by
    have h1 : x * h ^ b * x⁻¹ = h ^ b := by rw [hb, pow_two]; group
    rw [hconjpow] at h1
    have h2 : h ^ (b * 2 ^ (a - 1)) = 1 := by
      have e : h ^ ((1 + 2 ^ (a - 1)) * b) = h ^ b * h ^ (b * 2 ^ (a - 1)) := by
        rw [← pow_add]
        congr 1
        ring
      rw [e] at h1
      exact mul_eq_left.mp h1
    rw [hpow_one, e3] at h2
    exact (Nat.mul_dvd_mul_iff_right (by positivity)).mp h2
  obtain ⟨b', rfl⟩ := hbeven
  have hodd : Odd (1 + 2 ^ (a - 2)) :=
    (Nat.even_pow.mpr ⟨even_two, by omega⟩).one_add
  have hcop : Nat.Coprime (1 + 2 ^ (a - 2)) (2 ^ (a - 1)) :=
    Nat.Coprime.pow_right _ hodd.coprime_two_right
  obtain ⟨c, hc⟩ : ∃ c : ℕ, 2 ^ (a - 1) ∣ c * (1 + 2 ^ (a - 2)) + b' := by
    let w : ZMod (2 ^ (a - 1)) := -(b' : ZMod (2 ^ (a - 1))) *
      ((ZMod.unitOfCoprime _ hcop)⁻¹ : (ZMod (2 ^ (a - 1)))ˣ)
    refine ⟨w.val, ?_⟩
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val,
      ← ZMod.coe_unitOfCoprime _ hcop]
    simp only [w]
    rw [mul_assoc, Units.inv_mul, mul_one, neg_add_cancel]
  have key : ∀ g y : G, (g * y) ^ 2 = g * (y * g * y⁻¹) * y ^ 2 := fun g y => by
    rw [pow_two, pow_two]
    group
  have hy2 : (h ^ c * x) ^ 2 = 1 := by
    have e1 : (h ^ c * x) ^ 2 = h ^ (c + (1 + 2 ^ (a - 1)) * c + 2 * b') := by
      rw [pow_two, pow_add, pow_add, ← hconjpow c, hb, pow_two]
      group
    rw [e1, hpow_one]
    have e2 : c + (1 + 2 ^ (a - 1)) * c + 2 * b' = 2 * (c * (1 + 2 ^ (a - 2)) + b') := by
      rw [e4]
      ring
    rw [e2, e3]
    exact mul_dvd_mul_left 2 hc
  refine ⟨c, hy2, ?_, ?_⟩
  · intro g hg hg2
    obtain ⟨j, rfl⟩ := hpow g hg
    have hyc : (h ^ c * x) * h ^ j * (h ^ c * x)⁻¹ = h ^ ((1 + 2 ^ (a - 1)) * j) := by
      rw [show h ^ c * x * h ^ j * (h ^ c * x)⁻¹ = h ^ c * (x * h ^ j * x⁻¹) * (h ^ c)⁻¹ by
        group, hconjpow]
      group
    have e1 : (h ^ j * (h ^ c * x)) ^ 2 = h ^ (j + (1 + 2 ^ (a - 1)) * j) := by
      rw [key, hyc, hy2, mul_one, pow_add]
    rw [e1, hpow_one] at hg2
    have e2 : j + (1 + 2 ^ (a - 1)) * j = 2 * (j * (1 + 2 ^ (a - 2))) := by
      rw [e4]
      ring
    rw [e2, e3] at hg2
    have h3 : 2 ^ (a - 1) ∣ j * (1 + 2 ^ (a - 2)) :=
      (Nat.mul_dvd_mul_iff_left (by norm_num)).mp hg2
    exact pow_eq_one_or_of_two_pow_dvd (by omega) hh (hcop.symm.dvd_of_dvd_mul_right h3)
  · intro g hg hg2
    obtain ⟨j, rfl⟩ := hpow g hg
    rw [← pow_mul, hpow_one, e3, mul_comm j 2] at hg2
    exact pow_eq_one_or_of_two_pow_dvd (by omega) hh
      ((Nat.mul_dvd_mul_iff_left (by norm_num)).mp hg2)

theorem inv_conj_pow {G : Type*} [Group G] (x b : G) (i : ℕ) :
    (x⁻¹ * b * x) ^ i = x⁻¹ * b ^ i * x := by
  simpa using conj_pow (a := x⁻¹) (b := b) (i := i)

theorem unipotent_cyclic_extension_involution_hull {L : Type*} [Group L] [Finite L] {a : ℕ}
    (ha : 3 ≤ a) (h : L) (hh : orderOf h = 2 ^ a) (hindex : (Subgroup.zpowers h).index = 2)
    (x : L) (hx : x ∉ Subgroup.zpowers h) (hconj : x⁻¹ * h * x = h ^ (1 + 2 ^ (a - 1))) :
    ∃ y : L, (∃ c : ℕ, y = h ^ c * x) ∧ y ^ 2 = 1 ∧
      (∀ g : L, (g ^ 2 = 1 ∧ g ≠ 1) ↔
        (g = h ^ 2 ^ (a - 1) ∨ g = y ∨ g = h ^ 2 ^ (a - 1) * y)) ∧
      (Subgroup.closure {h ^ 2 ^ (a - 1), y}).Characteristic ∧
      IsMulCommutative (Subgroup.closure {h ^ 2 ^ (a - 1), y}) ∧
      (∀ v ∈ Subgroup.closure {h ^ 2 ^ (a - 1), y}, v ^ 2 = 1) ∧
      Nat.card (Subgroup.closure {h ^ 2 ^ (a - 1), y}) = 4 := by
  classical
  set H := Subgroup.zpowers h with hH
  have hHn : H.Normal := Subgroup.normal_of_index_eq_two hindex
  have hx2 : x ^ 2 ∈ H := by
    rw [pow_two]
    exact Subgroup.mul_self_mem_of_index_two hindex x
  have hfwd : x * h * x⁻¹ = h ^ (1 + 2 ^ (a - 1)) := by
    have hsq : (1 + 2 ^ (a - 1)) * (1 + 2 ^ (a - 1)) = 1 + 2 ^ a * (1 + 2 ^ (a - 2)) := by
      obtain ⟨b, rfl⟩ : ∃ b, a = b + 2 := ⟨a - 2, by omega⟩
      rw [show b + 2 - 1 = b + 1 by omega, show b + 2 - 2 = b by omega]
      ring
    have h1 : x⁻¹ * h ^ (1 + 2 ^ (a - 1)) * x = h := by
      rw [← inv_conj_pow, hconj, ← pow_mul, hsq, pow_add, pow_one, pow_mul, ← hh,
        pow_orderOf_eq_one, one_pow, mul_one]
    calc x * h * x⁻¹ = x * (x⁻¹ * h ^ (1 + 2 ^ (a - 1)) * x) * x⁻¹ := by rw [h1]
      _ = h ^ (1 + 2 ^ (a - 1)) := by group
  obtain ⟨c, hy2, hout, hin⟩ := unipotent_extension_involutions ha hh hx2 hfwd
  set z := h ^ 2 ^ (a - 1) with hz
  set y := h ^ c * x with hy
  have hzH : z ∈ H := H.pow_mem (Subgroup.mem_zpowers h) _
  have hyH : y ∉ H := fun hmem => hx (by
    have e : x = (h ^ c)⁻¹ * y := by rw [hy, inv_mul_cancel_left]
    rw [e]
    exact H.mul_mem (H.inv_mem (H.pow_mem (Subgroup.mem_zpowers h) c)) hmem)
  have hz1 : z ≠ 1 := pow_ne_one_of_lt_orderOf (pow_ne_zero _ two_ne_zero)
    (by rw [hh]; exact Nat.pow_lt_pow_right (by norm_num) (by omega))
  have hz2 : z ^ 2 = 1 := by
    rw [hz, ← pow_mul, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ a), ← hh,
      pow_orderOf_eq_one]
  have hy1 : y ≠ 1 := fun h1 => hyH (h1 ▸ H.one_mem)
  have hyz : y * z * y⁻¹ = z := by
    have hmem : y * z * y⁻¹ ∈ H := hHn.conj_mem z hzH y
    have hsq : (y * z * y⁻¹) ^ 2 = 1 := by rw [conj_pow, hz2]; group
    rcases hin _ hmem hsq with h1 | h1
    · exfalso
      apply hz1
      calc z = y⁻¹ * (y * z * y⁻¹) * y := by group
        _ = 1 := by rw [h1]; group
    · exact h1
  have hcomm : z * y = y * z := by
    calc z * y = (y * z * y⁻¹) * y := by rw [hyz]
      _ = y * z := by group
  have hzy2 : (z * y) ^ 2 = 1 := by
    calc (z * y) ^ 2 = z * (y * z) * y := by rw [pow_two]; group
      _ = z * (z * y) * y := by rw [hcomm]
      _ = z ^ 2 * y ^ 2 := by rw [pow_two, pow_two]; group
      _ = 1 := by rw [hz2, hy2, one_mul]
  have hzyH : z * y ∉ H := fun hmem => hyH (by
    have e : y = z⁻¹ * (z * y) := by group
    rw [e]
    exact H.mul_mem (H.inv_mem hzH) hmem)
  have hzy1 : z * y ≠ 1 := fun h1 => hzyH (h1 ▸ H.one_mem)
  have hclass : ∀ g : L, (g ^ 2 = 1 ∧ g ≠ 1) ↔ (g = z ∨ g = y ∨ g = z * y) := by
    intro g
    constructor
    · rintro ⟨hg2, hg1⟩
      by_cases hgH : g ∈ H
      · rcases hin g hgH hg2 with h1 | h1
        · exact absurd h1 hg1
        · exact Or.inl h1
      · have hgy : g * y⁻¹ ∈ H := by
          rw [Subgroup.mul_mem_iff_of_index_two hindex]
          exact iff_of_false hgH (fun hmem => hyH (by simpa using H.inv_mem hmem))
        have hg' : (g * y⁻¹ * y) ^ 2 = 1 := by rw [inv_mul_cancel_right]; exact hg2
        have e : g = g * y⁻¹ * y := by group
        rcases hout _ hgy hg' with h1 | h1
        · right; left
          rw [e, h1, one_mul]
        · right; right
          rw [e, h1]
    · rintro (rfl | rfl | rfl)
      · exact ⟨hz2, hz1⟩
      · exact ⟨hy2, hy1⟩
      · exact ⟨hzy2, hzy1⟩
  set V := Subgroup.closure ({z, y} : Set L) with hV
  have hzV : z ∈ V := Subgroup.subset_closure (by simp)
  have hyV : y ∈ V := Subgroup.subset_closure (by simp)
  have hVcomm : IsMulCommutative V := by
    rw [← Subgroup.le_centralizer_iff_isMulCommutative, hV, Subgroup.centralizer_closure,
      Subgroup.closure_le]
    intro g hg
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro k hk
    rcases hg with rfl | rfl <;> rcases hk with rfl | rfl
    · rfl
    · exact hcomm.symm
    · exact hcomm
    · rfl
  have hVexp : ∀ v ∈ V, v ^ 2 = 1 := by
    intro v hv
    induction hv using Subgroup.closure_induction with
    | mem g hg =>
      rcases hg with rfl | rfl
      · exact hz2
      · exact hy2
    | one => exact one_pow 2
    | mul g k hg hk ihg ihk =>
      have hgk : Commute g k := setLike_mul_comm (s := V) hg hk
      rw [hgk.mul_pow, ihg, ihk, one_mul]
    | inv g hg ihg => rw [inv_pow, ihg, inv_one]
  have hVset : (V : Set L) = ↑({1, z, y, z * y} : Finset L) := by
    ext g
    simp only [SetLike.mem_coe, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    constructor
    · intro hg
      by_cases hg1 : g = 1
      · exact Or.inl hg1
      · exact Or.inr ((hclass g).mp ⟨hVexp g hg, hg1⟩)
    · rintro (rfl | rfl | rfl | rfl)
      · exact V.one_mem
      · exact hzV
      · exact hyV
      · exact V.mul_mem hzV hyV
  have hzy : z ≠ y := fun e => hyH (e ▸ hzH)
  have hVcard : Nat.card V = 4 := by
    rw [show Nat.card V = Nat.card (V : Set L) from rfl, hVset, Nat.card_coe_set_eq,
      Set.ncard_coe_finset]
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair]
    · intro e
      apply hz1
      calc z = z * y * y⁻¹ := by group
        _ = 1 := by rw [← e]; group
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hzy, fun e => hy1 (by
        calc y = z⁻¹ * (z * y) := by group
          _ = 1 := by rw [← e]; group)⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm hz1, Ne.symm hy1, Ne.symm hzy1⟩
  have hVinv : V = Subgroup.closure {g : L | g ^ 2 = 1} := by
    apply le_antisymm
    · apply Subgroup.closure_mono
      rintro g (rfl | rfl)
      · exact hz2
      · exact hy2
    · rw [Subgroup.closure_le]
      intro g hg
      by_cases hg1 : g = 1
      · rw [hg1]
        exact V.one_mem
      · rcases (hclass g).mp ⟨hg, hg1⟩ with rfl | rfl | rfl
        · exact hzV
        · exact hyV
        · exact V.mul_mem hzV hyV
  have hchar : V.Characteristic := by
    rw [Subgroup.characteristic_iff_map_eq]
    intro φ
    rw [hVinv, MonoidHom.map_closure]
    congr 1
    ext g
    simp only [Set.mem_image, Set.mem_ofPred_eq, MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨k, hk, rfl⟩
      rw [← map_pow, hk, map_one]
    · intro hg
      refine ⟨φ.symm g, ?_, by simp⟩
      rw [← map_pow, hg, map_one]
  exact ⟨y, ⟨c, rfl⟩, hy2, hclass, hchar, hVcomm, hVexp, hVcard⟩

theorem closure_normal_of_conj_mem {G : Type*} [Group G] {s : Set G}
    (hs : ∀ g : G, ∀ x ∈ s, g * x * g⁻¹ ∈ Subgroup.closure s) : (Subgroup.closure s).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have hle : (Subgroup.closure s).map (MulAut.conj g).toMonoidHom ≤ Subgroup.closure s := by
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨x, hx, rfl⟩
    exact hs g x hx
  exact hle ⟨n, hn, rfl⟩

theorem cyclic_abelian_normal_index_two {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hcyc : ∀ A : Subgroup P, A.Normal → IsMulCommutative A → IsCyclic A) :
    ∃ H : Subgroup P, H.Normal ∧ IsCyclic H ∧ H.index ≤ 2 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (Subgroup P) :=
    Finite.of_injective (fun H : Subgroup P => (H : Set P)) SetLike.coe_injective
  obtain ⟨H, -, hHmax⟩ := (Set.toFinite {A : Subgroup P | A.Normal ∧ IsMulCommutative A}).exists_le_maximal
    (a := Subgroup.center P) ⟨inferInstance, inferInstance⟩
  obtain ⟨hHn, hHab⟩ := hHmax.1
  have hHcyc : IsCyclic H := hcyc H hHn hHab
  refine ⟨H, hHn, hHcyc, ?_⟩
  have hcent : Subgroup.centralizer (H : Set P) = H :=
    Helpers.maximal_abelian_normal_selfCentralizing Nat.prime_two hP H hHab
      (fun L hL hLab hHL => hHmax.2 ⟨hL, hLab⟩ hHL)
  by_contra hidx
  push Not at hidx
  let φ : P →* MulAut H := MulAut.conjNormal
  have hker : φ.ker = H := (Helpers.conjNormal_ker_eq_centralizer H).trans hcent
  have hΓ : 2 < Nat.card φ.range := by
    rw [← Subgroup.index_ker, hker]
    exact hidx
  obtain ⟨h₀, hh₀⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top H).mp hHcyc
  have hh₀H : h₀ ∈ H := hh₀ ▸ Subgroup.mem_zpowers h₀
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp (hP.to_subgroup H)
  have hord : orderOf h₀ = 2 ^ a := by rw [← Nat.card_zpowers, hh₀, ha]
  let hH : H := ⟨h₀, hh₀H⟩
  have hordH : orderOf hH = 2 ^ a := by rw [Subgroup.orderOf_mk]; exact hord
  have hgen : Subgroup.zpowers hH = ⊤ := by
    rw [← Subgroup.card_eq_iff_eq_top, Nat.card_zpowers, hordH, ha]
  have ha3 : 3 ≤ a := by
    by_contra hlt
    push Not at hlt
    have : Finite (MulAut H) :=
      Finite.of_injective (fun σ : MulAut H => (σ : H → H)) (fun σ τ hστ => MulEquiv.ext
        (congrFun hστ))
    have h1 : Nat.card φ.range ≤ Nat.card (MulAut H) := Subgroup.card_le_card_group _
    rw [IsCyclic.card_mulAut, ha] at h1
    rcases Nat.eq_zero_or_pos a with h0 | hpos
    · subst h0
      rw [pow_zero, Nat.totient_one] at h1
      omega
    · rw [Nat.totient_prime_pow Nat.prime_two hpos, show (2 : ℕ) - 1 = 1 from rfl,
        mul_one] at h1
      have : 2 ^ (a - 1) ≤ 2 := by
        calc 2 ^ (a - 1) ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
          _ = 2 := by norm_num
      omega
  obtain ⟨σ, hσΓ, hσh, hσord⟩ :=
    cyclic_two_large_automorphism_subgroup ha3 hH hgen hordH φ.range hΓ
  obtain ⟨g, rfl⟩ := hσΓ
  have hgh : g * h₀ * g⁻¹ = h₀ ^ (1 + 2 ^ (a - 1)) := by
    have := congrArg Subtype.val hσh
    simpa [φ, MulAut.conjNormal_apply, hH] using this
  have hgH : g ∉ H := by
    intro hg
    have h1 : φ g = 1 := by
      rw [← MonoidHom.mem_ker, hker]
      exact hg
    rw [h1, orderOf_one] at hσord
    norm_num at hσord
  have hg2 : g ^ 2 ∈ H := by
    rw [← hker, MonoidHom.mem_ker, map_pow, ← hσord, pow_orderOf_eq_one]
  have hHz : ∀ k ∈ H, k ∈ Subgroup.zpowers h₀ := fun k hk => hh₀ ▸ hk
  obtain ⟨c, hy2, hout, hin⟩ := unipotent_extension_involutions ha3 hord (hHz _ hg2) hgh
  set z := h₀ ^ 2 ^ (a - 1) with hz
  set y := h₀ ^ c * g with hy
  have hzH : z ∈ H := H.pow_mem hh₀H _
  have hyH : y ∉ H := fun hmem => hgH (by
    have e : g = (h₀ ^ c)⁻¹ * y := by rw [hy, inv_mul_cancel_left]
    rw [e]
    exact H.mul_mem (H.inv_mem (H.pow_mem hh₀H c)) hmem)
  have hz1 : z ≠ 1 := pow_ne_one_of_lt_orderOf (pow_ne_zero _ two_ne_zero)
    (by rw [hord]; exact Nat.pow_lt_pow_right (by norm_num) (by omega))
  have hz2 : z ^ 2 = 1 := by
    rw [hz, ← pow_mul, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ a), ← hord,
      pow_orderOf_eq_one]
  have hconjz : ∀ p : P, p * z * p⁻¹ = z := by
    intro p
    have hmem : p * z * p⁻¹ ∈ H := hHn.conj_mem z hzH p
    have hsq : (p * z * p⁻¹) ^ 2 = 1 := by rw [conj_pow, hz2]; group
    rcases hin _ (hHz _ hmem) hsq with h1 | h1
    · exfalso
      apply hz1
      calc z = p⁻¹ * (p * z * p⁻¹) * p := by group
        _ = 1 := by rw [h1]; group
    · exact h1
  have hcommAut : ∀ p q : P, p * q * p⁻¹ * q⁻¹ ∈ H := by
    intro p q
    rw [← hker, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv,
      mulAut_mul_comm_of_isCyclic (φ p) (φ q)]
    group
  have hconjy : ∀ p : P, p * y * p⁻¹ = y ∨ p * y * p⁻¹ = z * y := by
    intro p
    obtain ⟨w, hw⟩ : ∃ w, w = p * y * p⁻¹ * y⁻¹ := ⟨_, rfl⟩
    have hwH : w ∈ H := by
      have e : w = (p * h₀ ^ c * p⁻¹) * (p * g * p⁻¹ * g⁻¹) * (h₀ ^ c)⁻¹ := by
        rw [hw, hy]
        group
      rw [e]
      exact H.mul_mem (H.mul_mem (hHn.conj_mem _ (H.pow_mem hh₀H c) p) (hcommAut p g))
        (H.inv_mem (H.pow_mem hh₀H c))
    have e2 : p * y * p⁻¹ = w * y := by rw [hw, inv_mul_cancel_right]
    have hsq : (w * y) ^ 2 = 1 := by
      rw [← e2, conj_pow, hy2]
      group
    rcases hout w (hHz w hwH) hsq with h1 | h1
    · left
      rw [e2, h1, one_mul]
    · right
      rw [e2, h1]
  have hzc : ∀ q : P, q * z = z * q := fun q => by
    calc q * z = q * z * q⁻¹ * q := by group
      _ = z * q := by rw [hconjz]
  set V := Subgroup.closure ({z, y} : Set P) with hV
  have hzV : z ∈ V := Subgroup.subset_closure (by simp)
  have hyV : y ∈ V := Subgroup.subset_closure (by simp)
  have hVn : V.Normal := by
    apply closure_normal_of_conj_mem
    intro p k hk
    rcases hk with rfl | rfl
    · rw [hconjz]
      exact hzV
    · rcases hconjy p with h1 | h1 <;> rw [h1]
      · exact hyV
      · exact V.mul_mem hzV hyV
  have hVab : IsMulCommutative V := by
    rw [← Subgroup.le_centralizer_iff_isMulCommutative, hV, Subgroup.centralizer_closure,
      Subgroup.closure_le]
    intro k hk
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro l hl
    rcases hk with rfl | rfl
    · exact hzc l
    · rcases hl with rfl | rfl
      · exact (hzc y).symm
      · rfl
  have hVcyc : IsCyclic V := hcyc V hVn hVab
  have heq := eq_of_sq_eq_one_of_isCyclic (G := V) (a := ⟨z, hzV⟩) (b := ⟨y, hyV⟩)
    (Subtype.ext (by simpa using hz2)) (fun h1 => hz1 (congrArg Subtype.val h1))
    (Subtype.ext (by simpa using hy2))
    (fun h1 => hyH (by
      have e : y = 1 := congrArg Subtype.val h1
      rw [e]
      exact H.one_mem))
  have e : z = y := congrArg Subtype.val heq
  exact hyH (e ▸ hzH)

end CFSG.RankTwoShapes
