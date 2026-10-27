module

public import CFSG.GH74.GLS.SP.GlueT3
public import TauCeti.GroupTheory.SpecificGroups.Dihedral.Basic

public section

namespace CFSG.GH74.GLS.SP

open CFSG.GH74.BNPair
open scoped Pointwise

variable {X : Type*} [Group X]

theorem rot_pos_aux {n : ℕ} (_hn : 3 ≤ n) {k : ℤ} (hk0 : 0 ≤ k) (hkn : k < n)
    (h1 : 1 ≤ Rt n (2 * k) ∧ Rt n (2 * k) ≤ n)
    (h2 : 1 ≤ Rt n (n - 1 + 2 * k) ∧ Rt n (n - 1 + 2 * k) ≤ n) : k = 0 := by
  by_contra hk
  rcases lt_or_ge (2 * k) n with h | h
  · have : Rt n (n - 1 + 2 * k) = -((n - 1 + 2 * k) - n + 1) := Rt_of_ge (by omega) (by omega)
    omega
  · have : Rt n (2 * k) = -(2 * k - n + 1) := Rt_of_ge h (by omega)
    omega

theorem refl_pos_aux {n : ℕ} (hn : 3 ≤ n) {k : ℤ} (hk0 : 0 ≤ k) (hkn : k < n)
    (h1 : 1 ≤ Rt n (n - 2 * k) ∧ Rt n (n - 2 * k) ≤ n)
    (h2 : 1 ≤ Rt n (1 - 2 * k) ∧ Rt n (1 - 2 * k) ≤ n) : False := by
  rcases eq_or_lt_of_le hk0 with h | h
  · subst h
    have : Rt n (n - 2 * 0) = -1 := by
      rw [show (n : ℤ) - 2 * 0 = n by ring]
      exact Rt_self (by omega)
    omega
  · rcases le_or_gt (-(n : ℤ)) (1 - 2 * k) with hh | hh
    · have : Rt n (1 - 2 * k) = -((1 - 2 * k) + n + 1) := Rt_of_neg hh (by omega)
      omega
    · have : Rt n (n - 2 * k) = -((n - 2 * k) + n + 1) := Rt_of_neg (by omega) (by omega)
      omega

theorem Rt_add_two_mul_mod {n : ℕ} (a k : ℤ) :
    Rt n (a + 2 * k) = Rt n (a + 2 * (k % (n : ℤ))) := by
  have e := Int.emod_add_mul_ediv k (n : ℤ)
  conv_lhs => rw [← e]
  rw [show a + 2 * (k % (n : ℤ) + (n : ℤ) * (k / (n : ℤ))) =
    (a + 2 * (k % (n : ℤ))) + 2 * (n : ℤ) * (k / (n : ℤ)) by ring, Rt_add_mul]

theorem rot_pos {n : ℕ} (hn : 3 ≤ n) {k : ℤ} (h1 : 1 ≤ Rt n (0 + 2 * k) ∧ Rt n (0 + 2 * k) ≤ n)
    (h2 : 1 ≤ Rt n ((n : ℤ) - 1 + 2 * k) ∧ Rt n ((n : ℤ) - 1 + 2 * k) ≤ n) : k % (n : ℤ) = 0 := by
  rw [Rt_add_two_mul_mod, zero_add] at h1
  rw [Rt_add_two_mul_mod] at h2
  exact rot_pos_aux hn (Int.emod_nonneg k (by omega)) (Int.emod_lt_of_pos k (by omega)) h1 h2

theorem Rt_sub_two_mul_mod {n : ℕ} (a k : ℤ) :
    Rt n (a - 2 * k) = Rt n (a - 2 * (k % (n : ℤ))) := by
  have e := Int.emod_add_mul_ediv k (n : ℤ)
  conv_lhs => rw [← e]
  rw [show a - 2 * (k % (n : ℤ) + (n : ℤ) * (k / (n : ℤ))) =
    (a - 2 * (k % (n : ℤ))) + 2 * (n : ℤ) * (-(k / (n : ℤ))) by ring, Rt_add_mul]

theorem refl_pos {n : ℕ} (hn : 3 ≤ n) {k : ℤ}
    (h1 : 1 ≤ Rt n ((n : ℤ) - 2 * k) ∧ Rt n ((n : ℤ) - 2 * k) ≤ n)
    (h2 : 1 ≤ Rt n (1 - 2 * k) ∧ Rt n (1 - 2 * k) ≤ n) : False := by
  rw [Rt_sub_two_mul_mod] at h1 h2
  exact refl_pos_aux hn (Int.emod_nonneg k (by omega)) (Int.emod_lt_of_pos k (by omega)) h1 h2

theorem ActsPos.congr {n : ℕ} {root : ℤ → Subgroup X} {m : X} {f g : ℤ → ℤ}
    (h : ActsPos n root m f) (hfg : ∀ q, f q = g q) : ActsPos n root m g := by
  intro q x hx
  rw [← hfg q]
  exact h q x hx

namespace RGD2

variable {n : ℕ} {H : Subgroup X} {r₁ r₂ : X} {U : Subgroup X} {root : ℤ → Subgroup X}
  (R : RGD2 n H r₁ r₂ U root)

include R in
theorem B_le_normalizer_U : H ⊔ U ≤ Subgroup.normalizer (U : Set X) :=
  sup_le R.H_le_normalizer_U Subgroup.le_normalizer

include R in
theorem pos_of_mem_B {m : X} (hmB : m ∈ H ⊔ U) {f : ℤ → ℤ} (hf : ActsPos n root m f) {p : ℤ}
    (hp : 1 ≤ Rt n p ∧ Rt n p ≤ n) : 1 ≤ Rt n (f p) ∧ Rt n (f p) ≤ n := by
  have hn : 0 < n := by have := R.three_le; omega
  have hne := R.ne_bot (Rt n p) (Rt_isRoot hn p)
  obtain ⟨⟨y, hy⟩, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  have hy1' : y ≠ 1 := fun h => hy1 (Subtype.ext h)
  have hyU : y ∈ U := R.root_le_U hp.1 hp.2 hy
  have hmU : m * y * m⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.1 (R.B_le_normalizer_U hmB) y).1 hyU
  have hmy := hf p y hy
  by_contra hcon
  have hk := Rt_isRoot hn (f p)
  have hneg : Rt n (f p) ≤ -1 := by
    have h1 := hk.1
    have h2 := hk.2
    omega
  have hyneg : m * y * m⁻¹ ∈ negGen n root := by
    refine mem_negGen_of_mem (k := -Rt n (f p)) (by omega) (by have := hk.2; omega) ?_
    rw [neg_neg]
    exact hmy
  have := R.meet_one _ ((le_sup_right : U ≤ H ⊔ U) hmU) hyneg
  apply hy1'
  have h3 := congrArg (fun z => m⁻¹ * z * m) this
  simpa [mul_assoc] using h3

include R in
theorem actsPos_pow (k : ℕ) :
    ActsPos n root ((r₁ * r₂) ^ k) (fun q => q + 2 * (k : ℤ)) := by
  induction k with
  | zero => simpa using (ActsPos.one : ActsPos n root (1 : X) (fun q => q))
  | succ k ih =>
    have h := (R.actsPos_r₁.mul R.actsPos_r₂).mul ih
    rw [pow_succ']
    refine h.congr (fun q => ?_)
    push_cast
    ring

include R in
theorem normal_H_subgroupOf : (H.subgroupOf R.N).Normal := by
  rw [Subgroup.normal_subgroupOf_iff R.H_le_N]
  intro h m hh hm
  exact (R.N_normalizes_H hm h hh).1

include R in
theorem r₁_not_mem_B : r₁ ∉ H ⊔ U := by
  intro hB
  have hn : 0 < n := by have := R.three_le; omega
  have h := R.pos_of_mem_B hB R.actsPos_r₁ (p := 0)
    ⟨by rw [Rt_zero hn], by rw [Rt_zero hn]; omega⟩
  simp only [sub_zero] at h
  rw [Rt_self hn] at h
  omega

include R in
theorem r₂_not_mem_B : r₂ ∉ H ⊔ U := by
  intro hB
  have hn : 0 < n := by have := R.three_le; omega
  have h := R.pos_of_mem_B hB R.actsPos_r₂ (p := (n : ℤ) - 1)
    ⟨by rw [Rt_pred hn]; omega, by rw [Rt_pred hn]⟩
  have e : (n : ℤ) - 2 - ((n : ℤ) - 1) = -1 := by ring
  simp only [e] at h
  rw [Rt_of_neg (by omega) (by omega)] at h
  omega

include R in
theorem normal_form_and_card :
    (∀ x : X, x ∈ R.N →
      ∃ k : ℕ, ∃ h ∈ H, x = (r₁ * r₂) ^ k * h ∨ x = r₁ * (r₁ * r₂) ^ k * h) ∧
    Nat.card (R.N ⧸ H.subgroupOf R.N) = 2 * n := by
  have := R.normal_H_subgroupOf
  have h3 := R.three_le
  have hn : 0 < n := by omega
  have : NeZero n := ⟨by omega⟩
  set a₁ : R.N := ⟨r₁, R.r₁_mem_N⟩ with ha₁
  set a₂ : R.N := ⟨r₂, R.r₂_mem_N⟩ with ha₂
  set s : R.N ⧸ H.subgroupOf R.N := (a₁ : R.N ⧸ H.subgroupOf R.N) with hsd
  set t : R.N ⧸ H.subgroupOf R.N := (a₂ : R.N ⧸ H.subgroupOf R.N) with htd
  have hmk : ∀ m : ℕ, (s * t) ^ m = (((a₁ * a₂) ^ m : R.N) : R.N ⧸ H.subgroupOf R.N) := by
    intro m
    rw [QuotientGroup.mk_pow, QuotientGroup.mk_mul]
  have hpow : ∀ m : ℕ, (s * t) ^ m = 1 ↔ (r₁ * r₂) ^ m ∈ H := by
    intro m
    rw [hmk m, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact Iff.rfl
  have hs : s * s = 1 := by
    rw [hsd, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact R.sq₁
  have ht : t * t = 1 := by
    rw [htd, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact R.sq₂
  have hs1 : s ≠ 1 := by
    intro h
    exact R.r₁_not_mem_B ((le_sup_left : H ≤ H ⊔ U)
      (Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff a₁).1 h)))
  have ht1 : t ≠ 1 := by
    intro h
    exact R.r₂_not_mem_B ((le_sup_left : H ≤ H ⊔ U)
      (Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff a₂).1 h)))
  have hord : orderOf (s * t) = n := by
    rw [orderOf_eq_iff hn]
    refine ⟨(hpow n).2 R.pow, fun m hmn hm0 hone => ?_⟩
    have hmH := (hpow m).1 hone
    have hB : (r₁ * r₂) ^ m ∈ H ⊔ U := (le_sup_left : H ≤ H ⊔ U) hmH
    have h1 := R.pos_of_mem_B hB (R.actsPos_pow m) (p := 0)
      ⟨by rw [Rt_zero hn], by rw [Rt_zero hn]; omega⟩
    have h2 := R.pos_of_mem_B hB (R.actsPos_pow m) (p := (n : ℤ) - 1)
      ⟨by rw [Rt_pred hn]; omega, by rw [Rt_pred hn]⟩
    have h4 := rot_pos h3 h1 h2
    have h5 : (m : ℤ) % n = m := Int.emod_eq_of_lt (by omega) (by omega)
    omega
  have hgen : Subgroup.closure ({s, t} : Set (R.N ⧸ H.subgroupOf R.N)) = ⊤ := by
    set K := Subgroup.closure ({s, t} : Set (R.N ⧸ H.subgroupOf R.N)) with hK
    have hle : R.N ≤ (K.comap (QuotientGroup.mk' (H.subgroupOf R.N))).map R.N.subtype := by
      refine (Subgroup.closure_le _).2 ?_
      rintro z (hz | hz)
      · have hzN : z ∈ R.N := R.H_le_N hz
        refine ⟨⟨z, hzN⟩, ?_, rfl⟩
        have : (QuotientGroup.mk' (H.subgroupOf R.N)) ⟨z, hzN⟩ = 1 := by
          rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
          exact hz
        show (QuotientGroup.mk' (H.subgroupOf R.N)) ⟨z, hzN⟩ ∈ K
        rw [this]
        exact K.one_mem
      · rcases hz with rfl | rfl
        · exact ⟨a₁, Subgroup.subset_closure (Or.inl rfl), rfl⟩
        · exact ⟨a₂, Subgroup.subset_closure (Or.inr rfl), rfl⟩
    rw [eq_top_iff]
    intro q _
    induction q using QuotientGroup.induction_on with
    | H z =>
      obtain ⟨w, hw, hwz⟩ := hle z.2
      have : w = z := Subtype.ext hwz
      subst this
      exact hw
  have hbij := TauCeti.dihedralHom_bijective hs ht hs1 ht1 hord hgen
  refine ⟨fun x hx => ?_, ?_⟩
  · obtain ⟨d, hd⟩ := hbij.2 (⟨x, hx⟩ : R.N)
    cases d with
    | r i =>
      rw [TauCeti.dihedralHom_r, ZMod.cast_eq_val, zpow_natCast, hmk] at hd
      have h1 : ((r₁ * r₂) ^ i.val)⁻¹ * x ∈ H :=
        Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 hd)
      exact ⟨i.val, ((r₁ * r₂) ^ i.val)⁻¹ * x, h1, Or.inl (by group)⟩
    | sr i =>
      rw [TauCeti.dihedralHom_sr, ZMod.cast_eq_val, zpow_natCast, hmk,
        ← QuotientGroup.mk_mul] at hd
      have h1 : (r₁ * (r₁ * r₂) ^ i.val)⁻¹ * x ∈ H :=
        Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 hd)
      exact ⟨i.val, (r₁ * (r₁ * r₂) ^ i.val)⁻¹ * x, h1, Or.inr (by group)⟩
  · rw [← Nat.card_congr (Equiv.ofBijective _ hbij), DihedralGroup.nat_card]

include R in
theorem exists_normal_form {x : X} (hx : x ∈ R.N) :
    ∃ k : ℕ, ∃ h ∈ H, x = (r₁ * r₂) ^ k * h ∨ x = r₁ * (r₁ * r₂) ^ k * h :=
  R.normal_form_and_card.1 x hx

include R in
theorem card_quotient : Nat.card (R.N ⧸ H.subgroupOf R.N) = 2 * n :=
  R.normal_form_and_card.2

include R in
theorem B_inf_N : (H ⊔ U) ⊓ R.N = H := by
  refine le_antisymm ?_ (le_inf le_sup_left R.H_le_N)
  rintro x ⟨hxB, hxN⟩
  have h3 := R.three_le
  have hn : 0 < n := by omega
  obtain ⟨k, h, hh, hxe⟩ := R.exists_normal_form hxN
  have hhB : h ∈ H ⊔ U := (le_sup_left : H ≤ H ⊔ U) hh
  rcases hxe with rfl | rfl
  · have hmB : (r₁ * r₂) ^ k ∈ H ⊔ U := by
      have := (H ⊔ U).mul_mem hxB ((H ⊔ U).inv_mem hhB)
      simpa using this
    have h1 := R.pos_of_mem_B hmB (R.actsPos_pow k) (p := 0)
      ⟨by rw [Rt_zero hn], by rw [Rt_zero hn]; omega⟩
    have h2 := R.pos_of_mem_B hmB (R.actsPos_pow k) (p := (n : ℤ) - 1)
      ⟨by rw [Rt_pred hn]; omega, by rw [Rt_pred hn]⟩
    have hk := rot_pos h3 h1 h2
    have hdvd : (n : ℤ) ∣ (k : ℤ) := Int.dvd_of_emod_eq_zero hk
    obtain ⟨j, rfl⟩ : n ∣ k := Int.natCast_dvd_natCast.1 hdvd
    have : (r₁ * r₂) ^ (n * j) ∈ H := by
      rw [pow_mul]
      exact H.pow_mem R.pow j
    exact H.mul_mem this hh
  · have hmB : r₁ * (r₁ * r₂) ^ k ∈ H ⊔ U := by
      have := (H ⊔ U).mul_mem hxB ((H ⊔ U).inv_mem hhB)
      simpa using this
    have hact := R.actsPos_r₁.mul (R.actsPos_pow k)
    have h1 := R.pos_of_mem_B hmB hact (p := 0)
      ⟨by rw [Rt_zero hn], by rw [Rt_zero hn]; omega⟩
    have h2 := R.pos_of_mem_B hmB hact (p := (n : ℤ) - 1)
      ⟨by rw [Rt_pred hn]; omega, by rw [Rt_pred hn]⟩
    have e1 : (n : ℤ) - (0 + 2 * (k : ℤ)) = (n : ℤ) - 2 * (k : ℤ) := by ring
    have e2 : (n : ℤ) - ((n : ℤ) - 1 + 2 * (k : ℤ)) = 1 - 2 * (k : ℤ) := by ring
    rw [e1] at h1
    rw [e2] at h2
    exact (refl_pos h3 h1 h2).elim

end RGD2

end CFSG.GH74.GLS.SP
