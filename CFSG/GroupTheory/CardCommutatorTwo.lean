module

public import CFSG.ClassicalInvolution.LBalance.Glauberman.CoprimeAction
public import CFSG.GroupTheory.SubgroupCardMul

public section

namespace CFSG.GroupTheory

open CFSG.ClassicalInvolution.GlaubermanAut

variable {A : Type*} [CommGroup A] [Finite A]

private theorem mulAut_mul_inv_comm {w x : MulAut A} (h : w * x = x * w) :
    w * x⁻¹ = x⁻¹ * w :=
  Commute.inv_right h

private theorem commutatorSubgroup_mul_le (α β : MulAut A) :
    commutatorSubgroup (α * β) ≤ commutatorSubgroup α ⊔ commutatorSubgroup β := by
  intro a ha
  obtain ⟨c, rfl⟩ := (mem_commutatorSubgroup (α * β)).mp ha
  have h : c * ((α * β) c)⁻¹ =
      (c * (β c)⁻¹) * ((β c) * (α (β c))⁻¹) := by
    rw [MulAut.mul_apply]
    group
  rw [h, mul_comm]
  exact Subgroup.mul_mem_sup (mul_inv_apply_mem_commutatorSubgroup α (β c))
    (mul_inv_apply_mem_commutatorSubgroup β c)

private theorem mem_commutatorSubgroup_conj_iff (φ ψ : MulAut A) (y : A) :
    y ∈ commutatorSubgroup (φ⁻¹ * ψ * φ) ↔ φ y ∈ commutatorSubgroup ψ := by
  constructor
  · rintro ⟨a, rfl⟩
    refine (mem_commutatorSubgroup ψ).2 ⟨φ a, ?_⟩
    have h1 : φ ((φ⁻¹ * ψ * φ) a) = ψ (φ a) := by
      simp only [MulAut.mul_apply, MulAut.apply_inv_self]
    change φ a * (ψ (φ a))⁻¹ = φ (a * ((φ⁻¹ * ψ * φ) a)⁻¹)
    rw [map_mul, map_inv, h1]
  · rintro ⟨b, hb⟩
    refine (mem_commutatorSubgroup (φ⁻¹ * ψ * φ)).2 ⟨φ⁻¹ b, ?_⟩
    have h2 : (φ⁻¹ * ψ * φ) (φ⁻¹ b) = φ⁻¹ (ψ b) := by
      simp only [MulAut.mul_apply, MulAut.apply_inv_self, MulAut.inv_apply_self]
    have hb' : b * (ψ b)⁻¹ = φ y := hb
    rw [h2, ← map_inv, ← map_mul, hb', MulAut.inv_apply_self]

private theorem isPGroup_two_of_sq_eq_one (hA : ∀ a : A, a ^ 2 = 1) : IsPGroup 2 A := by
  intro a
  have hdvd : orderOf a ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (hA a)
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact ⟨0, by simpa using orderOf_eq_one_iff.mp h⟩
  · exact ⟨1, by simpa [h] using pow_orderOf_eq_one a⟩

private theorem coprime_orderOf_of_odd (hA : ∀ a : A, a ^ 2 = 1) {x : MulAut A}
    (hxodd : Odd (orderOf x)) : Nat.Coprime (orderOf x) (Nat.card A) := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (isPGroup_two_of_sq_eq_one hA)
  rw [hk]
  exact (hxodd.coprime_two_right).pow_right k

private theorem pow_two_eq_mul_conj {x v : MulAut A} (hv2 : v * v = 1)
    (hxv : v * x * v = x⁻¹) : x ^ 2 = v * (x⁻¹ * v * x) := by
  have h1 : x * v = v * x⁻¹ := by
    calc x * v = (v * v) * (x * v) := by rw [hv2]; group
      _ = v * (v * x * v) := by group
      _ = v * x⁻¹ := by rw [hxv]
  calc x ^ 2 = x * (v * v) * x := by rw [hv2, pow_two]; group
    _ = (x * v) * (v * x) := by group
    _ = (v * x⁻¹) * (v * x) := by rw [h1]
    _ = v * (x⁻¹ * v * x) := by group

private theorem w_fixes_commutator_v {v w : MulAut A}
    (hAvw : ∀ a : A, w (a * (v a)⁻¹) = a * (v a)⁻¹) :
    ∀ a ∈ commutatorSubgroup v, w a = a := by
  intro a ha
  obtain ⟨b, rfl⟩ := (mem_commutatorSubgroup v).mp ha
  exact hAvw b

private theorem w_fixes_commutator_vx {x v w : MulAut A} (hvw : v * w = w * v)
    (hwx : w * x = x * w) (hwv : ∀ a ∈ commutatorSubgroup v, w a = a) :
    ∀ b ∈ commutatorSubgroup (x⁻¹ * v * x), w b = b := by
  intro b hb
  have hd : x b ∈ commutatorSubgroup v := (mem_commutatorSubgroup_conj_iff x v b).mp hb
  have hwd : w (x b) = x b := hwv _ hd
  have hwxinv : w * x⁻¹ = x⁻¹ * w := mulAut_mul_inv_comm hwx
  calc w b = w (x⁻¹ (x b)) := by rw [MulAut.inv_apply_self]
    _ = (w * x⁻¹) (x b) := rfl
    _ = (x⁻¹ * w) (x b) := by rw [hwxinv]
    _ = x⁻¹ (w (x b)) := rfl
    _ = b := by rw [hwd, MulAut.inv_apply_self]

private def commFix (x v : MulAut A) : Subgroup A :=
  commutatorSubgroup x ⊓ fixedSubgroup v

private theorem commutator_x_le_sup {x v : MulAut A} (hxodd : Odd (orderOf x))
    (hv2 : v * v = 1) (hxv : v * x * v = x⁻¹) :
    commutatorSubgroup x ≤ commutatorSubgroup v ⊔ commutatorSubgroup (x⁻¹ * v * x) := by
  have hxpow : ∃ m : ℕ, x = (x ^ 2) ^ m := by
    obtain ⟨m, hm⟩ := Nat.exists_mul_mod_eq_of_coprime 1 hxodd.coprime_two_left
      (orderOf_pos x).ne'
    refine ⟨m, ?_⟩
    calc x = x ^ 1 := (pow_one x).symm
      _ = x ^ (2 * m) := (pow_eq_pow_iff_modEq.mpr hm.2).symm
      _ = (x ^ 2) ^ m := by rw [pow_mul]
  obtain ⟨m, hm⟩ := hxpow
  have h1 : commutatorSubgroup x ≤ commutatorSubgroup (x ^ 2) := by
    intro d hd
    obtain ⟨a, rfl⟩ := (mem_commutatorSubgroup x).mp hd
    have hxam : x a = ((x ^ 2) ^ m) a := congrArg (fun f : MulAut A => f a) hm
    rw [hxam]
    exact mul_inv_pow_apply_mem_commutatorSubgroup (φ := x ^ 2) (i := m) a
  refine h1.trans ?_
  have h2 := commutatorSubgroup_mul_le v (x⁻¹ * v * x)
  rwa [← pow_two_eq_mul_conj hv2 hxv] at h2

private theorem commFix_relIndex_le_two (hA : ∀ a : A, a ^ 2 = 1) (F₀ : Subgroup A)
    (hF : F₀.index ≤ 2) {x v w : MulAut A} (hxodd : Odd (orderOf x)) (hv2 : v * v = 1)
    (hxv : v * x * v = x⁻¹) (hvw : v * w = w * v) (hwx : w * x = x * w)
    (hAvw : ∀ a : A, w (a * (v a)⁻¹) = a * (v a)⁻¹)
    (hF0 : ∀ a ∈ F₀, w a = a → v a = a) :
    (commFix x v).relIndex (commutatorSubgroup x) ≤ 2 := by
  have hwv := w_fixes_commutator_v hAvw
  have hwvx := w_fixes_commutator_vx hvw hwx hwv
  have hD_le := commutator_x_le_sup hxodd hv2 hxv
  have hwD : ∀ d ∈ commutatorSubgroup x, w d = d := by
    intro d hd
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp (hD_le hd)
    rw [map_mul, hwv a ha, hwvx b hb]
  have hDF : commutatorSubgroup x ⊓ F₀ ≤ commFix x v := by
    intro d hd
    rw [Subgroup.mem_inf] at hd
    exact Subgroup.mem_inf.mpr ⟨hd.1, hF0 d hd.2 (hwD d hd.1)⟩
  have hpos : F₀.relIndex ⊤ ≠ 0 := by
    have hdvd := Subgroup.relIndex_dvd_card (H := F₀) (K := (⊤ : Subgroup A))
    exact (Nat.pos_of_dvd_of_pos hdvd Nat.card_pos).ne'
  have h1 : (commFix x v).relIndex (commutatorSubgroup x) ≤
      (commutatorSubgroup x ⊓ F₀).relIndex (commutatorSubgroup x) :=
    Subgroup.relIndex_le_of_le_left hDF (by
      have hdvd := Subgroup.relIndex_dvd_card
        (H := commutatorSubgroup x ⊓ F₀) (K := commutatorSubgroup x)
      exact (Nat.pos_of_dvd_of_pos hdvd Nat.card_pos).ne')
  have h2 : (commutatorSubgroup x ⊓ F₀).relIndex (commutatorSubgroup x) ≤
      F₀.relIndex (commutatorSubgroup x) := by
    have h := Subgroup.relIndex_inf_le (H := commutatorSubgroup x) (K := F₀)
      (L := commutatorSubgroup x)
    rwa [Subgroup.relIndex_self, one_mul] at h
  have h3 : F₀.relIndex (commutatorSubgroup x) ≤ F₀.relIndex ⊤ :=
    Subgroup.relIndex_le_of_le_right (le_top : commutatorSubgroup x ≤ ⊤) hpos
  rw [Subgroup.relIndex_top_right] at h3
  exact h1.trans (h2.trans (h3.trans hF))

private theorem commFix_inf_commFix_eq_bot (hA : ∀ a : A, a ^ 2 = 1) {x v : MulAut A}
    (hxodd : Odd (orderOf x)) (hv2 : v * v = 1) (hxv : v * x * v = x⁻¹) :
    commFix x v ⊓ commFix x (x⁻¹ * v * x) = ⊥ := by
  have hcop := coprime_orderOf_of_odd hA hxodd
  have hx2 := pow_two_eq_mul_conj hv2 hxv
  have hxpow : ∃ m : ℕ, x = (x ^ 2) ^ m := by
    obtain ⟨m, hm⟩ := Nat.exists_mul_mod_eq_of_coprime 1 hxodd.coprime_two_left
      (orderOf_pos x).ne'
    refine ⟨m, ?_⟩
    calc x = x ^ 1 := (pow_one x).symm
      _ = x ^ (2 * m) := (pow_eq_pow_iff_modEq.mpr hm.2).symm
      _ = (x ^ 2) ^ m := by rw [pow_mul]
  have hD_fixed_x2 : commutatorSubgroup x ⊓ fixedSubgroup (x ^ 2) = ⊥ := by
    rw [eq_bot_iff]
    intro d hd
    rw [Subgroup.mem_inf] at hd
    have hdx : x d = d := by
      obtain ⟨m, hm⟩ := hxpow
      have hpow : ∀ m, ((x ^ 2) ^ m) d = d := by
        intro m
        induction m with
        | zero => rfl
        | succ m ih =>
          rw [pow_succ', MulAut.mul_apply, ih, hd.2]
      rw [hm]
      exact hpow m
    have hbot := fixedSubgroup_inf_commutatorSubgroup (φ := x) (n := orderOf x)
      (pow_orderOf_eq_one x) hcop
    have hmem : d ∈ fixedSubgroup x ⊓ commutatorSubgroup x := ⟨hdx, hd.1⟩
    rw [hbot] at hmem
    exact hmem
  rw [eq_bot_iff]
  intro d hd
  rw [Subgroup.mem_inf] at hd
  have hdx2 : (x ^ 2) d = d := by
    rw [hx2, MulAut.mul_apply, (mem_fixedSubgroup (x⁻¹ * v * x)).mp hd.2.2,
      (mem_fixedSubgroup v).mp hd.1.2]
  have hmem : d ∈ commutatorSubgroup x ⊓ fixedSubgroup (x ^ 2) := ⟨hd.1.1, hdx2⟩
  rw [hD_fixed_x2] at hmem
  exact hmem

private theorem card_commFix_vx (hA : ∀ a : A, a ^ 2 = 1) {x v : MulAut A}
    (hv2 : v * v = 1) (hxv : v * x * v = x⁻¹) :
    Nat.card (commFix x (x⁻¹ * v * x)) = Nat.card (commFix x v) := by
  refine (Nat.card_congr ?_).symm
  refine
    { toFun := fun d => ⟨x⁻¹ (d : A), ?_⟩
      invFun := fun d => ⟨x (d : A), ?_⟩
      left_inv := fun d => Subtype.ext (by simp)
      right_inv := fun d => Subtype.ext (by simp) }
  · obtain ⟨a, ha⟩ := (mem_commutatorSubgroup x).mp d.2.1
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [← ha]
      have := mul_inv_apply_mem_commutatorSubgroup (φ := x) (x⁻¹ a)
      simpa [MulAut.inv_apply_self] using this
    · have hdv : v (d : A) = (d : A) := d.2.2
      rw [mem_fixedSubgroup]
      calc (x⁻¹ * v * x) (x⁻¹ (d : A)) = x⁻¹ (v (x (x⁻¹ (d : A)))) := rfl
        _ = x⁻¹ (v (d : A)) := by rw [MulAut.apply_inv_self]
        _ = x⁻¹ (d : A) := by rw [hdv]
  · refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact apply_mem_commutatorSubgroup (φ := x) d.2.1
    · have hdvx : (x⁻¹ * v * x) (d : A) = (d : A) := d.2.2
      rw [mem_fixedSubgroup]
      have hvx' : v * x = x * (x⁻¹ * v * x) := by group
      calc v (x (d : A)) = (v * x) (d : A) := rfl
        _ = (x * (x⁻¹ * v * x)) (d : A) := by rw [hvx']
        _ = x ((x⁻¹ * v * x) (d : A)) := rfl
        _ = x (d : A) := by rw [hdvx]

theorem card_comm_le_four (hA : ∀ a : A, a ^ 2 = 1) (F₀ : Subgroup A) (hF : F₀.index ≤ 2)
    (x v w : MulAut A) (hxodd : Odd (orderOf x)) (hv2 : v * v = 1) (hw2 : w * w = 1)
    (hxv : v * x * v = x⁻¹) (hvw : v * w = w * v) (hwx : w * x = x * w)
    (hAvw : ∀ a : A, w (a * (v a)⁻¹) = a * (v a)⁻¹)
    (hF0 : ∀ a ∈ F₀, w a = a → v a = a) :
    Nat.card ↥(commutatorSubgroup x) ≤ 4 := by
  have hrel := commFix_relIndex_le_two hA F₀ hF hxodd hv2 hxv hvw hwx hAvw hF0
  have hinf := commFix_inf_commFix_eq_bot hA hxodd hv2 hxv
  have hcard := card_commFix_vx hA hv2 hxv
  have hlower : Nat.card (commFix x v) * Nat.card (commFix x v) ≤
      Nat.card ↥(commutatorSubgroup x) := by
    have h := CFSG.card_mul_card_le_of_inf_eq_bot (A := commutatorSubgroup x)
      (D := commFix x v) (D' := commFix x (x⁻¹ * v * x))
      inf_le_left inf_le_left hinf
    rwa [hcard] at h
  have hupper : Nat.card ↥(commutatorSubgroup x) ≤ 2 * Nat.card (commFix x v) := by
    have h := Subgroup.relIndex_mul_card (H := commFix x v) (K := commutatorSubgroup x)
    have hle : commFix x v ≤ commutatorSubgroup x := inf_le_left
    rw [inf_eq_left.mpr hle] at h
    rw [← h]
    exact Nat.mul_le_mul_right _ hrel
  have hcpos : 0 < Nat.card (commFix x v) := Nat.card_pos
  have hc_le : Nat.card (commFix x v) ≤ 2 := by
    have hc2 : Nat.card (commFix x v) * Nat.card (commFix x v) ≤
        2 * Nat.card (commFix x v) := hlower.trans hupper
    exact Nat.le_of_mul_le_mul_right hc2 hcpos
  exact hupper.trans (by simpa [mul_comm] using Nat.mul_le_mul_left 2 hc_le)

open scoped IsMulCommutative in
theorem card_le_four_mul_card_fixed {B : Type*} [Group B] [IsMulCommutative B] [Finite B]
    (hB : ∀ b : B, b ^ 2 = 1) (F₀ : Subgroup B) (hF : F₀.index ≤ 2)
    (x v w : MulAut B) (hxodd : Odd (orderOf x)) (hv2 : v * v = 1) (hw2 : w * w = 1)
    (hxv : v * x * v = x⁻¹) (hvw : v * w = w * v) (hwx : w * x = x * w)
    (hBvw : ∀ b : B, w (b * (v b)⁻¹) = b * (v b)⁻¹)
    (hF0 : ∀ b ∈ F₀, w b = b → v b = b) :
    Nat.card B ≤ 4 * Nat.card {b : B // x b = b} := by
  classical
  have hfour := card_comm_le_four (A := B) hB F₀ hF x v w hxodd hv2 hw2 hxv hvw hwx hBvw hF0
  have hfour' : Nat.card ↥((commutatorHom (φ := x)).range) ≤ 4 := hfour
  have hker : (commutatorHom (φ := x)).ker = fixedSubgroup x := by
    ext b
    rw [MonoidHom.mem_ker, mem_fixedSubgroup]
    exact mul_inv_eq_one.trans eq_comm
  have hmul := Subgroup.card_ker_mul_card_range (commutatorHom (φ := x))
  rw [hker] at hmul
  calc Nat.card B = Nat.card ↥(fixedSubgroup x) * Nat.card ↥((commutatorHom (φ := x)).range) :=
        hmul.symm
    _ ≤ Nat.card ↥(fixedSubgroup x) * 4 := Nat.mul_le_mul_left _ hfour'
    _ = 4 * Nat.card {b : B // x b = b} := by rw [mul_comm]; rfl

end CFSG.GroupTheory
