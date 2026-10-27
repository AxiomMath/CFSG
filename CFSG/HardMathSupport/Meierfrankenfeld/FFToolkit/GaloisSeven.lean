module

public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.Heisenberg
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.Bridge

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit

open Polynomial

section Poly

private theorem two_eq_zero_poly : (2 : (ZMod 2)[X]) = 0 := by
  have := CharP.cast_eq_zero ((ZMod 2)[X]) 2
  simpa using this

private theorem bezout_poly :
    X * (X ^ 3 + X + 1) + (X + 1) * (X ^ 3 + X ^ 2 + 1) = (1 : (ZMod 2)[X]) := by
  linear_combination (X ^ 4 + X ^ 3 + X ^ 2 + X) * two_eq_zero_poly

private theorem phi_poly :
    (X + 1) * ((X ^ 3 + X + 1) * (X ^ 3 + X ^ 2 + 1)) = (X ^ 7 - 1 : (ZMod 2)[X]) := by
  linear_combination (X ^ 6 + X ^ 5 + 2 * X ^ 4 + 2 * X ^ 3 + X ^ 2 + X + 1) * two_eq_zero_poly

end Poly

section Lin

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def F1 (Z : Module.End (ZMod 2) V) : Module.End (ZMod 2) V := Z ^ 3 + Z + 1

@[expose] def F2 (Z : Module.End (ZMod 2) V) : Module.End (ZMod 2) V := Z ^ 3 + Z ^ 2 + 1

theorem bezout_end (Z : Module.End (ZMod 2) V) : Z * F1 Z + (Z + 1) * F2 Z = 1 := by
  have h := congrArg (Polynomial.aeval Z) (bezout_poly)
  simpa [F1, F2] using h

theorem phi_end {Z : Module.End (ZMod 2) V} (hZ : Z ^ 7 = 1) : (Z + 1) * (F1 Z * F2 Z) = 0 := by
  have h := congrArg (Polynomial.aeval Z) (phi_poly)
  simp only [map_mul, map_add, map_sub, map_pow, aeval_X, map_one, hZ, sub_self] at h
  simpa [F1, F2] using h

theorem F1_apply (Z : Module.End (ZMod 2) V) (a : V) : F1 Z a = Z (Z (Z a)) + Z a + a := by
  simp [F1, pow_succ, Module.End.mul_apply]

theorem F2_apply (Z : Module.End (ZMod 2) V) (a : V) : F2 Z a = Z (Z (Z a)) + Z (Z a) + a := by
  simp [F2, pow_succ, Module.End.mul_apply]

theorem add_self_eq_zero_of_zmod2 (u : V) : u + u = 0 := by
  rw [← two_smul (ZMod 2) u, show (2 : ZMod 2) = 0 from rfl, zero_smul]

theorem exists_decomp {Z : Module.End (ZMod 2) V} (hZ : Z ^ 7 = 1) (S : AddSubgroup V)
    (hS : ∀ a ∈ S, Z a ∈ S) (hfp : ∀ a ∈ S, Z a = a → a = 0) {a : V} (ha : a ∈ S) :
    ∃ b c : V, b ∈ S ∧ c ∈ S ∧ F2 Z b = 0 ∧ F1 Z c = 0 ∧ a = b + c := by
  have hF1 : ∀ x ∈ S, F1 Z x ∈ S := fun x hx => by
    rw [F1_apply]; exact add_mem (add_mem (hS _ (hS _ (hS _ hx))) (hS _ hx)) hx
  have hF2 : ∀ x ∈ S, F2 Z x ∈ S := fun x hx => by
    rw [F2_apply]; exact add_mem (add_mem (hS _ (hS _ (hS _ hx))) (hS _ (hS _ hx))) hx
  have hphi : ∀ x, (Z + 1) (F1 Z (F2 Z x)) = 0 := fun x => by
    have := congrArg (fun E => E x) (phi_end hZ)
    simpa [Module.End.mul_apply] using this
  have hbez : ∀ x, Z (F1 Z x) + (Z + 1) (F2 Z x) = x := fun x => by
    have := congrArg (fun E => E x) (bezout_end Z)
    simpa [Module.End.mul_apply] using this
  have hu0 : F1 Z (F2 Z a) = 0 := by
    refine hfp _ (hF1 _ (hF2 _ ha)) ?_
    have h := hphi a
    rw [LinearMap.add_apply, Module.End.one_apply] at h
    exact add_right_cancel (h.trans (add_self_eq_zero_of_zmod2 _).symm)
  have e' : F1 Z ((Z + 1) (F2 Z a)) = (Z + 1) (F1 Z (F2 Z a)) := by
    simp only [F1_apply, F2_apply, LinearMap.add_apply, Module.End.one_apply, map_add]
    abel
  refine ⟨Z (F1 Z a), (Z + 1) (F2 Z a), hS _ (hF1 _ ha), ?_, ?_, e'.trans (hphi a), (hbez a).symm⟩
  · rw [LinearMap.add_apply, Module.End.one_apply]
    exact add_mem (hS _ (hF2 _ ha)) (hF2 _ ha)
  · have e : F2 Z (Z (F1 Z a)) = Z (F1 Z (F2 Z a)) := by
      simp only [F1_apply, F2_apply, map_add]
      abel
    rw [e, hu0, map_zero]

theorem swap_ker {Z G : Module.End (ZMod 2) V} (hZ : Z ^ 7 = 1) (hG : G * Z = Z ^ 6 * G) :
    (∀ v, F1 Z v = 0 → F2 Z (G v) = 0) ∧ (∀ v, F2 Z v = 0 → F1 Z (G v) = 0) := by
  have h18 : Z ^ 18 = Z ^ 4 := by
    rw [show 18 = 7 * 2 + 4 by norm_num, pow_add, pow_mul, hZ, one_pow, one_mul]
  have h12 : Z ^ 12 = Z ^ 5 := by
    rw [show 12 = 7 + 5 by norm_num, pow_add, hZ, one_mul]
  have hk : ∀ k : ℕ, G * Z ^ k = Z ^ (6 * k) * G := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ← mul_assoc, ih, mul_assoc, hG, ← mul_assoc, ← pow_add]
      congr 2
  have hZZ : ∀ m n : ℕ, Z ^ m * Z ^ n = Z ^ (m + n) := fun m n => (pow_add Z m n).symm
  have e1 : G * F1 Z = Z ^ 4 * F2 Z * G := by
    have hid : Z ^ 18 + Z ^ 6 + 1 = Z ^ 4 * F2 Z := by
      have : Z ^ 4 * F2 Z = Z ^ 7 + Z ^ 6 + Z ^ 4 := by unfold F2; noncomm_ring
      rw [this, h18, hZ]; abel
    have : G * F1 Z = (Z ^ 18 + Z ^ 6 + 1) * G := by
      unfold F1
      rw [mul_add, mul_add, mul_one, hk 3, hG, add_mul, add_mul, one_mul]
    rw [this, hid]
  have e2 : G * F2 Z = Z ^ 4 * F1 Z * G := by
    have hid : Z ^ 18 + Z ^ 12 + 1 = Z ^ 4 * F1 Z := by
      have : Z ^ 4 * F1 Z = Z ^ 7 + Z ^ 5 + Z ^ 4 := by unfold F1; noncomm_ring
      rw [this, h18, h12, hZ]; abel
    have : G * F2 Z = (Z ^ 18 + Z ^ 12 + 1) * G := by
      unfold F2
      rw [mul_add, mul_add, mul_one, hk 3, hk 2, add_mul, add_mul, one_mul]
    rw [this, hid]
  have hinv : ∀ w : V, (Z ^ 3) ((Z ^ 4) w) = w := fun w => by
    have : (Z ^ 3 * Z ^ 4) w = (Z ^ 7) w := by rw [← pow_add]
    rw [← Module.End.mul_apply, this, hZ, Module.End.one_apply]
  refine ⟨fun v hv => ?_, fun v hv => ?_⟩
  · have h := congrArg (fun E => E v) e1
    simp only [Module.End.mul_apply, hv, map_zero] at h
    exact (hinv _).symm.trans (by rw [← h, map_zero])
  · have h := congrArg (fun E => E v) e2
    simp only [Module.End.mul_apply, hv, map_zero] at h
    exact (hinv _).symm.trans (by rw [← h, map_zero])

end Lin

section Grp

open CFSG.Quasithin CFSG.QuasithinUnique.Setup.X1
open CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542 (binRep binModule)

variable {W : Type} [CommGroup W] [Module (ZMod 2) (Additive W)]

@[expose] def Tgen (F : Module.End (ZMod 2) (Additive W) → Module.End (ZMod 2) (Additive W))
    (z : MulAut W) : Subgroup W where
  carrier := {t | t ∈ imgT z ∧ F (binRep W z) (Additive.ofMul t) = 0}
  one_mem' := ⟨one_mem _, by simp⟩
  mul_mem' := fun {a b} ha hb =>
    ⟨mul_mem ha.1 hb.1, by rw [ofMul_mul, map_add, ha.2, hb.2, add_zero]⟩
  inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by rw [ofMul_inv, map_neg, ha.2, neg_zero]⟩

theorem Tgen_le_imgT {F : Module.End (ZMod 2) (Additive W) → Module.End (ZMod 2) (Additive W)}
    {z : MulAut W} : Tgen F z ≤ imgT z := fun _ h => h.1

theorem mem_stabSub_Tgen {F : Module.End (ZMod 2) (Additive W) → Module.End (ZMod 2) (Additive W)}
    {z E : MulAut W}
    (hF : ∀ E' : MulAut W, E' * z = z * E' → ∀ a : Additive W,
      F (binRep W z) (binRep W E' a) = binRep W E' (F (binRep W z) a))
    (hE : E * z = z * E) : E ∈ stabSub (Tgen F z) := by
  have key : ∀ E : MulAut W, E * z = z * E → ∀ t ∈ Tgen F z, E t ∈ Tgen F z := by
    intro E hE t ht
    refine ⟨apply_mem_imgT hE ht.1, ?_⟩
    have := hF E hE (Additive.ofMul t)
    show F (binRep W z) (binRep W E (Additive.ofMul t)) = 0
    rw [this, ht.2, map_zero]
  intro u
  constructor
  · intro hu
    have hE' : E⁻¹ * z = z * E⁻¹ := (Commute.inv_left (show Commute E z from hE)).eq
    have := key E⁻¹ hE' (E u) hu
    simpa using this
  · exact key E hE u

theorem F1_comm {Z E : Module.End (ZMod 2) (Additive W)} (hE : E * Z = Z * E) (a : Additive W) :
    F1 Z (E a) = E (F1 Z a) := by
  have hc : ∀ b, Z (E b) = E (Z b) := fun b => by
    have := congrArg (fun M => M b) hE
    simpa [Module.End.mul_apply] using this.symm
  simp only [F1_apply, hc, map_add]

theorem F2_comm {Z E : Module.End (ZMod 2) (Additive W)} (hE : E * Z = Z * E) (a : Additive W) :
    F2 Z (E a) = E (F2 Z a) := by
  have hc : ∀ b, Z (E b) = E (Z b) := fun b => by
    have := congrArg (fun M => M b) hE
    simpa [Module.End.mul_apply] using this.symm
  simp only [F2_apply, hc, map_add]

theorem binRep_comm {z E : MulAut W} (hE : E * z = z * E) :
    binRep W E * binRep W z = binRep W z * binRep W E := by
  rw [← map_mul, ← map_mul, hE]

end Grp

section Final

open CFSG.Quasithin CFSG.QuasithinUnique.Setup.X1
open CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542 (binRep binModule)

variable {W : Type} [CommGroup W] [Finite W]

theorem orderOf_two_zmod_seven : orderOf (2 : ZMod 7) = 3 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun m hm hm0 => ?_⟩
  interval_cases m <;> decide

theorem two_pow_le_card_of_stab (hW : ∀ w : W, w * w = 1) {n : ℕ} {x y : Fin n → MulAut W}
    {z : MulAut W} (h : HeisCfg 7 n x y z) (U : Subgroup W) (hU1 : U ≠ ⊥) (hUT : U ≤ imgT z)
    (hxs : ∀ i, x i ∈ stabSub U) (hys : ∀ i, y i ∈ stabSub U) (hzs : z ∈ stabSub U) :
    2 ^ (7 ^ n * 3) ≤ Nat.card U := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hodd : Odd 7 := by decide
  have hfz : resHom U ⟨z, hzs⟩ ≠ 1 := by
    intro hf1
    apply hU1
    rw [eq_bot_iff]
    intro e he
    have hze : z e = e := congrArg (fun φ : MulAut ↥U => ((φ ⟨e, he⟩ : W))) hf1
    exact Subgroup.mem_bot.2 (eq_one_of_mem_imgT_fixed hW hodd h.zp (hUT he) hze)
  have h' := HeisCfg.ofSubgroup (stabSub U) (resHom U) hxs hys hzs h hfz
  have hW' : ∀ w : ↥U, w * w = 1 := fun w => Subtype.ext (by simpa using hW w)
  have := two_pow_le_card_imgT_of_heisCfg hW' (p := 7) (by norm_num) h'
  rw [orderOf_two_zmod_seven] at this
  exact this.trans (Subgroup.card_le_card_group _)

theorem two_pow_le_card_imgT_of_heisCfg_of_inv_seven
    (hW : ∀ w : W, w * w = 1) {n : ℕ} {x y : Fin n → MulAut W} {z : MulAut W}
    (h : HeisCfg 7 n x y z) {g : MulAut W} (hg : g * z * g⁻¹ = z⁻¹) :
    2 ^ (2 * (7 ^ n * 3)) ≤ Nat.card (imgT z) := by
  classical
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hodd : Odd 7 := by decide
  let _ : Module (ZMod 2) (Additive W) := binModule (fun v => by rw [pow_two]; exact hW v)
  set Z : Module.End (ZMod 2) (Additive W) := binRep W z with hZdef
  have hZ7 : Z ^ 7 = 1 := by rw [hZdef, ← map_pow, h.zp, map_one]
  let S : AddSubgroup (Additive W) := (imgT z).toAddSubgroup
  have hS : ∀ a ∈ S, Z a ∈ S := fun a ha =>
    show Additive.toMul (Z a) ∈ imgT z from apply_mem_imgT rfl (show Additive.toMul a ∈ imgT z from ha)
  have hfp : ∀ a ∈ S, Z a = a → a = 0 := by
    intro a ha hZa
    have h1 := eq_one_of_mem_imgT_fixed hW hodd h.zp (show Additive.toMul a ∈ imgT z from ha)
      (congrArg Additive.toMul hZa)
    exact Additive.toMul.injective h1
  have hdec : ∀ t ∈ imgT z, ∃ a ∈ Tgen F2 z, ∃ b ∈ Tgen F1 z, t = a * b := by
    intro t ht
    obtain ⟨b, c, hb, hc, hF2, hF1, habc⟩ := exists_decomp hZ7 S hS hfp (a := Additive.ofMul t) ht
    refine ⟨Additive.toMul b, ⟨hb, by simpa using hF2⟩, Additive.toMul c, ⟨hc, by simpa using hF1⟩, ?_⟩
    have := congrArg Additive.toMul habc
    simpa using this
  have hinf : Tgen F1 z ⊓ Tgen F2 z = ⊥ := by
    rw [eq_bot_iff]
    intro t ht
    have h0 : Additive.ofMul t = 0 := by
      have := congrArg (fun E => E (Additive.ofMul t)) (bezout_end Z)
      simp only [Module.End.mul_apply, LinearMap.add_apply, Module.End.one_apply] at this
      rw [← this, ht.1.2, ht.2.2]
      simp
    exact Subgroup.mem_bot.2 (ofMul_eq_zero.mp h0)
  have hne : imgT z ≠ ⊥ := by
    intro hbot
    apply h.z1
    ext v
    have h1 : z v * v⁻¹ ∈ imgT z := mem_imgT.2 ⟨v, rfl⟩
    rw [hbot, Subgroup.mem_bot, mul_inv_eq_one] at h1
    simpa using h1
  have hgz : g * z = z ^ 6 * g := by
    have h1 : g * z = z⁻¹ * g := by
      calc g * z = (g * z * g⁻¹) * g := by group
        _ = z⁻¹ * g := by rw [hg]
    have h2 : z ^ 6 = z⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_succ, h.zp])
    rw [h1, h2]
  have hgimg : ∀ t ∈ imgT z, g t ∈ imgT z := by
    intro t ht
    obtain ⟨w, rfl⟩ := mem_imgT.1 ht
    have h1 : g (z w) = z⁻¹ (g w) := by
      have : (g * z) w = (z⁻¹ * g) w := by
        rw [show g * z = z⁻¹ * g by rw [hgz]; congr 1; exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ, h.zp])]
      simpa [MulAut.mul_apply] using this
    have h2 : g (z w * w⁻¹) = (z (z⁻¹ (g w)) * (z⁻¹ (g w))⁻¹)⁻¹ := by
      rw [map_mul, map_inv, h1]
      simp
    rw [h2]
    exact (imgT z).inv_mem (mem_imgT.2 ⟨_, rfl⟩)
  have hG : binRep W g * Z = Z ^ 6 * binRep W g := by
    rw [hZdef, ← map_mul, ← map_pow, ← map_mul, hgz]
  obtain ⟨hsw1, hsw2⟩ := swap_ker hZ7 hG
  have hgT12 : ∀ t ∈ Tgen F1 z, g t ∈ Tgen F2 z := fun t ht =>
    ⟨hgimg t ht.1, hsw1 (Additive.ofMul t) ht.2⟩
  have hgT21 : ∀ t ∈ Tgen F2 z, g t ∈ Tgen F1 z := fun t ht =>
    ⟨hgimg t ht.1, hsw2 (Additive.ofMul t) ht.2⟩
  have hgne : ∀ t : W, t ≠ 1 → g t ≠ 1 := fun t ht h1 => ht (g.injective (by simpa using h1))
  have hor : Tgen F1 z ≠ ⊥ ∨ Tgen F2 z ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    obtain ⟨hc1, hc2⟩ := hcon
    apply hne
    rw [eq_bot_iff]
    intro t ht
    obtain ⟨a, ha, b, hb, rfl⟩ := hdec t ht
    rw [hc1] at hb
    rw [hc2] at ha
    rw [Subgroup.mem_bot] at ha hb ⊢
    rw [ha, hb, mul_one]
  have hT1 : Tgen F1 z ≠ ⊥ := by
    rcases hor with h1 | h2
    · exact h1
    · intro hbot
      obtain ⟨⟨t, ht⟩, ht1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 h2
      have := hgT21 t ht
      rw [hbot, Subgroup.mem_bot] at this
      exact hgne t (fun e => ht1 (Subtype.ext e)) this
  have hT2 : Tgen F2 z ≠ ⊥ := by
    obtain ⟨⟨t, ht⟩, ht1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hT1
    intro hbot
    have := hgT12 t ht
    rw [hbot, Subgroup.mem_bot] at this
    exact hgne t (fun e => ht1 (Subtype.ext e)) this
  have hs1 : ∀ E : MulAut W, E * z = z * E → E ∈ stabSub (Tgen F1 z) := fun E hE =>
    mem_stabSub_Tgen (fun E' hE' a => F1_comm (binRep_comm hE') a) hE
  have hs2 : ∀ E : MulAut W, E * z = z * E → E ∈ stabSub (Tgen F2 z) := fun E hE =>
    mem_stabSub_Tgen (fun E' hE' a => F2_comm (binRep_comm hE') a) hE
  have b1 := two_pow_le_card_of_stab hW h (Tgen F1 z) hT1 Tgen_le_imgT
    (fun i => hs1 _ (h.zx i)) (fun i => hs1 _ (h.zy i)) (hs1 _ rfl)
  have b2 := two_pow_le_card_of_stab hW h (Tgen F2 z) hT2 Tgen_le_imgT
    (fun i => hs2 _ (h.zx i)) (fun i => hs2 _ (h.zy i)) (hs2 _ rfl)
  let f : Tgen F1 z × Tgen F2 z → imgT z := fun p =>
    ⟨(p.1 : W) * (p.2 : W), mul_mem (Tgen_le_imgT p.1.2) (Tgen_le_imgT p.2.2)⟩
  have hf : Function.Injective f := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ hab
    have h1 : (a : W) * b = a' * b' := congrArg Subtype.val hab
    have h2 : (a : W)⁻¹ * a' ∈ Tgen F1 z ⊓ Tgen F2 z := by
      refine ⟨(Tgen F1 z).mul_mem ((Tgen F1 z).inv_mem a.2) a'.2, ?_⟩
      have : (a : W)⁻¹ * a' = b * (b' : W)⁻¹ := by
        calc (a : W)⁻¹ * a' = (a : W)⁻¹ * (a' * b') * (b' : W)⁻¹ := by group
          _ = (a : W)⁻¹ * (a * b) * (b' : W)⁻¹ := by rw [← h1]
          _ = b * (b' : W)⁻¹ := by group
      rw [this]
      exact (Tgen F2 z).mul_mem b.2 ((Tgen F2 z).inv_mem b'.2)
    rw [hinf, Subgroup.mem_bot, inv_mul_eq_one] at h2
    have h3 : (b : W) = b' := by
      rw [← h2] at h1
      exact mul_left_cancel h1
    have ha : a = a' := Subtype.ext h2
    have hb : b = b' := Subtype.ext h3
    rw [ha, hb]
  have hcard := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod] at hcard
  calc 2 ^ (2 * (7 ^ n * 3)) = 2 ^ (7 ^ n * 3) * 2 ^ (7 ^ n * 3) := by rw [two_mul, pow_add]
    _ ≤ Nat.card (Tgen F1 z) * Nat.card (Tgen F2 z) := Nat.mul_le_mul b1 b2
    _ ≤ Nat.card (imgT z) := hcard

end Final

end CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit
