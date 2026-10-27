module

public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.HeisLift

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic

open CFSG.Quasithin CFSG.QuasithinUnique.Setup.X1 CFSG.QuasithinUnique.Setup.Family
open CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit
open CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542 (binRep binModule)

theorem card_modEq_one_of_fpf_three {U : Type} [Group U] [Finite U] {σ : MulAut U}
    (hσ : σ ^ 3 = 1) (hfp : ∀ u : U, σ u = u → u = 1) : Nat.card U ≡ 1 [MOD 3] := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hG : IsPGroup 3 (Subgroup.zpowers σ) := by
    intro g
    refine ⟨1, Subtype.ext ?_⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 g.2
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← hk, pow_one, ← zpow_natCast, ← zpow_mul, mul_comm,
      zpow_mul, zpow_natCast, hσ, one_zpow]
  have h := hG.card_modEq_card_fixedPoints U
  have hfix : Nat.card (MulAction.fixedPoints (Subgroup.zpowers σ) U) = 1 := by
    rw [Nat.card_eq_one_iff_exists]
    refine ⟨⟨1, fun g => map_one (g : MulAut U)⟩, fun v => Subtype.ext ?_⟩
    exact hfp _ (v.2 ⟨σ, Subgroup.mem_zpowers σ⟩)
  rwa [hfix] at h

theorem two_pow_odd_not_modEq_one {m : ℕ} (hm : Odd m) : ¬ 2 ^ m ≡ 1 [MOD 3] := by
  obtain ⟨k, rfl⟩ := hm
  intro h
  have h4 : 4 ^ k ≡ 1 [MOD 3] := by
    have := (show 4 ≡ 1 [MOD 3] by decide).pow k
    rwa [one_pow] at this
  have h2 : 2 ^ (2 * k + 1) ≡ 2 [MOD 3] := by
    rw [pow_succ, pow_mul]
    have := h4.mul_right 2
    rwa [one_mul] at this
  have := h2.symm.trans h
  exact absurd this (by decide)

theorem two_pow_succ_le_of_modEq {U : Type} [Group U] [Finite U] (hU : ∀ u : U, u * u = 1)
    (h3 : Nat.card U ≡ 1 [MOD 3]) {m : ℕ} (hm : Odd m) (h : 2 ^ m ≤ Nat.card U) :
    2 ^ (m + 1) ≤ Nat.card U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 U := fun u => ⟨1, by rw [pow_one, pow_two, hU]⟩
  obtain ⟨d, hd⟩ := hp.exists_card_eq
  rw [hd] at h h3 ⊢
  have hmd : m ≤ d := (Nat.pow_le_pow_iff_right (by norm_num)).1 h
  have hne : m ≠ d := by
    rintro rfl
    exact two_pow_odd_not_modEq_one hm h3
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

section Final

variable {W : Type} [CommGroup W] [Finite W]

theorem two_pow_le_card_imgT_of_heisCfg_of_inv_seven_of_three
    (hW : ∀ w : W, w * w = 1) {n : ℕ} {x y : Fin n → MulAut W} {z : MulAut W}
    (h : HeisCfg 7 n x y z) {g : MulAut W} (hg : g * z * g⁻¹ = z⁻¹) {ω : MulAut W}
    (hω3 : ω ^ 3 = 1) (hωz : ω * z = z * ω) (hfp : ∀ w : W, ω w = w → w = 1) :
    2 ^ (2 * (7 ^ n * 3 + 1)) ≤ Nat.card (imgT z) := by
  classical
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hodd : Odd 7 := by decide
  let _ : Module (ZMod 2) (Additive W) := binModule (fun v => by rw [pow_two]; exact hW v)
  set Z : Module.End (ZMod 2) (Additive W) := binRep W z with hZdef
  have hZ7 : Z ^ 7 = 1 := by rw [hZdef, ← map_pow, h.zp, map_one]
  let S : AddSubgroup (Additive W) := (imgT z).toAddSubgroup
  have hS : ∀ a ∈ S, Z a ∈ S := fun a ha =>
    show Additive.toMul (Z a) ∈ imgT z from
      apply_mem_imgT rfl (show Additive.toMul a ∈ imgT z from ha)
  have hfpz : ∀ a ∈ S, Z a = a → a = 0 := by
    intro a ha hZa
    have h1 := eq_one_of_mem_imgT_fixed hW hodd h.zp (show Additive.toMul a ∈ imgT z from ha)
      (congrArg Additive.toMul hZa)
    exact Additive.toMul.injective h1
  have hdec : ∀ t ∈ imgT z, ∃ a ∈ Tgen F2 z, ∃ b ∈ Tgen F1 z, t = a * b := by
    intro t ht
    obtain ⟨b, c, hb, hc, hF2, hF1, habc⟩ :=
      exists_decomp hZ7 S hS hfpz (a := Additive.ofMul t) ht
    refine ⟨Additive.toMul b, ⟨hb, by simpa using hF2⟩, Additive.toMul c, ⟨hc, by simpa using hF1⟩,
      ?_⟩
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
  have hz6 : z ^ 6 = z⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_succ, h.zp])
  have hgz' : g * z = z⁻¹ * g := by
    calc g * z = (g * z * g⁻¹) * g := by group
      _ = z⁻¹ * g := by rw [hg]
  have hgz : g * z = z ^ 6 * g := by rw [hgz', hz6]
  have hgimg : ∀ t ∈ imgT z, g t ∈ imgT z := by
    intro t ht
    obtain ⟨w, rfl⟩ := mem_imgT.1 ht
    have h1 : g (z w) = z⁻¹ (g w) := by
      have : (g * z) w = (z⁻¹ * g) w := by rw [hgz']
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
  have hmodd : Odd (7 ^ n * 3) := (Odd.pow (by decide)).mul (by decide)
  have hpiece : ∀ T : Subgroup W, ω ∈ stabSub T → 2 ^ (7 ^ n * 3) ≤ Nat.card T →
      2 ^ (7 ^ n * 3 + 1) ≤ Nat.card T := by
    intro T hωT hT
    set σ := resHom T ⟨ω, hωT⟩ with hσ
    have hσ3 : σ ^ 3 = 1 := by
      rw [hσ, ← map_pow]
      have : (⟨ω, hωT⟩ : ↥(stabSub T)) ^ 3 = 1 := Subtype.ext (by simpa using hω3)
      rw [this, map_one]
    have hσfp : ∀ u : T, σ u = u → u = 1 := by
      intro u hu
      apply Subtype.ext
      have := congrArg Subtype.val hu
      rw [hσ, resHom_apply] at this
      exact hfp _ this
    have hT2 : ∀ u : T, u * u = 1 := fun u => Subtype.ext (by simpa using hW u)
    exact two_pow_succ_le_of_modEq hT2 (card_modEq_one_of_fpf_three hσ3 hσfp) hmodd hT
  have c1 := hpiece _ (hs1 ω hωz) b1
  have c2 := hpiece _ (hs2 ω hωz) b2
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
  calc 2 ^ (2 * (7 ^ n * 3 + 1)) = 2 ^ (7 ^ n * 3 + 1) * 2 ^ (7 ^ n * 3 + 1) := by
        rw [two_mul, pow_add]
    _ ≤ Nat.card (Tgen F1 z) * Nat.card (Tgen F2 z) := Nat.mul_le_mul c1 c2
    _ ≤ Nat.card (imgT z) := hcard

end Final

section Center

variable {W : Type} [CommGroup W] [Finite W] {L : Subgroup (MulAut W)} {S : Type} [Group S]

theorem two_pow_le_card_of_heisCfg_centerQuotient_of_inv_seven_of_three
    (hW : ∀ w : W, w * w = 1) (hirr : IsIrrOn L) (e : CQ L ≃* S) {n : ℕ}
    (hZ : ¬ 7 ∣ Nat.card (Subgroup.center ↥L)) (hZ3 : 3 ∣ Nat.card (Subgroup.center ↥L))
    {x y : Fin n → S} {z : S} (h : HeisCfg 7 n x y z) (hy : ∀ i, y i ^ 7 = 1) {g : S}
    (hg : g * z * g⁻¹ = z⁻¹) :
    2 ^ (2 * (7 ^ n * 3 + 1)) ≤ Nat.card W := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK := ker_centerQuotientHom e
  have hKp : ¬ 7 ∣ Nat.card (centerQuotientHom e).ker := by rw [hK]; exact hZ
  obtain ⟨x', y', z', h', -, -, hz'1, -⟩ := HeisCfg.exists_lift (centerQuotientHom e)
    (centerQuotientHom_surjective e) hK.le hKp h hy
  obtain ⟨g', hg'⟩ := centerQuotientHom_surjective e g
  have hinv : g' * z' * g'⁻¹ = z'⁻¹ := by
    refine eq_of_map_eq_of_pow_eq_one (centerQuotientHom e) hK.le hKp
      (by rw [conj_pow, h'.zp, mul_one, mul_inv_cancel]) (by rw [inv_pow, h'.zp, inv_one]) ?_
    rw [map_mul, map_mul, map_inv, map_inv, hg', hz'1]
    exact hg
  have hz' : L.subtype z' ≠ 1 := fun hz1 => h'.z1 (L.subtype_injective (by rw [hz1, map_one]))
  have hinv' : L.subtype g' * L.subtype z' * (L.subtype g')⁻¹ = (L.subtype z')⁻¹ := by
    simp only [← map_inv, ← map_mul]
    exact congrArg L.subtype hinv
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 3 hZ3
  set ω : MulAut W := ((c : ↥L) : MulAut W) with hωdef
  have hω3 : ω ^ 3 = 1 := by
    have h1 : (c : ↥L) ^ 3 = 1 := by
      rw [← Subgroup.coe_pow, ← hc, pow_orderOf_eq_one, Subgroup.coe_one]
    rw [hωdef, ← Subgroup.coe_pow, h1, Subgroup.coe_one]
  have hωl : ∀ l ∈ L, ω * l = l * ω := fun l hl =>
    congrArg Subtype.val (Subgroup.mem_center_iff.1 c.2 ⟨l, hl⟩).symm
  have hωz : ω * L.subtype z' = L.subtype z' * ω := hωl _ z'.2
  have hfp : ∀ w : W, ω w = w → w = 1 := by
    let C : Subgroup W :=
      { carrier := {w | ω w = w}
        one_mem' := map_one ω
        mul_mem' := fun {a b} ha hb => by
          show ω (a * b) = a * b
          rw [map_mul, ha, hb]
        inv_mem' := fun {a} ha => by
          show ω a⁻¹ = a⁻¹
          rw [map_inv, ha] }
    have hC : ∀ l ∈ L, ∀ u ∈ C, l u ∈ C := fun l hl u hu => by
      show ω (l u) = l u
      have := congrArg (fun φ : MulAut W => φ u) (hωl l hl)
      simp only [MulAut.mul_apply] at this
      rw [this, hu]
    rcases hirr.2 C hC with hbot | htop
    · intro w hw
      have : w ∈ C := hw
      rw [hbot, Subgroup.mem_bot] at this
      exact this
    · exfalso
      have h1 : ω = 1 := by
        ext w
        have : w ∈ C := by rw [htop]; exact Subgroup.mem_top w
        exact this
      have h2 : orderOf ω = 3 := by
        rw [hωdef, Subgroup.orderOf_coe, Subgroup.orderOf_coe]
        exact hc
      rw [h1, orderOf_one] at h2
      exact absurd h2 (by norm_num)
  have h2 := two_pow_le_card_imgT_of_heisCfg_of_inv_seven_of_three hW (h'.map L.subtype hz') hinv'
    hω3 hωz hfp
  exact h2.trans (Subgroup.card_le_card_group _)

end Center

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic
