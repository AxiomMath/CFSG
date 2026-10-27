module

public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.HeisLift
public import CFSG.Quasithin.Background.B5Sec

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic

open CFSG.Quasithin CFSG.QuasithinUnique.Setup.X1 CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit

section Algebra

variable {W : Type} [CommGroup W]

theorem inv_eq_self_of_sq_one (hW : ∀ w : W, w * w = 1) (w : W) : w⁻¹ = w :=
  inv_eq_of_mul_eq_one_right (hW w)

theorem imgT_le_fixV_zpowers (hW : ∀ w : W, w * w = 1) {a : MulAut W} (ha : a * a = 1) :
    imgT a ≤ fixV (Subgroup.zpowers a) := by
  intro t ht
  rw [mem_fixV_zpowers]
  obtain ⟨v, rfl⟩ := mem_imgT.1 ht
  have h1 : a (a v) = v := by
    simpa [MulAut.mul_apply] using congrArg (fun g : MulAut W => g v) ha
  rw [map_mul, map_inv, h1]
  have h2 := inv_eq_self_of_sq_one hW (a v * v⁻¹)
  rw [mul_inv_rev, inv_inv] at h2
  exact h2

theorem card_eq_card_fixV_mul_card_imgT (a : MulAut W) :
    Nat.card W = Nat.card (fixV (Subgroup.zpowers a)) * Nat.card (imgT a) := by
  have hker : (cHom a).ker = fixV (Subgroup.zpowers a) := by
    ext v
    rw [MonoidHom.mem_ker, mem_fixV_zpowers]
    show a v * v⁻¹ = 1 ↔ a v = v
    rw [mul_inv_eq_one]
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (cHom a).ker
  have h2 : Nat.card (W ⧸ (cHom a).ker) = Nat.card (imgT a) :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange (cHom a)).toEquiv
  rw [h1, h2, hker, mul_comm]

theorem index_fixV_zpowers_eq_card_imgT [Finite W] (a : MulAut W) :
    (fixV (Subgroup.zpowers a)).index = Nat.card (imgT a) := by
  have h1 := (fixV (Subgroup.zpowers a)).card_mul_index
  have h2 := card_eq_card_fixV_mul_card_imgT a
  have hpos : 0 < Nat.card (fixV (Subgroup.zpowers a)) := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_left hpos (h1.trans h2)

theorem eq_one_of_trivial_sections (hW : ∀ w : W, w * w = 1) {a z : MulAut W}
    (hz3 : z ^ 3 = 1) (hza : z * a = a * z) (hT : ∀ t ∈ imgT a, z t = t)
    (hF : ∀ f : W, a f = f → z f * f⁻¹ ∈ imgT a) : z = 1 := by
  ext w
  have hz3w : z (z (z w)) = w := by
    have := congrArg (fun g : MulAut W => g w) hz3
    simpa [pow_succ, MulAut.mul_apply] using this
  have hcomm : ∀ v : W, z (a v) = a (z v) := fun v => by
    simpa only [MulAut.mul_apply] using congrArg (fun g : MulAut W => g v) hza
  set d : W := z w * w⁻¹ with hd
  have hdF : a d = d := by
    have h1 : a w * w⁻¹ ∈ imgT a := mem_imgT.2 ⟨w, rfl⟩
    have h2 := hT _ h1
    rw [map_mul, map_inv, hcomm, ← div_eq_mul_inv, ← div_eq_mul_inv,
      div_eq_div_iff_mul_eq_mul] at h2
    rw [hd, map_mul, map_inv, ← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff_mul_eq_mul,
      mul_comm (z w) (a w)]
    exact h2
  set u : W := z d * d⁻¹ with hu
  have huT : u ∈ imgT a := hF d hdF
  have hzu : z u = u := hT u huT
  have hzd : z d = u * d := by rw [hu, inv_mul_cancel_right]
  have hzw : z w = d * w := by rw [hd, inv_mul_cancel_right]
  have hzzw : z (z w) = u * w := by
    rw [hzw, map_mul, hzd, hzw, mul_assoc, ← mul_assoc d, hW d, one_mul]
  have hud : u * d = 1 := by
    have h3 : z (z (z w)) = u * (d * w) := by rw [hzzw, map_mul, hzu, hzw]
    rw [h3] at hz3w
    have : u * d * w = 1 * w := by rw [mul_assoc, hz3w, one_mul]
    exact mul_right_cancel this
  have hdu : u = d := by
    have := inv_eq_self_of_sq_one hW d
    exact (eq_inv_of_mul_eq_one_left hud).trans this
  have hd1 : d = 1 := by
    apply z.injective
    rw [hzd, hdu, hW d, map_one]
  rw [MulAut.one_apply]
  exact mul_inv_eq_one.1 hd1

end Algebra

section Dichotomy

theorem heisCfg_toSubgroup {G : Type*} [Group G] {p n : ℕ} {x y : Fin n → G} {z : G}
    (S : Subgroup G) (hx : ∀ i, x i ∈ S) (hy : ∀ i, y i ∈ S) (hz : z ∈ S)
    (h : HeisCfg p n x y z) :
    HeisCfg p n (fun i => (⟨x i, hx i⟩ : S)) (fun i => ⟨y i, hy i⟩) ⟨z, hz⟩ where
  xp i := Subtype.ext (by simpa using h.xp i)
  zp := Subtype.ext (by simpa using h.zp)
  zx i := Subtype.ext (h.zx i)
  zy i := Subtype.ext (h.zy i)
  yx i := Subtype.ext (by simpa using h.yx i)
  xx i j := Subtype.ext (h.xx i j)
  yy i j hij := Subtype.ext (h.yy i j hij)
  xy i j hij := Subtype.ext (h.xy i j hij)
  z1 := fun h1 => h.z1 (congrArg Subtype.val h1)

theorem two_pow_162_le_card_of_hom {Q : Type} [CommGroup Q] [Finite Q]
    (hQ : ∀ q : Q, q * q = 1) {G : Type*} [Group G] {x y : Fin 4 → G} {z : G}
    (h : HeisCfg 3 4 x y z) (ρ : G →* MulAut Q) (hz : ρ z ≠ 1) : 2 ^ 162 ≤ Nat.card Q := by
  have h2 := two_pow_le_card_imgT_of_heisCfg (p := 3) hQ (by norm_num) (h.map ρ hz)
  have hord : orderOf (2 : ZMod 3) = 2 := orderOf_eq_prime (by decide) (by decide)
  rw [hord] at h2
  have h3 : 2 ^ 162 = 2 ^ (3 ^ 4 * 2) := by norm_num
  rw [h3]
  exact h2.trans (Subgroup.card_le_card_group _)

variable {W : Type} [CommGroup W]

theorem heis_dichotomy [Finite W] (hW : ∀ w : W, w * w = 1) {a : MulAut W} (ha : a * a = 1)
    {x y : Fin 4 → MulAut W} {z : MulAut W} (h : HeisCfg 3 4 x y z)
    (hx : ∀ i, x i * a = a * x i) (hy : ∀ i, y i * a = a * y i) (hz : z * a = a * z) :
    2 ^ 162 ≤ Nat.card (imgT a) ∨ 2 ^ 162 * Nat.card (imgT a) ^ 2 ≤ Nat.card W := by
  set X : Subgroup (MulAut W) := Subgroup.centralizer ({a} : Set (MulAut W)) with hX
  have memX : ∀ g : MulAut W, g * a = a * g → g ∈ X := fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.2 hg
  have memX' : ∀ g ∈ X, g * a = a * g := fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.1 hg
  set F : Subgroup W := fixV (Subgroup.zpowers a) with hF
  set T : Subgroup W := imgT a with hT
  have hTF : T ≤ F := imgT_le_fixV_zpowers hW ha
  have hXF : X ≤ stabSub F := by
    intro g hg u
    have hg' := memX' g hg
    have hcomm : a (g u) = g (a u) := by
      simpa only [MulAut.mul_apply] using (congrArg (fun k : MulAut W => k u) hg').symm
    show g u ∈ F ↔ u ∈ F
    rw [hF, mem_fixV_zpowers, mem_fixV_zpowers, hcomm]
    exact ⟨fun h => g.injective h, fun h => by rw [h]⟩
  have hXT : X ≤ stabSub T := by
    intro g hg u
    have hg' := memX' g hg
    have hgi' := memX' g⁻¹ (X.inv_mem hg)
    show g u ∈ imgT a ↔ u ∈ imgT a
    constructor
    · intro h1
      simpa using apply_mem_imgT hgi' h1
    · exact apply_mem_imgT hg'
  have hx' : ∀ i, x i ∈ X := fun i => memX _ (hx i)
  have hy' : ∀ i, y i ∈ X := fun i => memX _ (hy i)
  have hz' : z ∈ X := memX _ hz
  have hH := heisCfg_toSubgroup X hx' hy' hz' h
  let ρT : ↥X →* MulAut ↥T := (CFSG.Quasithin.resHom T).comp (Subgroup.inclusion hXT)
  let ρQ : ↥X →* MulAut (Sec F T) := CFSG.Quasithin.B5.secHom X hXF hXT
  have hTm : ∀ w : ↥T, w * w = 1 := fun w => Subtype.ext (by simpa using hW w)
  by_cases hzT : ρT ⟨z, hz'⟩ = 1
  · by_cases hzQ : ρQ ⟨z, hz'⟩ = 1
    · exfalso
      apply h.z1
      refine eq_one_of_trivial_sections hW h.zp hz (fun t ht => ?_) (fun f hf => ?_)
      · have := congrArg (fun φ : MulAut ↥T => ((φ ⟨t, ht⟩ : ↥T) : W)) hzT
        exact this
      · have hfF : f ∈ F := by rw [hF, mem_fixV_zpowers]; exact hf
        have hzF : z f ∈ F := ((hXF hz') f).2 hfF
        have h1 := congrArg (fun φ : MulAut (Sec F T) => φ (QuotientGroup.mk ⟨f, hfF⟩)) hzQ
        have h2 : (QuotientGroup.mk ⟨z f, hzF⟩ : Sec F T) = QuotientGroup.mk ⟨f, hfF⟩ := h1
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h2
        have h3 := T.inv_mem h2
        rw [mul_comm]
        simpa using h3
    · right
      have hQ : ∀ q : Sec F T, q * q = 1 := by
        intro q
        induction q using QuotientGroup.induction_on with
        | _ f =>
          rw [← QuotientGroup.mk_mul, show f * f = 1 from Subtype.ext (by simpa using hW f),
            QuotientGroup.mk_one]
      have hb := two_pow_162_le_card_of_hom hQ hH ρQ hzQ
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (T.subgroupOf F)
      have h2 : Nat.card (T.subgroupOf F) = Nat.card T :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTF).toEquiv
      have h3 := card_eq_card_fixV_mul_card_imgT a
      rw [h2] at h1
      calc 2 ^ 162 * Nat.card (imgT a) ^ 2 ≤ Nat.card (Sec F T) * Nat.card (imgT a) ^ 2 :=
            Nat.mul_le_mul_right _ hb
        _ = Nat.card F * Nat.card T := by rw [h1]; ring
        _ = Nat.card W := h3.symm
  · left
    exact two_pow_162_le_card_of_hom hTm hH ρT hzT

end Dichotomy

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic
