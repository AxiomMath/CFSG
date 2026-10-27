module

public import CFSG.ClassicalInvolution.Q3.TA3SmallTwinGood
public import CFSG.ClassicalInvolution.Q3.TL3Induct
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.ClassicalInvolution.Q3.TA3.Twin3

open CFSG CFSG.ClassicalInvolution
open scoped commutatorElement

section Comm

variable {G : Type*} [Group G]

theorem commutatorElement_eq_of_central {a b : G} (h : ∀ g : G, g * ⁅a, b⁆ = ⁅a, b⁆ * g) :
    ⁅a, b⁆ = a * a * (b * b) * ((a * b) * (a * b))⁻¹ := by
  set k := ⁅a, b⁆ with hk
  have hab : a * b = k * (b * a) := by rw [hk, commutatorElement_def]; group
  have hki : a * k⁻¹ = k⁻¹ * a := by
    calc a * k⁻¹ = k⁻¹ * (k * a) * k⁻¹ := by group
      _ = k⁻¹ * (a * k) * k⁻¹ := by rw [h a]
      _ = k⁻¹ * a := by group
  have hba : b * a = k⁻¹ * (a * b) := by rw [hab, ← mul_assoc, inv_mul_cancel, one_mul]
  have h2 : (a * b) * (a * b) = k⁻¹ * (a * a * (b * b)) := by
    calc (a * b) * (a * b) = a * (b * a) * b := by group
      _ = a * (k⁻¹ * (a * b)) * b := by rw [hba]
      _ = a * k⁻¹ * a * b * b := by group
      _ = k⁻¹ * a * a * b * b := by rw [hki]
      _ = k⁻¹ * (a * a * (b * b)) := by group
  rw [h2]
  group

theorem commutatorElement_mul_of_eq_one {x u w : G} (h : ⁅x, w⁆ = 1) : ⁅x, u * w⁆ = ⁅x, u⁆ := by
  rw [commutatorElement_def] at h ⊢
  rw [commutatorElement_def]
  calc x * (u * w) * x⁻¹ * (u * w)⁻¹ = x * u * x⁻¹ * (x * w * x⁻¹ * w⁻¹) * u⁻¹ := by group
    _ = x * u * x⁻¹ * u⁻¹ := by rw [h]; group

end Comm

section Index

variable {Y : Type} [Group Y] [Finite Y]

theorem index_le_two {L : Subgroup Y} [L.Normal]
    (hcent : ∀ y : Y, (∀ l ∈ L, y * l = l * y) → y ∈ L) (hZ : Nat.card (Subgroup.center L) = 2)
    (hA : Nat.card (MulAut L) ≤ Nat.card L) : L.index ≤ 2 := by
  let φ : Y →* MulAut L := MulAut.conjNormal
  have hker : ∀ y ∈ φ.ker, y ∈ L ∧ ∀ l ∈ L, y * l = l * y := by
    intro y hy
    have hc : ∀ l ∈ L, y * l = l * y := by
      intro l hl
      have h1 := congrArg (fun f : MulAut L => ((f ⟨l, hl⟩ : L) : Y)) (MonoidHom.mem_ker.1 hy)
      simp only [φ, MulAut.conjNormal_apply, MulAut.one_apply] at h1
      calc y * l = y * l * y⁻¹ * y := by group
        _ = l * y := by rw [h1]
    exact ⟨hcent y hc, hc⟩
  let f : φ.ker → Subgroup.center L := fun y =>
    ⟨⟨y, (hker y y.2).1⟩, Subgroup.mem_center_iff.2 fun l =>
      Subtype.ext ((hker y y.2).2 l l.2).symm⟩
  have hf : Function.Injective f := fun a b hab =>
    Subtype.ext (congrArg (fun z : Subgroup.center L => ((z : L) : Y)) hab)
  have hk : Nat.card φ.ker ≤ 2 := hZ ▸ Nat.card_le_card_of_injective f hf
  have : Finite (MulAut L) := Finite.of_injective _ DFunLike.coe_injective
  have hr : Nat.card φ.range ≤ Nat.card (MulAut L) := Subgroup.card_le_card_group _
  have hY : Nat.card Y = Nat.card φ.ker * Nat.card φ.range := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  have hL : Nat.card L * L.index = Nat.card Y := Subgroup.card_mul_index L
  have hpos : 0 < Nat.card L := Nat.card_pos
  have h2 : Nat.card Y ≤ 2 * Nat.card L :=
    hY ▸ (Nat.mul_le_mul hk (hr.trans hA))
  by_contra hcon
  push Not at hcon
  have : Nat.card L * 3 ≤ Nat.card L * L.index := Nat.mul_le_mul_left _ hcon
  omega

end Index

section Square

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

open QuaternionGroup in
theorem exists_q8_hom (hd : TightDatum R S t) (hc : TightCls Y R S t) :
    ∃ ι : QuaternionGroup 2 →* Y, Function.Injective ι ∧ (∀ q, ι q ∈ R) ∧ ι (a 2) = t := by
  obtain ⟨e⟩ := hc.1
  let ι : QuaternionGroup 2 →* Y :=
    R.subtype.comp ((S : Subgroup R).subtype.comp e.symm.toMonoidHom)
  have hι : Function.Injective ι :=
    Subtype.val_injective.comp (Subtype.val_injective.comp e.symm.injective)
  have hR : ∀ q, ι q ∈ R := fun q => (e.symm q : R).2
  refine ⟨ι, hι, hR, hd.eq_of_orderOf_eq_two (hR _) ?_⟩
  rw [orderOf_injective ι hι]
  exact orderOf_eq_prime (by decide) (by decide)

open QuaternionGroup in
theorem exists_sq_eq_of_index_le_two (hd : TightDatum R S t) (hc : TightCls Y R S t)
    {L : Subgroup Y} (hL : L.index ≤ 2) : ∃ s ∈ R, s ∈ L ∧ s * s = t := by
  obtain ⟨ι, -, hR, ht⟩ := exists_q8_hom hd hc
  have hsq : ∀ q : QuaternionGroup 2, q * q = a 2 → ι q * ι q = t := fun q hq => by
    rw [← map_mul, hq, ht]
  have h1 := hsq (a 1) (by decide)
  have h2 := hsq (xa 0) (by decide)
  have h3 := hsq (a 1 * xa 0) (by decide)
  have hne : L.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  rcases (show L.index = 1 ∨ L.index = 2 by omega) with h | h
  · exact ⟨ι (a 1), hR _, Subgroup.index_eq_one.1 h ▸ Subgroup.mem_top _, h1⟩
  · by_cases hi : ι (a 1) ∈ L
    · exact ⟨_, hR _, hi, h1⟩
    by_cases hj : ι (xa 0) ∈ L
    · exact ⟨_, hR _, hj, h2⟩
    refine ⟨_, hR _, ?_, h3⟩
    rw [map_mul, Subgroup.mul_mem_iff_of_index_two h]
    exact iff_of_false hi hj

end Square

section Core

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem false_of_conj_eq_mul (hD : TightDatum R S t) {c : Y} (hc2 : orderOf c = 2)
    (hct : c ≠ t) {s x : Y} (hsR : s ∈ R) (hx : x ∈ Subgroup.centralizer ({t} : Set Y))
    (hxs : x * s * x⁻¹ = c * s) : False := by
  have h1 : x * s * x⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp (hD.le_normalizer hx) s).mp hsR
  rw [hxs] at h1
  have hcR : c ∈ R := by
    have := R.mul_mem h1 (R.inv_mem hsR)
    rwa [mul_inv_cancel_right] at this
  exact hct (hD.eq_of_orderOf_eq_two hcR hc2)

theorem false_of_commutator_eq {L : Subgroup Y} (hH : TwinFr.TwinHyp L R S t) {x s z : L}
    (hz : z ∈ Subgroup.center L) (hz1 : z ≠ 1) (hzz : z * z = 1) (hsR : (s : Y) ∈ R)
    (hxt : x * ⟨t, hH.mem⟩ = ⟨t, hH.mem⟩ * x) (hxs : ⁅x, s⁆ = z) : False := by
  have hz2 : orderOf (z : Y) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime (by rw [sq, hzz]) hz1
  have hzt : (z : Y) ≠ t := by
    intro h
    obtain ⟨l, hl, hlt⟩ := hH.not_central
    apply hlt
    have := congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨l, hl⟩)
    simpa [h] using this
  have hx : (x : Y) ∈ Subgroup.centralizer ({t} : Set Y) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val hxt
  have hxs' : x * s * x⁻¹ = z * s := by
    rw [← hxs, commutatorElement_def]
    group
  exact false_of_conj_eq_mul hH.datum hz2 hzt hsR hx (by simpa using congrArg Subtype.val hxs')

end Core

end CFSG.ClassicalInvolution.Q3.TA3.Twin3
