module

public import CFSG.Quasithin.Background.CommVCommute
public import CFSG.GroupTheory.HyperplaneGeneration
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.Quasithin
open scoped commutatorElement

section Basic

variable {V : Type*} [CommGroup V]

theorem sq_eq_one_of_commonImage (hV : ∀ v : V, v ^ 2 = 1) {g : MulAut V} {W : Subgroup V}
    (h1 : ∀ v : V, g v * v⁻¹ ∈ W) (h2 : ∀ w ∈ W, g w = w) : g ^ 2 = 1 := by
  refine MulEquiv.ext fun v => ?_
  obtain ⟨w, hw, hgv⟩ : ∃ w ∈ W, g v = w * v := ⟨g v * v⁻¹, h1 v, by simp⟩
  rw [sq, MulAut.mul_apply, MulAut.one_apply, hgv, map_mul, h2 w hw, hgv, ← mul_assoc, ← sq,
    hV w, one_mul]

theorem sq_mul_eq_one_of_commonImage (hV : ∀ v : V, v ^ 2 = 1) {e f : MulAut V}
    {W : Subgroup V} (he1 : ∀ v : V, e v * v⁻¹ ∈ W) (he2 : ∀ w ∈ W, e w = w)
    (hf1 : ∀ v : V, f v * v⁻¹ ∈ W) (hf2 : ∀ w ∈ W, f w = w) : (e * f) ^ 2 = 1 := by
  refine sq_eq_one_of_commonImage hV (W := W) (fun v => ?_) fun w hw => ?_
  · have : (e * f) v * v⁻¹ = (e (f v) * (f v)⁻¹) * (f v * v⁻¹) := by
      show e (f v) * v⁻¹ = _
      group
    rw [this]
    exact W.mul_mem (he1 (f v)) (hf1 v)
  · show e (f w) = w
    rw [hf2 w hw, he2 w hw]

theorem sq_commutator_eq_one_of_commonImage (hV : ∀ v : V, v ^ 2 = 1) {e h : MulAut V}
    {W : Subgroup V} (he1 : ∀ v : V, e v * v⁻¹ ∈ W) (he2 : ∀ w ∈ W, e w = w)
    (hh1 : ∀ w ∈ W, h w ∈ W) (hh2 : ∀ w ∈ W, h⁻¹ w ∈ W) : ⁅e, h⁆ ^ 2 = 1 := by
  have he : e⁻¹ = e :=
    inv_eq_of_mul_eq_one_right (by rw [← sq]; exact sq_eq_one_of_commonImage hV he1 he2)
  have hf1 : ∀ v : V, (h * e * h⁻¹) v * v⁻¹ ∈ W := by
    intro v
    have : (h * e * h⁻¹) v * v⁻¹ = h (e (h⁻¹ v) * (h⁻¹ v)⁻¹) := by
      show h (e (h⁻¹ v)) * v⁻¹ = _
      rw [map_mul, map_inv, MulAut.apply_inv_self]
    rw [this]
    exact hh1 _ (he1 _)
  have hf2 : ∀ w ∈ W, (h * e * h⁻¹) w = w := by
    intro w hw
    show h (e (h⁻¹ w)) = w
    rw [he2 _ (hh2 w hw), MulAut.apply_inv_self]
  have hc : ⁅e, h⁆ = e * (h * e * h⁻¹) := by
    rw [commutatorElement_def, he]
    group
  rw [hc]
  exact sq_mul_eq_one_of_commonImage hV he1 he2 hf1 hf2

end Basic

section Odd

variable {V : Type*} [CommGroup V] [Finite V]

theorem eq_one_of_sq_eq_one_of_odd {G : Type*} [Group G] [Finite G] (hG : ¬ 2 ∣ Nat.card G)
    {x : G} (hx : x ^ 2 = 1) : x = 1 := by
  have hcop : Nat.Coprime 2 (Nat.card G) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hG
  have := pow_gcd_eq_one.mpr ⟨hx, pow_card_eq_one' (G := G)⟩
  rwa [hcop.gcd_eq_one, pow_one] at this

theorem commute_of_commonImage (hV : ∀ v : V, v ^ 2 = 1) {E X : Subgroup (MulAut V)}
    {W : Subgroup V} (hW1 : ∀ e ∈ E, ∀ v : V, e v * v⁻¹ ∈ W) (hW2 : ∀ e ∈ E, ∀ w ∈ W, e w = w)
    (hX : ¬ 2 ∣ Nat.card X) (hEX : E ≤ Subgroup.normalizer (X : Set (MulAut V)))
    {e h : MulAut V} (he : e ∈ E) (hhX : h ∈ X) (hh1 : ∀ w ∈ W, h w ∈ W)
    (hh2 : ∀ w ∈ W, h⁻¹ w ∈ W) : e * h = h * e := by
  have hsq := sq_commutator_eq_one_of_commonImage hV (hW1 e he) (hW2 e he) hh1 hh2
  have hmem : ⁅e, h⁆ ∈ X := by
    rw [commutatorElement_def]
    have h1 : e * h * e⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp (hEX he) h).mp hhX
    exact X.mul_mem h1 (X.inv_mem hhX)
  have h1 : (⟨⁅e, h⁆, hmem⟩ : X) = 1 :=
    eq_one_of_sq_eq_one_of_odd hX (Subtype.ext hsq)
  exact commutatorElement_eq_one_iff_mul_comm.mp (congrArg Subtype.val h1)

omit [Finite V] in
theorem smul_mem_of_commute {W : Subgroup V} {a h : MulAut V}
    (ha : ∀ v : V, a v * v⁻¹ ∈ W) (hW : ∀ w ∈ W, ∃ v : V, w = a v * v⁻¹)
    (hch : a * h = h * a) : ∀ w ∈ W, h w ∈ W := by
  intro w hw
  obtain ⟨v, rfl⟩ := hW w hw
  have : h (a v * v⁻¹) = a (h v) * (h v)⁻¹ := by
    have h1 : h (a v) = a (h v) := by
      have := congrArg (fun g : MulAut V => g v) hch.symm
      exact this
    rw [map_mul, map_inv, h1]
  rw [this]
  exact ha (h v)

omit [Finite V] in
theorem isElementaryAbelian_two_of {E : Subgroup (MulAut V)} (hE : IsElemAbelian2 E) :
    IsElementaryAbelian 2 E :=
  { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (hE.1 a a.2 b b.2)⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2
      (fun a => Subtype.ext (by simpa using hE.2 a a.2)) }

theorem mem_centralizer_of_normalizes_W (hV : ∀ v : V, v ^ 2 = 1) {E X : Subgroup (MulAut V)}
    {W : Subgroup V} (hW1 : ∀ e ∈ E, ∀ v : V, e v * v⁻¹ ∈ W) (hW2 : ∀ e ∈ E, ∀ w ∈ W, e w = w)
    (hX : ¬ 2 ∣ Nat.card X) (hEX : E ≤ Subgroup.normalizer (X : Set (MulAut V)))
    {x : MulAut V} (hxX : x ∈ X) (hh1 : ∀ w ∈ W, x w ∈ W) (hh2 : ∀ w ∈ W, x⁻¹ w ∈ W) :
    x ∈ Subgroup.centralizer (E : Set (MulAut V)) :=
  Subgroup.mem_centralizer_iff.mpr fun _ he =>
    commute_of_commonImage hV hW1 hW2 hX hEX he hxX hh1 hh2

theorem le_centralizer_of_commonImage (hV : ∀ v : V, v ^ 2 = 1) {E : Subgroup (MulAut V)}
    (hE : IsElemAbelian2 E) (hE4 : 4 ≤ Nat.card E) {W : Subgroup V}
    (hW1 : ∀ e ∈ E, ∀ v : V, e v * v⁻¹ ∈ W) (hW2 : ∀ e ∈ E, ∀ w ∈ W, e w = w)
    (hW3 : ∀ e ∈ E, e ≠ 1 → ∀ w ∈ W, ∃ v : V, w = e v * v⁻¹)
    {X : Subgroup (MulAut V)} (hX : ¬ 2 ∣ Nat.card X)
    (hEX : E ≤ Subgroup.normalizer (X : Set (MulAut V))) :
    X ≤ Subgroup.centralizer (E : Set (MulAut V)) := by
  have := isElementaryAbelian_two_of hE
  have : Subgroup.Normalizes E X := ⟨hEX⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hgen := SolvableHall.coprime_centralizer_generation (p := 2) (A := ↥E) (H := ↥X)
    (by norm_num; exact hE4) hX
  let Z : Subgroup X := (Subgroup.centralizer (E : Set (MulAut V))).comap X.subtype
  have hle : (⨆ (a : E) (_ : a ≠ 1), fixedPointSubgroup (Subgroup.zpowers a) X) ≤ Z := by
    refine iSup₂_le fun a ha x hx => ?_
    have hax : a • x = x := (SolvableHall.mem_fixedPointSubgroup_zpowers_iff a x).mp hx
    have hch : (a : MulAut V) * (x : MulAut V) = (x : MulAut V) * a := by
      have h1 := congrArg (fun z : X => (z : MulAut V)) hax
      have h2 : (a : MulAut V) * (x : MulAut V) * (a : MulAut V)⁻¹ = x := by
        simpa using h1
      exact mul_inv_eq_iff_eq_mul.mp h2
    have ha1 : (a : MulAut V) ≠ 1 := fun h => ha (Subtype.ext h)
    have hW3a := hW3 a a.2 ha1
    have hcm : Commute (a : MulAut V) (x : MulAut V) := hch
    have hch' : (a : MulAut V) * (x : MulAut V)⁻¹ = (x : MulAut V)⁻¹ * a := hcm.inv_right.eq
    exact mem_centralizer_of_normalizes_W hV hW1 hW2 hX hEX x.2
      (smul_mem_of_commute (hW1 a a.2) hW3a hch) (smul_mem_of_commute (hW1 a a.2) hW3a hch')
  intro x hx
  have hmem : (⟨x, hx⟩ : X) ∈ (⊤ : Subgroup X) := Subgroup.mem_top _
  rw [← hgen] at hmem
  exact hle hmem

omit [Finite V] in
theorem smul_mem_commV_of_commute {B : Subgroup (MulAut V)} {h : MulAut V}
    (hch : ∀ b ∈ B, b * h = h * b) : ∀ w ∈ commV B, h w ∈ commV B :=
  fun _ hw => CFSG.Quasithin.apply_mem_commV_of_forall_commute (fun b hb => (hch b hb).symm) hw

omit [Finite V] in
theorem commV_le_of_forall {B : Subgroup (MulAut V)} {W : Subgroup V}
    (hW1 : ∀ e ∈ B, ∀ v : V, e v * v⁻¹ ∈ W) : commV B ≤ W :=
  Subgroup.closure_le _ |>.mpr (by rintro _ ⟨b, hb, v, rfl⟩; exact hW1 b hb v)

theorem le_centralizer_of_commonImage_hyperplane (hV : ∀ v : V, v ^ 2 = 1)
    {E : Subgroup (MulAut V)} (hE : IsElemAbelian2 E) [Nontrivial E] {W : Subgroup V}
    (hW1 : ∀ e ∈ E, ∀ v : V, e v * v⁻¹ ∈ W) (hW2 : ∀ e ∈ E, ∀ w ∈ W, e w = w)
    (hW3 : ∀ B : Subgroup E, B.index = 2 → ∀ w ∈ W, w ∈ commV (B.map E.subtype))
    {X : Subgroup (MulAut V)} (hX : ¬ 2 ∣ Nat.card X)
    (hEX : E ≤ Subgroup.normalizer (X : Set (MulAut V))) :
    X ≤ Subgroup.centralizer (E : Set (MulAut V)) := by
  have := isElementaryAbelian_two_of hE
  have : Subgroup.Normalizes E X := ⟨hEX⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hgen := SolvableHall.coprime_hyperplane_generation (p := 2) (A := ↥E) (H := ↥X) hX
  let Z : Subgroup X := (Subgroup.centralizer (E : Set (MulAut V))).comap X.subtype
  have hle : (⨆ (B : Subgroup E) (_ : B.index = 2), fixedPointSubgroup B X) ≤ Z := by
    refine iSup₂_le fun B hB x hx => ?_
    have hch : ∀ b ∈ B.map E.subtype, b * (x : MulAut V) = (x : MulAut V) * b := by
      rintro _ ⟨β, hβ, rfl⟩
      have hβx : (⟨β, hβ⟩ : B) • x = x := hx ⟨β, hβ⟩
      have h1 := congrArg (fun z : X => (z : MulAut V)) hβx
      have h2 : (β : MulAut V) * (x : MulAut V) * (β : MulAut V)⁻¹ = x := by
        simpa [Subgroup.smul_def] using h1
      exact mul_inv_eq_iff_eq_mul.mp h2
    have hch' : ∀ b ∈ B.map E.subtype, b * (x : MulAut V)⁻¹ = (x : MulAut V)⁻¹ * b := fun b hb =>
      (Commute.inv_right (show Commute b (x : MulAut V) from hch b hb)).eq
    have hBW : commV (B.map E.subtype) = W :=
      le_antisymm (commV_le_of_forall fun e he v => by
        obtain ⟨β, -, rfl⟩ := he
        exact hW1 β β.2 v) (fun w hw => hW3 B hB w hw)
    refine mem_centralizer_of_normalizes_W hV hW1 hW2 hX hEX x.2 (fun w hw => ?_) (fun w hw => ?_)
    · rw [← hBW] at hw ⊢
      exact smul_mem_commV_of_commute hch w hw
    · rw [← hBW] at hw ⊢
      exact smul_mem_commV_of_commute hch' w hw
  intro x hx
  have hmem : (⟨x, hx⟩ : X) ∈ (⊤ : Subgroup X) := Subgroup.mem_top _
  rw [← hgen] at hmem
  exact hle hmem

end Odd

end CFSG.CGT.PushingUpLit.CGT6
