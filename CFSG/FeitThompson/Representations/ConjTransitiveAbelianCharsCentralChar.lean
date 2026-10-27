module

public import CFSG.FeitThompson.Definitions.ExtraspecialFinitePGroup
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import CFSG.FeitThompson.Representations.ExtraspecialQuotientAlternatingForm
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open scoped commutatorElement

universe u v

variable {p n : ℕ} {P : Type u} [Group P] {B : Subgroup P} {k : Type v} [Field k]
  {hcl : commutator P ≤ Subgroup.center P}

def commCenter (hcl : commutator P ≤ Subgroup.center P) (x y : P) : Subgroup.center P :=
  ⟨⁅x, y⁆, commutatorElement_mem_center_of_commutator_le_center hcl x y⟩

@[simp] theorem coe_commCenter (x y : P) : (commCenter hcl x y : P) = ⁅x, y⁆ := (rfl)

theorem commCenter_eq_one_left {x : P} (hx : x ∈ Subgroup.center P) (y : P) :
    commCenter hcl x y = 1 :=
  Subtype.ext (by simpa using commutatorElement_left_eq_one_of_mem_center (x := y) hx)

@[simp] theorem commCenter_one_right (x : P) : commCenter hcl x 1 = 1 := Subtype.ext (by simp)

theorem commCenter_eq_one_iff {x y : P} : commCenter hcl x y = 1 ↔ x * y = y * x := by
  rw [show (x * y = y * x) ↔ Commute x y from Iff.rfl,
    ← commutatorElement_eq_one_iff_commute (g₁ := x) (g₂ := y)]
  exact ⟨fun hx => by simpa using congrArg Subtype.val hx,
    fun hx => Subtype.ext (by simpa using hx)⟩

theorem commCenter_mul_left (x y t : P) :
    commCenter hcl (x * y) t = commCenter hcl x t * commCenter hcl y t :=
  Subtype.ext (by simpa using commutatorElement_mul_left_of_commutator_le_center hcl x y t)

theorem commCenter_mul_right (x y t : P) :
    commCenter hcl x (y * t) = commCenter hcl x y * commCenter hcl x t :=
  Subtype.ext (by simpa using commutatorElement_mul_right_of_commutator_le_center hcl x y t)

theorem normal_of_commutator_le_center (hcl : commutator P ≤ Subgroup.center P)
    (hZB : Subgroup.center P ≤ B) : B.Normal :=
  Subgroup.Normal.of_commutator_le P (hcl.trans hZB)

def conjHom (hBn : B.Normal) (t : P) : ↥B →* ↥B :=
  MonoidHom.mk' (fun b => ⟨t⁻¹ * (b : P) * t, hBn.conj_mem' _ b.2 t⟩) fun b₁ b₂ =>
    Subtype.ext (by push_cast; group)

@[simp] theorem coe_conjHom_apply (hBn : B.Normal) (t : P) (b : ↥B) :
    ((conjHom hBn t b : ↥B) : P) = t⁻¹ * (b : P) * t := (rfl)

def centerChar (hZB : Subgroup.center P ≤ B) (lam : ↥B →* kˣ) : ↥(Subgroup.center P) →* kˣ :=
  lam.comp (Subgroup.inclusion hZB)

variable {hZB : Subgroup.center P ≤ B} {lam mu : ↥B →* kˣ}

theorem centerChar_apply (z : ↥(Subgroup.center P)) :
    centerChar hZB lam z = lam ⟨(z : P), hZB z.2⟩ := (rfl)

theorem centerChar_injective (hP : IsExtraspecial p P) (hnt : centerChar hZB lam ≠ 1) :
    Function.Injective (centerChar hZB lam) := by
  have : Fact (Nat.card ↥(Subgroup.center P)).Prime := ⟨hP.card_center ▸ hP.prime⟩
  rcases Subgroup.eq_bot_or_eq_top_of_prime_card (centerChar hZB lam).ker with h | h
  · exact (MonoidHom.ker_eq_bot_iff _).1 h
  · exact absurd (MonoidHom.ker_eq_top_iff.1 h) hnt

def commChar (hcl : commutator P ≤ Subgroup.center P) (hZB : Subgroup.center P ≤ B)
    (lam : ↥B →* kˣ) (t : P) : ↥B →* kˣ :=
  MonoidHom.mk' (fun b => centerChar hZB lam (commCenter hcl (b : P) t)) fun b₁ b₂ => by
    push_cast
    rw [commCenter_mul_left, map_mul]

theorem commChar_apply (t : P) (b : ↥B) :
    commChar hcl hZB lam t b = centerChar hZB lam (commCenter hcl (b : P) t) := (rfl)

theorem commChar_eq_one_iff {t : P} {b : ↥B} (hinj : Function.Injective (centerChar hZB lam)) :
    commChar hcl hZB lam t b = 1 ↔ (b : P) * t = t * (b : P) := by
  rw [commChar_apply, ← commCenter_eq_one_iff (hcl := hcl)]
  exact ⟨fun h => hinj (by rw [h, map_one]), fun h => by rw [h, map_one]⟩

theorem commChar_eq_one_of_mem_center {t : P} {b : ↥B} (hb : (b : P) ∈ Subgroup.center P) :
    commChar hcl hZB lam t b = 1 := by
  rw [commChar_apply, commCenter_eq_one_left hb, map_one]

theorem subgroupOf_center_le_ker_commChar (t : P) :
    (Subgroup.center P).subgroupOf B ≤ (commChar hcl hZB lam t).ker := fun _ hb =>
  commChar_eq_one_of_mem_center (Subgroup.mem_subgroupOf.1 hb)

theorem apply_conjHom (hBn : B.Normal) (t : P) (b : ↥B) :
    lam (conjHom hBn t b) = commChar hcl hZB lam t b * lam b := by
  have hb : conjHom hBn t b = b * ⟨(commCenter hcl (b : P) t : P),
      hZB (commCenter hcl (b : P) t).2⟩ := by
    refine Subtype.ext ?_
    rw [coe_conjHom_apply]
    push_cast
    rw [coe_commCenter, ← inv_mul_inv_mul_mul_eq_commutatorElement_of_mem_center
      (commutatorElement_mem_center_of_commutator_le_center hcl (b : P) t)]
    group
  rw [hb, map_mul, mul_comm, commChar_apply, centerChar_apply]

abbrev QuotientCenterSubgroup (B : Subgroup P) : Type u :=
  ↥B ⧸ (Subgroup.center P).subgroupOf B

def conjChar (hcl : commutator P ≤ Subgroup.center P) (hZB : Subgroup.center P ≤ B)
    (lam : ↥B →* kˣ) (t : P) : QuotientCenterSubgroup B →* kˣ :=
  QuotientGroup.lift _ (commChar hcl hZB lam t) (subgroupOf_center_le_ker_commChar t)

theorem conjChar_mk (t : P) (b : ↥B) :
    conjChar hcl hZB lam t (QuotientGroup.mk b) = commChar hcl hZB lam t b := (rfl)

def conjCharHom (hcl : commutator P ≤ Subgroup.center P) (hZB : Subgroup.center P ≤ B)
    (lam : ↥B →* kˣ) : P →* (QuotientCenterSubgroup B →* kˣ) where
  toFun := conjChar hcl hZB lam
  map_one' := by
    refine MonoidHom.ext fun q => ?_
    induction q using QuotientGroup.induction_on with
    | H b =>
      rw [conjChar_mk, commChar_apply, commCenter_one_right, map_one, MonoidHom.one_apply]
  map_mul' t₁ t₂ := by
    refine MonoidHom.ext fun q => ?_
    induction q using QuotientGroup.induction_on with
    | H b =>
      rw [MonoidHom.mul_apply, conjChar_mk, conjChar_mk, conjChar_mk, commChar_apply,
        commChar_apply, commChar_apply, commCenter_mul_right, map_mul]

theorem conjCharHom_apply (t : P) :
    conjCharHom hcl hZB lam t = conjChar hcl hZB lam t := (rfl)

theorem mem_ker_conjCharHom_iff (hBn : B.Normal) {t : P} :
    t ∈ (conjCharHom hcl hZB lam).ker ↔ ∀ b : ↥B, lam (conjHom hBn t b) = lam b := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h b
    have hq := congrArg (fun f => f (QuotientGroup.mk b)) h
    rw [conjCharHom_apply, conjChar_mk, MonoidHom.one_apply] at hq
    rw [apply_conjHom (hcl := hcl) (hZB := hZB) hBn, hq, one_mul]
  · intro h
    refine MonoidHom.ext fun q => ?_
    induction q using QuotientGroup.induction_on with
    | H b =>
      rw [conjCharHom_apply, conjChar_mk, MonoidHom.one_apply]
      have hb := h b
      rw [apply_conjHom (hcl := hcl) (hZB := hZB) hBn] at hb
      exact mul_right_cancel (by rw [hb, one_mul])

theorem ker_conjCharHom (hinj : Function.Injective (centerChar hZB lam)) :
    (conjCharHom hcl hZB lam).ker = Subgroup.centralizer (B : Set P) := by
  ext t
  simp only [MonoidHom.mem_ker, Subgroup.mem_centralizer_iff]
  constructor
  · intro h b hb
    have hq := congrArg (fun f => f (QuotientGroup.mk (⟨b, hb⟩ : ↥B))) h
    rw [conjCharHom_apply, conjChar_mk, MonoidHom.one_apply] at hq
    exact (commChar_eq_one_iff hinj).1 hq
  · intro h
    refine MonoidHom.ext fun q => ?_
    induction q using QuotientGroup.induction_on with
    | H b =>
      rw [conjCharHom_apply, conjChar_mk, MonoidHom.one_apply,
        (commChar_eq_one_iff hinj).2 (h _ b.2)]

theorem card_charGroup_quotientCenterSubgroup (hP : IsExtraspecial p P)
    (hBab : IsMulCommutative ↥B) [IsAlgClosed k] (hp : (p : k) ≠ 0) :
    Nat.card (QuotientCenterSubgroup B →* kˣ) = (Subgroup.center P).relIndex B := by
  have := hP.finite
  have : NeZero p := ⟨hP.prime.ne_zero⟩
  have : NeZero ((p : ℕ) : k) := ⟨hp⟩
  let _ : CommGroup ↥B := IsMulCommutative.instCommGroup
  have hexp : ∀ q : QuotientCenterSubgroup B, q ^ p = 1 := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H b =>
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      push_cast
      exact hP.pow_mem_center _
  have : HasEnoughRootsOfUnity k p := IsSepClosed.hasEnoughRootsOfUnity k p
  have : HasEnoughRootsOfUnity k (Monoid.exponent (QuotientCenterSubgroup B)) :=
    HasEnoughRootsOfUnity.of_dvd k (Monoid.exponent_dvd_of_forall_pow_eq_one hexp)
  rw [CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity (QuotientCenterSubgroup B) k]
  exact (Subgroup.index_eq_card _).symm

theorem conjCharHom_surjective (hP : IsExtraspecial p P) (hBab : IsMulCommutative ↥B)
    (hCB : Subgroup.centralizer (B : Set P) = B) (hPB : B.index = p ^ n)
    (hBZ : (Subgroup.center P).relIndex B = p ^ n) [IsAlgClosed k] (hp : (p : k) ≠ 0)
    (hnt : centerChar hZB lam ≠ 1) :
    Function.Surjective (conjCharHom hcl hZB lam) := by
  have htot : Nat.card (QuotientCenterSubgroup B →* kˣ) = p ^ n := by
    rw [card_charGroup_quotientCenterSubgroup hP hBab hp, hBZ]
  have : Finite (QuotientCenterSubgroup B →* kˣ) :=
    Nat.finite_of_card_ne_zero (by rw [htot]; exact pow_ne_zero _ hP.prime.ne_zero)
  have hrange : Nat.card ↥(conjCharHom hcl hZB lam).range = p ^ n := by
    rw [← Subgroup.index_ker, ker_conjCharHom (centerChar_injective hP hnt), hCB, hPB]
  exact MonoidHom.range_eq_top.1 (Subgroup.eq_top_of_card_eq _ (by rw [hrange, htot]))

def ratioChar (hZB : Subgroup.center P ≤ B) (lam mu : ↥B →* kˣ)
    (hlm : centerChar hZB lam = centerChar hZB mu) : QuotientCenterSubgroup B →* kˣ :=
  QuotientGroup.lift _ (mu * lam⁻¹) <| by
    intro b hb
    have hb' : (b : P) ∈ Subgroup.center P := Subgroup.mem_subgroupOf.1 hb
    have h1 : lam b = mu b := by
      have := congrArg (fun f => f ⟨(b : P), hb'⟩) hlm
      simpa [centerChar_apply] using this
    simp [MonoidHom.mem_ker, h1]

theorem ratioChar_mk (hlm : centerChar hZB lam = centerChar hZB mu) (b : ↥B) :
    ratioChar hZB lam mu hlm (QuotientGroup.mk b) = mu b * (lam b)⁻¹ := (rfl)

theorem exists_conj_apply_eq_of_centerChar_eq (hP : IsExtraspecial p P)
    (hBab : IsMulCommutative ↥B) (hCB : Subgroup.centralizer (B : Set P) = B)
    (hPB : B.index = p ^ n) (hBZ : (Subgroup.center P).relIndex B = p ^ n)
    [IsAlgClosed k] (hp : (p : k) ≠ 0)
    (hlm : centerChar hZB lam = centerChar hZB mu) (hnt : centerChar hZB lam ≠ 1) :
    ∃ t : P, ∀ (b : P) (hb : b ∈ B) (hb' : t⁻¹ * b * t ∈ B),
      mu ⟨b, hb⟩ = lam ⟨t⁻¹ * b * t, hb'⟩ := by
  have hcl := hP.commutator_le_center
  have hBn := normal_of_commutator_le_center hcl hZB
  obtain ⟨t, ht⟩ := conjCharHom_surjective (hcl := hcl) (hZB := hZB) (lam := lam) hP hBab hCB
    hPB hBZ hp hnt (ratioChar hZB lam mu hlm)
  refine ⟨t, fun b hb hb' => ?_⟩
  have hq := congrArg (fun f => f (QuotientGroup.mk (⟨b, hb⟩ : ↥B))) ht
  rw [conjCharHom_apply, conjChar_mk, ratioChar_mk] at hq
  have hkey : lam (conjHom hBn t ⟨b, hb⟩) = mu ⟨b, hb⟩ := by
    rw [apply_conjHom (hcl := hcl) (hZB := hZB) hBn, hq]
    group
  rw [← hkey]
  rfl

theorem setOf_forall_conj_apply_eq_eq_coe (hP : IsExtraspecial p P)
    (hCB : Subgroup.centralizer (B : Set P) = B) (hnt : centerChar hZB lam ≠ 1) :
    {t : P | ∀ (b : P) (hb : b ∈ B) (hb' : t⁻¹ * b * t ∈ B),
      lam ⟨t⁻¹ * b * t, hb'⟩ = lam ⟨b, hb⟩} = (B : Set P) := by
  have hcl := hP.commutator_le_center
  have hBn := normal_of_commutator_le_center hcl hZB
  have hker : (conjCharHom hcl hZB lam).ker = B := by
    rw [ker_conjCharHom (centerChar_injective hP hnt), hCB]
  ext t
  change (∀ (b : P) (hb : b ∈ B) (hb' : t⁻¹ * b * t ∈ B),
      lam ⟨t⁻¹ * b * t, hb'⟩ = lam ⟨b, hb⟩) ↔ t ∈ (B : Set P)
  rw [SetLike.mem_coe]
  constructor
  · intro h
    have hmem : t ∈ (conjCharHom hcl hZB lam).ker :=
      (mem_ker_conjCharHom_iff (hcl := hcl) hBn).2 fun b => h _ b.2 (hBn.conj_mem' _ b.2 t)
    rwa [hker] at hmem
  · intro h b hb _
    have hmem : t ∈ (conjCharHom hcl hZB lam).ker := by rwa [hker]
    exact (mem_ker_conjCharHom_iff (hcl := hcl) hBn).1 hmem ⟨b, hb⟩

end

end CFSG.FeitThompson
