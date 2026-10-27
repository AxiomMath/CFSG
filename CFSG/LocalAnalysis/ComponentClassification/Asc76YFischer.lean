module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76YS4
public import CFSG.Fischer.Uniq.Connected
import CFSG.LocalAnalysis.ZStar
import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.ComponentClassification.Asc76.Sec4

open Subgroup CFSG.Fischer CFSG.Blueprint.Fischer SimpleGraph

section Fischer

variable {X : Type} [Group X]

theorem isConj_of_not_connected [Finite X] {D : Set X} (hD2 : ∀ d ∈ D, orderOf d = 2)
    (hD3 : ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ≤ 3)
    (hdis : ¬ (commGraph D).Connected) {d e : X} (hd : d ∈ D) (he : e ∈ D) : IsConj d e := by
  have hsq : ∀ a ∈ D, a * a = 1 := fun a ha => by
    rw [← sq, ← hD2 a ha, pow_orderOf_eq_one]
  by_contra hde
  have hcomm : ∀ a ∈ D, ∀ b ∈ D, IsConj d a → ¬ IsConj d b → a * b = b * a := by
    intro a ha b hb hda hdb
    by_contra hab
    have hbr := braid_of_orderOf_le_three (hsq a ha) (hsq b hb) (hD3 a ha b hb) hab
    have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hsq b hb)
    have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hsq a ha)
    apply hdb
    have h1 : IsConj d (b * a * b) := hda.trans (isConj_iff.2 ⟨b, by rw [hbi]⟩)
    have h2 : IsConj b (a * b * a) := isConj_iff.2 ⟨a, by rw [hai]⟩
    rw [← hbr] at h1
    exact h1.trans h2.symm
  apply hdis
  refine (connected_iff_exists_forall_reachable _).2 ⟨⟨d, hd⟩, fun v => ?_⟩
  have hadj : ∀ a b : D, IsConj d a → ¬ IsConj d b → (commGraph D).Adj a b := by
    intro a b ha hb
    refine commGraph_adj_iff.2 ⟨fun h => hb (h ▸ ha), hcomm a a.2 b b.2 ha hb⟩
  by_cases hv : IsConj d v
  · exact (hadj ⟨d, hd⟩ ⟨e, he⟩ (IsConj.refl d) hde).reachable.trans
      (hadj v ⟨e, he⟩ hv hde).reachable.symm
  · exact (hadj ⟨d, hd⟩ v (IsConj.refl d) hv).reachable

theorem pair_of_not_connected [Finite X] {D : Set X} {d : X} (hd : d ∈ D)
    (hD2 : ∀ d ∈ D, orderOf d = 2) (hDn : ∀ d ∈ D, ∀ x : X, x * d * x⁻¹ ∈ D)
    (hD3 : ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ≤ 3) (hgen : closure D = ⊤)
    (hdis : ¬ (commGraph D).Connected) : Pair X D := by
  refine ⟨inferInstance, ⟨d, ?_⟩, hD2, ?_, hgen⟩
  · ext x
    constructor
    · exact fun hx => isConj_of_not_connected hD2 hD3 hdis hd hx
    · intro h
      obtain ⟨c, rfl⟩ := isConj_iff.1 h
      exact hDn d hd c
  · intro e he f hf
    have h1 := hD3 e he f hf
    have h2 := orderOf_pos (e * f)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    omega

def d6ToPermFun : DihedralGroup 3 → Equiv.Perm (Fin 3)
  | .r i => finRotate 3 ^ (i.val)
  | .sr i => Equiv.swap 1 2 * finRotate 3 ^ (i.val)

theorem d6ToPermFun_mul :
    ∀ x y : DihedralGroup 3, d6ToPermFun (x * y) = d6ToPermFun x * d6ToPermFun y := by
  decide

theorem d6ToPermFun_bijective : Function.Bijective d6ToPermFun := by
  refine ⟨?_, ?_⟩
  · intro x y h
    revert x y
    decide
  · decide

noncomputable def d6EquivPerm : DihedralGroup 3 ≃* Equiv.Perm (Fin 3) :=
  MulEquiv.ofBijective (MonoidHom.mk' d6ToPermFun d6ToPermFun_mul) d6ToPermFun_bijective

variable {D : Set X} (hP : Pair X D)
include hP

theorem compPerm_eq_of_reachable {a b : D} (h : (commGraph D).Reachable a b) :
    Pair.compPerm hP a = Pair.compPerm hP b := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => rfl
  | cons hadj _ ih => exact (Pair.compPerm_eq_of_adj hP hadj).trans ih

omit hP in
abbrev compR (hP : Pair X D) : X →* (Pair.compPerm hP).range := (Pair.compPerm hP).rangeRestrict

theorem r_eq_of_reachable {a b : D} (h : (commGraph D).Reachable a b) : compR hP a = compR hP b :=
  Subtype.ext (compPerm_eq_of_reachable hP h)

theorem r_mul_ne_of_not_reachable {a b : D} (h : ¬ (commGraph D).Reachable a b) :
    compR hP a * compR hP b ≠ compR hP b * compR hP a := fun he =>
  Pair.compPerm_mul_ne hP h (congrArg Subtype.val he)

variable [Finite X]

omit hP [Finite X] in
theorem exists_not_reachable (hdis : ¬ (commGraph D).Connected) (a : D) :
    ∃ b : D, ¬ (commGraph D).Reachable a b := by
  by_contra! hall
  exact hdis ((connected_iff_exists_forall_reachable _).2 ⟨a, hall⟩)

theorem exists_odd_normal_image (hdis : ¬ (commGraph D).Connected) {d : X} (hd : d ∈ D) :
    ∃ N : Subgroup (Pair.compPerm hP).range, N.Normal ∧ Odd (Nat.card N) ∧
      ∀ e ∈ D, compR hP e * compR hP d ∈ N := by
  classical
  let := Fintype.ofFinite (Pair.compPerm hP).range
  have hdd : compR hP d * compR hP d = 1 := by rw [← map_mul, Pair.mul_self hP hd, map_one]
  obtain ⟨b, hb⟩ := exists_not_reachable hdis ⟨d, hd⟩
  have ht1 : compR hP d ≠ 1 := by
    intro h1
    apply r_mul_ne_of_not_reachable hP hb
    change compR hP d * compR hP b = compR hP b * compR hP d
    rw [h1, one_mul, mul_one]
  have hiso : ∀ g : (Pair.compPerm hP).range,
      (g * compR hP d * g⁻¹) * compR hP d = compR hP d * (g * compR hP d * g⁻¹) →
      g * compR hP d * g⁻¹ = compR hP d := by
    intro g hg
    obtain ⟨x, rfl⟩ := (Pair.compPerm hP).rangeRestrict_surjective g
    have hmem : x * d * x⁻¹ ∈ D := Pair.conj_mem hP hd x
    have hrx : compR hP x * compR hP d * (compR hP x)⁻¹ = compR hP (x * d * x⁻¹) := by simp
    rw [hrx] at hg ⊢
    by_contra hne
    by_cases hreach : (commGraph D).Reachable ⟨d, hd⟩ ⟨x * d * x⁻¹, hmem⟩
    · exact hne (r_eq_of_reachable hP hreach).symm
    · exact r_mul_ne_of_not_reachable hP hreach hg.symm
  obtain ⟨N, hN, hNodd, hNt⟩ := CFSG.ZStar.glauberman_zStar _ (compR hP d) ht1 hdd hiso
  refine ⟨N, hN, hNodd, fun e he => ?_⟩
  obtain ⟨c, rfl⟩ := isConj_iff.1 (Pair.isConj hP hd he)
  have h1 := hNt (compR hP c)
  have hdi : (compR hP d)⁻¹ = compR hP d := inv_eq_of_mul_eq_one_right hdd
  rw [hdi] at h1
  simpa using h1

omit [Finite X] in
def prodGroup (hP : Pair X D) : Subgroup (Pair.compPerm hP).range :=
  closure {m | ∃ e ∈ D, ∃ f ∈ D, m = compR hP e * compR hP f}

omit [Finite X] in
theorem mem_prodGroup {e f : X} (he : e ∈ D) (hf : f ∈ D) :
    compR hP e * compR hP f ∈ prodGroup hP :=
  subset_closure ⟨e, he, f, hf, rfl⟩

omit [Finite X] in
theorem prodGroup_normal : (prodGroup hP).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨x, rfl⟩ := (Pair.compPerm hP).rangeRestrict_surjective g
  induction hn using closure_induction with
  | mem m hm =>
    obtain ⟨e, he, f, hf, rfl⟩ := hm
    have : compR hP x * (compR hP e * compR hP f) * (compR hP x)⁻¹ =
        compR hP (x * e * x⁻¹) * compR hP (x * f * x⁻¹) := by simp [mul_assoc]
    rw [this]
    exact mem_prodGroup hP (Pair.conj_mem hP he x) (Pair.conj_mem hP hf x)
  | one => simp
  | mul a b _ _ ha hb =>
    rw [show compR hP x * (a * b) * (compR hP x)⁻¹ =
      compR hP x * a * (compR hP x)⁻¹ * (compR hP x * b * (compR hP x)⁻¹) by group]
    exact mul_mem ha hb
  | inv a _ ha =>
    rw [show compR hP x * a⁻¹ * (compR hP x)⁻¹ = (compR hP x * a * (compR hP x)⁻¹)⁻¹ by group]
    exact inv_mem ha

omit [Finite X] in
theorem compR_mul_self {e : X} (he : e ∈ D) : compR hP e * compR hP e = 1 := by
  rw [← map_mul, Pair.mul_self hP he, map_one]

omit [Finite X] in
theorem prodGroup_le {N : Subgroup (Pair.compPerm hP).range} {d : X} (hd : d ∈ D)
    (hN : ∀ e ∈ D, compR hP e * compR hP d ∈ N) : prodGroup hP ≤ N := by
  refine (closure_le _).2 ?_
  rintro _ ⟨e, he, f, hf, rfl⟩
  have h1 := mul_mem (hN e he) (inv_mem (hN f hf))
  rwa [mul_inv_rev, inv_eq_of_mul_eq_one_right (compR_mul_self hP hd),
    inv_eq_of_mul_eq_one_right (compR_mul_self hP hf), mul_assoc, ← mul_assoc (compR hP d),
    compR_mul_self hP hd, one_mul] at h1

omit [Finite X] in
theorem mem_prodGroup_or {d : X} (hd : d ∈ D) (x : X) :
    compR hP x ∈ prodGroup hP ∨ compR hP x * compR hP d ∈ prodGroup hP := by
  have hgen : x ∈ closure D := by rw [Pair.closure_eq hP]; exact mem_top x
  have hn := prodGroup_normal hP
  induction hgen using closure_induction_left with
  | one => left; simp
  | mul_left e he y _ ih =>
    rcases ih with h | h
    · right
      have := mul_mem (mem_prodGroup hP he hd)
        (hn.conj_mem _ h (compR hP d))
      rwa [inv_eq_of_mul_eq_one_right (compR_mul_self hP hd), show compR hP e * compR hP d *
        (compR hP d * compR hP y * compR hP d) = compR hP e * (compR hP d * compR hP d) *
        compR hP y * compR hP d by group, compR_mul_self hP hd, mul_one, ← map_mul] at this
    · left
      have := mul_mem (mem_prodGroup hP he hd) (hn.conj_mem _ h (compR hP d))
      rwa [inv_eq_of_mul_eq_one_right (compR_mul_self hP hd), show compR hP e * compR hP d *
        (compR hP d * (compR hP y * compR hP d) * compR hP d) =
        compR hP e * (compR hP d * compR hP d) * compR hP y * (compR hP d * compR hP d) by group,
        compR_mul_self hP hd, mul_one, mul_one, ← map_mul] at this
  | inv_mul_cancel e he y hy ih =>
    rw [Pair.inv_eq hP he]
    rcases ih with h | h
    · right
      have := mul_mem (mem_prodGroup hP he hd)
        (hn.conj_mem _ h (compR hP d))
      rwa [inv_eq_of_mul_eq_one_right (compR_mul_self hP hd), show compR hP e * compR hP d *
        (compR hP d * compR hP y * compR hP d) = compR hP e * (compR hP d * compR hP d) *
        compR hP y * compR hP d by group, compR_mul_self hP hd, mul_one, ← map_mul] at this
    · left
      have := mul_mem (mem_prodGroup hP he hd) (hn.conj_mem _ h (compR hP d))
      rwa [inv_eq_of_mul_eq_one_right (compR_mul_self hP hd), show compR hP e * compR hP d *
        (compR hP d * (compR hP y * compR hP d) * compR hP d) =
        compR hP e * (compR hP d * compR hP d) * compR hP y * (compR hP d * compR hP d) by group,
        compR_mul_self hP hd, mul_one, mul_one, ← map_mul] at this

section Quotient

variable (hdis : ¬ (commGraph D).Connected) {d : X} (hd : d ∈ D)
include hdis hd

theorem odd_card_prodGroup : Odd (Nat.card (prodGroup hP)) := by
  obtain ⟨N, -, hNodd, hNt⟩ := exists_odd_normal_image hP hdis hd
  exact hNodd.of_dvd_nat (Subgroup.card_dvd_of_le (prodGroup_le hP hd hNt))

omit [Finite X] in
theorem prodGroup_ne_bot : prodGroup hP ≠ ⊥ := by
  obtain ⟨b, hb⟩ := exists_not_reachable hdis ⟨d, hd⟩
  intro hbot
  have hmem := mem_prodGroup hP b.2 hd
  rw [hbot, mem_bot] at hmem
  apply r_mul_ne_of_not_reachable hP hb
  have hbd : compR hP b = compR hP d := by
    have := eq_inv_of_mul_eq_one_left hmem
    rwa [inv_eq_of_mul_eq_one_right (compR_mul_self hP hd)] at this
  change compR hP d * compR hP b = compR hP b * compR hP d
  rw [hbd]

theorem pow_three_compR {e f : X} (he : e ∈ D) (hf : f ∈ D) :
    (compR hP e * compR hP f) ^ 3 = 1 := by
  have h1 : orderOf (compR hP e * compR hP f) ∣ orderOf (e * f) := by
    rw [← map_mul]; exact orderOf_map_dvd _ _
  have h2 : Odd (orderOf (compR hP e * compR hP f)) := by
    have := orderOf_dvd_natCard (⟨_, mem_prodGroup hP he hf⟩ : prodGroup hP)
    rw [Subgroup.orderOf_mk] at this
    exact (odd_card_prodGroup hP hdis hd).of_dvd_nat this
  have h3 := Pair.orderOf_mul_mem hP he hf
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h3
  have h4 : orderOf (compR hP e * compR hP f) ∣ 3 := by
    rcases h3 with h | h | h
    · rw [h] at h1; exact h1.trans (one_dvd 3)
    · rw [h] at h1
      rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h' | h'
      · rw [h']; exact one_dvd 3
      · rw [h'] at h2; exact absurd h2 (by decide)
    · rw [h] at h1; exact h1
  exact orderOf_dvd_iff_pow_eq_one.1 h4

theorem exists_hom_zmod_three : ∃ ψ : prodGroup hP →* Multiplicative (ZMod 3),
    Function.Surjective ψ ∧ ∀ m : prodGroup hP,
      ψ ((@MulAut.conjNormal _ _ (prodGroup hP) (prodGroup_normal hP) (compR hP d)) m) =
        ψ m⁻¹ := by
  classical
  have hn := prodGroup_normal hP
  have hodd := odd_card_prodGroup hP hdis hd
  have hsol : Group.IsSolvable (prodGroup hP) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have hnt : Nontrivial (prodGroup hP) :=
    (Subgroup.nontrivial_iff_ne_bot _).2 (prodGroup_ne_bot hP hdis hd)
  have hlt := Group.IsSolvable.commutator_lt_top_of_nontrivial (prodGroup hP)
  have hA : Nontrivial (Abelianization (prodGroup hP)) := QuotientGroup.nontrivial_iff.2 hlt.ne
  have hexp : ∀ a : Abelianization (prodGroup hP), a ^ 3 = 1 := by
    intro a
    obtain ⟨⟨x, hx⟩, rfl⟩ : ∃ m, Abelianization.of m = a := QuotientGroup.mk_surjective a
    induction hx using closure_induction with
    | mem y hy =>
      obtain ⟨e, he, f, hf, rfl⟩ := hy
      rw [← map_pow]
      have : (⟨compR hP e * compR hP f, subset_closure ⟨e, he, f, hf, rfl⟩⟩ :
          prodGroup hP) ^ 3 = 1 := Subtype.ext (by simpa using pow_three_compR hP hdis hd he hf)
      rw [this, map_one]
    | one => rw [show (⟨1, _⟩ : prodGroup hP) = 1 from rfl, map_one, one_pow]
    | mul y z hy hz ihy ihz =>
      rw [show (⟨y * z, mul_mem hy hz⟩ : prodGroup hP) = ⟨y, hy⟩ * ⟨z, hz⟩ from rfl, map_mul,
        mul_pow, ihy, ihz, one_mul]
    | inv y hy ih =>
      rw [show (⟨y⁻¹, inv_mem hy⟩ : prodGroup hP) = (⟨y, hy⟩)⁻¹ from rfl, map_inv, inv_pow, ih,
        inv_one]
  obtain ⟨ι, hι, n, hn1, ⟨e⟩⟩ :=
    CommGroup.equiv_prod_multiplicative_zmod_of_finite (Abelianization (prodGroup hP))
  have hne : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    obtain ⟨a, b, hab⟩ := hA
    exact hab (e.injective (funext fun i => (h.elim i)))
  obtain ⟨i⟩ := hne
  let χ₀ : Abelianization (prodGroup hP) →* Multiplicative (ZMod (n i)) :=
    (Pi.evalMonoidHom _ i).comp e.toMonoidHom
  have hχ₀ : Function.Surjective χ₀ := by
    intro y
    refine ⟨e.symm (Pi.mulSingle i y), ?_⟩
    simp [χ₀]
  have h3 : n i = 3 := by
    obtain ⟨a, ha⟩ := hχ₀ (Multiplicative.ofAdd 1)
    have h1 := congrArg χ₀ (hexp a)
    rw [map_pow, map_one, ha, ← ofAdd_nsmul] at h1
    have h2 : ((3 : ℕ) : ZMod (n i)) = 0 := by
      rw [← nsmul_one]
      exact congrArg Multiplicative.toAdd h1
    rw [ZMod.natCast_eq_zero_iff] at h2
    have := hn1 i
    rcases (Nat.dvd_prime Nat.prime_three).1 h2 with h | h <;> omega
  let χ : Abelianization (prodGroup hP) →* Multiplicative (ZMod 3) :=
    ((ZMod.ringEquivCongr h3).toAddEquiv.toMultiplicative.toMonoidHom).comp χ₀
  have hχ : Function.Surjective χ :=
    (ZMod.ringEquivCongr h3).toAddEquiv.toMultiplicative.surjective.comp hχ₀
  refine ⟨χ.comp Abelianization.of, hχ.comp fun a => QuotientGroup.mk_surjective a, ?_⟩
  have hdd := compR_mul_self hP hd
  have hdi : (compR hP d)⁻¹ = compR hP d := inv_eq_of_mul_eq_one_right hdd
  rintro ⟨x, hx⟩
  induction hx using closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hy
    set ga : prodGroup hP := ⟨_, mem_prodGroup hP ha hd⟩
    set gb : prodGroup hP := ⟨_, mem_prodGroup hP hb hd⟩
    have hm : (⟨compR hP a * compR hP b, subset_closure ⟨a, ha, b, hb, rfl⟩⟩ : prodGroup hP) =
        ga * gb⁻¹ := by
      apply Subtype.ext
      simp only [ga, gb, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, hdi,
        inv_eq_of_mul_eq_one_right (compR_mul_self hP hb)]
      rw [show compR hP a * compR hP d * (compR hP d * compR hP b) =
        compR hP a * (compR hP d * compR hP d) * compR hP b by group, hdd, mul_one]
    have hc : (@MulAut.conjNormal _ _ (prodGroup hP) hn (compR hP d))
        ⟨compR hP a * compR hP b, subset_closure ⟨a, ha, b, hb, rfl⟩⟩ = ga⁻¹ * gb := by
      apply Subtype.ext
      simp only [MulAut.conjNormal_apply, ga, gb, Subgroup.coe_mul, Subgroup.coe_inv,
        mul_inv_rev, hdi, inv_eq_of_mul_eq_one_right (compR_mul_self hP ha)]
      group
    rw [hc, hm, mul_inv_rev, inv_inv, map_mul, map_mul]
    exact mul_comm _ _
  | one =>
    rw [show (⟨1, _⟩ : prodGroup hP) = 1 from rfl, map_one, inv_one]
  | mul y z hy hz ihy ihz =>
    rw [show (⟨y * z, mul_mem hy hz⟩ : prodGroup hP) = ⟨y, hy⟩ * ⟨z, hz⟩ from rfl, map_mul,
      map_mul, ihy, ihz, mul_inv_rev, map_mul]
    exact mul_comm _ _
  | inv y hy ih =>
    rw [show (⟨y⁻¹, inv_mem hy⟩ : prodGroup hP) = (⟨y, hy⟩)⁻¹ from rfl, map_inv, inv_inv]
    apply mul_right_cancel (b := (χ.comp Abelianization.of)
      ((@MulAut.conjNormal _ _ (prodGroup hP) hn (compR hP d)) ⟨y, hy⟩))
    rw [← map_mul, inv_mul_cancel, map_one, ih, ← map_mul, mul_inv_cancel, map_one]

omit [Finite X] in
theorem compR_ne_one : compR hP d ≠ 1 := by
  obtain ⟨b, hb⟩ := exists_not_reachable hdis ⟨d, hd⟩
  intro h1
  apply r_mul_ne_of_not_reachable hP hb
  change compR hP d * compR hP b = compR hP b * compR hP d
  rw [h1, one_mul, mul_one]

theorem compR_not_mem_prodGroup : compR hP d ∉ prodGroup hP := by
  intro h
  have h2 : orderOf (compR hP d) = 2 :=
    orderOf_eq_prime (by rw [sq, compR_mul_self hP hd]) (compR_ne_one hP hdis hd)
  have := orderOf_dvd_natCard (⟨_, h⟩ : prodGroup hP)
  rw [Subgroup.orderOf_mk, h2] at this
  exact (Nat.not_even_iff_odd.2 (odd_card_prodGroup hP hdis hd)) (even_iff_two_dvd.2 this)

omit hdis [Finite X] in
theorem mem_prodGroup_or' (h : (Pair.compPerm hP).range) :
    h ∈ prodGroup hP ∨ h * compR hP d ∈ prodGroup hP := by
  obtain ⟨x, rfl⟩ := (Pair.compPerm hP).rangeRestrict_surjective h
  exact mem_prodGroup_or hP hd x

theorem exists_surjective_dihedralGroup_three :
    ∃ Φ : (Pair.compPerm hP).range →* DihedralGroup 3, Function.Surjective Φ := by
  classical
  obtain ⟨ψ, hψs, hψi⟩ := exists_hom_zmod_three hP hdis hd
  have htt : compR hP d * compR hP d = 1 := compR_mul_self hP hd
  have hti : (compR hP d)⁻¹ = compR hP d := inv_eq_of_mul_eq_one_right htt
  have hn := prodGroup_normal hP
  have hor := mem_prodGroup_or' hP hd
  have htM := compR_not_mem_prodGroup hP hdis hd
  set t := compR hP d with htdef
  let α : (Pair.compPerm hP).range → ZMod 3 := fun h =>
    if hh : h ∈ prodGroup hP then Multiplicative.toAdd (ψ ⟨h, hh⟩) else 0
  have hα : ∀ (h : (Pair.compPerm hP).range) (hh : h ∈ prodGroup hP),
      α h = Multiplicative.toAdd (ψ ⟨h, hh⟩) := fun h hh => by simp only [α, hh, ↓reduceDIte]
  have hα_mul : ∀ x y : (Pair.compPerm hP).range, x ∈ prodGroup hP → y ∈ prodGroup hP →
      α (x * y) = α x + α y := by
    intro x y hx hy
    rw [hα _ (mul_mem hx hy), hα x hx, hα y hy, ← toAdd_mul, ← map_mul]
    rfl
  have hα_conj : ∀ x : (Pair.compPerm hP).range, x ∈ prodGroup hP →
      α (t * x * t) = - α x := by
    intro x hx
    have hx' : t * x * t ∈ prodGroup hP := by simpa [hti] using hn.conj_mem x hx t
    have h1 := hψi ⟨x, hx⟩
    have h2 : (@MulAut.conjNormal _ _ (prodGroup hP) hn t) ⟨x, hx⟩ = ⟨t * x * t, hx'⟩ :=
      Subtype.ext (by rw [MulAut.conjNormal_apply, hti])
    rw [hα _ hx', hα x hx, ← h2, h1, map_inv, toAdd_inv]
  have hmul_not : ∀ x y : (Pair.compPerm hP).range, x ∈ prodGroup hP → y ∉ prodGroup hP →
      x * y ∉ prodGroup hP := fun x y hx hy hxy =>
    hy (by simpa using mul_mem (inv_mem hx) hxy)
  have hmul_not' : ∀ x y : (Pair.compPerm hP).range, x ∉ prodGroup hP → y ∈ prodGroup hP →
      x * y ∉ prodGroup hP := fun x y hx hy hxy =>
    hx (by simpa using mul_mem hxy (inv_mem hy))
  have htconj : ∀ x : (Pair.compPerm hP).range, x ∈ prodGroup hP → t * x * t ∈ prodGroup hP :=
    fun x hx => by simpa [hti] using hn.conj_mem x hx t
  let Φf : (Pair.compPerm hP).range → DihedralGroup 3 := fun h =>
    if h ∈ prodGroup hP then DihedralGroup.r (α h) else DihedralGroup.sr (- α (h * t))
  have hΦ : ∀ h₁ h₂, Φf (h₁ * h₂) = Φf h₁ * Φf h₂ := by
    intro h₁ h₂
    by_cases h₁M : h₁ ∈ prodGroup hP <;> by_cases h₂M : h₂ ∈ prodGroup hP
    · have h12 : h₁ * h₂ ∈ prodGroup hP := mul_mem h₁M h₂M
      simp only [Φf, h12, h₁M, h₂M, ite_true, DihedralGroup.r_mul_r]
      rw [hα_mul _ _ h₁M h₂M]
    · have h12 := hmul_not h₁ h₂ h₁M h₂M
      simp only [Φf, h12, h₁M, h₂M, ite_true, ite_false, DihedralGroup.r_mul_sr]
      rw [mul_assoc, hα_mul _ _ h₁M ((hor _).resolve_left h₂M)]
      congr 1
      abel
    · have h12 := hmul_not' h₁ h₂ h₁M h₂M
      simp only [Φf, h12, h₁M, h₂M, ite_true, ite_false, DihedralGroup.sr_mul_r]
      have e : h₁ * h₂ * t = h₁ * t * (t * h₂ * t) := by
        rw [show h₁ * t * (t * h₂ * t) = h₁ * (t * t) * h₂ * t by group, htt, mul_one]
      rw [e, hα_mul _ _ ((hor _).resolve_left h₁M) (htconj h₂ h₂M), hα_conj h₂ h₂M]
      congr 1
      abel
    · have h1t := (hor h₁).resolve_left h₁M
      have h2t := (hor h₂).resolve_left h₂M
      have e : h₁ * h₂ = h₁ * t * (t * (h₂ * t) * t) := by
        rw [show h₁ * t * (t * (h₂ * t) * t) = h₁ * (t * t) * h₂ * (t * t) by group, htt,
          mul_one, mul_one]
      have h12 : h₁ * h₂ ∈ prodGroup hP := by
        rw [e]
        exact mul_mem h1t (htconj _ h2t)
      simp only [Φf, h12, h₁M, h₂M, ite_true, ite_false, DihedralGroup.sr_mul_sr]
      rw [e, hα_mul _ _ h1t (htconj _ h2t), hα_conj _ h2t]
      congr 1
      abel
  refine ⟨MonoidHom.mk' Φf hΦ, ?_⟩
  rintro (k | k)
  · obtain ⟨m, hm⟩ := hψs (Multiplicative.ofAdd k)
    refine ⟨m, ?_⟩
    simp only [MonoidHom.mk'_apply, Φf, m.2, ite_true]
    rw [hα _ m.2]
    simp [hm]
  · obtain ⟨m, hm⟩ := hψs (Multiplicative.ofAdd (-k))
    have hmt : (m : (Pair.compPerm hP).range) * t ∉ prodGroup hP := hmul_not _ _ m.2 htM
    refine ⟨m * t, ?_⟩
    simp only [MonoidHom.mk'_apply, Φf, hmt, ite_false]
    rw [mul_assoc, htt, mul_one, hα _ m.2]
    simp only [hm, toAdd_ofAdd]
    exact congrArg DihedralGroup.sr (neg_neg k)

theorem exists_surjective_perm_three :
    ∃ φ : X →* Equiv.Perm (Fin 3), Function.Surjective φ := by
  obtain ⟨Φ, hΦ⟩ := exists_surjective_dihedralGroup_three hP hdis hd
  exact ⟨(d6EquivPerm.toMonoidHom.comp Φ).comp (Pair.compPerm hP).rangeRestrict,
    (d6EquivPerm.surjective.comp hΦ).comp (Pair.compPerm hP).rangeRestrict_surjective⟩

end Quotient

omit hP [Finite X] in
theorem closure_normal_of_conj {S : Set X} (hS : ∀ s ∈ S, ∀ g : X, g * s * g⁻¹ ∈ S) :
    (closure S).Normal := by
  refine ⟨fun n hn g => ?_⟩
  induction hn using closure_induction with
  | mem x hx => exact subset_closure (hS x hx g)
  | one => simp
  | mul a b _ _ ha hb =>
    rw [show g * (a * b) * g⁻¹ = g * a * g⁻¹ * (g * b * g⁻¹) by group]
    exact mul_mem ha hb
  | inv a _ ha =>
    rw [show g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ by group]
    exact inv_mem ha

omit [Group X] hP [Finite X] in
theorem eq_bot_of_normal_isPGroup_perm_three {P : Subgroup (Equiv.Perm (Fin 3))} (hPn : P.Normal)
    (h2 : IsPGroup 2 P) : P = ⊥ := by
  have key : ∀ x : Equiv.Perm (Fin 3), x ≠ 1 → x * x = 1 →
      ∃ g : Equiv.Perm (Fin 3), (g * x * g⁻¹ * x) * (g * x * g⁻¹ * x) ≠ 1 := by decide
  have hsq : ∀ x ∈ P, x * x = 1 := by
    intro x hx
    obtain ⟨k, hk⟩ := h2 ⟨x, hx⟩
    have h1 : orderOf x ∣ 2 ^ k :=
      orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
    have h2 : orderOf x ∣ 6 := by
      have := orderOf_dvd_natCard x
      rwa [Nat.card_perm, Nat.card_fin] at this
    have h3 : orderOf x ∣ 2 := by
      have := Nat.dvd_gcd h1 h2
      have hg : Nat.gcd (2 ^ k) 6 ∣ 2 := by
        rcases k with _ | k
        · simp
        · rw [pow_succ, show (6 : ℕ) = 3 * 2 by norm_num, Nat.gcd_mul_right]
          exact Nat.mul_dvd_mul_right (Nat.Coprime.gcd_eq_one
            (Nat.Coprime.pow_left _ (by norm_num))).dvd 2 |>.trans (by norm_num)
      exact this.trans hg
    rw [← sq]
    exact orderOf_dvd_iff_pow_eq_one.1 h3
  rw [eq_bot_iff]
  intro x hx
  by_contra hx1
  obtain ⟨g, hg⟩ := key x hx1 (hsq x hx)
  exact hg (hsq _ (mul_mem (hPn.conj_mem x hx g) hx))

omit hP [Finite X] in
theorem isPGroup_two_closure {S : Set X} (hc : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x)
    (hs : ∀ x ∈ S, x * x = 1) : IsPGroup 2 (closure S) := by
  have hcomm : IsMulCommutative (closure S) :=
    Subgroup.isMulCommutative_closure fun x hx y hy _ => hc x hx y hy
  have hsq : ∀ x ∈ closure S, x * x = 1 := by
    intro x hx
    induction hx using closure_induction with
    | mem y hy => exact hs y hy
    | one => exact mul_one 1
    | mul y z hy hz ihy ihz =>
      have hyz : y * z = z * y :=
        congrArg Subtype.val (hcomm.is_comm.comm (⟨y, hy⟩ : closure S) ⟨z, hz⟩)
      calc y * z * (y * z) = y * (z * y) * z := by group
        _ = y * (y * z) * z := by rw [hyz]
        _ = 1 := by rw [show y * (y * z) * z = y * y * (z * z) by group, ihy, ihz, one_mul]
    | inv y hy ih => rw [← mul_inv_rev, ih, inv_one]
  intro g
  exact ⟨1, Subtype.ext (by simpa [pow_two] using hsq g g.2)⟩

omit hP [Finite X] in
theorem le_normalizer_closure {S : Set X} {K : Subgroup X}
    (h : ∀ k ∈ K, ∀ s ∈ S, k * s * k⁻¹ ∈ S) : K ≤ normalizer (closure S : Set X) := by
  have hmap : ∀ k ∈ K, ∀ x ∈ closure S, k * x * k⁻¹ ∈ closure S := by
    intro k hk x hx
    induction hx using closure_induction with
    | mem y hy => exact subset_closure (h k hk y hy)
    | one => simp
    | mul a b _ _ ha hb =>
      rw [show k * (a * b) * k⁻¹ = k * a * k⁻¹ * (k * b * k⁻¹) by group]
      exact mul_mem ha hb
    | inv a _ ha =>
      rw [show k * a⁻¹ * k⁻¹ = (k * a * k⁻¹)⁻¹ by group]
      exact inv_mem ha
  intro k hk
  rw [mem_normalizer_iff]
  intro x
  refine ⟨hmap k hk x, fun hx => ?_⟩
  have := hmap k⁻¹ (inv_mem hk) _ hx
  rwa [show k⁻¹ * (k * x * k⁻¹) * k⁻¹⁻¹ = x by group] at this

omit [Group X] hP [Finite X] in
theorem perm_three_involutions : ∀ σ τ ρ : Equiv.Perm (Fin 3),
    (σ * σ = 1 ∧ τ * τ = 1 ∧ ρ * ρ = 1 ∧ σ ≠ 1 ∧ τ ≠ 1 ∧ ρ ≠ 1 ∧ σ ≠ τ) →
      ρ = σ ∨ ρ = τ ∨ ρ = σ * τ * σ := by
  decide

omit [Group X] hP [Finite X] in
theorem perm_three_not_commute : ∀ σ τ : Equiv.Perm (Fin 3),
    (σ * σ = 1 ∧ τ * τ = 1 ∧ σ ≠ 1 ∧ τ ≠ 1 ∧ σ ≠ τ) → σ * τ ≠ τ * σ := by
  decide

theorem ker_eq_pCore {φ : X →* Equiv.Perm (Fin 3)} (hφ : Function.Surjective φ) {d : X}
    (hd : d ∈ D) (hcomm : ∀ e ∈ D, d⁻¹ * e ∈ φ.ker → d * e = e * d) :
    φ.ker = CFSG.pCore 2 X := by
  classical
  have hsq : ∀ e ∈ D, e * e = 1 := fun e he => Pair.mul_self hP he
  have hcomm' : ∀ a ∈ D, ∀ e ∈ D, φ a = φ e → a * e = e * a := by
    intro a ha e he hae
    obtain ⟨c, rfl⟩ := isConj_iff.1 (Pair.isConj hP hd ha)
    have hmem : c⁻¹ * e * c ∈ D := by simpa using Pair.conj_mem hP he c⁻¹
    have hker : d⁻¹ * (c⁻¹ * e * c) ∈ φ.ker := by
      have e1 : φ (d⁻¹ * (c⁻¹ * e * c)) = (φ c)⁻¹ * ((φ (c * d * c⁻¹))⁻¹ * φ e) * φ c := by
        simp only [map_mul, map_inv]
        group
      rw [MonoidHom.mem_ker, e1, ← hae, inv_mul_cancel, mul_one, inv_mul_cancel]
    have h := hcomm _ hmem hker
    calc c * d * c⁻¹ * e = c * (d * (c⁻¹ * e * c)) * c⁻¹ := by group
      _ = c * ((c⁻¹ * e * c) * d) * c⁻¹ := by rw [h]
      _ = e * (c * d * c⁻¹) := by group
  have hφd : φ d ≠ 1 := by
    intro h1
    have hall : ∀ e ∈ D, φ e = 1 := by
      intro e he
      obtain ⟨c, rfl⟩ := isConj_iff.1 (Pair.isConj hP hd he)
      rw [map_mul, map_mul, h1, mul_one, ← map_mul, mul_inv_cancel, map_one]
    have hle : (⊤ : Subgroup X) ≤ φ.ker := by
      rw [← Pair.closure_eq hP, closure_le]
      exact fun e he => hall e he
    obtain ⟨x, hx⟩ := hφ (Equiv.swap 0 1)
    have := hle (mem_top x)
    rw [MonoidHom.mem_ker, hx] at this
    exact absurd this (by decide)
  have hφe : ∀ e ∈ D, φ e ≠ 1 := by
    intro e he h1
    obtain ⟨c, rfl⟩ := isConj_iff.1 (Pair.isConj hP hd he)
    apply hφd
    rw [map_mul, map_mul, map_inv] at h1
    calc φ d = (φ c)⁻¹ * (φ c * φ d * (φ c)⁻¹) * φ c := by group
      _ = 1 := by rw [h1]; group
  have hφsq : ∀ e ∈ D, φ e * φ e = 1 := fun e he => by rw [← map_mul, hsq e he, map_one]
  obtain ⟨b, hb, hbd⟩ : ∃ b ∈ D, φ b ≠ φ d := by
    by_contra! hall
    have hsub : ∀ x : X, φ x = 1 ∨ φ x = φ d := by
      intro x
      have hx : x ∈ closure D := by rw [Pair.closure_eq hP]; exact mem_top x
      induction hx using closure_induction_left with
      | one => left; exact map_one φ
      | mul_left e he y _ ih =>
        rw [map_mul, hall e he]
        rcases ih with h | h
        · right; rw [h, mul_one]
        · left; rw [h, hφsq d hd]
      | inv_mul_cancel e he y _ ih =>
        rw [map_mul, map_inv, hall e he, inv_eq_of_mul_eq_one_right (hφsq d hd)]
        rcases ih with h | h
        · right; rw [h, mul_one]
        · left; rw [h, hφsq d hd]
    obtain ⟨x, hx⟩ := hφ (finRotate 3)
    have hd2 := hφsq d hd
    rcases hsub x with h | h
    · rw [hx] at h; exact absurd h (by decide)
    · rw [hx] at h
      rw [← h] at hd2
      exact absurd hd2 (by decide)
  have hnc : φ d * φ b ≠ φ b * φ d :=
    perm_three_not_commute _ _ ⟨hφsq d hd, hφsq b hb, hφe d hd, hφe b hb, hbd.symm⟩
  have hdb : d * b ≠ b * d := fun h => hnc (by rw [← map_mul, h, map_mul])
  have hbraid : d * b * d = b * d * b :=
    braid_of_orderOf_le_three (hsq d hd) (hsq b hb) (by
      have := Pair.orderOf_mul_mem hP hd hb
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
      omega) hdb
  have hdbd : d * b * d ∈ D := by
    have := Pair.conj_mem hP hb d
    rwa [Pair.inv_eq hP hd] at this
  have hcases : ∀ e ∈ D, φ e = φ d ∨ φ e = φ b ∨ φ e = φ (d * b * d) := by
    intro e he
    have := perm_three_involutions _ _ _
      ⟨hφsq d hd, hφsq b hb, hφsq e he, hφe d hd, hφe b hb, hφe e he, hbd.symm⟩
    simpa [map_mul] using this
  set Q : Subgroup X := closure {x | ∃ e ∈ D, ∃ f ∈ D, φ e = φ f ∧ x = e * f} with hQdef
  have hQn : Q.Normal := closure_normal_of_conj (by
    rintro _ ⟨e, he, f, hf, hef, rfl⟩ g
    refine ⟨g * e * g⁻¹, Pair.conj_mem hP he g, g * f * g⁻¹, Pair.conj_mem hP hf g, ?_, by group⟩
    simp only [map_mul, map_inv, hef])
  have hQk : Q ≤ φ.ker := by
    refine (closure_le _).2 ?_
    rintro _ ⟨e, he, f, hf, hef, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, hef, hφsq f hf]
  have hmemQ : ∀ e ∈ D, ∀ u ∈ D, φ e = φ u → e * u ∈ Q := fun e he u hu h =>
    subset_closure ⟨e, he, u, hu, h, rfl⟩
  let sv : Fin 6 → X := ![1, d, b, d * b, b * d, d * b * d]
  have hdd := hsq d hd
  have hbb := hsq b hb
  have hds : ∀ i, ∃ j, d * sv i = sv j := by
    intro i
    fin_cases i
    · exact ⟨1, by simp [sv]⟩
    · exact ⟨0, by simp [sv, hdd]⟩
    · exact ⟨3, by simp [sv]⟩
    · exact ⟨2, by simp [sv, ← mul_assoc, hdd]⟩
    · exact ⟨5, by simp [sv, mul_assoc]⟩
    · exact ⟨4, by simp [sv, ← mul_assoc, hdd]⟩
  have hbs : ∀ i, ∃ j, b * sv i = sv j := by
    intro i
    fin_cases i
    · exact ⟨2, by simp [sv]⟩
    · exact ⟨4, by simp [sv]⟩
    · exact ⟨0, by simp [sv, hbb]⟩
    · exact ⟨5, by simp [sv, ← mul_assoc, hbraid]⟩
    · exact ⟨1, by simp [sv, ← mul_assoc, hbb]⟩
    · refine ⟨3, ?_⟩
      show b * (d * b * d) = d * b
      rw [hbraid, show b * (b * d * b) = b * b * d * b by group, hbb, one_mul]
  have hus : ∀ u ∈ ({d, b, d * b * d} : Set X), ∀ i, ∃ j, u * sv i = sv j := by
    intro u hu i
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl | rfl
    · exact hds i
    · exact hbs i
    · obtain ⟨j₁, h₁⟩ := hds i
      obtain ⟨j₂, h₂⟩ := hbs j₁
      obtain ⟨j₃, h₃⟩ := hds j₂
      exact ⟨j₃, by rw [show d * b * d * sv i = d * (b * (d * sv i)) by group, h₁, h₂, h₃]⟩
  have hdecomp : ∀ x : X, ∃ q ∈ Q, ∃ i, x = q * sv i := by
    intro x
    have hx : x ∈ closure D := by rw [Pair.closure_eq hP]; exact mem_top x
    have key : ∀ e ∈ D, ∀ y : X, (∃ q ∈ Q, ∃ i, y = q * sv i) → ∃ q ∈ Q, ∃ i, e * y = q * sv i := by
      rintro e he y ⟨q, hq, i, rfl⟩
      have hu : ∃ u ∈ ({d, b, d * b * d} : Set X), u ∈ D ∧ φ e = φ u := by
        rcases hcases e he with h | h | h
        · exact ⟨d, by simp, hd, h⟩
        · exact ⟨b, by simp, hb, h⟩
        · exact ⟨d * b * d, by simp, hdbd, h⟩
      obtain ⟨u, hu, huD, heu⟩ := hu
      obtain ⟨j, hj⟩ := hus u hu i
      refine ⟨e * q * e⁻¹ * (e * u), mul_mem (hQn.conj_mem q hq e) (hmemQ e he u huD heu), j, ?_⟩
      rw [← hj, show e * q * e⁻¹ * (e * u) * (u * sv i) = e * q * (e⁻¹ * e) * (u * u) * sv i by
        group, inv_mul_cancel, mul_one, hsq u huD, mul_one]
      group
    induction hx using closure_induction_left with
    | one => exact ⟨1, one_mem _, 0, by simp [sv]⟩
    | mul_left e he y _ ih => exact key e he y ih
    | inv_mul_cancel e he y _ ih => rw [Pair.inv_eq hP he]; exact key e he y ih
  have hcardX : Nat.card X ≤ Nat.card Q * 6 := by
    let F : Q × Fin 6 → X := fun p => p.1 * sv p.2
    have hF : Function.Surjective F := by
      intro x
      obtain ⟨q, hq, i, rfl⟩ := hdecomp x
      exact ⟨(⟨q, hq⟩, i), rfl⟩
    have := Nat.card_le_card_of_surjective F hF
    rwa [Nat.card_prod, Nat.card_fin] at this
  have hker6 : Nat.card X = Nat.card φ.ker * 6 := by
    have h1 := φ.ker.card_mul_index
    have h2 : φ.ker.index = 6 := by
      rw [Subgroup.index, Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv,
        Nat.card_perm, Nat.card_fin]
      rfl
    rw [h2] at h1
    exact h1.symm
  have hQeq : Q = φ.ker := Subgroup.eq_of_le_of_card_ge hQk (by omega)
  let Qc : Equiv.Perm (Fin 3) → Subgroup X := fun c =>
    closure {x | ∃ e ∈ D, ∃ f ∈ D, φ e = c ∧ φ f = c ∧ x = e * f}
  have hQc2 : ∀ c, IsPGroup 2 (Qc c) := by
    intro c
    refine isPGroup_two_closure ?_ ?_
    · rintro _ ⟨e, he, f, hf, hec, hfc, rfl⟩ _ ⟨e', he', f', hf', hec', hfc', rfl⟩
      have c1 := hcomm' e he e' he' (hec.trans hec'.symm)
      have c2 := hcomm' e he f' hf' (hec.trans hfc'.symm)
      have c3 := hcomm' f hf e' he' (hfc.trans hec'.symm)
      have c4 := hcomm' f hf f' hf' (hfc.trans hfc'.symm)
      calc e * f * (e' * f') = e * (f * e') * f' := by group
        _ = e * (e' * f) * f' := by rw [c3]
        _ = e * e' * (f * f') := by group
        _ = e' * e * (f' * f) := by rw [c1, c4]
        _ = e' * (e * f') * f := by group
        _ = e' * (f' * e) * f := by rw [c2]
        _ = e' * f' * (e * f) := by group
    · rintro _ ⟨e, he, f, hf, hec, hfc, rfl⟩
      have c0 := hcomm' e he f hf (hec.trans hfc.symm)
      rw [show e * f * (e * f) = e * (f * e) * f by group, ← c0,
        show e * (e * f) * f = e * e * (f * f) by group, hsq e he, hsq f hf, one_mul]
  have hQck : ∀ c, Qc c ≤ φ.ker := by
    intro c
    refine (closure_le _).2 ?_
    rintro _ ⟨e, he, f, hf, hec, hfc, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, hec, ← hfc, hφsq f hf]
  have hQcn : ∀ c, φ.ker ≤ normalizer (Qc c : Set X) := by
    intro c
    refine le_normalizer_closure ?_
    rintro k hk _ ⟨e, he, f, hf, hec, hfc, rfl⟩
    rw [MonoidHom.mem_ker] at hk
    refine ⟨k * e * k⁻¹, Pair.conj_mem hP he k, k * f * k⁻¹, Pair.conj_mem hP hf k, ?_, ?_,
      by group⟩
    · simp only [map_mul, map_inv, hk, one_mul, inv_one, mul_one, hec]
    · simp only [map_mul, map_inv, hk, one_mul, inv_one, mul_one, hfc]
  have hsup2 : IsPGroup 2 (Qc (φ d) ⊔ Qc (φ b) ⊔ Qc (φ (d * b * d)) : Subgroup X) := by
    refine IsPGroup.to_sup_of_normal_right'
      (IsPGroup.to_sup_of_normal_right' (hQc2 _) (hQc2 _) ((hQck _).trans (hQcn _)))
      (hQc2 _) ((sup_le (hQck _) (hQck _)).trans (hQcn _))
  have hQle : Q ≤ Qc (φ d) ⊔ Qc (φ b) ⊔ Qc (φ (d * b * d)) := by
    refine (closure_le _).2 ?_
    rintro _ ⟨e, he, f, hf, hef, rfl⟩
    have hgen : ∀ c, φ e = c → e * f ∈ Qc c := fun c hc =>
      subset_closure ⟨e, he, f, hf, hc, hef.symm.trans hc, rfl⟩
    rcases hcases e he with h | h | h
    · exact mem_sup_left (mem_sup_left (hgen _ h))
    · exact mem_sup_left (mem_sup_right (hgen _ h))
    · exact mem_sup_right (hgen _ h)
  have hk2 : IsPGroup 2 φ.ker := hQeq ▸ hsup2.to_le hQle
  apply le_antisymm
  · exact le_sSup ⟨inferInstance, hk2⟩
  · have hmapn : ((CFSG.pCore 2 X).map φ).Normal := CFSG.pCore_normal.map φ hφ
    have hmap2 : IsPGroup 2 ((CFSG.pCore 2 X).map φ) := CFSG.pCore_isPGroup.map φ
    have hbot := eq_bot_of_normal_isPGroup_perm_three hmapn hmap2
    rwa [Subgroup.map_eq_bot_iff] at hbot

end Fischer

theorem fischerDisconnected :
    ∀ (X : Type) [Group X] [Finite X] (D : Set X), D.Nonempty → (∀ d ∈ D, orderOf d = 2) →
      (∀ d ∈ D, ∀ x : X, x * d * x⁻¹ ∈ D) → (∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ≤ 3) →
      closure D = ⊤ → ¬ (CFSG.Fischer.commGraph D).Connected →
      (∀ d ∈ D, ∀ e ∈ D, IsConj d e) ∧
        ∃ (Y : Subgroup X) (_ : Y.Normal), Nonempty (X ⧸ Y ≃* Equiv.Perm (Fin 3)) ∧
          ∀ d ∈ D, (∀ e ∈ D, d⁻¹ * e ∈ Y → d * e = e * d) → Y = pCore 2 X := by
  intro X _ _ D hne hD2 hDn hD3 hgen hdis
  obtain ⟨d, hd⟩ := hne
  have hP := pair_of_not_connected hd hD2 hDn hD3 hgen hdis
  refine ⟨fun a ha b hb => isConj_of_not_connected hD2 hD3 hdis ha hb, ?_⟩
  obtain ⟨φ, hφ⟩ := exists_surjective_perm_three hP hdis hd
  exact ⟨φ.ker, inferInstance, ⟨QuotientGroup.quotientKerEquivOfSurjective φ hφ⟩,
    fun d' hd' hc => ker_eq_pCore hP hφ hd' hc⟩

end CFSG.ComponentClassification.Asc76.Sec4
