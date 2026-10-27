module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Disp
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Sub

public section

namespace CFSG.QuasithinUnique.Setup.X1

open CFSG.Quasithin CFSG.QuasithinUnique.Setup.Family

section Inner

variable {W : Type} [CommGroup W]

@[expose] def redHom (L : Subgroup (MulAut W)) {S : Type} [Group S] (e : CQ L ≃* S) : ↥L →* S :=
  e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))

theorem redHom_apply (L : Subgroup (MulAut W)) {S : Type} [Group S] (e : CQ L ≃* S) (b : ↥L) :
    redHom L e b = e (QuotientGroup.mk b) := rfl

theorem redHom_surjective (L : Subgroup (MulAut W)) {S : Type} [Group S] (e : CQ L ≃* S) :
    Function.Surjective (redHom L e) :=
  e.surjective.comp (QuotientGroup.mk'_surjective _)

theorem redHom_eq_one_iff (L : Subgroup (MulAut W)) {S : Type} [Group S] (e : CQ L ≃* S)
    (b : ↥L) : redHom L e b = 1 ↔ b ∈ Subgroup.center ↥L := by
  rw [redHom_apply, ← map_one e, e.injective.eq_iff, ← QuotientGroup.eq_one_iff]

theorem redHom_comp_injective [Finite W] (hW : ∀ w : W, w * w = 1) {L E : Subgroup (MulAut W)}
    (hirr : IsIrrOn L) (hEL : E ≤ L) (hEel : IsElemAbelian2 E) {S : Type} [Group S]
    (e : CQ L ≃* S) : Function.Injective ((redHom L e).comp (Subgroup.inclusion hEL)) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have h1 : (Subgroup.inclusion hEL x) ∈ Subgroup.center ↥L := by
    rw [← redHom_eq_one_iff L e]
    exact hx
  have hcomm : ∀ l ∈ L, l * (x : MulAut W) = (x : MulAut W) * l := fun l hl => by
    have := Subgroup.mem_center_iff.1 h1 ⟨l, hl⟩
    exact congrArg Subtype.val this
  have hodd := odd_orderOf_of_commutes hW hirr hcomm
  have hx2 : (x : MulAut W) ^ 2 = 1 := hEel.2 x x.2
  have hdvd : orderOf (x : MulAut W) ∣ 2 := orderOf_dvd_of_pow_eq_one hx2
  have h1' : orderOf (x : MulAut W) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · exact h
    · rw [h] at hodd
      exact absurd hodd (by decide)
  exact Subtype.ext (orderOf_eq_one_iff.1 h1')

@[expose] def imgSub (L E : Subgroup (MulAut W)) (hEL : E ≤ L) {S : Type} [Group S]
    (e : CQ L ≃* S) : Subgroup S :=
  ((redHom L e).comp (Subgroup.inclusion hEL)).range

theorem mem_imgSub {L E : Subgroup (MulAut W)} {hEL : E ≤ L} {S : Type} [Group S]
    {e : CQ L ≃* S} {s : S} :
    s ∈ imgSub L E hEL e ↔ ∃ b : ↥E, redHom L e (Subgroup.inclusion hEL b) = s := by
  simp [imgSub, MonoidHom.mem_range]

theorem imgSub_comm {L E : Subgroup (MulAut W)} {hEL : E ≤ L} {S : Type} [Group S]
    {e : CQ L ≃* S} (hEel : IsElemAbelian2 E) :
    ∀ x ∈ imgSub L E hEL e, ∀ y ∈ imgSub L E hEL e, x * y = y * x := by
  intro x hx y hy
  obtain ⟨a, rfl⟩ := mem_imgSub.1 hx
  obtain ⟨b, rfl⟩ := mem_imgSub.1 hy
  have h : a * b = b * a := Subtype.ext (hEel.1 a a.2 b b.2)
  calc redHom L e (Subgroup.inclusion hEL a) * redHom L e (Subgroup.inclusion hEL b)
      = redHom L e (Subgroup.inclusion hEL (a * b)) := by simp [map_mul]
    _ = redHom L e (Subgroup.inclusion hEL (b * a)) := by rw [h]
    _ = _ := by simp [map_mul]

theorem imgSub_sq {L E : Subgroup (MulAut W)} {hEL : E ≤ L} {S : Type} [Group S]
    {e : CQ L ≃* S} (hEel : IsElemAbelian2 E) :
    ∀ x ∈ imgSub L E hEL e, x * x = 1 := by
  intro x hx
  obtain ⟨a, rfl⟩ := mem_imgSub.1 hx
  rw [← map_mul]
  have : a * a = 1 := Subtype.ext (by simpa [sq] using hEel.2 a a.2)
  have h2 : Subgroup.inclusion hEL (a * a) = 1 := by rw [this, map_one]
  rw [map_mul] at h2
  rw [h2, map_one]

theorem card_imgSub [Finite W] (hW : ∀ w : W, w * w = 1) {L E : Subgroup (MulAut W)}
    (hirr : IsIrrOn L) (hEL : E ≤ L) (hEel : IsElemAbelian2 E) {S : Type} [Group S]
    (e : CQ L ≃* S) : Nat.card (imgSub L E hEL e) = Nat.card E :=
  (Nat.card_congr (MonoidHom.ofInjective (redHom_comp_injective hW hirr hEL hEel e)).toEquiv).symm

theorem two_pow_le_of_inner_gen [Finite W] (hW : ∀ w : W, w * w = 1) {L E : Subgroup (MulAut W)}
    (hEL : E ≤ L) {S : Type} [Group S] (e : CQ L ≃* S) {k p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hgen : ∃ cs : List S, cs.length = k ∧ ∃ x ∈ Subgroup.closure
      (conjSet cs ((imgSub L E hEL e : Subgroup S) : Set S)), orderOf x = p) :
    2 ^ orderOf (2 : ZMod p) ≤ (fixV E).index ^ k := by
  obtain ⟨cs, hcs, x, hx, hxp⟩ := hgen
  subst hcs
  refine two_pow_le_index_pow_of_mem hW (redHom L e) cs (fun c _ => ?_) hp2 hxp ?_
  · obtain ⟨b, hb⟩ := redHom_surjective L e c
    exact ⟨b, hb⟩
  · refine Subgroup.closure_mono ?_ hx
    rintro _ ⟨c, hc, t, ht, rfl⟩
    obtain ⟨a, rfl⟩ := mem_imgSub.1 ht
    exact ⟨c, hc, Subgroup.inclusion hEL a, a.2, rfl⟩

theorem weight_lt_of_lt_index [Finite W] (E : Subgroup (MulAut W))
    (h : Nat.card E < (fixV E).index) : Nat.card E * Nat.card (fixV E) < Nat.card W := by
  have hmul := Subgroup.card_mul_index (fixV E)
  have hpos : 0 < Nat.card (fixV E) := Nat.card_pos
  rw [← hmul]
  nlinarith

end Inner

end CFSG.QuasithinUnique.Setup.X1
