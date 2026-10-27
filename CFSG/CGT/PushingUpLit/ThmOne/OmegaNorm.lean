module

public import CFSG.Quasithin.Background.CommVBasics
public import CFSG.CGT.PushingUpLit.ThmOne.SchurAut
public import CFSG.Quasithin.Background.A3Structure37Schur

public section

namespace CFSG.CGT.PushingUpLit.ThmOne

open CFSG.Quasithin CFSG.Quasithin.XMod

namespace OmegaNorm

variable {P : Type*} [CommGroup P]

@[expose] def autAddEnd (t : MulAut P) : AddMonoid.End (Additive P) :=
  MonoidHom.toAdditive (t : P →* P)

theorem toMonoidEnd_mul (f g : AddMonoid.End (Additive P)) (p : P) :
    toMonoidEnd (f * g) p = toMonoidEnd f (toMonoidEnd g p) := rfl

theorem toMonoidEnd_sub (f g : AddMonoid.End (Additive P)) (p : P) :
    toMonoidEnd (f - g) p = toMonoidEnd f p * (toMonoidEnd g p)⁻¹ := by
  change Additive.toMul (f (Additive.ofMul p) - g (Additive.ofMul p)) = _
  rw [toMul_sub, div_eq_mul_inv]
  rfl

theorem toMonoidEnd_one (p : P) : toMonoidEnd (1 : AddMonoid.End (Additive P)) p = p := rfl

theorem conj_mem_eqvEnd {S : Subgroup (MulAut P)} {t : MulAut P}
    (ht : t ∈ Subgroup.normalizer (S : Set (MulAut P))) {f : AddMonoid.End (Additive P)}
    (hf : f ∈ eqvEnd ↥S P) : autAddEnd t * f * autAddEnd t⁻¹ ∈ eqvEnd ↥S P := by
  rw [mem_eqvEnd_iff] at hf ⊢
  intro a p
  have ha : t⁻¹ * (a : MulAut P) * t ∈ S := by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem ht) a).mp a.2
    rwa [inv_inv] at this
  have key := hf ⟨_, ha⟩ (t⁻¹ p)
  change toMonoidEnd f ((t⁻¹ * (a : MulAut P) * t) (t⁻¹ p)) =
    (t⁻¹ * (a : MulAut P) * t) (toMonoidEnd f (t⁻¹ p)) at key
  change t (toMonoidEnd f (t⁻¹ ((a : MulAut P) p))) = (a : MulAut P) (t (toMonoidEnd f (t⁻¹ p)))
  simp only [MulAut.mul_apply, MulAut.apply_inv_self] at key
  rw [key, MulAut.apply_inv_self]

theorem injective_of_mem_eqvEnd {S : Subgroup (MulAut P)} (hS : IsIrrSec ↥S (⊥ : Subgroup P) ⊤)
    {f : AddMonoid.End (Additive P)} (hf : f ∈ eqvEnd ↥S P) (hf0 : f ≠ 0) :
    Function.Injective (toMonoidEnd f) := by
  rcases eqvEnd_isUnit_or_eq_zero hS ⟨f, hf⟩ with h | h
  · obtain ⟨g, hg⟩ := h.exists_left_inv
    intro p q hpq
    have h1 : ∀ x : P, toMonoidEnd (g : AddMonoid.End (Additive P)) (toMonoidEnd f x) = x :=
      fun x => by
        rw [← toMonoidEnd_mul]
        have := congrArg (fun e : ↥(eqvEnd ↥S P) => toMonoidEnd (e : AddMonoid.End _) x) hg
        exact this
    rw [← h1 p, hpq, h1 q]
  · exact absurd (congrArg Subtype.val h) hf0

variable [Finite P]

theorem bijective_of_mem_eqvEnd {S : Subgroup (MulAut P)} (hS : IsIrrSec ↥S (⊥ : Subgroup P) ⊤)
    {f : AddMonoid.End (Additive P)} (hf : f ∈ eqvEnd ↥S P) (hf0 : f ≠ 0) :
    Function.Bijective (toMonoidEnd f) :=
  (injective_of_mem_eqvEnd hS hf hf0).bijective_of_nat_card_le le_rfl

omit [Finite P] in
theorem toMonoidEnd_apply_comm {S Y : Subgroup (MulAut P)} (hYS : Y ≤ S)
    {f : AddMonoid.End (Additive P)} (hf : f ∈ eqvEnd ↥S P) {y : MulAut P} (hy : y ∈ Y) (p : P) :
    toMonoidEnd f (y p) = y (toMonoidEnd f p) :=
  mem_eqvEnd_iff.mp hf ⟨y, hYS hy⟩ p

omit [Finite P] in
theorem commV_apply_mem_of_commute {Y : Subgroup (MulAut P)} {a : MulAut P}
    (ha : ∀ y ∈ Y, y * a = a * y) {u : P} (hu : u ∈ commV Y) : a u ∈ commV Y := by
  have hu' : u ∈ Subgroup.closure {w | ∃ y ∈ Y, ∃ v : P, y v * v⁻¹ = w} := hu
  clear hu
  induction hu' using Subgroup.closure_induction with
  | mem w hw =>
    obtain ⟨y, hy, v, rfl⟩ := hw
    apply Subgroup.subset_closure
    refine ⟨y, hy, a v, ?_⟩
    rw [map_mul, map_inv, ← MulAut.mul_apply, ha y hy, MulAut.mul_apply]
  | one => rw [map_one]; exact one_mem _
  | mul x z _ _ hx hz => rw [map_mul]; exact mul_mem hx hz
  | inv x _ hx => rw [map_inv]; exact inv_mem hx

omit [Finite P] in
theorem commV_apply_mem_of_mem {Y : Subgroup (MulAut P)} {a : MulAut P} (ha : a ∈ Y) {u : P}
    (hu : u ∈ commV Y) : a u ∈ commV Y :=
  CFSG.Quasithin.commV_apply_mem_of_mem ha hu

omit [Finite P] in
theorem toMonoidEnd_mem_commV {S Y : Subgroup (MulAut P)} (hYS : Y ≤ S)
    {f : AddMonoid.End (Additive P)} (hf : f ∈ eqvEnd ↥S P) {u : P} (hu : u ∈ commV Y) :
    toMonoidEnd f u ∈ commV Y := by
  have hu' : u ∈ Subgroup.closure {w | ∃ y ∈ Y, ∃ v : P, y v * v⁻¹ = w} := hu
  clear hu
  induction hu' using Subgroup.closure_induction with
  | mem w hw =>
    obtain ⟨y, hy, v, rfl⟩ := hw
    apply Subgroup.subset_closure
    refine ⟨y, hy, toMonoidEnd f v, ?_⟩
    rw [map_mul, map_inv, toMonoidEnd_apply_comm hYS hf hy]
  | one => rw [map_one]; exact one_mem _
  | mul x z _ _ hx hz => rw [map_mul]; exact mul_mem hx hz
  | inv x _ hx => rw [map_inv]; exact inv_mem hx

omit [Finite P] in
theorem apply_mem_commV_inf_fixV {Y : Subgroup (MulAut P)} {a : MulAut P}
    (ha : ∀ y ∈ Y, y * a = a * y) {u : P} (hu : u ∈ commV Y ⊓ fixV Y) :
    a u ∈ commV Y ⊓ fixV Y :=
  ⟨commV_apply_mem_of_commute ha hu.1, fun y hy => by
    rw [← MulAut.mul_apply, ha y hy, MulAut.mul_apply, hu.2 y hy]⟩

@[expose] noncomputable def restrictInvHom (T : Subgroup (MulAut P)) (U : Subgroup P)
    (hT : ∀ a ∈ T, ∀ u ∈ U, a u ∈ U) : ↥T →* MulAut ↥U where
  toFun a :=
    { toFun := fun u => ⟨(a : MulAut P) u, hT a a.2 u u.2⟩
      invFun := fun u => ⟨(a : MulAut P)⁻¹ u, hT _ (inv_mem a.2) u u.2⟩
      left_inv := fun _ => Subtype.ext (MulAut.inv_apply_self _ _ _)
      right_inv := fun _ => Subtype.ext (MulAut.apply_inv_self _ _ _)
      map_mul' := fun _ _ => Subtype.ext (map_mul _ _ _) }
  map_one' := MulEquiv.ext fun _ => Subtype.ext rfl
  map_mul' _ _ := MulEquiv.ext fun _ => Subtype.ext rfl

omit [Finite P] in
theorem coe_restrictInvHom_apply {T : Subgroup (MulAut P)} {U : Subgroup P}
    (hT : ∀ a ∈ T, ∀ u ∈ U, a u ∈ U) (a : ↥T) (u : ↥U) :
    ((restrictInvHom T U hT a u : ↥U) : P) = (a : MulAut P) u := rfl

theorem mul_inv_mem_of_commute_irreducible {Y : Subgroup (MulAut P)}
    (hirr : ∀ J : Subgroup P, (∀ y ∈ Y, ∀ j ∈ J, y j ∈ J) → commV Y ⊓ fixV Y ≤ J →
      J ≤ commV Y → J = commV Y ⊓ fixV Y ∨ J = commV Y)
    (hlt : commV Y ⊓ fixV Y < commV Y) {a b : MulAut P} (ha : ∀ y ∈ Y, y * a = a * y)
    (hb : ∀ y ∈ Y, y * b = b * y) {u : P} (hu : u ∈ commV Y) :
    (a (b u))⁻¹ * b (a u) ∈ commV Y ⊓ fixV Y := by
  classical
  let T : Subgroup (MulAut P) := Subgroup.centralizer (Y : Set (MulAut P))
  have haT : a ∈ T := Subgroup.mem_centralizer_iff.mpr ha
  have hbT : b ∈ T := Subgroup.mem_centralizer_iff.mpr hb
  have hTc : ∀ c ∈ T, ∀ y ∈ Y, y * c = c * y := fun c hc => Subgroup.mem_centralizer_iff.mp hc
  have hTU : ∀ c ∈ T, ∀ v ∈ commV Y, c v ∈ commV Y :=
    fun c hc _ hv => commV_apply_mem_of_commute (hTc c hc) hv
  have hYU : ∀ c ∈ Y, ∀ v ∈ commV Y, c v ∈ commV Y := fun _ hc _ hv => commV_apply_mem_of_mem hc hv
  let Zq : Subgroup ↥(commV Y) := (commV Y ⊓ fixV Y).subgroupOf (commV Y)
  have hσ : ∀ (s : ↥Y) (x : ↥(commV Y)), x ∈ Zq ↔ restrictInvHom Y (commV Y) hYU s x ∈ Zq := by
    intro s x
    simp only [Zq, Subgroup.mem_subgroupOf, coe_restrictInvHom_apply]
    refine ⟨fun hx => ?_, fun hx => ?_⟩
    · rw [hx.2 s s.2]
      exact hx
    · have h1 : (s : MulAut P)⁻¹ ((s : MulAut P) x) = (s : MulAut P) x := hx.2 _ (inv_mem s.2)
      rw [MulAut.inv_apply_self] at h1
      rw [h1]
      exact hx
  have hτ : ∀ (c : ↥T) (x : ↥(commV Y)), x ∈ Zq ↔ restrictInvHom T (commV Y) hTU c x ∈ Zq := by
    intro c x
    simp only [Zq, Subgroup.mem_subgroupOf, coe_restrictInvHom_apply]
    refine ⟨fun hx => apply_mem_commV_inf_fixV (hTc c c.2) hx, fun hx => ?_⟩
    have h1 := apply_mem_commV_inf_fixV (hTc _ (inv_mem c.2)) hx
    rwa [MulAut.inv_apply_self] at h1
  have hne : Zq ≠ ⊤ := by
    intro htop
    refine (not_le_of_gt hlt) fun v hv => ?_
    have : (⟨v, hv⟩ : ↥(commV Y)) ∈ Zq := by rw [htop]; trivial
    exact this
  have hirr' : ∀ J : Subgroup ↥(commV Y), Zq ≤ J →
      (∀ s : ↥Y, ∀ x ∈ J, restrictInvHom Y (commV Y) hYU s x ∈ J) → J = Zq ∨ J = ⊤ := by
    intro J hZJ hJ
    have hinv : ∀ y ∈ Y, ∀ j ∈ J.map (commV Y).subtype, y j ∈ J.map (commV Y).subtype := by
      rintro y hy _ ⟨j, hj, rfl⟩
      exact ⟨_, hJ ⟨y, hy⟩ j hj, rfl⟩
    have hCJ : commV Y ⊓ fixV Y ≤ J.map (commV Y).subtype := fun v hv =>
      ⟨⟨v, hv.1⟩, hZJ (show (v : P) ∈ commV Y ⊓ fixV Y from hv), rfl⟩
    have hJU : J.map (commV Y).subtype ≤ commV Y := by
      rintro _ ⟨j, -, rfl⟩
      exact j.2
    rcases hirr _ hinv hCJ hJU with h | h
    · left
      apply Subgroup.map_injective (commV Y).subtype_injective
      rw [h, Subgroup.map_subgroupOf_eq_of_le inf_le_left]
    · right
      apply Subgroup.map_injective (commV Y).subtype_injective
      rw [h, Subgroup.map_top, Subgroup.range_subtype]
  obtain ⟨σ', τ', hσ', hτ', hirrQ⟩ := exists_quotAction Zq (restrictInvHom Y (commV Y) hYU)
    (restrictInvHom T (commV Y) hTU) hσ hτ hne hirr'
  have hST : ∀ s ∈ σ'.range, ∀ x ∈ τ'.range, s * x = x * s := by
    rintro _ ⟨s, rfl⟩ _ ⟨c, rfl⟩
    refine MulEquiv.ext fun q => ?_
    induction q using QuotientGroup.induction_on with
    | H x =>
      rw [MulAut.mul_apply, MulAut.mul_apply, hτ', hσ', hσ', hτ']
      congr 1
      apply Subtype.ext
      simp only [coe_restrictInvHom_apply]
      rw [← MulAut.mul_apply, hTc c c.2 s s.2, MulAut.mul_apply]
  have hcomm := CFSG.Quasithin.A37.commute_of_irreducible σ'.range τ'.range hirrQ hST
    (τ' ⟨a, haT⟩) ⟨_, rfl⟩ (τ' ⟨b, hbT⟩) ⟨_, rfl⟩
  have h1 := congrArg (fun φ : MulAut (↥(commV Y) ⧸ Zq) =>
    φ ((⟨u, hu⟩ : ↥(commV Y)) : ↥(commV Y) ⧸ Zq)) hcomm
  simp only [MulAut.mul_apply, hτ'] at h1
  rw [QuotientGroup.eq] at h1
  exact h1

theorem commute_eqvEnd_of_commute {S Y : Subgroup (MulAut P)}
    (hS : IsIrrSec ↥S (⊥ : Subgroup P) ⊤) (hYS : Y ≤ S)
    (hirr : ∀ J : Subgroup P, (∀ y ∈ Y, ∀ j ∈ J, y j ∈ J) → commV Y ⊓ fixV Y ≤ J →
      J ≤ commV Y → J = commV Y ⊓ fixV Y ∨ J = commV Y)
    (hlt : commV Y ⊓ fixV Y < commV Y) {t : MulAut P}
    (htS : t ∈ Subgroup.normalizer (S : Set (MulAut P))) (htY : ∀ y ∈ Y, t * y = y * t)
    {f : AddMonoid.End (Additive P)} (hf : f ∈ eqvEnd ↥S P) (p : P) :
    toMonoidEnd f (t p) = t (toMonoidEnd f p) := by
  by_cases hf0 : f = 0
  · subst hf0
    exact (map_one t).symm
  let fA : MulAut P := MulEquiv.ofBijective (toMonoidEnd f) (bijective_of_mem_eqvEnd hS hf hf0)
  have hfA : ∀ y ∈ Y, y * fA = fA * y := fun y hy => MulEquiv.ext fun x =>
    (toMonoidEnd_apply_comm hYS hf hy x).symm
  have htY' : ∀ y ∈ Y, y * t = t * y := fun y hy => (htY y hy).symm
  set g : AddMonoid.End (Additive P) := autAddEnd t * f * autAddEnd t⁻¹ - f with hgdef
  have hg : g ∈ eqvEnd ↥S P := sub_mem (conj_mem_eqvEnd htS hf) hf
  have hgU : ∀ v ∈ commV Y, toMonoidEnd g v ∈ commV Y ⊓ fixV Y := by
    intro v hv
    have hu : t⁻¹ v ∈ commV Y := commV_apply_mem_of_commute
      (fun y hy => (Commute.inv_right (htY' y hy)).eq) hv
    have h1 := inv_mem (mul_inv_mem_of_commute_irreducible hirr hlt htY' hfA hu)
    rw [hgdef, toMonoidEnd_sub]
    change t (toMonoidEnd f (t⁻¹ v)) * (toMonoidEnd f v)⁻¹ ∈ _
    rw [mul_inv_rev, inv_inv, MulAut.apply_inv_self] at h1
    rw [mul_comm]
    exact h1
  by_cases hg0 : g = 0
  · have h1 : autAddEnd t * f * autAddEnd t⁻¹ = f := sub_eq_zero.mp hg0
    have h2 := congrArg (fun e => toMonoidEnd e (t p)) h1
    change t (toMonoidEnd f (t⁻¹ (t p))) = toMonoidEnd f (t p) at h2
    rw [MulAut.inv_apply_self] at h2
    exact h2.symm
  exfalso
  have hinj := injective_of_mem_eqvEnd hS hg hg0
  have hle : Nat.card ↥(commV Y) ≤ Nat.card ↥(commV Y ⊓ fixV Y) :=
    Nat.card_le_card_of_injective (fun v : ↥(commV Y) => (⟨_, hgU v v.2⟩ : ↥(commV Y ⊓ fixV Y)))
      fun v w hvw => Subtype.ext (hinj (congrArg Subtype.val hvw))
  exact absurd hle (not_le_of_gt (Subgroup.card_lt_of_lt hlt))

end OmegaNorm

end CFSG.CGT.PushingUpLit.ThmOne
