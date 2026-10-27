module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.Quasithin CFSG.CGT.PushingUp Equiv

variable {V : Type} [CommGroup V]

theorem exists_perm_of_normalizes {m : ℕ} (hm : 5 ≤ m) (hm6 : m ≠ 6) {Y : Subgroup (MulAut V)}
    (θ : ↥Y ≃* alternatingGroup (Fin m)) {s : MulAut V} (hs : ∀ y ∈ Y, s * y * s⁻¹ ∈ Y) :
    ∃ π : Perm (Fin m), ∀ (y : MulAut V) (hy : y ∈ Y),
      (θ ⟨s * y * s⁻¹, hs y hy⟩ : Perm (Fin m)) = π * (θ ⟨y, hy⟩ : Perm (Fin m)) * π⁻¹ := by
  classical
  let f : ↥Y →* ↥Y :=
    { toFun := fun y => ⟨s * (y : MulAut V) * s⁻¹, hs y y.2⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp [mul_assoc] }
  have hf : Function.Injective f := by
    intro a b h
    have h1 := congrArg Subtype.val h
    exact Subtype.ext (by simpa [f] using h1)
  have : Finite ↥Y := Finite.of_equiv _ θ.symm.toEquiv
  have hbij : Function.Bijective f := Finite.injective_iff_bijective.mp hf
  let φ : MulAut (alternatingGroup (Fin m)) :=
    θ.symm.trans ((MulEquiv.ofBijective f hbij).trans θ)
  obtain ⟨π, hπ⟩ := (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj m hm hm6).2 φ
  refine ⟨π, fun y hy => ?_⟩
  have h1 := congrArg (fun e : MulAut (alternatingGroup (Fin m)) =>
    (e (θ ⟨y, hy⟩) : Perm (Fin m))) hπ
  simp only [MulAut.conjNormal_apply] at h1
  rw [h1]
  simp [φ, f]

theorem perm_unique {m : ℕ} (hm : 5 ≤ m) {π π' : Perm (Fin m)}
    (h : ∀ σ : alternatingGroup (Fin m),
      π * (σ : Perm (Fin m)) * π⁻¹ = π' * (σ : Perm (Fin m)) * π'⁻¹) : π = π' := by
  refine GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup m (by omega)
    (MulEquiv.ext fun σ => Subtype.ext ?_)
  simp only [MulAut.conjNormal_apply]
  exact h σ

private theorem cap_rel {m : ℕ} {Y : Subgroup (MulAut V)} (θ : ↥Y ≃* alternatingGroup (Fin m))
    {s : MulAut V} (hs : ∀ y ∈ Y, s * y * s⁻¹ ∈ Y) {π : Perm (Fin m)}
    (hπ : ∀ (y : MulAut V) (hy : y ∈ Y),
      (θ ⟨s * y * s⁻¹, hs y hy⟩ : Perm (Fin m)) = π * (θ ⟨y, hy⟩ : Perm (Fin m)) * π⁻¹)
    {y z : ↥Y} (h : s * (y : MulAut V) * s⁻¹ = z) :
    (θ z : Perm (Fin m)) = π * (θ y : Perm (Fin m)) * π⁻¹ := by
  obtain rfl : z = ⟨s * (y : MulAut V) * s⁻¹, hs y y.2⟩ := Subtype.ext h.symm
  exact hπ y y.2

theorem perm_eq_one_iff {m : ℕ} (hm : 5 ≤ m) {Y : Subgroup (MulAut V)}
    (θ : ↥Y ≃* alternatingGroup (Fin m)) {s : MulAut V} (hs : ∀ y ∈ Y, s * y * s⁻¹ ∈ Y)
    {π : Perm (Fin m)}
    (hπ : ∀ (y : MulAut V) (hy : y ∈ Y),
      (θ ⟨s * y * s⁻¹, hs y hy⟩ : Perm (Fin m)) = π * (θ ⟨y, hy⟩ : Perm (Fin m)) * π⁻¹) :
    π = 1 ↔ ∀ y ∈ Y, s * y = y * s := by
  constructor
  · rintro rfl y hy
    have h1 := hπ y hy
    simp only [inv_one, one_mul, mul_one] at h1
    have h2 : (⟨s * y * s⁻¹, hs y hy⟩ : ↥Y) = ⟨y, hy⟩ := θ.injective (Subtype.ext h1)
    have h3 : s * y * s⁻¹ = y := congrArg Subtype.val h2
    calc s * y = s * y * s⁻¹ * s := by group
      _ = y * s := by rw [h3]
  · intro h
    refine perm_unique hm fun σ => ?_
    obtain ⟨y, rfl⟩ := θ.surjective σ
    have h3 : s * (y : MulAut V) * s⁻¹ = y := by rw [h y y.2]; group
    rw [← cap_rel θ hs hπ h3]
    simp

theorem perm_mul_self {m : ℕ} (hm : 5 ≤ m) {Y : Subgroup (MulAut V)}
    (θ : ↥Y ≃* alternatingGroup (Fin m)) {s : MulAut V} (hs : ∀ y ∈ Y, s * y * s⁻¹ ∈ Y)
    (hs2 : s ^ 2 = 1) {π : Perm (Fin m)}
    (hπ : ∀ (y : MulAut V) (hy : y ∈ Y),
      (θ ⟨s * y * s⁻¹, hs y hy⟩ : Perm (Fin m)) = π * (θ ⟨y, hy⟩ : Perm (Fin m)) * π⁻¹) :
    π * π = 1 := by
  have hss : s * s = 1 := by rw [← pow_two]; exact hs2
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  refine perm_unique hm (π := π * π) (π' := 1) fun σ => ?_
  obtain ⟨y, rfl⟩ := θ.surjective σ
  have h1 := cap_rel θ hs hπ (y := y) (z := ⟨s * (y : MulAut V) * s⁻¹, hs y y.2⟩) rfl
  have h2 := cap_rel θ hs hπ (y := ⟨s * (y : MulAut V) * s⁻¹, hs y y.2⟩) (z := y)
    (by
      calc s * (s * (y : MulAut V) * s⁻¹) * s⁻¹ = (s * s) * y * (s⁻¹ * s⁻¹) := by group
        _ = y := by rw [hss, hsi, hss]; simp)
  calc π * π * (θ y : Perm (Fin m)) * (π * π)⁻¹
      = π * (π * (θ y : Perm (Fin m)) * π⁻¹) * π⁻¹ := by group
    _ = π * (θ ⟨s * (y : MulAut V) * s⁻¹, hs y y.2⟩ : Perm (Fin m)) * π⁻¹ := by rw [h1]
    _ = (θ y : Perm (Fin m)) := h2.symm
    _ = 1 * (θ y : Perm (Fin m)) * 1⁻¹ := by simp

private theorem cap_mul {m : ℕ} {Y : Subgroup (MulAut V)} (θ : ↥Y ≃* alternatingGroup (Fin m))
    {a b x : MulAut V} (ha : a ∈ Y) (hb : b ∈ Y) (hx : x ∈ Y) (h : x = a * b) :
    (θ ⟨x, hx⟩ : Perm (Fin m)) = (θ ⟨a, ha⟩ : Perm (Fin m)) * (θ ⟨b, hb⟩ : Perm (Fin m)) := by
  subst h
  have : (⟨a * b, hx⟩ : ↥Y) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
  rw [this, map_mul]
  rfl

private theorem cap_inv {m : ℕ} {Y : Subgroup (MulAut V)} (θ : ↥Y ≃* alternatingGroup (Fin m))
    {a x : MulAut V} (ha : a ∈ Y) (hx : x ∈ Y) (h : x = a⁻¹) :
    (θ ⟨x, hx⟩ : Perm (Fin m)) = (θ ⟨a, ha⟩ : Perm (Fin m))⁻¹ := by
  subst h
  have : (⟨a⁻¹, hx⟩ : ↥Y) = (⟨a, ha⟩ : ↥Y)⁻¹ := rfl
  rw [this, map_inv]
  rfl

theorem partner_prod {m : ℕ} (hm : 5 ≤ m) {Y : Subgroup (MulAut V)}
    (θ : ↥Y ≃* alternatingGroup (Fin m)) {s : MulAut V} (hs : ∀ y ∈ Y, s * y * s⁻¹ ∈ Y)
    (hs2 : s ^ 2 = 1) {π : Perm (Fin m)}
    (hπ : ∀ (y : MulAut V) (hy : y ∈ Y),
      (θ ⟨s * y * s⁻¹, hs y hy⟩ : Perm (Fin m)) = π * (θ ⟨y, hy⟩ : Perm (Fin m)) * π⁻¹)
    {y : MulAut V} (hy : y ∈ Y) :
    ∃ (hs'' : ∀ z ∈ Y, (y⁻¹ * s * y) * z * (y⁻¹ * s * y)⁻¹ ∈ Y)
      (hprod : s * (y⁻¹ * s * y) ∈ Y),
      (∀ (z : MulAut V) (hz : z ∈ Y),
        (θ ⟨(y⁻¹ * s * y) * z * (y⁻¹ * s * y)⁻¹, hs'' z hz⟩ : Perm (Fin m)) =
          ((θ ⟨y, hy⟩ : Perm (Fin m))⁻¹ * π * (θ ⟨y, hy⟩ : Perm (Fin m))) *
            (θ ⟨z, hz⟩ : Perm (Fin m)) *
            ((θ ⟨y, hy⟩ : Perm (Fin m))⁻¹ * π * (θ ⟨y, hy⟩ : Perm (Fin m)))⁻¹) ∧
      (θ ⟨s * (y⁻¹ * s * y), hprod⟩ : Perm (Fin m)) =
        π * ((θ ⟨y, hy⟩ : Perm (Fin m))⁻¹ * π * (θ ⟨y, hy⟩ : Perm (Fin m))) := by
  have hππ := perm_mul_self hm θ hs hs2 hπ
  have hπi : π⁻¹ = π := inv_eq_of_mul_eq_one_right hππ
  have hss : s * s = 1 := by rw [← pow_two]; exact hs2
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  have hyi : y⁻¹ ∈ Y := Y.inv_mem hy
  have hconj : ∀ z ∈ Y, y * z * y⁻¹ ∈ Y := fun z hz => Y.mul_mem (Y.mul_mem hy hz) hyi
  have hs'' : ∀ z ∈ Y, (y⁻¹ * s * y) * z * (y⁻¹ * s * y)⁻¹ ∈ Y := by
    intro z hz
    have e : (y⁻¹ * s * y) * z * (y⁻¹ * s * y)⁻¹ = y⁻¹ * (s * (y * z * y⁻¹) * s⁻¹) * y := by
      group
    rw [e]
    exact Y.mul_mem (Y.mul_mem hyi (hs _ (hconj z hz))) hy
  have hv : s * y⁻¹ * s⁻¹ ∈ Y := hs _ hyi
  have hprod : s * (y⁻¹ * s * y) ∈ Y := by
    have e : s * (y⁻¹ * s * y) = (s * y⁻¹ * s⁻¹) * y := by rw [hsi]; group
    rw [e]
    exact Y.mul_mem hv hy
  refine ⟨hs'', hprod, fun z hz => ?_, ?_⟩
  · have hu := hconj z hz
    have hw := hs _ hu
    have h1 := cap_mul θ (Y.mul_mem hy hz) hyi hu rfl
    have h2 := cap_mul θ hy hz (Y.mul_mem hy hz) rfl
    have h3 := cap_inv θ hy hyi rfl
    have h4 := hπ _ hu
    have h5 := cap_mul θ (Y.mul_mem hyi hw) hy (hs'' z hz) (by group)
    have h6 := cap_mul θ hyi hw (Y.mul_mem hyi hw) rfl
    rw [h5, h6, h4, h1, h2, h3]
    group
  · have h1 := cap_mul θ hv hy hprod (by rw [hsi]; group)
    have h2 := hπ _ hyi
    have h3 := cap_inv θ hy hyi rfl
    rw [h1, h2, h3, hπi]
    group

theorem exists_partner_one {m : ℕ} (hm : 7 ≤ m) {c d : Fin m} (hcd : c ≠ d) :
    ∃ y : alternatingGroup (Fin m), ∃ r u : Fin m, r ≠ u ∧ r ≠ c ∧ r ≠ d ∧ u ≠ c ∧ u ≠ d ∧
      (y : Perm (Fin m))⁻¹ * swap c d * (y : Perm (Fin m)) = swap r u := by
  classical
  have hcard : 1 < (Finset.univ \ {c, d} : Finset (Fin m)).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      Finset.card_pair hcd, Fintype.card_fin]
    omega
  obtain ⟨r, hr, u, hu, hru⟩ := Finset.one_lt_card.1 hcard
  simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
    true_and, not_or] at hr hu
  have hy : swap c r * swap d u ∈ alternatingGroup (Fin m) := by
    rw [Perm.mem_alternatingGroup, map_mul, Perm.sign_swap (Ne.symm hr.1),
      Perm.sign_swap (Ne.symm hu.2)]
    decide
  refine ⟨⟨swap c r * swap d u, hy⟩, r, u, hru, hr.1, hr.2, hu.1, hu.2, ?_⟩
  have e1 : (swap c r * swap d u) r = c := by
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne hr.2 hru, swap_apply_right]
  have e2 : (swap c r * swap d u) u = d := by
    rw [Perm.mul_apply, swap_apply_right, swap_apply_of_ne_of_ne (Ne.symm hcd) (Ne.symm hr.2)]
  have h := swap_apply_apply (swap c r * swap d u)⁻¹ c d
  rw [inv_inv] at h
  show (swap c r * swap d u)⁻¹ * swap c d * (swap c r * swap d u) = swap r u
  rw [← h, Perm.inv_eq_iff_eq.2 e1.symm, Perm.inv_eq_iff_eq.2 e2.symm]

theorem exists_partner_two {m : ℕ} (hm : 7 ≤ m) {π : Perm (Fin m)} (hπ : π * π = 1)
    {p q p' q' : Fin m} (hp : π p = q) (hp' : π p' = q') (hpq : p ≠ q) (hpp' : p ≠ p')
    (hpq' : p ≠ q') (hqp' : q ≠ p') (hqq' : q ≠ q') (hpq'' : p' ≠ q') :
    ∃ y : alternatingGroup (Fin m),
      ((y : Perm (Fin m))⁻¹ * π * (y : Perm (Fin m))) p = p' ∧
      ((y : Perm (Fin m))⁻¹ * π * (y : Perm (Fin m))) p' = p ∧
      ((y : Perm (Fin m))⁻¹ * π * (y : Perm (Fin m))) q = q' ∧
      ((y : Perm (Fin m))⁻¹ * π * (y : Perm (Fin m))) q' = q ∧
      (∀ i, i ≠ p → i ≠ q → i ≠ p' → i ≠ q' →
        ((y : Perm (Fin m))⁻¹ * π * (y : Perm (Fin m))) i = π i) := by
  have _ := hm
  have hπx : ∀ x, π (π x) = x := fun x => by
    have := congrArg (fun f : Perm (Fin m) => f x) hπ
    simpa using this
  have hq : π q = p := by rw [← hp, hπx]
  have hq' : π q' = p' := by rw [← hp', hπx]
  have hy : swap q p' * swap p p' ∈ alternatingGroup (Fin m) := by
    rw [Perm.mem_alternatingGroup, map_mul, Perm.sign_swap hqp', Perm.sign_swap hpp']
    decide
  have y1 : (swap q p' * swap p p') p = q := by
    rw [Perm.mul_apply, swap_apply_left, swap_apply_right]
  have y2 : (swap q p' * swap p p') p' = p := by
    rw [Perm.mul_apply, swap_apply_right, swap_apply_of_ne_of_ne hpq hpp']
  have y3 : (swap q p' * swap p p') q = p' := by
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne (Ne.symm hpq) hqp', swap_apply_left]
  have y4 : (swap q p' * swap p p') q' = q' := by
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne (Ne.symm hpq') (Ne.symm hpq''),
      swap_apply_of_ne_of_ne (Ne.symm hqq') (Ne.symm hpq'')]
  refine ⟨⟨swap q p' * swap p p', hy⟩, ?_, ?_, ?_, ?_, ?_⟩
  · show (swap q p' * swap p p')⁻¹ (π ((swap q p' * swap p p') p)) = p'
    rw [y1, hq]
    exact Perm.inv_eq_iff_eq.2 y2.symm
  · show (swap q p' * swap p p')⁻¹ (π ((swap q p' * swap p p') p')) = p
    rw [y2, hp]
    exact Perm.inv_eq_iff_eq.2 y1.symm
  · show (swap q p' * swap p p')⁻¹ (π ((swap q p' * swap p p') q)) = q'
    rw [y3, hp']
    exact Perm.inv_eq_iff_eq.2 y4.symm
  · show (swap q p' * swap p p')⁻¹ (π ((swap q p' * swap p p') q')) = q
    rw [y4, hq']
    exact Perm.inv_eq_iff_eq.2 y3.symm
  · intro i h1 h2 h3 h4
    have hπi : π i ≠ p ∧ π i ≠ q ∧ π i ≠ p' ∧ π i ≠ q' := by
      refine ⟨fun h => h2 ?_, fun h => h1 ?_, fun h => h4 ?_, fun h => h3 ?_⟩
      · rw [← hπx i, h, hp]
      · rw [← hπx i, h, hq]
      · rw [← hπx i, h, hp']
      · rw [← hπx i, h, hq']
    have hfix : ∀ x, x ≠ p → x ≠ q → x ≠ p' → (swap q p' * swap p p') x = x := fun x a b c => by
      rw [Perm.mul_apply, swap_apply_of_ne_of_ne a c, swap_apply_of_ne_of_ne b c]
    show (swap q p' * swap p p')⁻¹ (π ((swap q p' * swap p p') i)) = π i
    rw [hfix i h1 h2 h3]
    exact Perm.inv_eq_iff_eq.2 (hfix _ hπi.1 hπi.2.1 hπi.2.2.1).symm

end CFSG.CGT.PushingUpLit.CGT6
