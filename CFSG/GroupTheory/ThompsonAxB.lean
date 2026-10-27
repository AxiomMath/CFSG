module

public import CFSG.LocalAnalysis.ComponentClassification.CoprimeAutomorphisms

public section

namespace CFSG.GroupTheory

open CFSG.ComponentClassification.CoprimeAutomorphisms

theorem thompson_A_times_B {p : ℕ} [hp : Fact p.Prime] {R A B : Type*} [Group R] [Group A]
    [Group B] [Finite R] [Finite A] [Finite B] (hR : IsPGroup p R) (hA : ¬ p ∣ Nat.card A)
    (hB : IsPGroup p B) (α : A →* MulAut R) (β : B →* MulAut R)
    (hcomm : ∀ a b, α a * β b = β b * α a)
    (hfix : ∀ a r, (∀ b, β b r = r) → α a r = r) : ∀ a, α a = 1 := by
  have hcomm' : ∀ a b r, α a (β b r) = β b (α a r) := fun a b r => by
    rw [← MulAut.mul_apply, hcomm, MulAut.mul_apply]
  let ext : A → MulAut (R ⋊[β] B) := fun a =>
    { toFun := fun t => ⟨α a t.left, t.right⟩
      invFun := fun t => ⟨(α a)⁻¹ t.left, t.right⟩
      left_inv := fun t => by
        apply SemidirectProduct.ext
        · exact MulAut.inv_apply_self R (α a) t.left
        · rfl
      right_inv := fun t => by
        apply SemidirectProduct.ext
        · exact MulAut.apply_inv_self R (α a) t.left
        · rfl
      map_mul' := fun t s => by
        apply SemidirectProduct.ext
        · change α a (t.left * β t.right s.left) = α a t.left * β t.right (α a s.left)
          rw [map_mul, hcomm']
        · rfl }
  have hext : ∀ (a : A) (t : R ⋊[β] B), ext a t = ⟨α a t.left, t.right⟩ := fun _ _ => rfl
  let φ : A →* MulAut (R ⋊[β] B) :=
    { toFun := ext
      map_one' := MulEquiv.ext fun t => by
        rw [hext, map_one]
        rfl
      map_mul' := fun a a' => MulEquiv.ext fun t => by
        rw [MulAut.mul_apply, hext, hext, hext, map_mul]
        rfl }
  have hφ : ∀ (a : A) (t : R ⋊[β] B), φ a t = ⟨α a t.left, t.right⟩ := fun _ _ => rfl
  have : Finite (R ⋊[β] B) :=
    Finite.of_injective (fun t : R ⋊[β] B => (t.left, t.right)) fun t s h =>
      SemidirectProduct.ext (congrArg Prod.fst h) (congrArg Prod.snd h)
  have hT : IsPGroup p (R ⋊[β] B) := by
    rw [IsPGroup.iff_card] at hR hB ⊢
    obtain ⟨m, hm⟩ := hR
    obtain ⟨n, hn⟩ := hB
    exact ⟨m + n, by rw [SemidirectProduct.card, hm, hn, pow_add]⟩
  let CRB : Subgroup R :=
    { carrier := {r | ∀ b, β b r = r}
      mul_mem' := fun {x y} hx hy b => by rw [map_mul, hx b, hy b]
      one_mem' := fun b => map_one _
      inv_mem' := fun {x} hx b => by rw [map_inv, hx b] }
  let U : Subgroup (R ⋊[β] B) :=
    CRB.map SemidirectProduct.inl ⊔ (⊤ : Subgroup B).map SemidirectProduct.inr
  have hself : Subgroup.centralizer (U : Set (R ⋊[β] B)) ≤ U := by
    intro t ht
    have hcentr : ∀ b : B, (SemidirectProduct.inr b : R ⋊[β] B) * t =
        t * SemidirectProduct.inr b := fun b =>
      Subgroup.mem_centralizer_iff.1 ht _
        (Subgroup.mem_sup_right ⟨b, Subgroup.mem_top b, rfl⟩)
    have hleft : t.left ∈ CRB := by
      intro b
      have h := congrArg SemidirectProduct.left (hcentr b)
      simpa [SemidirectProduct.mul_left] using h
    rw [← SemidirectProduct.inl_left_mul_inr_right t]
    exact mul_mem (Subgroup.mem_sup_left ⟨t.left, hleft, rfl⟩)
      (Subgroup.mem_sup_right ⟨t.right, Subgroup.mem_top _, rfl⟩)
  intro a
  have hfixU : ∀ t ∈ U, φ a t = t := by
    have hle : U ≤ (φ a).toMonoidHom.eqLocus (MonoidHom.id _) := by
      refine sup_le ?_ ?_
      · rintro _ ⟨r, hr, rfl⟩
        change φ a (SemidirectProduct.inl r) = SemidirectProduct.inl r
        rw [hφ]
        apply SemidirectProduct.ext
        · exact hfix a r hr
        · rfl
      · rintro _ ⟨b, -, rfl⟩
        change φ a (SemidirectProduct.inr b) = SemidirectProduct.inr b
        rw [hφ]
        apply SemidirectProduct.ext
        · change α a 1 = 1
          exact map_one _
        · rfl
    exact fun t ht => hle ht
  have hpow : φ a ^ orderOf a = 1 := by
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  have hcop : (orderOf a).Coprime (Nat.card (R ⋊[β] B)) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hT
    rw [hk]
    refine Nat.Coprime.pow_right k ((Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp.out).2
      fun h => hA (h.trans (orderOf_dvd_natCard a)))))
  have h1 := eq_one_of_self_centralizing p hT U hself (φ a) (orderOf a) hpow hcop hfixU
  refine MulEquiv.ext fun r => ?_
  have h2 := congrArg (fun ψ : MulAut (R ⋊[β] B) => (ψ (SemidirectProduct.inl r)).left) h1
  simpa [hφ] using h2

end CFSG.GroupTheory
