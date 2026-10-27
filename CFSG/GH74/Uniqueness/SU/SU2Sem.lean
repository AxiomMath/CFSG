module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureLinearPointKernelSemilinear
public import CFSG.GroupTheory.SteinbergBKSemilinearFixedBasis

public section

open CFSG.ShultStronglyClosedTI.LinearChain
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ShultStronglyClosedTI.CyclicSemiregular CFSG.GroupTheory.SteinbergBK

namespace CFSG.GH74.Uniqueness.SU.SU2.Sem

variable {B Q : Type} [Group B] [CommGroup Q]

abbrev zmodModule2 (hQ : ∀ q : Q, q * q = 1) : Module (ZMod 2) (Additive Q) :=
  AddCommGroup.zmodModule (n := 2) fun v => by
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero, sq]
    exact hQ v.toMul

theorem exists_semilinear [Finite B] [Finite Q] (hQ : ∀ q : Q, q * q = 1) (ρ : B →* MulAut Q)
    {E : Subgroup B} [E.Normal] (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hEtr : ∀ v w : Q, v ≠ 1 → w ≠ 1 → ∃ x ∈ E, ρ x v = w)
    (hEinj : ∀ x ∈ E, (∀ v, ρ x v = v) → x = 1) (hEcard : Nat.card E + 1 = Nat.card Q) {e : ℕ}
    (hQe : Nat.card Q = 2 ^ e) (he : 1 ≤ e) :
    ∃ (k₀ : Type) (_ : Field k₀) (_ : Finite k₀), Nat.card k₀ = 2 ^ e ∧
      ∃ (ev : k₀ ≃ Q) (ι : B →* k₀ˣ ⋊[ringAutUnits k₀] RingAut k₀),
        (∀ b : B, ι b = 1 ↔ ∀ v, ρ b v = v) ∧
        (∀ (b : B) (a : k₀), ρ b (ev a) = ev (((ι b).left : k₀) * (ι b).right a)) := by
  classical
  let _ : Module (ZMod 2) (Additive Q) := zmodModule2 hQ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdim : Module.finrank (ZMod 2) (Additive Q) = e := by
    have h1 := FiniteField.pow_finrank_eq_natCard 2 (Additive Q)
    have h2 : Nat.card (Additive Q) = Nat.card Q := rfl
    rw [h2, hQe] at h1
    exact Nat.pow_right_injective (le_refl 2) h1
  let ρ' : B →* LinearMap.GeneralLinearGroup (ZMod 2) (Additive Q) := (mulAutGL 2 Q).comp ρ
  have hρ' : ∀ (b : B) (v : Additive Q),
      ((ρ' b : LinearMap.GeneralLinearGroup (ZMod 2) (Additive Q)) :
        Module.End (ZMod 2) (Additive Q)) v = Additive.ofMul (ρ b v.toMul) := fun _ _ => rfl
  have htrans : ∀ v w : Additive Q, v ≠ 0 → w ≠ 0 → ∃ x ∈ E,
      ((ρ' x : LinearMap.GeneralLinearGroup (ZMod 2) (Additive Q)) :
        Module.End (ZMod 2) (Additive Q)) v = w := by
    intro v w hv hw
    obtain ⟨x, hx, hxv⟩ := hEtr v.toMul w.toMul (fun h => hv (by simpa using h))
      (fun h => hw (by simpa using h))
    exact ⟨x, hx, by rw [hρ', hxv]; rfl⟩
  have hXinj : ∀ x ∈ E, ρ' x = 1 → x = 1 := by
    intro x hx h1
    apply hEinj x hx
    intro v
    have := congrArg (fun g : LinearMap.GeneralLinearGroup (ZMod 2) (Additive Q) =>
      ((g : Module.End (ZMod 2) (Additive Q)) (Additive.ofMul v)).toMul) h1
    simpa [hρ'] using this
  have hXcard : Nat.card E = 2 ^ e - 1 := by omega
  obtain ⟨k₀, hF, hfin, hk₀, ev, ι, hker, hcompat, -⟩ :=
    semilinear_of_transitive_commutative he hdim ρ' hEc htrans hXinj hXcard
  refine ⟨k₀, hF, hfin, hk₀, ev.toEquiv.trans (Additive.toMul : Additive Q ≃ Q), ι, ?_, ?_⟩
  · intro b
    have : ι b = 1 ↔ b ∈ ρ'.ker := by rw [← hker]; rfl
    rw [this, MonoidHom.mem_ker]
    constructor
    · intro h v
      have := congrArg (fun g : LinearMap.GeneralLinearGroup (ZMod 2) (Additive Q) =>
        ((g : Module.End (ZMod 2) (Additive Q)) (Additive.ofMul v)).toMul) h
      simpa [hρ'] using this
    · intro h
      apply Units.ext
      apply LinearMap.ext
      intro v
      rw [Units.val_one, Module.End.one_apply, hρ']
      exact congrArg Additive.ofMul (h v.toMul)
  · intro b a
    have := hcompat b a
    rw [hρ'] at this
    exact congrArg Additive.toMul this

theorem card_le_of_faithful [Finite B] [Finite Q] (hQ : ∀ q : Q, q * q = 1) (ρ : B →* MulAut Q)
    {E : Subgroup B} [E.Normal] (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hEtr : ∀ v w : Q, v ≠ 1 → w ≠ 1 → ∃ x ∈ E, ρ x v = w)
    (hEinj : ∀ x ∈ E, (∀ v, ρ x v = v) → x = 1) (hEcard : Nat.card E + 1 = Nat.card Q) {e : ℕ}
    (hQe : Nat.card Q = 2 ^ e) (he : 1 ≤ e) (hfaith : ∀ b : B, (∀ v, ρ b v = v) → b = 1) :
    Nat.card B ≤ (2 ^ e - 1) * e := by
  obtain ⟨k₀, hF, hfin, hk₀, ev, ι, hι, -⟩ := exists_semilinear hQ ρ hEc hEtr hEinj hEcard hQe he
  have hinj : Function.Injective ι := by
    rw [injective_iff_map_eq_one]
    intro b hb
    exact hfaith b ((hι b).1 hb)
  obtain ⟨-, -, -, -, hcardAut, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality (F := k₀) Nat.prime_two he hk₀
  have hcard : Nat.card (RingAut k₀) = e := hcardAut
  have : Finite (RingAut k₀) := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  have : Finite (k₀ˣ ⋊[ringAutUnits k₀] RingAut k₀) :=
    Finite.of_equiv (k₀ˣ × RingAut k₀) SemidirectProduct.equivProd.symm
  have h1 := Nat.card_le_card_of_injective ι hinj
  rw [SemidirectProduct.card, Nat.card_units, hk₀, hcard] at h1
  exact h1

theorem isCyclic_of_isPGroup_faithful [Finite B] [Finite Q] (hQ : ∀ q : Q, q * q = 1)
    (ρ : B →* MulAut Q) {E : Subgroup B} [E.Normal] (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hEtr : ∀ v w : Q, v ≠ 1 → w ≠ 1 → ∃ x ∈ E, ρ x v = w)
    (hEinj : ∀ x ∈ E, (∀ v, ρ x v = v) → x = 1) (hEcard : Nat.card E + 1 = Nat.card Q) {e : ℕ}
    (hQe : Nat.card Q = 2 ^ e) (he : 1 ≤ e) {T : Subgroup B} (hT : IsPGroup 2 T)
    (hfaith : ∀ t ∈ T, (∀ v, ρ t v = v) → t = 1) : IsCyclic T := by
  obtain ⟨k₀, hF, hfin, hk₀, ev, ι, hι, -⟩ := exists_semilinear hQ ρ hEc hEtr hEinj hEcard hQe he
  obtain ⟨σ₀, -, -, hzp, -, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality (F := k₀) Nat.prime_two he hk₀
  have hcyc : IsCyclic (RingAut k₀) :=
    ⟨⟨σ₀, fun τ => by
      have : τ ∈ Subgroup.zpowers σ₀ := by rw [hzp]; trivial
      exact this⟩⟩
  let f : T →* RingAut k₀ := SemidirectProduct.rightHom.comp (ι.comp T.subtype)
  refine isCyclic_of_injective f ?_
  rw [injective_iff_map_eq_one]
  intro s hs
  have hs' : (ι (s : B)).right = 1 := hs
  have hodd : Odd (Nat.card k₀ˣ) := by
    rw [Nat.card_units, hk₀]
    have h2 : 2 ∣ 2 ^ e := dvd_pow_self 2 (by omega)
    have hpos : 0 < 2 ^ e := by positivity
    rw [Nat.odd_iff]
    omega
  set g := ι (s : B) with hg
  have hgeq : g = SemidirectProduct.inl g.left := by
    apply SemidirectProduct.ext
    · simp
    · simp [hs']
  obtain ⟨j, hj⟩ := hT s
  have hgj : g ^ 2 ^ j = 1 := by
    rw [hg, ← map_pow]
    have : ((s : B)) ^ 2 ^ j = 1 := by
      have := congrArg Subtype.val hj
      simpa using this
    rw [this, map_one]
  have hgn : g ^ Nat.card k₀ˣ = 1 := by
    rw [hgeq, ← map_pow, pow_card_eq_one', map_one]
  have hcop : Nat.Coprime (Nat.card k₀ˣ) (2 ^ j) := by
    refine Nat.Coprime.pow_right _ (Nat.Coprime.symm ?_)
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
    rw [Nat.odd_iff] at hodd
    omega
  have hg1 : g = 1 := by
    have h1 : orderOf g ∣ Nat.card k₀ˣ := orderOf_dvd_of_pow_eq_one hgn
    have h2 : orderOf g ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one hgj
    have h3 : orderOf g ∣ Nat.gcd (Nat.card k₀ˣ) (2 ^ j) := Nat.dvd_gcd h1 h2
    rw [hcop] at h3
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)
  have : s = 1 := Subtype.ext (hfaith (s : B) s.2 ((hι (s : B)).1 hg1))
  exact this

theorem card_fixed_sq_of_involution [Finite B] [Finite Q] (hQ : ∀ q : Q, q * q = 1)
    (ρ : B →* MulAut Q) {E : Subgroup B} [E.Normal] (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hEtr : ∀ v w : Q, v ≠ 1 → w ≠ 1 → ∃ x ∈ E, ρ x v = w)
    (hEinj : ∀ x ∈ E, (∀ v, ρ x v = v) → x = 1) (hEcard : Nat.card E + 1 = Nat.card Q) {e : ℕ}
    (hQe : Nat.card Q = 2 ^ e) (he : 1 ≤ e) {t : B} (ht : orderOf t = 2)
    (hnt : ∃ v, ρ t v ≠ v) : Nat.card {v : Q // ρ t v = v} ^ 2 = Nat.card Q := by
  obtain ⟨k₀, hF, hfin, hk₀, ev, ι, hι, hcompat⟩ :=
    exists_semilinear hQ ρ hEc hEtr hEinj hEcard hQe he
  have hit1 : ι t ≠ 1 := fun h => by
    obtain ⟨v, hv⟩ := hnt
    exact hv ((hι t).1 h v)
  have hit2 : ι t ^ 2 = 1 := by rw [← map_pow, ← ht, pow_orderOf_eq_one, map_one]
  have hmul : ι t * ι t = 1 := by rwa [pow_two] at hit2
  set g := ι t with hg
  set σ : RingAut k₀ := g.right with hσdef
  set c : k₀ˣ := g.left with hcdef
  have hright : σ * σ = 1 := by
    have := congrArg SemidirectProduct.right hmul
    simpa [SemidirectProduct.mul_right] using this
  have hleft : c * ringAutUnits k₀ σ c = 1 := by
    have := congrArg SemidirectProduct.left hmul
    simpa [SemidirectProduct.mul_left] using this
  have hσσ : ∀ x : k₀, σ (σ x) = x := fun x => by
    have := congrArg (fun τ : RingAut k₀ => τ x) hright
    simpa using this
  have hcc : (c : k₀) * σ c = 1 := by
    have := congrArg (fun u : k₀ˣ => (u : k₀)) hleft
    simpa [coe_ringAutUnits_apply] using this
  have hodd : Odd (Nat.card k₀ˣ) := by
    rw [Nat.card_units, hk₀]
    have h2 : 2 ∣ 2 ^ e := dvd_pow_self 2 (by omega)
    have hpos : 0 < 2 ^ e := by positivity
    rw [Nat.odd_iff]
    omega
  have hσ1 : σ ≠ 1 := by
    intro h1
    apply hit1
    have hc2 : c * c = 1 := by rw [h1, map_one] at hleft; simpa using hleft
    have hord : orderOf c ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hc2)
    have hord2 : orderOf c ∣ Nat.card k₀ˣ := orderOf_dvd_natCard c
    have hcop : Nat.Coprime (Nat.card k₀ˣ) 2 := by
      refine Nat.Coprime.symm ?_
      rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
      rw [Nat.odd_iff] at hodd
      omega
    have h3 : orderOf c ∣ Nat.gcd (Nat.card k₀ˣ) 2 := Nat.dvd_gcd hord2 hord
    rw [hcop] at h3
    have hc1 : c = 1 := orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)
    apply SemidirectProduct.ext
    · simpa using hc1
    · simpa using h1
  have hσord : orderOf σ = 2 := orderOf_eq_prime (by rw [pow_two]; exact hright) hσ1
  have hah : ∀ x : k₀, (c : k₀) * σ ((c : k₀) * σ x) = x := fun x => by
    rw [map_mul, hσσ, ← mul_assoc, hcc, one_mul]
  let a : k₀ ≃+ k₀ :=
    { toFun := fun x => (c : k₀) * σ x
      invFun := fun x => (c : k₀) * σ x
      left_inv := hah
      right_inv := hah
      map_add' := fun x y => by simp [map_add, mul_add] }
  have ha : ∀ (l x : k₀), a (l • x) = σ l • a x := fun l x => by
    change (c : k₀) * σ (l * x) = σ l * ((c : k₀) * σ x)
    rw [map_mul]; ring
  have hah2 : ∀ x : k₀, (⇑a)^[2] x = x := fun x => by
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id]
    exact hah x
  obtain ⟨h2e, -, -, -, -, -, -, hcardfix⟩ :=
    coprime_finite_field_semilinear_fixed_basis (p := 2) (e := e) (h := 2) (m := 1)
      Nat.prime_two he hk₀ σ hσord (V := k₀) (by simp) a ha hah2
  have hequiv : {x : k₀ // a x = x} ≃ {v : Q // ρ t v = v} :=
    Equiv.subtypeEquiv ev (fun x => by
      have h' : ρ t (ev x) = ev (a x) := hcompat t x
      rw [h']
      exact ev.injective.eq_iff.symm)
  have hsub : Nat.card ↥(semilinearFixedSubmodule σ a ha) = Nat.card {x : k₀ // a x = x} := rfl
  have hcard1 : Nat.card {v : Q // ρ t v = v} = 2 ^ (e * 1 / 2) := by
    rw [← hcardfix, hsub]
    exact (Nat.card_congr hequiv).symm
  have hdiv : e * 1 / 2 * 2 = e := by rw [mul_one]; exact Nat.div_mul_cancel h2e
  rw [hcard1, hQe, ← pow_mul, hdiv]

end CFSG.GH74.Uniqueness.SU.SU2.Sem
