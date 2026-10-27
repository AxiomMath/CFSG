module

public import CFSG.ClassicalInvolution.LBalance.Glauberman.CoprimeAction
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.ClassicalInvolution.GlaubermanAut

section OddAction

variable {Λ : Type*} [Group Λ] [Finite Λ]

theorem exists_elementary_commutator_subgroup {A₀ : Subgroup Λ}
    (hcomm : ∀ a ∈ A₀, ∀ b ∈ A₀, a * b = b * a) (hp : IsPGroup 2 A₀) {x : Λ}
    (hxA : ∀ a ∈ A₀, x * a * x⁻¹ ∈ A₀) (hxA' : ∀ a ∈ A₀, x⁻¹ * a * x ∈ A₀)
    (hodd : Odd (orderOf x)) (hnc : ∃ a ∈ A₀, x * a ≠ a * x) :
    ∃ U : Subgroup Λ, U ≤ A₀ ∧ (∀ u ∈ U, u * u = 1) ∧
      (∀ u ∈ U, x * u * x⁻¹ ∈ U ∧ x⁻¹ * u * x ∈ U) ∧ (∃ τ ∈ U, τ ≠ 1) ∧
      ∀ u ∈ U, ∃ u' ∈ U, u = u' * x * u'⁻¹ * x⁻¹ := by
  classical
  let _ : CommGroup A₀ := { (inferInstance : Group A₀) with
    mul_comm := fun a b => Subtype.ext (hcomm _ a.2 _ b.2) }
  have hxN : x ∈ Subgroup.normalizer (A₀ : Set Λ) := by
    rw [Subgroup.mem_normalizer_iff]
    intro a
    refine ⟨hxA a, fun h => ?_⟩
    simpa [mul_assoc] using hxA' _ h
  let ψ : Subgroup.normalizer (A₀ : Set Λ) →* MulAut A₀ := A₀.normalizerMonoidHom
  let φ : MulAut A₀ := ψ ⟨x, hxN⟩
  have hφ : ∀ a : A₀, ((φ a : A₀) : Λ) = x * a * x⁻¹ := fun a => rfl
  have hn : φ ^ orderOf x = 1 := by
    have h1 : (⟨x, hxN⟩ : Subgroup.normalizer (A₀ : Set Λ)) ^ orderOf x = 1 :=
      Subtype.ext (pow_orderOf_eq_one x)
    rw [← map_pow, h1, map_one]
  have hcop : Nat.Coprime (orderOf x) (Nat.card A₀) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hp
    rw [hk]
    exact Nat.Coprime.pow_right k hodd.coprime_two_right
  have hFR := fixedSubgroup_inf_commutatorSubgroup hn hcop
  have hFR' := fixedSubgroup_sup_commutatorSubgroup hn hcop
  set R := commutatorSubgroup φ with hR
  set F := fixedSubgroup φ with hF
  have hRne : R ≠ ⊥ := by
    intro h
    rw [h, sup_bot_eq] at hFR'
    obtain ⟨a, haA, hax⟩ := hnc
    apply hax
    have h1 : (⟨a, haA⟩ : A₀) ∈ F := by rw [hFR']; exact Subgroup.mem_top _
    have h2 : φ ⟨a, haA⟩ = ⟨a, haA⟩ := h1
    have h3 : x * a * x⁻¹ = a := congrArg Subtype.val h2
    calc x * a = x * a * x⁻¹ * x := by group
      _ = a * x := by rw [h3]
  let U' : Subgroup A₀ :=
    { carrier := {r | r ∈ R ∧ r * r = 1}
      one_mem' := ⟨R.one_mem, one_mul 1⟩
      mul_mem' := by
        rintro a b ⟨ha, ha2⟩ ⟨hb, hb2⟩
        refine ⟨R.mul_mem ha hb, ?_⟩
        calc a * b * (a * b) = (a * a) * (b * b) := by rw [mul_mul_mul_comm]
          _ = 1 := by rw [ha2, hb2, mul_one]
      inv_mem' := by
        rintro a ⟨ha, ha2⟩
        refine ⟨R.inv_mem ha, ?_⟩
        calc a⁻¹ * a⁻¹ = (a * a)⁻¹ := by rw [mul_inv_rev]
          _ = 1 := by rw [ha2, inv_one] }
  have hU'mem : ∀ r : A₀, r ∈ U' ↔ r ∈ R ∧ r * r = 1 := fun r => Iff.rfl
  have hφU' : ∀ r ∈ U', φ r ∈ U' := by
    intro r hr
    refine ⟨apply_mem_commutatorSubgroup φ hr.1, ?_⟩
    rw [← map_mul, hr.2, map_one]
  have hφsurj : ∀ r ∈ U', ∃ r' ∈ U', φ r' = r := by
    intro r hr
    let g : U' → U' := fun r => ⟨φ r, hφU' r r.2⟩
    have hg : Function.Injective g := fun a b hab =>
      Subtype.ext (φ.injective (congrArg Subtype.val hab))
    obtain ⟨r', hr'⟩ := Finite.injective_iff_surjective.1 hg ⟨r, hr⟩
    exact ⟨r', r'.2, congrArg Subtype.val hr'⟩
  refine ⟨U'.map A₀.subtype, Subgroup.map_subtype_le U', ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨r, hr, rfl⟩
    exact congrArg Subtype.val hr.2
  · rintro _ ⟨r, hr, rfl⟩
    refine ⟨⟨φ r, hφU' r hr, rfl⟩, ?_⟩
    obtain ⟨r', hr', hrr'⟩ := hφsurj r hr
    refine ⟨r', hr', ?_⟩
    have h1 : (r : Λ) = x * (r' : Λ) * x⁻¹ := by rw [← hrr']; rfl
    show (r' : Λ) = x⁻¹ * (r : Λ) * x
    rw [h1]
    group
  ·
    have hRnt : Nontrivial R := (Subgroup.nontrivial_iff_ne_bot R).2 hRne
    have hRp : IsPGroup 2 R := hp.of_injective R.subtype R.subtype_injective
    have h2d : 2 ∣ Nat.card R := by
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hRp
      have hne : Nat.card R ≠ 1 := by
        have := Finite.one_lt_card_iff_nontrivial.2 hRnt
        omega
      rw [hn] at hne ⊢
      rcases n with _ | n
      · simp at hne
      · exact dvd_pow_self 2 (Nat.succ_ne_zero n)
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 h2d
    have hz2 : z * z = 1 := by
      have : z ^ 2 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
      simpa [pow_two] using this
    have hz1 : z ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at hz
      omega
    refine ⟨(((z : R) : A₀) : Λ), ⟨(z : A₀), ⟨z.2, ?_⟩, rfl⟩, ?_⟩
    · exact congrArg (fun t : R => ((t : R) : A₀)) hz2
    · intro h
      apply hz1
      exact Subtype.ext (Subtype.ext h)
  ·
    let cH := commutatorHom φ
    have hcH : ∀ a : A₀, cH a = a * (φ a)⁻¹ := fun a => rfl
    have hcU' : ∀ u ∈ U', cH u ∈ U' := by
      intro u hu
      refine ⟨mul_inv_apply_mem_commutatorSubgroup φ u, ?_⟩
      have h1 : φ u * φ u = 1 := by rw [← map_mul, hu.2, map_one]
      rw [hcH]
      calc u * (φ u)⁻¹ * (u * (φ u)⁻¹) = (u * u) * ((φ u)⁻¹ * (φ u)⁻¹) := by
            rw [mul_mul_mul_comm]
        _ = 1 := by rw [hu.2, one_mul, ← mul_inv_rev, h1, inv_one]
    let f : U' → U' := fun u => ⟨cH u, hcU' u u.2⟩
    have hf : Function.Injective f := by
      intro a b hab
      have h1 : cH ((a : A₀) * (b : A₀)⁻¹) = 1 := by
        rw [map_mul, map_inv]
        have : cH a = cH b := congrArg Subtype.val hab
        rw [this, mul_inv_cancel]
      have h2 : (a : A₀) * (b : A₀)⁻¹ ∈ F ⊓ R := by
        refine ⟨?_, R.mul_mem a.2.1 (R.inv_mem b.2.1)⟩
        change φ ((a : A₀) * (b : A₀)⁻¹) = (a : A₀) * (b : A₀)⁻¹
        rw [hcH, mul_inv_eq_one] at h1
        exact h1.symm
      rw [hFR, Subgroup.mem_bot, mul_inv_eq_one] at h2
      exact Subtype.ext h2
    have hfs := Finite.injective_iff_surjective.1 hf
    rintro _ ⟨r, hr, rfl⟩
    obtain ⟨u', hu'⟩ := hfs ⟨r, hr⟩
    refine ⟨((u' : A₀) : Λ), ⟨u', u'.2, rfl⟩, ?_⟩
    have h1 : cH u' = r := congrArg Subtype.val hu'
    have h2 : ((cH u' : A₀) : Λ) = ((u' : A₀) : Λ) * (x * ((u' : A₀) : Λ) * x⁻¹)⁻¹ := by
      rw [hcH]
      rfl
    rw [h1] at h2
    show (r : Λ) = _
    rw [h2]
    group

end OddAction

end CFSG.ClassicalInvolution.GlaubermanAut
