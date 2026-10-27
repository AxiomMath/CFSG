module

public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.CharacterTheory.Semidihedral.PrimeFieldDegreeTwoAction

public section

namespace CFSG.Semidihedral.ExchangedEigensubgroups

noncomputable section

universe u v w

variable {R : Type u} [CommGroup R]

@[expose] def positiveGroup (α : MulAut R) : Subgroup R :=
  α.toMonoidHom.eqLocus (MonoidHom.id R)

@[expose] def negativeGroup (α : MulAut R) : Subgroup R :=
  α.toMonoidHom.eqLocus (invMonoidHom : R →* R)

theorem mem_positiveGroup (α : MulAut R) (r : R) :
    r ∈ positiveGroup α ↔ α r = r := Iff.rfl

theorem mem_negativeGroup (α : MulAut R) (r : R) :
    r ∈ negativeGroup α ↔ α r = r⁻¹ := Iff.rfl

theorem square_injective (hodd : Odd (Nat.card R)) :
    Function.Injective (fun r : R => r ^ 2) :=
  (Nat.coprime_two_right.mpr hodd).pow_left_bijective.1

theorem automorphism_involutive (α : MulAut R) (hα : α ^ 2 = 1) :
    Function.Involutive α := by
  intro r
  have h := congrArg (fun a : MulAut R => a r) hα
  simpa only [pow_two, MulAut.mul_apply, MulAut.one_apply] using h

theorem eigengroups_disjoint (hodd : Odd (Nat.card R)) (α : MulAut R) :
    Disjoint (positiveGroup α) (negativeGroup α) := by
  apply Subgroup.disjoint_def.mpr
  intro r hp hn
  have hri : r = r⁻¹ := (mem_positiveGroup α r).mp hp |>.symm.trans
    ((mem_negativeGroup α r).mp hn)
  have hsquare : r ^ 2 = (1 : R) ^ 2 := by
    calc
      r ^ 2 = r * r := pow_two r
      _ = r⁻¹ * r := congrArg (fun x : R => x * r) hri
      _ = 1 := inv_mul_cancel r
      _ = 1 ^ 2 := by simp
  exact square_injective hodd hsquare

theorem eigengroups_factorization (hodd : Odd (Nat.card R))
    (α : MulAut R) (hα : α ^ 2 = 1) (r : R) :
    ∃ a ∈ positiveGroup α, ∃ b ∈ negativeGroup α, a * b = r := by
  obtain ⟨x, hx⟩ := (Nat.coprime_two_right.mpr hodd).pow_left_bijective.2 r
  have hinv := automorphism_involutive α hα x
  refine ⟨x * α x, ?_, x * (α x)⁻¹, ?_, ?_⟩
  · change α (x * α x) = x * α x
    rw [map_mul, hinv, mul_comm]
  · change α (x * (α x)⁻¹) = (x * (α x)⁻¹)⁻¹
    rw [map_mul, map_inv, hinv, mul_inv_rev, inv_inv]
  · calc
      (x * α x) * (x * (α x)⁻¹) = (x * x) * (α x * (α x)⁻¹) := by ac_rfl
      _ = x ^ 2 := by rw [mul_inv_cancel, mul_one, pow_two]
      _ = r := hx

theorem eigengroups_isComplement (hodd : Odd (Nat.card R))
    (α : MulAut R) (hα : α ^ 2 = 1) :
    (positiveGroup α).IsComplement' (negativeGroup α) := by
  refine ⟨Subgroup.mul_injective_of_disjoint (eigengroups_disjoint hodd α), ?_⟩
  intro r
  obtain ⟨a, ha, b, hb, hab⟩ := eigengroups_factorization hodd α hα r
  exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), hab⟩

@[expose] def eigenProductEquiv (hodd : Odd (Nat.card R))
    (α : MulAut R) (hα : α ^ 2 = 1) :
    positiveGroup α × negativeGroup α ≃* R :=
  OddFieldLift.internalDirectEquiv _ _
    (fun r _ => Subgroup.mem_center_iff.mpr (fun s => mul_comm s r))
    (eigengroups_isComplement hodd α hα)

theorem eigenProductEquiv_apply (hodd : Odd (Nat.card R))
    (α : MulAut R) (hα : α ^ 2 = 1)
    (r : positiveGroup α × negativeGroup α) :
    eigenProductEquiv hodd α hα r = (r.1 : R) * r.2 := rfl

theorem eigengroups_card_mul (hodd : Odd (Nat.card R))
    (α : MulAut R) (hα : α ^ 2 = 1) :
    Nat.card R = Nat.card (positiveGroup α) * Nat.card (negativeGroup α) := by
  rw [← Nat.card_congr (eigenProductEquiv hodd α hα).toEquiv, Nat.card_prod]

theorem exchange_identity {J : Type v} [Group J] (ρ : J →* MulAut R)
    (t d : J) (hρt : ∀ r : R, ρ t r = r⁻¹) (α : MulAut R)
    (hexchange : ρ d * α * (ρ d)⁻¹ = ρ t * α) (r : R) :
    ρ d (α r) = (α (ρ d r))⁻¹ := by
  have h := congrArg (fun a : MulAut R => a (ρ d r)) hexchange
  simpa only [MulAut.mul_apply, MulAut.inv_apply_self, hρt] using h

theorem exchange_positive_iff (α δ : MulAut R)
    (hexchange : ∀ r : R, δ (α r) = (α (δ r))⁻¹) (r : R) :
    δ r ∈ negativeGroup α ↔ r ∈ positiveGroup α := by
  rw [mem_negativeGroup, mem_positiveGroup]
  constructor
  · intro h
    apply δ.injective
    rw [hexchange, h, inv_inv]
  · intro h
    have he := hexchange r
    rw [h] at he
    exact inv_injective (he.symm.trans (inv_inv (δ r)).symm)

@[expose] def exchangeEquiv (α δ : MulAut R)
    (hexchange : ∀ r : R, δ (α r) = (α (δ r))⁻¹) :
    positiveGroup α ≃* negativeGroup α where
  toFun r := ⟨δ r, (exchange_positive_iff α δ hexchange r).mpr r.property⟩
  invFun r := ⟨δ⁻¹ r, (exchange_positive_iff α δ hexchange (δ⁻¹ r)).mp
    (by simpa only [MulAut.apply_inv_self] using r.property)⟩
  left_inv r := Subtype.ext (MulAut.inv_apply_self R δ (r : R))
  right_inv r := Subtype.ext (MulAut.apply_inv_self R δ (r : R))
  map_mul' r s := Subtype.ext (map_mul δ (r : R) (s : R))

theorem exchangeEquiv_apply (α δ : MulAut R)
    (hexchange : ∀ r : R, δ (α r) = (α (δ r))⁻¹) (r : positiveGroup α) :
    (exchangeEquiv α δ hexchange r : R) = δ r := rfl

theorem exchangeEquiv_symm_apply (α δ : MulAut R)
    (hexchange : ∀ r : R, δ (α r) = (α (δ r))⁻¹) (r : negativeGroup α) :
    ((exchangeEquiv α δ hexchange).symm r : R) = δ⁻¹ r := rfl

theorem eigengroups_card_eq (α δ : MulAut R)
    (hexchange : ∀ r : R, δ (α r) = (α (δ r))⁻¹) :
    Nat.card (positiveGroup α) = Nat.card (negativeGroup α) :=
  Nat.card_congr (exchangeEquiv α δ hexchange).toEquiv

theorem eigengroups_card_square (hodd : Odd (Nat.card R))
    (α : MulAut R) (hα : α ^ 2 = 1) (δ : MulAut R)
    (hexchange : ∀ r : R, δ (α r) = (α (δ r))⁻¹) :
    Nat.card R = Nat.card (positiveGroup α) ^ 2 := by
  rw [eigengroups_card_mul hodd α hα, ← eigengroups_card_eq α δ hexchange, pow_two]

theorem eigengroups_nontrivial [Nontrivial R] (hodd : Odd (Nat.card R))
    (α : MulAut R) (hα : α ^ 2 = 1) (δ : MulAut R)
    (hexchange : ∀ r : R, δ (α r) = (α (δ r))⁻¹) :
    Nontrivial (positiveGroup α) ∧ Nontrivial (negativeGroup α) := by
  obtain ⟨r, hr⟩ := exists_ne (1 : R)
  obtain ⟨a, ha, b, hb, hab⟩ := eigengroups_factorization hodd α hα r
  have hp : ∃ x : positiveGroup α, x ≠ 1 := by
    by_cases haone : a = 1
    · have hbone : b ≠ 1 := by
        intro h
        apply hr
        rw [← hab, haone, h, one_mul]
      let y : negativeGroup α := ⟨b, hb⟩
      refine ⟨(exchangeEquiv α δ hexchange).symm y, ?_⟩
      intro h
      have hyone : y = 1 := (exchangeEquiv α δ hexchange).symm.injective
        (h.trans (map_one (exchangeEquiv α δ hexchange).symm).symm)
      exact hbone (congrArg Subtype.val hyone)
    · exact ⟨⟨a, ha⟩, fun h => haone (congrArg Subtype.val h)⟩
  obtain ⟨x, hx⟩ := hp
  refine ⟨⟨⟨x, 1, hx⟩⟩, ?_⟩
  refine ⟨⟨exchangeEquiv α δ hexchange x, 1, ?_⟩⟩
  intro h
  exact hx ((exchangeEquiv α δ hexchange).injective
    (h.trans (map_one (exchangeEquiv α δ hexchange)).symm))

theorem negativeGroup_eq_twisted_fixed {J : Type v} [Group J]
    (ρ : J →* MulAut R) (t : J) (hinv : ∀ r : R, ρ t r = r⁻¹)
    (α : MulAut R) : negativeGroup α = positiveGroup (ρ t * α) := by
  ext r
  change α r = r⁻¹ ↔ ρ t (α r) = r
  rw [hinv]
  constructor
  · intro h
    rw [h, inv_inv]
  · intro h
    exact inv_injective (h.trans (inv_inv r).symm)

theorem projective_embedding_nondefining_cyclic
    {F : Type v} [Field F] {A : Type w} [Group A]
    {p ell f : ℕ} (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hF : Nat.card F = p ^ f) (hell : ell.Prime) (hellodd : Odd ell)
    (hellp : ell ≠ p) (hA : IsPGroup ell A)
    (ι : A →* OddProjectiveCoverKernel.S F) (hι : Function.Injective ι) :
    IsCyclic A := by
  let : Fact ell.Prime := ⟨hell⟩
  let : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; exact pow_ne_zero f hp.ne_zero)
  have hιP : IsPGroup ell ι.range := hA.of_surjective ι.rangeRestrict
    (MonoidHom.rangeRestrict_surjective _)
  obtain ⟨P, hP⟩ := hιP.exists_le_sylow
  let : IsCyclic (P : Subgroup (OddProjectiveCoverKernel.S F)) :=
    (OddProjectiveCoverKernel.odd_projective_linear_two_Sylow_data F
      hp hpodd hf hF).2.2.2.2.2.2 ell hell hellodd hellp P
  let e : A ≃* ι.range := ι.ofInjective hι
  let φ : A →* (P : Subgroup (OddProjectiveCoverKernel.S F)) :=
    (Subgroup.inclusion hP).comp e.toMonoidHom
  exact isCyclic_of_injective φ
    ((Subgroup.inclusion_injective hP).comp e.injective)

theorem projective_defining_sylow_elementary_card
    {F : Type v} [Field F] {p f : ℕ}
    (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hF : Nat.card F = p ^ f)
    (P : Sylow p (OddProjectiveCoverKernel.S F)) :
    CFSG.IsElementaryAbelian p (P : Subgroup (OddProjectiveCoverKernel.S F)) ∧
      Nat.card (P : Subgroup (OddProjectiveCoverKernel.S F)) = p ^ f := by
  let : Fact p.Prime := ⟨hp⟩
  let : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; exact pow_ne_zero f hp.ne_zero)
  obtain ⟨_, _, hU, hUcard, ⟨P₀, hP₀⟩, _, _⟩ :=
    OddProjectiveCoverKernel.odd_projective_linear_two_Sylow_data F hp hpodd hf hF
  let e : (P : Subgroup (OddProjectiveCoverKernel.S F)) ≃*
      OddProjectiveCoverKernel.U F :=
    (Sylow.equiv P P₀).trans (MulEquiv.subgroupCongr hP₀)
  refine ⟨?_, (Nat.card_congr e.toEquiv).trans hUcard⟩
  refine { toIsMulCommutative := ⟨⟨fun x y => e.injective ?_⟩⟩
           exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
  · rw [map_mul, map_mul]
    exact (hU.1.is_comm).comm _ _
  · intro x
    apply e.injective
    rw [map_pow, map_one]
    apply Subtype.ext
    exact hU.2 (e x : OddProjectiveCoverKernel.S F) (e x).property

theorem projective_embedding_defining_elementary_card
    {F : Type v} [Field F] {A : Type w} [Group A]
    {p f : ℕ} (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hF : Nat.card F = p ^ f) (hA : IsPGroup p A)
    (ι : A →* OddProjectiveCoverKernel.S F) (hι : Function.Injective ι) :
    CFSG.IsElementaryAbelian p A ∧ Nat.card A ≤ p ^ f := by
  let : Fact p.Prime := ⟨hp⟩
  let : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; exact pow_ne_zero f hp.ne_zero)
  have hιP : IsPGroup p ι.range := hA.of_surjective ι.rangeRestrict
    (MonoidHom.rangeRestrict_surjective _)
  obtain ⟨P, hP⟩ := hιP.exists_le_sylow
  obtain ⟨hPe, hPcard⟩ := projective_defining_sylow_elementary_card hp hpodd hf hF P
  let : CFSG.IsElementaryAbelian p (P : Subgroup (OddProjectiveCoverKernel.S F)) := hPe
  let e : A ≃* ι.range := ι.ofInjective hι
  let φ : A →* (P : Subgroup (OddProjectiveCoverKernel.S F)) :=
    (Subgroup.inclusion hP).comp e.toMonoidHom
  have hφ : Function.Injective φ :=
    (Subgroup.inclusion_injective hP).comp e.injective
  refine ⟨?_, hPcard ▸ Nat.card_le_card_of_injective φ hφ⟩
  refine { toIsMulCommutative := ⟨⟨fun x y => hφ ?_⟩⟩
           exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
  · rw [map_mul, map_mul]
    exact (hPe.toIsMulCommutative.is_comm).comm _ _
  · intro x
    apply hφ
    rw [map_pow, map_one]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hPe.exponent_dvd_p (φ x)

theorem projective_embedding_range_sylow
    {F : Type v} [Field F] {A : Type w} [Group A]
    {p f : ℕ} (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hF : Nat.card F = p ^ f) (hA : IsPGroup p A)
    (ι : A →* OddProjectiveCoverKernel.S F) (hι : Function.Injective ι)
    (hcard : Nat.card A = p ^ f) :
    ∃ P : Sylow p (OddProjectiveCoverKernel.S F), (P : Subgroup _) = ι.range := by
  let : Fact p.Prime := ⟨hp⟩
  let : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; exact pow_ne_zero f hp.ne_zero)
  have hιP : IsPGroup p ι.range := hA.of_surjective ι.rangeRestrict
    (MonoidHom.rangeRestrict_surjective _)
  obtain ⟨P, hP⟩ := hιP.exists_le_sylow
  have hPcard := (projective_defining_sylow_elementary_card hp hpodd hf hF P).2
  have hιcard : Nat.card ι.range = p ^ f :=
    (Nat.card_congr (ι.ofInjective hι).toEquiv).symm.trans hcard
  exact ⟨P, (Subgroup.eq_of_le_of_card_ge hP (by rw [hPcard, hιcard])).symm⟩

theorem odd_card_of_odd_prime_group [Finite R] {ell : ℕ}
    (hell : ell.Prime) (hellodd : Odd ell) (hR : IsPGroup ell R) :
    Odd (Nat.card R) := by
  let : Fact ell.Prime := ⟨hell⟩
  obtain ⟨n, hn⟩ := hR.exists_card_eq
  rw [hn]
  exact hellodd.pow

theorem eigengroups_nondefining_cyclic
    {F : Type v} [Field F] {p ell f : ℕ}
    (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hF : Nat.card F = p ^ f)
    (hell : ell.Prime) (hellodd : Odd ell) (hellp : ell ≠ p)
    (hR : IsPGroup ell R) (α δ : MulAut R)
    (hexchange : ∀ r : R, δ (α r) = (α (δ r))⁻¹)
    (ι : positiveGroup α →* OddProjectiveCoverKernel.S F) (hι : Function.Injective ι) :
    IsCyclic (positiveGroup α) ∧ IsCyclic (negativeGroup α) := by
  have hpcyc := projective_embedding_nondefining_cyclic hp hpodd hf hF
    hell hellodd hellp (hR.to_subgroup (positiveGroup α)) ι hι
  let : IsCyclic (positiveGroup α) := hpcyc
  exact ⟨hpcyc, isCyclic_of_injective (exchangeEquiv α δ hexchange).symm.toMonoidHom
    (exchangeEquiv α δ hexchange).symm.injective⟩

theorem elementary_of_eigengroups {p : ℕ}
    (hodd : Odd (Nat.card R)) (α : MulAut R) (hα : α ^ 2 = 1) (δ : MulAut R)
    (hexchange : ∀ r : R, δ (α r) = (α (δ r))⁻¹)
    (hplus : CFSG.IsElementaryAbelian p (positiveGroup α)) :
    CFSG.IsElementaryAbelian p (negativeGroup α) ∧ CFSG.IsElementaryAbelian p R := by
  have hminus : CFSG.IsElementaryAbelian p (negativeGroup α) := by
    refine { toIsMulCommutative := inferInstance
             exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
    intro r
    apply (exchangeEquiv α δ hexchange).symm.injective
    rw [map_pow, map_one]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hplus.exponent_dvd_p
      ((exchangeEquiv α δ hexchange).symm r)
  refine ⟨hminus, ?_⟩
  refine { toIsMulCommutative := inferInstance
           exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
  intro r
  obtain ⟨a, ha, b, hb, hab⟩ := eigengroups_factorization hodd α hα r
  have hap : a ^ p = 1 := by
    have h := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hplus.exponent_dvd_p
      (⟨a, ha⟩ : positiveGroup α)
    exact congrArg Subtype.val h
  have hbp : b ^ p = 1 := by
    have h := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hminus.exponent_dvd_p
      (⟨b, hb⟩ : negativeGroup α)
    exact congrArg Subtype.val h
  rw [← hab, mul_pow, hap, hbp, one_mul]

theorem eigengroups_defining_elementary_order_bounds [Finite R]
    {F : Type v} [Field F] {p f : ℕ}
    (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hF : Nat.card F = p ^ f)
    (hR : IsPGroup p R) (α : MulAut R) (hα : α ^ 2 = 1) (δ : MulAut R)
    (hexchange : ∀ r : R, δ (α r) = (α (δ r))⁻¹)
    (ι : positiveGroup α →* OddProjectiveCoverKernel.S F) (hι : Function.Injective ι) :
    CFSG.IsElementaryAbelian p (positiveGroup α) ∧
      CFSG.IsElementaryAbelian p (negativeGroup α) ∧ CFSG.IsElementaryAbelian p R ∧
      Nat.card (positiveGroup α) ≤ p ^ f ∧ Nat.card (negativeGroup α) ≤ p ^ f ∧
      Nat.card R ≤ p ^ (2 * f) := by
  have hodd := odd_card_of_odd_prime_group hp hpodd hR
  obtain ⟨hplus, hpluscard⟩ := projective_embedding_defining_elementary_card hp hpodd hf hF
    (hR.to_subgroup (positiveGroup α)) ι hι
  obtain ⟨hminus, hwhole⟩ := elementary_of_eigengroups hodd α hα δ hexchange hplus
  have hcards := eigengroups_card_eq α δ hexchange
  refine ⟨hplus, hminus, hwhole, hpluscard, hcards ▸ hpluscard, ?_⟩
  calc
    Nat.card R = Nat.card (positiveGroup α) ^ 2 :=
      eigengroups_card_square hodd α hα δ hexchange
    _ ≤ (p ^ f) ^ 2 := Nat.pow_le_pow_left hpluscard 2
    _ = p ^ (2 * f) := by rw [← pow_mul, Nat.mul_comm f 2]

theorem eigengroups_defining_full_dimension_and_kernel [Finite R] [Nontrivial R]
    {F : Type v} [Field F] {J : Type w} [Group J] [Finite J] [Group.IsPerfect J]
    {p f : ℕ} (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hF : Nat.card F = p ^ f) (hq : 5 ≤ p ^ f)
    (β : J →* Matrix.SpecialLinearGroup (Fin 2) F) (hβ : Function.Surjective β)
    (hcentral : β.ker ≤ Subgroup.center J) (hodd : Odd (Nat.card β.ker))
    (t : J) (ht : t ∈ Subgroup.center J) (htorder : orderOf t = 2)
    (htβ : β t = OddFieldSL2.minusIdentity F)
    (ρ : J →* MulAut R) (hinv : ∀ r : R, ρ t r = r⁻¹) (hR : IsPGroup p R)
    (α : MulAut R) (hα : α ^ 2 = 1) (d : J)
    (hexchange : ρ d * α * (ρ d)⁻¹ = ρ t * α)
    (ι : positiveGroup α →* OddProjectiveCoverKernel.S F) (hι : Function.Injective ι) :
    CFSG.IsElementaryAbelian p (positiveGroup α) ∧
      CFSG.IsElementaryAbelian p (negativeGroup α) ∧
      ∃ hwhole : CFSG.IsElementaryAbelian p R,
        letI : Fact p.Prime := ⟨hp⟩
        letI : CFSG.IsElementaryAbelian p R := hwhole
        Module.finrank (ZMod p) (Additive R) = 2 * f ∧
          Nat.card (positiveGroup α) = p ^ f ∧
          Nat.card (negativeGroup α) = p ^ f ∧ Nat.card R = p ^ (2 * f) ∧
          (∃ P : Sylow p (OddProjectiveCoverKernel.S F), (P : Subgroup _) = ι.range) ∧
          Representation.IsIrreducible
            (ElementaryActionTransport.primeFieldRepresentation (p := p) ρ) ∧
          ρ.ker = β.ker ∧
          (∀ A : Subgroup R, (∀ j : J, ∀ r : R, r ∈ A → ρ j r ∈ A) → A = ⊥ ∨ A = ⊤) := by
  let : Fact p.Prime := ⟨hp⟩
  let : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; exact pow_ne_zero f hp.ne_zero)
  have he := exchange_identity ρ t d hinv α hexchange
  obtain ⟨hplus, hminus, hwhole, _, _, hcardbound⟩ :=
    eigengroups_defining_elementary_order_bounds hp hpodd hf hF hR α hα (ρ d) he ι hι
  refine ⟨hplus, hminus, hwhole, ?_⟩
  let : CFSG.IsElementaryAbelian p R := hwhole
  have hdimupper : Module.finrank (ZMod p) (Additive R) ≤ 2 * f := by
    apply (Nat.pow_le_pow_iff_right hp.one_lt).mp
    rwa [← ElementaryActionTransport.card_eq_prime_pow_finrank]
  have hk : Nat.card (ZMod p) = p := by simp [ZMod.card]
  let τ := ElementaryActionTransport.primeFieldAction (p := p) ρ
  have hτ : τ t ≠ 1 :=
    ElementaryActionTransport.primeFieldAction_inversion_ne_one hpodd ρ t hinv
  obtain ⟨_, hdimlower, _, hequality⟩ :=
    OddCentralDimension.odd_central_SL2_cover_defining_characteristic_minimum_dimension
      hp hpodd hf hF hq hk β hβ hcentral hodd t ht htorder htβ τ hτ
  have hdim : Module.finrank (ZMod p) (Additive R) = 2 * f :=
    Nat.le_antisymm hdimupper hdimlower
  obtain ⟨_, hirr, hker, _⟩ := hequality hdim
  have hρker : ρ.ker = β.ker :=
    (ElementaryActionTransport.primeFieldAction_kernel ρ).symm.trans hker
  obtain ⟨_, _, hpluscard, hminuscard, hwholecard⟩ :=
    ElementaryActionTransport.equal_internalProduct_factors_of_finrank
      (positiveGroup α) (negativeGroup α)
      (eigenProductEquiv (odd_card_of_odd_prime_group hp hpodd hR) α hα)
      (eigengroups_card_eq α (ρ d) he) f hdim
  have hSylow := projective_embedding_range_sylow hp hpodd hf hF
    (hR.to_subgroup (positiveGroup α)) ι hι hpluscard
  exact ⟨hdim, hpluscard, hminuscard, hwholecard, hSylow, hirr, hρker,
    (ElementaryActionTransport.primeFieldRepresentation_irreducible_iff ρ).mp hirr⟩

theorem eigengroups_characteristic_eq [Finite R] [Nontrivial R]
    {F : Type v} [Field F] {J : Type w} [Group J] [Finite J] [Group.IsPerfect J]
    {p ell f : ℕ} (hp : p.Prime) (hpodd : Odd p) (hell : ell.Prime) (hellodd : Odd ell)
    (hf : 1 ≤ f) (hF : Nat.card F = p ^ f) (hq : 5 < p ^ f)
    (β : J →* Matrix.SpecialLinearGroup (Fin 2) F) (hβ : Function.Surjective β)
    (hcentral : β.ker ≤ Subgroup.center J) (hodd : Odd (Nat.card β.ker))
    (t : J) (ht : t ∈ Subgroup.center J) (htorder : orderOf t = 2)
    (htβ : β t = OddFieldSL2.minusIdentity F)
    (ρ : J →* MulAut R) (hinv : ∀ r : R, ρ t r = r⁻¹) (hR : IsPGroup ell R)
    (α : MulAut R) (hα : α ^ 2 = 1) (d : J)
    (hexchange : ρ d * α * (ρ d)⁻¹ = ρ t * α)
    (ι : positiveGroup α →* OddProjectiveCoverKernel.S F) (hι : Function.Injective ι) :
    ell = p := by
  by_contra hne
  let : Fact ell.Prime := ⟨hell⟩
  have hoddR := odd_card_of_odd_prime_group hell hellodd hR
  have he := exchange_identity ρ t d hinv α hexchange
  obtain ⟨hpnontrivial, hmnontrivial⟩ := eigengroups_nontrivial hoddR α hα (ρ d) he
  let : Nontrivial (positiveGroup α) := hpnontrivial
  let : Nontrivial (negativeGroup α) := hmnontrivial
  obtain ⟨hpcyclic, hmcyclic⟩ := eigengroups_nondefining_cyclic hp hpodd hf hF
    hell hellodd hne hR α (ρ d) he ι hι
  let : IsCyclic (positiveGroup α) := hpcyclic
  let : IsCyclic (negativeGroup α) := hmcyclic
  let e := eigenProductEquiv hoddR α hα
  let hplus := hR.to_subgroup (positiveGroup α)
  let hminus := hR.to_subgroup (negativeGroup α)
  let τ := CyclicPairFrattini.matrixCoordinateAction ell hplus hminus e ρ
  have hτ : τ t ≠ 1 :=
    CyclicPairFrattini.matrixCoordinateAction_inversion_ne_one
      ell hplus hminus e hellodd ρ t hinv
  have htβ' : β t = ProjectiveSL2Cover.minusIdentity F :=
    htβ.trans (ProjectiveSL2Cover.minusIdentity_eq_neg_one F).symm
  obtain ⟨_, _, _, _, _, _, _, hchar, _⟩ :=
    PrimeFieldDegreeTwoAction.prime_field_degree_two_central_cover_action
      hp hpodd hell hellodd hf hF (Nat.card_zmod ell) (Nat.le_of_lt hq)
      β hβ hcentral hodd t ht htorder htβ' τ hτ
  exact hne (hchar hq).symm

theorem exchanged_eigensubgroups_projective_embedding_forces_defining_square_order
    [Finite R] [Nontrivial R] {F : Type v} [Field F]
    {J : Type w} [Group J] [Finite J] [Group.IsPerfect J]
    {p ell f : ℕ} (hp : p.Prime) (hpodd : Odd p) (hell : ell.Prime) (hellodd : Odd ell)
    (hf : 1 ≤ f) (hF : Nat.card F = p ^ f) (hq : 5 < p ^ f)
    (β : J →* Matrix.SpecialLinearGroup (Fin 2) F) (hβ : Function.Surjective β)
    (hcentral : β.ker ≤ Subgroup.center J) (hodd : Odd (Nat.card β.ker))
    (t : J) (ht : t ∈ Subgroup.center J) (htorder : orderOf t = 2)
    (htβ : β t = OddFieldSL2.minusIdentity F)
    (ρ : J →* MulAut R) (hinv : ∀ r : R, ρ t r = r⁻¹) (hR : IsPGroup ell R)
    (α : MulAut R) (hα : α ^ 2 = 1) (d : J)
    (hexchange : ρ d * α * (ρ d)⁻¹ = ρ t * α)
    (ι : positiveGroup α →* OddProjectiveCoverKernel.S F) (hι : Function.Injective ι) :
    ell = p ∧
      (positiveGroup α).IsComplement' (positiveGroup (ρ t * α)) ∧
      CFSG.IsElementaryAbelian p (positiveGroup α) ∧
      CFSG.IsElementaryAbelian p (positiveGroup (ρ t * α)) ∧
      (∃ e : positiveGroup α × positiveGroup (ρ t * α) ≃* R,
        ∀ r, e r = (r.1 : R) * r.2) ∧
      ∃ hwhole : CFSG.IsElementaryAbelian p R,
        letI : Fact p.Prime := ⟨hp⟩
        letI : CFSG.IsElementaryAbelian p R := hwhole
        Nat.card (positiveGroup α) = p ^ f ∧
          Nat.card (positiveGroup (ρ t * α)) = p ^ f ∧
          Nat.card R = (p ^ f) ^ 2 ∧
          (∃ P : Sylow p (OddProjectiveCoverKernel.S F), (P : Subgroup _) = ι.range) ∧
          Module.finrank (ZMod p) (Additive R) = 2 * f ∧
          Representation.IsIrreducible
            (ElementaryActionTransport.primeFieldRepresentation (p := p) ρ) ∧
          ρ.ker = β.ker ∧
          (∀ A : Subgroup R, (∀ j : J, ∀ r : R, r ∈ A → ρ j r ∈ A) → A = ⊥ ∨ A = ⊤) ∧
          ∃ σ : Matrix.SpecialLinearGroup (Fin 2) F →* MulAut R,
            Function.Injective σ ∧ σ.comp β = ρ ∧
            (∀ (j : J) (r : R), σ (β j) r = ρ j r) ∧
            Function.Injective (ElementaryActionTransport.primeFieldAction (p := p) σ) ∧
            (ElementaryActionTransport.primeFieldAction (p := p) σ).comp β =
              ElementaryActionTransport.primeFieldAction (p := p) ρ := by
  have hchar := eigengroups_characteristic_eq hp hpodd hell hellodd hf hF hq
    β hβ hcentral hodd t ht htorder htβ ρ hinv hR α hα d hexchange ι hι
  have hRdef : IsPGroup p R := hchar ▸ hR
  have hoddR := odd_card_of_odd_prime_group hell hellodd hR
  rw [← negativeGroup_eq_twisted_fixed ρ t hinv α]
  obtain ⟨hplus, hminus, hwhole, hdim, hpluscard, hminuscard, hwholecard,
      hSylow, hirr, hker, hinvariant⟩ :=
    eigengroups_defining_full_dimension_and_kernel hp hpodd hf hF (Nat.le_of_lt hq)
      β hβ hcentral hodd t ht htorder htβ ρ hinv hRdef α hα d hexchange ι hι
  refine ⟨hchar, eigengroups_isComplement hoddR α hα, hplus, hminus,
    ⟨eigenProductEquiv hoddR α hα, eigenProductEquiv_apply hoddR α hα⟩, hwhole, ?_⟩
  let : Fact p.Prime := ⟨hp⟩
  let : CFSG.IsElementaryAbelian p R := hwhole
  have hsquare : Nat.card R = (p ^ f) ^ 2 := by
    rw [hwholecard, ← pow_mul, Nat.mul_comm f 2]
  let σ := ElementaryActionTransport.descendedOriginalAction β hβ ρ hker.ge
  have hσ : Function.Injective σ :=
    ElementaryActionTransport.descendedOriginalAction_injective β hβ ρ hker.ge hker
  have hσcomp : σ.comp β = ρ :=
    ElementaryActionTransport.descendedOriginalAction_comp β hβ ρ hker.ge
  refine ⟨hpluscard, hminuscard, hsquare, hSylow, hdim, hirr, hker, hinvariant,
    σ, hσ, hσcomp, ElementaryActionTransport.descendedOriginalAction_apply_element
      β hβ ρ hker.ge, ?_, ?_⟩
  · exact (ElementaryActionTransport.autToGL_injective (p := p)).comp hσ
  · apply MonoidHom.ext
    intro j
    change ElementaryActionTransport.autToGL (p := p) (σ (β j)) =
      ElementaryActionTransport.autToGL (p := p) (ρ j)
    exact congrArg (ElementaryActionTransport.autToGL (p := p))
      (DFunLike.congr_fun hσcomp j)

end

end CFSG.Semidihedral.ExchangedEigensubgroups
