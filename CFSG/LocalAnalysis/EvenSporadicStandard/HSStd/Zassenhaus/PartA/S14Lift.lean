module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.InnerThreePart

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup
open scoped commutatorElement

section Bridge

variable {G : Type*} [Group G]

theorem comm_central {k : G} (hk : k ∈ center G) (n m : G) : ⁅k * n, m⁆ = ⁅n, m⁆ := by
  have h1 := Subgroup.mem_center_iff.1 hk
  rw [commutatorElement_def, commutatorElement_def]
  have e : k * n * m * (k * n)⁻¹ * m⁻¹ = (k * (n * m * n⁻¹)) * k⁻¹ * m⁻¹ := by group
  rw [e, ← h1 (n * m * n⁻¹)]
  group

theorem comm_central' {k : G} (hk : k ∈ center G) (n m : G) : ⁅n, k * m⁆ = ⁅n, m⁆ := by
  rw [← commutatorElement_inv, comm_central hk, commutatorElement_inv]

end Bridge

section Lift

set_option linter.unusedSectionVars false

variable {H : Type} [Group H] [Finite H]

abbrev A6 : Type := alternatingGroup (Fin 6)

theorem lift_unique {π : H →* A6} (hker : π.ker ≤ center H) (hper : commutator H = ⊤)
    (γ : H →* H) (hγ : ∀ h, π (γ h) = π h) (h : H) : γ h = h := by
  have hk : ∀ g, γ g * g⁻¹ ∈ center H := by
    intro g
    apply hker
    rw [MonoidHom.mem_ker, map_mul, map_inv, hγ, mul_inv_cancel]
  have hle : commutator H ≤ MonoidHom.eqLocus γ (MonoidHom.id H) := by
    rw [commutator_def]
    refine Subgroup.commutator_le.2 fun g₁ _ g₂ _ => ?_
    show γ ⁅g₁, g₂⁆ = ⁅g₁, g₂⁆
    obtain ⟨c₁, hc₁, e1⟩ : ∃ c ∈ center H, γ g₁ = c * g₁ := ⟨_, hk g₁, by group⟩
    obtain ⟨c₂, hc₂, e2⟩ : ∃ c ∈ center H, γ g₂ = c * g₂ := ⟨_, hk g₂, by group⟩
    rw [map_commutatorElement, e1, e2, comm_central hc₁, comm_central' hc₂]
  rw [hper] at hle
  exact hle (Subgroup.mem_top h)

section Aut

variable {π : H →* A6}

theorem aut_center_le (γ : MulAut H) {c : H} (hc : c ∈ center H) : γ c ∈ center H := by
  rw [Subgroup.mem_center_iff] at hc ⊢
  intro g
  simpa [map_mul] using congrArg γ (hc (γ.symm g))

theorem exists_induced (hπ : Function.Surjective π) (hker : π.ker = center H) (γ : MulAut H) :
    ∃ ᾱ : MulAut A6, ∀ h, ᾱ (π h) = π (γ h) := by
  have hle : π.ker ≤ (π.comp γ.toMonoidHom).ker := by
    intro k hk
    rw [hker] at hk
    rw [MonoidHom.mem_ker]
    have : γ k ∈ π.ker := by rw [hker]; exact aut_center_le γ hk
    exact this
  let f : A6 →* A6 := MonoidHom.liftOfSurjective π hπ ⟨π.comp γ.toMonoidHom, hle⟩
  have hf : ∀ h, f (π h) = π (γ h) := fun h =>
    MonoidHom.liftOfRightInverse_comp_apply π (Function.surjInv hπ) _
      ⟨π.comp γ.toMonoidHom, hle⟩ h
  have hfs : Function.Surjective f := by
    intro a
    obtain ⟨h, rfl⟩ := hπ a
    obtain ⟨h', hh'⟩ := hπ (π (γ.symm h))
    exact ⟨π (γ.symm h), by rw [hf]; simp⟩
  have hfi : Function.Injective f := Finite.injective_iff_surjective.2 hfs
  exact ⟨MulEquiv.ofBijective f ⟨hfi, hfs⟩, hf⟩

@[expose] noncomputable def thetaFun (hπ : Function.Surjective π) (hker : π.ker = center H)
    (γ : MulAut H) : MulAut A6 :=
  Classical.choose (exists_induced hπ hker γ)

theorem thetaFun_apply (hπ : Function.Surjective π) (hker : π.ker = center H) (γ : MulAut H)
    (h : H) : thetaFun hπ hker γ (π h) = π (γ h) :=
  Classical.choose_spec (exists_induced hπ hker γ) h

@[expose] noncomputable def Theta (hπ : Function.Surjective π) (hker : π.ker = center H) :
    MulAut H →* MulAut A6 where
  toFun := thetaFun hπ hker
  map_one' := by
    refine MulEquiv.ext fun a => ?_
    obtain ⟨h, rfl⟩ := hπ a
    rw [thetaFun_apply]
    simp
  map_mul' γ δ := by
    refine MulEquiv.ext fun a => ?_
    obtain ⟨h, rfl⟩ := hπ a
    rw [thetaFun_apply, MulAut.mul_apply, MulAut.mul_apply, thetaFun_apply, thetaFun_apply]

theorem Theta_apply (hπ : Function.Surjective π) (hker : π.ker = center H) (γ : MulAut H) (h : H) :
    Theta hπ hker γ (π h) = π (γ h) :=
  thetaFun_apply hπ hker γ h

theorem central_eq_one {a b k : H} (hb : b ^ 3 = 1) (ha : a ^ 3 = 1) (hk : k ∈ center H)
    (hk2 : k * k = 1) (e : a = b * k) : k = 1 := by
  have hc : Commute b k := ((Subgroup.mem_center_iff.1 hk) b)
  have h3 : k ^ 3 = k := by rw [pow_succ, pow_two, hk2, one_mul]
  rw [e, hc.mul_pow, hb, one_mul, h3] at ha
  exact ha

variable (hAut : Nonempty (MulAut H ≃* MulAut A6)) (hπ : Function.Surjective π) (hker : π.ker = center H)
  (hc2 : Nat.card (center H) = 2) (hper : commutator H = ⊤)

include hker hc2 in
theorem cover_sq {k : H} (hk : k ∈ center H) : k * k = 1 := by
  have : (⟨k, hk⟩ : center H) ^ Nat.card (center H) = 1 := pow_card_eq_one'
  rw [hc2] at this
  have := congrArg Subtype.val this
  simpa [pow_two] using this

include hAut hπ hker hc2 hper in
theorem exists_autEquiv : ∃ Φ : MulAut H ≃* MulAut A6,
    ∀ γ h, Φ γ (π h) = π (γ h) := by
  have hinj : Function.Injective (Theta hπ hker) := by
    rw [injective_iff_map_eq_one]
    intro γ hγ
    refine MulEquiv.ext fun h => ?_
    refine lift_unique (π := π) hker.le hper γ.toMonoidHom (fun h => ?_) h
    have := Theta_apply hπ hker γ h
    rw [hγ] at this
    exact this.symm
  have hle : Nat.card (MulAut A6) ≤ Nat.card (MulAut H) := by
    obtain ⟨e⟩ := hAut
    exact (Nat.card_congr e.toEquiv).symm.le
  have hbij := hinj.bijective_of_nat_card_le hle
  exact ⟨MulEquiv.ofBijective (Theta hπ hker) hbij, fun γ h => Theta_apply hπ hker γ h⟩

theorem pow_three_of_orderOf {x : H} (hx : orderOf x = 3) : x ^ 3 = 1 := by
  have := pow_orderOf_eq_one x
  rwa [hx] at this

include hker hc2 in
theorem cover_orderOf {x : H} (hx : orderOf x = 3) : orderOf (π x) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime ?_ ?_
  · rw [← map_pow, pow_three_of_orderOf hx, map_one]
  · intro h
    have hxc : x ∈ center H := hker ▸ (MonoidHom.mem_ker.2 h)
    have h2 := cover_sq hker hc2 hxc
    have h3 := pow_three_of_orderOf hx
    have : x ^ 3 = x := by rw [pow_succ, pow_two, h2, one_mul]
    rw [this] at h3
    rw [h3, orderOf_one] at hx
    omega

include hAut hπ hker hc2 hper in
theorem cover_trans {x x' : H} (hx : orderOf x = 3) (hx' : orderOf x' = 3) :
    ∃ α : MulAut H, α x = x' := by
  obtain ⟨Φ, hΦ⟩ := exists_autEquiv hAut hπ hker hc2 hper
  obtain ⟨ᾱ, hᾱ⟩ := exists_mulAut_apply_eq_of_orderOf_eq_three (cover_orderOf hker hc2 hx)
    (cover_orderOf hker hc2 hx')
  refine ⟨Φ.symm ᾱ, ?_⟩
  set β := Φ.symm ᾱ with hβ
  have hΦβ : Φ β = ᾱ := by simp [hβ]
  have h1 : π (β x) = π x' := by
    rw [← hΦ β x, hΦβ, hᾱ]
  have hk : x'⁻¹ * β x ∈ center H := by
    rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel]
  have e : β x = x' * (x'⁻¹ * β x) := by group
  have hb3 : (β x) ^ 3 = 1 := by
    rw [← map_pow, pow_three_of_orderOf hx, map_one]
  have := central_eq_one (pow_three_of_orderOf hx') hb3 hk (cover_sq hker hc2 hk) e
  rw [this, mul_one] at e
  exact e

include hAut hπ hker hc2 hper in
theorem cover_card_cent {x : H} (hx : orderOf x = 3) :
    Nat.card (centralizer ({MulAut.conj x} : Set (MulAut H))) = 18 := by
  obtain ⟨Φ, hΦ⟩ := exists_autEquiv hAut hπ hker hc2 hper
  have hc : Φ (MulAut.conj x) = MulAut.conj (π x) := by
    refine MulEquiv.ext fun a => ?_
    obtain ⟨h, rfl⟩ := hπ a
    rw [hΦ]
    simp [MulAut.conj_apply]
  rw [← card_centralizer_singleton_equiv Φ (MulAut.conj x), hc]
  exact card_centralizer_conj_of_orderOf_eq_three (cover_orderOf hker hc2 hx)

include hAut hπ hker hc2 hper in
theorem cover_card_aut : Nat.card (MulAut H) = 1440 := by
  obtain ⟨Φ, -⟩ := exists_autEquiv hAut hπ hker hc2 hper
  rw [Nat.card_congr Φ.toEquiv]
  exact CFSG.QuasithinUnique.Setup.X3Aut.card_mulAut_alt6

include hker hc2 in
theorem cover_conj_inj {m n : H} (hm : orderOf m = 3) (hn : orderOf n = 3)
    (h : MulAut.conj m = MulAut.conj n) : m = n := by
  have hz : n⁻¹ * m ∈ center H := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 : m * g * m⁻¹ = n * g * n⁻¹ := by
      have := congrArg (fun f : MulAut H => f g) h
      simpa [MulAut.conj_apply] using this
    calc g * (n⁻¹ * m) = n⁻¹ * (n * g * n⁻¹) * m := by group
      _ = n⁻¹ * (m * g * m⁻¹) * m := by rw [h1]
      _ = n⁻¹ * m * g := by group
  have e : m = n * (n⁻¹ * m) := by group
  have := central_eq_one (pow_three_of_orderOf hn) (pow_three_of_orderOf hm) hz
    (cover_sq hker hc2 hz) e
  rw [this, mul_one] at e
  exact e

end Aut

end Lift

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
