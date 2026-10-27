module

public import CFSG.LieType.Steinberg.CentralExt.MinusculeCentrallyClosed
public import CFSG.LieType.Steinberg.CentralExt.TwistedE6Coprime
public import CFSG.LieType.Steinberg.CentralExt.UnitaryField

public noncomputable section

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.ExceptionalCover CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.CentralExt.MinusculeClosed
open scoped commutatorElement

namespace CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed

attribute [local instance] TorusLift.centerCommGroup

theorem cartan_fold : ∀ (i : Fin (Tag.rank .F4)) (j : Fin (Tag.rank .E6)),
    (∑ a ∈ Finset.univ.filter (fun a => orbitMap a = i), Tag.cartan .E6 a j) =
      Tag.cartan .F4 i (orbitMap j) := by
  decide

theorem cartanCoord_fold (α : Fin (Tag.rank .E6) → ℤ) (i : Fin (Tag.rank .F4)) :
    ∑ a ∈ Finset.univ.filter (fun a => orbitMap a = i), cartanCoord α a =
      cartanCoord (proj α) i := by
  have h1 : ∑ a ∈ Finset.univ.filter (fun a => orbitMap a = i), cartanCoord α a =
      ∑ j, Tag.cartan .F4 i (orbitMap j) * α j := by
    simp only [cartanCoord]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_mul, cartan_fold]
  have h2 : cartanCoord (proj α) i = ∑ j, Tag.cartan .F4 i (orbitMap j) * α j := by
    have e : ∀ l, proj α l = ∑ j ∈ Finset.univ.filter (fun j => orbitMap j = l), α j :=
      fun _ => rfl
    simp only [cartanCoord, e, Finset.mul_sum]
    rw [← Finset.sum_fiberwise Finset.univ orbitMap
      (fun j => Tag.cartan .F4 i (orbitMap j) * α j)]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j hj => ?_
    rw [(Finset.mem_filter.1 hj).2]
  rw [h1, h2]

theorem orbitMap_rhoPerm (a : Fin (Tag.rank .E6)) : orbitMap (rhoPerm a) = orbitMap a := by
  revert a
  decide

theorem orbitMap_rhoPerm_symm (a : Fin (Tag.rank .E6)) :
    orbitMap (rhoPerm.symm a) = orbitMap a := by
  rw [← orbitMap_rhoPerm (rhoPerm.symm a), Equiv.apply_symm_apply]

theorem cartanCoord_rho (α : Fin (Tag.rank .E6) → ℤ) (a : Fin (Tag.rank .E6)) :
    cartanCoord (rho α) (rhoPerm a) = cartanCoord α a := by
  simp only [cartanCoord]
  rw [← Equiv.sum_comp rhoPerm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show Tag.cartan .E6 (rhoPerm a) (rhoPerm i) = Tag.cartan .E6 a i from
    TwistTag.cartan_perm .E6 a i]
  congr 1
  change α (rhoPerm.symm (rhoPerm i)) = α i
  rw [Equiv.symm_apply_apply]

theorem cartan_F4_neighbour : ∀ j : Fin (Tag.rank .F4), ∃ i, Tag.cartan .F4 i j = -1 := by
  decide

variable {k : Type} [Field k]

theorem rootChar_fold (α : Fin (Tag.rank .E6) → ℤ) (u : Fin (Tag.rank .F4) → kˣ) :
    rootChar k α (fun a => u (orbitMap a)) = rootChar k (proj α) u := by
  rw [rootChar_apply, rootChar_apply,
    ← Finset.prod_fiberwise Finset.univ orbitMap (fun a => u (orbitMap a) ^ cartanCoord α a)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← cartanCoord_fold, ← Finset.prod_zpow_eq_zpow_sum]
  refine Finset.prod_congr rfl fun a ha => ?_
  rw [(Finset.mem_filter.1 ha).2]

variable (θ : k →+* k)

theorem theta_coe (a : fixedSubfield θ) : θ (a : k) = a := a.2

variable {θ} in
theorem theta_theta_of_card [Finite k] {q : ℕ} (hk : Nat.card k = q ^ 2)
    (hθq : ∀ c, θ c = c ^ q) (c : k) : θ (θ c) = c := by
  have : Fintype k := Fintype.ofFinite k
  rw [hθq, hθq, ← pow_mul, ← sq, ← hk, Nat.card_eq_fintype_card, FiniteField.pow_card]

theorem card_fixedSubfield_of_card [Finite k] {q : ℕ} (hk : Nat.card k = q ^ 2)
    (hθq : ∀ c, θ c = c ^ q) : Nat.card (fixedSubfield θ) = q := by
  obtain ⟨p, hp, hchar⟩ := TorusLift.exists_prime_charP (k := k)
  have : Fintype k := Fintype.ofFinite k
  obtain ⟨n, -, hcard⟩ := FiniteField.card k p
  have hdvd : q ∣ p ^ (n : ℕ) := by
    rw [← hcard, Fintype.card_eq_nat_card, hk]
    exact Dvd.intro q (sq q).symm
  obtain ⟨f, -, rfl⟩ := (Nat.dvd_prime_pow hp.out).1 hdvd
  have hθ : θ = (CFSG.LieType.BorelTits.unitaryInvolution k p f).toRingHom :=
    RingHom.ext fun c => by
      rw [hθq]
      exact (CFSG.LieType.BorelTits.unitaryInvolution_apply k p f c).symm
  subst hθ
  exact CFSG.LieType.Steinberg.card_fixedSubfield hk

theorem rootChar_rho {u : Fin (Tag.rank .E6) → kˣ} (hu : IsSymU θ u) (α : Fin (Tag.rank .E6) → ℤ) :
    rootChar k (rho α) u = Units.map (θ : k →* k) (rootChar k α u) := by
  rw [rootChar_apply, rootChar_apply, map_prod, ← Equiv.prod_comp rhoPerm]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [cartanCoord_rho, hu, map_zpow]

theorem theta_rootChar_of_fixed {u : Fin (Tag.rank .E6) → kˣ} (hu : IsSymU θ u)
    {α : Fin (Tag.rank .E6) → ℤ} (hfix : rho α = α) :
    θ (rootChar k α u : k) = rootChar k α u := by
  have h := congrArg (fun v : kˣ => (v : k)) (rootChar_rho θ hu α)
  rw [hfix] at h
  simpa using h.symm

abbrev coeU (s : (fixedSubfield θ)ˣ) : kˣ :=
  Units.map (fixedSubfield θ).subtype.toMonoidHom s

theorem units_map_coeU (s : (fixedSubfield θ)ˣ) : Units.map (θ : k →* k) (coeU θ s) = coeU θ s :=
  Units.ext (theta_coe θ s)

theorem isSymU_split (s : Fin (Tag.rank .F4) → (fixedSubfield θ)ˣ) :
    IsSymU θ (fun a => coeU θ (s (orbitMap a))) := fun a => by
  dsimp only
  rw [orbitMap_rhoPerm, units_map_coeU]

abbrev chiS (s : Fin (Tag.rank .F4) → (fixedSubfield θ)ˣ) (β : Fin (Tag.rank .F4) → ℤ) :
    (fixedSubfield θ)ˣ :=
  rootChar (fixedSubfield θ) β s

theorem rootChar_split (s : Fin (Tag.rank .F4) → (fixedSubfield θ)ˣ) (α : Fin (Tag.rank .E6) → ℤ) :
    rootChar k α (fun a => coeU θ (s (orbitMap a))) = coeU θ (chiS θ s (proj α)) := by
  rw [rootChar_fold α (fun i => coeU θ (s i))]
  simp only [coeU, rootChar_apply, map_prod, map_zpow]

theorem exists_rootChar_eq {K : Type} [Field K] {β : Fin (Tag.rank .F4) → ℤ} (hβ : IsRoot .F4 β)
    (u : Kˣ) : ∃ s : Fin (Tag.rank .F4) → Kˣ, rootChar K β s = u := by
  obtain ⟨m, hm⟩ := AdjointClosed.exists_unitVec_of_neighbour cartan_F4_neighbour hβ
  exact ⟨AdjointClosed.tvec u m, by rw [AdjointClosed.rootChar_tvec, hm, zpow_one]⟩

theorem sigma_minTorus (u : Fin (Tag.rank .E6) → kˣ) :
    sigma k θ (minTorus e6Data_valid k u) =
      minTorus e6Data_valid k (fun a => Units.map (θ : k →* k) (u (rhoPerm.symm a))) := by
  induction u using torusVec_induction with
  | h1 =>
    have e : (fun a => Units.map (θ : k →* k) ((1 : Fin (Tag.rank .E6) → kˣ) (rhoPerm.symm a))) =
        1 := by
      funext a
      simp
    rw [map_one, map_one, e, map_one]
  | hmul t t' ht ht' =>
    rw [map_mul, map_mul, ht, ht', ← map_mul]
    congr 1
    funext a
    simp
  | hsingle a s =>
    rw [minTorus_mulSingle, sigma_hm]
    have e : (fun b => Units.map (θ : k →* k) ((Pi.mulSingle a s : Fin (Tag.rank .E6) → kˣ)
        (rhoPerm.symm b))) = Pi.mulSingle (rhoPerm a) (Units.map (θ : k →* k) s) := by
      funext b
      by_cases hb : b = rhoPerm a
      · subst hb
        simp
      · have hb' : rhoPerm.symm b ≠ a := fun h => hb (by rw [← h, Equiv.apply_symm_apply])
        rw [Pi.mulSingle_eq_of_ne hb', Pi.mulSingle_eq_of_ne hb, map_one]
    rw [e, minTorus_mulSingle]

theorem minTorus_mem_fixedGroup {u : Fin (Tag.rank .E6) → kˣ} (hu : IsSymU θ u) :
    minTorus e6Data_valid k u ∈ fixedGroup k θ := by
  rw [mem_fixedGroup, sigma_minTorus]
  congr 1
  funext a
  rw [← hu (rhoPerm.symm a), Equiv.apply_symm_apply]

@[expose] def torU (u : Fin (Tag.rank .E6) → kˣ) (hu : IsSymU θ u) : fixedGroup k θ :=
  ⟨minTorus e6Data_valid k u, by exact minTorus_mem_fixedGroup θ hu⟩

theorem torU_val (u : Fin (Tag.rank .E6) → kˣ) (hu : IsSymU θ u) :
    (torU θ u hu : e6Data_valid.minGroup k) = minTorus e6Data_valid k u :=
  rfl

theorem torU_conj_xFixed {u : Fin (Tag.rank .E6) → kˣ} (hu : IsSymU θ u)
    {α : Fin (Tag.rank .E6) → ℤ} (hα : IsRoot .E6 α) (hfix : rho α = α) (c : k) (hc : θ c = c) :
    torU θ u hu * xFixed θ hα hfix c hc * (torU θ u hu)⁻¹ =
      xFixed θ hα hfix ((rootChar k α u : k) * c)
        (by rw [map_mul, hc, theta_rootChar_of_fixed θ hu hfix]) := by
  refine Subtype.ext ?_
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, xFixed_val, xFixed_val, torU_val,
    minTorus_conj_xm e6Data_valid k u hα]

theorem torU_conj_xPair (hθ : ∀ c, θ (θ c) = c) {u : Fin (Tag.rank .E6) → kˣ} (hu : IsSymU θ u)
    {α : Fin (Tag.rank .E6) → ℤ} (hα : IsRoot .E6 α) (hne : rho α ≠ α) (c : k) :
    torU θ u hu * xPair θ hθ hα hne c * (torU θ u hu)⁻¹ =
      xPair θ hθ hα hne ((rootChar k α u : k) * c) := by
  refine Subtype.ext ?_
  have e : ∀ g a b : e6Data_valid.minGroup k, g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) :=
    fun _ _ _ => by group
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, xPair_val, xPair_val, torU_val, e,
    minTorus_conj_xm e6Data_valid k u hα, minTorus_conj_xm e6Data_valid k u (isRoot_rho hα),
    rootChar_rho θ hu]
  congr 2
  simp only [Units.coe_map, MonoidHom.coe_ofClass, map_mul]
  ring

@[expose] def torS (s : Fin (Tag.rank .F4) → (fixedSubfield θ)ˣ) : fixedGroup k θ :=
  torU θ (fun a => coeU θ (s (orbitMap a))) (isSymU_split θ s)

theorem torS_mul (s s' : Fin (Tag.rank .F4) → (fixedSubfield θ)ˣ) :
    torS θ (s * s') = torS θ s * torS θ s' := by
  refine Subtype.ext ?_
  rw [Subgroup.coe_mul]
  change minTorus e6Data_valid k _ = minTorus e6Data_valid k _ * minTorus e6Data_valid k _
  rw [← map_mul]
  rfl

theorem torS_commute (s s' : Fin (Tag.rank .F4) → (fixedSubfield θ)ˣ) :
    torS θ s * torS θ s' = torS θ s' * torS θ s := by
  rw [← torS_mul, ← torS_mul, mul_comm]

theorem torS_conj_xFixed (s : Fin (Tag.rank .F4) → (fixedSubfield θ)ˣ)
    {α : Fin (Tag.rank .E6) → ℤ} (hα : IsRoot .E6 α) (hfix : rho α = α) (c : k) (hc : θ c = c) :
    torS θ s * xFixed θ hα hfix c hc * (torS θ s)⁻¹ =
      xFixed θ hα hfix (((chiS θ s (proj α) : fixedSubfield θ) : k) * c)
        (by rw [map_mul, hc, theta_coe]) := by
  refine Subtype.ext ?_
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, xFixed_val, xFixed_val]
  change minTorus e6Data_valid k _ * _ * (minTorus e6Data_valid k _)⁻¹ = _
  rw [minTorus_conj_xm e6Data_valid k _ hα, rootChar_split]
  rfl

theorem torS_conj_xPair (hθ : ∀ c, θ (θ c) = c) (s : Fin (Tag.rank .F4) → (fixedSubfield θ)ˣ)
    {α : Fin (Tag.rank .E6) → ℤ} (hα : IsRoot .E6 α) (hne : rho α ≠ α) (c : k) :
    torS θ s * xPair θ hθ hα hne c * (torS θ s)⁻¹ =
      xPair θ hθ hα hne (((chiS θ s (proj α) : fixedSubfield θ) : k) * c) := by
  rw [torS, torU_conj_xPair θ hθ _ hα hne c, rootChar_split]
  rfl

section Lift

variable {θ} {E : Type*} [Group E] {π : E →* fixedGroup k θ}

@[expose] def LiftsCommute (π : E →* fixedGroup k θ) (β : Fin (Tag.rank .F4) → ℤ) : Prop :=
  ∀ y ∈ twistedRootGroup k θ β, ∀ y' ∈ twistedRootGroup k θ β, ∀ e e' : E, π e = y →
    π e' = y' → e * e' = e' * e

theorem liftsCommute_reflect (hπ : Function.Surjective π) (i : Fin (Tag.rank .F4))
    {β : Fin (Tag.rank .F4) → ℤ} (hβ : IsRoot .F4 β) (h : LiftsCommute π β) :
    LiftsCommute π (reflect .F4 i β) := by
  set n := nHat θ i
  have hinv : ∀ y ∈ twistedRootGroup k θ (reflect .F4 i β),
      n⁻¹ * y * n ∈ twistedRootGroup k θ β := by
    intro y hy
    have h1 := nHat_conj_mem θ i (IsRoot.reflect i hβ) hy
    rw [reflect_reflect] at h1
    have h2 := hHat_conj_mem θ i hβ (inv_mem (nHat_sq_mem θ i)) h1
    have e : (n ^ 2)⁻¹ * (n * y * n⁻¹) * ((n ^ 2)⁻¹)⁻¹ = n⁻¹ * y * n := by group
    rwa [e] at h2
  intro y hy y' hy' e e' he he'
  obtain ⟨m, hm⟩ := hπ n
  have hc := h _ (hinv y hy) _ (hinv y' hy') (m⁻¹ * e * m) (m⁻¹ * e' * m)
    (by rw [map_mul, map_mul, map_inv, hm, he]) (by rw [map_mul, map_mul, map_inv, hm, he'])
  calc e * e' = m * ((m⁻¹ * e * m) * (m⁻¹ * e' * m)) * m⁻¹ := by group
    _ = m * ((m⁻¹ * e' * m) * (m⁻¹ * e * m)) * m⁻¹ := by rw [hc]
    _ = e' * e := by group

theorem liftsCommute_of_isRoot (hπ : Function.Surjective π)
    (hsimple : ∀ j, LiftsCommute π (Pi.single j 1)) {β : Fin (Tag.rank .F4) → ℤ}
    (hβ : IsRoot .F4 β) : LiftsCommute π β := by
  induction hβ with
  | basis j => exact hsimple j
  | @reflect i v hv ih => exact liftsCommute_reflect hπ i hv ih

variable (hcen : π.ker ≤ Subgroup.center E)
include hcen

theorem commPairing_eq_zero_of_liftsCommute (hπ : Function.Surjective π) {F : Type*} [Field F]
    {x : F → fixedGroup k θ} (hx : ∀ s t, x (s + t) = x s * x t) {β : Fin (Tag.rank .F4) → ℤ}
    (hmem : ∀ c, x c ∈ twistedRootGroup k θ β) (h : LiftsCommute π β) :
    TorusLift.commPairing hcen hπ hx = 0 := by
  refine AddMonoidHom.ext fun s => AddMonoidHom.ext fun t => ?_
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [TorusLift.commPairing_apply, AddMonoidHom.zero_apply, AddMonoidHom.zero_apply, toMul_zero,
    OneMemClass.coe_one, commutatorElement_eq_one_iff_mul_comm]
  exact h _ (hmem s) _ (hmem t) _ _ (TorusLift.map_lift hπ _) (TorusLift.map_lift hπ _)

theorem liftsCommute_of_commPairing_eq_zero (hπ : Function.Surjective π) {F : Type*} [Field F]
    {x : F → fixedGroup k θ} (hx : ∀ s t, x (s + t) = x s * x t) {β : Fin (Tag.rank .F4) → ℤ}
    (hpar : ∀ y ∈ twistedRootGroup k θ β, ∃ c, x c = y)
    (h0 : TorusLift.commPairing hcen hπ hx = 0) : LiftsCommute π β := by
  intro y hy y' hy' e e' he he'
  obtain ⟨c, rfl⟩ := hpar y hy
  obtain ⟨d, rfl⟩ := hpar y' hy'
  exact TorusLift.commute_of_commPairing_eq_zero hcen hπ hx h0 he he'

end Lift

end CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed
