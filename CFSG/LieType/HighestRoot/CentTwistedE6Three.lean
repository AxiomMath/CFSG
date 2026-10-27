module

public import CFSG.LieType.HighestRoot.CentTwistedE6Act
public import CFSG.LieType.HighestRoot.CentTwistedE6Main
public import CFSG.LieType.HighestRoot.CentTrialityThree

public section

namespace CFSG.LieType.HighestRoot

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.CurtisTits CFSG.ClassicalInvolution.ModelFacts
  CFSG.ClassicalInvolution.ModelFacts.ChevAut CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  MinData.Valid
open scoped Matrix

@[expose] def a5Nodes : List (Fin (Tag.rank .E6)) := [nd 0, nd 2, nd 4, nd 5]

abbrev deltaE6 : Fin (Tag.rank .E6) → ℤ := ![0, 1, 1, 2, 1, 0]

@[expose] def a5Gens : List (Fin (Tag.rank .E6) → ℤ) :=
  [Pi.single (nd 0) 1, -Pi.single (nd 0) 1, Pi.single (nd 2) 1, -Pi.single (nd 2) 1,
    Pi.single (nd 4) 1, -Pi.single (nd 4) 1, Pi.single (nd 5) 1, -Pi.single (nd 5) 1,
    deltaE6 + Pi.single (nd 0) 1, -deltaE6 + -Pi.single (nd 0) 1]

@[expose] def a5Step (l : List (Fin (Tag.rank .E6) → ℤ)) : List (Fin (Tag.rank .E6) → ℤ) :=
  (l ++ l.flatMap fun γ => a5Nodes.map fun i => reflect .E6 i γ).dedup

theorem a5_check : ∀ γ ∈ rootFinset .E6, corootPair .E6 e6one γ % 2 = 0 →
    γ = Pi.single e6one 1 ∨ γ = -Pi.single e6one 1 ∨ γ ∈ a5Step (a5Step (a5Step a5Gens)) := by
  decide +kernel

theorem isRoot_deltaE6
    : IsRoot .E6 deltaE6 := mem_rootFinset.1 (by decide +kernel)

theorem rho_deltaE6 : rho deltaE6 = deltaE6 := by decide

theorem rho_neg_deltaE6 : rho (-deltaE6) = -deltaE6 := by decide

theorem isRoot_smul_single (a : Fin (Tag.rank .E6)) {s : ℤ} (hs : s = 1 ∨ s = -1) :
    IsRoot .E6 (s • Pi.single a 1) := by
  rcases hs with rfl | rfl
  · rw [one_smul]
    exact .basis a
  · rw [neg_one_smul]
    exact isRoot_neg_single _ a

variable {k : Type} [Field k]

theorem commute_xm_smul_single_one
    {γ : Fin (Tag.rank .E6) → ℤ} (hγ : IsRoot .E6 γ)
    (h : ∀ s : ℤ, (s = 1 ∨ s = -1) → γ + s • Pi.single e6one 1 ≠ 0 ∧
      MinData.toWeight (γ + s • Pi.single e6one 1) ⬝ᵥ (γ + s • Pi.single e6one 1) ≠ 2)
    {s : ℤ} (hs : s = 1 ∨ s = -1) (c d : k) :
    Commute (e6Data_valid.xm k γ c) (e6Data_valid.xm k (s • Pi.single e6one 1) d) :=
  commute_xm hγ (isRoot_smul_single _ hs) (h s hs).1 (not_isRoot_of_form (h s hs).2) c d

theorem rootGroup_le_centralizer_of_commute
    {γ : Fin (Tag.rank .E6) → ℤ}
    (hγ : ∀ s : ℤ, (s = 1 ∨ s = -1) → ∀ c d : k,
      Commute (e6Data_valid.xm k γ c) (e6Data_valid.xm k (s • Pi.single e6one 1) d))
    {z : e6Data_valid.minGroup k} (hz : z ∈ rankOneE6one k) :
    e6Data_valid.rootGroup k γ ≤ Subgroup.centralizer ({z} : Set (e6Data_valid.minGroup k)) := by
  intro x hx
  obtain ⟨c, rfl⟩ := (e6Data_valid.mem_rootGroup k).1 hx
  have h1 := hγ 1 (Or.inl rfl) c
  have h2 := hγ (-1) (Or.inr rfl) c
  simp only [one_smul, neg_one_smul] at h1 h2
  have hle : rankOneE6one k ≤
      Subgroup.centralizer ({e6Data_valid.xm k γ c} : Set (e6Data_valid.minGroup k)) := by
    refine sup_le (fun y hy => ?_) (fun y hy => ?_)
    · obtain ⟨d, rfl⟩ := (e6Data_valid.mem_rootGroup k).1 hy
      exact Subgroup.mem_centralizer_singleton_iff.2 (h1 d).eq.symm
    · obtain ⟨d, rfl⟩ := (e6Data_valid.mem_rootGroup k).1 hy
      exact Subgroup.mem_centralizer_singleton_iff.2 (h2 d).eq.symm
  exact Subgroup.mem_centralizer_singleton_iff.2
    (Subgroup.mem_centralizer_singleton_iff.1 (hle hz)).symm

theorem rankOne_le_centralizer
    {a : Fin (Tag.rank .E6)}
    (ha : a = nd 0 ∨ a = nd 2 ∨ a = nd 4 ∨ a = nd 5) {z : e6Data_valid.minGroup k}
    (hz : z ∈ rankOneE6one k) :
    rankOne (e6Data_valid.rootGroup k) a ≤
      Subgroup.centralizer ({z} : Set (e6Data_valid.minGroup k)) := by
  have key : ∀ t : ℤ, (t = 1 ∨ t = -1) →
      e6Data_valid.rootGroup k (t • Pi.single a 1) ≤
        Subgroup.centralizer ({z} : Set (e6Data_valid.minGroup k)) := by
    intro t ht
    refine rootGroup_le_centralizer_of_commute (fun s hs c d => ?_) hz
    refine commute_xm_smul_single_one (isRoot_smul_single a ht) (fun s' hs' => ?_) hs c d
    rcases ha with rfl | rfl | rfl | rfl <;> rcases ht with rfl | rfl <;>
      rcases hs' with rfl | rfl <;> decide
  have h1 := key 1 (Or.inl rfl)
  have h2 := key (-1) (Or.inr rfl)
  rw [one_smul] at h1
  rw [neg_one_smul] at h2
  exact sup_le h1 h2

variable (θ : k →+* k)

theorem slRankOne_lower
    (a : Fin (Tag.rank .E6)) (c : k) :
    (slRankOne k a (slLower k c) : e6Data_valid.minGroup k) =
      e6Data_valid.xm k (-Pi.single a 1) c :=
  Subtype.ext (Units.ext (by
    change e6Data_valid.blockOp k a (slLower k c : Matrix (Fin 2) (Fin 2) k) = _
    rw [slLower_val, e6Data_valid.blockOp_lower]
    rfl))

theorem slOrbitHom_lower
    (hθ : ∀ c, θ (θ c) = c) {a b : Fin (Tag.rank .E6)}
    (hab : (a = nd 2 ∧ b = nd 4) ∨ (a = nd 0 ∧ b = nd 5)) (c : k) :
    (slOrbitHom θ hθ hab (slLower k c) : e6Data_valid.minGroup k) =
      e6Data_valid.xm k (-Pi.single a 1) c * e6Data_valid.xm k (-Pi.single b 1) (θ c) := by
  change phiOrbit θ hab (slRankOne k a (slLower k c)) = _
  rw [phiOrbit_apply, slRankOne_lower, sigma_xm_neg_single, rhoPerm_of_orbit hab]

theorem slOrbitHom_mem_centralizer
    (hθ : ∀ c, θ (θ c) = c) {a b : Fin (Tag.rank .E6)}
    (hab : (a = nd 2 ∧ b = nd 4) ∨ (a = nd 0 ∧ b = nd 5)) {z : fixedGroup k θ}
    (hz : z ∈ rankOneTwE6 k θ) (M : Matrix.SpecialLinearGroup (Fin 2) k) :
    slOrbitHom θ hθ hab M ∈ Subgroup.centralizer ({z} : Set (fixedGroup k θ)) := by
  have hz' := coe_mem_rankOneE6one θ hz
  have ha : a = nd 0 ∨ a = nd 2 ∨ a = nd 4 ∨ a = nd 5 := by
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  have hb : b = nd 0 ∨ b = nd 2 ∨ b = nd 4 ∨ b = nd 5 := by
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  set y := slRankOne k a M
  have hy : (y : e6Data_valid.minGroup k) ∈ rankOne (e6Data_valid.rootGroup k) a := y.2
  have hσy : sigma k θ y ∈ rankOne (e6Data_valid.rootGroup k) b :=
    rhoPerm_of_orbit hab ▸ sigma_mem_rankOne θ hy
  have c1 := Subgroup.mem_centralizer_singleton_iff.1 (rankOne_le_centralizer ha hz' hy)
  have c2 := Subgroup.mem_centralizer_singleton_iff.1 (rankOne_le_centralizer hb hz' hσy)
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  change (y : e6Data_valid.minGroup k) * sigma k θ y * z = z * (y * sigma k θ y)
  rw [mul_assoc, c2, ← mul_assoc, c1, mul_assoc]

theorem xFixed_mem_centralizer
    {γ : Fin (Tag.rank .E6) → ℤ} (hγ : IsRoot .E6 γ)
    (hfix : rho γ = γ)
    (h : ∀ s : ℤ, (s = 1 ∨ s = -1) → γ + s • Pi.single e6one 1 ≠ 0 ∧
      MinData.toWeight (γ + s • Pi.single e6one 1) ⬝ᵥ (γ + s • Pi.single e6one 1) ≠ 2)
    {z : fixedGroup k θ} (hz : z ∈ rankOneTwE6 k θ) :
    xFixed θ hγ hfix 1 (map_one θ) ∈ Subgroup.centralizer ({z} : Set (fixedGroup k θ)) := by
  have hle := rootGroup_le_centralizer_of_commute
    (fun s hs c d => commute_xm_smul_single_one hγ h hs c d) (coe_mem_rankOneE6one θ hz)
  have hmem := hle (e6Data_valid.xm_mem_rootGroup k γ 1)
  rw [Subgroup.mem_centralizer_singleton_iff] at hmem ⊢
  exact Subtype.ext hmem

section Closure

variable
    {x : e6Data_valid.minGroup k}

theorem commute_nm
    {i : Fin (Tag.rank .E6)}
    (h1 : ∀ c : k, Commute x (e6Data_valid.xm k (Pi.single i 1) c))
    (h2 : ∀ c : k, Commute x (e6Data_valid.xm k (-Pi.single i 1) c)) :
    Commute x (e6Data_valid.nm k i) :=
  ((h1 _).mul_right (h2 _)).mul_right (h1 _)

theorem commute_xm_reflect
    {γ : Fin (Tag.rank .E6) → ℤ} (hγ : IsRoot .E6 γ)
    {i : Fin (Tag.rank .E6)} (h1 : ∀ c : k, Commute x (e6Data_valid.xm k (Pi.single i 1) c))
    (h2 : ∀ c : k, Commute x (e6Data_valid.xm k (-Pi.single i 1) c))
    (hx : ∀ c : k, Commute x (e6Data_valid.xm k γ c)) (c : k) :
    Commute x (e6Data_valid.xm k (reflect .E6 i γ) c) := by
  obtain ⟨σ, hσ, hconj⟩ := e6Data_valid.nm_conj_xm k hγ i
  have e : e6Data_valid.xm k (reflect .E6 i γ) c =
      e6Data_valid.nm k i * e6Data_valid.xm k γ (σ * c) * (e6Data_valid.nm k i)⁻¹ := by
    rw [hconj, ← mul_assoc, hσ.mul_self, one_mul]
  rw [e]
  have hn := commute_nm h1 h2
  exact (hn.mul_right (hx _)).mul_right hn.inv_right

theorem forall_mem_a5Step_iterate
    (hgen : ∀ γ ∈ a5Gens, IsRoot .E6 γ ∧ ∀ c : k, Commute x (e6Data_valid.xm k γ c))
    (hnodes : ∀ i ∈ a5Nodes, (∀ c : k, Commute x (e6Data_valid.xm k (Pi.single i 1) c)) ∧
      ∀ c : k, Commute x (e6Data_valid.xm k (-Pi.single i 1) c)) :
    ∀ n : ℕ, ∀ γ ∈ a5Step^[n] a5Gens,
      IsRoot .E6 γ ∧ ∀ c : k, Commute x (e6Data_valid.xm k γ c)
  | 0 => hgen
  | n + 1 => by
    intro γ hγ
    rw [Function.iterate_succ_apply', a5Step, List.mem_dedup, List.mem_append,
      List.mem_flatMap] at hγ
    rcases hγ with hγ | ⟨δ, hδ, hγ⟩
    · exact forall_mem_a5Step_iterate hgen hnodes n γ hγ
    · obtain ⟨hδr, hδc⟩ := forall_mem_a5Step_iterate hgen hnodes n δ hδ
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hγ
      exact ⟨hδr.reflect i, commute_xm_reflect hδr (hnodes i hi).1 (hnodes i hi).2 hδc⟩

end Closure

section Module

variable
    {x : e6Data_valid.minGroup k}

theorem commute_endo
    {y : e6Data_valid.minGroup k} (h : Commute x y) :
    Commute (e6Data_valid.endo k x) (e6Data_valid.endo k y) := by
  change e6Data_valid.endo k x * e6Data_valid.endo k y =
    e6Data_valid.endo k y * e6Data_valid.endo k x
  rw [← e6Data_valid.endo_mul, ← e6Data_valid.endo_mul, h.eq]

theorem commute_xm_of_commute_rootOp
    {γ : Fin (Tag.rank .E6) → ℤ}
    (h : Commute (e6Data_valid.endo k x) (e6Data.rootOp k γ)) (c : k) :
    Commute x (e6Data_valid.xm k γ c) := by
  change x * e6Data_valid.xm k γ c = e6Data_valid.xm k γ c * x
  apply e6Data_valid.endo_injective k
  rw [e6Data_valid.endo_mul, e6Data_valid.endo_mul, e6Data_valid.endo_xm]
  exact ((Commute.one_right _).add_right (h.smul_right c)).eq

theorem commute_rootOp_conj
    (h2 : (2 : k) ≠ 0) {ω : k} (hω : θ ω ≠ ω)
    {g : e6Data_valid.minGroup k} {γ₁ γ₂ : Fin (Tag.rank .E6) → ℤ}
    (h : ∀ c : k, Commute x (g * (e6Data_valid.xm k γ₁ c * e6Data_valid.xm k γ₂ (θ c)) * g⁻¹)) :
    Commute (e6Data_valid.endo k x)
        (e6Data_valid.endo k g * e6Data.rootOp k γ₁ * e6Data_valid.endo k g⁻¹) ∧
      Commute (e6Data_valid.endo k x)
        (e6Data_valid.endo k g * e6Data.rootOp k γ₂ * e6Data_valid.endo k g⁻¹) := by
  refine commute_of_forall_commute_one_add_smul_mul θ h2 hω fun c => ?_
  have hc := commute_endo (h c)
  have hgg : e6Data_valid.endo k g * e6Data_valid.endo k g⁻¹ = 1 := e6Data_valid.endo_mul_inv k g
  have hgg' : e6Data_valid.endo k g⁻¹ * e6Data_valid.endo k g = 1 :=
    e6Data_valid.endo_inv_mul k g
  have e : ∀ (d : k) (Y : Module.End k (Fin e6Data.d →₀ k)),
      e6Data_valid.endo k g * (1 + d • Y) * e6Data_valid.endo k g⁻¹ =
        1 + d • (e6Data_valid.endo k g * Y * e6Data_valid.endo k g⁻¹) := by
    intro d Y
    rw [mul_add, add_mul, mul_one, hgg, mul_smul_comm, smul_mul_assoc]
  rw [e6Data_valid.endo_mul, e6Data_valid.endo_mul, e6Data_valid.endo_mul, e6Data_valid.endo_xm,
    e6Data_valid.endo_xm] at hc
  have e2 : ∀ P Q : Module.End k (Fin e6Data.d →₀ k),
      e6Data_valid.endo k g * (P * Q) * e6Data_valid.endo k g⁻¹ =
        (e6Data_valid.endo k g * P * e6Data_valid.endo k g⁻¹) *
          (e6Data_valid.endo k g * Q * e6Data_valid.endo k g⁻¹) := by
    intro P Q
    simp only [mul_assoc]
    rw [← mul_assoc (e6Data_valid.endo k g⁻¹) (e6Data_valid.endo k g), hgg', one_mul]
  rwa [e2, e, e] at hc

theorem commute_rootOp_add
    {γ δ : Fin (Tag.rank .E6) → ℤ} (hγ : IsRoot .E6 γ)
    (hδ : IsRoot .E6 δ) (hne : δ + γ ≠ 0) (hr : IsRoot .E6 (δ + γ))
    (hc : Commute (e6Data_valid.endo k x)
      ((1 + (1 : k) • e6Data.rootOp k δ) * e6Data.rootOp k γ * (1 - (1 : k) • e6Data.rootOp k δ)))
    (hγc : Commute (e6Data_valid.endo k x) (e6Data.rootOp k γ)) :
    Commute (e6Data_valid.endo k x) (e6Data.rootOp k (δ + γ)) := by
  obtain ⟨⟨σ, hσ, h1⟩, h2, -⟩ := (e6Data_valid.pairRel (R := k) hδ hγ hne).1 hr
  have e : (1 + (1 : k) • e6Data.rootOp k δ) * e6Data.rootOp k γ *
      (1 - (1 : k) • e6Data.rootOp k δ) = e6Data.rootOp k γ + σ • e6Data.rootOp k (δ + γ) := by
    rw [one_smul, ← h1]
    calc (1 + e6Data.rootOp k δ) * e6Data.rootOp k γ * (1 - e6Data.rootOp k δ) =
        e6Data.rootOp k γ + (e6Data.rootOp k δ * e6Data.rootOp k γ -
          e6Data.rootOp k γ * e6Data.rootOp k δ) -
            e6Data.rootOp k δ * e6Data.rootOp k γ * e6Data.rootOp k δ := by noncomm_ring
      _ = _ := by rw [h2, sub_zero]
  rw [e] at hc
  have h3 : Commute (e6Data_valid.endo k x) (σ • e6Data.rootOp k (δ + γ)) := by
    have h4 := hc.sub_right hγc
    rwa [add_sub_cancel_left] at h4
  rcases hσ with rfl | rfl
  · rwa [one_smul] at h3
  · rwa [neg_one_smul, Commute.neg_right_iff] at h3

end Module

section Isogeny

variable [Finite k]

theorem ringChar_eq_three_of_card_eq_nine (hk9 : Nat.card k = 9) : ringChar k = 3 := by
  have : Fintype k := Fintype.ofFinite k
  have hp := CharP.prime_ringChar k
  have h9 : ((9 : ℕ) : k) = 0 := by
    have h := FiniteField.cast_card_eq_zero k
    rwa [← Nat.card_eq_fintype_card, hk9] at h
  have hdvd : ringChar k ∣ 3 ^ 2 := ringChar.dvd h9
  exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow hdvd)

theorem mem_rankOneE6one_of_forall_commute
    (hk9 : Nat.card k = 9)
    {z x : e6Data_valid.minGroup k} (hz : z ∈ rankOneE6one k) (h2 : orderOf z = 2)
    (hxz : x * z = z * x) (hx3 : x ^ 3 = 1)
    (hcomm : ∀ γ ∈ a5Step (a5Step (a5Step a5Gens)), ∀ c : k,
      Commute x (e6Data_valid.xm k γ c)) :
    x ∈ rankOneE6one k := by
  have hk3 := ringChar_eq_three_of_card_eq_nine hk9
  have hK : ringChar k ≠ 2 := by rw [hk3]; decide
  have hK3 : Nat.Coprime 3 (Nat.card k - 1) := by rw [hk9]; decide
  have := finite_minGroup e6Data_valid k
  have : Fact (ringChar k).Prime := ⟨CharP.prime_ringChar k⟩
  set φ := e6Isogeny k with hφ
  have hX : ∀ α, IsRoot .E6 α → (e6Data_valid.rootGroup k α).map φ =
      rootGroup (rootOperatorFamily .E6) k α := fun α hα => map_e6Isogeny_rootGroup k hα
  have hker := e6Isogeny_ker_le_center k
  have hpk := e6Isogeny_not_dvd_card_ker (p := ringChar k) k
  set γ : Fin (Tag.rank .E6) → ℤ := Pi.single e6one 1 with hγ_def
  have hγ : IsRoot .E6 γ := isRoot_single _ e6one
  have hJmap := map_sup_eq_rankOneGroup φ (e6Data_valid.rootGroup k) hX hγ
  obtain ⟨e⟩ := nonempty_rankOneGroup_adjDatum_equiv (τ := .E6) hK e6one
  have hinj := eq_one_of_map_eq_one_of_card_le φ ((MulEquiv.subgroupCongr hJmap).trans e)
    (card_rankOne_le e6Data_valid k e6one)
  rw [rankOneGroup_adjDatum _ hγ] at hJmap
  have hz1 : z ≠ 1 := fun h => by rw [h, orderOf_one] at h2; exact absurd h2 (by decide)
  have hφz1 : φ z ≠ 1 := fun h => hz1 (hinj z hz h)
  have hφz2 : orderOf (φ z) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime ?_ hφz1
    rw [← map_pow, ← h2, pow_orderOf_eq_one, map_one]
  have hφzQ : (φ z : ModGL .E6 k) ∈ rootSubgroup .E6 k γ ⊔ rootSubgroup .E6 k (-γ) :=
    Subgroup.mem_subgroupOf.1 (hJmap ▸ Subgroup.mem_map_of_mem φ hz)
  have hzC : (φ z : ModGL .E6 k) = rootDiagUnit .E6 (signTuple .E6 k e6one) := by
    rw [← torusElt_neg_one_eq]
    exact eq_torusElt_neg_one hK e6one hφzQ (by rwa [Subgroup.orderOf_coe])
  have hxT : (φ x : ModGL .E6 k) ∈ toralCentralizer .E6 k (signTuple .E6 k e6one) := by
    refine (mem_toralCentralizer_iff_mem_centralizer hzC (φ x)).2
      (Subgroup.mem_centralizer_singleton_iff.2 ?_)
    rw [← map_mul, ← map_mul, hxz]
  have hφx3 : (φ x : ModGL .E6 k) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, ← map_pow, hx3, map_one]
    rfl
  have hker' := rootCharKernel_signTuple_eq (τ := .E6) (i := e6one) hK
  have hxS := mem_rootSpan_of_pow_three_eq_one hK3 hK (signTuple_eq_one_or_eq_neg_one e6one)
    hxT hφx3
  rw [hker'] at hxS
  set χ := signChar .E6 k e6one with hχ
  have hγk : γ ∈ kernelRoots χ := hker' ▸ single_mem_rootCharKernel_signTuple hK e6one
  set k₀ : KernelComponent χ := ⟦⟨γ, hγk⟩⟧ with hk₀
  have hxk : ∀ k', k' ≠ k₀ → ∀ y ∈ componentRootSpan k χ k',
      (φ x : ModGL .E6 k) * y = y * φ x := by
    intro k' hk' y hy
    have hle : componentRootSpan k χ k' ≤
        Subgroup.centralizer ({(φ x : ModGL .E6 k)} : Set (ModGL .E6 k)) := by
      refine iSup₂_le fun α hα => ?_
      obtain ⟨hαk, hαmk⟩ := hα
      have hα' : α ∈ rootCharKernel (signTuple .E6 k e6one) := hker' ▸ hαk
      rw [mem_rootCharKernel_signTuple hK] at hα'
      rcases a5_check α (mem_rootFinset.2 hα'.1) (Int.even_iff.1 hα'.2) with h | h | h
      · exfalso
        apply hk'
        rw [← hαmk]
        exact congrArg (fun a => (⟦a⟧ : KernelComponent χ)) (Subtype.ext h)
      · exfalso
        apply hk'
        rw [← hαmk]
        have hneg : (⟨α, hαk⟩ : kernelRoots χ) = ⟨-γ, ⟨IsRoot.neg hγk.1, chi_neg hγk.2⟩⟩ :=
          Subtype.ext h
        rw [hneg]
        exact mk_eq_of_iform_ne_zero (iform_neg_self_ne_zero hγ)
      · intro s hs
        have hsH : s ∈ adjointGroup .E6 k := rootSubgroup_le_adjointGroup α hs
        have hs' : (⟨s, hsH⟩ : adjointGroup .E6 k) ∈ (e6Data_valid.rootGroup k α).map φ := by
          rw [hX α hα'.1, rootGroup_eq_subgroupOf hα'.1]
          exact Subgroup.mem_subgroupOf.2 hs
        obtain ⟨m, hm, hφm⟩ := hs'
        obtain ⟨c, rfl⟩ := (e6Data_valid.mem_rootGroup k).1 hm
        have hc := congrArg (fun w => ((φ w : adjointGroup .E6 k) : ModGL .E6 k))
          (hcomm α h c).eq
        simp only [map_mul, Subgroup.coe_mul, hφm] at hc
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact hc.symm
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hy)).symm
  obtain ⟨j, hj, t, ⟨htT, htJ⟩, hxtj⟩ := exists_eq_mul_of_commute χ k₀ hxS hxk
  have hcomm' : Commute t j := ((Subgroup.mem_centralizer_iff.1 htJ) j hj).symm
  have hpow : (t * j) ^ 3 = 1 := by rw [← hxtj]; exact hφx3
  rw [hcomm'.mul_pow] at hpow
  have ht3 : t ^ 3 ∈ componentRootSpan k χ k₀ := by
    rw [eq_inv_of_mul_eq_one_left hpow]
    exact inv_mem (pow_mem hj 3)
  have hcop : Nat.Coprime 3 (orderOf t) :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one
      (pow_card_sub_one_eq_one_of_mem_diagonalGroup (torusGroup_le_diagonalGroup htT))) hK3
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  have htS : t ∈ componentRootSpan k χ k₀ := by
    rw [← hm]
    exact pow_mem ht3 m
  have hxS₀ : (φ x : ModGL .E6 k) ∈ componentRootSpan k χ k₀ := by
    rw [hxtj]
    exact mul_mem htS hj
  have hS₀ : componentRootSpan k χ k₀ = rootSubgroup .E6 k γ ⊔ rootSubgroup .E6 k (-γ) := by
    rw [← rootSpan_pair_eq]
    change rootSpan .E6 k (componentRoots χ k₀) = _
    congr 1
    ext α
    constructor
    · rintro ⟨hα, hαk⟩
      exact (mem_pair_iff_of_mk_eq hK (iform_le_of_symmetrizer_le
        (symmetrizer_le_one .E6 rfl _)) hαk).2 (Or.inl rfl)
    · rintro (rfl | rfl)
      · exact ⟨hγk, rfl⟩
      · exact ⟨⟨IsRoot.neg hγk.1, chi_neg hγk.2⟩,
          mk_eq_of_iform_ne_zero (iform_neg_self_ne_zero hγk.1)⟩
  have hφxJ : φ x ∈ (e6Data_valid.rootGroup k γ ⊔ e6Data_valid.rootGroup k (-γ)).map φ := by
    rw [hJmap]
    exact Subgroup.mem_subgroupOf.2 (hS₀ ▸ hxS₀)
  exact mem_of_map_mem φ hker hpk hφxJ (n := 1) (by rw [hk3, pow_one]; exact hx3)

end Isogeny

theorem exists_slFixed_eq
    {g : fixedGroup k θ}
    (hg : (g : e6Data_valid.minGroup k) ∈ rankOneE6one k) :
    ∃ N : Matrix.SpecialLinearGroup (Fin 2) (TwistedD4.fixedField θ),
      ((g : e6Data_valid.minGroup k) : (Module.End k (Fin e6Data.d →₀ k))ˣ) =
        e6Data_valid.slHom k e6one
          (Matrix.SpecialLinearGroup.map (TwistedD4.fixedField θ).subtype N) := by
  obtain ⟨M, hM, hσM⟩ := exists_slHom_sigma θ hg
  have hfixM : Matrix.SpecialLinearGroup.map θ M = M := by
    apply slHom_injective e6one
    rw [← hσM, ← hM, (mem_fixedGroup θ).1 g.2]
  have hent : ∀ p q, θ ((M : Matrix (Fin 2) (Fin 2) k) p q) = (M : Matrix (Fin 2) (Fin 2) k) p q :=
    fun p q => congrArg (fun N : Matrix.SpecialLinearGroup (Fin 2) k =>
      (N : Matrix (Fin 2) (Fin 2) k) p q) hfixM
  let M' : Matrix (Fin 2) (Fin 2) (TwistedD4.fixedField θ) := fun p q =>
    ⟨(M : Matrix (Fin 2) (Fin 2) k) p q, hent p q⟩
  have hdet : M'.det = 1 := by
    apply Subtype.ext
    have h1 : ((M'.det : TwistedD4.fixedField θ) : k) = (M : Matrix (Fin 2) (Fin 2) k).det := by
      rw [Matrix.det_fin_two, Matrix.det_fin_two]
      rfl
    rw [h1, M.2]
    rfl
  refine ⟨⟨M', hdet⟩, ?_⟩
  rw [hM]
  congr 1

theorem card_rankOneTwE6_le
    [Finite k] :
    Nat.card (rankOneTwE6 k θ) ≤
      Nat.card (Matrix.SpecialLinearGroup (Fin 2) (TwistedD4.fixedField θ)) := by
  classical
  choose F hF using fun g : rankOneTwE6 k θ => exists_slFixed_eq θ (coe_mem_rankOneE6one θ g.2)
  refine Nat.card_le_card_of_injective F fun g g' h => ?_
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  rw [hF g, hF g', h]

theorem card_center_SL2_mul_lt [Finite k] (hk9 : Nat.card k = 9) :
    Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) k)) * 81 <
      Nat.card (Matrix.SpecialLinearGroup (Fin 2) k) := by
  classical
  have : Fintype k := Fintype.ofFinite k
  have hq : Fintype.card k = 9 := by rw [← Nat.card_eq_fintype_card, hk9]
  have hcard : Nat.card (Matrix.SpecialLinearGroup (Fin 2) k) = 720 := by
    rw [Matrix.card_SL_field, Fin.prod_univ_two, hq]
    norm_num
  have hsub : ((Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) k)) :
      Set (Matrix.SpecialLinearGroup (Fin 2) k)) ⊆
        (({1, -1} : Finset (Matrix.SpecialLinearGroup (Fin 2) k)) :
          Set (Matrix.SpecialLinearGroup (Fin 2) k)) := by
    intro A hA
    obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
    simp only [Fintype.card_fin] at hr
    have hr' : r = 1 ∨ r = -1 := mul_self_eq_one_iff.1 (by rw [← sq]; exact hr)
    rcases hr' with rfl | rfl
    · have e : A = 1 := Subtype.ext (by rw [← hrA]; simp)
      simp [e]
    · have e : A = -1 := Subtype.ext (by
        rw [← hrA, Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one]
        ext i j
        fin_cases i <;> fin_cases j <;> simp)
      simp [e]
  have h2 : Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) k)) ≤ 2 := by
    have h := Nat.card_mono (Set.toFinite _) hsub
    rw [Nat.card_coe_set_eq (({1, -1} : Finset (Matrix.SpecialLinearGroup (Fin 2) k)) :
      Set (Matrix.SpecialLinearGroup (Fin 2) k)), Set.ncard_coe_finset] at h
    exact h.trans Finset.card_le_two
  omega

theorem eq_rankOneTwE6_of_card_eq_nine
    [Finite k] (hk9 : Nat.card k = 9)
    (hθ3 : ∀ c, θ c = c ^ 3) {z : fixedGroup k θ} (hz : z ∈ rankOneTwE6 k θ)
    (h2 : orderOf z = 2) {L : Subgroup (fixedGroup k θ)}
    (hLC : L ≤ Subgroup.centralizer ({z} : Set (fixedGroup k θ)))
    (hCL : Subgroup.centralizer ({z} : Set (fixedGroup k θ)) ≤
      Subgroup.normalizer (L : Set (fixedGroup k θ)))
    {F : Type} [Field F] [Finite F] (hF3 : Nat.card F = 3)
    (eL : L ≃* Matrix.SpecialLinearGroup (Fin 2) F) :
    L = rankOneTwE6 k θ := by
  classical
  have : Fintype k := Fintype.ofFinite k
  have := finite_minGroup e6Data_valid k
  have hk3 := ringChar_eq_three_of_card_eq_nine hk9
  have hK : ringChar k ≠ 2 := by rw [hk3]; decide
  have h2k : (2 : k) ≠ 0 := Ring.two_ne_zero hK
  have hθθ : ∀ c, θ (θ c) = c := fun c => by
    rw [hθ3, hθ3, ← pow_mul]
    have h := FiniteField.pow_card c
    rwa [← Nat.card_eq_fintype_card, hk9] at h
  have hfix3 := card_fixedField_eq_three hK hθ3
  obtain ⟨ω, hω⟩ : ∃ ω : k, θ ω ≠ ω := by
    by_contra hcon
    simp only [not_exists, ne_eq, not_not] at hcon
    have h := Nat.card_congr (Equiv.subtypeUnivEquiv (p := fun c : k => c ∈
      TwistedD4.fixedField θ) hcon)
    rw [hfix3, hk9] at h
    exact absurd h (by decide)
  have hSq : CFSG.IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) k) :=
    isQuasisimple_SL2_of_four_le (by rw [hk9]; decide)
  have hZ := card_center_SL2_mul_lt hk9
  have h2' : orderOf (z : e6Data_valid.minGroup k) = 2 := by rwa [Subgroup.orderOf_coe]
  have hz' := coe_mem_rankOneE6one θ hz
  have hcen : ∀ g ∈ Subgroup.centralizer ({z} : Set (fixedGroup k θ)),
      ∀ {a b : Fin (Tag.rank .E6)} (hab : (a = nd 2 ∧ b = nd 4) ∨ (a = nd 0 ∧ b = nd 5)),
      ∀ y ∈ L, ∀ M, Commute (y : e6Data_valid.minGroup k)
        ((g : e6Data_valid.minGroup k) * (slOrbitHom θ hθθ hab M : e6Data_valid.minGroup k) *
          (g : e6Data_valid.minGroup k)⁻¹) := by
    intro g hg a b hab y hy M
    have hψ : ∀ M, ((MulAut.conj g).toMonoidHom.comp (slOrbitHom θ hθθ hab)) M ∈
        Subgroup.normalizer (L : Set (fixedGroup k θ)) := by
      intro M
      apply hCL
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact mul_mem (mul_mem hg (slOrbitHom_mem_centralizer θ hθθ hab hz M)) (inv_mem hg)
    have h := map_mem_centralizer_of_isQuasisimple hSq hZ hF3 eL _ hψ M
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
    have h' := Subgroup.mem_centralizer_iff.1 h y hy
    exact congrArg Subtype.val h'
  have hJ : ∀ y ∈ L, orderOf y = 3 → y ∈ rankOneTwE6 k θ := by
    intro y hy hy3
    set x : e6Data_valid.minGroup k := y.1 with hx
    have hpair : ∀ g ∈ Subgroup.centralizer ({z} : Set (fixedGroup k θ)),
        ∀ {a b : Fin (Tag.rank .E6)} (hab : (a = nd 2 ∧ b = nd 4) ∨ (a = nd 0 ∧ b = nd 5)),
        (∀ γ ∈ ({Pi.single a 1, Pi.single b 1, -Pi.single a 1, -Pi.single b 1} :
          Set (Fin (Tag.rank .E6) → ℤ)),
          Commute (e6Data_valid.endo k x) (e6Data_valid.endo k (g : e6Data_valid.minGroup k) *
            e6Data.rootOp k γ * e6Data_valid.endo k (g : e6Data_valid.minGroup k)⁻¹)) := by
      intro g hg a b hab
      have hU := commute_rootOp_conj θ h2k hω (x := x) (g := g) (γ₁ := Pi.single a 1)
        (γ₂ := Pi.single b 1) fun c => by
          have h := hcen g hg hab y hy (slUpper k c)
          rwa [slOrbitHom_upper] at h
      have hL := commute_rootOp_conj θ h2k hω (x := x) (g := g) (γ₁ := -Pi.single a 1)
        (γ₂ := -Pi.single b 1) fun c => by
          have h := hcen g hg hab y hy (slLower k c)
          rwa [slOrbitHom_lower] at h
      rintro γ (rfl | rfl | rfl | rfl)
      · exact hU.1
      · exact hU.2
      · exact hL.1
      · exact hL.2
    have h1 : ∀ {a b : Fin (Tag.rank .E6)} (hab : (a = nd 2 ∧ b = nd 4) ∨ (a = nd 0 ∧ b = nd 5)),
        ∀ γ ∈ ({Pi.single a 1, Pi.single b 1, -Pi.single a 1, -Pi.single b 1} :
          Set (Fin (Tag.rank .E6) → ℤ)), ∀ c : k, Commute x (e6Data_valid.xm k γ c) := by
      intro a b hab γ hγ c
      have h := hpair 1 (one_mem _) hab γ hγ
      simp only [OneMemClass.coe_one, inv_one, e6Data_valid.endo_one, one_mul, mul_one] at h
      exact commute_xm_of_commute_rootOp h c
    have h24 := h1 (a := nd 2) (b := nd 4) (Or.inl ⟨rfl, rfl⟩)
    have h05 := h1 (a := nd 0) (b := nd 5) (Or.inr ⟨rfl, rfl⟩)
    have hδz := xFixed_mem_centralizer θ isRoot_deltaE6 rho_deltaE6
      (fun s hs => by rcases hs with rfl | rfl <;> decide) hz
    have hδz' := xFixed_mem_centralizer θ (IsRoot.neg isRoot_deltaE6) rho_neg_deltaE6
      (fun s hs => by rcases hs with rfl | rfl <;> decide) hz
    have hrδ : IsRoot .E6 (deltaE6 + Pi.single (nd 0) 1) := mem_rootFinset.1 (by decide +kernel)
    have hrδ' : IsRoot .E6 (-deltaE6 + -Pi.single (nd 0) 1) :=
      mem_rootFinset.1 (by decide +kernel)
    have hE0 : Commute (e6Data_valid.endo k x) (e6Data.rootOp k (Pi.single (nd 0) 1)) := by
      have h := hpair 1 (one_mem _) (a := nd 0) (b := nd 5) (Or.inr ⟨rfl, rfl⟩)
        (Pi.single (nd 0) 1) (by simp)
      simpa only [OneMemClass.coe_one, inv_one, e6Data_valid.endo_one, one_mul, mul_one] using h
    have hE0' : Commute (e6Data_valid.endo k x) (e6Data.rootOp k (-Pi.single (nd 0) 1)) := by
      have h := hpair 1 (one_mem _) (a := nd 0) (b := nd 5) (Or.inr ⟨rfl, rfl⟩)
        (-Pi.single (nd 0) 1) (by simp)
      simpa only [OneMemClass.coe_one, inv_one, e6Data_valid.endo_one, one_mul, mul_one] using h
    have hδ1 : Commute (e6Data_valid.endo k x)
        (e6Data.rootOp k (deltaE6 + Pi.single (nd 0) 1)) := by
      have h := hpair _ hδz (a := nd 0) (b := nd 5) (Or.inr ⟨rfl, rfl⟩) (Pi.single (nd 0) 1)
        (by simp)
      rw [xFixed_val, e6Data_valid.endo_xm, e6Data_valid.endo_xm_inv] at h
      exact commute_rootOp_add (isRoot_single _ _) isRoot_deltaE6 (by decide) hrδ h hE0
    have hδ2 : Commute (e6Data_valid.endo k x)
        (e6Data.rootOp k (-deltaE6 + -Pi.single (nd 0) 1)) := by
      have h := hpair _ hδz' (a := nd 0) (b := nd 5) (Or.inr ⟨rfl, rfl⟩) (-Pi.single (nd 0) 1)
        (by simp)
      rw [xFixed_val, e6Data_valid.endo_xm, e6Data_valid.endo_xm_inv] at h
      exact commute_rootOp_add (isRoot_neg_single _ _) (IsRoot.neg isRoot_deltaE6) (by decide)
        hrδ' h hE0'
    have hnodes : ∀ i ∈ a5Nodes, (∀ c : k, Commute x (e6Data_valid.xm k (Pi.single i 1) c)) ∧
        ∀ c : k, Commute x (e6Data_valid.xm k (-Pi.single i 1) c) := by
      intro i hi
      simp only [a5Nodes, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl
      · exact ⟨h05 _ (by simp), h05 _ (by simp)⟩
      · exact ⟨h24 _ (by simp), h24 _ (by simp)⟩
      · exact ⟨h24 _ (by simp), h24 _ (by simp)⟩
      · exact ⟨h05 _ (by simp), h05 _ (by simp)⟩
    have hgen : ∀ γ ∈ a5Gens, IsRoot .E6 γ ∧ ∀ c : k, Commute x (e6Data_valid.xm k γ c) := by
      intro γ hγ
      simp only [a5Gens, List.mem_cons, List.not_mem_nil, or_false] at hγ
      rcases hγ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨isRoot_single _ _, (hnodes _ (by simp [a5Nodes])).1⟩
      · exact ⟨isRoot_neg_single _ _, (hnodes _ (by simp [a5Nodes])).2⟩
      · exact ⟨isRoot_single _ _, (hnodes _ (by simp [a5Nodes])).1⟩
      · exact ⟨isRoot_neg_single _ _, (hnodes _ (by simp [a5Nodes])).2⟩
      · exact ⟨isRoot_single _ _, (hnodes _ (by simp [a5Nodes])).1⟩
      · exact ⟨isRoot_neg_single _ _, (hnodes _ (by simp [a5Nodes])).2⟩
      · exact ⟨isRoot_single _ _, (hnodes _ (by simp [a5Nodes])).1⟩
      · exact ⟨isRoot_neg_single _ _, (hnodes _ (by simp [a5Nodes])).2⟩
      · exact ⟨hrδ, commute_xm_of_commute_rootOp hδ1⟩
      · exact ⟨hrδ', commute_xm_of_commute_rootOp hδ2⟩
    have hall := forall_mem_a5Step_iterate hgen hnodes 3
    have hxz : x * z = z * x := congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1
      (hLC hy))
    have hx3 : x ^ 3 = 1 := by
      have h := pow_orderOf_eq_one y
      rw [hy3] at h
      exact congrArg Subtype.val h
    exact mem_rankOneTwE6_of_mem θ (mem_rankOneE6one_of_forall_commute hk9 hz' h2' hxz hx3
      fun γ hγ => (hall γ hγ).2)
  have hle : L ≤ rankOneTwE6 k θ := by
    intro y hy
    have hgen := closure_orderOf_three_eq_top_of_mulEquiv hF3 eL
    have hle' : Subgroup.closure {w : L | orderOf w = 3} ≤ (rankOneTwE6 k θ).subgroupOf L :=
      (Subgroup.closure_le _).2 fun w hw => Subgroup.mem_subgroupOf.2
        (hJ w.1 w.2 (by rw [Subgroup.orderOf_coe]; exact hw))
    exact Subgroup.mem_subgroupOf.1 (hle' (hgen ▸ Subgroup.mem_top (⟨y, hy⟩ : L)))
  have hcardJ := card_rankOneTwE6_le θ
  rw [card_eq_24 hfix3 (MulEquiv.refl _)] at hcardJ
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [card_eq_24 hF3 eL]
  exact hcardJ

theorem twistedE6ThreeCZ2
    : TwistedE6ThreeCZ2 := by
  intro z hz h2 L hLC hCL ⟨eL⟩ _
  have hk9 : Nat.card (GaloisField 3 (2 * 1)) = 9 := by
    rw [GaloisField.card 3 (2 * 1) (by norm_num)]
    norm_num
  have : Finite (GaloisField 3 (2 * 1)) := Nat.finite_of_card_ne_zero (by rw [hk9]; decide)
  have hF3 : Nat.card (GaloisField 3 1) = 3 := by
    rw [GaloisField.card 3 1 (by norm_num), pow_one]
  have : Finite (GaloisField 3 1) := Nat.finite_of_card_ne_zero (by rw [hF3]; decide)
  exact eq_rankOneTwE6_of_card_eq_nine (CFSG.LieType.Steinberg.Exceptional.frobQ 3 1) hk9
    (fun c => by rw [CFSG.LieType.Steinberg.Exceptional.frobQ_apply, pow_one]) hz h2 hLC hCL
    hF3 eL

variable (p f : ℕ) [Fact p.Prime]

theorem highestRootCZ_modelUniv_twistedE6_full
    (n : ℕ) (hp2 : p ≠ 2) (hf : 1 ≤ f) :
    HighestRootCZ (CFSG.ClassicalInvolution.Generic.modelUniv .twistedE6 n p f Fact.out).D
      (GaloisField p f) :=
  highestRootCZ_modelUniv_twistedE6 p f n hp2 hf fun _ => twistedE6ThreeCZ2

end CFSG.LieType.HighestRoot
