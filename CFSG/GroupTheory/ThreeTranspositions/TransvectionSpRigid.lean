module

public import CFSG.Fischer.Classification.Orthogonal2.SpModel
public import CFSG.GroupTheory.ThreeTranspositions.TransvectionSymplectic

public section

namespace CFSG.GroupTheory.ThreeTranspositions.TransvectionSpRigid

open CFSG.Fischer.Classification CFSG.Fischer.Classification.Orth2
open CFSG.GroupTheory.ThreeTranspositions.TransvectionSymplectic

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Tv

variable {V : Type*} [Group V]

theorem mul_comm_of_sq_eq_one (h2V : ∀ u : V, u * u = 1) (a b : V) : a * b = b * a := by
  have ha : a⁻¹ = a := inv_eq_of_mul_eq_one_left (h2V a)
  have hb : b⁻¹ = b := inv_eq_of_mul_eq_one_left (h2V b)
  have hab : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_left (h2V (a * b))
  rw [← hab, mul_inv_rev, ha, hb]

theorem tv_apply_center (h2V : ∀ u : V, u * u = 1) {τ : MulAut V} {c : V}
    (hc : ∀ u, τ u = u ∨ τ u = u * c) : τ c = c := by
  rcases hc c with h | h
  · exact h
  · rw [h2V] at h
    have hc1 : c = 1 := τ.injective (by rw [h, map_one])
    rw [hc1, map_one]

theorem tv_center_unique {τ : MulAut V} {c c' : V} (hc : ∀ u, τ u = u ∨ τ u = u * c)
    (hc' : ∀ u, τ u = u ∨ τ u = u * c') (hτ : τ ≠ 1) : c = c' := by
  obtain ⟨u, hu⟩ : ∃ u, τ u ≠ u := by
    by_contra hall
    push Not at hall
    exact hτ (MulEquiv.ext hall)
  rcases hc u with h1 | h1
  · exact absurd h1 hu
  rcases hc' u with h2 | h2
  · exact absurd h2 hu
  exact mul_left_cancel (h1.symm.trans h2)

theorem tv_conj {τ σ : MulAut V} {c : V} (hc : ∀ u, τ u = u ∨ τ u = u * c) :
    ∀ u, (σ * τ * σ⁻¹) u = u ∨ (σ * τ * σ⁻¹) u = u * σ c := by
  intro u
  rcases hc (σ⁻¹ u) with h | h
  · left
    rw [MulAut.mul_apply, MulAut.mul_apply, h, ← MulAut.mul_apply, mul_inv_cancel,
      MulAut.one_apply]
  · right
    rw [MulAut.mul_apply, MulAut.mul_apply, h, map_mul, ← MulAut.mul_apply, mul_inv_cancel,
      MulAut.one_apply]

theorem tv_commute_of_fix (h2V : ∀ u : V, u * u = 1) {τ τ' : MulAut V} {c c' : V}
    (hc : ∀ u, τ u = u ∨ τ u = u * c) (hc' : ∀ u, τ' u = u ∨ τ' u = u * c')
    (h1 : τ c' = c') (h2 : τ' c = c) : τ * τ' = τ' * τ := by
  have hcomm := mul_comm_of_sq_eq_one h2V
  refine MulEquiv.ext fun u => ?_
  change τ (τ' u) = τ' (τ u)
  rcases hc u with ha | ha <;> rcases hc' u with hb | hb
  · rw [hb, ha, hb]
  · rw [hb, map_mul, ha, h1, hb]
  · rw [hb, ha, map_mul, hb, h2]
  · rw [hb, map_mul, ha, h1, map_mul, hb, h2, mul_assoc, mul_assoc, hcomm c' c]

theorem tv_fix_of_commute (h2V : ∀ u : V, u * u = 1) {τ τ' : MulAut V} {c c' : V}
    (hc : ∀ u, τ u = u ∨ τ u = u * c) (hc' : ∀ u, τ' u = u ∨ τ' u = u * c')
    (hτ' : τ' ≠ 1) (hcomm : τ * τ' = τ' * τ) : τ c' = c' := by
  have hVc := mul_comm_of_sq_eq_one h2V
  by_contra hne
  have hτc' : τ c' = c' * c := (hc c').resolve_left hne
  obtain ⟨u, hu⟩ : ∃ u, τ' u ≠ u := by
    by_contra hall
    push Not at hall
    exact hτ' (MulEquiv.ext hall)
  have hτ'u : τ' u = u * c' := (hc' u).resolve_left hu
  have key : τ (τ' u) = τ' (τ u) := by
    rw [← MulAut.mul_apply, hcomm, MulAut.mul_apply]
  rw [hτ'u, map_mul, hτc'] at key
  apply hne
  rcases hc u with ha | ha
  · rw [ha, hτ'u] at key
    have h0 : c' * c = c' * 1 := by rw [mul_one]; exact mul_left_cancel key
    have hc1 : c = 1 := mul_left_cancel h0
    rw [hτc', hc1, mul_one]
  · rw [ha, map_mul, hτ'u] at key
    have e1 : u * c * (c' * c) = u * c' := by
      calc u * c * (c' * c) = u * (c * c) * c' := by rw [hVc c' c]; simp only [mul_assoc]
        _ = u * c' := by rw [h2V c, mul_one]
    have e2 : u * c' * 1 = u * c' * τ' c := by rw [mul_one]; exact e1.symm.trans key
    have hτ'c : τ' c = 1 := (mul_left_cancel e2).symm
    have hc1 : c = 1 := τ'.injective (by rw [hτ'c, map_one])
    rw [hτc', hc1, mul_one]

theorem tv_moves_of_not_commute (h2V : ∀ u : V, u * u = 1) {τ τ' : MulAut V} {c c' : V}
    (hc : ∀ u, τ u = u ∨ τ u = u * c) (hc' : ∀ u, τ' u = u ∨ τ' u = u * c')
    (hτ' : τ' ≠ 1) (hnc : τ * τ' ≠ τ' * τ) (h3 : (τ * τ') ^ 3 = 1) :
    τ c' ≠ c' := by
  intro h1
  rcases hc' c with h2 | h2
  · exact hnc (tv_commute_of_fix h2V hc hc' h1 h2)
  have hτc : τ c = c := tv_apply_center h2V hc
  have hτ'c' : τ' c' = c' := tv_apply_center h2V hc'
  have hc'1 : c' ≠ 1 := by
    intro h
    apply hτ'
    refine MulEquiv.ext fun u => ?_
    rcases hc' u with hu | hu
    · exact hu
    · rw [hu, h, mul_one]; rfl
  set ψ := τ * τ' with hψ
  have hψ_apply : ∀ x, ψ x = τ (τ' x) := fun x => rfl
  have hψc : ψ c = c * c' := by rw [hψ_apply, h2, map_mul, hτc, h1]
  have hψc' : ψ c' = c' := by rw [hψ_apply, hτ'c', h1]
  have hψcc' : ψ (c * c') = c := by rw [map_mul, hψc, hψc', mul_assoc, h2V, mul_one]
  have hcube : (ψ ^ 3) c = c * c' := by
    rw [pow_succ, pow_two, MulAut.mul_apply, MulAut.mul_apply, hψc, hψcc', hψc]
  rw [h3, MulAut.one_apply] at hcube
  exact hc'1 (mul_left_cancel (hcube.symm.trans (mul_one c).symm))

end Tv

section Group

variable {W K : Type} {V : Type*} [Group W] [Group K] [Group V]

theorem commute_of_pi_commute {π : W →* K} (hker : π.ker ≤ Subgroup.center W)
    (hodd : Odd (Nat.card π.ker)) {D : Set W} (hself : ∀ x ∈ D, x * x = 1)
    (h3 : ∀ x ∈ D, ∀ y ∈ D, orderOf (x * y) ∈ ({1, 2, 3} : Set ℕ))
    {e e' : W} (he : e ∈ D) (he' : e' ∈ D) (h : π e * π e' = π e' * π e) :
    e * e' = e' * e := by
  by_contra hne
  have h3' : orderOf (e * e') = 3 :=
    orderOf_mul_eq_three_of_not_commute (hself e he) (hself e' he') (h3 e he e' he') hne
  have hinv : ∀ x ∈ D, x⁻¹ = x := fun x hx => inv_eq_of_mul_eq_one_left (hself x hx)
  have hsq : (e * e') ^ 2 ∈ π.ker := by
    have hπ2 : ∀ x ∈ D, π x * π x = 1 := fun x hx => by rw [← map_mul, hself x hx, map_one]
    rw [MonoidHom.mem_ker, map_pow, map_mul, sq]
    calc π e * π e' * (π e * π e') = π e * (π e' * π e) * π e' := by group
      _ = π e * (π e * π e') * π e' := by rw [← h]
      _ = (π e * π e) * (π e' * π e') := by group
      _ = 1 := by rw [hπ2 e he, hπ2 e' he', one_mul]
  have hcube : (e * e') ^ 3 = 1 := by rw [← h3', pow_orderOf_eq_one]
  have hee' : e * e' ∈ π.ker := by
    have : e * e' = ((e * e') ^ 2)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← pow_succ', hcube]
    rw [this]
    exact inv_mem hsq
  have hπ : π e = π e' := by
    have h1 : π e * π e' = 1 := by rw [← map_mul]; exact hee'
    rw [eq_inv_of_mul_eq_one_left h1, ← map_inv, hinv e' he']
  have heq : e = e' := by
    by_contra hne'
    exact pi_ne_of_rho_eq he he' hne' hself hker hodd hπ
  rw [heq] at h3'
  rw [hself e' he', orderOf_one] at h3'
  exact absurd h3' (by norm_num)

theorem injOn_of_commutator_eq_top (ρ : W →* MulAut V) (π : W →* K)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center W)
    (hodd : Odd (Nat.card π.ker)) {D : Set W} (hself : ∀ x ∈ D, x * x = 1)
    (hK : Hyp K (π '' D)) (hperf : commutator K = ⊤) {d : W} (hd : d ∈ D) (hρd : ρ d ≠ 1) :
    Set.InjOn ρ D := by
  intro x hx y hy hxy
  by_contra hne
  have hπne : π x ≠ π y := pi_ne_of_rho_eq hx hy hne hself hker hodd
  have hmem : x * y ∈ ρ.ker := by
    rw [MonoidHom.mem_ker, map_mul, hxy, ← map_mul, hself y hy, map_one]
  have hπxy : π (x * y) ≠ 1 := by
    rw [map_mul]
    intro h
    apply hπne
    have hy2 : π y * π y = 1 := by rw [← map_mul, hself y hy, map_one]
    rw [eq_inv_of_mul_eq_one_left h, inv_eq_of_mul_eq_one_right hy2]
  have hNnormal : ((ρ.ker).map π).Normal :=
    Subgroup.Normal.map (MonoidHom.normal_ker ρ) π hπ
  have hNne : (ρ.ker).map π ≠ ⊥ := by
    intro hbot
    have h' : π (x * y) ∈ (⊥ : Subgroup K) := by
      rw [← hbot]
      exact Subgroup.mem_map_of_mem π hmem
    exact hπxy (by simpa using h')
  have hNK' : commutator K ≤ (ρ.ker).map π :=
    CFSG.Fischer.Classification.commutator_le_of_normal hK.center hK.simple hNne
  rw [hperf] at hNK'
  obtain ⟨k, hk, hkd⟩ := Subgroup.mem_map.mp (hNK' (Subgroup.mem_top (π d)))
  have hζ : k⁻¹ * d ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hkd, inv_mul_cancel]
  have hρdζ : ρ d = ρ (k⁻¹ * d) := by
    rw [map_mul, map_inv, MonoidHom.mem_ker.mp hk, inv_one, one_mul]
  have hord2 : orderOf (ρ d) = 2 := by
    apply orderOf_eq_prime
    · rw [sq, ← map_mul, hself d hd, map_one]
    · exact hρd
  have hdvd : orderOf (ρ d) ∣ Nat.card π.ker := by
    rw [hρdζ]
    exact (orderOf_map_dvd ρ (k⁻¹ * d)).trans (Subgroup.orderOf_dvd_natCard π.ker hζ)
  rw [hord2] at hdvd
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)

theorem center_injOn (h2V : ∀ u : V, u * u = 1) (ρ : W →* MulAut V) {D : Set W}
    (hself : ∀ x ∈ D, x * x = 1)
    (h3 : ∀ x ∈ D, ∀ y ∈ D, orderOf (x * y) ∈ ({1, 2, 3} : Set ℕ))
    (C : W → V) (hC : ∀ e ∈ D, ∀ u, ρ e u = u ∨ ρ e u = u * C e) (hne1 : ∀ e ∈ D, ρ e ≠ 1)
    (hinj : Set.InjOn ρ D)
    (hsep : ∀ e ∈ D, ∀ e' ∈ D, e ≠ e' → ∃ x ∈ D, x * e ≠ e * x ∧ x * e' = e' * x) :
    Set.InjOn C D := by
  let _ : CommGroup V := CommGroup.mk (mul_comm_of_sq_eq_one h2V)
  intro e he e' he' hCe
  by_contra hne
  obtain ⟨x, hx, hxe, hxe'⟩ := hsep e he e' he' hne
  have hρxe : ρ x * ρ e ≠ ρ e * ρ x := fun h =>
    hxe (commute_of_rho_commute (ρ := ρ) hx he (hself x hx) (hself e he) (h3 x hx e he) hinj h)
  have h3' : (ρ x * ρ e) ^ 3 = 1 := by
    rw [← map_mul, ← map_pow, ← orderOf_mul_eq_three_of_not_commute (hself x hx)
      (hself e he) (h3 x hx e he) hxe, pow_orderOf_eq_one, map_one]
  have hmove := tv_moves_of_not_commute h2V (hC x hx) (hC e he) (hne1 e he) hρxe h3'
  have hfix := tv_fix_of_commute h2V (hC x hx) (hC e' he') (hne1 e' he')
    (by rw [← map_mul, ← map_mul, hxe'])
  rw [hCe] at hmove
  exact hmove hfix

theorem eq_self_of_equivariant (h2V : ∀ u : V, u * u = 1) (ρ : W →* MulAut V) {D : Set W}
    (C : W → V) (hC : ∀ e ∈ D, ∀ u, ρ e u = u ∨ ρ e u = u * C e) (hne1 : ∀ e ∈ D, ρ e ≠ 1)
    (hCinj : Set.InjOn C D) (σ : MulAut V) (κ : W → W) (hκD : ∀ e ∈ D, κ e ∈ D)
    (hκ : ∀ e ∈ D, ρ (κ e) = σ * ρ e * σ⁻¹) {d : W} (hd : d ∈ D)
    (hσ : ∀ u, ρ d u = u → σ u = u) : ∀ e ∈ D, e * d = d * e → κ e = e := by
  intro e he hed
  have hfix : ρ d (C e) = C e :=
    tv_fix_of_commute h2V (hC d hd) (hC e he) (hne1 e he) (by rw [← map_mul, ← map_mul, hed])
  have hσC : σ (C e) = C e := hσ _ hfix
  have hcen : σ (C e) = C (κ e) := by
    refine tv_center_unique (τ := ρ (κ e)) ?_ (hC (κ e) (hκD e he)) (hne1 (κ e) (hκD e he))
    rw [hκ e he]
    exact tv_conj (hC e he)
  exact hCinj (hκD e he) he (by rw [← hcen, hσC])

end Group

section Model

variable {W K : Type} [Group W] [Group K] {m : ℕ}
  {b : LinearMap.BilinForm (ZMod 2) (Fin (2 * m) → ZMod 2)}

theorem exists_separating_of_model {π : W →* K} (hker : π.ker ≤ Subgroup.center W)
    (hodd : Odd (Nat.card π.ker)) {D : Set W} (hself : ∀ x ∈ D, x * x = 1)
    (h3 : ∀ x ∈ D, ∀ y ∈ D, orderOf (x * y) ∈ ({1, 2, 3} : Set ℕ))
    (halt : ∀ x, b x x = 0) (hnd : ∀ x, (∀ y, b x y = 0) → x = 0)
    (Φ : K ≃* TauCeti.BilinForm.isometryGroup b)
    (hΦ : ∀ g, g ∈ π '' D ↔ ∃ v, v ≠ 0 ∧ Φ g = spT (f := b) halt v) :
    ∀ e ∈ D, ∀ e' ∈ D, e ≠ e' → ∃ x ∈ D, x * e ≠ e * x ∧ x * e' = e' * x := by
  have hb : b.IsAlt := halt
  have hbn : b.Nondegenerate := nondegenerate_of_isAlt halt hnd
  intro e he e' he' hne
  have hπne : π e ≠ π e' :=
    pi_ne_of_rho_eq he he' hne hself hker hodd
  obtain ⟨v, hv, hev⟩ := (hΦ (π e)).mp ⟨e, he, rfl⟩
  obtain ⟨v', hv', hev'⟩ := (hΦ (π e')).mp ⟨e', he', rfl⟩
  have hvv' : v ≠ v' := fun h => hπne (Φ.injective (by rw [hev, hev', h]))
  obtain ⟨y, hy1, hy0⟩ := exists_apply_eq_one_eq_zero hb hbn hv hvv'
  have hy : y ≠ 0 := by
    intro h
    rw [h, LinearMap.map_zero₂] at hy1
    exact zero_ne_one hy1
  obtain ⟨x, hx, hxy⟩ := (hΦ (Φ.symm (spT hb y))).mpr ⟨y, hy, Φ.apply_symm_apply _⟩
  have hΦx : Φ (π x) = spT hb y := by rw [hxy, Φ.apply_symm_apply]
  refine ⟨x, hx, fun h => ?_, ?_⟩
  · have h' : Φ (π x) * Φ (π e) = Φ (π e) * Φ (π x) := by
      rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, h]
    rw [hΦx, hev, spT_mul_comm_iff hb hbn hy, hy1] at h'
    exact one_ne_zero h'
  · refine commute_of_pi_commute hker hodd hself h3 hx he' (Φ.injective ?_)
    rw [map_mul, map_mul, hΦx, hev']
    exact (spT_mul_comm_iff hb hbn hy).mpr hy0

end Model

end CFSG.GroupTheory.ThreeTranspositions.TransvectionSpRigid
