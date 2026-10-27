module

public import CFSG.GH74.GLS.IVK.Proofs2.Lemma15b
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma12l
public import CFSG.Permutation.AlternatingAutomorphism.Conjugation
public import CFSG.LocalAnalysis.ComponentInitial.FourGroupCommuting
public import CFSG.GH74.GLS.IVK.L2.Fixed14a
public import CFSG.GH74.GLS.IVK.L2.Lemma13f

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG.GH74.GLS.IVK CFSG.GorensteinWalter Equiv

section Common

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K]

theorem no_outer_of_inner_action
    (hF : L2Field F) (e : K ≃* L2 F) {u : MulAut K}
    (hu : u ∈ innDiagSub e) (hu' : u ∉ innAut K) (V : Subgroup K)
    (hV4 : Nat.card V = 4) (hVsq : ∀ v ∈ V, v * v = 1)
    (m₀ : K) (hact : ∀ v ∈ V, u v = m₀ * v * m₀⁻¹) : False := by
  have hconj := conj_injective_of_L2 e
  let U : Subgroup (MulAut K) := V.map (MulAut.conj : K →* MulAut K)
  have hUinn : U ≤ innAut K := by
    rintro _ ⟨k, -, rfl⟩
    exact ⟨k, rfl⟩
  have hUcard : Nat.card U = 4 := by
    rw [Subgroup.card_map_of_injective hconj, hV4]
  have hVcomm : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v := by
    intro v hv w hw
    have h1 : v * w * (v * w) = 1 := hVsq _ (V.mul_mem hv hw)
    have hv' : v⁻¹ = v := inv_eq_of_mul_eq_one_right (hVsq v hv)
    have hw' : w⁻¹ = w := inv_eq_of_mul_eq_one_right (hVsq w hw)
    have h2 : v * w = (v * w)⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
    rw [h2, mul_inv_rev, hv', hw']
  have hVel : CFSG.IsElementaryAbelian 2 V :=
    { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (hVcomm a a.2 b b.2)⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one (fun a => by
        apply Subtype.ext
        simpa [sq] using hVsq a a.2) }
  have hUel : CFSG.IsElementaryAbelian 2 U :=
    have := hVel
    isElementaryAbelian_of_mulEquiv
      (Subgroup.equivMapOfInjective V (MulAut.conj : K →* MulAut K) hconj).symm
  set c : MulAut K := (MulAut.conj m₀)⁻¹ * u with hc
  have hcv : ∀ v ∈ V, c v = v := by
    intro v hv
    rw [hc, MulAut.mul_apply, hact v hv, ← map_inv, MulAut.conj_apply]
    group
  have hcU : c ∈ centralizer (U : Set (MulAut K)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨v, hv, rfl⟩
    have h := mul_conj_mul_inv_eq_conj_apply c v
    rw [hcv v hv] at h
    exact (mul_inv_eq_iff_eq_mul.mp h).symm
  have hcD : c ∈ innDiagSub e :=
    (innDiagSub e).mul_mem ((innDiagSub e).inv_mem (innAut_le_innDiagSub e ⟨m₀, rfl⟩)) hu
  have hcmem : c ∈ U := by
    rw [← centralizer_four_inf_innDiagSub e hF U hUinn ⟨hUel, hUcard⟩]
    exact ⟨hcU, hcD⟩
  apply hu'
  have hu_eq : u = MulAut.conj m₀ * c := by rw [hc]; group
  rw [hu_eq]
  exact (innAut K).mul_mem ⟨m₀, rfl⟩ (hUinn hcmem)

end Common

section Restrict

variable {K : Type} [Group K] [Finite K]

@[expose] def restrictAut (u : MulAut K) (M : Subgroup K) (hM : ∀ m ∈ M, u m ∈ M) : MulAut M where
  toFun m := ⟨u m, hM m m.2⟩
  invFun m := ⟨u⁻¹ m, inv_apply_mem_of_apply_mem M u hM m m.2⟩
  left_inv m := by ext; simp
  right_inv m := by ext; simp
  map_mul' a b := by ext; simp

theorem restrictAut_coe (u : MulAut K) (M : Subgroup K) (hM : ∀ m ∈ M, u m ∈ M) (m : M) :
    ((restrictAut u M hM m : M) : K) = u m := rfl

@[expose] def transportAut {H : Type} [Group H] (u : MulAut K) (M : Subgroup K) (eM : M ≃* H)
    (hM : ∀ m ∈ M, u m ∈ M) : MulAut H :=
  eM.symm.trans ((restrictAut u M hM).trans eM)

theorem transportAut_apply {H : Type} [Group H] (u : MulAut K) (M : Subgroup K) (eM : M ≃* H)
    (hM : ∀ m ∈ M, u m ∈ M) (a : H) :
    transportAut u M eM hM a = eM (restrictAut u M hM (eM.symm a)) := rfl

theorem exists_inner_action_of_fixed {H : Type} [Group H] (u : MulAut K) (M : Subgroup K) (eM : M ≃* H)
    (hM : ∀ m ∈ M, u m ∈ M) {x : K} (hxM : x ∈ M) (hux : u x = x)
    (hinner : ∀ β : MulAut H, β (eM ⟨x, hxM⟩) = eM ⟨x, hxM⟩ → ∃ h : H, ∀ a, β a = h * a * h⁻¹) :
    ∃ m₀ ∈ M, ∀ m ∈ M, u m = m₀ * m * m₀⁻¹ := by
  have hα : restrictAut u M hM ⟨x, hxM⟩ = ⟨x, hxM⟩ :=
    Subtype.ext (by rw [restrictAut_coe]; exact hux)
  obtain ⟨h, hh⟩ := hinner (transportAut u M eM hM) (by
    rw [transportAut_apply, MulEquiv.symm_apply_apply, hα])
  refine ⟨(eM.symm h : K), (eM.symm h).2, fun m hm => ?_⟩
  have h1 := hh (eM ⟨m, hm⟩)
  rw [transportAut_apply, MulEquiv.symm_apply_apply] at h1
  have h2 : restrictAut u M hM ⟨m, hm⟩ = eM.symm h * ⟨m, hm⟩ * (eM.symm h)⁻¹ := by
    apply eM.injective
    rw [h1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  have h3 := congrArg Subtype.val h2
  rw [restrictAut_coe] at h3
  simpa using h3

omit [Finite K] in
theorem exists_four_of_equiv {H : Type} [Group H] (M : Subgroup K) (eM : M ≃* H) {a b : H}
    (ha : a * a = 1) (hb : b * b = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab' : a ≠ b)
    (hab : a * b = b * a) :
    ∃ V : Subgroup K, V ≤ M ∧ Nat.card V = 4 ∧ ∀ v ∈ V, v * v = 1 := by
  obtain ⟨V₀, hV₀, -, -, hV₀4⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.FourGroup.exists_kleinFour ha hb hab ha1 hb1 hab'
  let ι : H →* K := M.subtype.comp eM.symm.toMonoidHom
  have hι : Function.Injective ι := Subtype.val_injective.comp eM.symm.injective
  refine ⟨V₀.map ι, ?_, ?_, ?_⟩
  · rintro _ ⟨c, -, rfl⟩
    exact (eM.symm c).2
  · rw [Subgroup.card_map_of_injective hι, hV₀4]
  · rintro _ ⟨c, hc, rfl⟩
    have hcc : c * c = 1 := by
      rcases hV₀ c hc with rfl | rfl | rfl | rfl
      · exact one_mul 1
      · exact ha
      · exact hb
      · calc a * b * (a * b) = a * (b * a) * b := by group
          _ = a * (a * b) * b := by rw [hab]
          _ = 1 := by rw [← mul_assoc, ha, one_mul, hb]
    rw [← map_mul, hcc, map_one]

omit [Finite K] in
theorem orderOf_equiv_mk {H : Type} [Group H] (M : Subgroup K) (eM : M ≃* H) {x : K} (hxM : x ∈ M)
    {n : ℕ} (hx : orderOf x = n) : orderOf (eM ⟨x, hxM⟩) = n := by
  rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hx]

end Restrict

section A4

theorem perm4_commute_cases : ∀ g π : Perm (Fin 4), g ^ 3 = 1 → g ≠ 1 → π * g = g * π →
    π = 1 ∨ π = g ∨ π = g ^ 2 := by
  decide

theorem a4_aut_eq_conj_of_fixed (β : MulAut (alternatingGroup (Fin 4)))
    (x : alternatingGroup (Fin 4)) (hx : orderOf x = 3) (hβ : β x = x) :
    ∃ h : alternatingGroup (Fin 4), ∀ a, β a = h * a * h⁻¹ := by
  obtain ⟨π, hπ⟩ := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_four_bijective_conj.2 β
  have hπx : π * (x : Perm (Fin 4)) = (x : Perm (Fin 4)) * π := by
    have h0 : MulAut.conjNormal π x = x := by rw [hπ]; exact hβ
    have h1 := congrArg (fun a : alternatingGroup (Fin 4) => (a : Perm (Fin 4))) h0
    simp only [MulAut.conjNormal_apply] at h1
    rw [mul_inv_eq_iff_eq_mul] at h1
    exact h1
  have hx3 : (x : Perm (Fin 4)) ^ 3 = 1 := by
    have := pow_orderOf_eq_one x
    rw [hx] at this
    simpa using congrArg Subtype.val this
  have hx1 : (x : Perm (Fin 4)) ≠ 1 := by
    intro h
    have : x = 1 := Subtype.ext h
    rw [this, orderOf_one] at hx
    omega
  have key : ∃ i : ℕ, π = (x : Perm (Fin 4)) ^ i := by
    rcases perm4_commute_cases _ _ hx3 hx1 hπx with h | h | h
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa using h⟩
    · exact ⟨2, h⟩
  obtain ⟨i, hi⟩ := key
  refine ⟨x ^ i, fun a => ?_⟩
  rw [← hπ]
  apply Subtype.ext
  rw [MulAut.conjNormal_apply, hi]
  simp

theorem no_outer_normalizes_a4
    {F : Type} [Field F] [Finite F] (hF : L2Field F) {K : Type} [Group K] [Finite K]
    (e : K ≃* L2 F) {u : MulAut K}
    (hu : u ∈ innDiagSub e) (hu' : u ∉ innAut K)
    (M : Subgroup K) (eM : M ≃* alternatingGroup (Fin 4)) (hM : ∀ m ∈ M, u m ∈ M)
    {x : K} (hxM : x ∈ M) (hx : orderOf x = 3) (hux : u x = x) : False := by
  obtain ⟨m₀, -, hm₀⟩ := exists_inner_action_of_fixed u M eM hM hxM hux
    (fun β hβ => a4_aut_eq_conj_of_fixed β _ (orderOf_equiv_mk M eM hxM hx) hβ)
  obtain ⟨a, b, ha, hb, ha1, hb1, hab', hab⟩ := CFSG.Glauberman.Dickson.MaxCases.alternatingFour_klein
  obtain ⟨V, hVM, hV4, hVsq⟩ := exists_four_of_equiv M eM ha hb ha1 hb1 hab' hab
  exact no_outer_of_inner_action hF e hu hu' V hV4 hVsq m₀ (fun v hv => hm₀ v (hVM hv))

end A4

section A5

theorem eq_zpow_of_commute_of_transitive {α : Type*} {σ π : Perm α} (a₀ : α)
    (htr : ∀ b, ∃ k : ℤ, (σ ^ k) a₀ = b) (h : π * σ = σ * π) : ∃ j : ℤ, π = σ ^ j := by
  obtain ⟨j, hj⟩ := htr (π a₀)
  refine ⟨j, ?_⟩
  ext a
  obtain ⟨k, rfl⟩ := htr a
  have hc : ∀ k : ℤ, π * σ ^ k = σ ^ k * π := fun k =>
    (Commute.zpow_right (show Commute π σ from h) k).eq
  have h1 : π ((σ ^ k) a₀) = (σ ^ k) (π a₀) := by
    have := congrArg (fun f : Perm α => f a₀) (hc k)
    simpa using this
  have h2 : (σ ^ k) ((σ ^ j) a₀) = (σ ^ j) ((σ ^ k) a₀) := by
    have := congrArg (fun f : Perm α => f a₀) ((Commute.zpow_zpow_self σ k j).eq)
    simpa using this
  rw [h1, ← hj, h2]

theorem commute_five_cycle (σ π : Perm (Fin 5)) (hσ : orderOf σ = 5) (h : π * σ = σ * π) :
    ∃ j : ℤ, π = σ ^ j := by
  have hcyc : σ.IsCycle :=
    Equiv.Perm.isCycle_of_prime_order' (by rw [hσ]; exact Nat.prime_five) (by rw [hσ]; simp)
  have hsupp : σ.support = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [← hcyc.orderOf, hσ]
    simp
  have hmv : ∀ b, σ b ≠ b := fun b => by
    have : b ∈ σ.support := by rw [hsupp]; exact Finset.mem_univ b
    exact Equiv.Perm.mem_support.mp this
  exact eq_zpow_of_commute_of_transitive 0 (fun b => hcyc.exists_zpow_eq (hmv 0) (hmv b)) h

theorem a5_aut_eq_conj_of_fixed (β : MulAut (alternatingGroup (Fin 5)))
    (x : alternatingGroup (Fin 5)) (hx : orderOf x = 5) (hβ : β x = x) :
    ∃ h : alternatingGroup (Fin 5), ∀ a, β a = h * a * h⁻¹ := by
  obtain ⟨π, hπ⟩ :=
    CFSG.AlternatingAutomorphism.exists_perm_conj_of_degree_eq_five_or_seven_le (Or.inl rfl) β
  have hπx : π * (x : Perm (Fin 5)) = (x : Perm (Fin 5)) * π := by
    have h1 := hπ x
    rw [hβ] at h1
    calc π * (x : Perm (Fin 5)) = (π * x * π⁻¹) * π := by group
      _ = x * π := by rw [← h1]
  obtain ⟨j, hj⟩ := commute_five_cycle (x : Perm (Fin 5)) π (by rwa [Subgroup.orderOf_coe]) hπx
  refine ⟨x ^ j, fun a => ?_⟩
  apply Subtype.ext
  rw [hπ a, hj]
  simp

theorem no_outer_normalizes_a5
    {F : Type} [Field F] [Finite F] (hF : L2Field F) {K : Type} [Group K] [Finite K]
    (e : K ≃* L2 F) {u : MulAut K}
    (hu : u ∈ innDiagSub e) (hu' : u ∉ innAut K)
    (M : Subgroup K) (eM : M ≃* alternatingGroup (Fin 5)) (hM : ∀ m ∈ M, u m ∈ M)
    {x : K} (hxM : x ∈ M) (hx : orderOf x = 5) (hux : u x = x) : False := by
  obtain ⟨m₀, -, hm₀⟩ := exists_inner_action_of_fixed u M eM hM hxM hux
    (fun β hβ => a5_aut_eq_conj_of_fixed β _ (orderOf_equiv_mk M eM hxM hx) hβ)
  obtain ⟨a, b, ha, hb, ha1, hb1, hab', hab⟩ := CFSG.Glauberman.Dickson.MaxCases.alternatingFive_klein
  obtain ⟨V, hVM, hV4, hVsq⟩ := exists_four_of_equiv M eM ha hb ha1 hb1 hab' hab
  exact no_outer_of_inner_action hF e hu hu' V hV4 hVsq m₀ (fun v hv => hm₀ v (hVM hv))

end A5

section S4

theorem perm4_alt_sq : ∀ a : Perm (Fin 4), Perm.sign a = 1 → ∃ c : Perm (Fin 4), c * c = a := by
  decide

theorem perm4_order_three_alt : ∀ g : Perm (Fin 4), g ^ 3 = 1 → Perm.sign g = 1 := by
  decide

theorem perm4_aut_mem_alternatingGroup (β : MulAut (Perm (Fin 4))) {a : Perm (Fin 4)}
    (ha : a ∈ alternatingGroup (Fin 4)) : β a ∈ alternatingGroup (Fin 4) := by
  obtain ⟨c, rfl⟩ := perm4_alt_sq a (Perm.mem_alternatingGroup.mp ha)
  rw [map_mul, Perm.mem_alternatingGroup, Perm.sign_mul]
  exact Int.units_mul_self _

theorem no_outer_normalizes_s4
    {F : Type} [Field F] [Finite F] (hF : L2Field F) {K : Type} [Group K] [Finite K]
    (e : K ≃* L2 F) {u : MulAut K}
    (hu : u ∈ innDiagSub e) (hu' : u ∉ innAut K)
    (M : Subgroup K) (eM : M ≃* Perm (Fin 4)) (hM : ∀ m ∈ M, u m ∈ M)
    {x : K} (hxM : x ∈ M) (hx : orderOf x = 3) (hux : u x = x) : False := by
  let ι : Perm (Fin 4) →* K := M.subtype.comp eM.symm.toMonoidHom
  have hι : Function.Injective ι := Subtype.val_injective.comp eM.symm.injective
  let M₀ : Subgroup K := (alternatingGroup (Fin 4)).map ι
  let eM₀ : M₀ ≃* alternatingGroup (Fin 4) :=
    (Subgroup.equivMapOfInjective (alternatingGroup (Fin 4)) ι hι).symm
  have hιβ : ∀ a : Perm (Fin 4), ι (transportAut u M eM hM a) = u (ι a) := by
    intro a
    simp only [ι, transportAut_apply, MonoidHom.comp_apply, Subgroup.coe_subtype,
      MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply, restrictAut_coe]
  have hM₀ : ∀ m ∈ M₀, u m ∈ M₀ := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← hιβ]
    exact ⟨_, perm4_aut_mem_alternatingGroup _ ha, rfl⟩
  have hxM₀ : x ∈ M₀ := by
    refine ⟨eM ⟨x, hxM⟩, ?_, by simp [ι]⟩
    rw [SetLike.mem_coe, Perm.mem_alternatingGroup]
    apply perm4_order_three_alt
    have := pow_orderOf_eq_one (eM ⟨x, hxM⟩)
    rwa [orderOf_equiv_mk M eM hxM hx] at this
  exact no_outer_normalizes_a4 hF e hu hu' M₀ eM₀ hM₀ hxM₀ hx hux

end S4

end CFSG.GH74.GLS.IVK.Proofs2
