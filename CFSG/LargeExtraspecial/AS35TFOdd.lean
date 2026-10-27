module

public import CFSG.LargeExtraspecial.AS35TPbar

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

namespace Setting

namespace AS35T

theorem eq_one_of_pow_odd_of_pow_two_pow {H : Type*} [Group H] {a : H} {m b : ℕ} (hm : Odd m)
    (h1 : a ^ m = 1) (h2 : a ^ 2 ^ b = 1) : a = 1 := by
  have hc : Nat.Coprime m (2 ^ b) := (Nat.coprime_two_right.mpr hm).pow_right b
  have hd : orderOf a ∣ Nat.gcd m (2 ^ b) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2)
  rw [hc, Nat.dvd_one, orderOf_eq_one_iff] at hd
  exact hd

theorem commute_of_pow_odd_of_comm_pow_two {H : Type*} [Group H] {a w : H} {m b : ℕ}
    (hm : Odd m) (ha : a ^ m = 1)
    (hc : a * (a * w * a⁻¹ * w⁻¹) = a * w * a⁻¹ * w⁻¹ * a)
    (h2 : (a * w * a⁻¹ * w⁻¹) ^ 2 ^ b = 1) : a * w = w * a := by
  set c := a * w * a⁻¹ * w⁻¹ with hcdef
  have hcomm : Commute a c := hc
  have hj : ∀ j : ℕ, a ^ j * w * (a ^ j)⁻¹ = c ^ j * w := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have h3 : a * c ^ j * a⁻¹ = c ^ j := by
        rw [(hcomm.pow_right j).eq]
        group
      have h4 : a * w * a⁻¹ = c * w := by rw [hcdef]; group
      calc a ^ (j + 1) * w * (a ^ (j + 1))⁻¹ = a * (a ^ j * w * (a ^ j)⁻¹) * a⁻¹ := by
            rw [pow_succ']
            group
        _ = (a * c ^ j * a⁻¹) * (a * w * a⁻¹) := by rw [ih]; group
        _ = c ^ (j + 1) * w := by rw [h3, h4, pow_succ]; group
  have h5 := hj m
  rw [ha, one_mul, inv_one, mul_one] at h5
  have h6 : c ^ m = 1 := by
    have := congrArg (· * w⁻¹) h5
    simpa using this.symm
  have h7 := AS35T.eq_one_of_pow_odd_of_pow_two_pow hm h6 h2
  calc a * w = c * (w * a) := by rw [hcdef]; group
    _ = w * a := by rw [h7, one_mul]

theorem commSpace_inf_fixSpace_of_pow_odd {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {σ : V ≃ₗ[ZMod 2] V} {m : ℕ} (hm : Odd m) (hσ : σ ^ m = 1) :
    commSpace σ ⊓ fixSpace σ = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  obtain ⟨hvc, hvf⟩ := Submodule.mem_inf.mp hv
  obtain ⟨w, rfl⟩ := mem_commSpace.mp hvc
  rw [mem_fixSpace] at hvf
  have hj : ∀ j : ℕ, (σ ^ j) w = w + j • (σ w - w) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ', LinearEquiv.mul_apply, ih, map_add, map_nsmul, hvf, succ_nsmul]
      abel
  have h1 := hj m
  rw [hσ, LinearEquiv.coe_one, id, left_eq_add] at h1
  obtain ⟨r, rfl⟩ := hm
  have e : (2 * r + 1) • (σ w - w) = σ w - w := by
    rw [succ_nsmul, mul_nsmul, two_nsmul, ZModModule.add_self]
    simp
  rw [e] at h1
  rw [Submodule.mem_bot]
  exact h1

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem eq_one_of_odd_of_commute_pbar (hS : S.SixHyp) {g : G} (ht : g * S.z * g⁻¹ ∈ S.DSet)
    (htM : g * S.z * g⁻¹ ∈ S.M) {σ : S.O} (hσM : σ ∈ S.Mbar)
    (hσt : σ * S.ρ ⟨_, htM⟩ = S.ρ ⟨_, htM⟩ * σ) {m : ℕ} (hm : Odd m) (hσm : σ ^ m = 1)
    (hσP : ∀ p ∈ ((S.Qa g ⊓ S.M).subgroupOf S.M).map S.ρ, σ * p = p * σ)
    (hfix : ∀ v ∈ commSpace ((S.ρ ⟨_, htM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt),
      (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) : σ = 1 := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  set t := g * S.z * g⁻¹ with htdef
  obtain ⟨⟨x₀', hx₀'⟩, rfl⟩ := hσM
  obtain ⟨x₀, hx₀M, hx₀t, hx₀ρ⟩ := S.exists_commute_rho_eq_J hS ht htM hx₀' hσt
  rw [← hx₀ρ] at hσm hσP hfix ⊢
  have hm1 : (⟨x₀, hx₀M⟩ : S.M) ^ m ∈ S.Q := by
    apply S.mem_Q_of_ρ_eq_one
    rw [map_pow, hσm]
  obtain ⟨a, ha⟩ := S.extraspecial.1 ⟨_, hm1⟩
  have ha' : ((⟨x₀, hx₀M⟩ : S.M) ^ 2 ^ a) ^ m = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]
    exact congrArg (fun y : S.Q => (y : S.M)) ha
  set xM : S.M := (⟨x₀, hx₀M⟩ : S.M) ^ 2 ^ a with hxM
  set x : G := (xM : G) with hx
  have hxt : x * t = t * x := by
    rw [hx, hxM, SubmonoidClass.coe_pow]
    exact ((Commute.pow_left hx₀t) _).eq
  have hxm : x ^ m = 1 := by
    rw [hx, ← SubmonoidClass.coe_pow, ha']
    rfl
  suffices hx1 : x = 1 by
    have h1 : S.ρ xM = 1 := by
      rw [show xM = 1 from Subtype.ext hx1, map_one]
    rw [hxM, map_pow] at h1
    exact AS35T.eq_one_of_pow_odd_of_pow_two_pow hm hσm h1
  have hρx : ∀ p ∈ ((S.Qa g ⊓ S.M).subgroupOf S.M).map S.ρ, S.ρ xM * p = p * S.ρ xM := by
    intro p hp
    rw [hxM, map_pow]
    exact ((Commute.pow_left (hσP p hp)) _).eq
  have hfixx : ∀ v ∈ commSpace (S.rhoL htM), S.rhoL xM.2 v = v := by
    intro v hv
    change ((S.ρ xM : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v
    rw [hxM, map_pow, SubgroupClass.coe_pow]
    induction 2 ^ a with
    | zero => rfl
    | succ j ih => rw [pow_succ, LinearEquiv.mul_apply, hfix v hv, ih]
  have hxQt : ∀ y ∈ S.Qa g, x * y * x⁻¹ ∈ S.Qa g := fun y hy =>
    S.conj_mem_Qa_of_commute_asc hxt hy
  have hxw : ∀ w ∈ S.QG ⊓ S.Qa g, x * w * x⁻¹ = w :=
    fun w hw => AS35T.commute_of_mem_inf_Qa_of_fix hS ht htM xM.2 hxQt hfixx hw
  have hxP : ∀ w ∈ S.Qa g ⊓ S.M, x * w = w * x := by
    intro w hw
    obtain ⟨hwQt, hwM⟩ := mem_inf.mp hw
    have hcQ : x * w * x⁻¹ * w⁻¹ ∈ S.QG := by
      have e : S.ρ (xM * ⟨w, hwM⟩ * xM⁻¹ * ⟨w, hwM⟩⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv,
          hρx _ ((AS35T.mem_pbar_iff S).mpr ⟨⟨w, hwM⟩, hwQt, rfl⟩)]
        group
      exact (S.ρ_eq_one_iff _).mp e
    have hcQt : x * w * x⁻¹ * w⁻¹ ∈ S.Qa g :=
      (S.Qa g).mul_mem (hxQt w hwQt) ((S.Qa g).inv_mem hwQt)
    have hc : x * w * x⁻¹ * w⁻¹ ∈ S.QG ⊓ S.Qa g := mem_inf.mpr ⟨hcQ, hcQt⟩
    refine AS35T.commute_of_pow_odd_of_comm_pow_two (b := 1) hm hxm ?_ ?_
    · have h1 := hxw _ hc
      calc x * (x * w * x⁻¹ * w⁻¹) = x * (x * w * x⁻¹ * w⁻¹) * x⁻¹ * x := by group
        _ = x * w * x⁻¹ * w⁻¹ * x := by rw [h1]
    · rw [pow_one]
      exact AS35T.sq_eq_one_of_mem_inf_Qa hS ht hc
  obtain ⟨k, hk₁, hk₂⟩ := S.exists_swap_J hS ht rfl
  obtain ⟨hi₁, hi₂⟩ := AS35T.swap_inv hk₁ hk₂
  have hyM : k⁻¹ * x * k ∈ S.M := by
    have h1 := AS35T.conj_mem_M_of_commute_swap hi₂ hxt
    rwa [inv_inv] at h1
  have hyc : ∀ u ∈ S.QG ⊓ centralizer ({t} : Set G), (k⁻¹ * x * k) * u * (k⁻¹ * x * k)⁻¹ = u := by
    intro u hu
    have h1 := hxP _ (AS35T.conj_mem_Qa_inf_M_swap hk₁ hk₂ hu)
    calc (k⁻¹ * x * k) * u * (k⁻¹ * x * k)⁻¹ = k⁻¹ * (x * (k * u * k⁻¹)) * x⁻¹ * k := by group
      _ = k⁻¹ * ((k * u * k⁻¹) * x) * x⁻¹ * k := by rw [h1]
      _ = u := by group
  have hK := (S.fiveOne_two hS.sixFour hS.weak ht htM).2.2
  have hfixy : fixSpace (S.rhoL htM) ≤ fixSpace (S.rhoL hyM) := by
    intro v hv
    rw [← hK] at hv
    obtain ⟨u, hu, huQ, rfl⟩ := S.mem_clSub_iff.mp hv
    rw [mem_fixSpace, S.rhoL_cl hyM huQ, hyc u hu]
  have hym : S.rhoL hyM ^ m = 1 := by
    have e : (⟨k⁻¹ * x * k, hyM⟩ : S.M) ^ m = 1 := by
      refine Subtype.ext ?_
      rw [SubmonoidClass.coe_pow]
      change (k⁻¹ * x * k) ^ m = 1
      rw [show k⁻¹ * x * k = k⁻¹ * x * k⁻¹⁻¹ by rw [inv_inv], conj_pow, hxm]
      group
    change ((S.ρ ⟨k⁻¹ * x * k, hyM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ^ m = 1
    rw [← SubgroupClass.coe_pow, ← map_pow, e, map_one]
    rfl
  have hcy : commSpace (S.rhoL hyM) ≤ fixSpace (S.rhoL hyM) := by
    have htt := S.mul_self_of_isConj (S.isConj_of_mem_ESet ht.1)
    rw [← S.orthogonal_fixSpace_of_isometry (S.rhoL_mem hyM)]
    calc LinearMap.BilinForm.orthogonal S.q.polarBilin (fixSpace (S.rhoL hyM)) ≤
          LinearMap.BilinForm.orthogonal S.q.polarBilin (fixSpace (S.rhoL htM)) :=
          LinearMap.BilinForm.orthogonal_le hfixy
      _ = commSpace (S.rhoL htM) := S.orthogonal_fixSpace_of_isometry (S.rhoL_mem htM)
      _ ≤ fixSpace (S.rhoL htM) := commSpace_le_fixSpace (S.rhoL_mul_self htM htt)
      _ ≤ fixSpace (S.rhoL hyM) := hfixy
  have hy1 : S.rhoL hyM = 1 := by
    have h1 := AS35T.commSpace_inf_fixSpace_of_pow_odd hm hym
    rw [inf_of_le_left hcy] at h1
    refine LinearEquiv.ext fun v => ?_
    have h2 := sub_mem_commSpace (S.rhoL hyM) v
    rw [h1, Submodule.mem_bot, sub_eq_zero] at h2
    exact h2
  have hyQ : k⁻¹ * x * k ∈ S.QG := by
    refine (S.ρ_eq_one_iff ⟨_, hyM⟩).mp (Subtype.ext ?_)
    exact hy1
  have hy1' : k⁻¹ * x * k = 1 := by
    obtain ⟨c, hc⟩ := S.isPGroup_QG ⟨_, hyQ⟩
    refine AS35T.eq_one_of_pow_odd_of_pow_two_pow (b := c) hm ?_ (congrArg Subtype.val hc)
    rw [show k⁻¹ * x * k = k⁻¹ * x * k⁻¹⁻¹ by rw [inv_inv], conj_pow, hxm]
    group
  calc x = k * (k⁻¹ * x * k) * k⁻¹ := by group
    _ = 1 := by rw [hy1']; group

end AS35T

end Setting

end CFSG.LargeExtraspecial
