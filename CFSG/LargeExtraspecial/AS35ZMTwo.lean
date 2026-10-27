module

public import CFSG.LargeExtraspecial.AS35ZMData
public import CFSG.LargeExtraspecial.AS35ZMOrth

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module CFSG.RankThree.OrthogonalInvolutions

namespace Setting

variable {G : Type} [Group G] [Finite G] (S : Setting G)

theorem typeA_of_mem_DbarAsc_ZM (hS : S.SixHyp) {f : S.O} (hf : f ∈ S.DbarAsc) :
    IsTypeA S.q (f : S.Qt ≃ₗ[ZMod 2] S.Qt) 2 := by
  obtain ⟨s, hs, hsM, rfl⟩ := hf
  exact S.rhoL_typeA_ZM hS hs hsM

theorem exists_pow_two_eq_one_ZM {R : Subgroup S.O} (hR2 : IsPGroup 2 R) {u : S.O}
    (hu : u ∈ R) : ∃ n : ℕ, (u : S.Qt ≃ₗ[ZMod 2] S.Qt) ^ (2 ^ n) = 1 := by
  obtain ⟨n, hn⟩ := hR2 ⟨u, hu⟩
  refine ⟨n, ?_⟩
  have := congrArg (fun w : R => ((w : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) hn
  simpa only [Subgroup.coe_pow, OneMemClass.coe_one] using this

theorem orderOf_ne_three_ZM {R : Subgroup S.O} (hR2 : IsPGroup 2 R) {u : S.O} (hu : u ∈ R) :
    orderOf u ≠ 3 := by
  intro h3
  obtain ⟨n, hn⟩ := hR2 ⟨u, hu⟩
  have h1 : u ^ (2 ^ n) = 1 := by
    have := congrArg Subtype.val hn
    simpa only [Subgroup.coe_pow, OneMemClass.coe_one] using this
  have h2 := orderOf_dvd_of_pow_eq_one h1
  rw [h3] at h2
  exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h2) (by norm_num)

theorem orderOf_conj_ZM {X : Type*} [Group X] (a b : X) : orderOf (a * b * a⁻¹) = orderOf b := by
  have := orderOf_injective (MulAut.conj a).toMonoidHom (MulAut.conj a).injective b
  simpa [MulAut.conj_apply] using this

theorem mul_self_of_mem_DbarAsc_ZM {d : S.O} (hd : d ∈ S.DbarAsc) : d * d = 1 := by
  obtain ⟨t, ht, htM, rfl⟩ := hd
  exact S.ρ_mul_self_eq_one htM (S.mul_self_of_isConj (S.isConj_of_mem_ESet ht.1))

theorem mem_Mbar_of_mem_DbarAsc_ZM {f : S.O} (hf : f ∈ S.DbarAsc) : f ∈ S.Mbar := by
  obtain ⟨s, -, hsM, rfl⟩ := hf
  exact ⟨⟨s, hsM⟩, rfl⟩

theorem orderOf_mul_eq_three_ZM (h65 : S.SixFiveConcl) {a b : S.O} (ha : a ∈ S.DbarAsc)
    (hb : b ∈ S.DbarAsc) (hab : a * b ≠ b * a) : orderOf (a * b) = 3 := by
  rcases h65.three a ha b hb with h | h | h
  · exact absurd (AS35J.commute_of_orderOf_mul_le_two (S.mul_self_of_mem_DbarAsc_ZM ha)
      (S.mul_self_of_mem_DbarAsc_ZM hb) (Or.inl h)) hab
  · exact absurd (AS35J.commute_of_orderOf_mul_le_two (S.mul_self_of_mem_DbarAsc_ZM ha)
      (S.mul_self_of_mem_DbarAsc_ZM hb) (Or.inr h)) hab
  · exact h

section Pair

variable (hS : S.SixHyp) (h65 : S.SixFiveConcl) {r t : G} (hr : r ∈ S.DSet) (ht : t ∈ S.DSet)
  (hrM : r ∈ S.M) (htM : t ∈ S.M) (h3 : orderOf (r * t) = 3)

omit hS h65 in
include hr ht h3 in
theorem rho_not_commute_ZM : S.ρ ⟨r, hrM⟩ * S.ρ ⟨t, htM⟩ ≠ S.ρ ⟨t, htM⟩ * S.ρ ⟨r, hrM⟩ := by
  intro h
  have hrr := S.rhoL_mul_self hrM (S.mul_self_of_isConj (S.isConj_of_mem_ESet hr.1))
  have htt := S.rhoL_mul_self htM (S.mul_self_of_isConj (S.isConj_of_mem_ESet ht.1))
  have hc : S.rhoL hrM * S.rhoL htM = S.rhoL htM * S.rhoL hrM :=
    congrArg (fun w : S.O => (w : S.Qt ≃ₗ[ZMod 2] S.Qt)) h
  have h2 : (S.rhoL hrM * S.rhoL htM) ^ 2 = 1 := by
    rw [sq, mul_assoc, ← mul_assoc (S.rhoL htM), ← hc, mul_assoc, htt, mul_one, hrr]
  have hd := orderOf_dvd_of_pow_eq_one h2
  rw [S.orderOf_rhoL_mul_ZM hrM htM h3] at hd
  exact absurd hd (by norm_num)

include hS h65 hr ht h3 in
theorem Dx_facts_ZM {f : S.O} (hf : f ∈ S.DbarAsc) (hfa : f * S.ρ ⟨r, hrM⟩ = S.ρ ⟨r, hrM⟩ * f)
    (hfb : f * S.ρ ⟨t, htM⟩ = S.ρ ⟨t, htM⟩ * f) :
    (∀ w ∈ commSpace (S.rhoL hrM * S.rhoL htM), (f : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w) ∧
      commSpace (f : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤ fixSpace (S.rhoL hrM * S.rhoL htM) ∧
      ∀ c ∈ fixSpace (S.rhoL hrM * S.rhoL htM),
        (f : S.Qt ≃ₗ[ZMod 2] S.Qt) c ∈ fixSpace (S.rhoL hrM * S.rhoL htM) := by
  have hnc := S.rho_not_commute_ZM hr ht hrM htM h3
  have hfa_ne : f ≠ S.ρ ⟨r, hrM⟩ := by
    rintro rfl
    exact hnc hfb
  have hfb_ne : f ≠ S.ρ ⟨t, htM⟩ := by
    rintro rfl
    exact hnc hfa.symm
  have hdis_a := h65.disjoint f hf _ (S.ρ_mem_DbarAsc hr hrM) hfa hfa_ne
  have hdis_b := h65.disjoint f hf _ (S.ρ_mem_DbarAsc ht htM) hfb hfb_ne
  have hfaL : (f : S.Qt ≃ₗ[ZMod 2] S.Qt) * S.rhoL hrM = S.rhoL hrM * f :=
    congrArg (fun w : S.O => (w : S.Qt ≃ₗ[ZMod 2] S.Qt)) hfa
  have hfbL : (f : S.Qt ≃ₗ[ZMod 2] S.Qt) * S.rhoL htM = S.rhoL htM * f :=
    congrArg (fun w : S.O => (w : S.Qt ≃ₗ[ZMod 2] S.Qt)) hfb
  obtain ⟨-, hW, -, -, hC⟩ := S.commSpace_rt_ZM hS hr ht hrM htM h3
  refine ⟨fun w hw => ?_, ?_, fun c hc => ?_⟩
  · have h1 := S.commSpace_le_fixSpace_of_commute_disjoint hfaL hdis_a
    have h2 := S.commSpace_le_fixSpace_of_commute_disjoint hfbL hdis_b
    rw [hW] at hw
    exact (mem_fixSpace).1 ((sup_le h1 h2) hw)
  · have hda' : commSpace (S.rhoL hrM) ⊓ commSpace (f : S.Qt ≃ₗ[ZMod 2] S.Qt) = ⊥ := by
      rw [inf_comm]
      exact hdis_a
    have hdb' : commSpace (S.rhoL htM) ⊓ commSpace (f : S.Qt ≃ₗ[ZMod 2] S.Qt) = ⊥ := by
      rw [inf_comm]
      exact hdis_b
    rw [hC]
    exact le_inf (S.commSpace_le_fixSpace_of_commute_disjoint hfaL.symm hda')
      (S.commSpace_le_fixSpace_of_commute_disjoint hfbL.symm hdb')
  · rw [mem_fixSpace] at hc ⊢
    rw [LinearEquiv.mul_apply, ← LinearEquiv.mul_apply (S.rhoL htM), ← hfbL,
      LinearEquiv.mul_apply, ← LinearEquiv.mul_apply (S.rhoL hrM), ← hfaL,
      LinearEquiv.mul_apply, ← LinearEquiv.mul_apply (S.rhoL hrM), hc]

include hS hr ht h3 in
theorem rt_preserve_ZM :
    (∀ w ∈ commSpace (S.rhoL hrM * S.rhoL htM), S.rhoL hrM w ∈
      commSpace (S.rhoL hrM * S.rhoL htM)) ∧
    (∀ w ∈ commSpace (S.rhoL hrM * S.rhoL htM), S.rhoL htM w ∈
      commSpace (S.rhoL hrM * S.rhoL htM)) ∧
    (∀ c ∈ fixSpace (S.rhoL hrM * S.rhoL htM), S.rhoL hrM c = c) ∧
    (∀ c ∈ fixSpace (S.rhoL hrM * S.rhoL htM), S.rhoL htM c = c) := by
  have ha := (S.rhoL_typeA_ZM hS hr hrM).2.2.1
  have haa : ∀ v, S.rhoL hrM (S.rhoL hrM v) = v := fun v => by
    rw [← LinearEquiv.mul_apply, ha]; rfl
  have hbr := AS35ZM.braid_of_pow_three ha (S.rhoL_typeA_ZM hS ht htM).2.2.1
    (S.rhoL_mul_pow_three_ZM hrM htM h3)
  have hag : ∀ v, (S.rhoL hrM * S.rhoL htM) (S.rhoL hrM v) =
      S.rhoL hrM ((S.rhoL hrM * S.rhoL htM) ((S.rhoL hrM * S.rhoL htM) v)) := by
    intro v
    simp only [LinearEquiv.mul_apply]
    have e := congrArg (fun f : S.Qt ≃ₗ[ZMod 2] S.Qt => f v) hbr
    simp only [LinearEquiv.mul_apply] at e
    rw [e, haa]
  have hC := (S.commSpace_rt_ZM hS hr ht hrM htM h3).2.2.2.2
  have haW : ∀ w ∈ commSpace (S.rhoL hrM * S.rhoL htM), S.rhoL hrM w ∈
      commSpace (S.rhoL hrM * S.rhoL htM) := fun w hw => AS35ZM.a_commSpace_mem haa hag hw
  refine ⟨haW, fun w hw => ?_, fun c hc => ?_, fun c hc => ?_⟩
  · have e : S.rhoL htM w = S.rhoL hrM ((S.rhoL hrM * S.rhoL htM) w) := by
      rw [LinearEquiv.mul_apply, haa]
    rw [e]
    exact haW _ (AS35ZM.commSpace_apply_mem hw)
  · rw [hC] at hc
    exact (mem_fixSpace).1 (Submodule.mem_inf.1 hc).1
  · rw [hC] at hc
    exact (mem_fixSpace).1 (Submodule.mem_inf.1 hc).2

section Linear

variable {J : S.Qt ≃ₗ[ZMod 2] S.Qt} (hJ : ∀ v, J (J v) + J v + v = 0)
  (hJD : ∀ a ∈ S.DbarAsc, ∀ v, (a : S.Qt ≃ₗ[ZMod 2] S.Qt) (J v) = J ((a : S.Qt ≃ₗ[ZMod 2] S.Qt) v))

include hS hr ht h3 hJ hJD in
theorem linear_facts_ZM {u : S.O} {n : ℕ} (hn : (u : S.Qt ≃ₗ[ZMod 2] S.Qt) ^ (2 ^ n) = 1)
    (huJ : ∀ v, (u : S.Qt ≃ₗ[ZMod 2] S.Qt) (J v) = J ((u : S.Qt ≃ₗ[ZMod 2] S.Qt) v))
    (hux : ∀ v, (u : S.Qt ≃ₗ[ZMod 2] S.Qt) ((S.rhoL hrM * S.rhoL htM) v) =
      (S.rhoL hrM * S.rhoL htM) ((u : S.Qt ≃ₗ[ZMod 2] S.Qt) v)) :
    (∀ w ∈ commSpace (S.rhoL hrM * S.rhoL htM), (u : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w) ∧
      u * S.ρ ⟨r, hrM⟩ = S.ρ ⟨r, hrM⟩ * u ∧ u * S.ρ ⟨t, htM⟩ = S.ρ ⟨t, htM⟩ * u := by
  have haJ : ∀ v, S.rhoL hrM (J v) = J (S.rhoL hrM v) := hJD _ (S.ρ_mem_DbarAsc hr hrM)
  have hbJ : ∀ v, S.rhoL htM (J v) = J (S.rhoL htM v) := hJD _ (S.ρ_mem_DbarAsc ht htM)
  have hW := S.two_elt_on_commSpace_ZM hS hr ht hrM htM h3 hJ haJ hbJ huJ hux hn
  obtain ⟨haW, hbW, haC, hbC⟩ := S.rt_preserve_ZM hS hr ht hrM htM h3
  have htop := S.sup_commSpace_fixSpace_ZM hrM htM h3
  have huC : ∀ c ∈ fixSpace (S.rhoL hrM * S.rhoL htM),
      (u : S.Qt ≃ₗ[ZMod 2] S.Qt) c ∈ fixSpace (S.rhoL hrM * S.rhoL htM) := by
    intro c hc
    rw [mem_fixSpace] at hc ⊢
    rw [← hux, hc]
  refine ⟨hW, Subtype.ext (LinearEquiv.ext fun v => ?_),
    Subtype.ext (LinearEquiv.ext fun v => ?_)⟩
  · exact AS35ZM.commute_of_triv htop hW huC haC haW v
  · exact AS35ZM.commute_of_triv htop hW huC hbC hbW v

omit hr ht h3 in
include hS hJ hJD in
theorem triv_commSpace_ZM {u : S.O} {n : ℕ} (hn : (u : S.Qt ≃ₗ[ZMod 2] S.Qt) ^ (2 ^ n) = 1)
    (huJ : ∀ v, (u : S.Qt ≃ₗ[ZMod 2] S.Qt) (J v) = J ((u : S.Qt ≃ₗ[ZMod 2] S.Qt) v))
    {f : S.O} (hf : f ∈ S.DbarAsc) (huf : u * f = f * u) :
    ∀ w ∈ commSpace (f : S.Qt ≃ₗ[ZMod 2] S.Qt), (u : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  have hfin := (S.typeA_of_mem_DbarAsc_ZM hS hf).2.2.2.1
  have hfJ := hJD f hf
  have hufL : ∀ v, (u : S.Qt ≃ₗ[ZMod 2] S.Qt) ((f : S.Qt ≃ₗ[ZMod 2] S.Qt) v) =
      (f : S.Qt ≃ₗ[ZMod 2] S.Qt) ((u : S.Qt ≃ₗ[ZMod 2] S.Qt) v) := fun v => by
    have := congrArg (fun w : S.O => (w : S.Qt ≃ₗ[ZMod 2] S.Qt) v) huf
    simpa only [Subgroup.coe_mul, LinearEquiv.mul_apply] using this
  refine AS35ZM.point_two_elt hJ hfin.le (fun w hw => ?_) huJ
    (fun w hw => AS35ZM.commSpace_mem_of_commute hufL hw) hn
  exact AS35ZM.commSpace_mem_of_commute (fun v => (hfJ v).symm) hw

end Linear

section Group

variable {R : Subgroup S.O} (hRM : R ≤ S.Mbar) (hxM : r * t ∈ S.M)
  (hRx : ∀ σ ∈ R, σ * S.ρ ⟨r * t, hxM⟩ = S.ρ ⟨r * t, hxM⟩ * σ)
  (hRn : ∀ τ ∈ S.Mbar, τ * S.ρ ⟨r * t, hxM⟩ = S.ρ ⟨r * t, hxM⟩ * τ → ∀ σ ∈ R, τ * σ * τ⁻¹ ∈ R)
  (hR2 : IsPGroup 2 R)

theorem rho_mul_ZM : S.ρ ⟨r * t, hxM⟩ = S.ρ ⟨r, hrM⟩ * S.ρ ⟨t, htM⟩ := by
  rw [← map_mul]
  rfl

theorem commute_x_ZM {c : S.O} (hca : c * S.ρ ⟨r, hrM⟩ = S.ρ ⟨r, hrM⟩ * c)
    (hcb : c * S.ρ ⟨t, htM⟩ = S.ρ ⟨t, htM⟩ * c) :
    c * S.ρ ⟨r * t, hxM⟩ = S.ρ ⟨r * t, hxM⟩ * c := by
  rw [S.rho_mul_ZM hrM htM hxM, ← mul_assoc, hca, mul_assoc, hcb, mul_assoc]

include hRx in
theorem linear_of_mem_ZM {u : S.O} (hu : u ∈ R) :
    ∀ v, (u : S.Qt ≃ₗ[ZMod 2] S.Qt) ((S.rhoL hrM * S.rhoL htM) v) =
      (S.rhoL hrM * S.rhoL htM) ((u : S.Qt ≃ₗ[ZMod 2] S.Qt) v) := by
  intro v
  have e := congrArg (fun w : S.O => (w : S.Qt ≃ₗ[ZMod 2] S.Qt) v) (hRx u hu)
  simp only [Subgroup.coe_mul, LinearEquiv.mul_apply] at e
  rw [← S.rhoL_mul_mem hrM htM]
  exact e

theorem comm_mem_ZM (hRn : ∀ τ ∈ S.Mbar, τ * S.ρ ⟨r * t, hxM⟩ = S.ρ ⟨r * t, hxM⟩ * τ →
      ∀ σ ∈ R, τ * σ * τ⁻¹ ∈ R) {u c : S.O} (hu : u ∈ R) (hcM : c ∈ S.Mbar)
    (hcx : c * S.ρ ⟨r * t, hxM⟩ = S.ρ ⟨r * t, hxM⟩ * c) : u * c * u⁻¹ * c⁻¹ ∈ R := by
  have h := hRn c hcM hcx u⁻¹ (R.inv_mem hu)
  have := R.mul_mem hu h
  rwa [← mul_assoc, ← mul_assoc] at this

end Group

section Step

variable {J : S.Qt ≃ₗ[ZMod 2] S.Qt} (hJ : ∀ v, J (J v) + J v + v = 0)
  (hJD : ∀ a ∈ S.DbarAsc, ∀ v, (a : S.Qt ≃ₗ[ZMod 2] S.Qt) (J v) = J ((a : S.Qt ≃ₗ[ZMod 2] S.Qt) v))
  {R : Subgroup S.O} (hRM : R ≤ S.Mbar) (hxM : r * t ∈ S.M)
  (hRx : ∀ σ ∈ R, σ * S.ρ ⟨r * t, hxM⟩ = S.ρ ⟨r * t, hxM⟩ * σ)
  (hRn : ∀ τ ∈ S.Mbar, τ * S.ρ ⟨r * t, hxM⟩ = S.ρ ⟨r * t, hxM⟩ * τ → ∀ σ ∈ R, τ * σ * τ⁻¹ ∈ R)
  (hR2 : IsPGroup 2 R)
include hS h65 hr ht h3 hJ hJD hRM hRx hRn hR2

theorem commute_of_linear_ZM {k : ℕ} (hk : S.width = k + 2) {u : S.O} (hu : u ∈ R)
    (huJ : ∀ v, (u : S.Qt ≃ₗ[ZMod 2] S.Qt) (J v) = J ((u : S.Qt ≃ₗ[ZMod 2] S.Qt) v))
    {f : S.O} (hf : f ∈ S.DbarAsc) (hfa : f * S.ρ ⟨r, hrM⟩ = S.ρ ⟨r, hrM⟩ * f)
    (hfb : f * S.ρ ⟨t, htM⟩ = S.ρ ⟨t, htM⟩ * f) : u * f = f * u := by
  obtain ⟨n, hn⟩ := S.exists_pow_two_eq_one_ZM hR2 hu
  obtain ⟨-, hua, hub⟩ := S.linear_facts_ZM hS hr ht hrM htM h3 hJ hJD hn huJ
    (S.linear_of_mem_ZM hrM htM hxM hRx hu)
  have hfx := S.commute_x_ZM hrM htM hxM hfa hfb
  set d' := u * f * u⁻¹ with hd'
  have hd'D : d' ∈ S.DbarAsc := S.conj_mem_DbarAsc_L (hRM hu) hf
  have hd'a : d' * S.ρ ⟨r, hrM⟩ = S.ρ ⟨r, hrM⟩ * d' := by
    have cu : Commute u (S.ρ ⟨r, hrM⟩) := hua
    have cf : Commute f (S.ρ ⟨r, hrM⟩) := hfa
    exact ((cu.mul_left cf).mul_left cu.inv_left).eq
  have hd'b : d' * S.ρ ⟨t, htM⟩ = S.ρ ⟨t, htM⟩ * d' := by
    have cu : Commute u (S.ρ ⟨t, htM⟩) := hub
    have cf : Commute f (S.ρ ⟨t, htM⟩) := hfb
    exact ((cu.mul_left cf).mul_left cu.inv_left).eq
  have hff := S.mul_self_of_mem_DbarAsc_ZM hf
  have hfinv : f⁻¹ = f := inv_eq_of_mul_eq_one_right hff
  have hdf : d' * f ∈ R := by
    have := S.comm_mem_ZM hxM hRn hu (S.mem_Mbar_of_mem_DbarAsc_ZM hf) hfx
    rwa [hfinv] at this
  have hd'f : d' * f = f * d' := by
    by_contra hc
    exact S.orderOf_ne_three_ZM hR2 hdf (S.orderOf_mul_eq_three_ZM h65 hd'D hf hc)
  by_contra hne
  have hne' : f ≠ d' := by
    intro h
    apply hne
    calc u * f = u * f * u⁻¹ * u := by group
      _ = f * u := by rw [← hd', ← h]
  have hnc := S.rho_not_commute_ZM hr ht hrM htM h3
  obtain ⟨c, hc, hca, hcb, hcd', hcf⟩ := (S.pg_data_ZM h65 hk (S.ρ_mem_DbarAsc hr hrM)
    (S.ρ_mem_DbarAsc ht htM) hnc).1 f hf d' hd'D hfa hfb hd'a hd'b hd'f.symm hne'
  have hcx := S.commute_x_ZM hrM htM hxM hca hcb
  have hcc := S.mul_self_of_mem_DbarAsc_ZM hc
  have hcinv : c⁻¹ = c := inv_eq_of_mul_eq_one_right hcc
  have hdd := S.mul_self_of_mem_DbarAsc_ZM hd'D
  have hdinv : d'⁻¹ = d' := inv_eq_of_mul_eq_one_right hdd
  have hγ := S.comm_mem_ZM hxM hRn hdf (S.mem_Mbar_of_mem_DbarAsc_ZM hc) hcx
  have e : d' * f * c * (d' * f)⁻¹ * c⁻¹ = d' * ((f * c) * (f * c)) * d'⁻¹ := by
    rw [mul_inv_rev, hfinv, hdinv, hcinv]
    calc d' * f * c * (f * d') * c = d' * f * c * f * (d' * c) := by group
      _ = d' * f * c * f * (c * d') := by rw [hcd'.symm]
      _ = d' * (f * c * (f * c)) * d' := by group
  rw [e] at hγ
  have hfc : orderOf (f * c) = 3 := S.orderOf_mul_eq_three_ZM h65 hf hc
    (fun h => hcf h.symm)
  have h3' : orderOf (f * c * (f * c)) = 3 := by
    rw [← sq, Nat.Coprime.orderOf_pow (by rw [hfc]; norm_num), hfc]
  exact S.orderOf_ne_three_ZM hR2 hγ (by rw [orderOf_conj_ZM, h3'])

end Step

end Pair

end Setting

end CFSG.LargeExtraspecial
