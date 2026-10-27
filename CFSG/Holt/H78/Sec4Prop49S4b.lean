module

public import CFSG.Holt.H78.Sec4Prop49S4
import CFSG.Holt.H78.Sec4KnownKV
import CFSG.Holt.H78.Sec4SEAut
import CFSG.Holt.H78.KernelSylow

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Holt.General CFSG.Open Equiv
open scoped Pointwise commutatorElement

section Helpers


theorem IsNaturalSE.exists_mem_mul_self_ne {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ]
    {M : Subgroup (Perm Ψ)}
    (hM : IsNaturalSE M) {a : Ψ} {w : Perm Ψ} (hwM : w ∈ M) (hwa : w a = a) (hww : w * w = 1) :
    ∃ e ∈ M, e a = a ∧ e * e = 1 ∧ e ≠ 1 ∧ e ≠ w ∧ e * w = w * e := by
  classical
  have hw := hM.mem_mulLongInvClosure_of_mul_self hwM hwa hww
  obtain ⟨n, i, e, hA⟩ := hM.exists_isBenderAction
  obtain ⟨Q, hQ⟩ := hA.exists_sylow_le_stabilizer a
  have hcard : Nat.card (mulLongInvClosure M a) = 2 ^ n := by
    rw [hM.mulLongInvClosure_eq hQ, ← hA.rootCenter_seRadical_eq_map hQ,
      hA.card_rootCenter_seRadical]
  have h4 := hA.four_le_q
  obtain ⟨x, hx, hx1, hxw⟩ : ∃ x ∈ mulLongInvClosure M a, x ≠ 1 ∧ x ≠ w := by
    by_contra hno
    have hsub : ((mulLongInvClosure M a : Subgroup (Perm Ψ)) : Set (Perm Ψ)) ⊆ {1, w} :=
      fun x hx => by
        by_contra hx'
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hx'
        exact hno ⟨x, hx, hx'.1, hx'.2⟩
    have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe, hcard] at hle
    have := Set.ncard_insert_le (1 : Perm Ψ) {w}
    rw [Set.ncard_singleton] at this
    omega
  have hxM := mulLongInvClosure_le M a hx
  exact ⟨x, hxM.1, hxM.2, hM.mul_self_of_mem_mulLongInvClosure hx, hx1, hxw,
    hM.commute_of_mem_mulLongInvClosure hx hw⟩

theorem HoltData.exists_commute_of_rho_commute {K X : Type} [Group K] [Finite K]
    [MulAction K X] [Finite X] [FaithfulSMul K X] (hK : IsStarGroup K X) (D : HoltData K X)
    {x y : K} (hx : x ∈ longInv K X) (hy : y ∈ longInv K X)
    (h : ∀ l, D.ρ l ⟨x, mem_jHull_of_mem_longInv hx⟩ * D.ρ l ⟨y, mem_jHull_of_mem_longInv hy⟩ =
      D.ρ l ⟨y, mem_jHull_of_mem_longInv hy⟩ * D.ρ l ⟨x, mem_jHull_of_mem_longInv hx⟩) :
    ∃ (r : K) (hr : r ∈ longInv K X), r * x = x * r ∧
      ∀ l, D.ρ l ⟨r, mem_jHull_of_mem_longInv hr⟩ = D.ρ l ⟨y, mem_jHull_of_mem_longInv hy⟩ := by
  set xH : jHull K X := ⟨x, mem_jHull_of_mem_longInv hx⟩ with hxH
  set yH : jHull K X := ⟨y, mem_jHull_of_mem_longInv hy⟩ with hyH
  have hxx : x * x = 1 := mul_self_eq_one_of_mem_longInv hx
  have hyy : y * y = 1 := mul_self_eq_one_of_mem_longInv hy
  have hsq : (x * y) ^ 2 = ⁅x, y⁆ := by
    rw [commutatorElement_def, inv_eq_of_mul_eq_one_right hxx, inv_eq_of_mul_eq_one_right hyy,
      sq, ← mul_assoc]
  have hsoc : ⁅x, y⁆ ∈ D.socPre := by
    rw [← hsq]
    exact pow_mem (D.mul_mem_socPre hK hx hy) 2
  have hker : ⁅x, y⁆ ∈ jOrbitKernel K X := by
    have h1 := (D.mem_jOrbitKernel_iff_rho (h := ⁅xH, yH⁆)).mpr fun l => by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact h l
    exact h1
  have hO : ⁅x, y⁆ ∈ jOddCore K X := by
    rw [← D.socPre_inf_jOrbitKernel]
    exact ⟨hsoc, hker⟩
  have hodd : Odd (orderOf ((x * y) ^ 2)) := by
    rw [hsq]
    exact Odd.of_dvd_nat odd_card_jOddCore (Subgroup.orderOf_dvd_natCard _ hO)
  obtain ⟨k, hk⟩ := hodd
  obtain ⟨r, g, hrx, hgr, hyr⟩ := exists_conj_commute_of_odd hxx hyy k
    (by rw [← hk]; exact pow_orderOf_eq_one _)
  have hrJ : r ∈ longInv K X := by
    rw [← hgr]
    exact conj_mem_longInv hy g
  refine ⟨r, hrJ, hrx, fun l => ?_⟩
  have hoO : ((x * y) ^ 2) ^ k ∈ jOddCore K X := pow_mem (hsq ▸ hO) k
  have hr' : r = y * ((x * y) ^ 2) ^ k := by rw [← hyr, mul_inv_cancel_left]
  have hr : (⟨r, mem_jHull_of_mem_longInv hrJ⟩ : jHull K X) =
      yH * ⟨((x * y) ^ 2) ^ k, jOddCore_le_jHull hoO⟩ := Subtype.ext hr'
  rw [hr, map_mul, D.rho_eq_one_of_mem_jOddCore
    (h := ⟨((x * y) ^ 2) ^ k, jOddCore_le_jHull hoO⟩) hoO l, mul_one]


theorem mem_stabilizer_of_mul_self {G Ω : Type*} [Group G] [MulAction G Ω] {g : G}
    (hg : g * g = 1) {Λ : Set Ω} (h : ∀ δ ∈ Λ, g • δ ∈ Λ) : g ∈ stabilizer G Λ := by
  rw [mem_stabilizer_iff]
  refine Set.Subset.antisymm (Set.smul_set_subset_iff.mpr h) fun δ hδ =>
    ⟨g • δ, h δ hδ, by show g • g • δ = δ; rw [smul_smul, hg, one_smul]⟩

end Helpers

section Lemma74

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α : Ω} {v : G} {hS : Sec4Setting G Ω} {C : P49Config G Ω α v}

theorem P49K3.eq_j₀ (K : P49K3 hS C)
    (hL48 : ∀ {α : Ω} {v : G}, IsTypeL G Ω α v →
      ∀ (D : HoltData (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v))) (i : D.ι),
        IsNaturalSE (factorImage _ _ (D.L i) (D.ρ i)))
    (j : K.D'.ι) : j = K.j₀ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hj
  have h3 := C.three_le_card_holtDelta hS
  have hG := hS.star_twoPoint C.ne h3
  obtain ⟨w, hw, -, -⟩ := C.exists_mem_longInvSwap_mul hS
  have hŵJ := C.twoPointElt_mem_longInv hS hw
  set ŵ := twoPointElt (closure_longInvSwap_le_stabilizer_pair α C.β (Subgroup.subset_closure hw))
    with hŵ
  set wH : jHull (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β) :=
    ⟨ŵ, mem_jHull_of_mem_longInv hŵJ⟩ with hwH
  have hwjJ := K.D'.rho_mem_longInv hŵJ j
  obtain ⟨pj, hpj, -⟩ := hwjJ.2
  have hwjM : K.D'.ρ j wH ∈ K.D'.M j :=
    (K.D'.rho_mem_M_iff hŵJ j).mpr (K.se j hj).not_isOuterFactor
  obtain ⟨e, heM, hepj, hee, he1, hew, hecomm⟩ := (K.se j hj).exists_mem_mul_self_ne hwjM hpj
    (mul_self_eq_one_of_mem_longInv hwjJ)
  have heJ : e ∈ longInv (Perm (K.D'.Ψc j)) (K.D'.Ψc j) :=
    (K.se j hj).mem_longInv_perm heM (orderOf_eq_prime (by rw [sq]; exact hee) he1)
  obtain ⟨c₂, hc₂, hρ₂⟩ := hS.exists_mem_longInvSwap_rho_eq_of_twoPoint C.ne h3 K.D'
    (Function.update (fun l => K.D'.ρ l wH) j e) fun l => by
      rcases eq_or_ne l j with rfl | hl
      · rw [Function.update_self]
        exact ⟨Subgroup.map_le_range _ _ heM, heJ⟩
      · rw [Function.update_of_ne hl]
        exact ⟨⟨wH, rfl⟩, K.D'.rho_mem_longInv hŵJ l⟩
  have hy₀J := C.twoPointElt_mem_longInv hS hc₂
  set y₀ := twoPointElt (closure_longInvSwap_le_stabilizer_pair α C.β (Subgroup.subset_closure hc₂))
    with hy₀
  have hρ₂' : ∀ l, K.D'.ρ l ⟨y₀, mem_jHull_of_mem_longInv hy₀J⟩ =
      Function.update (fun l => K.D'.ρ l wH) j e l := hρ₂
  obtain ⟨r, hrJ, hrw, hρr⟩ := K.D'.exists_commute_of_rho_commute hG hŵJ hy₀J fun l => by
    rw [hρ₂' l]
    rcases eq_or_ne l j with rfl | hl
    · rw [Function.update_self]
      exact hecomm.symm
    · rw [Function.update_of_ne hl]
  have hρr' : ∀ l, K.D'.ρ l ⟨r, mem_jHull_of_mem_longInv hrJ⟩ =
      Function.update (fun l => K.D'.ρ l wH) j e l := fun l => (hρr l).trans (hρ₂' l)
  obtain ⟨c, hc, c', hc', hcc', hcŵ, hc'r⟩ := K.exists_commute_lift hL48 hŵJ hrJ hrw.symm
  have hŵr : ŵ ≠ r := fun h => hew (by
    have h1 := hρr' j
    rw [Function.update_self] at h1
    rw [← h1]
    exact congrArg (K.D'.ρ j) (Subtype.ext h.symm))
  have hne : c ≠ c' := fun h => hŵr (Subtype.ext (Equiv.ext fun δ =>
    Subtype.ext (by rw [hcŵ, hc'r, h])))
  obtain ⟨p₀, hp₀, -⟩ := hc.1.2
  have hc'p₀ : c' • p₀ = p₀ := by
    have h : c • (c' • p₀) = c' • p₀ := by rw [← mul_smul, hcc', mul_smul, hp₀]
    exact hc.1.2.unique h hp₀
  have hsα : (c * c') • α = α := by rw [mul_smul, hc'.2, smul_eq_of_mem_longInvSwap hc]
  have hsβ : (c * c') • C.β = C.β := by rw [mul_smul, smul_eq_of_mem_longInvSwap hc', hc.2]
  have hsJ : c * c' ∉ longInv G Ω := fun h => C.ne (h.2.unique hsα hsβ)
  have hs : IsTypeL G Ω p₀ (c * c') :=
    ⟨c, ⟨hc.1, hp₀⟩, c', ⟨hc'.1, hc'p₀⟩, hne, hcc', rfl, hsJ⟩
  have hŵŵ := mul_self_eq_one_of_mem_longInv hŵJ
  have hrr := mul_self_eq_one_of_mem_longInv hrJ
  have hsq' : ŵ * r * (ŵ * r) = ŵ * ŵ * (r * r) := by
    calc ŵ * r * (ŵ * r) = ŵ * (r * ŵ) * r := by group
      _ = ŵ * (ŵ * r) * r := by rw [hrw]
      _ = ŵ * ŵ * (r * r) := by group
  have hord : orderOf (ŵ * r) = 2 := orderOf_eq_prime (by rw [sq, hsq', hŵŵ, hrr, one_mul])
    fun h1 => hŵr ((eq_inv_of_mul_eq_one_right h1).trans (inv_eq_of_mul_eq_one_right hŵŵ)).symm
  set Λ : Set Ω := {δ | ∃ hδ : δ ∈ holtDelta G Ω α C.β, K.D'.coord ⟨δ, hδ⟩ j = pj} with hΛdef
  have hΛ : Λ ⊆ holtDelta G Ω α C.β ∩ fixSet Ω (Subgroup.zpowers (c * c')) := by
    rintro δ ⟨hδ, hδj⟩
    refine ⟨hδ, mem_fixSet_zpowers_iff.mpr ?_⟩
    have horb : (ŵ * r) • (⟨δ, hδ⟩ : holtDelta G Ω α C.β) ∈
        orbit (jOddCore (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β)) ⟨δ, hδ⟩ := by
      refine (K.D'.coord_eq_iff _ _).mp (funext fun l => ?_)
      rw [show (ŵ * r) • (⟨δ, hδ⟩ : holtDelta G Ω α C.β) =
        ((wH * ⟨r, mem_jHull_of_mem_longInv hrJ⟩ : jHull (twoPointSection G Ω α C.β)
          (holtDelta G Ω α C.β)) : twoPointSection G Ω α C.β) • ⟨δ, hδ⟩ from rfl,
        K.D'.coord_smul, map_mul, Perm.mul_apply, hρr' l]
      rcases eq_or_ne l j with rfl | hl
      · rw [Function.update_self, hδj, hepj]
        exact hpj.symm
      · rw [Function.update_of_ne hl, ← Perm.mul_apply, ← map_mul,
          show wH * wH = 1 from Subtype.ext hŵŵ, map_one, Perm.one_apply]
    have hT6 := hS.smul_eq_of_mul_mem_longInv_twoPointSection h3 K.D' hŵJ hrJ hord horb
      ⟨δ, hδ⟩ (mem_orbit_self _)
    calc (c * c') • δ = c • (c' • δ) := mul_smul _ _ _
      _ = c • (((r : Perm (holtDelta G Ω α C.β)) ⟨δ, hδ⟩ : holtDelta G Ω α C.β) : Ω) := by
        rw [hc'r]
      _ = (((ŵ : Perm (holtDelta G Ω α C.β)) ((r : Perm (holtDelta G Ω α C.β)) ⟨δ, hδ⟩) :
          holtDelta G Ω α C.β) : Ω) := by rw [hcŵ]
      _ = (((ŵ * r) • (⟨δ, hδ⟩ : holtDelta G Ω α C.β) : holtDelta G Ω α C.β) : Ω) := rfl
      _ = δ := by rw [hT6]
  obtain ⟨δ₀, -, hδ₀, -, -⟩ := C.exists_mem_holtDelta_ne hS
  have honto : ∀ p : K.D'.Ψc K.j₀, ∃ δ : holtDelta G Ω α C.β, (δ : Ω) ∈ Λ ∧
      K.D'.coord δ K.j₀ = p := fun p => by
    obtain ⟨δ, hδ⟩ := K.D'.coord_surjective
      (Function.update (Function.update (K.D'.coord ⟨_, hδ₀⟩) j pj) K.j₀ p)
    refine ⟨δ, ⟨δ.2, ?_⟩, by rw [hδ, Function.update_self]⟩
    show K.D'.coord δ j = pj
    rw [hδ, Function.update_of_ne hj, Function.update_self]
  have hreal : ∀ e₀ ∈ longInv (Perm (K.D'.Ψc K.j₀)) (K.D'.Ψc K.j₀),
      ∃ y : Subgroup.closure (longInvSwap G Ω α C.β), (y : G) ∈ longInvSwap G Ω α C.β ∧
        (y : G) ∈ stabilizer G Λ ∧ K.D'.ρ K.j₀ (twoPointJHom hS.star α C.β y) = e₀ := by
    intro e₀ he₀
    obtain ⟨c₃, hc₃, hρ₃⟩ := hS.exists_mem_longInvSwap_rho_eq_of_twoPoint C.ne h3 K.D'
      (Function.update (fun l => K.D'.ρ l wH) K.j₀ e₀) fun l => by
        rcases eq_or_ne l K.j₀ with rfl | hl
        · rw [Function.update_self]
          exact ⟨K.D'.mem_range_rho_of_alternating K.alt he₀, he₀⟩
        · rw [Function.update_of_ne hl]
          exact ⟨⟨wH, rfl⟩, K.D'.rho_mem_longInv hŵJ l⟩
    refine ⟨c₃, hc₃, mem_stabilizer_of_mul_self (mul_self_eq_one_of_mem_longInv hc₃.1) ?_,
      by rw [hρ₃, Function.update_self]⟩
    rintro δ ⟨hδ, hδj⟩
    refine ⟨((twoPointJHom hS.star α C.β c₃ : twoPointSection G Ω α C.β) •
      (⟨δ, hδ⟩ : holtDelta G Ω α C.β)).2, ?_⟩
    show K.D'.coord ((twoPointJHom hS.star α C.β c₃ : twoPointSection G Ω α C.β) •
      (⟨δ, hδ⟩ : holtDelta G Ω α C.β)) j = pj
    rw [K.D'.coord_smul, hρ₃, Function.update_of_ne hj, hδj]
    exact hpj
  exact hS.false_of_isTypeL_of_realize hL48 C.ne hs hsα hsβ K.D' K.j₀
    (by rw [K.card_eq]; norm_num) hΛ honto hreal

end Lemma74

end CFSG.Holt.H78
