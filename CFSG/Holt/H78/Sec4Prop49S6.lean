module

public import CFSG.Holt.H78.Sec4Prop49End
import CFSG.Holt.H78.Sec4Prop49S6L71
import CFSG.Holt.H78.Sec4KnownKV
import CFSG.Holt.H78.Sec4Lemma48

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt Equiv
open scoped Pointwise

section Points

variable {Ψ : Type*} [DecidableEq Ψ]

private theorem ofSubtype_mul_mem_longInv_perm {F : Finset Ψ} {e : Perm F}
    (he : e ∈ longInv (Perm F) F) {τ : Perm Ψ} (hτ : τ * τ = 1) (hτF : ∀ ψ ∈ F, τ ψ = ψ)
    (hτF' : ∀ ψ ∉ F, τ ψ ≠ ψ) :
    Perm.ofSubtype e * τ ∈ longInv (Perm Ψ) Ψ ∧ ∀ ψ : F, (Perm.ofSubtype e * τ) ψ = e ψ := by
  have hττ : ∀ ψ, τ (τ ψ) = ψ := fun ψ => by rw [← Perm.mul_apply, hτ, Perm.one_apply]
  have hee : ∀ ψ, e (e ψ) = ψ := fun ψ => by
    rw [← Perm.mul_apply, mul_self_eq_one_of_mem_longInv he, Perm.one_apply]
  have hin : ∀ ψ (h : ψ ∈ F), (Perm.ofSubtype e * τ) ψ = e ⟨ψ, h⟩ := fun ψ h => by
    rw [Perm.mul_apply, hτF ψ h]
    exact Perm.ofSubtype_apply_coe e ⟨ψ, h⟩
  have hτout : ∀ ψ ∉ F, τ ψ ∉ F := fun ψ hψ h => hψ (by
    have h2 := hτF _ h
    rw [hττ] at h2
    rw [h2]
    exact h)
  have hout : ∀ ψ ∉ F, (Perm.ofSubtype e * τ) ψ = τ ψ := fun ψ hψ => by
    rw [Perm.mul_apply, Perm.ofSubtype_apply_of_not_mem e (hτout ψ hψ)]
  set y := Perm.ofSubtype e * τ with hy
  have hyy : y * y = 1 := by
    ext ψ
    rw [Perm.mul_apply, Perm.one_apply]
    by_cases hψ : ψ ∈ F
    · rw [hin ψ hψ, hin _ (e ⟨ψ, hψ⟩).2, Subtype.coe_eta, hee]
    · rw [hout ψ hψ, hout _ (hτout ψ hψ), hττ]
  obtain ⟨r, hr, hr'⟩ := he.2
  have hy1 : y ≠ 1 := fun h => by
    have he1 : e = 1 := Equiv.ext fun x => Subtype.ext (by
      have := hin x x.2
      rw [h, Perm.one_apply] at this
      exact this.symm)
    have h2 := he.1
    rw [he1, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  refine ⟨⟨orderOf_eq_prime (by rw [sq]; exact hyy) hy1, (r : Ψ), ?_, fun ψ hψ => ?_⟩,
    fun ψ => hin ψ ψ.2⟩
  · show y r = r
    rw [hin r r.2]
    exact congrArg Subtype.val hr
  · have hψ' : y ψ = ψ := hψ
    by_cases hψF : ψ ∈ F
    · have h1 : e ⟨ψ, hψF⟩ = ⟨ψ, hψF⟩ := Subtype.ext ((hin ψ hψF).symm.trans hψ')
      exact congrArg Subtype.val (hr' _ h1)
    · exact absurd (by rw [← hout ψ hψF]; exact hψ') (hτF' ψ hψF)

private theorem exists_two_cycles_of_mem_longInv_perm [Fintype Ψ] {w : Perm Ψ}
    (hw : w ∈ longInv (Perm Ψ) Ψ) (h5 : 5 ≤ Fintype.card Ψ) :
    ∃ a c : Ψ, w a ≠ a ∧ w c ≠ c ∧ c ≠ a ∧ c ≠ w a := by
  obtain ⟨r, hr, hr'⟩ := hw.2
  obtain ⟨a, ha⟩ := Fintype.exists_ne_of_one_lt_card (by omega) r
  obtain ⟨c, -, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := {r, a, w a})
    (t := Finset.univ) (by rw [Finset.card_univ]; exact Finset.card_le_three.trans_lt (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
  exact ⟨a, c, fun h => ha (hr' a h), fun h => hc.1 (hr' c h), hc.2.1, hc.2.2⟩

private theorem mul_conj_swap_eq {w : Perm Ψ} (hw : w * w = 1) (a c : Ψ) :
    w * (swap a c * w * swap a c) = swap (w a) (w c) * swap a c := by
  rw [show w * (swap a c * w * swap a c) = w * swap a c * w * swap a c by simp only [mul_assoc],
    mul_swap_eq_swap_mul w a c, mul_assoc (swap (w a) (w c)) w w, hw, mul_one]

variable {p q s t : Ψ}

private theorem swap_mul_swap_apply_eq_self_iff (hpq : p ≠ q) (hps : p ≠ s) (hpt : p ≠ t)
    (hqs : q ≠ s) (hqt : q ≠ t) (hst : s ≠ t) (ψ : Ψ) :
    (swap p q * swap s t) ψ = ψ ↔ ψ ∉ ({p, q, s, t} : Finset Ψ) := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or, Perm.mul_apply]
  constructor
  · intro h
    refine ⟨fun hψ => ?_, fun hψ => ?_, fun hψ => ?_, fun hψ => ?_⟩ <;> rw [hψ] at h
    · rw [swap_apply_of_ne_of_ne hps hpt, swap_apply_left] at h
      exact hpq h.symm
    · rw [swap_apply_of_ne_of_ne hqs hqt, swap_apply_right] at h
      exact hpq h
    · rw [swap_apply_left, swap_apply_of_ne_of_ne hpt.symm hqt.symm] at h
      exact hst h.symm
    · rw [swap_apply_right, swap_apply_of_ne_of_ne hps.symm hqs.symm] at h
      exact hst h
  · rintro ⟨h1, h2, h3, h4⟩
    rw [swap_apply_of_ne_of_ne h3 h4, swap_apply_of_ne_of_ne h1 h2]

private theorem swap_mul_swap_mul_self (hps : p ≠ s) (hpt : p ≠ t) (hqs : q ≠ s) (hqt : q ≠ t) :
    swap p q * swap s t * (swap p q * swap s t) = 1 := by
  have hcomm : swap p q * swap s t = swap s t * swap p q := by
    rw [mul_swap_eq_swap_mul, swap_apply_of_ne_of_ne hps.symm hqs.symm,
      swap_apply_of_ne_of_ne hpt.symm hqt.symm]
  rw [mul_assoc, ← mul_assoc (swap s t), ← hcomm, mul_assoc, swap_mul_self_mul, swap_mul_self]

private theorem card_four (hpq : p ≠ q) (hps : p ≠ s) (hpt : p ≠ t) (hqs : q ≠ s) (hqt : q ≠ t)
    (hst : s ≠ t) : ({p, q, s, t} : Finset Ψ).card = 4 := by
  rw [Finset.card_insert_of_notMem (by simp [hpq, hps, hpt]),
    Finset.card_insert_of_notMem (by simp [hqs, hqt]), Finset.card_pair_eq_two_iff.mpr hst]

end Points

section Dihedral

variable {X : Type*} [Group X] {x y : X}

private theorem mul_pow_mul_inv_eq_inv (hx : x * x = 1) (hy : y * y = 1) (n : ℕ) :
    x * (x * y) ^ n * x⁻¹ = ((x * y) ^ n)⁻¹ := by
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  rw [← conj_pow, show x * (x * y) * x⁻¹ = (x * y)⁻¹ by
    rw [mul_inv_rev, hxi, hyi, ← mul_assoc, hx, one_mul], inv_pow]

private theorem inv_mul_mul_pow_eq (hx : x * x = 1) (hy : y * y = 1) (n : ℕ) :
    ((x * y) ^ n)⁻¹ * x * (x * y) ^ n = x * (x * y) ^ (2 * n) := by
  rw [← mul_pow_mul_inv_eq_inv hx hy n, two_mul, pow_add]
  simp only [mul_assoc, inv_mul_cancel_left]

end Dihedral

section P73

private def jHom {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [MulAction G Ω]
    (hG : IsStarGroup G Ω) (α β : Ω) : Subgroup.closure (longInvSwap G Ω α β) →*
      jHull (twoPointSection G Ω α β) (holtDelta G Ω α β) where
  toFun w := ⟨twoPointElt (closure_longInvSwap_le_stabilizer_pair α β w.2),
    twoPointElt_mem_jHull hG w.2⟩
  map_one' := Subtype.ext (Subtype.ext (map_one (twoPointHom G Ω α β)))
  map_mul' u v := Subtype.ext (Subtype.ext (map_mul (twoPointHom G Ω α β) ⟨u, _⟩ ⟨v, _⟩))

private abbrev jEltS {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [MulAction G Ω]
    (hG : IsStarGroup G Ω) {α β : Ω} {c : G} (hc : c ∈ longInvSwap G Ω α β) :
    jHull (twoPointSection G Ω α β) (holtDelta G Ω α β) :=
  jHom hG α β ⟨c, Subgroup.subset_closure hc⟩

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω]

private theorem p49Step96_aux (hS : Sec4Setting G Ω)
    (hL48 : ∀ {α : Ω} {v : G}, IsTypeL G Ω α v →
      ∀ (D : HoltData (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v))) (i : D.ι),
        IsNaturalSE (factorImage _ _ (D.L i) (D.ρ i)))
    {α β : Ω} (hαβ : α ≠ β) (D' : HoltData (twoPointSection G Ω α β) (holtDelta G Ω α β))
    (k : D'.ι) (h9 : 9 ≤ Fintype.card (D'.Ψc k))
    (hJr : longInv (Perm (D'.Ψc k)) (D'.Ψc k) ⊆ (D'.ρ k).range)
    {x y : G} (hx : x ∈ longInvSwap G Ω α β) (hy : y ∈ longInvSwap G Ω α β)
    {π : Perm (D'.Ψc k)} (F₁ : Finset (D'.Ψc k)) (hπF : ∀ ψ, π ψ = ψ ↔ ψ ∈ F₁)
    (hππ : π * π = 1) (hπ1 : π ≠ 1) (h5 : 5 ≤ F₁.card) (hodd : Odd F₁.card)
    (hρk : D'.ρ k (jEltS hS.star hx * jEltS hS.star hy) = π)
    (hρj : ∀ j, j ≠ k → D'.ρ j (jEltS hS.star hx * jEltS hS.star hy) = 1) :
    False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h3Δ := three_le_card_holtDelta_of_holtData hS.star D'
  set gC : Subgroup.closure (longInvSwap G Ω α β) := ⟨x * y, Subgroup.mul_mem _
    (Subgroup.subset_closure hx) (Subgroup.subset_closure hy)⟩ with hgC
  set r := jHom hS.star α β gC with hr
  have hJ : ∀ {c : G} (hc : c ∈ longInvSwap G Ω α β),
      (jEltS hS.star hc : twoPointSection G Ω α β) ∈
        longInv (twoPointSection G Ω α β) (holtDelta G Ω α β) :=
    fun {c} hc => (hS.mem_longInv_twoPointSection_iff hαβ h3Δ _).mpr ⟨c, hc, fun _ => rfl⟩
  have hrxy : r = jEltS hS.star hx * jEltS hS.star hy := by
    rw [hr, ← map_mul]
    rfl
  rw [← hrxy] at hρk hρj
  have hrS : (r : twoPointSection G Ω α β) ∈ D'.socPre := by
    rw [hrxy, Subgroup.coe_mul]
    exact hS.mul_mem_socPre_twoPointSection h3Δ D' (hJ hx) (hJ hy)
  have hrK : ((r ^ 2 : jHull _ _) : twoPointSection G Ω α β) ∈
      jOrbitKernel (twoPointSection G Ω α β) (holtDelta G Ω α β) :=
    (D'.mem_jOrbitKernel_iff_rho (h := r ^ 2)).mpr fun j => by
      rw [map_pow]
      rcases eq_or_ne j k with rfl | hj
      · rw [hρk, sq, hππ]
      · rw [hρj j hj, one_pow]
  have hrO : ((r ^ 2 : jHull _ _) : twoPointSection G Ω α β) ∈
      jOddCore (twoPointSection G Ω α β) (holtDelta G Ω α β) := by
    rw [← D'.socPre_inf_jOrbitKernel]
    exact ⟨by rw [Subgroup.coe_pow]; exact pow_mem hrS 2, hrK⟩
  have hodd2 : Odd (orderOf (r ^ 2)) := by
    rw [← Subgroup.orderOf_coe]
    exact Odd.of_dvd_nat odd_card_jOddCore (Subgroup.orderOf_dvd_natCard _ hrO)
  obtain ⟨a', m, hm, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos gC).ne'
  have hr2m : r ^ (2 * m) = 1 := by
    have h1 : (r ^ 2) ^ orderOf gC = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hr, ← map_pow, pow_orderOf_eq_one, map_one, one_pow]
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [hord] at h2
    rw [pow_mul, orderOf_dvd_iff_pow_eq_one.mp
      (((hodd2.coprime_two_right).pow_right a').dvd_of_dvd_mul_left h2)]
  set uC := gC ^ m with huC
  have hu : jHom hS.star α β uC = r ^ m := by rw [huC, map_pow]
  have hρku : D'.ρ k (r ^ m) = π := by
    obtain ⟨j, rfl⟩ := hm
    rw [map_pow, hρk, pow_succ, pow_mul, sq, hππ, one_pow, one_mul]
  have hρju : ∀ j, j ≠ k → D'.ρ j (r ^ m) = 1 := fun j hj => by
    rw [map_pow, hρj j hj, one_pow]
  have hu2 : jHom hS.star α β (uC ^ 2) = 1 := by
    rw [map_pow, hu, ← pow_mul, mul_comm, hr2m]
  have hx2 : x * x = 1 := mul_self_eq_one_of_mem_longInv hx.1
  have hy2 : y * y = 1 := mul_self_eq_one_of_mem_longInv hy.1
  have hgα : (x * y) • α = α := by rw [mul_smul, hy.2, smul_eq_of_mem_longInvSwap hx]
  have hgβ : (x * y) • β = β := by rw [mul_smul, smul_eq_of_mem_longInvSwap hy, hx.2]
  have hpow : ∀ n : ℕ, ((gC ^ n : Subgroup.closure (longInvSwap G Ω α β)) : G) = (x * y) ^ n :=
    fun n => Subgroup.coe_pow _ _ _
  have hpowα : ∀ n : ℕ, (x * y) ^ n • α = α := fun n =>
    mem_stabilizer_iff.mp (pow_mem (mem_stabilizer_iff.mpr hgα) n)
  have hpowβ : ∀ n : ℕ, (x * y) ^ n • β = β := fun n =>
    mem_stabilizer_iff.mp (pow_mem (mem_stabilizer_iff.mpr hgβ) n)
  obtain ⟨γ, hγ, hγ'⟩ := hx.1.2
  have hγΔ : γ ∈ holtDelta G Ω α β := ⟨x, hx, hγ⟩
  have hnotJ : ∀ {w : G}, w • α = α → w • β = β → w ∉ longInv G Ω := fun hwα hwβ hw =>
    hαβ (hw.2.unique hwα hwβ)
  by_cases huu : uC ^ 2 = 1
  ·
    set u : G := (uC : G) with hudef
    have hum : u = (x * y) ^ m := hpow m
    have huu' : u * u = 1 := by
      rw [hudef, ← Subgroup.coe_mul, ← sq, huu, Subgroup.coe_one]
    have hu1 : jHom hS.star α β uC ≠ 1 := fun h => hπ1 (by rw [← hρku, ← hu, h, map_one])
    obtain ⟨j, hj⟩ := hm
    obtain ⟨y', c', hy'x, hc', hy'⟩ := exists_conj_commute_of_odd hx2 hy2 j (by
      rw [← pow_mul, mul_comm 2, ← hj, pow_mul, ← hum, sq, huu'])
    have hxy' : x * y' = u := by
      have h1 : y' = y * ((x * y) ^ 2) ^ j := by rw [← hy', mul_inv_cancel_left]
      rw [h1, ← mul_assoc, ← pow_mul, ← pow_succ', hum, hj]
    have hy'J : y' ∈ longInv G Ω := hc' ▸ conj_mem_longInv hy.1 c'
    have huα : u • α = α := by rw [hum]; exact hpowα m
    have huβ : u • β = β := by rw [hum]; exact hpowβ m
    have hy'S : y' ∈ longInvSwap G Ω α β := by
      refine ⟨hy'J, ?_⟩
      rw [show y' = x * u by rw [← hxy', ← mul_assoc, hx2, one_mul], mul_smul, huα, hx.2]
    have hy'γ : y' • γ = γ := hγ' _ (by
      show x • (y' • γ) = y' • γ
      rw [smul_smul, ← hy'x, mul_smul, hγ])
    have hxne : x ≠ y' := fun h => hu1 (by
      have huC1 : uC = 1 := Subtype.ext (by rw [← hudef, ← hxy', ← h, hx2]; rfl)
      rw [huC1, map_one])
    have hz : IsTypeL G Ω γ u :=
      ⟨x, ⟨hx.1, hγ⟩, y', ⟨hy'J, hy'γ⟩, hxne, hy'x.symm, hxy', hnotJ huα huβ⟩
    have hmul : (jEltS hS.star hx : twoPointSection G Ω α β) *
        (jEltS hS.star hy'S : twoPointSection G Ω α β) =
        (jHom hS.star α β uC : twoPointSection G Ω α β) :=
      Subtype.ext (Equiv.ext fun δ => Subtype.ext (by
        show x • (y' • (δ : Ω)) = u • (δ : Ω)
        rw [← mul_smul, hxy']))
    have huo : orderOf (jHom hS.star α β uC : twoPointSection G Ω α β) = 2 := by
      refine orderOf_eq_prime ?_ fun h => hu1 (Subtype.ext h)
      rw [← Subgroup.coe_pow, ← map_pow, hu2, Subgroup.coe_one]
    have hFz : ∀ δ : holtDelta G Ω α β, u • (δ : Ω) = δ ↔ D'.coord δ k ∈ F₁ := by
      intro δ
      have hcoord : ∀ j, D'.coord ((jHom hS.star α β uC : twoPointSection G Ω α β) • δ) j =
          D'.ρ j (r ^ m) (D'.coord δ j) := fun j => by rw [D'.coord_smul, hu]
      constructor
      · intro h
        have h' : (jHom hS.star α β uC : twoPointSection G Ω α β) • δ = δ := Subtype.ext h
        rw [← hπF, ← hρku, ← hcoord k, h']
      · intro h
        have hco : D'.coord δ =
            D'.coord ((jHom hS.star α β uC : twoPointSection G Ω α β) • δ) :=
          funext fun j => by
            rw [hcoord j]
            rcases eq_or_ne j k with rfl | hj
            · rw [hρku, (hπF _).mpr h]
            · rw [hρju j hj, Perm.one_apply]
        have hω := (D'.coord_eq_iff _ _).mp hco
        rw [← hmul] at hω
        have h1 := hS.smul_eq_of_mul_mem_longInv_twoPointSection h3Δ D' (hJ hx) (hJ hy'S)
          (by rw [hmul]; exact huo) hω δ (mem_orbit_self δ)
        rw [hmul] at h1
        exact congrArg Subtype.val h1
    refine hS.false_of_isTypeL_of_coord hL48 hαβ hz huα huβ D' k F₁ hodd h5 hFz ?_
    intro e he
    obtain ⟨h1, h2⟩ := ofSubtype_mul_mem_longInv_perm he hππ (fun ψ hψ => (hπF ψ).mpr hψ)
      (fun ψ hψ h => hψ ((hπF ψ).mp h))
    exact ⟨_, h1, hJr h1, h2⟩
  ·
    obtain ⟨n, rfl⟩ : ∃ n, a' = n + 2 := by
      rcases a' with _ | _ | n
      · exact absurd (by rw [huC, ← pow_mul, show m * 2 = orderOf gC * 2 by rw [hord]; ring,
          pow_mul, pow_orderOf_eq_one, one_pow]) huu
      · exact absurd (by rw [huC, ← pow_mul, show m * 2 = orderOf gC by rw [hord]; ring,
          pow_orderOf_eq_one]) huu
      · exact ⟨n, rfl⟩
    set zC := uC ^ 2 ^ (n + 1) with hzC
    set z : G := (zC : G) with hzdef
    have hzpow : z = (x * y) ^ (2 * (m * 2 ^ n)) := by
      rw [hzdef, hzC, huC, ← pow_mul, hpow]
      ring_nf
    have hzz : zC ^ 2 = 1 := by
      rw [hzC, ← pow_mul, ← pow_succ, huC, ← pow_mul,
        show m * 2 ^ (n + 1 + 1) = orderOf gC by rw [hord]; ring, pow_orderOf_eq_one]
    have hz1 : z ≠ 1 := by
      intro h
      have h1 : gC ^ (m * 2 ^ (n + 1)) = 1 := Subtype.ext (by
        rw [hpow, show m * 2 ^ (n + 1) = 2 * (m * 2 ^ n) by ring, ← hzpow, h]; rfl)
      have hm0 : 0 < m := hm.pos
      have h2n : 0 < 2 ^ n := by positivity
      have h2 := Nat.le_of_dvd (by positivity) (orderOf_dvd_of_pow_eq_one h1)
      rw [hord, pow_succ, pow_succ] at h2
      nlinarith
    have hzΔ : jHom hS.star α β zC = 1 := by
      rw [hzC, pow_succ', pow_mul, map_pow, hu2, one_pow]
    have hzfix : ∀ δ : holtDelta G Ω α β, z • (δ : Ω) = δ := fun δ =>
      congrArg (fun σ : jHull (twoPointSection G Ω α β) (holtDelta G Ω α β) =>
        ((((σ : twoPointSection G Ω α β) : Perm (holtDelta G Ω α β)) δ : holtDelta G Ω α β) :
          Ω)) hzΔ
    have hzα : z • α = α := by rw [hzpow]; exact hpowα _
    have hzβ : z • β = β := by rw [hzpow]; exact hpowβ _
    have hzz' : z * z = 1 := by
      rw [hzdef, ← Subgroup.coe_mul, ← sq, hzz, Subgroup.coe_one]
    have hxzJ : x * z ∈ longInv G Ω := by
      have h := conj_mem_longInv hx.1 ((x * y) ^ (m * 2 ^ n))⁻¹
      rwa [inv_inv, inv_mul_mul_pow_eq hx2 hy2, ← hzpow] at h
    have hxz : x * z = z * x := by
      have h := mul_pow_mul_inv_eq_inv hx2 hy2 (2 * (m * 2 ^ n))
      rw [← hzpow, inv_eq_of_mul_eq_one_right hzz', mul_inv_eq_iff_eq_mul] at h
      exact h
    have hxzγ : (x * z) • γ = γ := by rw [mul_smul, hzfix ⟨γ, hγΔ⟩, hγ]
    have hxne : x ≠ x * z := fun h => hz1 (mul_left_cancel (h.symm.trans (mul_one x).symm))
    have hz : IsTypeL G Ω γ z := ⟨x, ⟨hx.1, hγ⟩, x * z, ⟨hxzJ, hxzγ⟩, hxne,
      by rw [Commute, SemiconjBy, ← mul_assoc, hx2, one_mul, hxz, mul_assoc, hx2, mul_one],
      by rw [← mul_assoc, hx2, one_mul], hnotJ hzα hzβ⟩
    refine hS.false_of_isTypeL_of_coord hL48 hαβ hz hzα hzβ D' k Finset.univ
      (by rw [Finset.card_univ]; exact D'.odd_card_Ψc k) (by rw [Finset.card_univ]; omega)
      (fun δ => ⟨fun _ => Finset.mem_univ _, fun _ => hzfix δ⟩) ?_
    intro e he
    obtain ⟨h1, h2⟩ := ofSubtype_mul_mem_longInv_perm he (mul_one 1) (fun _ _ => rfl)
      (fun ψ hψ => absurd (Finset.mem_univ ψ) hψ)
    exact ⟨_, h1, hJr h1, h2⟩

theorem Sec4Setting.p49Step96 (hS : Sec4Setting G Ω)
    (hL48 : ∀ {α : Ω} {v : G}, IsTypeL G Ω α v →
      ∀ (D : HoltData (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v))) (i : D.ι),
        IsNaturalSE (factorImage _ _ (D.L i) (D.ρ i))) :
    P49Step96 G Ω := by
  intro α β hαβ D' k hk h9
  classical
  have h3Δ := three_le_card_holtDelta_of_holtData hS.star D'
  have hAr : alternatingGroup (D'.Ψc k) ≤ (D'.ρ k).range := hk ▸ Subgroup.map_le_range _ _
  set w := D'.ρ k D'.tHull with hw
  have hwJ : w ∈ longInv (Perm (D'.Ψc k)) (D'.Ψc k) := D'.rho_mem_longInv D'.t_mem k
  have hJr : longInv (Perm (D'.Ψc k)) (D'.Ψc k) ⊆ (D'.ρ k).range :=
    longInv_perm_subset_of_alternatingGroup_le hAr ⟨D'.tHull, rfl⟩ hwJ
  have hww : w * w = 1 := mul_self_eq_one_of_mem_longInv hwJ
  obtain ⟨a, c, hwa, hwc, hca, hcwa⟩ := exists_two_cycles_of_mem_longInv_perm hwJ (by omega)
  have hwwc : w (w c) = c := by rw [← Perm.mul_apply, hww, Perm.one_apply]
  have h1 : w a ≠ w c := fun h => hca (w.injective h).symm
  have h3 : w a ≠ c := fun h => hcwa h.symm
  have h4 : w c ≠ a := fun h => hcwa (by rw [← h, hwwc])
  have h6 : a ≠ c := fun h => hca h.symm
  set F₁ : Finset (D'.Ψc k) := ({w a, w c, a, c} : Finset (D'.Ψc k))ᶜ with hF₁
  set π := swap (w a) (w c) * swap a c with hπ
  have hπF : ∀ ψ, π ψ = ψ ↔ ψ ∈ F₁ := fun ψ => by
    rw [hF₁, Finset.mem_compl]
    exact swap_mul_swap_apply_eq_self_iff h1 hwa h3 h4 hwc h6 ψ
  have hππ : π * π = 1 := swap_mul_swap_mul_self hwa h3 h4 hwc
  have hπ1 : π ≠ 1 := fun h => by
    have h' := (hπF a).mp (by rw [h, Perm.one_apply])
    exact Finset.mem_compl.mp h' (by simp)
  have hcard : F₁.card = Fintype.card (D'.Ψc k) - 4 := by
    rw [hF₁, Finset.card_compl, card_four h1 hwa h3 h4 hwc h6]
  set w' := swap a c * w * swap a c with hw'
  have hw'J : w' ∈ longInv (Perm (D'.Ψc k)) (D'.Ψc k) := by
    have h := conj_mem_longInv hwJ (swap a c)
    rwa [swap_inv] at h
  obtain ⟨ŷ, hŷJ, hŷk, hŷj⟩ := D'.exists_longInv_update k (hJr hw'J) hw'J
  obtain ⟨x, hx, hxt⟩ := (hS.mem_longInv_twoPointSection_iff hαβ h3Δ _).mp D'.t_mem
  obtain ⟨y, hy, hyŷ⟩ := (hS.mem_longInv_twoPointSection_iff hαβ h3Δ _).mp hŷJ
  have hxe : jEltS hS.star hx = D'.tHull :=
    Subtype.ext (Subtype.ext (Equiv.ext fun δ => Subtype.ext (hxt δ).symm))
  have hye : jEltS hS.star hy = ŷ :=
    Subtype.ext (Subtype.ext (Equiv.ext fun δ => Subtype.ext (hyŷ δ).symm))
  have hmul : jEltS hS.star hx * jEltS hS.star hy = D'.tHull * ŷ := by rw [hxe, hye]
  refine p49Step96_aux hS hL48 hαβ D' k h9 hJr hx hy F₁ hπF hππ hπ1 (by omega) ?_ ?_ ?_
  · obtain ⟨j, hj⟩ := D'.odd_card_Ψc k
    exact ⟨j - 2, by omega⟩
  · rw [hmul, map_mul, hŷk]
    exact mul_conj_swap_eq hww a c
  · intro j hj
    rw [hmul, map_mul, hŷj j hj]
    exact mul_self_eq_one_of_mem_longInv (D'.rho_mem_longInv D'.t_mem j)

theorem Sec4Setting.p49Step96_of (hS : Sec4Setting G Ω)
    (hP43 : ∀ {α β : Ω}, α ≠ β → IsEmpty (AltConfig G Ω α β))
    (hP46 : ∀ {α : Ω} {v : G}, IsTypeL G Ω α v →
      CFSG.pPrimeCore 2 (typeLSection G Ω v) = ⊥) :
    P49Step96 G Ω :=
  hS.p49Step96 fun hv D i => hS.isNaturalSE_factor_typeLSection_of hP43 hv (hP46 hv) D i

end P73

end CFSG.Holt.H78
