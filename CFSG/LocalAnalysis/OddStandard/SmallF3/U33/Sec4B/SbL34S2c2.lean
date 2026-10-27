module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34Stmt
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutZmodProd

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34Z

open Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem card_modEq_one_of_fixedPointFree_aux {X : Type*} [Group X] [Finite X]
    {E : Subgroup X} (hE : CFSG.Open.IsElemAbelian 2 E) {x : X} (hx3 : x ^ 3 = 1)
    (hxE : ∀ e ∈ E, x * e * x⁻¹ ∈ E)
    (hff : ∀ e ∈ E, x * e * x⁻¹ = e → e = 1) : Nat.card E ≡ 1 [MOD 3] := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let f : ↥E → ↥E := fun e => ⟨x * e * x⁻¹, hxE e e.2⟩
  have hfinj : Function.Injective f := by
    intro e e' h
    have h' : x * (e : X) * x⁻¹ = x * (e' : X) * x⁻¹ := congrArg Subtype.val h
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h'))
  let σ : Equiv.Perm ↥E := Equiv.ofBijective f ⟨hfinj, Finite.surjective_of_injective hfinj⟩
  have hσf : ∀ e : ↥E, σ e = f e := fun e => rfl
  have hσ3 : σ ^ 3 = 1 := by
    ext e
    have hcalc : x * (x * (x * (e : X) * x⁻¹) * x⁻¹) * x⁻¹ = (e : X) := by
      have k1 : x * (x * (x * (e : X) * x⁻¹) * x⁻¹) * x⁻¹ =
          x ^ 3 * (e : X) * (x ^ 3)⁻¹ := by
        simp only [pow_succ, pow_zero, one_mul, mul_assoc, mul_inv_rev, inv_mul_cancel_left]
      rw [k1, hx3, inv_one, mul_one, one_mul]
    simp only [pow_succ, pow_zero, one_mul, Equiv.Perm.mul_apply, Equiv.Perm.one_apply, hσf]
    exact hcalc
  have hord : orderOf σ ∣ 3 ^ 1 := by
    rw [pow_one]
    exact orderOf_dvd_of_pow_eq_one hσ3
  have hpG : IsPGroup 3 (Subgroup.zpowers σ) := by
    rw [IsPGroup.iff_card]
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hord
    exact ⟨i, by rw [Nat.card_zpowers, hi]⟩
  have hfix : MulAction.fixedPoints (Subgroup.zpowers σ) ↥E = {1} := by
    ext e
    rw [Set.mem_singleton_iff, MulAction.mem_fixedPoints]
    constructor
    · intro h
      have hσe : σ e = e := by
        have := h ⟨σ, Subgroup.mem_zpowers σ⟩
        simpa using this
      have h2 : f e = e := by rw [← hσf]; exact hσe
      have hfe : x * (e : X) * x⁻¹ = e := congrArg Subtype.val h2
      exact Subtype.ext (hff e e.2 hfe)
    · rintro rfl m
      have hst : Subgroup.zpowers σ ≤ MulAction.stabilizer (Equiv.Perm ↥E) (1 : ↥E) := by
        rw [Subgroup.zpowers_le, MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def, hσf]
        exact Subtype.ext (by simp [f])
      have hm := hst m.2
      rw [MulAction.mem_stabilizer_iff] at hm
      exact hm
  have hcard := hpG.card_modEq_card_fixedPoints ↥E
  rw [hfix] at hcard
  simpa using hcard

private theorem eq_sq_of_mem_zpowers_of_sq_eq_one {x y : G} (hx : orderOf x = 4)
    (hy : y ∈ zpowers x) (hy2 : y * y = 1) (hy1 : y ≠ 1) : y = x * x := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hmod : x ^ (k % 4) = y := by
    have h : x ^ (k % (orderOf x : ℤ)) = x ^ k := zpow_mod_orderOf x k
    rw [hx] at h
    exact h.trans hk
  have ht : k % 4 = 0 ∨ k % 4 = 2 := by
    have hnonneg : 0 ≤ k % 4 := Int.emod_nonneg k (by norm_num)
    have hlt : k % 4 < 4 := Int.emod_lt_of_pos k (by norm_num)
    have hsquare : (x ^ (k % 4)) * (x ^ (k % 4)) = 1 := by rw [hmod, hy2]
    have hpow : x ^ (2 * (k % 4)) = 1 := by
      rw [show 2 * (k % 4) = (k % 4) + (k % 4) by ring, zpow_add]
      simpa using hsquare
    have hdvd : (4 : ℤ) ∣ 2 * (k % 4) := by
      have := orderOf_dvd_iff_zpow_eq_one.mpr hpow
      rwa [hx] at this
    obtain ⟨c, hc⟩ := hdvd
    omega
  rcases ht with h | h
  · exact absurd (by rw [← hmod, h, zpow_zero] : y = 1) hy1
  · have : y = x ^ (2 : ℤ) := by rw [← hmod, h]
    rw [this, zpow_two]

theorem isE16_or_isZ4Z4_of_abelian (Q V B : Subgroup G) (rho : G) (hVB : V ≤ B) (hBQ : B ≤ Q)
    (hVcard : Nat.card V = 4) (hVsq : ∀ v ∈ V, v * v = 1) (hQs : ∀ a ∈ Q, a * a ∈ V)
    (hρ3 : rho * rho * rho = 1) (hfix : ∀ q ∈ Q, rho * q = q * rho → q = 1)
    (hρB : ∀ b ∈ B, rho * b * rho⁻¹ ∈ B) (hB : Nat.card B = 16)
    (hab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) :
    IsZ4Z4Grp B ∨ IsE16Grp B := by
  let Ω : Subgroup G :=
    { carrier := {b | b ∈ B ∧ b * b = 1}
      one_mem' := ⟨B.one_mem, by simp⟩
      mul_mem' := by
        rintro a b ⟨haB, ha2⟩ ⟨hbB, hb2⟩
        refine ⟨B.mul_mem haB hbB, ?_⟩
        calc (a * b) * (a * b) = a * (b * a) * b := by group
          _ = a * (a * b) * b := by rw [hab b hbB a haB]
          _ = (a * a) * (b * b) := by group
          _ = 1 := by rw [ha2, hb2, one_mul]
      inv_mem' := by
        rintro a ⟨haB, ha2⟩
        refine ⟨B.inv_mem haB, ?_⟩
        have hinv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
        rw [hinv, ha2] }
  have hΩmem : ∀ b : G, b ∈ Ω ↔ b ∈ B ∧ b * b = 1 := fun b => Iff.rfl
  have hΩB : Ω ≤ B := fun b hb => ((hΩmem b).mp hb).1
  have hVΩ : V ≤ Ω := fun v hv => (hΩmem v).mpr ⟨hVB hv, hVsq v hv⟩
  have hE : CFSG.Open.IsElemAbelian 2 Ω := by
    refine ⟨IsMulCommutative.of_comm (fun a b => Subtype.ext ?_), ?_⟩
    · exact hab a.1 ((hΩmem a.1).mp a.2).1 b.1 ((hΩmem b.1).mp b.2).1
    · intro x hx
      rw [pow_two]
      exact ((hΩmem x).mp hx).2
  have hx3 : rho ^ 3 = 1 := by
    have hp : rho ^ 3 = rho * rho * rho := by
      rw [show (3 : ℕ) = 2 + 1 by rfl, pow_succ, pow_two]
    rw [hp]
    exact hρ3
  have hρΩ : ∀ e ∈ Ω, rho * e * rho⁻¹ ∈ Ω := by
    intro e he
    have heB : e ∈ B := ((hΩmem e).mp he).1
    have he2 : e * e = 1 := ((hΩmem e).mp he).2
    refine (hΩmem _).mpr ⟨hρB e heB, ?_⟩
    have hconj : (rho * e * rho⁻¹) * (rho * e * rho⁻¹) = rho * (e * e) * rho⁻¹ := by group
    rw [hconj, he2]
    group
  have hff : ∀ e ∈ Ω, rho * e * rho⁻¹ = e → e = 1 := by
    intro e he h
    apply hfix e (hBQ ((hΩmem e).mp he).1)
    calc rho * e = rho * e * rho⁻¹ * rho := by group
      _ = e * rho := by rw [h]
  have hmod : Nat.card Ω ≡ 1 [MOD 3] :=
    card_modEq_one_of_fixedPointFree_aux hE hx3 hρΩ hff
  have hn4or16 : Nat.card Ω = 4 ∨ Nat.card Ω = 16 := by
    have h4dvd : 4 ∣ Nat.card Ω := by
      have := Subgroup.card_dvd_of_le hVΩ
      rwa [hVcard] at this
    have h16dvd : Nat.card Ω ∣ 16 := by
      have := Subgroup.card_dvd_of_le hΩB
      rwa [hB] at this
    obtain ⟨i, hi_le, hn_eq⟩ :=
      (Nat.dvd_prime_pow (p := 2) (m := 4) Nat.prime_two).mp (by simpa using h16dvd)
    interval_cases i
    · rw [hn_eq] at h4dvd
      exact absurd h4dvd (by norm_num)
    · rw [hn_eq] at h4dvd
      exact absurd h4dvd (by norm_num)
    · left; rw [hn_eq]; norm_num
    · exfalso
      have hmod8 : (8 : ℕ) ≡ 1 [MOD 3] := by
        have h8 : Nat.card Ω = 8 := by rw [hn_eq]; norm_num
        rwa [h8] at hmod
      exact absurd hmod8 (by decide)
    · right; rw [hn_eq]; norm_num
  rcases hn4or16 with hn4 | hn16
  · left
    have hVeqΩ : V = Ω := by
      apply Subgroup.eq_of_le_of_card_ge hVΩ
      rw [hVcard, hn4]
    have hex : ∃ u ∈ B, u ∉ Ω := by
      by_contra h
      push_neg at h
      have hle : B ≤ Ω := fun u hu => h u hu
      have hc := Subgroup.card_dvd_of_le hle
      rw [hB, hn4] at hc
      exact absurd hc (by norm_num)
    obtain ⟨u, huB, huΩ⟩ := hex
    have hu2 : u * u ≠ 1 := fun h => huΩ ((hΩmem u).mpr ⟨huB, h⟩)
    have hu_mem_Q : u ∈ Q := hBQ huB
    have hu4 : u ^ 4 = 1 := by
      rw [show (4 : ℕ) = 2 + 2 by rfl, pow_add, pow_two]
      exact hVsq (u * u) (hQs u hu_mem_Q)
    have hu_ord : orderOf u = 4 := by
      have hnot : ¬ u ^ (2 : ℕ) ^ 1 = 1 := by
        rw [show (2 : ℕ) ^ 1 = 2 by norm_num]
        simpa [pow_two] using hu2
      have hfin : u ^ (2 : ℕ) ^ (1 + 1) = 1 := by
        rw [show (2 : ℕ) ^ (1 + 1) = 4 by norm_num]; exact hu4
      have h := orderOf_eq_prime_pow (x := u) (p := 2) (n := 1) hnot hfin
      rwa [show (2 : ℕ) ^ (1 + 1) = 4 by norm_num] at h
    let u₁ : G := rho * u * rho⁻¹
    have hu₁B : u₁ ∈ B := hρB u huB
    have hu₁sq_eq : u₁ * u₁ = rho * (u * u) * rho⁻¹ := by
      change (rho * u * rho⁻¹) * (rho * u * rho⁻¹) = rho * (u * u) * rho⁻¹
      group
    have hu₁2 : u₁ * u₁ ≠ 1 := by
      intro h
      apply hu2
      have h2 : rho * (u * u) * rho⁻¹ = 1 := by rw [← hu₁sq_eq]; exact h
      have h2' : rho * (u * u) = rho := by
        have hc : rho * (u * u) * rho⁻¹ = rho * rho⁻¹ := by rw [h2, mul_inv_cancel]
        exact mul_right_cancel hc
      have : rho * (u * u) = rho * 1 := by rw [mul_one]; exact h2'
      exact mul_left_cancel this
    have hu₁4 : u₁ ^ 4 = 1 := by
      rw [show (4 : ℕ) = 2 + 2 by rfl, pow_add, pow_two, hu₁sq_eq]
      have hA : (u * u) * (u * u) = 1 := hVsq (u * u) (hQs u hu_mem_Q)
      calc (rho * (u * u) * rho⁻¹) * (rho * (u * u) * rho⁻¹)
          = rho * ((u * u) * (u * u)) * rho⁻¹ := by group
        _ = 1 := by rw [hA]; group
    have hu₁_ord : orderOf u₁ = 4 := by
      have hnot : ¬ u₁ ^ (2 : ℕ) ^ 1 = 1 := by
        rw [show (2 : ℕ) ^ 1 = 2 by norm_num]
        simpa [pow_two] using hu₁2
      have hfin : u₁ ^ (2 : ℕ) ^ (1 + 1) = 1 := by
        rw [show (2 : ℕ) ^ (1 + 1) = 4 by norm_num]; exact hu₁4
      have h := orderOf_eq_prime_pow (x := u₁) (p := 2) (n := 1) hnot hfin
      rwa [show (2 : ℕ) ^ (1 + 1) = 4 by norm_num] at h
    have hu_comm : u * u₁ = u₁ * u := hab u huB u₁ hu₁B
    have hu_sq_ne : u * u ≠ u₁ * u₁ := by
      intro h
      apply hu2
      have hcc : u * u = rho * (u * u) * rho⁻¹ := by
        calc u * u = u₁ * u₁ := h
          _ = rho * (u * u) * rho⁻¹ := hu₁sq_eq
      have hcomm : rho * (u * u) = (u * u) * rho := by
        calc rho * (u * u) = rho * (u * u) * rho⁻¹ * rho := by group
          _ = (u * u) * rho := by rw [← hcc]
      exact hfix (u * u) (mul_mem hu_mem_Q hu_mem_Q) hcomm
    have hdisj : zpowers u ⊓ zpowers u₁ = ⊥ := by
      apply le_antisymm _ bot_le
      intro g hg
      rw [Subgroup.mem_bot]
      by_contra hg1
      have hgord : orderOf g ∣ 4 := by
        have := orderOf_dvd_of_mem_zpowers hg.1
        rwa [hu_ord] at this
      have hle : orderOf g ≤ 4 := Nat.le_of_dvd (by norm_num) hgord
      have hpos : 0 < orderOf g := Nat.pos_of_dvd_of_pos hgord (by norm_num)
      interval_cases hcases : orderOf g
      · exact hg1 (orderOf_eq_one_iff.mp hcases)
      · have hg2 : g * g = 1 := by
          have := pow_orderOf_eq_one g
          rw [hcases] at this
          simpa [pow_two] using this
        have hgu : g = u * u := eq_sq_of_mem_zpowers_of_sq_eq_one hu_ord hg.1 hg2 hg1
        have hgu₁ : g = u₁ * u₁ := eq_sq_of_mem_zpowers_of_sq_eq_one hu₁_ord hg.2 hg2 hg1
        exact hu_sq_ne (hgu.symm.trans hgu₁)
      · exact absurd hgord (by decide)
      · have hgsq_ord : orderOf (g ^ 2) = 2 := by
          rw [orderOf_pow, hcases]
          norm_num
        have hsq_mem_u : g ^ 2 ∈ zpowers u := by rw [pow_two]; exact (zpowers u).mul_mem hg.1 hg.1
        have hsq_mem_u₁ : g ^ 2 ∈ zpowers u₁ := by
          rw [pow_two]; exact (zpowers u₁).mul_mem hg.2 hg.2
        have hsq_ne : g ^ 2 ≠ 1 := by
          intro h
          rw [h, orderOf_one] at hgsq_ord
          norm_num at hgsq_ord
        have hg4 : g ^ 4 = 1 := by
          have := pow_orderOf_eq_one g
          rwa [hcases] at this
        have hsq_sq : (g ^ 2) * (g ^ 2) = 1 := by
          have := hg4
          rw [show (4 : ℕ) = 2 + 2 by rfl, pow_add] at this
          exact this
        have hgu : g ^ 2 = u * u :=
          eq_sq_of_mem_zpowers_of_sq_eq_one hu_ord hsq_mem_u hsq_sq hsq_ne
        have hgu₁ : g ^ 2 = u₁ * u₁ :=
          eq_sq_of_mem_zpowers_of_sq_eq_one hu₁_ord hsq_mem_u₁ hsq_sq hsq_ne
        exact hu_sq_ne (hgu.symm.trans hgu₁)
    have hle_sup : zpowers u ⊔ zpowers u₁ ≤ B :=
      sup_le (Subgroup.zpowers_le.mpr huB) (Subgroup.zpowers_le.mpr hu₁B)
    obtain ⟨e⟩ :=
      CFSG.OddStandard.SmallF3.HarrisU33.Outside.exists_mulEquiv_Z4Z4 u u₁ hu_comm hu_ord hu₁_ord
        hdisj
    have hcard :=
      CFSG.OddStandard.SmallF3.HarrisU33.Outside.card_zpowers_sup_zpowers u u₁ hu_comm 4 hu_ord
        hu₁_ord hdisj
    have hsup_eq_B : zpowers u ⊔ zpowers u₁ = B := by
      apply Subgroup.eq_of_le_of_card_ge hle_sup
      rw [hB, hcard]
    exact ⟨(MulEquiv.subgroupCongr hsup_eq_B).symm.trans e⟩
  · right
    have hΩeqB : Ω = B := by
      apply Subgroup.eq_of_le_of_card_ge hΩB
      rw [hB, hn16]
    exact ⟨hΩeqB ▸ hE, hB⟩

end CFSG.OddStandard.SmallF3.HarrisU33.L34Z
