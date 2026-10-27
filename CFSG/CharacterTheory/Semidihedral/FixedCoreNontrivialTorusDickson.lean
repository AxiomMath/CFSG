module

public import CFSG.CharacterTheory.Semidihedral.UnitaryBranchDValueDataProjective
public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialLocal
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonClassification
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Semidihedral.FixedCoreNontrivial

open CFSG.ComponentClassification.CatalogueSchreierLinearTwo

variable {K : Type} [Field K] [Finite K]

omit [Field K] in
theorem card_omega : Nat.card (Omega K) = Nat.card K + 1 := Finite.card_option

theorem card_fixed_le_two {u : Equiv.Perm (Omega K)} (hu : u ∈ coordinateD K) (hu1 : u ≠ 1) :
    Nat.card {x : Omega K // u x = x} ≤ 2 := by
  classical
  have := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  by_contra h
  push Not at h
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := Finset.two_lt_card_iff.mp h
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb hc
  exact hu1 (UnitaryBranch.eq_one_of_three_fixed_points K hu hab hac hbc ha hb hc)

omit [Field K] in
theorem card_fixed_modEq {u : Equiv.Perm (Omega K)} {r : ℕ} [Fact r.Prime] (hu : orderOf u = r) :
    Nat.card {x : Omega K // u x = x} ≡ Nat.card K + 1 [MOD r] := by
  have hZ : IsPGroup r (Subgroup.zpowers u) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu, pow_one])
  have h := hZ.card_modEq_card_fixedPoints (Omega K)
  have he : Nat.card (MulAction.fixedPoints (Subgroup.zpowers u) (Omega K)) =
      Nat.card {x : Omega K // u x = x} := by
    apply Nat.card_congr
    apply Equiv.subtypeEquivRight
    intro x
    constructor
    · intro hx
      exact hx ⟨u, Subgroup.mem_zpowers u⟩
    · intro hx g
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp g.2
      change (g : Equiv.Perm (Omega K)) x = x
      rw [← hk]
      exact Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hx k
  rw [he, card_omega] at h
  exact h.symm

theorem existsUnique_fixed_of_orderOf_eq_char {p f : ℕ} (hp : p.Prime) (hpodd : Odd p)
    (hK : Nat.card K = p ^ f) {u : Equiv.Perm (Omega K)} (hu : u ∈ coordinateD K)
    (hup : orderOf u = p) : ∃! x : Omega K, u x = x := by
  have : Fact p.Prime := ⟨hp⟩
  have hf : f ≠ 0 := by
    rintro rfl
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    rw [hK, pow_zero] at h1
    exact lt_irrefl 1 h1
  have hu1 : u ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hup
    exact hp.one_lt.ne hup
  have hmod := card_fixed_modEq hup
  have hle := card_fixed_le_two hu hu1
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    rcases hpodd with ⟨k, hk⟩
    omega
  have hq1 : (p ^ f + 1) % p = 1 := by
    obtain ⟨g, hg⟩ : p ∣ p ^ f := dvd_pow_self p hf
    rw [hg, Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt (by omega)
  rw [hK] at hmod
  have h1 : Nat.card {x : Omega K // u x = x} = 1 := by
    unfold Nat.ModEq at hmod
    rw [hq1] at hmod
    interval_cases h : Nat.card {x : Omega K // u x = x}
    · simp at hmod
    · rfl
    · rw [Nat.mod_eq_of_lt (by omega)] at hmod
      exact absurd hmod (by norm_num)
  obtain ⟨⟨x, hx⟩, hxu⟩ := Nat.card_eq_one_iff_exists.mp h1
  exact ⟨x, hx, fun y hy => congrArg Subtype.val (hxu ⟨y, hy⟩)⟩

theorem exists_fixed_of_normal_elementary {p f : ℕ} (hp : p.Prime) (hpodd : Odd p)
    (hK : Nat.card K = p ^ f) {X N : Subgroup (Equiv.Perm (Omega K))} (hXD : X ≤ coordinateD K)
    (hNX : N ≤ X) (hNn : ∀ g ∈ X, ∀ n ∈ N, g * n * g⁻¹ ∈ N) (hNp : ∀ n ∈ N, n ^ p = 1)
    (hNcomm : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a) {u : Equiv.Perm (Omega K)} (huN : u ∈ N)
    (hu1 : u ≠ 1) : ∃ x : Omega K, ∀ g ∈ X, g x = x := by
  have : Fact p.Prime := ⟨hp⟩
  have hup : orderOf u = p := orderOf_eq_prime (hNp u huN) hu1
  obtain ⟨x, hx, hxu⟩ := existsUnique_fixed_of_orderOf_eq_char hp hpodd hK (hXD (hNX huN)) hup
  refine ⟨x, fun g hg => ?_⟩
  have hvN : g * u * g⁻¹ ∈ N := hNn g hg u huN
  have hv1 : g * u * g⁻¹ ≠ 1 := by
    intro h
    apply hu1
    calc u = g⁻¹ * (g * u * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  have hvp : orderOf (g * u * g⁻¹) = p := orderOf_eq_prime (hNp _ hvN) hv1
  obtain ⟨y, -, hyv⟩ := existsUnique_fixed_of_orderOf_eq_char hp hpodd hK (hXD (hNX hvN)) hvp
  have hvx : (g * u * g⁻¹) x = x := by
    have hc : (g * u * g⁻¹) * u = u * (g * u * g⁻¹) := hNcomm _ hvN u huN
    have h2 : u ((g * u * g⁻¹) x) = (g * u * g⁻¹) x := by
      rw [← Equiv.Perm.mul_apply, ← hc, Equiv.Perm.mul_apply, hx]
    exact hxu _ h2
  have hvgx : (g * u * g⁻¹) (g x) = g x := by
    simp [Equiv.Perm.mul_apply, hx]
  rw [hyv _ hvgx, hyv _ hvx]

theorem exists_fixed_of_cyclic_dvd {X : Subgroup (Equiv.Perm (Omega K))}
    (hXD : X ≤ coordinateD K) (hXc : IsCyclic X) (hXodd : Odd (Nat.card X))
    (hXq : Nat.card X ∣ Nat.card K - 1) : ∃ x : Omega K, ∀ g ∈ X, g x = x := by
  classical
  have := Fintype.ofFinite K
  obtain ⟨g, hg⟩ := hXc.exists_generator
  by_cases h1 : Nat.card X = 1
  · refine ⟨none, fun y hy => ?_⟩
    have hbot : X = ⊥ := Subgroup.card_eq_one.mp h1
    rw [hbot, Subgroup.mem_bot] at hy
    rw [hy]
    rfl
  obtain ⟨r, hr, hrX⟩ := Nat.exists_prime_and_dvd h1
  have : Fact r.Prime := ⟨hr⟩
  have hr3 : 3 ≤ r := by
    have h2 := hr.two_le
    have hodd := hXodd.of_dvd_nat hrX
    rcases hodd with ⟨k, hk⟩
    omega
  have hX0 : Nat.card X ≠ 0 := Nat.card_pos.ne'
  have hgo : orderOf (g : Equiv.Perm (Omega K)) = Nat.card X := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg]
  set h : Equiv.Perm (Omega K) := (g : Equiv.Perm (Omega K)) ^ (Nat.card X / r) with hhdef
  have hdiv : Nat.card X / r ≠ 0 := by
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hX0) hrX
    exact (Nat.div_pos this hr.pos).ne'
  have hho : orderOf h = r := by
    rw [hhdef, orderOf_pow_of_dvd hdiv (by rw [hgo]; exact Nat.div_dvd_of_dvd hrX), hgo,
      Nat.div_div_self hrX hX0]
  have hhD : h ∈ coordinateD K := (coordinateD K).pow_mem (hXD g.2) _
  have hh1 : h ≠ 1 := by
    intro h0
    rw [h0, orderOf_one] at hho
    exact hr.one_lt.ne hho
  have hmod := card_fixed_modEq hho
  have hle := card_fixed_le_two hhD hh1
  have hq : Nat.card K + 1 ≡ 2 [MOD r] := by
    have hrq : r ∣ Nat.card K - 1 := hrX.trans hXq
    have hK1 : 1 ≤ Nat.card K := Nat.one_le_iff_ne_zero.mpr Nat.card_pos.ne'
    obtain ⟨c, hc⟩ := hrq
    unfold Nat.ModEq
    rw [show Nat.card K + 1 = r * c + 2 by omega, Nat.mul_add_mod]
  have h2 : Nat.card {x : Omega K // h x = x} = 2 := by
    have hm := hmod.trans hq
    unfold Nat.ModEq at hm
    interval_cases hc : Nat.card {x : Omega K // h x = x}
    · rw [Nat.zero_mod, Nat.mod_eq_of_lt (by omega)] at hm
      exact absurd hm (by norm_num)
    · rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hm
      exact absurd hm (by norm_num)
    · rfl
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h2
  obtain ⟨x₁, x₂, hx12, hfix⟩ := Finset.card_eq_two.mp h2
  have hx₁ : h x₁ = x₁ := by
    have : x₁ ∈ Finset.univ.filter (fun x => h x = x) := by rw [hfix]; simp
    simpa using this
  have hmemfix : ∀ y, h y = y → y = x₁ ∨ y = x₂ := by
    intro y hy
    have : y ∈ Finset.univ.filter (fun x => h x = x) := by simpa using hy
    rw [hfix] at this
    simpa using this
  have hcomm : Commute (g : Equiv.Perm (Omega K)) h := (Commute.refl _).pow_right _
  have hgfix : ∀ y, h y = y → h ((g : Equiv.Perm (Omega K)) y) = (g : Equiv.Perm (Omega K)) y := by
    intro y hy
    rw [← Equiv.Perm.mul_apply, ← hcomm.eq, Equiv.Perm.mul_apply, hy]
  have hgx₁ : (g : Equiv.Perm (Omega K)) x₁ = x₁ := by
    rcases hmemfix _ (hgfix x₁ hx₁) with h3 | h3
    · exact h3
    · exfalso
      have hx₂ : h x₂ = x₂ := by rw [← h3]; exact hgfix x₁ hx₁
      have hgx₂ : (g : Equiv.Perm (Omega K)) x₂ = x₁ := by
        rcases hmemfix _ (hgfix x₂ hx₂) with h4 | h4
        · exact h4
        · exfalso
          apply hx12
          apply (g : Equiv.Perm (Omega K)).injective
          rw [h3, h4]
      have hsq : ∀ k : ℕ, ((g : Equiv.Perm (Omega K)) ^ (2 * k)) x₁ = x₁ := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          rw [show 2 * (k + 1) = 2 * k + 2 by ring, pow_add, Equiv.Perm.mul_apply, pow_two,
            Equiv.Perm.mul_apply, h3, hgx₂, ih]
      obtain ⟨k, hk⟩ := hXodd
      have hone : ((g : Equiv.Perm (Omega K)) ^ (2 * k + 1)) x₁ = x₁ := by
        rw [← hk, ← hgo, pow_orderOf_eq_one, Equiv.Perm.one_apply]
      rw [pow_succ', Equiv.Perm.mul_apply, hsq k, h3] at hone
      exact hx12 hone.symm
  refine ⟨x₁, fun y hy => ?_⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨y, hy⟩)
  have hk' : (g : Equiv.Perm (Omega K)) ^ k = y := by rw [← Subgroup.coe_zpow, hk]
  rw [← hk']
  exact Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hgx₁ k

theorem even_mul_sq_sub_one_div_two {q : ℕ} (hq : Odd q) : Even (q * (q ^ 2 - 1) / 2) := by
  obtain ⟨k, rfl⟩ := hq
  have h1 : (2 * k + 1) ^ 2 - 1 = 4 * (k * (k + 1)) := by
    rw [Nat.sub_eq_iff_eq_add (Nat.one_le_pow _ _ (by omega))]
    ring
  rw [h1, show (2 * k + 1) * (4 * (k * (k + 1))) = 2 * (2 * ((2 * k + 1) * (k * (k + 1)))) by ring,
    Nat.mul_div_cancel_left _ (by norm_num)]
  exact even_two_mul _

theorem even_mul_sq_sub_one {q : ℕ} (hq : Odd q) : Even (q * (q ^ 2 - 1)) := by
  have h1 : Even (q ^ 2 - 1) := Nat.Odd.sub_odd (hq.pow) odd_one
  exact h1.mul_left q

theorem relIndex_coordinateG_coordinateD {p f : ℕ} (hp : p.Prime) (hpodd : Odd p)
    (hK : Nat.card K = p ^ f) : (coordinateG K).relIndex (coordinateD K) = 2 := by
  have hf : f ≠ 0 := by
    rintro rfl
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    rw [hK, pow_zero] at h1
    exact lt_irrefl 1 h1
  have hKodd : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card K) :=
    ⟨p, f, hp, hpodd, Nat.one_le_iff_ne_zero.mpr hf, hK⟩
  have hqodd : Odd (Nat.card K) := hK ▸ hpodd.pow
  have hD : Nat.card (coordinateD K) = Nat.card K * (Nat.card K ^ 2 - 1) := by
    rw [← Nat.card_congr (pglEquivCoordinateD K).toEquiv, CFSG.GorensteinWalter.pgl2_card_formula]
  have hG : Nat.card (coordinateG K) = Nat.card K * (Nat.card K ^ 2 - 1) / 2 := by
    rw [← Nat.card_congr (pslEquivCoordinateG K).toEquiv,
      CFSG.GorensteinWalter.psl2_card_formula K hKodd]
  have h1 := ((coordinateG K).subgroupOf (coordinateD K)).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (coordinateG_le_D K)).toEquiv, hG, hD] at h1
  obtain ⟨c, hc⟩ := even_mul_sq_sub_one hqodd
  have hq3 : 3 ≤ Nat.card K := by
    have := hp.two_le
    rcases hpodd with ⟨k, hk⟩
    have : p ≤ p ^ f := Nat.le_self_pow hf p
    omega
  have hpos : 0 < c := by
    have : 0 < Nat.card K * (Nat.card K ^ 2 - 1) := by
      have : 1 < Nat.card K ^ 2 := by nlinarith
      exact Nat.mul_pos (by omega) (by omega)
    omega
  rw [hc, show c + c = 2 * c by ring, Nat.mul_div_cancel_left _ (by norm_num)] at h1
  change ((coordinateG K).subgroupOf (coordinateD K)).index = 2
  exact Nat.eq_of_mul_eq_mul_left hpos (by linarith)

theorem le_coordinateG_of_odd {p f : ℕ} (hp : p.Prime) (hpodd : Odd p) (hK : Nat.card K = p ^ f)
    {X : Subgroup (Equiv.Perm (Omega K))} (hXD : X ≤ coordinateD K) (hX : Odd (Nat.card X)) :
    X ≤ coordinateG K := by
  intro x hx
  have hidx := relIndex_coordinateG_coordinateD hp hpodd hK
  have hodd : Odd (orderOf (⟨x, hXD hx⟩ : coordinateD K)) := by
    rw [Subgroup.orderOf_mk]
    exact hX.of_dvd_nat (Subgroup.orderOf_dvd_natCard X hx)
  exact Subgroup.mem_subgroupOf.mp (mem_of_index_two_of_odd hidx hodd)

theorem odd_subgroup_fixes_point_or_cyclic
    {K : Type} [Field K] [Finite K] {p f : ℕ}
    (hp : p.Prime) (hpodd : Odd p) (hK : Nat.card K = p ^ f)
    (X : Subgroup (Equiv.Perm (Omega K))) (hXD : X ≤ coordinateD K) (hX : Odd (Nat.card X)) :
    (∃ x : Omega K, ∀ g ∈ X, g x = x) ∨ (IsCyclic X ∧ Nat.card X ∣ (Nat.card K + 1) / 2) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hXG : X ≤ coordinateG K := le_coordinateG_of_odd hp hpodd hK hXD hX
  set ψ : coordinateG K →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K :=
    (pslEquivCoordinateG K).symm.toMonoidHom with hψdef
  set H : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) :=
    (X.subgroupOf (coordinateG K)).map ψ with hHdef
  let e : X ≃* H := (Subgroup.subgroupOfEquivOfLe hXG).symm.trans
    ((X.subgroupOf (coordinateG K)).equivMapOfInjective ψ (pslEquivCoordinateG K).symm.injective)
  have hHcard : Nat.card H = Nat.card X := (Nat.card_congr e.toEquiv).symm
  have hHodd : Odd (Nat.card H) := hHcard ▸ hX
  have hnoteven : ¬ Even (Nat.card H) := Nat.not_even_iff_odd.mpr hHodd
  have hqodd : Odd (Nat.card K) := hK ▸ hpodd.pow
  have hgcd : Nat.gcd (Nat.card K - 1) 2 = 2 := by
    obtain ⟨k, hk⟩ := hqodd
    rw [show Nat.card K - 1 = 2 * k by omega]
    exact Nat.gcd_mul_right_left k 2
  have hfixed_of_bot : X = ⊥ → ∃ x : Omega K, ∀ g ∈ X, g x = x := fun hbot =>
    ⟨none, fun g hg => by rw [hbot, Subgroup.mem_bot] at hg; rw [hg]; rfl⟩
  have he_pow : ∀ (x : X) (k : ℕ), e x ^ k = 1 → (x : Equiv.Perm (Omega K)) ^ k = 1 := by
    intro x k hk
    rw [← map_pow, map_eq_one_iff _ e.injective] at hk
    exact congrArg Subtype.val hk
  rcases CFSG.Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification hK H with
    hEA | ⟨z, hz, hzc, hcyc⟩ | ⟨z, -, hzc, -⟩ | ⟨-, ⟨eA4⟩⟩ | ⟨-, ⟨eS4⟩⟩ | ⟨-, ⟨eA5⟩⟩ |
      ⟨m, t, -, ht, N, Cc, hNn, hNea, hNcard, hCcyc, hCcard, hdisj, hsup⟩ |
      ⟨m, hm0, -, ⟨eP⟩⟩ | ⟨m, hm0, -, ⟨eP⟩⟩
  ·
    left
    by_cases hX1 : X = ⊥
    · exact hfixed_of_bot hX1
    obtain ⟨⟨u, huX⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hX1
    have hu1' : u ≠ 1 := fun h => hu1 (Subtype.ext h)
    refine exists_fixed_of_normal_elementary hp hpodd hK hXD le_rfl
      (fun g hg n hn => X.mul_mem (X.mul_mem hg hn) (X.inv_mem hg)) (fun n hn => ?_)
      (fun a ha b hb => ?_) huX hu1'
    · apply he_pow ⟨n, hn⟩ p
      exact (Monoid.exponent_dvd_iff_forall_pow_eq_one).mp
        (IsElementaryAbelian.exponent_dvd_p p H) (e ⟨n, hn⟩)
    · have hc : e ⟨a, ha⟩ * e ⟨b, hb⟩ = e ⟨b, hb⟩ * e ⟨a, ha⟩ :=
        hEA.toIsMulCommutative.is_comm.comm _ _
      rw [← map_mul, ← map_mul] at hc
      exact congrArg Subtype.val (e.injective hc)
  ·
    have hXc : IsCyclic X :=
      isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
    rw [hgcd] at hz
    rcases hz with hz | hz
    · left
      refine exists_fixed_of_cyclic_dvd hXD hXc hX ?_
      rw [← hHcard, hzc]
      exact hz.trans (Nat.div_dvd_of_dvd (by
        obtain ⟨k, hk⟩ := hqodd
        exact ⟨k, by omega⟩))
    · right
      exact ⟨hXc, by rw [← hHcard, hzc]; exact hz⟩
  ·
    exact absurd ⟨z, by rw [hzc]; ring⟩ hnoteven
  ·
    exfalso
    apply hnoteven
    rw [Nat.card_congr eA4.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    decide
  ·
    exfalso
    apply hnoteven
    rw [Nat.card_congr eS4.toEquiv, Nat.card_perm, Nat.card_fin]
    decide
  ·
    exfalso
    apply hnoteven
    rw [Nat.card_congr eA5.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    decide
  ·
    left
    by_cases hN1 : N = ⊥
    ·
      have hCtop : Cc = ⊤ := by rw [hN1, bot_sup_eq] at hsup; exact hsup
      have hHc : IsCyclic H := by
        have : IsCyclic (⊤ : Subgroup H) := hCtop ▸ hCcyc
        exact isCyclic_of_surjective (Subgroup.topEquiv.toMonoidHom) Subgroup.topEquiv.surjective
      have hXc : IsCyclic X :=
        isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
      refine exists_fixed_of_cyclic_dvd hXD hXc hX ?_
      have hHt : Nat.card H = t := by
        rw [← hCcard, hCtop, Subgroup.card_top]
      rw [← hHcard, hHt]
      rw [← hK] at ht
      rw [hgcd] at ht
      exact ht.trans (Nat.div_dvd_of_dvd (by
        obtain ⟨k, hk⟩ := hqodd
        exact ⟨k, by omega⟩))
    ·
      obtain ⟨⟨n₀, hn₀N⟩, hn₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hN1
      have hn₀1' : n₀ ≠ 1 := fun h => hn₀1 (Subtype.ext h)
      let N' : Subgroup (Equiv.Perm (Omega K)) := (N.map e.symm.toMonoidHom).map X.subtype
      have hN'X : N' ≤ X := Subgroup.map_subtype_le _
      have hmemN' : ∀ n ∈ N, ((e.symm n : X) : Equiv.Perm (Omega K)) ∈ N' :=
        fun n hn => ⟨e.symm n, ⟨n, hn, rfl⟩, rfl⟩
      have hNmem : ∀ y ∈ N', ∃ n ∈ N, y = ((e.symm n : X) : Equiv.Perm (Omega K)) := by
        rintro _ ⟨_, ⟨n, hn, rfl⟩, rfl⟩
        exact ⟨n, hn, rfl⟩
      have := hNea
      refine exists_fixed_of_normal_elementary hp hpodd hK hXD hN'X ?_ ?_ ?_ (hmemN' _ hn₀N) ?_
      · intro g hg y hy
        obtain ⟨n, hn, rfl⟩ := hNmem y hy
        have hc : e ⟨g, hg⟩ * n * (e ⟨g, hg⟩)⁻¹ ∈ N := hNn.conj_mem n hn _
        have h1 := hmemN' _ hc
        simpa [map_mul, map_inv] using h1
      · intro y hy
        obtain ⟨n, hn, rfl⟩ := hNmem y hy
        apply he_pow (e.symm n) p
        rw [MulEquiv.apply_symm_apply]
        exact elemPow_eq_one_of_isElementaryAbelian (p := p) (A := N) n hn
      · intro a ha b hb
        obtain ⟨n, hn, rfl⟩ := hNmem a ha
        obtain ⟨n', hn', rfl⟩ := hNmem b hb
        have hc : (⟨n, hn⟩ : N) * ⟨n', hn'⟩ = ⟨n', hn'⟩ * ⟨n, hn⟩ :=
          hNea.toIsMulCommutative.is_comm.comm _ _
        have hc' : n * n' = n' * n := congrArg Subtype.val hc
        have h2 : e.symm n * e.symm n' = e.symm n' * e.symm n := by
          rw [← map_mul, hc', map_mul]
        exact congrArg Subtype.val h2
      · intro h
        apply hn₀1'
        have h2 : e.symm n₀ = 1 := Subtype.ext h
        rw [map_eq_one_iff _ e.symm.injective] at h2
        exact h2
  ·
    exfalso
    apply hnoteven
    have hm1 : Odd (p ^ m) := hpodd.pow
    have hcardF : Nat.card (GaloisField p m) = p ^ m := GaloisField.card p m hm0
    have hodd' : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card (GaloisField p m)) :=
      ⟨p, m, hp, hpodd, Nat.one_le_iff_ne_zero.mpr hm0, hcardF⟩
    rw [Nat.card_congr eP.toEquiv, CFSG.GorensteinWalter.psl2_card_formula _ hodd', hcardF]
    exact even_mul_sq_sub_one_div_two hm1
  ·
    exfalso
    apply hnoteven
    have hcardF : Nat.card (GaloisField p m) = p ^ m := GaloisField.card p m hm0
    rw [Nat.card_congr eP.toEquiv, CFSG.GorensteinWalter.pgl2_card_formula, hcardF]
    exact even_mul_sq_sub_one hpodd.pow

end CFSG.Semidihedral.FixedCoreNontrivial
