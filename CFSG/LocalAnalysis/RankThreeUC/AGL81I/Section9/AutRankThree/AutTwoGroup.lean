module

public import CFSG.Permutation.FiveTransitive.CharacteristicAutomorphism
public import CFSG.Sporadic.Schreier.RuElemAut
public import CFSG.LocalAnalysis.SignalizerFunctor.TwoPrimeOrderSolvability

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open scoped commutatorElement

open FiveTransitive.CharacteristicAutomorphism (restrict quotient quotient_apply_mk)

section Helpers

variable {C : Type} [Group C]

theorem apply_eq_of_mem_center_of_isPerfect (hZ : IsCyclic (Subgroup.center C))
    {G : Subgroup (MulAut C)} (hG : Group.IsPerfect G) {σ : MulAut C} (hσ : σ ∈ G) {z : C}
    (hz : z ∈ Subgroup.center C) : σ z = z := by
  let f := (restrict (Subgroup.center C)).comp G.subtype
  have : Group.IsPerfect f.range := Group.IsPerfect.range f
  have : IsMulCommutative f.range := ⟨⟨fun a b => Subtype.ext <| by
    obtain ⟨m, hm⟩ := (a : MulAut (Subgroup.center C)).toMonoidHom.map_cyclic
    obtain ⟨n, hn⟩ := (b : MulAut (Subgroup.center C)).toMonoidHom.map_cyclic
    simp only [MulEquiv.coe_toMonoidHom] at hm hn
    ext w
    simp only [Subgroup.coe_mul, MulAut.mul_apply, hm, hn]
    rw [← zpow_mul, ← zpow_mul, mul_comm]⟩⟩
  have h1 : f ⟨σ, hσ⟩ = 1 :=
    congrArg Subtype.val (Subsingleton.elim (⟨f ⟨σ, hσ⟩, ⟨σ, hσ⟩, rfl⟩ : f.range) 1)
  have := congrArg (fun a : MulAut (Subgroup.center C) => ((a ⟨z, hz⟩ : Subgroup.center C) : C)) h1
  simpa [f] using this

theorem center_quot_sq_eq_one (hsq : ∀ x : C, x ^ 2 ∈ Subgroup.center C)
    (e : C ⧸ Subgroup.center C) : e ^ 2 = 1 := by
  induction e using QuotientGroup.induction_on with
  | H x => rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact hsq x

theorem center_quot_mul_comm (hsq : ∀ x : C, x ^ 2 ∈ Subgroup.center C)
    (a b : C ⧸ Subgroup.center C) : a * b = b * a := by
  have hi : ∀ e : C ⧸ Subgroup.center C, e⁻¹ = e := fun e =>
    inv_eq_of_mul_eq_one_right (by rw [← sq]; exact center_quot_sq_eq_one hsq e)
  calc a * b = (a * b)⁻¹ := (hi _).symm
    _ = b * a := by rw [mul_inv_rev, hi, hi]

theorem commutatorElement_mem_center_of_sq_mem (hsq : ∀ x : C, x ^ 2 ∈ Subgroup.center C)
    (a b : C) : ⁅a, b⁆ ∈ Subgroup.center C := by
  have := map_commutatorElement (QuotientGroup.mk' (Subgroup.center C)) a b
  simp only [QuotientGroup.mk'_apply] at this
  rw [← QuotientGroup.eq_one_iff, this, commutatorElement_eq_one_iff_mul_comm]
  exact center_quot_mul_comm hsq _ _

theorem commutatorElement_mul_right_of_commutator_mem_center {x a b : C}
    (hb : ⁅x, b⁆ ∈ Subgroup.center C) : ⁅x, a * b⁆ = ⁅x, a⁆ * ⁅x, b⁆ := by
  have hc := Subgroup.mem_center_iff.mp hb a⁻¹
  calc ⁅x, a * b⁆ = x * a * x⁻¹ * (⁅x, b⁆ * a⁻¹) := by simp only [commutatorElement_def]; group
    _ = ⁅x, a⁆ * ⁅x, b⁆ := by rw [← hc]; simp only [commutatorElement_def]; group

private lemma commutatorElement_apply_right (hsq : ∀ x : C, x ^ 2 ∈ Subgroup.center C)
    {σ : MulAut C} (hσZ : ∀ z ∈ Subgroup.center C, σ z = z) {x : C}
    (hx : x⁻¹ * σ x ∈ Subgroup.center C) (w : C) : ⁅x, σ w⁆ = ⁅x, w⁆ := by
  obtain ⟨z₀, hz₀, hσx⟩ : ∃ z₀ ∈ Subgroup.center C, σ x = x * z₀ := ⟨_, hx, by group⟩
  have hz := Subgroup.mem_center_iff.mp hz₀ (σ w)
  calc ⁅x, σ w⁆ = x * (σ w * z₀) * z₀⁻¹ * x⁻¹ * (σ w)⁻¹ := by
        simp only [commutatorElement_def]; group
    _ = ⁅x * z₀, σ w⁆ := by rw [hz]; simp only [commutatorElement_def]; group
    _ = ⁅σ x, σ w⁆ := by rw [hσx]
    _ = σ ⁅x, w⁆ := (map_commutatorElement σ x w).symm
    _ = ⁅x, w⁆ := hσZ _ (commutatorElement_mem_center_of_sq_mem hsq x w)

private lemma commutatorElement_eq_one_of_norm (hsq : ∀ x : C, x ^ 2 ∈ Subgroup.center C)
    {σ : MulAut C} (hσZ : ∀ z ∈ Subgroup.center C, σ z = z) {x : C}
    (hx : x⁻¹ * σ x ∈ Subgroup.center C) (y : C)
    (hN : ⁅x, y * σ y * σ (σ y) * σ (σ (σ y)) * σ (σ (σ (σ y))) * σ (σ (σ (σ (σ y)))) *
      σ (σ (σ (σ (σ (σ y)))))⁆ = 1) : ⁅x, y⁆ = 1 := by
  have hm : ∀ a b : C, ⁅x, a * b⁆ = ⁅x, a⁆ * ⁅x, b⁆ := fun a b =>
    commutatorElement_mul_right_of_commutator_mem_center
      (commutatorElement_mem_center_of_sq_mem hsq x b)
  simp only [hm, commutatorElement_apply_right hsq hσZ hx] at hN
  have h2 : ⁅x, y⁆ * ⁅x, y⁆ = 1 := by
    rw [← hm, ← sq, commutatorElement_eq_one_iff_mul_comm]
    exact Subgroup.mem_center_iff.mp (hsq y) x
  rwa [h2, one_mul, h2, one_mul, h2, one_mul] at hN

theorem mul_comm_of_trivial_on_center_quot {σ τ : MulAut C}
    (hσZ : ∀ z ∈ Subgroup.center C, σ z = z)
    (hτZ : ∀ z ∈ Subgroup.center C, τ z = z) (hσ : ∀ x : C, x⁻¹ * σ x ∈ Subgroup.center C)
    (hτ : ∀ x : C, x⁻¹ * τ x ∈ Subgroup.center C) : σ * τ = τ * σ := by
  ext x
  obtain ⟨a, ha, hax⟩ : ∃ a ∈ Subgroup.center C, σ x = x * a := ⟨_, hσ x, by group⟩
  obtain ⟨b, hb, hbx⟩ : ∃ b ∈ Subgroup.center C, τ x = x * b := ⟨_, hτ x, by group⟩
  rw [MulAut.mul_apply, MulAut.mul_apply, hbx, map_mul, hσZ b hb, hax, map_mul, hτZ a ha, hbx,
    mul_assoc, mul_assoc, Subgroup.mem_center_iff.mp ha b]

private lemma card_mulAut_quot [Finite C] (hC : IsPGroup 2 C)
    (hsq : ∀ x : C, x ^ 2 ∈ Subgroup.center C)
    (hcard : Nat.card (C ⧸ Subgroup.center C) ≤ 16) :
    Nat.card (MulAut (C ⧸ Subgroup.center C)) ∣ 168 ∨
      (Nat.card (C ⧸ Subgroup.center C) = 16 ∧
        Nat.card (MulAut (C ⧸ Subgroup.center C)) ∣ 20160) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (hC.to_quotient (Subgroup.center C)).exists_card_eq
  have hn4 : n ≤ 4 := (Nat.pow_le_pow_iff_right (by norm_num)).1 (hn ▸ hcard : 2 ^ n ≤ 2 ^ 4)
  rw [CFSG.Sporadic.RuSchreier.ru_card_mulAut_elementary (center_quot_mul_comm hsq)
    (center_quot_sq_eq_one hsq) hn, hn]
  interval_cases n <;> simp [Fin.prod_univ_succ]

private lemma prime_eq_of_dvd_20160 {d : ℕ} (hd : d.Prime) (h : d ∣ 20160) :
    d = 2 ∨ d = 3 ∨ d = 5 ∨ d = 7 := by
  have h' : d ∣ 2 ^ 6 * 3 ^ 2 * 5 * 7 := h
  have hq : ∀ q : ℕ, q.Prime → ∀ k, d ∣ q ^ k → d = q := fun q hq k hk =>
    (Nat.prime_dvd_prime_iff_eq hd hq).1 (hd.dvd_of_dvd_pow hk)
  rcases (Nat.Prime.dvd_mul hd).1 h' with h1 | h7
  · rcases (Nat.Prime.dvd_mul hd).1 h1 with h2 | h5
    · rcases (Nat.Prime.dvd_mul hd).1 h2 with h3 | h4
      · exact Or.inl (hq 2 Nat.prime_two 6 h3)
      · exact Or.inr (Or.inl (hq 3 Nat.prime_three 2 h4))
    · exact Or.inr (Or.inr (Or.inl (hq 5 (by norm_num) 1 (by simpa using h5))))
  · exact Or.inr (Or.inr (Or.inr (hq 7 (by norm_num) 1 (by simpa using h7))))

private lemma exists_unique_fixed {E : Type*} [Group E] [Finite E] (hE : Nat.card E = 16)
    {g : MulAut E} (hg : orderOf g = 7) :
    ∃ u : E, u ≠ 1 ∧ g u = u ∧ ∀ e : E, g e = e → e = 1 ∨ e = u := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let F := FixedPoints.subgroup (Subgroup.zpowers g) E
  have hmem : ∀ e, e ∈ F ↔ g e = e := fun e => by
    refine ⟨fun h => h ⟨g, Subgroup.mem_zpowers g⟩, fun h m => ?_⟩
    have hle : Subgroup.zpowers g ≤ MulAction.stabilizer (MulAut E) e :=
      (Subgroup.zpowers_le).2 h
    exact hle m.2
  have hp : IsPGroup 7 (Subgroup.zpowers g) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hg, pow_one])
  have hmod : Nat.card E ≡ Nat.card F [MOD 7] := hp.card_modEq_card_fixedPoints E
  have hne : Nat.card F ≠ 16 := fun h16 => by
    have hF := Subgroup.eq_top_of_card_eq F (h16.trans hE.symm)
    have h1 : g = 1 := MulEquiv.ext fun e => (hmem e).1 (hF ▸ Subgroup.mem_top e)
    rw [h1, orderOf_one] at hg
    exact absurd hg (by norm_num)
  obtain ⟨k, hk, hkF⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
    (by simpa [hE] using F.card_subgroup_dvd_card : Nat.card F ∣ 2 ^ 4)
  have h2 : Nat.card F = 2 := by
    rw [hE, hkF] at hmod; rw [hkF] at hne ⊢
    interval_cases k <;> simp_all [Nat.ModEq]
  obtain ⟨⟨u, hu⟩, hu1, huniq⟩ := (Nat.card_eq_two_iff' (1 : F)).1 h2
  refine ⟨u, fun h => hu1 (Subtype.ext h), (hmem u).1 hu, fun e he => ?_⟩
  by_cases h1 : e = 1
  · exact Or.inl h1
  · exact Or.inr (congrArg Subtype.val
      (huniq ⟨e, (hmem e).2 he⟩ fun h => h1 (congrArg Subtype.val h)))

private lemma commutatorElement_eq_one_of_mk {x N : C}
    (h : (N : C ⧸ Subgroup.center C) = 1 ∨ (N : C ⧸ Subgroup.center C) = x) : ⁅x, N⁆ = 1 := by
  rw [commutatorElement_eq_one_iff_mul_comm]
  rcases h with h | h
  · exact Subgroup.mem_center_iff.1 ((QuotientGroup.eq_one_iff N).1 h) x
  · have hc := Subgroup.mem_center_iff.1 (QuotientGroup.eq.1 h) N
    calc x * N = N * (N⁻¹ * x) * N := by group
      _ = N * (N * (N⁻¹ * x)) := by rw [mul_assoc, ← hc]
      _ = N * x := by group

private lemma false_of_orderOf_eq_seven [Finite C] (hsq : ∀ x : C, x ^ 2 ∈ Subgroup.center C)
    (h16 : Nat.card (C ⧸ Subgroup.center C) = 16) {σ : MulAut C}
    (hσZ : ∀ z ∈ Subgroup.center C, σ z = z)
    (h7 : orderOf (quotient (Subgroup.center C) σ) = 7) : False := by
  set g := quotient (Subgroup.center C) σ
  have hg : ∀ w : C, g (w : C ⧸ Subgroup.center C) = (σ w : C ⧸ Subgroup.center C) :=
    fun w => quotient_apply_mk _ σ w
  have hg7 : ∀ e, g (g (g (g (g (g (g e)))))) = e := fun e => by
    have h := pow_orderOf_eq_one g
    rw [h7] at h
    simpa [pow_succ, MulAut.mul_apply] using DFunLike.congr_fun h e
  obtain ⟨u, hu1, hgu, huniq⟩ := exists_unique_fixed h16 h7
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective u
  have hx : x⁻¹ * σ x ∈ Subgroup.center C := by
    rw [← QuotientGroup.eq]; exact ((hg x).symm.trans hgu).symm
  refine hu1 ((QuotientGroup.eq_one_iff x).2 (Subgroup.mem_center_iff.2 fun y => ?_))
  refine (commutatorElement_eq_one_iff_mul_comm.1
    (commutatorElement_eq_one_of_norm hsq hσZ hx y (commutatorElement_eq_one_of_mk ?_))).symm
  refine huniq _ ?_
  simp only [QuotientGroup.mk_mul, ← hg]
  simp only [map_mul, hg7]
  rw [center_quot_mul_comm hsq _ (y : C ⧸ Subgroup.center C)]
  simp only [mul_assoc]

private lemma isSolvable_range [Finite C] (hC : IsPGroup 2 C) (hZ : IsCyclic (Subgroup.center C))
    (hsq : ∀ x : C, x ^ 2 ∈ Subgroup.center C)
    (hcard : Nat.card (C ⧸ Subgroup.center C) ≤ 16)
    {G : Subgroup (MulAut C)} (hG : Group.IsPerfect G) (h3 : Nat.Coprime 3 (Nat.card G)) :
    Group.IsSolvable ((quotient (Subgroup.center C)).comp G.subtype).range := by
  set f := (quotient (Subgroup.center C)).comp G.subtype
  have h3R : ¬ 3 ∣ Nat.card f.range := fun h =>
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 h3 (h.trans (Subgroup.card_range_dvd f))
  have hdvd := Subgroup.card_subgroup_dvd_card f.range
  rcases card_mulAut_quot hC hsq hcard with h168 | ⟨h16, h20160⟩
  · refine CFSG.SignalizerFunctor.Helpers.two_prime_order_solvable _ 2 7 Nat.prime_two
      (by norm_num) fun d hd hdR => ?_
    have hd168 := hdR.trans (hdvd.trans h168)
    rcases prime_eq_of_dvd_20160 hd (hd168.trans (by norm_num)) with h | h | h | h
    · exact Or.inl h
    · exact absurd (h ▸ hdR) h3R
    · subst h; omega
    · exact Or.inr h
  · refine CFSG.SignalizerFunctor.Helpers.two_prime_order_solvable _ 2 5 Nat.prime_two
      (by norm_num) fun d hd hdR => ?_
    rcases prime_eq_of_dvd_20160 hd (hdR.trans (hdvd.trans h20160)) with h | h | h | h
    · exact Or.inl h
    · exact absurd (h ▸ hdR) h3R
    · exact Or.inr h
    · subst h
      have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
      obtain ⟨⟨_, ⟨σ, hσ⟩, rfl⟩, hr⟩ := exists_prime_orderOf_dvd_card' 7 hdR
      rw [← Subgroup.orderOf_coe] at hr
      exact (false_of_orderOf_eq_seven hsq h16
        (fun z hz => apply_eq_of_mem_center_of_isPerfect hZ hG hσ hz) hr).elim

private lemma quotient_eq_one [Finite C] (hC : IsPGroup 2 C) (hZ : IsCyclic (Subgroup.center C))
    (hsq : ∀ x : C, x ^ 2 ∈ Subgroup.center C)
    (hcard : Nat.card (C ⧸ Subgroup.center C) ≤ 16)
    {G : Subgroup (MulAut C)} (hG : Group.IsPerfect G) (h3 : Nat.Coprime 3 (Nat.card G))
    {σ : MulAut C} (hσ : σ ∈ G) : quotient (Subgroup.center C) σ = 1 := by
  let f := (quotient (Subgroup.center C)).comp G.subtype
  have := hG
  have : Group.IsPerfect f.range := Group.IsPerfect.range f
  have hsol := isSolvable_range hC hZ hsq hcard hG h3
  rcases subsingleton_or_nontrivial f.range with h | h
  · exact congrArg Subtype.val (Subsingleton.elim (⟨f ⟨σ, hσ⟩, MonoidHom.mem_range.2 ⟨_, rfl⟩⟩ : f.range) 1)
  · exact absurd hsol (Group.IsPerfect.not_isSolvable _)

end Helpers

theorem eq_bot_of_isPerfect_of_coprime_three {C : Type} [Group C] [Finite C]
    (hC : IsPGroup 2 C) (hZ : IsCyclic (Subgroup.center C))
    (hsq : ∀ x : C, x ^ 2 ∈ Subgroup.center C)
    (hcard : Nat.card (C ⧸ Subgroup.center C) ≤ 16)
    {G : Subgroup (MulAut C)} (hG : Group.IsPerfect G) (h3 : Nat.Coprime 3 (Nat.card G)) :
    G = ⊥ := by
  have := hG
  have hZfix : ∀ σ ∈ G, ∀ z ∈ Subgroup.center C, σ z = z := fun σ hσ z hz =>
    apply_eq_of_mem_center_of_isPerfect hZ hG hσ hz
  have htriv : ∀ σ ∈ G, ∀ x : C, x⁻¹ * σ x ∈ Subgroup.center C := fun σ hσ x => by
    have h := quotient_apply_mk (Subgroup.center C) σ x
    rw [quotient_eq_one hC hZ hsq hcard hG h3 hσ] at h
    simp only [MulAut.one_apply, QuotientGroup.mk'_apply] at h
    exact QuotientGroup.eq.1 h
  have : IsMulCommutative G := ⟨⟨fun a b => Subtype.ext (mul_comm_of_trivial_on_center_quot
    (hZfix a a.2) (hZfix b b.2) (htriv a a.2) (htriv b b.2))⟩⟩
  exact Subgroup.eq_bot_of_subsingleton G

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
