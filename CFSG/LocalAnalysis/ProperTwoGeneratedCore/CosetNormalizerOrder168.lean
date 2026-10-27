module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LinearAlgebra.LinearGroups.LinearTwo
public import CFSG.LocalAnalysis.ComponentInitial.CertSmallLinear

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.CosetNormalizer

open CFSG.ComponentClassification.CatalogueSchreierLinearTwo CFSG.LinearGroups
open CFSG.Assembly.LowTwoRank

local instance factPrimeSeven : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩

theorem translation_one_pow {K : Type*} [Field K] (n : ℕ) :
    translation K 1 ^ n = translation K n := by
  induction n with
  | zero =>
    refine Equiv.ext fun x => ?_
    cases x <;> simp
  | succ n ih =>
    rw [pow_succ, ih]
    refine Equiv.ext fun x => ?_
    cases x with
    | none => rfl
    | some x =>
      simp only [Equiv.Perm.mul_apply, translation_some, Nat.cast_succ]
      ring_nf

theorem exists_affine_of_mul_translation (σ : Equiv.Perm (Omega (ZMod 7))) (c : ZMod 7)
    (hσ : σ none = none) (hc : σ * translation (ZMod 7) 1 = translation (ZMod 7) c * σ) :
    ∃ d : ZMod 7, ∀ x : ZMod 7, σ (some x) = some (c * x + d) := by
  have hsome : ∀ x : ZMod 7, ∃ y, σ (some x) = some y := by
    intro x
    apply Option.ne_none_iff_exists'.mp
    intro h
    exact Option.some_ne_none x (σ.injective (h.trans hσ.symm))
  choose f hf using hsome
  have hstep : ∀ x, f (x + 1) = f x + c := by
    intro x
    have h := congrArg (fun τ : Equiv.Perm (Omega (ZMod 7)) => τ (some x)) hc
    simp only [Equiv.Perm.mul_apply, translation_some, hf] at h
    exact Option.some_inj.mp h
  have hform : ∀ n : ℕ, f n = f 0 + c * n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.cast_succ, hstep, ih]
      ring
  refine ⟨f 0, fun x => ?_⟩
  rw [hf, ← ZMod.natCast_zmod_val x, hform, add_comm]

theorem exists_affine_pow {K : Type*} [Field K] (σ : Equiv.Perm (Omega K)) {c d : K}
    (h : ∀ x : K, σ (some x) = some (c * x + d)) (n : ℕ) :
    ∃ e : K, ∀ x : K, (σ ^ n) (some x) = some (c ^ n * x + e) := by
  induction n with
  | zero => exact ⟨0, fun x => by simp⟩
  | succ n ih =>
    obtain ⟨e, he⟩ := ih
    refine ⟨c * e + d, fun x => ?_⟩
    rw [pow_succ', Equiv.Perm.mul_apply, he, h]
    congr 1
    ring

theorem pow_eq_one_of_affine {K : Type*} [Field K] (σ : Equiv.Perm (Omega K)) {c d : K}
    (h : ∀ x : K, σ (some x) = some (c * x + d)) {m : ℕ} (hm : σ ^ m = 1) : c ^ m = 1 := by
  obtain ⟨e, he⟩ := exists_affine_pow σ h m
  rw [hm] at he
  have h0 := he 0
  have h1 := he 1
  simp only [Equiv.Perm.one_apply, mul_zero, zero_add, mul_one, Option.some_inj] at h0 h1
  rw [← h0, add_zero] at h1
  exact h1.symm

theorem eq_one_or_two_or_four_of_pow_eq_one {c : ZMod 7} (hc : c ^ 21 = 1) :
    c = 1 ∨ c = 2 ∨ c = 4 := by
  revert c
  decide

theorem mem_coordinateG_of_affine (σ : Equiv.Perm (Omega (ZMod 7))) (hσ : σ none = none)
    {c d : ZMod 7} (hc : c = 1 ∨ c = 2 ∨ c = 4) (h : ∀ x, σ (some x) = some (c * x + d)) :
    σ ∈ coordinateG (ZMod 7) := by
  have hsq : ∃ s a : (ZMod 7)ˣ, (s : ZMod 7) = c ∧ s = a ^ 2 := by
    rcases hc with rfl | rfl | rfl
    · exact ⟨1, 1, rfl, by rw [one_pow]⟩
    · exact ⟨Units.mk0 2 (by decide), Units.mk0 3 (by decide), rfl,
        Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_mk0]; decide)⟩
    · exact ⟨Units.mk0 4 (by decide), Units.mk0 2 (by decide), rfl,
        Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_mk0]; decide)⟩
  obtain ⟨s, a, hs, hsa⟩ := hsq
  exact coordinateB_le_coordinateG (mem_coordinateB_iff_affine.mpr
    ⟨hσ, s, d, ⟨a, hsa⟩, fun x => by rw [h x, hs]⟩)

theorem mem_coordinateG_of_involution (σ : Equiv.Perm (Omega (ZMod 7)))
    (hinf : σ none = some 0) (hzero : σ (some 0) = none) (hinv : ∀ x, σ (σ x) = x)
    (hfree : ∀ x, σ x ≠ x)
    (hconj : ∀ x y : ZMod 7, σ (some x) = some y → σ (some (2 * x)) = some (4 * y)) :
    σ ∈ coordinateG (ZMod 7) := by
  obtain ⟨a, ha⟩ : ∃ a, σ (some 1) = some a := by
    apply Option.ne_none_iff_exists'.mp
    intro h
    exact absurd (σ.injective (h.trans hzero.symm)) (by decide)
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact absurd (σ.injective (ha.trans hinf.symm)) (by decide)
  have haa : σ (some a) = some 1 := by rw [← ha, hinv]
  have h2 := hconj 1 a ha
  have h4 := hconj 2 (4 * a) (by simpa using h2)
  have h2a := hconj a 1 haa
  have h4a := hconj (2 * a) 4 (by simpa using h2a)
  have hns : a = 3 ∨ a = 5 ∨ a = 6 := by
    have hcases : a = 1 ∨ a = 2 ∨ a = 4 ∨ a = 3 ∨ a = 5 ∨ a = 6 := by
      have key : ∀ b : ZMod 7, b ≠ 0 → b = 1 ∨ b = 2 ∨ b = 4 ∨ b = 3 ∨ b = 5 ∨ b = 6 := by
        decide
      exact key a ha0
    rcases hcases with rfl | rfl | rfl | h | h
    · exact absurd ha (hfree _)
    · have : σ (some 4) = some 4 := by
        rw [show (4 : ZMod 7) = 2 * 2 by decide, h4]
        decide
      exact absurd this (hfree _)
    · have : σ (some 2) = some 2 := by
        rw [show (2 : ZMod 7) = 2 * 1 by decide, h2]
        decide
      exact absurd this (hfree _)
    · exact Or.inl h
    · exact Or.inr h
  have hval : ∀ x : ZMod 7, x ≠ 0 → σ (some x) = some (a * x⁻¹) := by
    have hdouble : ∀ x : ZMod 7, x ≠ 0 → σ (some x) = some (a * x⁻¹) →
        σ (some (2 * x)) = some (a * (2 * x)⁻¹) := by
      intro x _ hx
      rw [hconj x _ hx, mul_inv, show (2 : ZMod 7)⁻¹ = 4 from
        inv_eq_of_mul_eq_one_right (by decide)]
      congr 1
      ring
    have h1 : σ (some 1) = some (a * 1⁻¹) := by rw [inv_one, mul_one, ha]
    have hA : σ (some a) = some (a * a⁻¹) := by rw [mul_inv_cancel₀ ha0, haa]
    have hcover : ∀ x : ZMod 7, x ≠ 0 →
        x = 1 ∨ x = 2 * 1 ∨ x = 2 * (2 * 1) ∨ x = a ∨ x = 2 * a ∨ x = 2 * (2 * a) := by
      have key : ∀ b : ZMod 7, (b = 3 ∨ b = 5 ∨ b = 6) → ∀ x : ZMod 7, x ≠ 0 →
          x = 1 ∨ x = 2 * 1 ∨ x = 2 * (2 * 1) ∨ x = b ∨ x = 2 * b ∨ x = 2 * (2 * b) := by
        decide
      exact key a hns
    intro x hx
    have two_ne : (2 : ZMod 7) ≠ 0 := by decide
    rcases hcover x hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact h1
    · exact hdouble 1 one_ne_zero h1
    · exact hdouble _ (mul_ne_zero two_ne one_ne_zero) (hdouble 1 one_ne_zero h1)
    · exact hA
    · exact hdouble a ha0 hA
    · exact hdouble _ (mul_ne_zero two_ne ha0) (hdouble a ha0 hA)
  have hna : -a ≠ 0 := neg_ne_zero.mpr ha0
  have hσ : σ = multiplier (ZMod 7) (Units.mk0 (-a) hna) * inversion (ZMod 7) := by
    refine Equiv.ext fun x => ?_
    rcases x with _ | x
    · rw [hinf, Equiv.Perm.mul_apply, inversion_none, multiplier_some, mul_zero]
    · by_cases hx : x = 0
      · rw [hx, hzero, Equiv.Perm.mul_apply, inversion_zero, multiplier_none]
      · rw [hval x hx, Equiv.Perm.mul_apply, inversion_nonzero _ x hx, multiplier_some,
          Units.val_mk0]
        exact congrArg some (neg_mul_neg a x⁻¹).symm
  have hsq : ∃ r : (ZMod 7)ˣ, Units.mk0 (-a) hna = r ^ 2 := by
    rcases hns with rfl | rfl | rfl
    · exact ⟨Units.mk0 2 (by decide),
        Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_mk0]; decide)⟩
    · exact ⟨Units.mk0 3 (by decide),
        Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_mk0]; decide)⟩
    · exact ⟨1, Units.ext (by rw [Units.val_mk0, one_pow, Units.val_one]; decide)⟩
  obtain ⟨r, hr⟩ := hsq
  rw [hσ, hr]
  exact (coordinateG (ZMod 7)).mul_mem (multiplier_sq_mem_coordinateG r)
    (Subgroup.subset_closure (Set.mem_union_right _ rfl))

theorem card_coordinateG_zmod_seven : Nat.card (coordinateG (ZMod 7)) = 168 := by
  rw [← Nat.card_congr (pslEquivCoordinateG (ZMod 7)).toEquiv,
    CFSG.GorensteinWalter.psl2_card_formula (ZMod 7)
      ⟨7, 1, Nat.prime_seven, by decide, le_rfl, by rw [Nat.card_zmod, pow_one]⟩, Nat.card_zmod]
  norm_num

theorem exists_sylow_seven_labeling (G : Type*) [Group G] [Finite G] [IsSimpleGroup G]
    (hcard : Nat.card G = 168) (hsix : ∀ g : G, orderOf g ≠ 6) :
    Nat.card (Sylow 7 G) = 8 ∧ Function.Injective (MulAction.toPermHom G (Sylow 7 G)) ∧
      ∃ ℓ : Sylow 7 G ≃ Omega (ZMod 7),
        (ℓ.permCongrHom.toMonoidHom.comp (MulAction.toPermHom G (Sylow 7 G))).range ≤
          coordinateG (ZMod 7) := by
  have hP7 : ∀ P : Sylow 7 G, Nat.card (P : Subgroup G) = 7 := by
    intro P
    have hfac : (Nat.card G).factorization 7 = 1 := by
      rw [hcard, show (168 : ℕ) = 7 * 24 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
        Nat.Prime.factorization_self Nat.prime_seven,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    rw [P.card_eq_multiplicity, hfac, pow_one]
  have hnotnormal : ∀ P : Sylow 7 G, ¬ (P : Subgroup G).Normal := by
    intro P hP
    have := hP7 P
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (P : Subgroup G) with h | h
    · rw [h, Subgroup.card_bot] at this
      norm_num at this
    · rw [h, Subgroup.card_top, hcard] at this
      norm_num at this
  obtain ⟨P⟩ : Nonempty (Sylow 7 G) := inferInstance
  have hcard8 : Nat.card (Sylow 7 G) = 8 := by
    have hindex : (P : Subgroup G).index = 24 := by
      have h := (P : Subgroup G).card_mul_index
      rw [hP7 P, hcard] at h
      omega
    have hdvd := P.card_dvd_index
    rw [hindex] at hdvd
    have hmod : Nat.card (Sylow 7 G) % 7 = 1 := card_sylow_modEq_one 7 G
    have hne : Nat.card (Sylow 7 G) ≠ 1 := by
      intro h1
      have : Subsingleton (Sylow 7 G) := (Nat.card_eq_one_iff_unique.mp h1).1
      exact hnotnormal P (Sylow.normal_of_subsingleton P)
    have hle : Nat.card (Sylow 7 G) ≤ 24 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases h : Nat.card (Sylow 7 G) <;> first | rfl | omega
  have hfaith : Function.Injective (MulAction.toPermHom G (Sylow 7 G)) := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (MulAction.toPermHom G (Sylow 7 G)).ker with
      h | h
    · exact h
    · refine absurd ?_ (hnotnormal P)
      rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff]
      intro g _
      have hg : g ∈ (MulAction.toPermHom G (Sylow 7 G)).ker := h ▸ Subgroup.mem_top g
      rw [MonoidHom.mem_ker] at hg
      have hgP : g • P = P := by
        simpa using congrArg (fun σ : Equiv.Perm (Sylow 7 G) => σ P) hg
      exact Sylow.smul_eq_iff_mem_normalizer.mp hgP
  refine ⟨hcard8, hfaith, ?_⟩
  have hstab : ∀ Q : Sylow 7 G, Nat.card (MulAction.stabilizer G Q) = 21 := by
    intro Q
    have h := (MulAction.stabilizer G Q).card_mul_index
    rw [MulAction.index_stabilizer_of_transitive G Q, hcard8, hcard] at h
    omega
  have hstab_pow : ∀ (Q : Sylow 7 G) (b : G), b • Q = Q → b ^ 21 = 1 := by
    intro Q b hb
    have hmem : b ∈ MulAction.stabilizer G Q := hb
    rw [← hstab Q]
    exact orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard _ hmem)
  have hPnt : Nontrivial (P : Subgroup G) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hP7 P]; norm_num)
  have horder7 : ∀ x ∈ (P : Subgroup G), x ≠ 1 → orderOf x = 7 := by
    intro x hxP hx1
    have hdvd : orderOf x ∣ 7 := hP7 P ▸ Subgroup.orderOf_dvd_natCard _ hxP
    rcases (Nat.dvd_prime Nat.prime_seven).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hx1
    · exact h
  have hzpowers : ∀ x ∈ (P : Subgroup G), x ≠ 1 → Subgroup.zpowers x = (P : Subgroup G) := by
    intro x hxP hx1
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxP)
    rw [Nat.card_zpowers, horder7 x hxP hx1, hP7 P]
  obtain ⟨⟨p, hpP⟩, hp1⟩ := exists_ne (1 : (P : Subgroup G))
  have hp1' : p ≠ 1 := fun h => hp1 (Subtype.ext h)
  have hporder : orderOf p = 7 := horder7 p hpP hp1'
  have hppow : ∀ n : ℕ, p ^ n • P = P := fun n =>
    Sylow.smul_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer (Subgroup.pow_mem _ hpP n))
  have : Nontrivial (Sylow 7 G) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard8]; norm_num)
  obtain ⟨Q₀, hQ₀⟩ := exists_ne P
  let f : Omega (ZMod 7) → Sylow 7 G := fun x => x.elim P fun i => p ^ i.val • Q₀
  have hf_none : f none = P := rfl
  have hf_some : ∀ i : ZMod 7, f (some i) = p ^ i.val • Q₀ := fun _ => rfl
  have hf_pow : ∀ n : ℕ, p ^ n • Q₀ = f (some (n : ZMod 7)) := by
    intro n
    have hmod : p ^ (n % 7) = p ^ n := by rw [← hporder, pow_mod_orderOf]
    rw [hf_some, ZMod.val_natCast, hmod]
  have hf_zero : f (some 0) = Q₀ := by rw [hf_some, ZMod.val_zero, pow_zero, one_smul]
  have hf_ne : ∀ n : ℕ, p ^ n • Q₀ ≠ P := by
    intro n h
    exact hQ₀ (smul_left_cancel _ (h.trans (hppow n).symm))
  have hPQ : ∀ x ∈ (P : Subgroup G), x • Q₀ = Q₀ → x = 1 := by
    intro x hxP hxQ
    by_contra hx1
    have hxN : x ∈ Subgroup.normalizer ((Q₀ : Subgroup G) : Set G) :=
      Sylow.smul_eq_iff_mem_normalizer.mp hxQ
    have hxQ₀ : x ∈ (Q₀ : Subgroup G) :=
      ((IsPGroup.inf_normalizer_sylow P.isPGroup' Q₀).le ⟨hxP, hxN⟩).2
    have hle : (P : Subgroup G) ≤ Q₀ := by
      rw [← hzpowers x hxP hx1, Subgroup.zpowers_le]
      exact hxQ₀
    exact hQ₀ (Sylow.ext (Subgroup.eq_of_le_of_card_ge hle (by rw [hP7, hP7])).symm)
  have hf_inj : Function.Injective f := by
    rintro (_ | i) (_ | j) h
    · rfl
    · exact absurd h.symm (hf_ne _)
    · exact absurd h (hf_ne _)
    · rw [hf_some, hf_some] at h
      have h' : ((p ^ j.val)⁻¹ * p ^ i.val) • Q₀ = Q₀ := by
        rw [mul_smul, h, inv_smul_smul]
      have h1 := hPQ _ ((P : Subgroup G).mul_mem ((P : Subgroup G).inv_mem
        ((P : Subgroup G).pow_mem hpP _)) ((P : Subgroup G).pow_mem hpP _)) h'
      have h2 : p ^ i.val = p ^ j.val := (inv_mul_eq_one.mp h1).symm
      rw [pow_eq_pow_iff_modEq, hporder] at h2
      have hi := ZMod.val_lt i
      have hj := ZMod.val_lt j
      unfold Nat.ModEq at h2
      exact congrArg some (ZMod.val_injective 7 (by omega))
  have hf_bij : Function.Bijective f := hf_inj.bijective_of_nat_card_le (by
    rw [hcard8, Nat.card_eq_fintype_card, Fintype.card_option, ZMod.card])
  let ℓ : Sylow 7 G ≃ Omega (ZMod 7) := (Equiv.ofBijective f hf_bij).symm
  refine ⟨ℓ, ?_⟩
  set ρ := ℓ.permCongrHom.toMonoidHom.comp (MulAction.toPermHom G (Sylow 7 G)) with hρ
  have hρ_spec : ∀ (g : G) (x y : Omega (ZMod 7)), ρ g x = y ↔ g • f x = f y := by
    intro g x y
    change ℓ (g • ℓ.symm x) = y ↔ _
    rw [← Equiv.eq_symm_apply]
    rfl
  have hρ_inj : Function.Injective ρ := ℓ.permCongrHom.injective.comp hfaith
  have hρp : ρ p = translation (ZMod 7) 1 := by
    refine Equiv.ext fun x => (hρ_spec p x _).mpr ?_
    rcases x with _ | i
    · simpa [hf_none] using hppow 1
    · rw [translation_some, hf_some, ← mul_smul, ← pow_succ', hf_pow, Nat.cast_succ,
        ZMod.natCast_zmod_val]
  have hρpow : ∀ n : ℕ, ρ (p ^ n) = translation (ZMod 7) n := by
    intro n
    rw [map_pow, hρp, translation_one_pow]
  have haffine : ∀ b : G, ρ b none = none → ∃ c d : ZMod 7, (c = 1 ∨ c = 2 ∨ c = 4) ∧
      ∀ x, ρ b (some x) = some (c * x + d) := by
    intro b hb
    have hbP : b • P = P := (hρ_spec b none none).mp hb
    have hbN : b ∈ Subgroup.normalizer ((P : Subgroup G) : Set G) :=
      Sylow.smul_eq_iff_mem_normalizer.mp hbP
    have hbpb : b * p * b⁻¹ ∈ Subgroup.zpowers p := by
      rw [hzpowers p hpP hp1']
      exact (Subgroup.mem_normalizer_iff.mp hbN p).mp hpP
    obtain ⟨k, hk⟩ : ∃ k : ℕ, p ^ k = b * p * b⁻¹ := by
      rw [← mem_powers_iff_mem_zpowers] at hbpb
      exact (Submonoid.mem_powers_iff _ _).mp hbpb
    have hcomm : ρ b * translation (ZMod 7) 1 = translation (ZMod 7) (k : ZMod 7) * ρ b := by
      rw [← hρp, ← hρpow, ← map_mul, ← map_mul, hk]
      congr 1
      group
    obtain ⟨d, hd⟩ := exists_affine_of_mul_translation (ρ b) k hb hcomm
    refine ⟨k, d, eq_one_or_two_or_four_of_pow_eq_one ?_, hd⟩
    apply pow_eq_one_of_affine (ρ b) hd
    rw [← map_pow, hstab_pow P b hbP, map_one]
  have hB : ∀ b : G, ρ b none = none → ρ b ∈ coordinateG (ZMod 7) := by
    intro b hb
    obtain ⟨c, d, hc, hd⟩ := haffine b hb
    exact mem_coordinateG_of_affine (ρ b) hb hc hd
  obtain ⟨g₁, hg₁⟩ := MulAction.exists_smul_eq G P Q₀
  have hg₁0 : ρ g₁⁻¹ (some 0) = none := by
    rw [hρ_spec, hf_zero, hf_none, inv_smul_eq_iff, hg₁]
  obtain ⟨e, he⟩ : ∃ e, ρ g₁⁻¹ none = some e := by
    apply Option.ne_none_iff_exists'.mp
    intro h
    exact absurd ((ρ g₁⁻¹).injective (h.trans hg₁0.symm)) (by simp)
  set w := p ^ (-e).val * g₁⁻¹ with hw
  have hw_inf : ρ w none = some 0 := by
    rw [hw, map_mul, Equiv.Perm.mul_apply, he, hρpow, translation_some, ZMod.natCast_zmod_val]
    exact congrArg some (add_neg_cancel e)
  have hw_zero : ρ w (some 0) = none := by
    rw [hw, map_mul, Equiv.Perm.mul_apply, hg₁0, hρpow, translation_none]
  have hw2 : ρ (w ^ 2) none = none := by
    rw [map_pow, pow_two, Equiv.Perm.mul_apply, hw_inf, hw_zero]
  have hw2' : ρ (w ^ 2) (some 0) = some 0 := by
    rw [map_pow, pow_two, Equiv.Perm.mul_apply, hw_zero, hw_inf]
  have hw6 : w ^ 6 = 1 := by
    obtain ⟨c, d, hc, hd⟩ := haffine (w ^ 2) hw2
    have hd0 : d = 0 := by
      have := hd 0
      rw [hw2', mul_zero, zero_add] at this
      exact (Option.some_inj.mp this).symm
    have hc3 : c * (c * c) = 1 := by rcases hc with rfl | rfl | rfl <;> decide
    apply hρ_inj
    rw [map_one, show 6 = 2 * 3 by rfl, pow_mul, map_pow]
    refine Equiv.ext fun x => ?_
    have e1 : (ρ (w ^ 2) ^ 3) x = ρ (w ^ 2) (ρ (w ^ 2) (ρ (w ^ 2) x)) := by
      simp only [pow_succ, pow_zero, one_mul, Equiv.Perm.mul_apply]
    rw [e1, Equiv.Perm.one_apply]
    rcases x with _ | x
    · rw [hw2, hw2, hw2]
    · rw [hd, hd, hd, hd0]
      congr 1
      calc c * (c * (c * x + 0) + 0) + 0 = (c * (c * c)) * x := by ring
        _ = x := by rw [hc3, one_mul]
  have hworder : orderOf w = 2 := by
    have hdvd : orderOf w ∣ 6 := orderOf_dvd_of_pow_eq_one hw6
    have hne1 : w ≠ 1 := by
      intro h
      rw [h, map_one, Equiv.Perm.one_apply] at hw_inf
      exact absurd hw_inf (by simp)
    have hw3 : w ^ 3 ≠ 1 := by
      intro h
      have h3 : ρ (w ^ 3) none = none := by rw [h, map_one, Equiv.Perm.one_apply]
      rw [pow_succ', map_mul, Equiv.Perm.mul_apply, hw2, hw_inf] at h3
      exact absurd h3 (by simp)
    have hle : orderOf w ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases h : orderOf w
    · exact absurd h (orderOf_pos w).ne'
    · exact absurd (orderOf_eq_one_iff.mp h) hne1
    · rfl
    · have := pow_orderOf_eq_one w
      rw [h] at this
      exact absurd this hw3
    · norm_num at hdvd
    · norm_num at hdvd
    · exact absurd h (hsix w)
  have hwsq : w ^ 2 = 1 := by
    rw [← hworder]
    exact pow_orderOf_eq_one w
  have hw_inv : ∀ x, ρ w (ρ w x) = x := by
    intro x
    rw [← Equiv.Perm.mul_apply, ← map_mul, ← pow_two, hwsq, map_one, Equiv.Perm.one_apply]
  have hw_free : ∀ x, ρ w x ≠ x := by
    intro x hx
    have hmem : w ∈ MulAction.stabilizer G (f x) := (hρ_spec w x x).mp hx
    have hdvd := Subgroup.orderOf_dvd_natCard _ hmem
    rw [hstab, hworder] at hdvd
    norm_num at hdvd
  have hw_inv_none : ρ w⁻¹ none = some 0 := by
    rw [map_inv, Equiv.Perm.inv_eq_iff_eq, hw_zero]
  have hw_inv_zero : ρ w⁻¹ (some 0) = none := by
    rw [map_inv, Equiv.Perm.inv_eq_iff_eq, hw_inf]
  obtain ⟨c₀, hc₀⟩ := exists_prime_orderOf_dvd_card' (G := MulAction.stabilizer G P) 3
    (by rw [hstab P]; norm_num)
  have hcorder : orderOf (c₀ : G) = 3 := by rw [Subgroup.orderOf_coe, hc₀]
  have hcP : ρ c₀ none = none := (hρ_spec c₀ none none).mpr c₀.property
  have hδ₀ : ∃ c' : G, ρ c' none = none ∧
      ∃ d' : ZMod 7, ∀ x, ρ c' (some x) = some (2 * x + d') := by
    obtain ⟨a, d, ha, hd⟩ := haffine c₀ hcP
    rcases ha with rfl | rfl | rfl
    · exfalso
      have hc3 : (c₀ : G) ^ 3 = 1 := by
        rw [← hcorder]
        exact pow_orderOf_eq_one _
      have h0 : (ρ c₀ ^ 3) (some 0) = some 0 := by
        rw [← map_pow, hc3, map_one, Equiv.Perm.one_apply]
      have e1 : (ρ c₀ ^ 3) (some 0) = ρ c₀ (ρ c₀ (ρ c₀ (some 0))) := by
        simp only [pow_succ, pow_zero, one_mul, Equiv.Perm.mul_apply]
      rw [e1, hd, hd, hd] at h0
      have hd0 : d = 0 := by
        have key : ∀ d : ZMod 7, 1 * (1 * (1 * 0 + d) + d) + d = 0 → d = 0 := by decide
        exact key d (Option.some_inj.mp h0)
      have hρc : ρ c₀ = 1 := by
        refine Equiv.ext fun x => ?_
        rcases x with _ | x
        · exact hcP
        · rw [hd, hd0, one_mul, add_zero]
          rfl
      have hc1 : (c₀ : G) = 1 := hρ_inj (by rw [hρc, map_one])
      rw [hc1, orderOf_one] at hcorder
      norm_num at hcorder
    · exact ⟨c₀, hcP, d, hd⟩
    · refine ⟨(c₀ : G) ^ 2, by rw [map_pow, pow_two, Equiv.Perm.mul_apply, hcP, hcP],
        4 * d + d, fun x => ?_⟩
      rw [map_pow, pow_two, Equiv.Perm.mul_apply, hd, hd]
      congr 1
      have h16 : (4 : ZMod 7) * 4 = 2 := by decide
      calc 4 * (4 * x + d) + d = (4 * 4) * x + (4 * d + d) := by ring
        _ = 2 * x + (4 * d + d) := by rw [h16]
  obtain ⟨c', hc'P, d', hd'⟩ := hδ₀
  set δ := p ^ (-d').val * c' with hδ
  have hρδ : ρ δ = multiplier (ZMod 7) (Units.mk0 2 (by decide)) := by
    refine Equiv.ext fun x => ?_
    rcases x with _ | x
    · rw [hδ, map_mul, Equiv.Perm.mul_apply, hc'P, hρpow, translation_none, multiplier_none]
    · rw [hδ, map_mul, Equiv.Perm.mul_apply, hd', hρpow, translation_some, multiplier_some,
        Units.val_mk0, ZMod.natCast_zmod_val]
      exact congrArg some (add_neg_cancel_right _ _)
  have hδorder : orderOf δ = 3 := by
    rw [← orderOf_injective ρ hρ_inj δ, hρδ]
    apply orderOf_eq_prime
    · refine Equiv.ext fun x => ?_
      rcases x with _ | x
      · simp only [pow_succ, pow_zero, one_mul, Equiv.Perm.mul_apply, multiplier_none,
          Equiv.Perm.one_apply]
      · simp only [pow_succ, pow_zero, one_mul, Equiv.Perm.mul_apply, multiplier_some,
          Units.val_mk0, Equiv.Perm.one_apply]
        congr 1
        have h8 : (2 : ZMod 7) * (2 * 2) = 1 := by decide
        calc 2 * (2 * (2 * x)) = (2 * (2 * 2)) * x := by ring
          _ = x := by rw [h8, one_mul]
    · intro h
      have h1 := congrArg (fun σ : Equiv.Perm (Omega (ZMod 7)) => σ (some 1)) h
      simp only [multiplier_some, Units.val_mk0, mul_one, Equiv.Perm.one_apply,
        Option.some_inj] at h1
      exact absurd h1 (by decide)
  have hε_none : ρ (w * δ * w⁻¹) none = none := by
    rw [map_mul, map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hw_inv_none, hρδ,
      multiplier_some, mul_zero, hw_zero]
  have hε_zero : ρ (w * δ * w⁻¹) (some 0) = some 0 := by
    rw [map_mul, map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hw_inv_zero, hρδ,
      multiplier_none, hw_inf]
  obtain ⟨a', d'', ha', hd''⟩ := haffine (w * δ * w⁻¹) hε_none
  have hd''0 : d'' = 0 := by
    have := hd'' 0
    rw [hε_zero, mul_zero, zero_add] at this
    exact (Option.some_inj.mp this).symm
  have h4 : a' = 4 := by
    rcases ha' with rfl | rfl | rfl
    · exfalso
      have hε1 : ρ (w * δ * w⁻¹) = 1 := by
        refine Equiv.ext fun x => ?_
        rcases x with _ | x
        · exact hε_none
        · rw [hd'', hd''0, one_mul, add_zero]
          rfl
      have hε : w * δ * w⁻¹ = 1 := hρ_inj (by rw [hε1, map_one])
      have hδ1 : δ = 1 := by
        have := congrArg (fun y => w⁻¹ * y * w) hε
        simpa [mul_assoc] using this
      rw [hδ1, orderOf_one] at hδorder
      norm_num at hδorder
    · exfalso
      have hεδ : ρ (w * δ * w⁻¹) = ρ δ := by
        rw [hρδ]
        refine Equiv.ext fun x => ?_
        rcases x with _ | x
        · rw [hε_none, multiplier_none]
        · rw [hd'', hd''0, add_zero, multiplier_some, Units.val_mk0]
      have heq : w * δ * w⁻¹ = δ := hρ_inj hεδ
      have hcomm : Commute w δ := by
        change w * δ = δ * w
        calc w * δ = w * δ * w⁻¹ * w := by group
          _ = δ * w := by rw [heq]
      have h6 := hcomm.orderOf_mul_eq_mul_orderOf_of_coprime
        (by rw [hworder, hδorder]; norm_num)
      rw [hworder, hδorder] at h6
      exact hsix _ h6
    · rfl
  have hconj : ∀ x y : ZMod 7, ρ w (some x) = some y → ρ w (some (2 * x)) = some (4 * y) := by
    intro x y hxy
    have key : ρ w * ρ δ = ρ (w * δ * w⁻¹) * ρ w := by
      rw [← map_mul, ← map_mul]
      congr 1
      group
    have := congrArg (fun σ : Equiv.Perm (Omega (ZMod 7)) => σ (some x)) key
    simp only [Equiv.Perm.mul_apply] at this
    rw [hρδ, multiplier_some, Units.val_mk0, hxy, hd'', hd''0, h4, add_zero] at this
    exact this
  have hw_mem : ρ w ∈ coordinateG (ZMod 7) :=
    mem_coordinateG_of_involution (ρ w) hw_inf hw_zero hw_inv hw_free hconj
  rintro _ ⟨g, rfl⟩
  by_cases hginf : ρ g none = none
  · exact hB g hginf
  · obtain ⟨j, hj⟩ := Option.ne_none_iff_exists'.mp hginf
    set b := p ^ j.val with hb
    have hρb : ρ b = translation (ZMod 7) j := by rw [hb, hρpow, ZMod.natCast_zmod_val]
    have hbinv : ρ b⁻¹ (some j) = some 0 := by
      rw [map_inv, Equiv.Perm.inv_eq_iff_eq, hρb, translation_some, zero_add]
    set h := w⁻¹ * b⁻¹ * g with hh
    have hh_none : ρ h none = none := by
      rw [hh, map_mul, map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hj, hbinv,
        hw_inv_zero]
    have hgeq : g = b * w * h := by
      rw [hh]
      group
    rw [hgeq, map_mul, map_mul]
    exact (coordinateG (ZMod 7)).mul_mem ((coordinateG (ZMod 7)).mul_mem
      (hB b (by rw [hρb, translation_none])) hw_mem) (hB h hh_none)

theorem simple_order_168_without_six_projective_seven_recognition (G : Type) [Group G]
    [Finite G] [IsSimpleGroup G] (_hnonab : ∃ a b : G, a * b ≠ b * a)
    (hcard : Nat.card G = 168) (hsix : ∀ g : G, orderOf g ≠ 6) :
    Nat.card (Sylow 7 G) = 8 ∧ Function.Injective (MulAction.toPermHom G (Sylow 7 G)) ∧
      ∃ (ℓ : Sylow 7 G ≃ Omega (ZMod 7))
        (φ : G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7)),
        (ℓ.permCongrHom.toMonoidHom.comp (MulAction.toPermHom G (Sylow 7 G))).range =
          coordinateG (ZMod 7) ∧
        (∀ g : G, ((pslEquivCoordinateG (ZMod 7) (φ g) : coordinateG (ZMod 7)) :
            Equiv.Perm (Omega (ZMod 7))) = ℓ.permCongr (MulAction.toPerm g)) ∧
        (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (ZMod 7)) :
            Set (Matrix.SpecialLinearGroup (Fin 2) (ZMod 7))) = {1, -1} ∧
        StatedClassicalModel G .PSL 2 7 1 := by
  obtain ⟨h8, hfaith, ℓ, hle⟩ := exists_sylow_seven_labeling G hcard hsix
  set ρ := ℓ.permCongrHom.toMonoidHom.comp (MulAction.toPermHom G (Sylow 7 G)) with hρ
  have hρ_inj : Function.Injective ρ := ℓ.permCongrHom.injective.comp hfaith
  have hrange : ρ.range = coordinateG (ZMod 7) := by
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [card_coordinateG_zmod_seven, ← hcard]
    exact (Nat.card_congr (MonoidHom.ofInjective hρ_inj).toEquiv).le
  let φ : G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7) :=
    ((MonoidHom.ofInjective hρ_inj).trans (MulEquiv.subgroupCongr hrange)).trans
      (pslEquivCoordinateG (ZMod 7)).symm
  refine ⟨h8, hfaith, ℓ, φ, hrange, fun g => ?_,
    CFSG.LocalAnalysis.ComponentInitial.smallLinear_center_eq, ?_⟩
  · change ((pslEquivCoordinateG (ZMod 7) ((pslEquivCoordinateG (ZMod 7)).symm _) :
      coordinateG (ZMod 7)) : Equiv.Perm (Omega (ZMod 7))) = _
    rw [MulEquiv.apply_symm_apply]
    rfl
  · exact ⟨⟨Nat.prime_seven, le_rfl, le_rfl, by decide, by decide⟩, ZMod 7, inferInstance,
      inferInstance, by rw [Nat.card_zmod, pow_one],
      ⟨φ.trans (projectiveSpecialLinearGroupEquivStatedProj 2 (ZMod 7))⟩⟩

end CFSG.ProperTwoGeneratedCore.CosetNormalizer
