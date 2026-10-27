module

public import CFSG.LieType.Steinberg.CentralExt.RankOne
public import CFSG.LieType.Universal.Spin.Twisted.Extras
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LieType.Steinberg.CentralExt.Split
public import CFSG.LieType.Steinberg.Classical.SpinOdd.RankOne

public section

namespace CFSG.LieType.Steinberg

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.LieType.CentralExt

theorem isPGroup_range_of_nsmul_eq_zero {V : Type*} [AddCommGroup V] {G : Type*} [Group G]
    {p : ℕ} (hV : ∀ v : V, p • v = 0) (f : Multiplicative V →* G) : IsPGroup p f.range := by
  rintro ⟨_, a, rfl⟩
  refine ⟨1, Subtype.ext ?_⟩
  change f a ^ p ^ 1 = 1
  rw [pow_one, ← map_pow, ← ofAdd_toAdd a, ← ofAdd_nsmul, hV, ofAdd_zero, map_one]

section Minus

variable {n : ℕ} {K : Type} [Field K] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)

theorem isPGroup_minusRootGroup {p : ℕ} [CharP K p] {γ : Fin (n - 1) → ℤ}
    (hγ : γ ∈ (minusDatum n hirr).roots) : IsPGroup p (minusRootGroup n hirr γ) := by
  rcases exists_toStdB_eq_of_mem_roots n hγ with ⟨i, j, hij, s, t, h⟩ | ⟨i, s, h⟩
  · rw [minusRootGroup_eq_long n hirr hij s t h]
    exact isPGroup_range_of_nsmul_eq_zero
      (fun v => by rw [nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]) _
  · rw [minusRootGroup_eq_short n hirr i s h]
    exact isPGroup_range_of_nsmul_eq_zero
      (fun v => by funext j; simp [CharP.cast_eq_zero]) _

variable [Fact (∀ r : K, r ^ 2 ≠ -c + b * r)]

theorem shortRels_h_eq_one (h2 : (2 : K) ≠ 0) (i : Fin (n - 1)) {t : ShortField b c}
    (ht : t ≠ 0) (h1 : (shortRels n hirr i).h t = 1) : t = 1 := by
  set a := fieldCoord t with ha_def
  have ha : a ≠ 0 := fieldCoord_ne_zero ht
  rw [shortRels_h] at h1
  have hN : planeNorm b c a = 1 := by
    have he := spinAction_shortTorusElt_eVec n hirr i ha
    rw [h1, map_one] at he
    have := congrFun (congrArg (fun v => (v : Vm n K)) he) (.inl i)
    simpa [eVec] using this.symm
  have hrefl : ∀ q, planeRefl b c a q = planeRefl b c planeOne q := by
    intro q
    have hp := spinAction_shortTorusElt_planeVec n hirr i ha (planeRefl b c planeOne q)
    rw [h1, map_one, planeRefl_planeRefl planeNorm_planeOne_ne_zero] at hp
    exact (planeVec_injective n hp).symm
  have h0 := hrefl planeOne
  rw [planeRefl, hN, div_one] at h0
  have hs1 : planeRefl b c planeOne planeOne = -planeOne := by
    ext k
    fin_cases k <;> norm_num [planeRefl, polarPlane, planeNorm, planeOne]
  rw [hs1] at h0
  have hB : polarPlane b c planeOne a = 2 * a 0 + b * a 1 := by
    simp [polarPlane, planeOne]
  have hp0 : (planeOne : Fin 2 → K) 0 = 1 := rfl
  have hp1 : (planeOne : Fin 2 → K) 1 = 0 := rfl
  have e1 := congrFun h0 0
  have e2 := congrFun h0 1
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply, hB, hp0, hp1] at e1 e2
  have ha1 : a 1 = 0 := by
    have hB0 : 2 * a 0 + b * a 1 ≠ 0 := by
      intro h0'
      rw [h0', zero_mul] at e1
      exact h2 (by linear_combination e1)
    have h' : (2 * a 0 + b * a 1) * a 1 = 0 := by linear_combination -e2
    exact (mul_eq_zero.1 h').resolve_left hB0
  simp only [planeNorm, ha1] at hN
  have ha0 : a 0 = 1 ∨ a 0 = -1 := mul_self_eq_one_iff.1 (by linear_combination hN)
  have hre : t.re = a 0 := rfl
  have him : t.im = 0 := ha1
  rcases ha0 with h | h
  · exact QuadraticAlgebra.ext (hre.trans (h.trans QuadraticAlgebra.re_one.symm))
      (him.trans QuadraticAlgebra.im_one.symm)
  ·
    exfalso
    have htm : t = -1 := QuadraticAlgebra.ext
      (by rw [hre, h, QuadraticAlgebra.re_neg, QuadraticAlgebra.re_one])
      (by rw [him, QuadraticAlgebra.im_neg, QuadraticAlgebra.im_one, neg_zero])
    have hfc : a = ((-1 : Kˣ) : K) • planeOne := by
      rw [ha_def, htm]
      ext k
      fin_cases k <;> simp [fieldCoord, planeOne, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
    have h1' : shortTorusElt n hirr i (((-1 : Kˣ) : K) • planeOne) = 1 := by
      rw [← hfc]
      exact h1
    rw [← minusFrame_shortTorus_eq n hirr i (-1), OddFrame.shortTorus_apply] at h1'
    have hd := SpinOdd.shortSL2_injective (minusFrame n b c) i true (h1'.trans (map_one _).symm)
    have := congrArg (fun M : Matrix.SpecialLinearGroup (Fin 2) K =>
      (M : Matrix (Fin 2) (Fin 2) K) 0 0) hd
    simp at this
    exact h2 (by linear_combination -this)

theorem mem_minusRootGroup_single_iff {k : Fin (n - 1)} (hk : ¬k.val + 1 < n - 1)
    (g : spinGroup (quadMinus n K b c)) :
    g ∈ minusRootGroup n hirr (Pi.single k 1) ↔ ∃ t, (shortRels n hirr k).x t = g := by
  rw [minusRootGroup_single_of_not_lt n hirr hk, MonoidHom.mem_range]
  constructor
  · rintro ⟨w, rfl⟩
    obtain ⟨t, ht⟩ := exists_fieldCoord_eq (b := b) (c := c) w.toAdd
    exact ⟨t, by rw [shortRels_x, ht, ofAdd_toAdd]⟩
  · rintro ⟨t, rfl⟩
    exact ⟨_, rfl⟩

theorem mem_minusRootGroup_neg_single_iff {k : Fin (n - 1)} (hk : ¬k.val + 1 < n - 1)
    (g : spinGroup (quadMinus n K b c)) :
    g ∈ minusRootGroup n hirr (-Pi.single k 1) ↔ ∃ t, (shortRels n hirr k).y t = g := by
  rw [minusRootGroup_neg_single_of_not_lt n hirr hk, MonoidHom.mem_range]
  constructor
  · rintro ⟨w, rfl⟩
    obtain ⟨t, ht⟩ := exists_starCoord_eq (b := b) (c := c) w.toAdd
    exact ⟨t, by rw [shortRels_y, ht, ofAdd_toAdd]⟩
  · rintro ⟨t, rfl⟩
    exact ⟨_, rfl⟩

theorem shortRels_x_injective (k : Fin (n - 1)) : Function.Injective (shortRels n hirr k).x := by
  intro s t hst
  rw [shortRels_x, shortRels_x] at hst
  have h := congrArg Multiplicative.toAdd (shortPosHom_injective n hirr k hst)
  simp only [toAdd_ofAdd] at h
  exact QuadraticAlgebra.ext (by simpa [fieldCoord] using congrFun h 0)
    (by simpa [fieldCoord] using congrFun h 1)

end Minus

variable {E : Type*} [Group E] [Finite E]

theorem spinMinus_central_two_extension_splitting {n : ℕ} (hn : 4 ≤ n) {k : Type} [Field k]
    [Finite k] (hk : ringChar k ≠ 2) {b c : k} (hirr : ∀ s : k, s ^ 2 + b * s + c ≠ 0)
    {π : E →* spinGroup (quadMinus n k b c)} (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 π.ker) :
    ∃ σ : spinGroup (quadMinus n k b c) →* E, (∀ x, π (σ x) = x) ∧
      (∀ τ : spinGroup (quadMinus n k b c) →* E, (∀ x, π (τ x) = x) → τ = σ) ∧
      ∃ e : π.ker × σ.range ≃* E, ∀ a, e a = (a.1 : E) * a.2 := by
  have : Fact (ringChar k).Prime := ⟨CharP.char_is_prime k _⟩
  have := fact_shortField hirr
  have := finite_shortField (b := b) (c := c)
  have : CharP (ShortField b c) (ringChar k) :=
    charP_of_injective_algebraMap (algebraMap k (ShortField b c)).injective _
  have hC := not_ringChar_dvd_card_ker hk h2
  refine exists_section_mulEquiv_of_existsUnique hker (existsUnique_section_of_rankOne_lift
    (minusDatum_isCTGroupDatum n hirr hn) (minusDatum_steinbergExtras n hirr)
    (fun _ hγ => isPGroup_minusRootGroup hirr hγ) hπ hker hC fun i => ?_)
  by_cases hi : i.val + 1 < n - 1
  · obtain ⟨ρ', hρ'⟩ := exists_lift hk hπ hker h2
      ((minusFrame n b c).longSL2 (succ_ne_of_lt n hi) true false)
    exact exists_lift_of_injective (SpinFrame.longSL2_injective _ _ _ _)
      (rankOne_minusRootGroup_of_lt n hirr hi).le fun g => DFunLike.congr_fun hρ' g
  · exact exists_rankOne_lift_of_rankOneRels (minusDatum_steinbergExtras n hirr) i
      (shortRels n hirr i) (mem_minusRootGroup_single_iff hirr hi)
      (mem_minusRootGroup_neg_single_iff hirr hi) (shortRels_x_injective hirr i)
      (fun t ht h1 => shortRels_h_eq_one hirr (Ring.two_ne_zero hk) i ht h1) hπ hker hC

end CFSG.LieType.Steinberg
