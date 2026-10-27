module

public import CFSG.LocalAnalysis.ComponentClassification.LiteratureLocalSmallReeOuter
public import CFSG.GH74.GLS.Stage2.OddAut.RPData

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.ComponentClassification.LiteratureLocal.SmallRee CFSG.LieType.Ree
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Walter.Ree.Model
  CFSG.GH74.GLS.Stage2.OddAut

section ReeCore

variable {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K ReeTag.G2.prime]
  (hK : Nat.card K = 3 ^ (2 * a + 1))

theorem uIn_one_ne_one : uIn hK (1 : K) 0 0 ≠ (1 : ReeTag.G2.reeGamma K a) := by
  intro h
  rw [← uIn_zero hK] at h
  exact one_ne_zero (uIn_inj hK h).1

theorem ree_ti {g : ReeTag.G2.reeGamma K a}
    (hg : g * uIn hK (1 : K) 0 0 * g⁻¹ = uIn hK 1 0 0) :
    (g : ModGL ReeTag.G2.tag K) ∈ ReeTag.G2.reeFixedBorel K a := by
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element ReeTag.G2.tag
  have hxU := uIn_mem hK (a := a) (1 : K) 0 0
  have hxB : ((uIn hK (1 : K) 0 0 : ReeTag.G2.reeGamma K a) : ModGL ReeTag.G2.tag K) ∈
      ReeTag.G2.reeFixedBorel K a := ReeTag.reeFixedPosUnipotent_le_reeFixedBorel hxU
  have hcomm : uIn hK (1 : K) 0 0 * g = g * uIn hK (1 : K) 0 0 := by
    have h1 : g * uIn hK (1 : K) 0 0 = uIn hK 1 0 0 * g := by
      calc g * uIn hK (1 : K) 0 0 = (g * uIn hK (1 : K) 0 0 * g⁻¹) * g := by group
        _ = uIn hK 1 0 0 * g := by rw [hg]
    exact h1.symm
  have h1 : (uIn hK (1 : K) 0 0 : ReeTag.G2.reeGamma K a) • (g • basePt a K) = g • basePt a K := by
    rw [← mul_smul, hcomm, mul_smul, smul_basePt_of_mem_borel hxB]
  have h2 := eq_basePt_of_smul_eq hK hw₀ hxU (uIn_one_ne_one hK) h1
  exact mem_borel_of_smul_basePt h2

theorem ree_borel_decomp {g : ReeTag.G2.reeGamma K a}
    (hg : (g : ModGL ReeTag.G2.tag K) ∈ ReeTag.G2.reeFixedBorel K a) :
    ∃ (t b c : K) (s : Kˣ), g = uIn hK t b c * hIn hK s := by
  have hg' : (g : ModGL ReeTag.G2.tag K) ∈
      (ReeTag.G2.reeFixedBorel K a : Set (ModGL ReeTag.G2.tag K)) := hg
  rw [ReeTag.reeFixedBorel_eq_mul'] at hg'
  obtain ⟨u, hu, h, hh, hgu⟩ := hg'
  obtain ⟨t, b, c, hu'⟩ := exists_smallReeU_eq hK hu
  obtain ⟨s, hs⟩ := exists_smallReeH_eq hh
  refine ⟨t, b, c, s, Subtype.ext ?_⟩
  rw [Subgroup.coe_mul, uIn_val, hIn_val, hs, hu']
  exact hgu.symm

theorem hIn_one : hIn hK (1 : Kˣ) = (1 : ReeTag.G2.reeGamma K a) := by
  apply Subtype.ext
  rw [hIn_val, OneMemClass.coe_one]
  exact smallReeH_one

theorem ree_first_coord {t₀ b₀ c₀ t b c t₁ b₁ c₁ : K} {s : Kˣ}
    (h : (uIn hK t₀ b₀ c₀ * hIn hK s) * uIn hK t b c * (uIn hK t₀ b₀ c₀ * hIn hK s)⁻¹ =
      uIn hK t₁ b₁ c₁) :
    ((s ^ (2 * 3 ^ a - 1) : Kˣ) : K) * t = t₁ := by
  have h1 : (uIn hK t₀ b₀ c₀ * hIn hK s) * uIn hK t b c =
      uIn hK t₁ b₁ c₁ * (uIn hK t₀ b₀ c₀ * hIn hK s) := by
    calc (uIn hK t₀ b₀ c₀ * hIn hK s) * uIn hK t b c
        = ((uIn hK t₀ b₀ c₀ * hIn hK s) * uIn hK t b c * (uIn hK t₀ b₀ c₀ * hIn hK s)⁻¹) *
          (uIn hK t₀ b₀ c₀ * hIn hK s) := by group
      _ = _ := by rw [h]
  have h2 : uIn hK t₀ b₀ c₀ * (hIn hK s * uIn hK t b c * (hIn hK s)⁻¹) =
      uIn hK t₁ b₁ c₁ * uIn hK t₀ b₀ c₀ := by
    have h3 : (uIn hK t₀ b₀ c₀ * (hIn hK s * uIn hK t b c * (hIn hK s)⁻¹)) * hIn hK s =
        (uIn hK t₁ b₁ c₁ * uIn hK t₀ b₀ c₀) * hIn hK s := by
      calc (uIn hK t₀ b₀ c₀ * (hIn hK s * uIn hK t b c * (hIn hK s)⁻¹)) * hIn hK s
          = (uIn hK t₀ b₀ c₀ * hIn hK s) * uIn hK t b c := by group
        _ = uIn hK t₁ b₁ c₁ * (uIn hK t₀ b₀ c₀ * hIn hK s) := h1
        _ = _ := by group
    exact mul_right_cancel h3
  rw [hIn_conj_uIn, uIn_mul, uIn_mul] at h2
  have h4 := (uIn_inj hK h2).1
  have h5 : ((s ^ (2 * 3 ^ a - 1) : Kˣ) : K) * t = t₁ := by
    have : t₀ + ((s ^ (2 * 3 ^ a - 1) : Kˣ) : K) * t = t₁ + t₀ := h4
    linear_combination this
  exact h5

theorem frobeniusΓ_pow_uIn_one (j : ℕ) :
    ((frobeniusΓ : MulAut (ReeTag.G2.reeGamma K a)) ^ j) (uIn hK (1 : K) 0 0) =
      uIn hK (1 : K) 0 0 := by
  rw [frobeniusΓ_pow_uIn, one_pow, zero_pow (pow_ne_zero _ (by norm_num))]

theorem ree_aut_of_fix_u1 (ha : 1 ≤ a) {α : MulAut (ReeTag.G2.reeGamma K a)}
    (h : α (uIn hK (1 : K) 0 0) = uIn hK 1 0 0) :
    ∃ (t b c : K) (j : ℕ),
      α = MulAut.conj (uIn hK t b c) * (frobeniusΓ : MulAut (ReeTag.G2.reeGamma K a)) ^ j := by
  obtain ⟨g, j, rfl⟩ := exists_eq_conj_mul_frobeniusΓ_pow ha hK α
  rw [MulAut.mul_apply, frobeniusΓ_pow_uIn_one, MulAut.conj_apply] at h
  have hB := ree_ti hK h
  obtain ⟨t₀, b₀, c₀, s, rfl⟩ := ree_borel_decomp hK hB
  have h1 := ree_first_coord hK h
  have hs : s = 1 := by
    by_contra hs1
    have := pow_two_mul_sub_one_ne_one hK hs1
    apply this
    apply Units.ext
    rw [mul_one] at h1
    simpa using h1
  subst hs
  refine ⟨t₀, b₀, c₀, j, ?_⟩
  rw [hIn_one, mul_one]

theorem frobeniusΓ_pow_longestIn {w₀ : WeylGroup ReeTag.G2.tag}
    (hw₀ : ∀ w, (coxeterSystem ReeTag.G2.tag).length w ≤
      (coxeterSystem ReeTag.G2.tag).length w₀) (j : ℕ) :
    ((frobeniusΓ : MulAut (ReeTag.G2.reeGamma K a)) ^ j) (longestIn a K hw₀) =
      longestIn a K hw₀ := by
  induction j with
  | zero => rfl
  | succ j ih => rw [pow_succ, MulAut.mul_apply, frobeniusΓ_longestIn hw₀, ih]

theorem ree_aut_of_fix_u1_n (ha : 1 ≤ a) {α : MulAut (ReeTag.G2.reeGamma K a)}
    (h : α (uIn hK (1 : K) 0 0) = uIn hK 1 0 0)
    {w₀ : WeylGroup ReeTag.G2.tag}
    (hw₀ : ∀ w, (coxeterSystem ReeTag.G2.tag).length w ≤
      (coxeterSystem ReeTag.G2.tag).length w₀) (hn : α (longestIn a K hw₀) = longestIn a K hw₀) :
    ∃ j : ℕ, α = (frobeniusΓ : MulAut (ReeTag.G2.reeGamma K a)) ^ j := by
  obtain ⟨t, b, c, j, rfl⟩ := ree_aut_of_fix_u1 hK ha h
  refine ⟨j, ?_⟩
  rw [MulAut.mul_apply, frobeniusΓ_pow_longestIn hw₀, MulAut.conj_apply] at hn
  have hcomm : uIn hK t b c * longestIn a K hw₀ = longestIn a K hw₀ * uIn hK t b c := by
    have h1 : uIn hK t b c * longestIn a K hw₀ * (uIn hK t b c)⁻¹ = longestIn a K hw₀ := hn
    calc uIn hK t b c * longestIn a K hw₀
        = (uIn hK t b c * longestIn a K hw₀ * (uIn hK t b c)⁻¹) * uIn hK t b c := by group
      _ = _ := by rw [h1]
  have huU := uIn_mem hK (a := a) t b c
  have huB : ((uIn hK t b c : ReeTag.G2.reeGamma K a) : ModGL ReeTag.G2.tag K) ∈
      ReeTag.G2.reeFixedBorel K a := ReeTag.reeFixedPosUnipotent_le_reeFixedBorel huU
  have hfix : uIn hK t b c • oppPt a K hw₀ = oppPt a K hw₀ := by
    have e : oppPt a K hw₀ = longestIn a K hw₀ • basePt a K := by
      rw [oppPt, basePt, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
    rw [e, ← mul_smul, hcomm, mul_smul, smul_basePt_of_mem_borel huB]
  have hu1 : uIn hK t b c = 1 := by
    by_contra hne
    have := eq_basePt_of_smul_eq hK hw₀ huU hne hfix
    have h2 := smul_oppPt_ne_basePt hK hw₀ (u := 1)
      (by rw [OneMemClass.coe_one]; exact one_mem _)
    rw [one_smul] at h2
    exact h2 this
  rw [hu1, map_one, one_mul]

theorem frobeniusΓ_pow_eq_one_of_dvd (hK : Nat.card K = 3 ^ (2 * a + 1)) {j : ℕ}
    (hj : 2 * a + 1 ∣ j) :
    (frobeniusΓ : MulAut (ReeTag.G2.reeGamma K a)) ^ j = 1 := by
  obtain ⟨l, rfl⟩ := hj
  rw [pow_mul, frobeniusΓ_pow hK, one_pow]

theorem ree_rigid_U (ha : 1 ≤ a) {α : MulAut (ReeTag.G2.reeGamma K a)}
    (h : ∀ u : ReeTag.G2.reeGamma K a,
      (u : ModGL ReeTag.G2.tag K) ∈ ReeTag.G2.reeFixedPosUnipotent K a → α u = u) :
    ∃ t b c : K, α = MulAut.conj (uIn hK t b c) := by
  obtain ⟨t, b, c, j, rfl⟩ := ree_aut_of_fix_u1 hK ha (h _ (uIn_mem hK (1 : K) 0 0))
  refine ⟨t, b, c, ?_⟩
  have hj : ∀ x : K, x ^ 3 ^ j = x := by
    intro x
    have h1 := h (uIn hK x 0 0) (uIn_mem hK x 0 0)
    rw [MulAut.mul_apply, MulAut.conj_apply, frobeniusΓ_pow_uIn,
      zero_pow (pow_ne_zero _ (by norm_num))] at h1
    have h2 := ree_first_coord hK (s := 1) (t₀ := t) (b₀ := b) (c₀ := c)
      (t := x ^ 3 ^ j) (b := 0) (c := 0) (t₁ := x) (b₁ := 0) (c₁ := 0) (by
        rw [hIn_one, mul_one]
        exact h1)
    simpa using h2
  rw [frobeniusΓ_pow_eq_one_of_dvd hK (dvd_of_forall_pow_three_pow_eq hK hj), mul_one]

theorem ree_aut_trivial_of_fix_subfield (ha : 1 ≤ a) {σ : K ≃+* K} {r : ℕ} (hrf : r ∣ 2 * a + 1)
    (hkc : Nat.card (fixSubfield σ) = 3 ^ ((2 * a + 1) / r))
    {w₀ : WeylGroup ReeTag.G2.tag}
    (hw₀ : ∀ w, (coxeterSystem ReeTag.G2.tag).length w ≤
      (coxeterSystem ReeTag.G2.tag).length w₀) {ζ : MulAut (ReeTag.G2.reeGamma K a)}
    (hu : ∀ t : K, σ t = t → ζ (uIn hK t 0 0) = uIn hK t 0 0)
    (hn : ζ (longestIn a K hw₀) = longestIn a K hw₀) (hcop : Nat.Coprime (orderOf ζ) r) :
    ζ = 1 := by
  have h1 : σ (1 : K) = 1 := map_one σ
  obtain ⟨j, rfl⟩ := ree_aut_of_fix_u1_n hK ha (hu 1 h1) hw₀ hn
  have hj : ∀ x : fixSubfield σ, x ^ 3 ^ j = x := by
    intro x
    have h2 := hu (x : K) x.2
    rw [frobeniusΓ_pow_uIn, zero_pow (pow_ne_zero _ (by norm_num))] at h2
    have h3 := (uIn_inj hK h2).1
    exact Subtype.ext (by simpa using h3)
  obtain ⟨d, hd⟩ := hrf
  have hdr : (2 * a + 1) / r = d := by
    have hr0 : 0 < r := by
      rcases Nat.eq_zero_or_pos r with h | h
      · subst h; omega
      · exact h
    rw [hd]
    exact Nat.mul_div_cancel_left d hr0
  have hdodd : d = 2 * ((d - 1) / 2) + 1 := by
    have : Odd d := by
      have : Odd (r * d) := hd ▸ odd_two_mul_add_one a
      exact (Nat.odd_mul.1 this).2
    obtain ⟨c, hc⟩ := this
    omega
  have hkc' : Nat.card (fixSubfield σ) = 3 ^ (2 * ((d - 1) / 2) + 1) := by
    rw [hkc, hdr, ← hdodd]
  have hdj : d ∣ j := by
    have := dvd_of_forall_pow_three_pow_eq (K := fixSubfield σ) hkc' hj
    rwa [← hdodd] at this
  obtain ⟨l, rfl⟩ := hdj
  have hpow : ((frobeniusΓ : MulAut (ReeTag.G2.reeGamma K a)) ^ (d * l)) ^ r = 1 := by
    have : ((frobeniusΓ : MulAut (ReeTag.G2.reeGamma K a)) ^ (d * l)) ^ r =
        (frobeniusΓ : MulAut (ReeTag.G2.reeGamma K a)) ^ ((2 * a + 1) * l) := by
      rw [← pow_mul]
      congr 1
      rw [hd]
      ring
    rw [this, pow_mul, frobeniusΓ_pow hK, one_pow]
  have hord : orderOf ((frobeniusΓ : MulAut (ReeTag.G2.reeGamma K a)) ^ (d * l)) ∣ r :=
    orderOf_dvd_of_pow_eq_one hpow
  exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd hcop hord)

theorem finite_reeGamma : Finite (ReeTag.G2.reeGamma K a) := by
  have : Finite (ModGL ReeTag.G2.tag K) := finite_modGL (τ := ReeTag.G2.tag) (K := K)
  infer_instance

theorem ree_pCharData (ha : 1 ≤ a) (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    PCharData (ReeTag.G2.reeGamma K a) 3
      (⊤ : Subgroup (MulAut (ReeTag.G2.reeGamma K a))) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (ReeTag.G2.reeGamma K a) := finite_reeGamma
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element ReeTag.G2.tag
  obtain ⟨-, -, -, -, -, -, hreg, -, -, -, ⟨U, hU⟩, hstab, hUn, hNU, -⟩ :=
    small_Ree_Borel_coset_Sylow_action a K hK w₀ hw₀
  set B' := (ReeTag.G2.reeFixedBorel K a).subgroupOf (ReeTag.G2.reeGamma K a) with hB'
  set U' := (ReeTag.G2.reeFixedPosUnipotent K a).subgroupOf (ReeTag.G2.reeGamma K a) with hU'
  refine PCharData.of_standard (fun x _ => Subgroup.mem_top _) U ?_
  intro P hNP hPtop
  rw [hU, hNU] at hNP
  have hUB : U' ≤ B' := by
    rw [← hNU]
    exact Subgroup.le_normalizer
  have hPB : P ≤ B' := by
    intro g hg
    by_contra hgB
    apply hPtop
    have hgξ : g • (QuotientGroup.mk 1 : ReeTag.G2.reeGamma K a ⧸ B') ≠ QuotientGroup.mk 1 := by
      intro h
      apply hgB
      rw [← hstab]
      exact h
    rw [eq_top_iff]
    intro x _
    by_cases hx : x • (QuotientGroup.mk 1 : ReeTag.G2.reeGamma K a ⧸ B') = QuotientGroup.mk 1
    · exact hNP (by rw [← hstab]; exact hx)
    · obtain ⟨u, hu, -⟩ := hreg _ _ hgξ hx
      have hxug : x⁻¹ * ((u : ReeTag.G2.reeGamma K a) * g) ∈ P := by
        apply hNP
        rw [← hstab]
        show (x⁻¹ * ((u : ReeTag.G2.reeGamma K a) * g)) • (QuotientGroup.mk 1 :
          ReeTag.G2.reeGamma K a ⧸ B') = QuotientGroup.mk 1
        rw [mul_smul, mul_smul, hu, inv_smul_smul]
      have huP : (u : ReeTag.G2.reeGamma K a) ∈ P := hNP (hUB u.2)
      have hugP : (u : ReeTag.G2.reeGamma K a) * g ∈ P := P.mul_mem huP hg
      have hxinv : x⁻¹ ∈ P := by
        have h2 := P.mul_mem hxug (P.inv_mem hugP)
        have e : x⁻¹ * ((u : ReeTag.G2.reeGamma K a) * g) *
            ((u : ReeTag.G2.reeGamma K a) * g)⁻¹ = x⁻¹ := by group
        rwa [e] at h2
      exact (inv_mem_iff).1 hxinv
  have hP : P = B' := le_antisymm hPB hNP
  subst hP
  refine ⟨(U : Subgroup (ReeTag.G2.reeGamma K a)), ?_, ?_, U.isPGroup', ?_⟩
  · rw [hU]
    exact hUB
  · rw [hU]
    exact hUn
  · intro α _ hα
    obtain ⟨t, b, c, rfl⟩ := ree_rigid_U hK ha (fun u hu => hα u (by
      rw [hU]
      exact Subgroup.mem_subgroupOf.2 hu))
    refine ⟨uIn hK t b c, ?_, rfl⟩
    rw [hU]
    exact Subgroup.mem_subgroupOf.2 (uIn_mem hK t b c)

end ReeCore


end CFSG.GH74.GLS.Stage2.Bender.Thm1
