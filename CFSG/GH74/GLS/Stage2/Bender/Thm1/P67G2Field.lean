module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67G2FieldAux
public import CFSG.GH74.GLS.Stage2.OddAut.LangR
public import CFSG.GH74.GLS.Stage2.OddAut.FixedCore
public import CFSG.RankThree.PartTwo.KFacts.AutG2
public import CFSG.RankThree.SteinbergR3ESmallReeCosetDescent
public import CFSG.LieType.Chevalley.EvenCanonicalFieldCentralizer

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LieType.Ree CFSG.RankThree.PartTwo.KFacts CFSG.GH74.GLS.Stage2.OddAut
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87

section G2Odd

variable {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (K : Type) [Field K]
  (hK : Nat.card K = p ^ f)

include hp hp2 hf hK in
theorem g2FieldHom_faithful (σ : K ≃+* K) (hσ : IsInnerAut (g2FieldHom K σ)) : σ = 1 := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hp.pos f).ne')
  have hchar : CharP K p := finite_field_prime_power_characteristic hp hf hK
  by_cases hp3 : p = 3
  · subst hp3
    have : CharP K ReeTag.G2.prime := hchar
    obtain ⟨-, -, ⟨Θ, hΘ1, -, hΘk⟩, -⟩ := G2_three_exact_automorphism_normal_form hf K hK
    obtain ⟨fr, hfr, hord, htop, -⟩ :=
      finite_field_automorphism_fixed_field_cardinality Nat.prime_three hf hK
    obtain ⟨j, hj⟩ : ∃ j : ℕ, fr ^ j = σ := by
      have hmem : σ ∈ Subgroup.zpowers fr := htop ▸ Subgroup.mem_top σ
      obtain ⟨k, hk⟩ := hmem
      refine ⟨(k % (orderOf fr : ℤ)).toNat, ?_⟩
      rw [← hk, ← zpow_natCast]
      rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by
        have : 0 < orderOf fr := orderOf_pos fr
        omega))]
      exact zpow_mod_orderOf fr k
    subst hj
    have h1 : g2FieldHom K (fr ^ j) = ReeTag.G2.finiteExceptionalAut K ^ (2 * j) := by
      change exactNormalAut Tag.G2 K 1 (fr ^ j) 0 = _
      rw [finiteExceptionalAut_pow_two_mul]
      exact exactNormalAut_one_eq_finiteFrobeniusAut_pow ReeTag.G2 (σ := fr ^ j)
        (ringAut_pow_apply_of_frobenius hfr j)
    have h2 : Θ (g2FieldHom K (fr ^ j)) = Multiplicative.ofAdd ((2 * j : ℕ) : ZMod (2 * f)) :=
      hΘ1 _ 1 (2 * j) (by rw [h1, map_one, one_mul])
    have h3 : g2FieldHom K (fr ^ j) ∈ Θ.ker := by
      rw [hΘk]
      exact hσ
    have h3' : Θ (g2FieldHom K (fr ^ j)) = 1 := h3
    rw [h2, ofAdd_eq_one] at h3'
    have h4 : 2 * f ∣ 2 * j := (ZMod.natCast_eq_zero_iff _ _).1 h3'
    have h5 : f ∣ j := Nat.dvd_of_mul_dvd_mul_left (by norm_num) h4
    rw [← orderOf_dvd_iff_pow_eq_one.1 (hord ▸ h5)]
  · have h5 := five_le_of_ne_three hp hp2 hp3
    have h4 : 4 ≤ Nat.card K := by
      rw [hK]
      calc 4 ≤ 5 := by norm_num
        _ ≤ p := h5
        _ ≤ p ^ f := Nat.le_self_pow (by omega) p
    have hrc : ringChar K ≠ 3 := by
      rw [ringChar.eq K p]
      exact hp3
    exact (g2_automorphism_normal_form hrc h4).2 σ hσ

theorem g2_three_odd_nf {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    [CharP K ReeTag.G2.prime] (hK : Nat.card K = 3 ^ f)
    (α : MulAut (adjointGroup ReeTag.G2.tag K)) (hα : Odd (orderOf α)) :
    ∃ (g : adjointGroup ReeTag.G2.tag K) (σ : K ≃+* K),
      α = MulAut.conj g * exactNormalAut ReeTag.G2.tag K 1 σ 0 := by
  classical
  obtain ⟨-, hex, ⟨Θ, hΘ1, -, hΘk⟩, -⟩ := G2_three_exact_automorphism_normal_form hf K hK
  obtain ⟨fr, hfr, hord, htop, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality Nat.prime_three hf hK
  obtain ⟨⟨g, k⟩, hk, -⟩ := hex α
  have hΘα : Θ α = Multiplicative.ofAdd (((k : ℕ)) : ZMod (2 * f)) := hΘ1 α g k hk
  have hpow : Θ α ^ orderOf α = 1 := by
    rw [← map_pow Θ α (orderOf α), pow_orderOf_eq_one, map_one]
  rw [hΘα, ← ofAdd_nsmul, ofAdd_eq_one, nsmul_eq_mul] at hpow
  have hdvd : 2 * f ∣ orderOf α * (k : ℕ) := by
    have : (((orderOf α * (k : ℕ) : ℕ)) : ZMod (2 * f)) = 0 := by
      push_cast
      exact hpow
    exact (ZMod.natCast_eq_zero_iff _ _).1 this
  have h2 : 2 ∣ orderOf α * (k : ℕ) := (Dvd.intro f rfl).trans hdvd
  have hk2 : 2 ∣ (k : ℕ) := by
    rcases (Nat.Prime.dvd_mul Nat.prime_two).1 h2 with h | h
    · exact absurd h (by simpa [even_iff_two_dvd] using Nat.not_even_iff_odd.2 hα)
    · exact h
  obtain ⟨j, hj⟩ := hk2
  have h1 : exactNormalAut ReeTag.G2.tag K 1 (fr ^ j) 0 =
      ReeTag.G2.finiteExceptionalAut K ^ (2 * j) := by
    rw [finiteExceptionalAut_pow_two_mul]
    exact exactNormalAut_one_eq_finiteFrobeniusAut_pow ReeTag.G2 (σ := fr ^ j)
      (ringAut_pow_apply_of_frobenius hfr j)
  refine ⟨g, fr ^ j, ?_⟩
  rw [h1, ← hj]
  exact hk

include hp hp2 hf hK in
theorem g2_nf_of_ne_three (hp3 : p ≠ 3) (α : MulAut (adjointGroup Tag.G2 K)) :
    ∃ (g : adjointGroup Tag.G2 K) (σ : K ≃+* K), α = MulAut.conj g * g2FieldHom K σ := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hp.pos f).ne')
  have hchar : CharP K p := finite_field_prime_power_characteristic hp hf hK
  have h5 := five_le_of_ne_three hp hp2 hp3
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 ≤ 5 := by norm_num
      _ ≤ p := h5
      _ ≤ p ^ f := Nat.le_self_pow (by omega) p
  have hrc : ringChar K ≠ 3 := by
    rw [ringChar.eq K p]
    exact hp3
  exact (g2_automorphism_normal_form hrc h4).1 α

include hp hp2 hf hK in
theorem g2_odd_nf (α : MulAut (adjointGroup Tag.G2 K)) (hα : Odd (orderOf α)) :
    ∃ (g : adjointGroup Tag.G2 K) (σ : K ≃+* K), α = MulAut.conj g * g2FieldHom K σ := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hp.pos f).ne')
  have hchar : CharP K p := finite_field_prime_power_characteristic hp hf hK
  by_cases hp3 : p = 3
  · subst hp3
    have : CharP K ReeTag.G2.prime := hchar
    exact g2_three_odd_nf hf K hK α hα
  · exact g2_nf_of_ne_three hp hp2 hf K hK hp3 α

include hp hp2 hf hK in
theorem g2_field_descent_of_nf {r : ℕ} (hr : r.Prime)
    {φ : MulAut (adjointGroup Tag.G2 K)} (hφord : orderOf φ = r) (hφinn : ¬ IsInnerAut φ)
    (hnf : ∃ (g : adjointGroup Tag.G2 K) (σ : K ≃+* K), φ = MulAut.conj g * g2FieldHom K σ) :
    r ∣ f ∧ ∃ (i : ℕ) (δ : MulAut (adjointGroup Tag.G2 K)) (τ : K ≃+* K),
      (∀ c, τ c = c ^ p ^ (f / r)) ∧ orderOf τ = r ∧ δ * φ ^ i * δ⁻¹ = g2FieldHom K τ := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hp.pos f).ne')
  have hchar : CharP K p := finite_field_prime_power_characteristic hp hf hK
  have : Fact p.Prime := ⟨hp⟩
  have : Fact r.Prime := ⟨hr⟩
  have hcenter : Subgroup.center (adjointGroup Tag.G2 K) = ⊥ := center_adjointGroup_eq_bot
  obtain ⟨fr, hfr, hord, htop, hcard, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality hp hf hK
  obtain ⟨g, σ', hφ⟩ := hnf
  have hσ1 : σ' ≠ 1 := by
    rintro rfl
    apply hφinn
    refine ⟨g, ?_⟩
    rw [hφ, map_one, mul_one]
  set Φ := g2FieldHom K σ' with hΦ
  have hr1 : (MulAut.conj g * Φ) ^ r = 1 := by rw [← hφ, ← hφord, pow_orderOf_eq_one]
  rw [conj_mul_pow_eq] at hr1
  have hΦr : Φ ^ r = MulAut.conj (normSeq Φ g r)⁻¹ := by
    rw [map_inv]
    exact eq_inv_of_mul_eq_one_right hr1
  have hσr : σ' ^ r = 1 := by
    apply g2FieldHom_faithful hp hp2 hf K hK
    refine ⟨(normSeq Φ g r)⁻¹, ?_⟩
    rw [map_pow, ← hΦ, hΦr]
  have hΦr1 : Φ ^ r = 1 := by rw [hΦ, ← map_pow, hσr, map_one]
  have hnorm : normSeq Φ g r = 1 :=
    normSeq_eq_one_of_pow_eq_one (S := adjointGroup Tag.G2 K) hcenter hΦr1 (by
      rw [← hφ, ← hφord, pow_orderOf_eq_one])
  have hσord : orderOf σ' = r := orderOf_eq_prime hσr hσ1
  have hdvd : orderOf σ' ∣ f := by
    rw [← hcard]
    exact orderOf_dvd_natCard σ'
  rw [hσord] at hdvd
  refine ⟨hdvd, ?_⟩
  obtain ⟨m, hm⟩ := hdvd
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; omega
    · exact h
  have hfm : f / r = m := by
    rw [hm]
    exact Nat.mul_div_cancel_left m hr.pos
  set τ : K ≃+* K := fr ^ m with hτ
  have hτc : ∀ c, τ c = c ^ p ^ m := ringAut_pow_apply_of_frobenius hfr m
  have hτr : τ ^ r = 1 := by
    rw [hτ, ← pow_mul, show m * r = f by rw [hm]; ring, ← hord, pow_orderOf_eq_one]
  obtain ⟨j, hj⟩ : ∃ j : ℕ, fr ^ j = σ' := by
    have hmem : σ' ∈ Subgroup.zpowers fr := htop ▸ Subgroup.mem_top σ'
    obtain ⟨k, hk⟩ := hmem
    refine ⟨(k % (orderOf fr : ℤ)).toNat, ?_⟩
    rw [← hk, ← zpow_natCast]
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by
      have : 0 < orderOf fr := orderOf_pos fr
      omega))]
    exact zpow_mod_orderOf fr k
  have hmj : m ∣ j := by
    have h1 : fr ^ (j * r) = 1 := by rw [pow_mul, hj, hσr]
    have h2 : f ∣ j * r := orderOf_dvd_iff_pow_eq_one.2 h1 |> (hord ▸ ·)
    rw [hm] at h2
    have h3 : r * m ∣ r * j := by rw [mul_comm j r] at h2; exact h2
    exact Nat.dvd_of_mul_dvd_mul_left hr.pos h3
  obtain ⟨i, hi⟩ := hmj
  have hσi : σ' = τ ^ i := by rw [← hj, hi, hτ, pow_mul]
  set i₀ := i % r with hi₀
  have hσi₀ : σ' = τ ^ i₀ := by
    rw [hσi, hi₀]
    exact pow_eq_pow_mod i hτr
  have hi₀0 : i₀ ≠ 0 := by
    intro h
    apply hσ1
    rw [hσi₀, h, pow_zero]
  have hi₀r : i₀ < r := Nat.mod_lt _ hr.pos
  have hcop : Nat.Coprime i₀ r := by
    have : ¬ r ∣ i₀ := fun h => absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hi₀0) h) (by omega)
    exact ((Nat.Prime.coprime_iff_not_dvd hr).2 this).symm
  obtain ⟨i', hi'⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hr.one_lt
  set Φτ := g2FieldHom K τ with hΦτ
  have hσi' : σ' ^ i' = τ := by
    rw [hσi₀, ← pow_mul, pow_eq_pow_mod _ hτr, hi'.2, pow_one]
  have hφi : φ ^ i' = MulAut.conj (normSeq Φ g i') * Φτ := by
    rw [hφ, conj_mul_pow_eq, hΦ, ← map_pow, hσi']
  have hΦτr : Φτ ^ r = 1 := by rw [hΦτ, ← map_pow, hτr, map_one]
  have hφir : (MulAut.conj (normSeq Φ g i') * Φτ) ^ r = 1 := by
    rw [← hφi, ← pow_mul, mul_comm, pow_mul, ← hφord, pow_orderOf_eq_one, one_pow]
  have hN := normSeq_eq_one_of_pow_eq_one (S := adjointGroup Tag.G2 K) hcenter hΦτr hφir
  have hK' : Nat.card K = p ^ (r * m) := by rw [hK, hm]
  obtain ⟨β, hβ⟩ := exists_conj_mul_eq_of_norm_eq_one_r (τ := Tag.G2) (K := K) (p := p) (m := m)
    (r := r) hm1 hr.pos hK' hτc (Φ := Φτ) (fun h => coe_g2FieldHom τ h) hN
  refine ⟨i', β⁻¹, τ, fun c => by rw [hfm]; exact hτc c, ?_, ?_⟩
  · have hτ1 : τ ≠ 1 := by
      intro h1
      have h2 : orderOf fr ∣ m := orderOf_dvd_of_pow_eq_one (by rw [← hτ]; exact h1)
      rw [hord] at h2
      have h3 := Nat.le_of_dvd hm1 h2
      have h4 := hr.two_le
      nlinarith
    exact orderOf_eq_prime hτr hτ1
  rw [hφi, hβ]
  have e : β⁻¹ * (β * Φτ * β⁻¹) * β⁻¹⁻¹ = Φτ := by group
  rw [e]

include hp hp2 hf hK in
theorem g2_field_descent {r : ℕ} (hr : r.Prime) (hrodd : Odd r)
    {φ : MulAut (adjointGroup Tag.G2 K)} (hφord : orderOf φ = r) (hφinn : ¬ IsInnerAut φ) :
    r ∣ f ∧ ∃ (i : ℕ) (δ : MulAut (adjointGroup Tag.G2 K)) (τ : K ≃+* K),
      (∀ c, τ c = c ^ p ^ (f / r)) ∧ orderOf τ = r ∧ δ * φ ^ i * δ⁻¹ = g2FieldHom K τ :=
  g2_field_descent_of_nf hp hp2 hf K hK hr hφord hφinn
    (g2_odd_nf hp hp2 hf K hK φ (by rw [hφord]; exact hrodd))

end G2Odd

section FixedFaith

variable {τ : Tag} {K : Type} [Field K] [Finite K]

theorem eq_one_of_forall_fixedFieldImage_faithful {σ : K ≃+* K}
    (hfaith : ∀ (g' : adjointGroup τ (fixSubfield σ)) (ψ : fixSubfield σ ≃+* fixSubfield σ),
      (∀ j' ∈ adjointGroup τ (fixSubfield σ), (g' : ModGL τ (fixSubfield σ)) *
        Units.map (entrywiseHom ψ.toRingHom) j' * (g' : ModGL τ (fixSubfield σ))⁻¹ = j') →
        g' = 1 ∧ ψ = 1)
    {g : adjointGroup τ K} (hgJ : (g : ModGL τ K) ∈ fixedFieldImage τ σ) (φ : K ≃+* K)
    (hfix : ∀ j : adjointGroup τ K, (j : ModGL τ K) ∈ fixedFieldImage τ σ →
      (g : ModGL τ K) * Units.map (entrywiseHom φ.toRingHom) (j : ModGL τ K) *
        (g : ModGL τ K)⁻¹ = j) :
    g = 1 ∧ ∀ c ∈ fixSubfield σ, φ c = c := by
  set k := fixSubfield σ
  set ι := baseChangeGL (τ := τ) k.subtype
  have hιinj : Function.Injective ι := baseChangeGL_injective _
  obtain ⟨g', hg', hgg'⟩ := hgJ
  set ψ := fixSubfieldRestrict φ σ
  have hid : ∀ j' ∈ adjointGroup τ k,
      g' * Units.map (entrywiseHom ψ.toRingHom) j' * g'⁻¹ = j' := by
    intro j' hj'
    have hj'J : ι j' ∈ fixedFieldImage τ σ := ⟨j', hj', rfl⟩
    have hj'C : ι j' ∈ adjointGroup τ K := (fixedFieldImage_le hj'J).1
    have h1 := hfix ⟨ι j', hj'C⟩ hj'J
    change (g : ModGL τ K) * Units.map (entrywiseHom φ.toRingHom) (ι j') *
      (g : ModGL τ K)⁻¹ = ι j' at h1
    rw [← hgg', units_map_entrywiseHom_baseChangeGL_restrict, ← map_inv, ← map_mul,
      ← map_mul] at h1
    exact hιinj h1
  obtain ⟨hg1, hψ1⟩ := hfaith ⟨g', hg'⟩ ψ hid
  refine ⟨Subtype.ext ?_, fun c hc => ?_⟩
  · rw [← hgg']
    have : g' = 1 := congrArg Subtype.val hg1
    rw [this, map_one]
    rfl
  · have h1 := congrArg (fun ψ' : k ≃+* k => (ψ' ⟨c, hc⟩ : K)) hψ1
    simp only [ψ] at h1
    exact h1

end FixedFaith

section G2Fixed

variable {K : Type} [Field K] [Finite K]

theorem g2_fixSub_equiv (τ : K ≃+* K) :
    Nonempty (adjointGroup Tag.G2 (fixSubfield τ) ≃* ↥(fixSub (g2FieldHom K τ))) := by
  have hJ : fixedFieldImage Tag.G2 τ = entrywiseFixedGroup Tag.G2 τ :=
    (CFSG.RankThree.entrywiseFixedGroup_eq_fixedFieldImage_of_det_one
      CFSG.RankThree.det_transpose_cartan_G2 τ).symm
  have hfix : fixSub (g2FieldHom K τ) = (entrywiseFixedGroup Tag.G2 τ).subgroupOf
      (adjointGroup Tag.G2 K) := by
    ext x
    rw [mem_fixSub, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      refine ⟨x.2, ?_⟩
      have h1 := congrArg (fun y : adjointGroup Tag.G2 K => (y : ModGL Tag.G2 K)) h
      simpa [coe_g2FieldHom] using h1
    · rintro ⟨-, h⟩
      apply Subtype.ext
      rw [coe_g2FieldHom]
      exact h
  have hle : entrywiseFixedGroup Tag.G2 τ ≤ adjointGroup Tag.G2 K := inf_le_left
  exact ⟨(fixedFieldImageEquiv τ).trans ((MulEquiv.subgroupCongr hJ).trans
    ((Subgroup.subgroupOfEquivOfLe hle).symm.trans (MulEquiv.subgroupCongr hfix.symm)))⟩

theorem g2_mem_fixSub_iff (τ : K ≃+* K) (x : adjointGroup Tag.G2 K) :
    x ∈ fixSub (g2FieldHom K τ) ↔ (x : ModGL Tag.G2 K) ∈ fixedFieldImage Tag.G2 τ := by
  have hJ : fixedFieldImage Tag.G2 τ = entrywiseFixedGroup Tag.G2 τ :=
    (CFSG.RankThree.entrywiseFixedGroup_eq_fixedFieldImage_of_det_one
      CFSG.RankThree.det_transpose_cartan_G2 τ).symm
  rw [hJ, mem_fixSub]
  constructor
  · intro h
    refine ⟨x.2, ?_⟩
    have h1 := congrArg (fun y : adjointGroup Tag.G2 K => (y : ModGL Tag.G2 K)) h
    simpa [coe_g2FieldHom] using h1
  · rintro ⟨-, h⟩
    apply Subtype.ext
    rw [coe_g2FieldHom]
    exact h

end G2Fixed

section G2FieldMain

theorem g2_hfaith {p d : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hd : 1 ≤ d) (k : Type) [Field k]
    [Finite k] (hk : Nat.card k = p ^ d) (g' : adjointGroup Tag.G2 k) (ψ : k ≃+* k)
    (h : ∀ j' ∈ adjointGroup Tag.G2 k, (g' : ModGL Tag.G2 k) *
      Units.map (entrywiseHom ψ.toRingHom) j' * (g' : ModGL Tag.G2 k)⁻¹ = j') :
    g' = 1 ∧ ψ = 1 := by
  have hcenter : Subgroup.center (adjointGroup Tag.G2 k) = ⊥ := center_adjointGroup_eq_bot
  have h1 : MulAut.conj g' * g2FieldHom k ψ = 1 := by
    refine MulEquiv.ext fun x => Subtype.ext ?_
    rw [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul, coe_g2FieldHom,
      Subgroup.coe_inv]
    exact h _ x.2
  have hψ : ψ = 1 := by
    apply g2FieldHom_faithful hp hp2 hd k hk
    refine ⟨g'⁻¹, ?_⟩
    rw [map_inv]
    exact (eq_inv_of_mul_eq_one_right h1).symm
  refine ⟨?_, hψ⟩
  rw [hψ, map_one, mul_one] at h1
  have : g' ∈ Subgroup.center (adjointGroup Tag.G2 k) := by
    rw [Subgroup.mem_center_iff]
    intro y
    have := congrArg (fun φ : MulAut (adjointGroup Tag.G2 k) => φ y) h1
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc y * g' = (g' * y * g'⁻¹) * g' := by rw [this]
      _ = g' * y := by group
  rw [hcenter, Subgroup.mem_bot] at this
  exact this

section Last


theorem g2_false_of_field {p f r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (K : Type)
    [Field K] (hK : Nat.card K = p ^ f) (hr : r.Prime) (hrodd : Odd r)
    {V Z : Subgroup (MulAut (adjointGroup Tag.G2 K))}
    (h2 : N2Cfg (adjointGroup Tag.G2 K) r V Z) (h3 : N3Full (adjointGroup Tag.G2 K) V Z)
    (hout : ∃ v ∈ V, ¬ IsInnerAut v) : False := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hp.pos f).ne')
  have : Fact p.Prime := ⟨hp⟩
  have : Fact r.Prime := ⟨hr⟩
  have hcenter : Subgroup.center (adjointGroup Tag.G2 K) = ⊥ := center_adjointGroup_eq_bot
  obtain ⟨-, -, hVe, hVc, -⟩ := id h2
  have := hVe
  obtain ⟨φ, hφV, hφinn⟩ := hout
  have hφ1 : φ ≠ 1 := fun h => hφinn (h ▸ ⟨1, map_one _⟩)
  have hφr : φ ^ r = 1 := elemPow_eq_one_of_isElementaryAbelian φ hφV
  have hφord : orderOf φ = r := orderOf_eq_prime hφr hφ1
  obtain ⟨hrf, i, δ, τ, hτc, hτord, hδ⟩ := g2_field_descent hp hp2 hf K hK hr hrodd hφord hφinn
  have hφ'V : φ ^ i ∈ V := pow_mem hφV i
  have hΦ1 : g2FieldHom K τ ≠ 1 := by
    intro h
    have hτ1 : τ = 1 := g2FieldHom_faithful hp hp2 hf K hK τ ⟨1, by rw [h, map_one]⟩
    rw [hτ1, orderOf_one] at hτord
    exact hr.one_lt.ne hτord
  have hφ'1 : φ ^ i ≠ 1 := by
    intro h
    apply hΦ1
    rw [← hδ, h]
    group
  have hkcard := card_fixSubfield hp hf hK hτord
  have hm1 : 1 ≤ f / r := Nat.div_pos (Nat.le_of_dvd (by omega) hrf) hr.pos
  have hk3 : 3 ≤ Nat.card (fixSubfield τ) := by
    rw [hkcard]
    have h5 : 3 ≤ p := by
      have := hp.two_le
      omega
    calc 3 ≤ p := h5
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ (f / r) := Nat.pow_le_pow_right hp.pos hm1
  refine false_of_fixed_core hcenter h2 h3 hφ'V hφ'1 ?_ ?_
  ·
    obtain ⟨e₁⟩ := fixSub_conj_equiv (φ ^ i) δ
    obtain ⟨e₂⟩ := g2_fixSub_equiv (K := K) τ
    have e : ↥(fixSub (φ ^ i)) ≃* adjointGroup Tag.G2 (fixSubfield τ) :=
      e₁.trans ((MulEquiv.subgroupCongr (congrArg fixSub hδ)).trans e₂.symm)
    have hcenterk : Subgroup.center (adjointGroup Tag.G2 (fixSubfield τ)) = ⊥ :=
      center_adjointGroup_eq_bot
    refine noAbelNormal_of_equiv e (fun N hN hc => ?_)
    exact eq_bot_of_normal_abelian_of_isQuasisimple
      (CFSG.LieType.Steinberg.Adjoint.isQuasisimple_g2_of_three_le_card (fixSubfield τ) hk3)
      hcenterk N hc
  · intro ζ hζodd hζcop hζφ hζfix
    set ζ' := δ * ζ * δ⁻¹ with hζ'
    have hord : orderOf ζ' = orderOf ζ := by
      have := MulEquiv.orderOf_eq (MulAut.conj δ) ζ
      rwa [MulAut.conj_apply] at this
    have hcomm : ζ' * g2FieldHom K τ = g2FieldHom K τ * ζ' := by
      rw [← hδ, hζ']
      calc δ * ζ * δ⁻¹ * (δ * φ ^ i * δ⁻¹) = δ * (ζ * φ ^ i) * δ⁻¹ := by group
        _ = δ * (φ ^ i * ζ) * δ⁻¹ := by rw [hζφ]
        _ = δ * φ ^ i * δ⁻¹ * (δ * ζ * δ⁻¹) := by group
    have hfixΦ : ∀ y : adjointGroup Tag.G2 K, g2FieldHom K τ y = y → ζ' y = y := by
      intro y hy
      have hδy : (φ ^ i) (δ⁻¹ y) = δ⁻¹ y := by
        have h1 : (δ * φ ^ i * δ⁻¹) y = y := by rw [hδ]; exact hy
        simp only [MulAut.mul_apply] at h1
        have h2' : δ⁻¹ (δ ((φ ^ i) (δ⁻¹ y))) = δ⁻¹ y := by rw [h1]
        rwa [MulAut.inv_apply_self] at h2'
      have hζx := hζfix (δ⁻¹ y) hδy
      simp only [hζ', MulAut.mul_apply]
      rw [hζx, MulAut.apply_inv_self]
    obtain ⟨g, ρ, hg⟩ := g2_odd_nf hp hp2 hf K hK ζ' (by rw [hord]; exact hζodd)
    have hgfix : g2FieldHom K τ g = g := by
      have hρτ : g2FieldHom K ρ * g2FieldHom K τ = g2FieldHom K τ * g2FieldHom K ρ := by
        rw [← map_mul, ← map_mul, ringAut_mul_comm K ρ τ]
      have h1 : MulAut.conj g * g2FieldHom K ρ * g2FieldHom K τ =
          g2FieldHom K τ * (MulAut.conj g * g2FieldHom K ρ) := by rw [← hg]; exact hcomm
      have h2' : g2FieldHom K τ * MulAut.conj g = MulAut.conj (g2FieldHom K τ g) *
          g2FieldHom K τ := by
        have := mul_mulAutConj_mul_inv (g2FieldHom K τ) g
        calc g2FieldHom K τ * MulAut.conj g
            = (g2FieldHom K τ * MulAut.conj g * (g2FieldHom K τ)⁻¹) * g2FieldHom K τ := by group
          _ = _ := by rw [this]
      have h3' : MulAut.conj g * (g2FieldHom K ρ * g2FieldHom K τ) =
          MulAut.conj (g2FieldHom K τ g) * (g2FieldHom K ρ * g2FieldHom K τ) := by
        calc MulAut.conj g * (g2FieldHom K ρ * g2FieldHom K τ)
            = MulAut.conj g * g2FieldHom K ρ * g2FieldHom K τ := by group
          _ = g2FieldHom K τ * MulAut.conj g * g2FieldHom K ρ := by rw [h1]; group
          _ = MulAut.conj (g2FieldHom K τ g) * g2FieldHom K τ * g2FieldHom K ρ := by rw [h2']
          _ = MulAut.conj (g2FieldHom K τ g) * (g2FieldHom K τ * g2FieldHom K ρ) := by group
          _ = _ := by rw [← hρτ]
      have h4 : MulAut.conj g = MulAut.conj (g2FieldHom K τ g) := mul_right_cancel h3'
      have hinj : Function.Injective
          (MulAut.conj : adjointGroup Tag.G2 K →* MulAut (adjointGroup Tag.G2 K)) :=
        mulAut_conj_injective_of_center_bot hcenter
      exact (hinj h4).symm
    have hgJ : (g : ModGL Tag.G2 K) ∈ fixedFieldImage Tag.G2 τ :=
      (g2_mem_fixSub_iff τ g).1 hgfix
    have hfix : ∀ j : adjointGroup Tag.G2 K, (j : ModGL Tag.G2 K) ∈ fixedFieldImage Tag.G2 τ →
        (g : ModGL Tag.G2 K) * Units.map (entrywiseHom ρ.toRingHom) (j : ModGL Tag.G2 K) *
          (g : ModGL Tag.G2 K)⁻¹ = j := by
      intro j hj
      have h1 : ζ' j = j := hfixΦ j (mem_fixSub.1 ((g2_mem_fixSub_iff τ j).2 hj))
      have h2' := congrArg (fun y : adjointGroup Tag.G2 K => (y : ModGL Tag.G2 K)) h1
      simp only [hg, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, coe_g2FieldHom,
        Subgroup.coe_inv] at h2'
      exact h2'
    obtain ⟨hg1, hρk⟩ := eq_one_of_forall_fixedFieldImage_faithful (σ := τ)
      (fun g' ψ h => g2_hfaith hp hp2 hm1 (fixSubfield τ) hkcard g' ψ h) hgJ ρ hfix
    obtain ⟨fr, hfr, hordfr, htop, -⟩ := finite_field_automorphism_fixed_field_cardinality hp hf hK
    obtain ⟨l, hl⟩ : ∃ l : ℕ, fr ^ l = ρ := by
      have hmem : ρ ∈ Subgroup.zpowers fr := htop ▸ Subgroup.mem_top ρ
      obtain ⟨k, hk⟩ := hmem
      refine ⟨(k % (orderOf fr : ℤ)).toNat, ?_⟩
      rw [← hk, ← zpow_natCast]
      rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by
        have : 0 < orderOf fr := orderOf_pos fr
        omega))]
      exact zpow_mod_orderOf fr k
    have hlk : ∀ x : fixSubfield τ, x ^ p ^ l = x := by
      intro x
      have h1 := hρk x x.2
      rw [← hl, ringAut_pow_apply_of_frobenius hfr l] at h1
      exact Subtype.ext (by simpa using h1)
    have hml : f / r ∣ l := dvd_of_forall_pow_prime_pow_eq hp (fixSubfield τ) hkcard hlk
    have hρr : ρ ^ r = 1 := by
      rw [← hl, ← pow_mul]
      have : f ∣ l * r := by
        obtain ⟨c, hc⟩ := hml
        refine ⟨c, ?_⟩
        have hfr' : f = r * (f / r) := (Nat.mul_div_cancel' hrf).symm
        rw [hc]
        calc f / r * c * r = (r * (f / r)) * c := by ring
          _ = f * c := by rw [← hfr']
      rw [← hordfr] at this
      exact orderOf_dvd_iff_pow_eq_one.1 this
    have hζ'ρ : ζ' = g2FieldHom K ρ := by rw [hg, hg1, map_one, one_mul]
    have hζ'r : ζ' ^ r = 1 := by rw [hζ'ρ, ← map_pow, hρr, map_one]
    have hordζ : orderOf ζ' ∣ r := orderOf_dvd_of_pow_eq_one hζ'r
    have hcop' : Nat.Coprime (orderOf ζ') r := by rw [hord]; exact hζcop
    have h1 : orderOf ζ' = 1 := Nat.Coprime.eq_one_of_dvd hcop' hordζ
    have h2' : ζ' = 1 := orderOf_eq_one_iff.1 h1
    have h3' : ζ = δ⁻¹ * ζ' * δ := by rw [hζ']; group
    rw [h3', h2']
    group

end Last

end G2FieldMain


end CFSG.GH74.GLS.Stage2.Bender.Thm1
