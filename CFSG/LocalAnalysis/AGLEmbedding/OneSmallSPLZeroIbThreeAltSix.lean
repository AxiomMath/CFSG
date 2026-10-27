module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLZeroThreeTorus
public import CFSG.LocalAnalysis.ComponentInitial.FieldNineAlternatingSix
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.ComponentInitial

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M H R : Subgroup G}
  {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}

theorem D1OneSmallData.exists_torus_altSix_cz (h3 : D1PhaseThree 3 P M H R)
    (hd : D1OneSmallData 3 P M H R Rbar K) (hA6 : IsAltTwoP 3 K) {z : G}
    (hz : D1SmallCZElt 3 H R K z) :
    ∃ φ : Multiplicative (GaloisField 3 2) ≃* d1LiftX 3 H R K,
      ∀ μ : (GaloisField 3 2)ˣ, ∃ t ∈ H ⊓ M, t * z = z * t ∧
        ∀ a : Multiplicative (GaloisField 3 2), t * (φ a : G) * t⁻¹ =
          φ (Multiplicative.ofAdd ((μ : GaloisField 3 2) ^ 2 * Multiplicative.toAdd a)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hzR, -, hzH, hzc⟩ := hz
  obtain ⟨T, hT, -⟩ := hd.exists_sylow
  obtain ⟨e₁⟩ := hA6
  have : Fintype (GaloisField 3 2) := Fintype.ofFinite _
  have hcard9 : Fintype.card (GaloisField 3 2) = 9 := by
    rw [Fintype.card_eq_nat_card, GaloisField.card 3 2 (by norm_num)]
    norm_num
  obtain ⟨e₂⟩ :=
    unique_field_nine_projective_linear_alternating_six_isomorphism (GaloisField 3 2) hcard9
  set f : K ≃* PSL2GF 3 2 := e₁.trans e₂.symm
  have hfs : Function.Surjective (f : K →* PSL2GF 3 2) := f.surjective
  set U : Sylow 3 (PSL2GF 3 2) := T.mapSurjective hfs
  have hUT : (U : Subgroup (PSL2GF 3 2)) = (T : Subgroup K).map (f : K →* PSL2GF 3 2) :=
    Sylow.coe_mapSurjective hfs T
  have hTcard : Nat.card (T : Subgroup K) = 3 ^ 2 := by
    rw [← (psl2GF_sylow 3 2 (by norm_num) U).2, hUT, Subgroup.card_map_of_injective
      (show Function.Injective (f : K →* PSL2GF 3 2) from f.injective)]
  have hcard : Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) ⊓ K :
      Subgroup _) = 3 ^ 2 := by
    rw [← hT, Subgroup.card_map_of_injective K.subtype_injective, hTcard]
  obtain ⟨ψ, hψinj, hψrange, hc⟩ := exists_torus_param_of_mulEquiv_psl2GF (by norm_num)
    (by norm_num) f ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) ⊓ K) inf_le_right
    hcard
  obtain ⟨z', hzR', hzK', hzp', hzc'⟩ := hd.z
  obtain ⟨hN, -⟩ := hd.cfg.red.rankOne_principle hd.comp hd.noncyclic hzR' hzK' hzp' hzc'
  have hT1 : (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) ⊓ K ≠ ⊥ :=
    fun h => hd.noncyclic (by rw [h]; infer_instance)
  set O := primeComplementCore (G := H) 3 with hOdef
  set X := d1LiftX 3 H R K with hXdef
  have hXH : X ≤ H := d1LiftX_le_H 3 H R K
  set zH : H := ⟨z, hzH⟩ with hzHdef
  have hcY : ∀ μ : (GaloisField 3 2)ˣ,
      ∃ c ∈ ((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' O),
        c * QuotientGroup.mk' O zH = QuotientGroup.mk' O zH * c ∧
        ∀ a : Multiplicative (GaloisField 3 2),
          c * ψ a * c⁻¹ =
            ψ (Multiplicative.ofAdd ((μ : GaloisField 3 2) ^ 2 * Multiplicative.toAdd a)) := by
    intro μ
    obtain ⟨c, hcK, hcψ⟩ := hc μ
    have hcN : c ∈ K ⊓ Subgroup.normalizer
        (((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) ⊓ K : Subgroup _) :
          Set (H ⧸ primeComplementCore (G := H) 3)) :=
      ⟨hcK, by rw [← hψrange]; exact mem_normalizer_range_of_torus ψ μ.ne_zero hcψ⟩
    exact ⟨c, hN _ le_rfl hT1 hcN, Subgroup.mem_centralizer_iff.mp hzc c hcK, hcψ⟩
  have hXz : IsPGroup 3 ((X.subgroupOf H) ⊔ Subgroup.zpowers zH : Subgroup H) := by
    have hle : (X.subgroupOf H) ⊔ Subgroup.zpowers zH ≤ R.subgroupOf H := by
      refine sup_le (Subgroup.subgroupOf_mono H (d1LiftX_le 3 H R K)) ?_
      rw [Subgroup.zpowers_le]
      exact Subgroup.mem_subgroupOf.mpr hzR
    exact (hd.cfg.ext.isPGroup.comap_subtype (K := H)).to_le hle
  have hNB : O ≤ (H ⊓ M).subgroupOf H := fun o ho =>
    Subgroup.mem_subgroupOf.mpr
      (le_inf (glbPrimeCore_le 3 H) h3.primeCore_le
        ((mem_glbPrimeCore_iff_mk_eq_one o).mpr ((QuotientGroup.eq_one_iff o).mpr ho)))
  have hψX : ψ.range = (X.subgroupOf H).map (QuotientGroup.mk' O) := by
    rw [hψrange, hd.cfg.map_d1LiftX_eq_inf]
  obtain ⟨φ, hφ⟩ := exists_torus_of_map_eq_cz Fact.out O (primeComplementCore_coprime 3) hXz hNB
    ψ hψinj hψX hcY
  refine ⟨φ.trans (Subgroup.subgroupOfEquivOfLe hXH), fun μ => ?_⟩
  obtain ⟨t, ht, htz, htφ⟩ := hφ μ
  refine ⟨t, Subgroup.mem_subgroupOf.mp ht, congrArg Subtype.val htz, fun a => ?_⟩
  exact congrArg Subtype.val (htφ a)

theorem conj_pow_apply_of_mul {Y : Type*} [Group Y] {F : Type*} [Field F]
    (φ : Multiplicative F →* Y) {c : Y} {l : F}
    (hc : ∀ a : Multiplicative F,
      c * φ a * c⁻¹ = φ (Multiplicative.ofAdd (l * Multiplicative.toAdd a)))
    (k : ℕ) (a : Multiplicative F) :
    c ^ k * φ a * (c ^ k)⁻¹ = φ (Multiplicative.ofAdd (l ^ k * Multiplicative.toAdd a)) := by
  induction k generalizing a with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_inv_rev]
    calc c * c ^ k * φ a * ((c ^ k)⁻¹ * c⁻¹) = c * (c ^ k * φ a * (c ^ k)⁻¹) * c⁻¹ := by group
      _ = φ (Multiplicative.ofAdd (l ^ (k + 1) * Multiplicative.toAdd a)) := by
        rw [ih, hc]
        congr 2
        simp only [toAdd_ofAdd]
        ring

theorem not_mem_normalizer_of_mul_sq {X : Subgroup G}
    (φ : Multiplicative (GaloisField 3 2) ≃* X) {t : G} {ν : GaloisField 3 2}
    (hν4 : ν ^ 4 = -1)
    (htφ : ∀ b : Multiplicative (GaloisField 3 2),
      t * (φ b : G) * t⁻¹ = φ (Multiplicative.ofAdd (ν ^ 2 * Multiplicative.toAdd b)))
    (F : Subgroup G) (hFX : F ≤ X) (hF3 : Nat.card F = 3) :
    t ∉ Subgroup.normalizer (F : Set G) := by
  intro htF
  have hφmem : ∀ x ∈ X, ∃ b : Multiplicative (GaloisField 3 2), (φ b : G) = x := fun x hx =>
    ⟨φ.symm ⟨x, hx⟩, by simp⟩
  have hφinj : ∀ b b' : Multiplicative (GaloisField 3 2), (φ b : G) = φ b' → b = b' :=
    fun b b' h => φ.injective (Subtype.ext h)
  have hF1 : (⊥ : Subgroup G) ≠ F := fun h => by
    rw [← h, Subgroup.card_bot] at hF3
    norm_num at hF3
  obtain ⟨f', hf'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp (Ne.symm hF1)
  have hfF : (f' : G) ∈ F := f'.2
  have hf1 : (f' : G) ≠ 1 := fun h => hf' (Subtype.ext h)
  obtain ⟨b, hbf⟩ := hφmem (f' : G) (hFX hfF)
  rw [← hbf] at hfF hf1
  have hb : b ≠ 1 := fun h => hf1 (by rw [h, map_one, Subgroup.coe_one])
  have hfo : orderOf (φ b : G) = 3 := by
    have h1 := Subgroup.orderOf_dvd_natCard F hfF
    rw [hF3] at h1
    rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hf1
    · exact h
  have hFz : F = Subgroup.zpowers (φ b : G) := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hfF) ?_).symm
    rw [Nat.card_zpowers, hfo, hF3]
  have hconj := (Subgroup.mem_normalizer_iff.mp htF (φ b : G)).mp hfF
  rw [hFz, Subgroup.mem_zpowers_iff] at hconj
  obtain ⟨k, hk⟩ := hconj
  rw [← zpow_mod_orderOf, hfo] at hk
  have hk3 : k % (3 : ℕ) = 0 ∨ k % (3 : ℕ) = 1 ∨ k % (3 : ℕ) = 2 := by omega
  rw [htφ] at hk
  have hb' : Multiplicative.toAdd b ≠ 0 := fun h => hb (by
    rw [← ofAdd_toAdd b, h, ofAdd_zero])
  have hchar : (2 : GaloisField 3 2) ≠ 0 := by
    intro h2
    have : ((2 : ℕ) : GaloisField 3 2) = 0 := by exact_mod_cast h2
    rw [CharP.cast_eq_zero_iff (GaloisField 3 2) 3] at this
    norm_num at this
  rcases hk3 with h | h | h <;> rw [h] at hk
  ·
    rw [zpow_zero] at hk
    have : (φ (Multiplicative.ofAdd (ν ^ 2 * Multiplicative.toAdd b)) : G) = φ 1 := by
      rw [map_one, Subgroup.coe_one]; exact hk.symm
    have h1 := congrArg Multiplicative.toAdd (hφinj _ _ this)
    simp only [toAdd_ofAdd, toAdd_one, mul_eq_zero] at h1
    rcases h1 with h1 | h1
    · have : ν ^ 4 = 0 := by
        rw [show 4 = 2 * 2 by norm_num, pow_mul, h1, zero_pow (by norm_num)]
      rw [hν4] at this
      norm_num at this
    · exact hb' h1
  ·
    rw [zpow_one] at hk
    have h1 := congrArg Multiplicative.toAdd (hφinj _ _ hk.symm)
    simp only [toAdd_ofAdd] at h1
    have hν2 : ν ^ 2 = 1 := mul_right_cancel₀ hb' (h1.trans (one_mul _).symm)
    have : ν ^ 4 = 1 := by
      rw [show 4 = 2 * 2 by norm_num, pow_mul, hν2, one_pow]
    rw [hν4] at this
    exact hchar (by linear_combination -this)
  ·
    have hf2 : (φ b : G) ^ (2 : ℤ) = φ b⁻¹ := by
      rw [map_inv, Subgroup.coe_inv, ← zpow_neg_one]
      rw [zpow_eq_zpow_iff_modEq, hfo]
      decide
    rw [hf2] at hk
    have h1 := congrArg Multiplicative.toAdd (hφinj _ _ hk.symm)
    simp only [toAdd_ofAdd, toAdd_inv] at h1
    have hν2 : ν ^ 2 = -1 := by
      have : (ν ^ 2 + 1) * Multiplicative.toAdd b = 0 := by
        linear_combination h1
      rcases mul_eq_zero.mp this with h | h
      · linear_combination h
      · exact absurd h hb'
    have : ν ^ 4 = 1 := by
      rw [show 4 = 2 * 2 by norm_num, pow_mul, hν2]; norm_num
    rw [hν4] at this
    exact hchar (by linear_combination -this)

theorem D1OneSmallData.exists_torus_altSix_period (h3 : D1PhaseThree 3 P M H R)
    (hd : D1OneSmallData 3 P M H R Rbar K) (hA6 : IsAltTwoP 3 K) {z : G}
    (hz : D1SmallCZElt 3 H R K z) :
    ∃ t : G, t ∈ H ⊓ M ∧ t * z = z * t ∧ Nat.Coprime 3 (orderOf t) ∧
      t ∈ Subgroup.normalizer (d1LiftX 3 H R K : Set G) ∧
      (∀ F : Subgroup G, F ≤ d1LiftX 3 H R K → Nat.card F = 3 →
        t ∉ Subgroup.normalizer (F : Set G)) ∧
      (∀ x ∈ d1LiftX 3 H R K, t ^ 2 * x * (t ^ 2)⁻¹ = x⁻¹) ∧
      Nat.card (d1LiftX 3 H R K) = 9 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set X := d1LiftX 3 H R K with hXdef
  obtain ⟨φ, hφ⟩ := D1OneSmallData.exists_torus_altSix_cz h3 hd hA6 hz
  have : Fintype (GaloisField 3 2) := Fintype.ofFinite _
  have hcard9 : Fintype.card (GaloisField 3 2) = 9 := by
    rw [Fintype.card_eq_nat_card, GaloisField.card 3 2 (by norm_num)]
    norm_num
  obtain ⟨μ, hμ⟩ := IsCyclic.exists_generator (α := (GaloisField 3 2)ˣ)
  have hμ8 : orderOf μ = 8 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hμ, Nat.card_eq_fintype_card, Fintype.card_units,
      hcard9]
  obtain ⟨t₀, ht₀, ht₀z, ht₀φ⟩ := hφ μ
  set a := (orderOf t₀).factorization 3 with ha
  set t := t₀ ^ (3 ^ a) with ht
  have ht₀0 : orderOf t₀ ≠ 0 := (orderOf_pos t₀).ne'
  have hcop : Nat.Coprime 3 (orderOf t) := by
    rw [ht, orderOf_pow' t₀ (pow_ne_zero a (by norm_num)),
      Nat.gcd_eq_right (Nat.ordProj_dvd (orderOf t₀) 3)]
    exact Nat.coprime_ordCompl Nat.prime_three ht₀0
  set ν := μ ^ (3 ^ a) with hν
  have hν8 : orderOf ν = 8 := by
    rw [hν, Nat.Coprime.orderOf_pow (by rw [hμ8]; exact Nat.Coprime.pow_right a (by norm_num)),
      hμ8]
  have htφ : ∀ b : Multiplicative (GaloisField 3 2), t * (φ b : G) * t⁻¹ =
      φ (Multiplicative.ofAdd ((ν : GaloisField 3 2) ^ 2 * Multiplicative.toAdd b)) := by
    intro b
    have h1 := conj_pow_apply_of_mul ((X.subtype).comp φ.toMonoidHom) (c := t₀)
      (l := (μ : GaloisField 3 2) ^ 2) (fun a' => ht₀φ a') (3 ^ a) b
    simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
      MulEquiv.coe_toMonoidHom] at h1
    rw [ht, h1, hν, Units.val_pow_eq_pow_val, ← pow_mul, ← pow_mul, mul_comm 2]
  have hν4 : (ν : GaloisField 3 2) ^ 4 = -1 := by
    have h8 : (ν : GaloisField 3 2) ^ 8 = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← hν8, pow_orderOf_eq_one, Units.val_one]
    have h4 : (ν : GaloisField 3 2) ^ 4 ≠ 1 := by
      intro h
      have : ν ^ 4 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, h, Units.val_one])
      have := orderOf_le_of_pow_eq_one (by norm_num) this
      omega
    have hsq : (ν : GaloisField 3 2) ^ 4 * (ν : GaloisField 3 2) ^ 4 = 1 := by
      rw [← pow_add]; exact h8
    rcases mul_self_eq_one_iff.mp hsq with h | h
    · exact absurd h h4
    · exact h
  have hφmem : ∀ x ∈ X, ∃ b : Multiplicative (GaloisField 3 2), (φ b : G) = x := fun x hx =>
    ⟨φ.symm ⟨x, hx⟩, by simp⟩
  refine ⟨t, (H ⊓ M).pow_mem ht₀ _, ((Commute.pow_left ht₀z (3 ^ a))).eq, hcop, ?_,
    not_mem_normalizer_of_mul_sq φ hν4 htφ, ?_, ?_⟩
  · refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    obtain ⟨b, rfl⟩ := hφmem x hx
    rw [htφ]
    exact (φ _).2
  · intro x hx
    obtain ⟨b, rfl⟩ := hφmem x hx
    have h2 := conj_pow_apply_of_mul ((X.subtype).comp φ.toMonoidHom) (c := t)
      (l := (ν : GaloisField 3 2) ^ 2) (fun a' => htφ a') 2 b
    simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
      MulEquiv.coe_toMonoidHom] at h2
    rw [h2, ← pow_mul, show 2 * 2 = 4 by norm_num, hν4, neg_one_mul]
    have hinvb : Multiplicative.ofAdd (-Multiplicative.toAdd b) = b⁻¹ := rfl
    rw [hinvb, map_inv, Subgroup.coe_inv]
  · rw [← Nat.card_congr φ.toEquiv, Nat.card_congr Multiplicative.toAdd,
      GaloisField.card 3 2 (by norm_num)]
    norm_num

end CFSG.AGLEmbedding
