module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3SylowActionKFacts
import CFSG.Quasithin.Recognition.CertF9
public import CFSG.Adapters.LinearFieldTransport
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Cardinality

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open Matrix Subgroup CFSG.Quasithin CFSG.Open

private abbrev SL29 := Matrix.SpecialLinearGroup (Fin 2) GF9

private abbrev PSL29 := Matrix.ProjectiveSpecialLinearGroup (Fin 2) GF9

private def um (a : GF9) : SL29 :=
  ⟨!![1, a; 0, 1], by rw [Matrix.det_fin_two_of]; simp⟩

private def hdi : SL29 :=
  ⟨!![GF9.ofNat' 3, 0; 0, (GF9.ofNat' 3)⁻¹], by rw [Matrix.det_fin_two_of]; decide⟩

private def hdw : SL29 :=
  ⟨!![GF9.ofNat' 4, 0; 0, (GF9.ofNat' 4)⁻¹], by rw [Matrix.det_fin_two_of]; decide⟩

private theorem um_mul : ∀ a b : GF9, um a * um b = um (a + b) := by decide +kernel

private theorem um_zero : um 0 = 1 := by decide +kernel

private theorem hdi_conj : ∀ a : GF9, hdi * um a * hdi⁻¹ = um (-a) := by decide +kernel

private theorem hdi_inv_conj : ∀ a : GF9, hdi⁻¹ * um a * hdi = um (-a) := by decide +kernel

private theorem hdw_conj : ∀ a : GF9, hdw * um a * hdw⁻¹ = um (GF9.ofNat' 6 * a) := by
  decide +kernel

private theorem hdw_inv_conj : ∀ a : GF9, hdw⁻¹ * um a * hdw = um (GF9.ofNat' 3 * a) := by
  decide +kernel

private theorem um_center_inj : ∀ b c : GF9,
    (∃ r : GF9, r ^ Fintype.card (Fin 2) = 1 ∧
      Matrix.scalar (Fin 2) r = (((um b)⁻¹ * um c : SL29) : Matrix (Fin 2) (Fin 2) GF9)) →
    b = c := by
  decide +kernel

private theorem um_inj_mod_center {b c : GF9}
    (h : (QuotientGroup.mk (um b) : PSL29) = QuotientGroup.mk (um c)) : b = c := by
  have h1 : (um b)⁻¹ * um c ∈ Subgroup.center SL29 := QuotientGroup.eq.mp h
  exact um_center_inj b c (Matrix.SpecialLinearGroup.mem_center_iff.mp h1)

private def uHom : Multiplicative GF9 →* PSL29 where
  toFun a := QuotientGroup.mk (um (Multiplicative.toAdd a))
  map_one' := by
    change (QuotientGroup.mk (um 0) : PSL29) = 1
    rw [um_zero]
    rfl
  map_mul' a b := by
    change (QuotientGroup.mk (um (Multiplicative.toAdd a + Multiplicative.toAdd b)) : PSL29) =
      QuotientGroup.mk (um (Multiplicative.toAdd a)) *
        QuotientGroup.mk (um (Multiplicative.toAdd b))
    rw [← um_mul]
    rfl

private theorem uHom_injective : Function.Injective uHom := fun _ _ h =>
  Multiplicative.toAdd.injective (um_inj_mod_center h)

private theorem uHom_card : Nat.card uHom.range = 3 ^ 2 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective uHom_injective).toEquiv, Nat.card_eq_fintype_card]
  decide

private def ut (a : GF9) : PSL29 := uHom (Multiplicative.ofAdd a)

private theorem ut_mul (a b : GF9) : ut a * ut b = ut (a + b) := by
  unfold ut
  rw [← map_mul]
  rfl

private theorem ut_zero : ut 0 = 1 := by
  unfold ut
  exact map_one uHom

private theorem ut_inj {a b : GF9} (h : ut a = ut b) : a = b :=
  Multiplicative.ofAdd.injective (uHom_injective h)

private theorem ut_inv (a : GF9) : (ut a)⁻¹ = ut (-a) := by
  unfold ut
  rw [← map_inv]
  rfl

private theorem mem_range_iff {x : PSL29} : x ∈ uHom.range ↔ ∃ a, x = ut a := by
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨Multiplicative.toAdd a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨Multiplicative.ofAdd a, rfl⟩

private theorem ut_cube (a : GF9) : ut a * ut a * ut a = 1 := by
  rw [ut_mul, ut_mul, show a + a + a = 0 from by revert a; decide, ut_zero]

private theorem conj_ut (h : SL29) (c : GF9 → GF9)
    (hc : ∀ a, h * um a * h⁻¹ = um (c a)) (a : GF9) :
    (QuotientGroup.mk h : PSL29) * ut a * (QuotientGroup.mk h)⁻¹ = ut (c a) := by
  change (QuotientGroup.mk h : PSL29) * QuotientGroup.mk (um a) * (QuotientGroup.mk h)⁻¹ =
    QuotientGroup.mk (um (c a))
  rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hc]

private theorem inv_conj_ut (h : SL29) (c : GF9 → GF9)
    (hc : ∀ a, h⁻¹ * um a * h = um (c a)) (a : GF9) :
    (QuotientGroup.mk h : PSL29)⁻¹ * ut a * (QuotientGroup.mk h) = ut (c a) := by
  change (QuotientGroup.mk h : PSL29)⁻¹ * QuotientGroup.mk (um a) * (QuotientGroup.mk h) =
    QuotientGroup.mk (um (c a))
  rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hc]

private theorem six_moves : ∀ a : GF9, a ≠ 0 →
    GF9.ofNat' 6 * a ≠ 0 ∧ GF9.ofNat' 6 * a ≠ a ∧ GF9.ofNat' 6 * a ≠ a + a := by
  decide

private theorem mem_normalizer_of_conj {K : Type} [Group K] {T₀ : Subgroup K} {n : K}
    (h : ∀ t ∈ T₀, n * t * n⁻¹ ∈ T₀) (h' : ∀ t ∈ T₀, n⁻¹ * t * n ∈ T₀) :
    n ∈ normalizer (T₀ : Set K) := by
  rw [mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  have := h' _ hx
  simpa [mul_assoc] using this

private theorem mk_mem_normalizer (h : SL29) (c c' : GF9 → GF9)
    (hc : ∀ a, h * um a * h⁻¹ = um (c a)) (hc' : ∀ a, h⁻¹ * um a * h = um (c' a)) :
    (QuotientGroup.mk h : PSL29) ∈ normalizer (uHom.range : Set PSL29) := by
  refine mem_normalizer_of_conj (fun t ht => ?_) (fun t ht => ?_)
  · obtain ⟨a, rfl⟩ := mem_range_iff.mp ht
    rw [conj_ut h c hc]
    exact mem_range_iff.mpr ⟨_, rfl⟩
  · obtain ⟨a, rfl⟩ := mem_range_iff.mp ht
    rw [inv_conj_ut h c' hc' a]
    exact mem_range_iff.mpr ⟨_, rfl⟩

private theorem psl29_model :
    ∃ n₁ n₂ : PSL29, n₁ ∈ normalizer (uHom.range : Set PSL29) ∧
      n₂ ∈ normalizer (uHom.range : Set PSL29) ∧
      (∀ t ∈ uHom.range, n₁ * t * n₁⁻¹ = t⁻¹) ∧
      ∀ t ∈ uHom.range, t ≠ 1 → n₂ * t * n₂⁻¹ ∉ zpowers t := by
  refine ⟨QuotientGroup.mk hdi, QuotientGroup.mk hdw,
    mk_mem_normalizer hdi (fun a => -a) (fun a => -a) hdi_conj hdi_inv_conj,
    mk_mem_normalizer hdw (fun a => GF9.ofNat' 6 * a) (fun a => GF9.ofNat' 3 * a) hdw_conj
      hdw_inv_conj, ?_, ?_⟩
  · intro t ht
    obtain ⟨a, rfl⟩ := mem_range_iff.mp ht
    rw [conj_ut hdi (fun a => -a) hdi_conj, ut_inv]
  · intro t ht ht1 hmem
    obtain ⟨a, rfl⟩ := mem_range_iff.mp ht
    have ha : a ≠ 0 := fun h0 => ht1 (by rw [h0, ut_zero])
    rw [conj_ut hdw (fun a => GF9.ofNat' 6 * a) hdw_conj] at hmem
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hmem
    have h3 : ut a ^ (3 : ℤ) = 1 := by
      rw [zpow_ofNat, pow_succ, pow_two]
      exact ut_cube a
    rw [zpow_eq_zpow_emod k h3] at hk
    obtain ⟨h60, h6a, h6aa⟩ := six_moves a ha
    have hk3 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases hk3 with h | h | h
    · rw [h, zpow_zero, ← ut_zero] at hk
      exact h60 (ut_inj hk).symm
    · rw [h, zpow_one] at hk
      exact h6a (ut_inj hk).symm
    · rw [h, show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, pow_two, ut_mul] at hk
      exact h6aa (ut_inj hk).symm

private theorem sylow_action_of_model {K : Type} [Group K] [Finite K] (hK : Nat.card K = 360)
    (T₀ : Subgroup K) (hT₀ : Nat.card T₀ = 3 ^ 2) {n₁ n₂ : K}
    (hn₁ : n₁ ∈ normalizer (T₀ : Set K)) (hn₂ : n₂ ∈ normalizer (T₀ : Set K))
    (h1 : ∀ t ∈ T₀, n₁ * t * n₁⁻¹ = t⁻¹)
    (h2 : ∀ t ∈ T₀, t ≠ 1 → n₂ * t * n₂⁻¹ ∉ zpowers t) (T : Sylow 3 K) :
    (∃ n ∈ normalizer ((T : Subgroup K) : Set K), ∀ t ∈ (T : Subgroup K), n * t * n⁻¹ = t⁻¹) ∧
    ∀ t ∈ (T : Subgroup K), t ≠ 1 →
      ∃ n ∈ normalizer ((T : Subgroup K) : Set K), n * t * n⁻¹ ∉ zpowers t := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 T₀ := IsPGroup.of_card hT₀
  have hidx : ¬ 3 ∣ T₀.index := by
    have h := T₀.index_mul_card
    rw [hT₀, hK] at h
    have : T₀.index = 40 := by omega
    rw [this]
    norm_num
  let S₀ : Sylow 3 K := hp.toSylow hidx
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K S₀ T
  have hT : ∀ t, t ∈ (T : Subgroup K) ↔ g⁻¹ * t * g ∈ T₀ := by
    intro t
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨s, hs, hst⟩
      have : g⁻¹ * t * g = s := by
        rw [← hst]
        simp [MulAut.smul_def, MulAut.conj_apply, mul_assoc]
      rw [this]
      exact hs
    · intro ht
      refine ⟨g⁻¹ * t * g, ht, ?_⟩
      simp [MulAut.smul_def, MulAut.conj_apply, mul_assoc]
  have hnorm : ∀ n : K, n ∈ normalizer (T₀ : Set K) →
      g * n * g⁻¹ ∈ normalizer ((T : Subgroup K) : Set K) := by
    intro n hn
    rw [mem_normalizer_iff] at hn ⊢
    intro x
    rw [hT x, hT (g * n * g⁻¹ * x * (g * n * g⁻¹)⁻¹)]
    have := hn (g⁻¹ * x * g)
    simpa [mul_assoc] using this
  refine ⟨⟨g * n₁ * g⁻¹, hnorm n₁ hn₁, fun t ht => ?_⟩, fun t ht ht1 => ?_⟩
  · have hs := h1 (g⁻¹ * t * g) ((hT t).mp ht)
    calc g * n₁ * g⁻¹ * t * (g * n₁ * g⁻¹)⁻¹ = g * (n₁ * (g⁻¹ * t * g) * n₁⁻¹) * g⁻¹ := by group
      _ = g * (g⁻¹ * t * g)⁻¹ * g⁻¹ := by rw [hs]
      _ = t⁻¹ := by group
  · refine ⟨g * n₂ * g⁻¹, hnorm n₂ hn₂, fun hmem => ?_⟩
    have hs := h2 (g⁻¹ * t * g) ((hT t).mp ht) (by
      intro h
      apply ht1
      calc t = g * (g⁻¹ * t * g) * g⁻¹ := by group
        _ = 1 := by rw [h]; group)
    apply hs
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hmem
    refine mem_zpowers_iff.mpr ⟨k, ?_⟩
    have h3 : g⁻¹ * (g * n₂ * g⁻¹ * t * (g * n₂ * g⁻¹)⁻¹) * g = n₂ * (g⁻¹ * t * g) * n₂⁻¹ := by
      group
    have h4 : g⁻¹ * t ^ k * g = (g⁻¹ * t * g) ^ k := by
      have := map_zpow (MulAut.conj g⁻¹) t k
      simpa [MulAut.conj_apply, mul_assoc] using this
    calc (g⁻¹ * t * g) ^ k = g⁻¹ * t ^ k * g := h4.symm
      _ = g⁻¹ * (g * n₂ * g⁻¹ * t * (g * n₂ * g⁻¹)⁻¹) * g := by rw [hk]
      _ = n₂ * (g⁻¹ * t * g) * n₂⁻¹ := h3

theorem a6SylowAction_proved : KFactA6SylowAction := by
  intro K _ _ hK T
  obtain ⟨eK⟩ := hK
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcardF : Nat.card GF9 = 3 ^ 2 := by
    rw [Nat.card_eq_fintype_card]
    decide
  let eF : GF9 ≃+* GaloisField 3 2 :=
    CFSG.ClassicalModels.finiteFieldEquivGaloisField GF9 3 2 (by norm_num) hcardF
  let eG : K ≃* PSL29 :=
    eK.trans (CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv eF (Fin 2)).symm
  have hK360 : Nat.card K = 360 := by
    rw [Nat.card_congr eK.toEquiv]
    have hc : Nat.card (GaloisField 3 2) = 3 ^ 2 := GaloisField.card 3 2 (by norm_num)
    have hodd : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card (GaloisField 3 2)) :=
      ⟨3, 2, by norm_num, by decide, by norm_num, hc⟩
    have h := CFSG.GorensteinWalter.psl2_card_formula (GaloisField 3 2) hodd
    rw [hc] at h
    norm_num at h
    exact h
  obtain ⟨n₁, n₂, hn₁, hn₂, h1, h2⟩ := psl29_model
  let T₀ : Subgroup K := uHom.range.map eG.symm.toMonoidHom
  have hmem : ∀ x : K, x ∈ T₀ ↔ eG x ∈ uHom.range := fun x => by
    rw [Subgroup.mem_map_equiv]
    rfl
  have hT₀ : Nat.card T₀ = 3 ^ 2 := by
    rw [← uHom_card]
    exact Nat.card_congr (Subgroup.equivMapOfInjective _ _ eG.symm.injective).symm.toEquiv
  have hnorm : ∀ n : PSL29, n ∈ normalizer (uHom.range : Set PSL29) →
      eG.symm n ∈ normalizer (T₀ : Set K) := by
    intro n hn
    rw [mem_normalizer_iff] at hn ⊢
    intro x
    rw [hmem, hmem]
    simpa using hn (eG x)
  obtain ⟨hinv, hmove⟩ := sylow_action_of_model hK360 T₀ hT₀ (n₁ := eG.symm n₁)
    (n₂ := eG.symm n₂) (hnorm n₁ hn₁) (hnorm n₂ hn₂)
    (fun t ht => by
      apply eG.injective
      simpa using h1 (eG t) ((hmem t).mp ht))
    (fun t ht ht1 hz => by
      apply h2 (eG t) ((hmem t).mp ht) (fun h => ht1 (eG.injective (by simpa using h)))
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hz
      refine mem_zpowers_iff.mpr ⟨k, ?_⟩
      apply eG.symm.injective
      simpa [map_zpow] using hk) T
  exact ⟨hinv, hmove⟩

private theorem six_six : ∀ a : GF9, GF9.ofNat' 6 * (GF9.ofNat' 6 * a) = -a := by decide

private theorem psl29_rotation :
    ∃ n : PSL29, n ∈ normalizer (uHom.range : Set PSL29) ∧
      ∀ t ∈ uHom.range, n * (n * t * n⁻¹) * n⁻¹ = t⁻¹ := by
  refine ⟨QuotientGroup.mk hdw, mk_mem_normalizer hdw (fun a => GF9.ofNat' 6 * a)
    (fun a => GF9.ofNat' 3 * a) hdw_conj hdw_inv_conj, fun t ht => ?_⟩
  obtain ⟨a, rfl⟩ := mem_range_iff.mp ht
  rw [conj_ut hdw (fun a => GF9.ofNat' 6 * a) hdw_conj,
    conj_ut hdw (fun a => GF9.ofNat' 6 * a) hdw_conj, ut_inv]
  exact congrArg ut (six_six a)

private theorem sylow_rotation_of_model {K : Type} [Group K] [Finite K] (hK : Nat.card K = 360)
    (T₀ : Subgroup K) (hT₀ : Nat.card T₀ = 3 ^ 2) {n : K} (hn : n ∈ normalizer (T₀ : Set K))
    (h : ∀ t ∈ T₀, n * (n * t * n⁻¹) * n⁻¹ = t⁻¹) (T : Sylow 3 K) :
    ∃ ρ ∈ normalizer ((T : Subgroup K) : Set K),
      ∀ t ∈ (T : Subgroup K), ρ * (ρ * t * ρ⁻¹) * ρ⁻¹ = t⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 T₀ := IsPGroup.of_card hT₀
  have hidx : ¬ 3 ∣ T₀.index := by
    have h := T₀.index_mul_card
    rw [hT₀, hK] at h
    have : T₀.index = 40 := by omega
    rw [this]
    norm_num
  let S₀ : Sylow 3 K := hp.toSylow hidx
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K S₀ T
  have hT : ∀ t, t ∈ (T : Subgroup K) ↔ g⁻¹ * t * g ∈ T₀ := by
    intro t
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨s, hs, hst⟩
      have : g⁻¹ * t * g = s := by
        rw [← hst]
        simp [MulAut.smul_def, MulAut.conj_apply, mul_assoc]
      rw [this]
      exact hs
    · intro ht
      refine ⟨g⁻¹ * t * g, ht, ?_⟩
      simp [MulAut.smul_def, MulAut.conj_apply, mul_assoc]
  have hnorm : g * n * g⁻¹ ∈ normalizer ((T : Subgroup K) : Set K) := by
    rw [mem_normalizer_iff] at hn ⊢
    intro x
    rw [hT x, hT (g * n * g⁻¹ * x * (g * n * g⁻¹)⁻¹)]
    have := hn (g⁻¹ * x * g)
    simpa [mul_assoc] using this
  refine ⟨g * n * g⁻¹, hnorm, fun t ht => ?_⟩
  have hs := h (g⁻¹ * t * g) ((hT t).mp ht)
  calc g * n * g⁻¹ * (g * n * g⁻¹ * t * (g * n * g⁻¹)⁻¹) * (g * n * g⁻¹)⁻¹
      = g * (n * (n * (g⁻¹ * t * g) * n⁻¹) * n⁻¹) * g⁻¹ := by group
    _ = g * (g⁻¹ * t * g)⁻¹ * g⁻¹ := by rw [hs]
    _ = t⁻¹ := by group

theorem a6SylowRotation_proved : ∀ (K : Type) [Group K] [Finite K], IsRankThreeA6 K →
    ∀ T : Sylow 3 K, ∃ ρ ∈ normalizer ((T : Subgroup K) : Set K),
      ∀ t ∈ (T : Subgroup K), ρ * (ρ * t * ρ⁻¹) * ρ⁻¹ = t⁻¹ := by
  intro K _ _ hK T
  obtain ⟨eK⟩ := hK
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcardF : Nat.card GF9 = 3 ^ 2 := by
    rw [Nat.card_eq_fintype_card]
    decide
  let eF : GF9 ≃+* GaloisField 3 2 :=
    CFSG.ClassicalModels.finiteFieldEquivGaloisField GF9 3 2 (by norm_num) hcardF
  let eG : K ≃* PSL29 :=
    eK.trans (CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv eF (Fin 2)).symm
  have hK360 : Nat.card K = 360 := by
    rw [Nat.card_congr eK.toEquiv]
    have hc : Nat.card (GaloisField 3 2) = 3 ^ 2 := GaloisField.card 3 2 (by norm_num)
    have hodd : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card (GaloisField 3 2)) :=
      ⟨3, 2, by norm_num, by decide, by norm_num, hc⟩
    have h := CFSG.GorensteinWalter.psl2_card_formula (GaloisField 3 2) hodd
    rw [hc] at h
    norm_num at h
    exact h
  obtain ⟨n, hn, hrot⟩ := psl29_rotation
  let T₀ : Subgroup K := uHom.range.map eG.symm.toMonoidHom
  have hmem : ∀ x : K, x ∈ T₀ ↔ eG x ∈ uHom.range := fun x => by
    rw [Subgroup.mem_map_equiv]
    rfl
  have hT₀ : Nat.card T₀ = 3 ^ 2 := by
    rw [← uHom_card]
    exact Nat.card_congr (Subgroup.equivMapOfInjective _ _ eG.symm.injective).symm.toEquiv
  have hnorm : eG.symm n ∈ normalizer (T₀ : Set K) := by
    rw [mem_normalizer_iff] at hn ⊢
    intro x
    rw [hmem, hmem]
    simpa using hn (eG x)
  exact sylow_rotation_of_model hK360 T₀ hT₀ hnorm (fun t ht => by
    apply eG.injective
    simpa using hrot (eG t) ((hmem t).mp ht)) T

end CFSG.LocalAnalysis.RankThreeTheoremC
