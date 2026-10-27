module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS09TD4G2A
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.Blueprint.Chevalley (TwistTag)
open CFSG.LieType.Chevalley (graphFixedRootGroup fieldActor fieldActor_one fieldActor_mul
  ringEquiv_cube_apply_eq fixSubfield)
open CFSG.LocalAnalysis.GLTheoremA.CatB (barAut barAut_mk barAut_pow_three conjL conjL_apply)


abbrev td4g2Inn (X : Type) [Group X] : Subgroup (MulAut X) := (MulAut.conj : X →* MulAut X).range

instance td4g2Inn_normal (X : Type) [Group X] : (td4g2Inn X).Normal where
  conj_mem n hn φ := by
    obtain ⟨g, rfl⟩ := hn
    exact ⟨φ g, MulEquiv.ext fun x => by simp [MulAut.conj_apply, MulAut.mul_apply, MulAut.inv_apply]⟩

theorem td4g2_fix_pow {X : Type} [Group X] {β : MulAut X} {y : X} (hy : β y = y) (k : ℕ) :
    (β ^ k) y = y := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ, MulAut.mul_apply, hy, ih]

theorem td4g2_fix_apply {X : Type} [Group X] {β : MulAut X} {v x : X} (hv : β v = v)
    (hx : β x = x) (k : ℕ) : (β ^ k * MulAut.conj v) x = v * x * v⁻¹ := by
  rw [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_mul, map_inv, td4g2_fix_pow hv,
    td4g2_fix_pow hx]

theorem td4g2_commute {X : Type} [Group X] (hZ : ∀ z : X, (∀ x, z * x = x * z) → z = 1)
    {β : MulAut X} (hβ3 : β ^ 3 = 1) {k : ℕ} {v : X} {α : MulAut X}
    (hα : α = β ^ k * MulAut.conj v) (hαβ : α * β = β * α) (hα3 : α ^ 3 = 1) :
    β v = v ∧ v ^ 3 = 1 := by
  have hc : β ^ k * (MulAut.conj v * β) = β ^ k * (β * MulAut.conj v) := by
    calc β ^ k * (MulAut.conj v * β) = (β ^ k * MulAut.conj v) * β := by rw [mul_assoc]
      _ = α * β := by rw [hα]
      _ = β * α := hαβ
      _ = β * (β ^ k * MulAut.conj v) := by rw [hα]
      _ = β ^ k * (β * MulAut.conj v) := by
        rw [← mul_assoc, (Commute.self_pow β k).eq, mul_assoc]
  have h1 : MulAut.conj v * β = β * MulAut.conj v := mul_left_cancel hc
  have hβc : ∀ w : X, β * MulAut.conj w = MulAut.conj (β w) * β := by
    intro w
    refine MulEquiv.ext fun x => ?_
    simp [MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv]
  have h2 : MulAut.conj (β v) = MulAut.conj v := by
    apply mul_right_cancel (b := β)
    rw [← hβc v]
    exact h1.symm
  have hz : v⁻¹ * β v = 1 := by
    apply hZ
    intro x
    have hx := congrArg (fun φ : MulAut X => φ x) h2
    simp only [MulAut.conj_apply] at hx
    have hx' : β v * x = v * x * v⁻¹ * β v := by
      calc β v * x = (β v * x * (β v)⁻¹) * β v := (inv_mul_cancel_right _ _).symm
        _ = (v * x * v⁻¹) * β v := by rw [hx]
    calc v⁻¹ * β v * x = v⁻¹ * (β v * x) := by rw [mul_assoc]
      _ = v⁻¹ * (v * x * v⁻¹ * β v) := by rw [hx']
      _ = x * (v⁻¹ * β v) := by group
  have hβv : β v = v := (inv_mul_eq_one.1 hz).symm
  refine ⟨hβv, ?_⟩
  have hcomm : Commute β (MulAut.conj v) := h1.symm
  have hcomm' : Commute (β ^ k) (MulAut.conj v) := hcomm.pow_left k
  have hcube : (MulAut.conj v) ^ 3 = 1 := by
    have h3 : (β ^ k * MulAut.conj v) ^ 3 = (MulAut.conj v) ^ 3 := by
      rw [hcomm'.mul_pow, ← pow_mul, mul_comm k 3, pow_mul, hβ3, one_pow, one_mul]
    rw [← h3, ← hα]
    exact hα3
  apply hZ
  intro x
  have hc3 : MulAut.conj (v ^ 3) = 1 := by rw [map_pow]; exact hcube
  have h := congrArg (fun φ : MulAut X => φ x) hc3
  simp only [MulAut.conj_apply, MulAut.one_apply] at h
  calc v ^ 3 * x = (v ^ 3 * x * (v ^ 3)⁻¹) * v ^ 3 := by group
    _ = x * v ^ 3 := by rw [h]

section Normal

variable {K : Type} [Field K] [Finite K]

theorem td4g2_normal_form {f : ℕ} (hf : 1 ≤ f) {σ : K ≃+* K} (hK : Nat.card K = (2 ^ f) ^ 3)
    (hσ : ∀ c, σ c = c ^ 2 ^ f) {β α : MulAut (td4g2C K σ)} (hβ3 : β ^ 3 = 1)
    (hβ : ¬ CFSG.RankThree.PartTwo.KFacts.IsInnerAut β) (hα3 : α ^ 3 = 1) :
    ∃ (k : ℕ) (v : td4g2C K σ), α = β ^ k * MulAut.conj v := by
  classical
  let mk : MulAut (td4g2C K σ) →* MulAut (td4g2C K σ) ⧸ td4g2Inn (td4g2C K σ) :=
    QuotientGroup.mk' (td4g2Inn (td4g2C K σ))
  have hmk_inn : ∀ g : td4g2C K σ, mk (MulAut.conj g) = 1 := fun g =>
    (QuotientGroup.eq_one_iff _).2 ⟨g, rfl⟩
  set s := mk (fieldActor (t := CFSG.Blueprint.Chevalley.TwistTag.D4) σ σ) with hs
  have hs3 : s ^ 3 = 1 := by
    rw [hs, ← map_pow, td4g2_sigma0_cube hK hσ, map_one]
  have hinv : s⁻¹ = s ^ 2 := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_succ']
    exact hs3
  have hout : ∀ γ : MulAut (td4g2C K σ), γ ^ 3 = 1 →
      ¬ CFSG.RankThree.PartTwo.KFacts.IsInnerAut γ → mk γ = s ∨ mk γ = s⁻¹ := by
    intro γ hγ3 hγ
    obtain ⟨g, hg | hg⟩ :=
      CFSG.RankThree.PartTwo.Sec8.Item8ModelProof.exists_conj_mul_sigma hf hK hσ hγ3 hγ
    · left
      rw [hg, map_mul, hmk_inn, one_mul]
    · right
      rw [hg, map_mul, hmk_inn, one_mul, map_inv]
  have hin : ∀ γ : MulAut (td4g2C K σ), CFSG.RankThree.PartTwo.KFacts.IsInnerAut γ →
      mk γ = 1 := by
    rintro γ ⟨g, rfl⟩
    exact hmk_inn g
  have hαs : mk α = 1 ∨ mk α = s ∨ mk α = s⁻¹ := by
    by_cases hαi : CFSG.RankThree.PartTwo.KFacts.IsInnerAut α
    · exact Or.inl (hin α hαi)
    · exact Or.inr (hout α hα3 hαi)
  have hβs := hout β hβ3 hβ
  have hs4 : s ^ 4 = s := by
    rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, hs3, one_mul]
  obtain ⟨k, hk⟩ : ∃ k : ℕ, mk α = mk β ^ k := by
    rcases hβs with hb | hb <;> rcases hαs with ha | ha | ha
    · exact ⟨0, by rw [ha, pow_zero]⟩
    · exact ⟨1, by rw [ha, hb, pow_one]⟩
    · exact ⟨2, by rw [ha, hb, hinv]⟩
    · exact ⟨0, by rw [ha, pow_zero]⟩
    · exact ⟨2, by rw [ha, hb, hinv, ← pow_mul]; exact hs4.symm⟩
    · exact ⟨1, by rw [ha, hb, pow_one]⟩
  have hk' : mk α = mk (β ^ k) := by rw [map_pow]; exact hk
  have hmem : α⁻¹ * β ^ k ∈ td4g2Inn (td4g2C K σ) := (QuotientGroup.eq).1 hk'
  obtain ⟨w, hw⟩ := hmem
  refine ⟨k, w⁻¹, ?_⟩
  have h1 : α⁻¹ = MulAut.conj w * (β ^ k)⁻¹ := by
    rw [hw]
    group
  calc α = (α⁻¹)⁻¹ := (inv_inv α).symm
    _ = β ^ k * (MulAut.conj w)⁻¹ := by rw [h1, mul_inv_rev, inv_inv]
    _ = β ^ k * MulAut.conj w⁻¹ := by rw [map_inv]

end Normal

theorem td4g2_autFix_conj {X : Type} [Group X] (g α : MulAut X) :
    Nonempty (↥(CFSG.RankThree.PartTwo.Sec4.autFix (g * α * g⁻¹)) ≃*
      ↥(CFSG.RankThree.PartTwo.Sec4.autFix α)) := by
  rw [← CFSG.RankThree.PartTwo.Sec4.mulAut_congr_eq_conj]
  exact ⟨CFSG.RankThree.PartTwo.Sec4.autFixCongrEquiv g α⟩

theorem td4g2_autFix_inv {X : Type} [Group X] (α : MulAut X) :
    CFSG.RankThree.PartTwo.Sec4.autFix α⁻¹ = CFSG.RankThree.PartTwo.Sec4.autFix α := by
  ext x
  rw [CFSG.RankThree.PartTwo.Sec4.mem_autFix, CFSG.RankThree.PartTwo.Sec4.mem_autFix]
  constructor
  · intro h
    have := congrArg α h
    rw [MulAut.inv_apply, MulEquiv.apply_symm_apply] at this
    exact this.symm
  · intro h
    rw [MulAut.inv_apply, MulEquiv.symm_apply_eq]
    exact h.symm

theorem td4g2_catalog_of_fix {q : TauCeti.PrimePower} (hq2 : q.p = 2)
    (hq : 2 < q.card ∧ ¬ 3 ∣ q.card)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (q.p ^ q.exponent) ^ 3) {σ : K ≃+* K}
    (hσ : ∀ c, σ c = c ^ (q.p ^ q.exponent)) {β : MulAut (td4g2C K σ)}
    (hβ3 : β ^ 3 = 1) (hβ : ¬ CFSG.RankThree.PartTwo.KFacts.IsInnerAut β)
    (htw : twoPart (Nat.card ↥(CFSG.RankThree.PartTwo.Sec4.autFix β)) = (2 ^ q.exponent) ^ 6) :
    catalogIs ↥(CFSG.RankThree.PartTwo.Sec4.autFix β) (onLie isG2Big) := by
  have hf : 1 ≤ q.exponent := q.exponent_pos
  have hK2 : Nat.card K = (2 ^ q.exponent) ^ 3 := by rw [← hq2]; exact hK
  have hσ2 : ∀ c, σ c = c ^ 2 ^ q.exponent := by
    intro c
    rw [← hq2]
    exact hσ c
  rcases CFSG.RankThree.PartTwo.Sec8.Item8KFacts2Proof.isStdGraphFieldConj_or_nonempty_autFix_equiv
      hf hK2 hσ2 hβ3 hβ with hstd | ⟨e2⟩
  · obtain ⟨g, hg⟩ := hstd
    have hiso : Nonempty (↥(CFSG.RankThree.PartTwo.Sec4.autFix β) ≃*
        ↥(CFSG.RankThree.PartTwo.Sec4.autFix (fieldActor (t := TwistTag.D4) σ σ))) := by
      rcases hg with rfl | rfl
      · exact td4g2_autFix_conj g _
      · obtain ⟨e⟩ := td4g2_autFix_conj g _
        exact ⟨e.trans (MulEquiv.subgroupCongr (td4g2_autFix_inv _))⟩
    obtain ⟨e⟩ := hiso
    obtain ⟨i, hi, ⟨e'⟩⟩ := td4g2_fixSub_catalog hq hK hσ
    exact ⟨i, hi, ⟨e.trans e'⟩⟩
  · exfalso
    obtain ⟨e2⟩ := e2
    have h6 := td4g2_pgl_case_twoPart hf hK2 hσ2 e2
    rw [h6] at htw
    have h2 : 2 ^ (q.exponent * 3) = 2 ^ (q.exponent * 6) := by
      rw [pow_mul, pow_mul]
      exact htw
    have := Nat.pow_right_injective (le_refl 2) h2
    omega

theorem td4g2_fix_lift {G : Type} [Group G] [Finite G] (T : Subgroup G) (hT : ¬ 3 ∣ Nat.card T)
    {g x : G} (hg3 : g ^ 3 = 1) (hgT : g ∈ Subgroup.normalizer (T : Set G))
    (hxT : x ∈ Subgroup.normalizer (T : Set G)) (hc : x⁻¹ * (g * x * g⁻¹) ∈ T) :
    ∃ n ∈ T, g * (x * n) * g⁻¹ = x * n := by
  classical
  set W : Subgroup G := Subgroup.normalizer (T : Set G) with hW
  have hTW : T ≤ W := Subgroup.le_normalizer
  haveI hNorm : (T.subgroupOf W).Normal := ⟨fun n hn h => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.mem_normalizer_iff.1 h.2 _).1 hn⟩
  set y : W := ⟨g, hgT⟩ with hy
  set k : W := ⟨x, hxT⟩ with hk
  have hy3 : y ^ 3 = 1 := Subtype.ext (by simpa [hy] using hg3)
  have hyP : IsPGroup 3 (Subgroup.zpowers y) := by
    rw [IsPGroup.iff_card]
    rcases (Nat.dvd_prime Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hy3) with h | h
    · exact ⟨0, by rw [Nat.card_zpowers, h, pow_zero]⟩
    · exact ⟨1, by rw [Nat.card_zpowers, h, pow_one]⟩
  have hker : ¬ 3 ∣ Nat.card (QuotientGroup.mk' (T.subgroupOf W)).ker := by
    rw [QuotientGroup.ker_mk', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTW).toEquiv]
    exact hT
  have hgi : ∀ t ∈ T, g⁻¹ * t * g ∈ T := by
    intro t ht
    refine (Subgroup.mem_normalizer_iff.1 hgT (g⁻¹ * t * g)).2 ?_
    have e : g * (g⁻¹ * t * g) * g⁻¹ = t := by group
    rw [e]
    exact ht
  have hk' : (QuotientGroup.mk' (T.subgroupOf W)) k * (QuotientGroup.mk' (T.subgroupOf W)) y =
      (QuotientGroup.mk' (T.subgroupOf W)) y * (QuotientGroup.mk' (T.subgroupOf W)) k := by
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    have e : (((k * y)⁻¹ * (y * k) : W) : G) = g⁻¹ * (x⁻¹ * (g * x * g⁻¹)) * g := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hk, hy]
      group
    rw [e]
    exact hgi _ hc
  obtain ⟨n, hn, hkn⟩ :=
    exists_mem_ker_mul_commute Nat.prime_three (QuotientGroup.mk' (T.subgroupOf W)) hker hyP hk'
  rw [QuotientGroup.ker_mk'] at hn
  refine ⟨(n : G), Subgroup.mem_subgroupOf.1 hn, ?_⟩
  have h2 : x * (n : G) * g = g * (x * n) := by
    have := congrArg Subtype.val hkn
    simpa [hk, hy, mul_assoc] using this
  rw [← h2]
  group

theorem td4g2_comp_ne_bot {H : Type} [Group H] [Finite H] {p : ℕ} {Y : Subgroup H}
    (h : GLAPLayer p Y ≠ ⊥) : ∃ K : Subgroup H, GLAPComponent p Y K ∧ K ≠ ⊥ := by
  by_contra hc
  push Not at hc
  apply h
  unfold GLAPLayer
  exact le_bot_iff.1 (sSup_le fun K hK => (hc K hK).le)

theorem td4g2_normalizer_centralizer {G : Type} [Group G] {g b : G} (hgb : g * b = b * g) :
    g ∈ Subgroup.normalizer ((Subgroup.centralizer ({b} : Set G) : Subgroup G) : Set G) := by
  have hb1 : g⁻¹ * b = b * g⁻¹ := by
    calc g⁻¹ * b = g⁻¹ * (b * g) * g⁻¹ := by group
      _ = g⁻¹ * (g * b) * g⁻¹ := by rw [hgb]
      _ = b * g⁻¹ := by group
  rw [Subgroup.mem_normalizer_iff]
  intro h
  simp only [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hh
    calc g * h * g⁻¹ * b = g * h * (g⁻¹ * b) := by group
      _ = g * h * (b * g⁻¹) := by rw [hb1]
      _ = g * (h * b) * g⁻¹ := by group
      _ = g * (b * h) * g⁻¹ := by rw [hh]
      _ = (g * b) * h * g⁻¹ := by group
      _ = (b * g) * h * g⁻¹ := by rw [hgb]
      _ = b * (g * h * g⁻¹) := by group
  · intro hh
    have hgb' : g⁻¹ * b * g = b := by
      rw [mul_assoc, ← hgb, inv_mul_cancel_left]
    calc h * b = h * (g⁻¹ * b * g) := by rw [hgb']
      _ = g⁻¹ * (g * h * g⁻¹ * b) * g := by group
      _ = g⁻¹ * (b * (g * h * g⁻¹)) * g := by rw [hh]
      _ = (g⁻¹ * b * g) * h := by group
      _ = b * h := by rw [hgb']

theorem td4g2_congr_apply {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (φ : MulAut X) (x : X) :
    MulAut.congr e φ (e x) = e (φ x) := by
  simp [MulAut.congr_apply]

theorem td4g2_mk_eq_iff {G : Type} [Group G] [Finite G] {L : Subgroup G} (x y : ↥L) :
    (QuotientGroup.mk x : PQuot 3 L) = QuotientGroup.mk y ↔
      (x : G)⁻¹ * (y : G) ∈ GLAPPrimeCoreOf 3 L := by
  rw [QuotientGroup.eq]
  have h := CFSG.LocalAnalysis.GLTheoremA.CatB.mem_primeCoreOf_iff (p := 3) (L := L) (x⁻¹ * y)
  rw [← h]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]

theorem td4g2_core_bot {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (h3 : 3 ∣ Nat.card S) :
    GLAPPrimeCore 3 S = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (GLAPPrimeCore 3 S) with h | h
  · exact h
  · exfalso
    have hc : Nat.Coprime 3 (Nat.card (GLAPPrimeCore 3 S)) := CFSG.pPrimeCore_coprime_card
    rw [h, Subgroup.card_top] at hc
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hc h3

end CFSG.LocalAnalysis.GLTheoremA

end
