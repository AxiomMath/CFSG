module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SmallRankOneData
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryBorelPCore
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryAutSemilinear
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Unitary
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallDefs

public section

namespace CFSG.AGLEmbedding.UnitaryModel

open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External CFSG.UnitaryThreeRecognition.Model

section Model

variable {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K)
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {p f : ℕ} [Fact p.Prime]
  (hK : Nat.card K = (p ^ f) ^ 2) (hfix : Nat.card {x : K // J.conj x = x} = p ^ f)

include hJ hK hfix

theorem ti_rootGroup (hq : 2 < p ^ f) :
    ∀ t ∈ rootGroup J hJ, t ≠ 1 → ∀ g : ProjectiveSpecialUnitaryMatrixGroup J,
      g * t * g⁻¹ ∈ rootGroup J hJ →
      g ∈ Subgroup.normalizer (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
  intro t ht ht1 g hg
  rw [normalizer_rootGroup_eq_stabilizer J hJ hK hfix hq]
  show g • pinf J hJ = pinf J hJ
  have h1 : (g * t * g⁻¹) • pinf J hJ = pinf J hJ := rootGroup_le_stabilizer J hJ hg
  have h2 : t • (g⁻¹ • pinf J hJ) = g⁻¹ • pinf J hJ := by
    have : t • (g⁻¹ • pinf J hJ) = g⁻¹ • ((g * t * g⁻¹) • pinf J hJ) := by
      rw [← mul_smul, ← mul_smul]
      group
    rw [this, h1]
  by_contra hne
  have hx : g⁻¹ • pinf J hJ ≠ pinf J hJ := fun h => hne (by
    calc g • pinf J hJ = g • (g⁻¹ • pinf J hJ) := by rw [h]
      _ = pinf J hJ := smul_inv_smul g _)
  obtain ⟨r, -, hr⟩ := rootGroup_regular J hJ _ _ hx hx
  have e1 := hr ⟨t, ht⟩ h2
  have e2 := hr 1 (one_smul _ _)
  exact ht1 (congrArg Subtype.val (e1.trans e2.symm))

omit [Finite K] [Fact p.Prime] hK hfix in
theorem torus_mul_center_mul_inv {t z : ProjectiveSpecialUnitaryMatrixGroup J}
    (ht : t ∈ Subgroup.normalizer (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)))
    (hz : z ∈ rootGroup J hJ ⊓
      Subgroup.centralizer (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J))) :
    t * z * t⁻¹ ∈ rootGroup J hJ ⊓
      Subgroup.centralizer (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
  refine ⟨(Subgroup.mem_normalizer_iff.1 ht z).1 hz.1,
    Subgroup.mem_centralizer_iff.2 fun r hr => ?_⟩
  have hr' : t⁻¹ * r * t ∈ rootGroup J hJ := by
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem ht) r).1 hr
    simpa using this
  have hc := Subgroup.mem_centralizer_iff.1 hz.2 _ hr'
  calc r * (t * z * t⁻¹) = t * ((t⁻¹ * r * t) * z) * t⁻¹ := by group
    _ = t * (z * (t⁻¹ * r * t)) * t⁻¹ := by rw [hc]
    _ = t * z * t⁻¹ * r := by group

theorem eq_center_or_eq_rootGroup_of_normalized (hq : 2 < p ^ f)
    {V : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)} (hVR : V ≤ rootGroup J hJ)
    (hV : V ≠ ⊥)
    (hVN : Subgroup.normalizer (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) ≤
      Subgroup.normalizer (V : Set (ProjectiveSpecialUnitaryMatrixGroup J))) :
    V = rootGroup J hJ ⊓ Subgroup.centralizer
      (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) ∨ V = rootGroup J hJ := by
  have hT : ∀ t ∈ torusGroup J hJ, ∀ v ∈ V, t * v * t⁻¹ ∈ V := fun t ht v hv =>
    (Subgroup.mem_normalizer_iff.1 (hVN (torusGroup_le_normalizer_rootGroup J hJ ht)) v).1 hv
  have hVZ : V ⊓ (rootGroup J hJ ⊓ Subgroup.centralizer
      (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J))) ≠ ⊥ := by
    have := (isPGroup_rootGroup J hJ hK hfix).isNilpotent
    have hnorm : (V.subgroupOf (rootGroup J hJ)).Normal := by
      constructor
      intro n hn g
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      have hgN := hVN (Subgroup.le_normalizer g.2)
      simpa using (Subgroup.mem_normalizer_iff.1 hgN n).1 hn
    have hne : V.subgroupOf (rootGroup J hJ) ≠ ⊥ := by
      intro h
      apply hV
      rw [eq_bot_iff]
      intro v hv
      have : (⟨v, hVR hv⟩ : ↥(rootGroup J hJ)) ∈ V.subgroupOf (rootGroup J hJ) := hv
      rw [h, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.2 (congrArg Subtype.val this)
    have hc := Group.IsNilpotent.inf_center_ne_bot_of_normal hne
    obtain ⟨⟨x, hx⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hc
    intro h
    have hxV : (x : ProjectiveSpecialUnitaryMatrixGroup J) ∈ V := hx.1
    have hxZ : (x : ProjectiveSpecialUnitaryMatrixGroup J) ∈ rootGroup J hJ ⊓
        Subgroup.centralizer (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
      refine ⟨x.2, Subgroup.mem_centralizer_iff.2 fun r hr => ?_⟩
      have := Subgroup.mem_center_iff.1 hx.2 ⟨r, hr⟩
      exact congrArg Subtype.val this
    have : (x : ProjectiveSpecialUnitaryMatrixGroup J) ∈ V ⊓ (rootGroup J hJ ⊓
        Subgroup.centralizer (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J))) :=
      ⟨hxV, hxZ⟩
    rw [h, Subgroup.mem_bot] at this
    exact hx1 (Subtype.ext (Subtype.ext this))
  have hZV : rootGroup J hJ ⊓ Subgroup.centralizer
      (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) ≤ V := by
    have h1 := eq_bot_or_eq_center_of_torus_invariant J hJ hK hfix
      (V := V ⊓ (rootGroup J hJ ⊓ Subgroup.centralizer
        (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)))) inf_le_right
      (fun t ht v hv => ⟨hT t ht v hv.1, torus_mul_center_mul_inv J hJ
        (torusGroup_le_normalizer_rootGroup J hJ ht) hv.2⟩)
    rcases h1 with h1 | h1
    · exact absurd h1 hVZ
    · rw [← h1]
      exact inf_le_left
  exact eq_center_or_eq_rootGroup_of_torus_invariant J hJ hK hfix hq hZV hVR hT

theorem exists_torus_rootGroup (hq : 2 < p ^ f) :
    ∃ T₀ : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J),
      T₀ ≤ Subgroup.normalizer (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) ∧
      p.Coprime (Nat.card T₀) ∧
      rootGroup J hJ ⊓ Subgroup.centralizer (T₀ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) =
        ⊥ := by
  have hp : p.Prime := Fact.out
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  refine ⟨torusGroup J hJ, torusGroup_le_normalizer_rootGroup J hJ, ?_, ?_⟩
  · have h1 : Nat.card (torusGroup J hJ) ∣ (p ^ f) ^ 2 - 1 := by
      have := Subgroup.card_range_dvd (torus J hJ)
      rwa [CFSG.ClassicalGroups.Unitary.card_units_of_card hK] at this
    refine Nat.Coprime.coprime_dvd_right h1 ((Nat.Prime.coprime_iff_not_dvd hp).2 fun hdvd => ?_)
    have h2 : p ∣ (p ^ f) ^ 2 := dvd_pow (dvd_pow_self p (by omega)) two_ne_zero
    have h3 : (p ^ f) ^ 2 = ((p ^ f) ^ 2 - 1) + 1 := by
      have : 1 ≤ (p ^ f) ^ 2 := Nat.one_le_pow _ _ (by positivity)
      omega
    rw [h3] at h2
    exact hp.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right hdvd).1 h2))
  · rw [eq_bot_iff]
    rintro x ⟨hxR, hxC⟩
    refine Subgroup.mem_bot.2 (eq_one_of_conj_fixes_torus J hJ hK hfix hq hxR fun t ht => ?_)
    have := Subgroup.mem_centralizer_iff.1 hxC t ht
    rw [← this]
    group

end Model

section Data

variable {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K)
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {p f : ℕ} [Fact p.Prime]
  (hK : Nat.card K = (p ^ f) ^ 2) (hfix : Nat.card {x : K // J.conj x = x} = p ^ f)

include hJ hK hfix

theorem smallRankOneData_psu (hq : 2 < p ^ f)
    (S : Sylow p (ProjectiveSpecialUnitaryMatrixGroup J))
    (hS : (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) = rootGroup J hJ)
    {d : TauCeti.ValidLieTypeIndex} (hd : CFSG.AGLEmbedding.IsUnitaryIndex p d)
    (he : Nonempty (ProjectiveSpecialUnitaryMatrixGroup J ≃* CFSG.AGLEmbedding.CatGroup d)) :
    CFSG.AGLEmbedding.SmallRankOneData p (ProjectiveSpecialUnitaryMatrixGroup J) S := by
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  have hmem : ∀ x, x ∈ (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) ↔
      x ∈ rootGroup J hJ := fun x => by rw [hS]
  have hN : Subgroup.normalizer ((S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) :
      Set (ProjectiveSpecialUnitaryMatrixGroup J)) =
      Subgroup.normalizer (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
    rw [hS]
  refine ⟨?_, ?_, center_eq_bot J hJ hK hfix hq, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hS, card_rootGroup_eq J hJ hK hfix]
    exact dvd_pow_self p (by omega)
  · intro t ht ht1 g hg
    rw [hN]
    exact ti_rootGroup J hJ hK hfix hq t ((hmem t).1 ht) ht1 g ((hmem _).1 hg)
  · rw [hN]
    exact isCoatom_normalizer_rootGroup J hJ hK hfix hq
  · rw [hN, normalizer_rootGroup_eq_stabilizer J hJ hK hfix hq]
    exact isSolvable_stabilizer_pinf J hJ hK hfix
  · intro f' hf'
    obtain ⟨r, hr, hfr⟩ := eq_conj_of_fixes_rootGroup J hJ hK hfix hq f'
      (fun r hr => hf' r ((hmem r).2 hr))
    exact ⟨r, (hmem r).2 hr, hfr⟩
  · intro Y hY hYN α hα
    obtain ⟨r, hr, hαr⟩ := eq_conj_of_normalized_pGroup J hJ hK hfix hq Y hY
      (fun b hb β hβ => hYN b (hN ▸ hb) β hβ) α hα
    exact ⟨r, (hmem r).2 hr, hαr⟩
  · exact CFSG.AGLEmbedding.kFactUnitaryOuterSolvable _ p d hd he
  · obtain ⟨T₀, hT₀N, hcop, hT₀⟩ := exists_torus_rootGroup J hJ hK hfix hq
    exact ⟨T₀, hN ▸ hT₀N, hcop, by rw [hS]; exact hT₀⟩
  · intro V hVS hV hVN
    rw [hS] at hVS ⊢
    rw [hN] at hVN
    rcases eq_center_or_eq_rootGroup_of_normalized J hJ hK hfix hq hVS hV hVN with h | h
    · exact Or.inr ⟨h, ⟨d, hd, he⟩⟩
    · exact Or.inl h

end Data

end CFSG.AGLEmbedding.UnitaryModel

namespace CFSG.AGLEmbedding

open CFSG.UnitaryThreeRecognition.Model (rootGroup)

theorem smallRankOneData_of_isSmallUnitary {K : Type} [Group K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hK : IsSmallUnitary p K) (T : Sylow p K) : SmallRankOneData p K T := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨d, ⟨q, hqp, -, hdq⟩, ⟨he⟩⟩ := hK
  have hd : IsUnitaryIndex p d := ⟨q, hqp, hdq⟩
  obtain ⟨-, hf, hq, F, _, _, J, hJ, hF, hfix, ⟨e⟩⟩ :=
    UnitaryModel.exists_equiv_psu (UnitaryModel.statedClassicalModel hd ⟨he⟩)
  obtain ⟨S, hS⟩ := UnitaryModel.exists_sylow_eq_rootGroup J hJ hF hfix hf
  obtain ⟨e', he'⟩ := UnitaryModel.exists_equiv_map_eq e T S
  exact SmallRankOneData.of_equiv e' he'
    (UnitaryModel.smallRankOneData_psu J hJ hF hfix hq S hS hd ⟨e'.symm.trans he⟩)

end CFSG.AGLEmbedding
