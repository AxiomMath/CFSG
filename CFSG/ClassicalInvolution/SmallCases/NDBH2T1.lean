module

public import CFSG.ClassicalInvolution.SmallCases.NDB1Main
public import CFSG.CharacterTheory.TwoRankLowerBound.Helpers

public section

namespace CFSG.ClassicalInvolution.NDB

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ComponentClassification

namespace NDBH2

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

variable (p f) in
structure HTri (Ω : Set (Subgroup G)) (K₁ K₂ K₃ : Subgroup G) (z₁ z₂ z₃ : G)
    (R₁ R₂ R₃ P : Subgroup G) : Prop where
  mem₂ : K₂ ∈ Ω
  mem₃ : K₃ ∈ Ω
  cls₂ : IsClassicalMember p f K₂ z₂
  cls₃ : IsClassicalMember p f K₃ z₃
  prod : z₁ * z₂ = z₃
  tq₁₂ : z₂ ∈ trivialOnQuot K₁
  tq₁₃ : z₃ ∈ trivialOnQuot K₁
  tq₂₁ : z₁ ∈ trivialOnQuot K₂
  tq₂₃ : z₃ ∈ trivialOnQuot K₂
  tq₃₁ : z₁ ∈ trivialOnQuot K₃
  tq₃₂ : z₂ ∈ trivialOnQuot K₃
  syl₁ : IsSylow2In R₁ K₁
  syl₂ : IsSylow2In R₂ K₂
  syl₃ : IsSylow2In R₃ K₃
  two : IsPGroup 2 P
  le₁ : R₁ ≤ P
  le₂ : R₂ ≤ P
  le₃ : R₃ ≤ P
  rank : 3 ≤ CFSG.Open.twoRank G

theorem exists_hTri {Ω : Set (Subgroup G)} (hΩ : HypOmegaMod p f Ω) (hp : p ≠ 2)
    (hq : 5 ≤ p ^ f) {K : Subgroup G} {z : G} (hK : K ∈ Ω) (hz : IsClassicalMember p f K z)
    {M₂ M₃ : Subgroup G} {u₂ u₃ : G} (hs : AxisSeed p f Ω K z M₂ M₃ u₂ u₃) :
    ∃ (K₂ K₃ : Subgroup G) (z₂ z₃ : G) (R₁ R₂ R₃ P : Subgroup G) (g₂ g₃ : G),
      HTri p f Ω K K₂ K₃ z z₂ z₃ R₁ R₂ R₃ P ∧ z₂ = g₂ * u₂ * g₂⁻¹ ∧ z₃ = g₃ * u₃ * g₃⁻¹ := by
  classical
  have hzc := isCentralInvolution_of_isClassicalMember hz
  have hz2 : z * z = 1 := hzc.sq
  have hc2 := ExactLayer.isPGroup_zpowers_of_sq_eq_one hz2
  have hKC : K ≤ Subgroup.centralizer ({z} : Set G) :=
    RouteD.le_centralizer_of_isClassicalMember hz
  have hzC : z ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hNodd := OddCore.odd_card ↥(Subgroup.centralizer ({z} : Set G))
  have hbot : IsPGroup 2 (⊥ : Subgroup G) :=
    IsPGroup.of_card (n := 0) (by rw [Subgroup.card_bot, pow_zero])
  obtain ⟨T₁, hT₁, -⟩ := Asc77.IsSylow2In.exists_ge (P := K) hbot bot_le
  obtain ⟨V₂, hV₂, -⟩ := Asc77.IsSylow2In.exists_ge (P := exactCore z M₂) hbot bot_le
  obtain ⟨V₃, hV₃, -⟩ := Asc77.IsSylow2In.exists_ge (P := exactCore z M₃) hbot bot_le
  set Tb := (T₁.subgroupOf (Subgroup.centralizer ({z} : Set G))).map (oddQuotMk z) with hTb
  set Vb₂ := (V₂.subgroupOf (Subgroup.centralizer ({z} : Set G))).map (oddQuotMk z) with hVb₂
  set Vb₃ := (V₃.subgroupOf (Subgroup.centralizer ({z} : Set G))).map (oddQuotMk z) with hVb₃
  have hTbK : Tb ≤ modOdd z K := Subgroup.map_mono fun x hx => hT₁.1 hx
  have hVb₂X : Vb₂ ≤ modOdd z (exactCore z M₂) := Subgroup.map_mono fun x hx => hV₂.1 hx
  have hVb₃X : Vb₃ ≤ modOdd z (exactCore z M₃) := Subgroup.map_mono fun x hx => hV₃.1 hx
  have hTb2 : IsPGroup 2 Tb := hT₁.2.1.comap_subtype.map _
  have hVb₂2 : IsPGroup 2 Vb₂ := hV₂.2.1.comap_subtype.map _
  have hVb₃2 : IsPGroup 2 Vb₃ := hV₃.2.1.comap_subtype.map _
  have c13 : ∀ a ∈ Tb, ∀ b ∈ Vb₃, a * b = b * a := fun a ha b hb =>
    hs.comm₁₃ a (hTbK ha) b (hVb₃X hb)
  have c23 : ∀ a ∈ Vb₂, ∀ b ∈ Vb₃, a * b = b * a := fun a ha b hb =>
    hs.comm₂₃ a (hVb₂X ha) b (hVb₃X hb)
  have hQ12 := Lift.isPGroup_sup_of_commute hTb2 hVb₂2 fun a ha b hb =>
    hs.comm₁₂ a (hTbK ha) b (hVb₂X hb)
  have c123 : ∀ a ∈ Tb ⊔ Vb₂, ∀ b ∈ Vb₃, a * b = b * a := by
    intro a ha b hb
    have hle : Tb ⊔ Vb₂ ≤ Subgroup.centralizer (Vb₃ : Set (OddQuot z)) :=
      sup_le (fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy => (c13 x hx y hy).symm)
        (fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy => (c23 x hx y hy).symm)
    exact ((Subgroup.mem_centralizer_iff.mp (hle ha)) b hb).symm
  have hQ := Lift.isPGroup_sup_of_commute hQ12 hVb₃2 c123
  obtain ⟨P, hP2, hTP, hPQ⟩ := Lift.exists_lift_ge _ hNodd hQ hT₁.2.1.comap_subtype
    (le_sup_left.trans le_sup_left)
  have hPQ' : P.map (oddQuotMk z) = Tb ⊔ Vb₂ ⊔ Vb₃ := hPQ
  have hV₂P : Vb₂ ≤ P.map (oddQuotMk z) := by
    rw [hPQ']
    exact le_sup_right.trans le_sup_left
  have hV₃P : Vb₃ ≤ P.map (oddQuotMk z) := by
    rw [hPQ']
    exact le_sup_right
  obtain ⟨g₂, hg₂C, hg₂1, S₂, hS₂, hS₂P, hS₂img⟩ :=
    Axis.exists_conj_sylow hΩ hz2 hs.tq₂ hs.cls₂ hP2 hV₂ hV₂P
  obtain ⟨g₃, hg₃C, hg₃1, S₃, hS₃, hS₃P, hS₃img⟩ :=
    Axis.exists_conj_sylow hΩ hz2 hs.tq₃ hs.cls₃ hP2 hV₃ hV₃P
  have hT₁P : T₁ ≤ P.map (Subgroup.centralizer ({z} : Set G)).subtype := fun a ha =>
    ⟨⟨a, hKC (hT₁.1 ha)⟩, hTP ha, rfl⟩
  have hcl₂ := hs.cls₂.conj g₂
  have hcl₃ := hs.cls₃.conj g₃
  obtain ⟨t₁, w₁, ht₁, hw₁, hsq₁, hinv₁⟩ := Lift.exists_sq_eq_of_isSylow2In hp hq hz hT₁
  obtain ⟨t₂, -, ht₂, -, hsq₂, -⟩ := Lift.exists_sq_eq_of_isSylow2In hp hq hcl₂ hS₂
  obtain ⟨t₃, -, ht₃, -, hsq₃, -⟩ := Lift.exists_sq_eq_of_isSylow2In hp hq hcl₃ hS₃
  have d12 : ∀ a ∈ T₁, ∀ b ∈ S₂, a * b = b * a := fun a ha b hb =>
    Axis.comm_of_mem_map hP2 (hT₁P ha) (hS₂P hb) fun ha' hb' =>
      hs.comm₁₂ _ (oddQuotMk_mem_modOdd (hT₁.1 ha) ha') _ (hS₂img b hb hb')
  have d13 : ∀ a ∈ T₁, ∀ b ∈ S₃, a * b = b * a := fun a ha b hb =>
    Axis.comm_of_mem_map hP2 (hT₁P ha) (hS₃P hb) fun ha' hb' =>
      hs.comm₁₃ _ (oddQuotMk_mem_modOdd (hT₁.1 ha) ha') _ (hS₃img b hb hb')
  have d23 : ∀ a ∈ S₂, ∀ b ∈ S₃, a * b = b * a := fun a ha b hb =>
    Axis.comm_of_mem_map hP2 (hS₂P ha) (hS₃P hb) fun ha' hb' =>
      hs.comm₂₃ _ (hS₂img a ha ha') _ (hS₃img b hb hb')
  have hzT : z ∈ T₁ := Lift.mem_of_isSylow2In hp hq hz hT₁
  have hz₂S : g₂ * u₂ * g₂⁻¹ ∈ S₂ := Lift.mem_of_isSylow2In hp hq hcl₂ hS₂
  have hz₃S : g₃ * u₃ * g₃⁻¹ ∈ S₃ := Lift.mem_of_isSylow2In hp hq hcl₃ hS₃
  have hu₂C : u₂ ∈ Subgroup.centralizer ({z} : Set G) :=
    exactCore_le_centralizer z M₂ (mem_exactCore hs.cls₂ hc2 hs.tq₂.2)
  have hu₃C : u₃ ∈ Subgroup.centralizer ({z} : Set G) :=
    exactCore_le_centralizer z M₃ (mem_exactCore hs.cls₃ hc2 hs.tq₃.2)
  have hbar : ∀ (g u : G) (hg : g ∈ Subgroup.centralizer ({z} : Set G))
      (hu : u ∈ Subgroup.centralizer ({z} : Set G)), oddQuotMk z ⟨g, hg⟩ = 1 →
      ∀ h : g * u * g⁻¹ ∈ Subgroup.centralizer ({z} : Set G),
        oddQuotMk z ⟨g * u * g⁻¹, h⟩ = oddQuotMk z ⟨u, hu⟩ := by
    intro g u hg hu hg1 h
    have e : (⟨g * u * g⁻¹, h⟩ : ↥(Subgroup.centralizer ({z} : Set G))) =
        ⟨g, hg⟩ * ⟨u, hu⟩ * (⟨g, hg⟩ : ↥(Subgroup.centralizer ({z} : Set G)))⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, hg1, one_mul, inv_one, mul_one]
  have hprod : z * (g₂ * u₂ * g₂⁻¹) = g₃ * u₃ * g₃⁻¹ := by
    refine Axis.eq_of_mem_map hP2 (Subgroup.mul_mem _ (hT₁P hzT) (hS₂P hz₂S)) (hS₃P hz₃S)
      fun ha hb => ?_
    have h₂C : g₂ * u₂ * g₂⁻¹ ∈ Subgroup.centralizer ({z} : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hg₂C hu₂C) (Subgroup.inv_mem _ hg₂C)
    have e : (⟨z * (g₂ * u₂ * g₂⁻¹), ha⟩ : ↥(Subgroup.centralizer ({z} : Set G))) =
        ⟨z, hzC⟩ * ⟨g₂ * u₂ * g₂⁻¹, h₂C⟩ := rfl
    rw [e, map_mul, hbar g₂ u₂ hg₂C hu₂C hg₂1, hbar g₃ u₃ hg₃C hu₃C hg₃1]
    exact hs.prod hzC hu₂C hu₃C
  have hc₂ := isCentralInvolution_of_isClassicalMember hcl₂
  have hc₃ := isCentralInvolution_of_isClassicalMember hcl₃
  have hzK : z ∈ trivialOnQuot K := mem_trivialOnQuot_of_le_centralizer hKC
  have tq₁₂ : g₂ * u₂ * g₂⁻¹ ∈ trivialOnQuot K :=
    (mem_trivialOnQuot_iff_exists_sylow hp hq hΩ (isPGroup_zpowers_of_sq_eq_one hc₂.sq) hK).mpr
      ⟨T₁, hT₁, fun a ha => Subgroup.mem_centralizer_singleton_iff.mpr (d12 a ha _ hz₂S)⟩
  have tq₂₁ : z ∈ trivialOnQuot (conjSub g₂ M₂) :=
    (conjSub_mem_tqMembers hΩ.conjInvariant hg₂C hs.tq₂).2
  have tq₃₁ : z ∈ trivialOnQuot (conjSub g₃ M₃) :=
    (conjSub_mem_tqMembers hΩ.conjInvariant hg₃C hs.tq₃).2

  have hz₂K₂ : g₂ * u₂ * g₂⁻¹ ∈ trivialOnQuot (conjSub g₂ M₂) :=
    mem_trivialOnQuot_of_le_centralizer (RouteD.le_centralizer_of_isClassicalMember hcl₂)
  have hz₃K₃ : g₃ * u₃ * g₃⁻¹ ∈ trivialOnQuot (conjSub g₃ M₃) :=
    mem_trivialOnQuot_of_le_centralizer (RouteD.le_centralizer_of_isClassicalMember hcl₃)
  have hz₂eq : g₂ * u₂ * g₂⁻¹ = z * (g₃ * u₃ * g₃⁻¹) := by
    rw [← hprod, ← mul_assoc, hz2, one_mul]
  have hwz : w₁ * z = z * w₁ := Subgroup.mem_centralizer_singleton_iff.mp (hKC (hT₁.1 hw₁))
  obtain ⟨helem, hcard⟩ := Axis.axis_elem_card hzc.ne_one hz2 hc₂.ne_one hc₂.sq hc₃.ne_one hprod
    hsq₁ hsq₂ hsq₃ (d12 t₁ ht₁ t₂ ht₂) (d13 t₁ ht₁ t₃ ht₃) (d23 t₂ ht₂ t₃ ht₃) hinv₁
    (d12 w₁ hw₁ t₂ ht₂) (d13 w₁ hw₁ t₃ ht₃) hwz
  refine ⟨conjSub g₂ M₂, conjSub g₃ M₃, g₂ * u₂ * g₂⁻¹, g₃ * u₃ * g₃⁻¹, T₁, S₂, S₃,
    P.map (Subgroup.centralizer ({z} : Set G)).subtype, g₂, g₃,
    { mem₂ := hΩ.conjInvariant g₂ M₂ hs.tq₂.1
      mem₃ := hΩ.conjInvariant g₃ M₃ hs.tq₃.1
      cls₂ := hcl₂
      cls₃ := hcl₃
      prod := hprod
      tq₁₂ := tq₁₂
      tq₁₃ := hprod ▸ Subgroup.mul_mem _ hzK tq₁₂
      tq₂₁ := tq₂₁
      tq₂₃ := hprod ▸ Subgroup.mul_mem _ tq₂₁ hz₂K₂
      tq₃₁ := tq₃₁
      tq₃₂ := hz₂eq ▸ Subgroup.mul_mem _ tq₃₁ hz₃K₃
      syl₁ := hT₁
      syl₂ := hS₂
      syl₃ := hS₃
      two := hP2.map _
      le₁ := hT₁P
      le₂ := hS₂P
      le₃ := hS₃P
      rank := CFSG.TwoRankLowerBound.Helpers.le_twoRank_of_elementary G _ helem 3
        (by rw [hcard]; norm_num) }, rfl, rfl⟩

end NDBH2

end CFSG.ClassicalInvolution.NDB
