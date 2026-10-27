module

public import CFSG.Fischer.Aut.TwoPower
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6Three
public import CFSG.LieType.SeitzGeneration.ExcWideThree.FixedE6
public import CFSG.LieType.SeitzGeneration.ExcWideThree.PlaneKernel
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.Untwisted
public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.Assembly
public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.Defs
public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.Generic
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.LieType.SeitzGeneration CFSG.LieType.SeitzGeneration.ExcOuterLeOne
  CFSG.RankThree.PartOne.CTP CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Lang.E6Descent CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Open
  CFSG.AGLEmbeddingD2 CFSG.Fischer TauCeti
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)

section E6


theorem coe_conj_mul_rootDiagAut {τ : Tag} {K : Type} [Field K] [Finite K]
    (g : adjointGroup τ K) (a : Fin τ.rank → Kˣ) (x : adjointGroup τ K) :
    ((MulAut.conj g * rootDiagAut τ K a) x : ModGL τ K) =
      (g : ModGL τ K) * rootDiagUnit τ a * (x : ModGL τ K) * (rootDiagUnit τ a)⁻¹ *
        (g : ModGL τ K)⁻¹ := by
  rw [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul, coe_rootDiagAut,
    Subgroup.coe_inv]
  simp only [mul_assoc]

theorem mem_e6Inndiag_iff {K : Type} [Field K] [Finite K] (α : MulAut (adjointGroup Tag.E6 K)) :
    α ∈ e6Inndiag K ↔ ∃ (g : adjointGroup Tag.E6 K) (a : Fin Tag.E6.rank → Kˣ),
      α = MulAut.conj g * rootDiagAut Tag.E6 K a := by
  constructor
  · intro h
    haveI := innerAut_normal (G := adjointGroup Tag.E6 K)
    obtain ⟨u, ⟨g, rfl⟩, v, ⟨a, rfl⟩, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 h
    exact ⟨g, a, rfl⟩
  · rintro ⟨g, a, rfl⟩
    exact mul_mem (Subgroup.mem_sup_left ⟨g, rfl⟩) (Subgroup.mem_sup_right ⟨a, rfl⟩)

theorem mem_ker_iff_mem_e6Inndiag {K : Type} [Field K] [Finite K]
    (Θ : MulAut (adjointGroup Tag.E6 K) →* RingAut K × Multiplicative (ZMod (exactE Tag.E6)))
    (hker : ∀ α : MulAut (adjointGroup Tag.E6 K), α ∈ Θ.ker ↔
      ∃ (g : adjointGroup Tag.E6 K) (a : Fin Tag.E6.rank → Kˣ), ∀ h : adjointGroup Tag.E6 K,
        (α h : ModGL Tag.E6 K) = (g : ModGL Tag.E6 K) * rootDiagUnit Tag.E6 a *
          (h : ModGL Tag.E6 K) * (rootDiagUnit Tag.E6 a)⁻¹ * (g : ModGL Tag.E6 K)⁻¹)
    (α : MulAut (adjointGroup Tag.E6 K)) : α ∈ Θ.ker ↔ α ∈ e6Inndiag K := by
  rw [hker, mem_e6Inndiag_iff]
  refine exists_congr fun g => exists_congr fun a => ?_
  constructor
  · intro h
    refine MulEquiv.ext fun x => Subtype.ext ?_
    rw [coe_conj_mul_rootDiagAut]
    exact h x
  · intro h x
    rw [h, coe_conj_mul_rootDiagAut]

theorem adjointGroup_le_centralizer_of_commute_subfield {τ : Tag} {K : Type} [Field K] [Finite K]
    (k : Subfield K) (hk : entryDegreeBound τ < Nat.card k) (y : ModGL τ K)
    (hy : ∀ h ∈ (adjointGroup τ k).map (baseChangeGL k.subtype), y * h = h * y) :
    adjointGroup τ K ≤ Subgroup.centralizer {y} := by
  classical
  have : Fintype k := Fintype.ofFinite k
  have hD : entryDegreeBound τ < Fintype.card k := by
    rw [← Nat.card_eq_fintype_card]
    exact hk
  have hx : ∀ (i : Fin τ.rank) (c : k), (y : Module.End K (RootModule τ K)) *
      xOp τ K i (k.subtype c) = xOp τ K i (k.subtype c) * (y : Module.End K (RootModule τ K)) :=
    fun i c => by
      have h1 := hy _ ⟨xUnit τ k i c, xUnit_mem_adjointGroup i c, rfl⟩
      rw [baseChangeGL_xUnit] at h1
      exact congrArg Units.val h1
  have hy' : ∀ (i : Fin τ.rank) (c : k), (y : Module.End K (RootModule τ K)) *
      yOp τ K i (k.subtype c) = yOp τ K i (k.subtype c) * (y : Module.End K (RootModule τ K)) :=
    fun i c => by
      have h1 := hy _ ⟨yUnit τ k i c, yUnit_mem_adjointGroup i c, rfl⟩
      rw [baseChangeGL_yUnit] at h1
      exact congrArg Units.val h1
  have hgen : ∀ (i : Fin τ.rank) (t : K),
      (y : Module.End K (RootModule τ K)) * xOp τ K i t = xOp τ K i t * (y : Module.End K _) ∧
      (y : Module.End K (RootModule τ K)) * yOp τ K i t = yOp τ K i t * (y : Module.End K _) := by
    intro i t
    refine ⟨?_, ?_⟩
    · refine commute_of_polynomial_entries (F := xOp τ K i) (fun a b => ?_) _ k.subtype
        k.subtype.injective hD (fun c => hx i c) t
      obtain ⟨p, q, hp, hq, hpq⟩ := exists_entry_polynomial (R := K) τ i a b
      exact ⟨p, hp, fun c => (hpq c).1⟩
    · refine commute_of_polynomial_entries (F := yOp τ K i) (fun a b => ?_) _ k.subtype
        k.subtype.injective hD (fun c => hy' i c) t
      obtain ⟨p, q, hp, hq, hpq⟩ := exists_entry_polynomial (R := K) τ i a b
      exact ⟨q, hq, fun c => (hpq c).2⟩
  rw [adjointGroup, Subgroup.closure_le]
  rintro g ⟨i, c, hg | hg⟩ <;>
    refine Subgroup.mem_centralizer_singleton_iff.2 (Units.ext ?_) <;>
    rw [Units.val_mul, Units.val_mul, hg]
  · exact (hgen i c).1.symm
  · exact (hgen i c).2.symm

theorem eq_one_of_mem_e6Inndiag_of_fix_subfield {K : Type} [Field K] [Finite K] (k : Subfield K)
    (hk : 2 < Nat.card k) {ι : MulAut (adjointGroup Tag.E6 K)} (hι : ι ∈ e6Inndiag K)
    (hfix : ∀ x : adjointGroup Tag.E6 K,
      (x : ModGL Tag.E6 K) ∈ (adjointGroup Tag.E6 k).map (baseChangeGL k.subtype) → ι x = x) :
    ι = 1 := by
  obtain ⟨g, a, rfl⟩ := (mem_e6Inndiag_iff ι).1 hι
  set y : ModGL Tag.E6 K := (g : ModGL Tag.E6 K) * rootDiagUnit Tag.E6 a with hy
  have hcoe : ∀ x : adjointGroup Tag.E6 K,
      ((MulAut.conj g * rootDiagAut Tag.E6 K a) x : ModGL Tag.E6 K) =
        y * (x : ModGL Tag.E6 K) * y⁻¹ := by
    intro x
    rw [coe_conj_mul_rootDiagAut, hy]
    simp only [mul_inv_rev, mul_assoc]
  have hcomm : ∀ h ∈ (adjointGroup Tag.E6 k).map (baseChangeGL k.subtype), y * h = h * y := by
    intro h hh
    have hhK : h ∈ adjointGroup Tag.E6 K := by
      obtain ⟨u, hu, rfl⟩ := hh
      exact baseChangeGL_mem_adjointGroup k.subtype hu
    have h1 := hfix ⟨h, hhK⟩ hh
    have h2 := congrArg Subtype.val h1
    rw [hcoe] at h2
    calc y * h = (y * h * y⁻¹) * y := by group
      _ = h * y := by rw [show y * h * y⁻¹ = h from h2]
  have hdeg : entryDegreeBound Tag.E6 = 2 := by simp [entryDegreeBound]
  have hle := adjointGroup_le_centralizer_of_commute_subfield (τ := Tag.E6) k
    (by rw [hdeg]; exact hk) y hcomm
  refine MulEquiv.ext fun x => Subtype.ext ?_
  rw [hcoe]
  have h3 := Subgroup.mem_centralizer_singleton_iff.1 (hle x.2)
  calc y * (x : ModGL Tag.E6 K) * y⁻¹ = (x : ModGL Tag.E6 K) * y * y⁻¹ := by rw [← h3]
    _ = (x : ModGL Tag.E6 K) := by group

theorem e6_fieldPlanes_three_of_big (hmax : ExcOuterLeOne.SubfieldMaximalAllThree .E6)
    {K : Type} [Field K] [Finite K] (hK3 : ringChar K ≠ 3)
    (hbig : ∀ T : K ≃+* K, orderOf T = 3 → 2 < Nat.card (fixSubfield T))
    (E : Subgroup (MulAut ↥(adjointGroup Tag.E6 K))) [hE : CFSG.IsElementaryAbelian 3 ↥E]
    (hEc : Nat.card ↥E = 3 ^ 2) (hout : ¬ E ≤ e6Inndiag K) :
    Subgroup.closure (fixUnion E) = ⊤ := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hℓ, hn⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hℓ⟩
  have hK : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn
  have : CharP K (ringChar K) := ringChar.charP K
  have : Finite (ModGL Tag.E6 K) := finite_modGL
  have : Finite (adjointGroup Tag.E6 K) := Subtype.finite
  obtain ⟨Θ, -, -, hker, -⟩ :=
    ordinary_E_field_graph_quotient_and_involutions Tag.E6 (Or.inl rfl) K
  obtain ⟨ι, hιE, hι1, hιker⟩ :=
    exists_ne_one_mem_ker_of_plane Tag.E6 (Or.inl rfl) Nat.prime_three (by norm_num) Θ E hEc
  have hιdiag : ι ∈ e6Inndiag K := (mem_ker_iff_mem_e6Inndiag Θ hker ι).1 hιker
  obtain ⟨α, hαE, hα⟩ : ∃ α ∈ E, α ∉ e6Inndiag K := by
    by_contra h
    push Not at h
    exact hout fun x hx => h x hx
  have hα1 : α ≠ 1 := fun h => hα (h ▸ one_mem _)
  have hβ : α * ι ∉ e6Inndiag K := fun h => hα (by simpa using mul_mem h (inv_mem hιdiag))
  have hβ1 : α * ι ≠ 1 := fun h => hβ (h ▸ one_mem _)
  have hα3 : α ^ 3 = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian α hαE
  have hβ3 : (α * ι) ^ 3 = 1 :=
    CFSG.elemPow_eq_one_of_isElementaryAbelian (α * ι) (E.mul_mem hαE hιE)
  obtain ⟨σa, hσa, -, ψa, hψa⟩ := exists_conj_entrywise_of_not_mem_e6Inndiag hℓ n.pos K hK
    Nat.prime_three (by norm_num) hα3 hα
  obtain ⟨σb, hσb, -, ψb, hψb⟩ := exists_conj_entrywise_of_not_mem_e6Inndiag hℓ n.pos K hK
    Nat.prime_three (by norm_num) hβ3 hβ
  have hRfix : CFSG.RankThree.PartOne.CTP.fixedSubgroup (entrywiseAdjointAut Tag.E6 σb) =
      CFSG.RankThree.PartOne.CTP.fixedSubgroup (entrywiseAdjointAut Tag.E6 σa) :=
    fixedSubgroup_eq_of_zpowers_eq (entrywiseAdjointAutHom (τ := Tag.E6))
      (zpowers_ringEquiv_eq_of_orderOf hℓ n.pos hK hσb hσa)
  refine closure_fixUnion_eq_top_of_kernel_escape (N := Θ.ker)
    (R := CFSG.RankThree.PartOne.CTP.fixedSubgroup (entrywiseAdjointAut Tag.E6 σa))
    (hmax K σa 3 rfl (fun h => hK3 h.symm) hσa) ?_ hαE hιE hα1 hβ1 hι1 hιker (by rw [hψa])
    (by rw [hψb, hRfix])
  intro ι' hι'ker hι'fix
  have hι'diag : ι' ∈ e6Inndiag K := (mem_ker_iff_mem_e6Inndiag Θ hker ι').1 hι'ker
  refine eq_one_of_mem_e6Inndiag_of_fix_subfield (fixSubfield σa) (hbig σa hσa) hι'diag ?_
  intro x hx
  apply hι'fix
  have h1 := fixedFieldImage_le (σ := σa) hx
  rw [CFSG.RankThree.PartOne.CTP.mem_fixedSubgroup]
  refine Subtype.ext ?_
  rw [coe_entrywiseAdjointAut]
  exact ((mem_entrywiseFixedGroup).1 h1).2

theorem e6_fieldPlanes_three_of_card_eight (hmax : ExcOuterLeOne.SubfieldMaximalAllThree .E6)
    {K : Type} [Field K] [Finite K] (hK3 : ringChar K ≠ 3) (hK8 : Nat.card K = 8)
    (E : Subgroup (MulAut ↥(adjointGroup Tag.E6 K))) [hE : CFSG.IsElementaryAbelian 3 ↥E]
    (hEc : Nat.card ↥E = 3 ^ 2) (hout : ¬ E ≤ innerAut (adjointGroup Tag.E6 K)) :
    Subgroup.closure (fixUnion E) = ⊤ := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hℓ, hn⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hℓ⟩
  have hK : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn
  have : CharP K (ringChar K) := ringChar.charP K
  have : Finite (ModGL Tag.E6 K) := finite_modGL
  have : Finite (adjointGroup Tag.E6 K) := Subtype.finite
  have hnd : ¬ 3 ∣ Nat.card K - 1 := by rw [hK8]; norm_num
  have hdiag : e6Inndiag K = innerAut (adjointGroup Tag.E6 K) :=
    e6Inndiag_eq_innerAut_of_not_dvd K hnd
  obtain ⟨Θ, -, -, hker, -⟩ :=
    ordinary_E_field_graph_quotient_and_involutions Tag.E6 (Or.inl rfl) K
  have hFAD : FieldAutData (adjointGroup Tag.E6 K) 3 := by
    refine fieldAutData_of_standard ⊤
      {g | ∃ σ : K ≃+* K, orderOf σ = 3 ∧ g = entrywiseAdjointAut Tag.E6 σ} ?_ ?_ ?_ ?_ ?_
    · intro E' hE' hEc'
      have := hE'
      obtain ⟨ι, hιE, hι1, hιker⟩ :=
        exists_ne_one_mem_ker_of_plane Tag.E6 (Or.inl rfl) Nat.prime_three (by norm_num) Θ E' hEc'
      have hιdiag : ι ∈ e6Inndiag K := (mem_ker_iff_mem_e6Inndiag Θ hker ι).1 hιker
      rw [hdiag] at hιdiag
      obtain ⟨g, rfl⟩ := hιdiag
      exact ⟨g, fun hg => hι1 (by rw [hg, map_one]), hιE⟩
    · intro α hα
      obtain ⟨hαo, hαin⟩ := hα
      have hα3 : α ^ 3 = 1 := by rw [← hαo]; exact pow_orderOf_eq_one α
      have hαdiag : α ∉ e6Inndiag K := by
        rw [hdiag]
        rintro ⟨g, hg⟩
        exact hαin g hg.symm
      obtain ⟨σ, hσ, -, ψ, hψ⟩ := exists_conj_entrywise_of_not_mem_e6Inndiag hℓ n.pos K hK
        Nat.prime_three (by norm_num) hα3 hαdiag
      refine ⟨ψ⁻¹, Subgroup.mem_top _, entrywiseAdjointAut Tag.E6 σ, ⟨σ, hσ, rfl⟩, ?_⟩
      rw [← hψ]
      group
    · rintro _ ⟨σ, hσ, rfl⟩ _ ⟨τ, hτ, rfl⟩
      exact fixedSubgroup_eq_of_zpowers_eq (entrywiseAdjointAutHom (τ := Tag.E6))
        (zpowers_ringEquiv_eq_of_orderOf hℓ n.pos hK hσ hτ)
    · rintro _ ⟨σ, hσ, rfl⟩ _ x hx hc
      have hcard := CFSG.RankThree.PartOne.SEITZ6.card_eq_card_fixSubfield_pow σ
      rw [hσ, hK8] at hcard
      have h3 : Nat.card (fixSubfield σ) ^ 3 = 2 ^ 3 := by rw [← hcard]; norm_num
      have hcard2 : Nat.card (fixSubfield σ) = 2 := Nat.pow_left_injective (by norm_num) h3
      exact eq_one_of_central_fixed_E6 σ (cubeDescent_of_card_two σ hcard2) hx hc
    · rintro _ ⟨σ, hσ, rfl⟩ d _ hne
      exact Or.inl (closure_pair_eq_top_of_maximal
        (hmax K σ 3 rfl (fun h => hK3 h.symm) hσ) d hne)
  exact closure_fixUnion_eq_top_of_fieldAutData'
    CFSG.AGLEmbedding.SeitzEqTwo.conj_injective_adjointGroup Nat.prime_three hFAD E hEc
    (fun h => hout fun φ hφ => (h φ hφ).imp fun g hg => hg.symm)

theorem e6_fieldPlanes_three (hmax : ExcOuterLeOne.SubfieldMaximalAllThree .E6)
    {K : Type} [Field K] [Finite K] (hK3 : ringChar K ≠ 3)
    (E : Subgroup (MulAut ↥(adjointGroup Tag.E6 K))) [hE : CFSG.IsElementaryAbelian 3 ↥E]
    (hEc : Nat.card ↥E = 3 ^ 2) (hout : ¬ E ≤ e6Inndiag K) :
    Subgroup.closure (fixUnion E) = ⊤ := by
  by_cases hbig : ∀ T : K ≃+* K, orderOf T = 3 → 2 < Nat.card (fixSubfield T)
  · exact e6_fieldPlanes_three_of_big hmax hK3 hbig E hEc hout
  · push Not at hbig
    obtain ⟨T, hT, hle⟩ := hbig
    have hcard := CFSG.RankThree.PartOne.SEITZ6.card_eq_card_fixSubfield_pow T
    rw [hT] at hcard
    have h2 : 2 ≤ Nat.card (fixSubfield T) := Finite.one_lt_card
    have h8 : Nat.card K = 8 := by
      rw [hcard, show Nat.card (fixSubfield T) = 2 by omega]
      norm_num
    have hdiag : e6Inndiag K = innerAut (adjointGroup Tag.E6 K) :=
      e6Inndiag_eq_innerAut_of_not_dvd K (by rw [h8]; norm_num)
    exact e6_fieldPlanes_three_of_card_eight hmax hK3 h8 E hEc (hdiag ▸ hout)

end E6

end CFSG.LieType.SeitzGeneration.ExcWideThree
