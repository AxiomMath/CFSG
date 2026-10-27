module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualTypeANTRead
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualTypeAConj
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualTypeAFixSpace

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Module QuadraticMap Subgroup CFSG.Assembly.LowTwoRank
open CFSG.Quasithin (perfectCore)
open LinearPilot (autFixSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (plusIndexEquiv coordinateQuadPlus regular_coordinateQuadPlus)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter (isometryConjugationHom)

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
theorem exists_sl2_ne_one : ∃ B : Matrix.SpecialLinearGroup (Fin 2) K, B ≠ 1 := by
  refine ⟨⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩, fun h => ?_⟩
  have h' := congrArg (fun B : Matrix.SpecialLinearGroup (Fin 2) K =>
    (B : Matrix (Fin 2) (Fin 2) K) 0 1) h
  simp at h'

theorem simple_nonabelian_of_surjective_sp (hq4 : 4 ≤ Nat.card K) {X : Type*} [Group X]
    {r : ℕ} (hr : 1 ≤ r) (ρ : X →* StatedSp r K) (hρ : Function.Surjective ρ) :
    IsSimpleGroup (X ⧸ ρ.ker) ∧ ∃ a b : X ⧸ ρ.ker, a * b ≠ b * a := by
  obtain ⟨hsimple, -⟩ := simple_perfect_statedProj_of_one_le hq4 hr
  refine ⟨MulEquiv.isSimpleGroup (chartOfSurjective ρ hρ), ?_⟩
  obtain ⟨a, b, hab⟩ := exists_mul_ne_statedProj_statedSp hq4 hr
  refine ⟨(chartOfSurjective ρ hρ).symm a, (chartOfSurjective ρ hρ).symm b, fun h => hab ?_⟩
  have h' := congrArg (chartOfSurjective ρ hρ) h
  rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h'

theorem isEmpty_quotient_mulEquiv_of_ne {X : Type*} [Group X] {r r' : ℕ} (hrr : r ≠ r')
    (ρ : X →* StatedSp r K) (hρ : Function.Surjective ρ) (ρ' : X →* StatedSp r' K)
    (hρ' : Function.Surjective ρ') : IsEmpty (X ⧸ ρ.ker ≃* X ⧸ ρ'.ker) :=
  ⟨fun e => hrr (rank_eq_of_mulEquiv
    (((chartOfSurjective ρ hρ).symm.trans e).trans (chartOfSurjective ρ' hρ')))⟩

theorem spLeviData_nSubTwo_of_rangeChart {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    {n ℓ : ℕ} (hn : 5 ≤ n) (hq4 : 4 ≤ Nat.card K) (P : LowPairing n ℓ) (hℓ2 : ℓ + 2 = n)
    {r : ℕ} (hr2 : 2 ≤ r) (ρ : typeACore K P →* StatedSp r K) (hρ : Function.Surjective ρ)
    (hρker : ρ.ker = (rangeRestrictHom (exists_coordinateQuadPlus_ne_zero (by omega))
      (typeACore K P) (lowNil P)
      (fun _ hx v => projLift_lowNil_of_mem_core (exists_coordinateQuadPlus_ne_zero (by omega))
        hx v)).ker)
    (htr : ∀ x, spMatTrace (ρ x) = LinearMap.trace K (LinearMap.range (lowNil (K := K) P))
      (rangeRestrictHom (exists_coordinateQuadPlus_ne_zero (by omega)) (typeACore K P) (lowNil P)
        (fun _ hx v => projLift_lowNil_of_mem_core (exists_coordinateQuadPlus_ne_zero (by omega))
          hx v) x)) :
    SpLeviData (plusFieldPart hf hK hn) (typeACore K P) := by
  set hQ := exists_coordinateQuadPlus_ne_zero (K := K) (n := n) (by omega) with hQdef
  have hr : 1 ≤ r := by omega
  set ρ₂ := coreSpLeft P hℓ2 hQ hq4 with hρ₂def
  set ρ₃ := coreSpRight P hℓ2 hQ hq4 with hρ₃def
  have hρ₂ : Function.Surjective ρ₂ := coreSpLeft_surjective P hℓ2 hQ hq4
  have hρ₃ : Function.Surjective ρ₃ := coreSpRight_surjective P hℓ2 hQ hq4
  obtain ⟨hq₁, hle₁⟩ := ker_props_of_surjective_sp hq4 hr ρ hρ
  obtain ⟨hq₂, hle₂⟩ := ker_props_of_surjective_sp hq4 le_rfl ρ₂ hρ₂
  obtain ⟨hq₃, hle₃⟩ := ker_props_of_surjective_sp hq4 le_rfl ρ₃ hρ₃
  have hR : ρ.ker ⊓ ρ₂.ker ⊓ ρ₃.ker =
      (rangeRestrictHom hQ (typeACore K P) (lowNil P)
        (fun _ hx v => projLift_lowNil_of_mem_core hQ hx v)).ker ⊓
      (kerQuotHom hQ (typeACore K P) (lowNil P)
        (fun _ hx v => projLift_lowNil_of_mem_core hQ hx v)).ker := by
    rw [inf_assoc, hρ₂def, hρ₃def, ker_coreSpLeft_inf_ker_coreSpRight, hρker]
  have h123 : IsPGroup 2 ↥(ρ.ker ⊓ ρ₂.ker ⊓ ρ₃.ker) := by
    rw [hR]
    exact isPGroup_ker_inf_ker hQ _ (lowNil P) _
  have h132 : IsPGroup 2 ↥(ρ.ker ⊓ ρ₃.ker ⊓ ρ₂.ker) := by
    rw [inf_right_comm]
    exact h123
  have hRn : (ρ.ker ⊓ ρ₂.ker ⊓ ρ₃.ker).Normal := inferInstance
  have hN : ∀ N ∈ ({ρ.ker, ρ₂.ker, ρ₃.ker} : Set (Subgroup ↥(typeACore K P))),
      ∀ M : Subgroup ↥(typeACore K P), M.Normal → IsPGroup 2 M → M ≤ N := by
    intro N hN M hM hMp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hN
    rcases hN with rfl | rfl | rfl
    · exact hle₁ M hM hMp
    · exact hle₂ M hM hMp
    · exact hle₃ M hM hMp
  have hq : ∀ N ∈ ({ρ.ker, ρ₂.ker, ρ₃.ker} : Set (Subgroup ↥(typeACore K P))),
      ∀ M : Subgroup ↥(typeACore K P), M.Normal → N ≤ M → M = N ∨ M = ⊤ := by
    intro N hN M hM hle
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hN
    rcases hN with rfl | rfl | rfl
    · exact hq₁ M hM hle
    · exact hq₂ M hM hle
    · exact hq₃ M hM hle
  have hq' : ∀ N ∈ ({ρ.ker, ρ₃.ker, ρ₂.ker} : Set (Subgroup ↥(typeACore K P))),
      ∀ M : Subgroup ↥(typeACore K P), M.Normal → N ≤ M → M = N ∨ M = ⊤ := by
    intro N hN M hM hle
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hN
    rcases hN with rfl | rfl | rfl
    · exact hq₁ M hM hle
    · exact hq₃ M hM hle
    · exact hq₂ M hM hle
  have hU : ∀ v, v ∈ LinearMap.range (lowNil (K := K) P) ↔
      ∀ x ∈ ρ.ker ⊓ ρ₂.ker ⊓ ρ₃.ker,
        projLift hQ (x : matrixProjectiveDerived (coordinateQuadPlus n K)) v = v := by
    intro v
    rw [hR]
    exact mem_range_lowNil_iff_forall_R P hn (by omega) (by omega) hq4 hQ v
  have hTr : ∀ g : similarityPairs (coordinateQuadPlus n K),
      (∀ x ∈ typeACore K P, matrixProjectiveConjugationHom _ g x ∈ typeACore K P) →
      ∀ u ∈ LinearMap.range (lowNil (K := K) P),
        coordinateSemilinearMap g.val u ∈ LinearMap.range (lowNil (K := K) P) :=
    fun g hgX => mapsTo_of_fixedSpace_eq hQ ρ.ker ρ₂.ker ρ₃.ker hN h123 hRn _ hU g hgX
  have hTW : ∀ g : similarityPairs (coordinateQuadPlus n K),
      (∀ x ∈ typeACore K P, matrixProjectiveConjugationHom _ g x ∈ typeACore K P) →
      ∀ u ∈ lowSpan K n ℓ, coordinateSemilinearMap g.val u ∈ lowSpan K n ℓ := by
    intro g hgX u hu
    rw [← range_lowNil P] at hu ⊢
    exact hTr g hgX u hu
  obtain ⟨hs₂, hnc₂⟩ := simple_nonabelian_of_surjective_sp hq4 le_rfl ρ₂ hρ₂
  obtain ⟨hs₃, hnc₃⟩ := simple_nonabelian_of_surjective_sp hq4 le_rfl ρ₃ hρ₃
  have h₁₂ : IsEmpty (↥(typeACore K P) ⧸ ρ.ker ≃* ↥(typeACore K P) ⧸ ρ₂.ker) :=
    isEmpty_quotient_mulEquiv_of_ne (by omega) ρ hρ ρ₂ hρ₂
  have h₁₃ : IsEmpty (↥(typeACore K P) ⧸ ρ.ker ≃* ↥(typeACore K P) ⧸ ρ₃.ker) :=
    isEmpty_quotient_mulEquiv_of_ne (by omega) ρ hρ ρ₃ hρ₃
  have hne : ρ₂.ker ≠ ρ₃.ker := by
    obtain ⟨B, hB⟩ := exists_sl2_ne_one (K := K)
    obtain ⟨x, hx⟩ := coreSLPair_surjective P hℓ2 hQ hq4 (1, B)
    intro heq
    have h1 : x ∈ ρ₂.ker := (mem_ker_coreSpLeft P hℓ2 hQ hq4 x).mpr (by rw [hx])
    rw [heq] at h1
    have h2 := (mem_ker_coreSpRight P hℓ2 hQ hq4 x).mp h1
    rw [hx] at h2
    exact hB h2
  have hXU : ∀ x ∈ typeACore K P, ∀ u ∈ LinearMap.range (lowNil (K := K) P),
      projLift hQ x u ∈ LinearMap.range (lowNil (K := K) P) := fun x hx =>
    mem_range_of_commute (fun v => projLift_lowNil_of_mem_core hQ hx v)
  have hs₁ : SpLeviSection (plusFieldPart hf hK hn) (typeACore K P) ρ.ker :=
    spLeviSection_of_trace_restrict hQ _ (fun g => orthAutFieldPart_kappa _ _ g)
      (exists_kappa_eq_plus hn) (LinearMap.range (lowNil P)) hXU hTr hr ρ hρ htr
  have hsl : SpLeviSection (plusFieldPart hf hK hn) (typeACore K P) ρ₂.ker :=
    spLeviSection_coreSpLeft P hℓ2 hQ hq4 hf hK hn hTW fun β hβ hN₂ =>
      mapsTo_of_mapsTo_of_isEmpty ρ.ker ρ₂.ker ρ₃.ker h123 hq hnc₃ h₁₃ hne
        (restrictAutOfMapsTo β _ hβ) hN₂
  have hsr : SpLeviSection (plusFieldPart hf hK hn) (typeACore K P) ρ₃.ker :=
    spLeviSection_coreSpRight P hℓ2 hQ hq4 hf hK hn hTW fun β hβ hN₃ =>
      mapsTo_of_mapsTo_of_isEmpty ρ.ker ρ₃.ker ρ₂.ker h132 hq' hnc₂ h₁₂ hne.symm
        (restrictAutOfMapsTo β _ hβ) hN₃
  have hs : ∀ (N : Subgroup ↥(typeACore K P)) [N.Normal],
      N ∈ ({ρ.ker, ρ₂.ker, ρ₃.ker} : Set (Subgroup ↥(typeACore K P))) →
        SpLeviSection (plusFieldPart hf hK hn) (typeACore K P) N := by
    intro N _ hN
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hN
    rcases hN with rfl | rfl | rfl
    · exact hs₁
    · exact hsl
    · exact hsr
  have he₂ : IsEmpty (↥(typeACore K P) ⧸ ρ₂.ker ≃* StatedProj (StatedSp r K)) :=
    ⟨fun e => by
      have := rank_eq_of_mulEquiv ((chartOfSurjective ρ₂ hρ₂).symm.trans e)
      omega⟩
  have he₃ : IsEmpty (↥(typeACore K P) ⧸ ρ₃.ker ≃* StatedProj (StatedSp r K)) :=
    ⟨fun e => by
      have := rank_eq_of_mulEquiv ((chartOfSurjective ρ₃ hρ₃).symm.trans e)
      omega⟩
  exact spLeviData_of_isEmpty_mulEquiv _ hq4 ρ.ker ρ₂.ker ρ₃.ker h123 hq hs hr
    (chartOfSurjective ρ hρ) he₂ he₃

theorem spLeviData_lowRep_nSubTwo {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) {n ℓ : ℕ}
    (hn : 5 ≤ n) (hq4 : 4 ≤ Nat.card K) (P : LowPairing n ℓ) (hℓ2 : ℓ + 2 = n) :
    SpLeviData (plusFieldPart hf hK hn) (typeACore K P) := by
  have hQ : ∃ v, coordinateQuadPlus n K v ≠ 0 := exists_coordinateQuadPlus_ne_zero (by omega)
  have hβ := wallForm_lowRep_isAlt (K := K) P
  have hβn := wallForm_lowRep_nondegenerate (K := K) P (by omega)
  obtain ⟨r, b, hdim, hb⟩ := CFSG.RankThree.PartOne.KCAlternating.exists_isSymplecticBasis hβ hβn
  have hr2 : 2 ≤ r := by
    rw [range_lowNil, finrank_lowSpan (by omega)] at hdim
    omega
  have hr : 1 ≤ r := by omega
  have hpres : ∀ (x : typeACore K P) (u u' : LinearMap.range (lowNil (K := K) P)),
      wallForm (QuadraticMap.polarBilin (coordinateQuadPlus n K)) (lowNil P) (polar_lowNil_left P)
        (rangeRestrictHom hQ (typeACore K P) (lowNil P)
          (fun _ hx v => projLift_lowNil_of_mem_core hQ hx v) x u)
        (rangeRestrictHom hQ (typeACore K P) (lowNil P)
          (fun _ hx v => projLift_lowNil_of_mem_core hQ hx v) x u') =
      wallForm (QuadraticMap.polarBilin (coordinateQuadPlus n K)) (lowNil P) (polar_lowNil_left P)
        u u' := fun x u u' =>
    wallForm_map _ _ _ (g := (projLift hQ (x : matrixProjectiveDerived (coordinateQuadPlus n K)) :
      (Fin (2 * n) → K) →ₗ[K] (Fin (2 * n) → K)))
      (fun v => projLift_lowNil_of_mem_core hQ x.2 v) (polar_projLift hQ _) u u'
  have hρ : Function.Surjective (sympChart hβ hb (rangeRestrictHom hQ (typeACore K P) (lowNil P)
      (fun _ hx v => projLift_lowNil_of_mem_core hQ hx v)) hpres) := fun A =>
    ⟨spLeviX P b hQ hb hq4 hr A, Subtype.ext (Units.ext (by
      rw [coe_sympChart, rangeRestrictHom_spLeviX, LinearMap.toMatrix_toLin]))⟩
  exact spLeviData_nSubTwo_of_rangeChart hf hK hn hq4 P hℓ2 hr2 _ hρ
    (sympChart_ker hβ hb _ hpres) (fun x => spMatTrace_sympChart hβ hb _ hpres x)

theorem exists_conj_spLeviData_typeA_nSubTwo {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    {n : ℕ} (hn : 5 ≤ n) (hq4 : 4 ≤ Nat.card K) (s : matrixIsometries (coordinateQuadPlus n K))
    (hss : s * s = 1)
    (hA : ∀ w ∈ LinearMap.range (sNil s.val), coordinateQuadPlus n K w = 0)
    (hℓ : finrank K (LinearMap.range (sNil s.val)) + 2 = n) :
    ∃ s₀ a : matrixIsometries (coordinateQuadPlus n K), s = a * s₀ * a⁻¹ ∧
      SpLeviData (plusFieldPart hf hK hn)
        (perfectCore (autFixSubgroup (isometryConjugationHom _ s₀))) := by
  have hreg := regular_coordinateQuadPlus n K (by omega)
  obtain ⟨r, hr⟩ := even_finrank_range_sNil_of_typeA hreg.1 hss hA
  have h2r : 2 * r ≤ n := by omega
  set P : LowPairing n (2 * r) := LowPairing.std h2r
  have hdim₀ : finrank K (LinearMap.range (sNil (lowRep (K := K) P).val)) = 2 * r := by
    rw [sNil_lowRep, range_lowNil, finrank_lowSpan h2r]
  have hA₀ : ∀ w ∈ LinearMap.range (sNil (lowRep (K := K) P).val),
      coordinateQuadPlus n K w = 0 := by
    rw [sNil_lowRep, range_lowNil]
    exact fun w hw => coordinateQuadPlus_lowSpan hw
  obtain ⟨a, ha⟩ := exists_conj_eq_of_typeA hreg.1 hss (lowRep_mul_self P) hA hA₀
    (by rw [hdim₀]; omega) (by rw [hdim₀]; omega)
  exact ⟨lowRep P, a, ha, spLeviData_lowRep_nSubTwo hf hK hn hq4 P (by omega)⟩

end CFSG.SeitzReduction.OmegaPilot
