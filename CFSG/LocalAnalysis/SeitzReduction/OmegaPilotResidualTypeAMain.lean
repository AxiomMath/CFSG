module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualTypeASection
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualTypeAConj
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualLeviAssembly
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualTypeAFixSpace

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Module QuadraticMap CFSG.Assembly.LowTwoRank
open CFSG.Quasithin (perfectCore)
open LinearPilot (autFixSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (plusIndexEquiv coordinateQuadPlus regular_coordinateQuadPlus)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter (isometryConjugationHom)
open CFSG.RankThree.Classical2 (orthDerived)

variable {K : Type} [Field K] [Finite K] [CharP K 2]

section Sections

variable {C : Type*} [Group C] [Finite C] (fp : MulAut C →* (K ≃+* K)) (X : Subgroup C)

theorem secondSection_of_eq_top (N : Subgroup ↥X) [N.Normal] (hN : N = ⊤) :
    (∀ M : Subgroup ↥X, M.Normal → N ≤ M → M = N ∨ M = ⊤) ∧
      (N = ⊤ ∨ ∃ a b : ↥X ⧸ N, a * b ≠ b * a) ∧ SpLeviSection fp X N ∧
      ∀ r : ℕ, 1 ≤ r → IsEmpty (↥X ⧸ N ≃* StatedProj (StatedSp r K)) := by
  subst hN
  refine ⟨fun M _ hM => Or.inr (top_le_iff.mp hM), Or.inl rfl, spLeviSection_top fp X,
    fun r hr => ⟨fun ε => ?_⟩⟩
  have h1 : Nat.card (↥X ⧸ (⊤ : Subgroup ↥X)) = 1 :=
    @Nat.card_of_subsingleton _ 1 QuotientGroup.subsingleton_quotient_top
  have h2 := Nat.card_congr ε.toEquiv
  have h3 := one_lt_card_statedProj_statedSp (K := K) hr
  omega

theorem secondSection_of_mulEquiv (N : Subgroup ↥X) [N.Normal] {f : ℕ} (hK : Nat.card K = 2 ^ f)
    (hf : 1 ≤ f) {m : ℕ} (hm : 3 ≤ m) (e : ↥X ⧸ N ≃* orthDerived (coordinateQuadPlus m K)) :
    (∀ M : Subgroup ↥X, M.Normal → N ≤ M → M = N ∨ M = ⊤) ∧
      (N = ⊤ ∨ ∃ a b : ↥X ⧸ N, a * b ≠ b * a) ∧ SpLeviSection fp X N ∧
      ∀ r : ℕ, 1 ≤ r → IsEmpty (↥X ⧸ N ≃* StatedProj (StatedSp r K)) := by
  have := isSimpleGroup_orthDerived_coordinateQuadPlus (K := K) hm
  have : IsSimpleGroup (↥X ⧸ N) := MulEquiv.isSimpleGroup e
  obtain ⟨a, b, hab⟩ := exists_mul_ne_orthDerived_coordinateQuadPlus (K := K) hm
  refine ⟨fun M hM hle => eq_or_eq_top_of_simple_quotient M hM hle,
    Or.inr ⟨e.symm a, e.symm b, fun hc => hab ?_⟩,
    spLeviSection_of_mulEquiv_orthDerived fp X N hK hf hm e,
    fun r _ => isEmpty_mulEquiv_statedSp_of_mulEquiv_orthDerived hK hf hm e r⟩
  have h' := congrArg e hc
  simpa using h'

end Sections

theorem spLeviData_lowRep {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) {n ℓ : ℕ} (hn : 5 ≤ n)
    (hq4 : 4 ≤ Nat.card K) (P : LowPairing n ℓ) (hℓn : ℓ ≤ n) (hℓ0 : 0 < ℓ) (hℓ2 : ℓ + 2 ≠ n) :
    SpLeviData (plusFieldPart hf hK hn) (typeACore K P) := by
  have hQ : ∃ v, coordinateQuadPlus n K v ≠ 0 := exists_coordinateQuadPlus_ne_zero (by omega)
  have hβ := wallForm_lowRep_isAlt (K := K) P
  have hβn := wallForm_lowRep_nondegenerate (K := K) P (by omega)
  obtain ⟨r, b, hdim, hb⟩ := CFSG.RankThree.PartOne.KCAlternating.exists_isSymplecticBasis hβ hβn
  have hr : 1 ≤ r := by
    rw [range_lowNil, finrank_lowSpan hℓn] at hdim
    omega
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
  have hker := sympChart_ker hβ hb (rangeRestrictHom hQ (typeACore K P) (lowNil P)
      (fun _ hx v => projLift_lowNil_of_mem_core hQ hx v)) hpres
  have hsec : (∀ M : Subgroup ↥(typeACore K P), M.Normal →
        (kerQuotHom hQ (typeACore K P) (lowNil P)
          (fun _ hx v => projLift_lowNil_of_mem_core hQ hx v)).ker ≤ M →
        M = (kerQuotHom hQ (typeACore K P) (lowNil P)
          (fun _ hx v => projLift_lowNil_of_mem_core hQ hx v)).ker ∨ M = ⊤) ∧
      ((kerQuotHom hQ (typeACore K P) (lowNil P)
          (fun _ hx v => projLift_lowNil_of_mem_core hQ hx v)).ker = ⊤ ∨
        ∃ a b : ↥(typeACore K P) ⧸ (kerQuotHom hQ (typeACore K P) (lowNil P)
          (fun _ hx v => projLift_lowNil_of_mem_core hQ hx v)).ker, a * b ≠ b * a) ∧
      SpLeviSection (plusFieldPart hf hK hn) (typeACore K P)
        (kerQuotHom hQ (typeACore K P) (lowNil P)
          (fun _ hx v => projLift_lowNil_of_mem_core hQ hx v)).ker ∧
      ∀ r : ℕ, 1 ≤ r → IsEmpty (↥(typeACore K P) ⧸ (kerQuotHom hQ (typeACore K P) (lowNil P)
          (fun _ hx v => projLift_lowNil_of_mem_core hQ hx v)).ker ≃*
            StatedProj (StatedSp r K)) := by
    rcases (show n = ℓ ∨ n = ℓ + 1 ∨ ℓ + 3 ≤ n by omega) with h0 | h1 | h3
    · exact secondSection_of_eq_top _ _ _ (kerQuotHom_ker_eq_top_of_eq P hQ h0.symm)
    · exact secondSection_of_eq_top _ _ _ (kerQuotHom_ker_eq_top_of_one P hQ h1.symm)
    · obtain ⟨m, hm⟩ : ∃ m, ℓ + m = n := ⟨n - ℓ, by omega⟩
      exact secondSection_of_mulEquiv _ _ _ hK hf (by omega : 3 ≤ m)
        (coreSectionEquiv P hm hQ (by omega))
  obtain ⟨hq₂, hab₂, hs₂, h₂⟩ := hsec
  exact spLeviData_of_rangeChart hf hK hn hq4 (lowNil P)
    (fun _ hx v => projLift_lowNil_of_mem_core hQ hx v) hr _ hρ hker
    (fun x => spMatTrace_sympChart hβ hb _ hpres x) hq₂ hab₂ hs₂ (h₂ r hr)
    (by rw [hker]; exact mem_range_lowNil_iff_forall_R P hn hℓn hℓ0 hq4 hQ)

omit [Finite K] [CharP K 2] in
theorem finrank_range_sNil_le [CharP K 2] {n : ℕ} {s : GL (Fin (2 * n)) K} (hss : s * s = 1) :
    finrank K (LinearMap.range (sNil s)) ≤ n := by
  have hle : LinearMap.range (sNil s) ≤ LinearMap.ker (sNil s) := by
    rintro _ ⟨v, rfl⟩
    exact sNil_sNil hss v
  have h1 := LinearMap.finrank_range_add_finrank_ker (sNil s)
  have h2 := Submodule.finrank_mono hle
  rw [Module.finrank_fin_fun] at h1
  omega

omit [Finite K] [CharP K 2] in
theorem finrank_range_sNil_pos {n : ℕ} {s : matrixIsometries (coordinateQuadPlus n K)}
    (hs : orderOf (isometryConjugationHom _ s) = 2) :
    0 < finrank K (LinearMap.range (sNil s.val)) := by
  by_contra h0
  have h0' : finrank K (LinearMap.range (sNil s.val)) = 0 := by omega
  have hbot : LinearMap.range (sNil s.val) = ⊥ := Submodule.finrank_eq_zero.mp h0'
  have hN : sNil s.val = 0 := LinearMap.range_eq_bot.mp hbot
  have h1 : matrixLinearIso s.val = matrixLinearIso 1 := by
    rw [map_one]
    refine LinearEquiv.ext fun v => ?_
    have := LinearMap.congr_fun hN v
    rw [sNil_apply, LinearMap.zero_apply, sub_eq_zero] at this
    exact this
  have hs1 : s = 1 := Subtype.ext (matrixLinearIso.injective h1)
  rw [hs1, map_one, orderOf_one] at hs
  omega

theorem exists_conj_spLeviData_typeA {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) {n : ℕ}
    (hn : 5 ≤ n) (hq4 : 4 ≤ Nat.card K) (s : matrixIsometries (coordinateQuadPlus n K))
    (hs : orderOf (isometryConjugationHom _ s) = 2)
    (hA : ∀ w ∈ LinearMap.range (sNil s.val), coordinateQuadPlus n K w = 0)
    (hℓ : finrank K (LinearMap.range (sNil s.val)) + 2 ≠ n) :
    ∃ s₀ a : matrixIsometries (coordinateQuadPlus n K), s = a * s₀ * a⁻¹ ∧
      SpLeviData (plusFieldPart hf hK hn)
        (perfectCore (autFixSubgroup (isometryConjugationHom _ s₀))) := by
  have hss := mul_self_eq_one_of_orderOf_plus (by omega) hs
  have hreg := regular_coordinateQuadPlus n K (by omega)
  have heven := even_finrank_range_sNil_of_typeA hreg.1 hss hA
  have hℓn := finrank_range_sNil_le (congrArg Subtype.val hss)
  have hℓ0 := finrank_range_sNil_pos hs
  obtain ⟨r, hr⟩ := heven
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
  exact ⟨lowRep P, a, ha, spLeviData_lowRep hf hK hn hq4 P h2r (by omega) (by omega)⟩

end CFSG.SeitzReduction.OmegaPilot
