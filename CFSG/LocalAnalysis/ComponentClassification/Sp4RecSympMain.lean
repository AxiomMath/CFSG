module

public import CFSG.LocalAnalysis.ComponentClassification.Sp4RecSymp

public noncomputable section

namespace CFSG.ComponentClassification.Sp4Rec

open CFSG Subgroup Module CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.CatalogueBSymplecticB
open CFSG.ComponentClassification.CatalogueBAlternatingIsometry
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBFixedCentralQuotient (onQuotient fixedProjection)
open LinearMap (BilinForm)
open CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]

theorem pairConfig_projectiveSymplectic_false {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hf : 1 ≤ f) [Finite K] (hK : Nat.card K = ℓ ^ f) [FiniteDimensional K V] {r : ℕ}
    (hr : 3 ≤ r) (hdim : finrank K V = 2 * r) {B : BilinForm K V} (hB : B.IsAlt)
    (hBnd : B.Nondegenerate) {x : projectiveSymplectic B}
    {K₁ K₂ : Subgroup (projectiveSymplectic B)} (hc : PairConfig _ x K₁ K₂) : False := by
  classical
  have hodd : Odd (Nat.card K) := by rw [hK]; exact (hℓ.odd_of_ne_two hℓ2).pow
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd_natCard hodd
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (scalarSigns B) x
  have hsim : ∀ v w, B (g.val v) (g.val w) = ((1 : Kˣ) : K) * B v w := fun v w => by
    rw [Units.val_one, one_mul]
    exact (mem_isometryGroup_iff B _).mp g.2 v w
  set ψ := similitudeConjugation B g.val 1 hsim with hψdef
  have hψ := scalarSigns_invariant B g.val 1 hsim
  have hψg : ∀ h, ψ h = g * h * g⁻¹ := fun h => Subtype.ext rfl
  have hfix : fixedSubgroup (onQuotient (scalarSigns B) ψ hψ) =
      centralizer ({QuotientGroup.mk' (scalarSigns B) g} : Set (projectiveSymplectic B)) := by
    ext y
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (scalarSigns B) y
    rw [mem_centralizer_singleton_iff]
    change onQuotient _ ψ hψ (QuotientGroup.mk' (scalarSigns B) h) =
      QuotientGroup.mk' (scalarSigns B) h ↔ _
    rw [CatalogueBFixedCentralQuotient.onQuotient_mk, hψg, map_mul, map_mul, map_inv,
      mul_inv_eq_iff_eq_mul]
    exact eq_comm
  set e₁ := MulEquiv.subgroupCongr hfix with he₁
  obtain ⟨M₁, M₂, hM₁, hM₂, hMne, hm₁, hm₂⟩ := exists_fixed_lifts (scalarSigns B)
    (scalarSigns_central B) ψ hψ
    (CatalogueBAlternating.pComponent_map_equiv 2 e₁.symm _ hc.isPComponent_K)
    (CatalogueBAlternating.pComponent_map_equiv 2 e₁.symm _ hc.isPComponent_K') (by
      intro h
      apply hc.ne
      have h1 := subgroupOf_inj.mp (map_injective e₁.symm.injective h)
      rwa [inf_of_le_left hc.K_le, inf_of_le_left hc.K'_le] at h1)
  have htrans : ∀ (L : Subgroup (projectiveSymplectic B)) (M : Subgroup (fixedSubgroup ψ))
      (u : fixedSubgroup ψ),
      M.map (fixedProjection (scalarSigns B) ψ hψ) =
        (L.subgroupOf (centralizer {QuotientGroup.mk' (scalarSigns B) g})).map
          e₁.symm.toMonoidHom → u ∈ M →
      QuotientGroup.mk' (scalarSigns B) (u : isometryGroup B) ∈ L := by
    intro L M u hML hu
    have h1 : fixedProjection (scalarSigns B) ψ hψ u ∈
        (L.subgroupOf (centralizer {QuotientGroup.mk' (scalarSigns B) g})).map
          e₁.symm.toMonoidHom := hML ▸ mem_map_of_mem _ hu
    obtain ⟨z, hz, hzu⟩ := h1
    have h3 : ((fixedProjection (scalarSigns B) ψ hψ u : fixedSubgroup _) :
        projectiveSymplectic B) = (z : projectiveSymplectic B) := by
      rw [← hzu]
      rfl
    change ((fixedProjection (scalarSigns B) ψ hψ u : fixedSubgroup _) :
      projectiveSymplectic B) ∈ L
    rw [h3]
    exact mem_subgroupOf.mp hz
  set A : LinearMap.GeneralLinearGroup K V := LinearMap.GeneralLinearGroup.ofLinearEquiv g.val
    with hAdef
  set E₀ : fixedSubgroup ψ ≃* similitudeCentralizer B A :=
    (fixedCentralizerEquiv B g.val 1 hsim).trans (centralizerSimilitudeEquiv B A) with hE₀def
  have hE₀ : ∀ (u : fixedSubgroup ψ) (v : V),
      ((E₀ u : LinearMap.GeneralLinearGroup K V) : Module.End K V) v = u.val.val v :=
    fun u v => rfl
  have hx1 : QuotientGroup.mk' (scalarSigns B) g ≠ 1 := fun h => by
    have := hc.orderOf_x
    rw [h, orderOf_one] at this
    exact absurd this (by norm_num)
  have hAns : ∀ c : K, (A : Module.End K V) ≠ c • 1 := by
    intro c hcA
    have hAv : ∀ w, g.val w = c • w := fun w => LinearMap.congr_fun hcA w
    obtain ⟨u, hu⟩ := exists_ne (0 : V)
    obtain ⟨v, hv⟩ : ∃ v, B u v ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hu (hBnd.1 u hcon)
    have h1 := hsim u v
    rw [hAv, hAv, LinearMap.map_smul₂, LinearMap.map_smul, smul_eq_mul, smul_eq_mul,
      Units.val_one, one_mul, ← mul_assoc] at h1
    have hcc : c * c = 1 := mul_right_cancel₀ hv (h1.trans (one_mul _).symm)
    apply hx1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_scalarSigns_iff]
    rcases mul_self_eq_one_iff.mp hcc with rfl | rfl
    · left
      apply Subtype.ext
      apply LinearEquiv.ext
      intro w
      rw [hAv, one_smul]
      rfl
    · right
      apply Subtype.ext
      apply LinearEquiv.ext
      intro w
      rw [hAv, neg_one_smul]
      rfl
  have hg2 : g * g ∈ scalarSigns B := by
    have h1 : (QuotientGroup.mk' (scalarSigns B) g) ^ 2 = 1 := by
      rw [← hc.orderOf_x, pow_orderOf_eq_one]
    rwa [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, pow_two] at h1
  obtain ⟨d, hd, hdd⟩ : ∃ d : K, (d = 1 ∨ d = -1) ∧
      (A : Module.End K V) * (A : Module.End K V) = d • 1 := by
    rcases hg2 with h | h
    · refine ⟨1, Or.inl rfl, LinearMap.ext fun w => ?_⟩
      have h3 : g.val (g.val w) = w := by
        have := congrArg (fun z : isometryGroup B => z.val w) h
        simpa using this
      change g.val (g.val w) = (1 : K) • w
      rw [one_smul]
      exact h3
    · refine ⟨-1, Or.inr rfl, LinearMap.ext fun w => ?_⟩
      have h3 : g.val (g.val w) = -w := by
        have := congrArg (fun z : isometryGroup B => z.val w) h
        simpa [negIsometry_apply] using this
      change g.val (g.val w) = (-1 : K) • w
      rw [neg_one_smul]
      exact h3
  have hd0 : d ≠ 0 := by rcases hd with rfl | rfl <;> norm_num
  have hAμ : ∀ v w, B ((A : Module.End K V) v) ((A : Module.End K V) w) = 1 * B v w :=
    fun v w => by
      rw [one_mul]
      exact (mem_isometryGroup_iff B _).mp g.2 v w
  obtain ⟨hε, hsplit, hnonsplit⟩ := odd_symplectic_scalar_square_centralizer_structure hℓ hℓ2
    hf hK (by omega : 1 ≤ r) hdim hB hBnd hAns hd0 hdd hAμ
  by_cases hsq : ∃ l : K, l ^ 2 = d
  · obtain ⟨l, hl⟩ := hsq
    have hl0 : l ≠ 0 := by
      rintro rfl
      exact hd0 (by rw [← hl]; ring)
    obtain ⟨hP, hM, hpos, hneg⟩ := hsplit l hl
    rcases hε with h1 | h1
    · obtain ⟨-, haltP, haltM, hndP, hndM, e, he⟩ := hpos h1
      set E := E₀.trans e with hEdef
      set ι := (fixedSubgroup ψ).subtype
      have hK₁ : ∀ u ∈ M₁, QuotientGroup.mk' (scalarSigns B) (ι u) ∈ K₁ := fun u hu =>
        htrans K₁ M₁ u hm₁ hu
      have hK₂ : ∀ u ∈ M₂, QuotientGroup.mk' (scalarSigns B) (ι u) ∈ K₂ := fun u hu =>
        htrans K₂ M₂ u hm₂ hu
      have hactP : ∀ (y : fixedSubgroup ψ) (v : eigenPlus l (A : Module.End K V)),
          (ι y).val v = ((((E y).1 : LinearMap.GeneralLinearGroup K
            (eigenPlus l (A : Module.End K V))) : Module.End K
              (eigenPlus l (A : Module.End K V))) v : eigenPlus l (A : Module.End K V)) := by
        intro y v
        have h3 := congrArg (fun φ => φ v) (he (E₀ y)).1
        simp only [LinearMap.comp_apply, Submodule.subtype_apply] at h3
        rw [hE₀] at h3
        exact h3.symm
      have hactM : ∀ (y : fixedSubgroup ψ) (v : eigenMinus l (A : Module.End K V)),
          (ι y).val v = ((((E y).2 : LinearMap.GeneralLinearGroup K
            (eigenMinus l (A : Module.End K V))) : Module.End K
              (eigenMinus l (A : Module.End K V))) v : eigenMinus l (A : Module.End K V)) := by
        intro y v
        have h3 := congrArg (fun φ => φ v) (he (E₀ y)).2
        simp only [LinearMap.comp_apply, Submodule.subtype_apply] at h3
        rw [hE₀] at h3
        exact h3.symm
      have hgP : ∀ v ∈ eigenPlus l (A : Module.End K V), g.val v = l • v := by
        intro v hv
        have h3 : (invSMulOp l (A : Module.End K V) - 1) v = 0 := hv
        simp only [invSMulOp, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
          sub_eq_zero] at h3
        calc g.val v = (A : Module.End K V) v := rfl
          _ = l • (l⁻¹ • (A : Module.End K V) v) := by
              rw [smul_smul, mul_inv_cancel₀ hl0, one_smul]
          _ = l • v := by rw [h3]
      have hgM : ∀ v ∈ eigenMinus l (A : Module.End K V), g.val v = (-l) • v := by
        intro v hv
        have h3 : (invSMulOp l (A : Module.End K V) + 1) v = 0 := hv
        simp only [invSMulOp, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
          add_eq_zero_iff_eq_neg] at h3
        calc g.val v = (A : Module.End K V) v := rfl
          _ = l • (l⁻¹ • (A : Module.End K V) v) := by
              rw [smul_smul, mul_inv_cancel₀ hl0, one_smul]
          _ = (-l) • v := by rw [h3, smul_neg, neg_smul]
      have hcompl : IsCompl (eigenPlus l (A : Module.End K V))
          (eigenMinus l (A : Module.End K V)) :=
        isCompl_ker_sub_one_ker_add_one h2 (invSMulOp_mul_self hl0 (by rw [hl]; exact hdd))
      have hsum := Submodule.finrank_add_eq_of_isCompl hcompl
      obtain ⟨a, ha⟩ := even_finrank _ haltP hndP
      obtain ⟨b, hb⟩ := even_finrank _ haltM hndM
      have hP2 := two_le_finrank_of_ne_bot hP _ haltP hndP
      have hM2 := two_le_finrank_of_ne_bot hM _ haltM hndM
      by_cases h4 : 4 ≤ finrank K (eigenPlus l (A : Module.End K V))
      · exact false_of_split_factor hodd hc ι hM₁ hM₂ hMne hK₁ hK₂ haltP hndP haltM hndM h4 hM
          E hactP hactM hgP
      · have h4' : 4 ≤ finrank K (eigenMinus l (A : Module.End K V)) := by omega
        exact false_of_split_factor hodd hc ι hM₁ hM₂ hMne hK₁ hK₂ haltM hndM haltP hndP h4' hP
          (E.trans (MulEquiv.prodComm)) (fun y w => hactM y w) (fun y v => hactP y v) hgM
    · obtain ⟨-, -, -, -, -, -, e, -⟩ := hneg h1
      set E := E₀.trans e
      exact hMne (map_injective E.injective (linGL_pComponent_eq
        (Submodule.one_le_finrank_iff.mpr hP)
        (CatalogueBAlternating.pComponent_map_equiv 2 E _ hM₁)
        (CatalogueBAlternating.pComponent_map_equiv 2 E _ hM₂)))
  · push Not at hsq
    have hd1 : d = -1 := hd.resolve_left fun h => hsq 1 (by rw [h]; ring)
    have h1 : (1 : K) / d = -1 := by rw [hd1]; norm_num
    obtain ⟨-, hF, hcard, hfinrank, bar, hbar, -, hbarbar, -, hneg⟩ := hnonsplit hsq
    obtain ⟨hh, -, hsymm, hsep, hiff⟩ := hneg h1
    have hEodd : Odd (Nat.card (scalarSquareField (A : Module.End K V))) := by
      rw [hcard]
      exact (hℓ.odd_of_ne_two hℓ2).pow.pow
    set E := fixedCentralizerEquiv B g.val 1 hsim
    exact hMne (map_injective E.injective (herm_centralizer_pComponent_eq hodd B A hAns hF hEodd
      (by omega) bar hbar hbarbar hh hsymm hsep hiff
      (CatalogueBAlternating.pComponent_map_equiv 2 E _ hM₁)
      (CatalogueBAlternating.pComponent_map_equiv 2 E _ hM₂)))

namespace Config

variable {H : Type} [Group H] [Finite H] (c : Sp4Rec.Config H)

include c in
theorem false_of_psp_high {n p f : ℕ} (hp2 : p ≠ 2) (hn : 3 ≤ n)
    (hG : StatedClassicalModel ↥(generalizedFitting H) .PSp n p f) : False := by
  obtain ⟨⟨hp, hf, -⟩, K, _, _, hK, ⟨φ⟩⟩ := hG
  exact pairConfig_projectiveSymplectic_false hp hp2 hf hK hn SymplecticFlag.finrank_standard
    SymplecticFlag.pairedSympForm_isAlt SymplecticFlag.pairedSympForm_nondegenerate
    (c.pairConfig (φ.trans (projectiveStatedEquiv (K := K) (by omega : 1 ≤ n))))

end Config

end CFSG.ComponentClassification.Sp4Rec
