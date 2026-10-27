module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Gen2318Local

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Gen2318Local

namespace Gen2318LocalE64Aux

theorem charP_two_of_card_four (K' : Type) [Field K'] [Finite K'] (h : Nat.card K' = 4) :
    CharP K' 2 := by
  classical
  haveI : Fintype K' := Fintype.ofFinite K'
  obtain ⟨p, hchar, n, hp, hcard⟩ := FiniteField.card' K'
  rw [Fintype.card_eq_nat_card, h] at hcard
  have hdvd : p ∣ 4 := by
    rw [hcard]
    exact dvd_pow_self p (PNat.ne_zero n)
  have hle : p ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
  have hp2 : p = 2 := by
    interval_cases p <;> first | rfl | exact absurd hdvd (by decide) | exact absurd hp (by decide)
  rw [hp2] at hchar
  exact hchar

theorem pow3_pi {ι : Type} {K' : Type} [Field K'] (x : ι → rootsOfUnity 3 K') : x ^ 3 = 1 := by
  funext j
  apply Subtype.ext
  have hj := (mem_rootsOfUnity 3 ((x j : rootsOfUnity 3 K') : K'ˣ)).1 (x j).2
  simpa using hj

section E6

set_option linter.unusedSectionVars false

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.CentralExt.MinusculeClosed
  CFSG.LieType.Steinberg.CentralExt.FieldFour


@[expose] def embFun {F : Type} [Field F] (x : Fin 5 → rootsOfUnity 3 F) : Fin 6 → Fˣ :=
  Fin.cons (α := fun _ => Fˣ) 1 (fun j => ((x j : rootsOfUnity 3 F) : Fˣ))

theorem embFun_zero {F : Type} [Field F] (x : Fin 5 → rootsOfUnity 3 F) : embFun x 0 = 1 := by
  simp [embFun]

theorem embFun_succ {F : Type} [Field F] (x : Fin 5 → rootsOfUnity 3 F) (j : Fin 5) :
    embFun x j.succ = ((x j : rootsOfUnity 3 F) : Fˣ) := by
  simp [embFun]

theorem embFun_mul {F : Type} [Field F] (x y : Fin 5 → rootsOfUnity 3 F) :
    embFun (x * y) = embFun x * embFun y := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [embFun_zero]
  · simp [embFun_succ]

@[expose] def embTorus (F : Type) [Field F] : (Fin 5 → rootsOfUnity 3 F) →* (Fin 6 → Fˣ) :=
  MonoidHom.mk' embFun embFun_mul

theorem e6_four_witness {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2 ^ 2)
    {K : Type} [Group K] [Finite K] (ρ : K →* AdjointQuotient Tag.E6 F)
    (hρ : Function.Surjective ρ) (hρk : ρ.ker = Subgroup.center K) :
    ∃ E P : Subgroup K, IsElemAbelian 3 E ∧ E ⊓ Subgroup.center K = ⊥ ∧
      5 ≤ CFSG.Open.pRank 3 E ∧ P ≠ ⊥ ∧ IsPGroup 2 P ∧ E ≤ Subgroup.normalizer (P : Set K) := by
  classical
  haveI : CharP F 2 := charP_two_of_card_four F (by rw [hF]; norm_num)
  have h2F : (2 : F) = 0 := by
    have h := CharP.cast_eq_zero F 2
    exact_mod_cast h
  haveI : Finite (e6Data_valid.minGroup F) := finite_minGroup' e6Data_valid
  let π : e6Data_valid.minGroup F →* AdjointQuotient Tag.E6 F :=
    (QuotientGroup.mk' (Subgroup.center ↥(adjointGroup Tag.E6 F))).comp (e6Isogeny F)
  have hπ : Function.Surjective π :=
    (QuotientGroup.mk'_surjective _).comp (e6Isogeny_surjective F)
  have hπk : π.ker = Subgroup.center (e6Data_valid.minGroup F) := by
    rw [← e6Isogeny_ker_eq_center (K := F)]
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    change (QuotientGroup.mk (e6Isogeny F x) : AdjointQuotient Tag.E6 F) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff, CFSG.LieType.Chevalley.center_adjointGroup_eq_bot,
      Subgroup.mem_bot]
  let Ehom : (Fin 5 → rootsOfUnity 3 F) →* e6Data_valid.minGroup F :=
    (minTorus e6Data_valid F).comp (embTorus F)
  have hAcard : Nat.card (Fin 5 → rootsOfUnity 3 F) = 3 ^ 5 := by
    rw [Nat.card_fun, Gen2318LocalAux.card_mu3 (F := F) (by rw [hF]; norm_num)]
    simp
  have hAcen : ∀ x : Fin 5 → rootsOfUnity 3 F,
      Ehom x ∈ Subgroup.center (e6Data_valid.minGroup F) → x = 1 := by
    intro x hx
    have hu : embTorus F x ∈ centerChars .E6 F := (minTorus_mem_center_iff e6Data_valid F _).1 hx
    funext j
    apply Subtype.ext
    have h := eq_zpow_of_mem_centerChars e6C_spec hu j.succ
    have h0 : embTorus F x (⟨0, by decide⟩ : Fin (Tag.rank .E6)) = 1 := embFun_zero x
    rw [h0, one_zpow] at h
    exact (embFun_succ x j).symm.trans h
  let i₀ : Fin (Tag.rank .E6) := ⟨0, by decide⟩
  let Phom : Multiplicative F →* e6Data_valid.minGroup F := e6Data_valid.xHom F (Pi.single i₀ 1)
  have hB2 : ∀ b : Multiplicative F, b ^ 2 = 1 := by
    intro b
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, nsmul_eq_mul, Nat.cast_ofNat, h2F, zero_mul]
  have hb₀ : Phom (Multiplicative.ofAdd (1 : F)) ∉ Subgroup.center (e6Data_valid.minGroup F) := by
    intro hz
    rw [← e6Isogeny_ker_eq_center (K := F)] at hz
    exact e6Isogeny_xm_single_one_ne_one F i₀ (MonoidHom.mem_ker.1 hz)
  have hconj : ∀ (x : Fin 5 → rootsOfUnity 3 F) (b : Multiplicative F),
      ∃ b' : Multiplicative F, Ehom x * Phom b * (Ehom x)⁻¹ = Phom b' := fun x b =>
    ⟨_, minTorus_conj_xm e6Data_valid F (embTorus F x) (IsRoot.basis i₀) (Multiplicative.toAdd b)⟩
  exact Gen2318LocalAux.core_generic
    (fun E _ _ p hp hc => e6_four_exists_section hF E p hp hc) π hπ hπk ρ hρ hρk Ehom
    (fun x => pow3_pi x) 5 hAcard hAcen Phom hB2 (Multiplicative.ofAdd 1) hb₀ hconj

end E6

end Gen2318LocalE64Aux

section Main

set_option linter.unusedSectionVars false


theorem gen2318Residual_E64 :
    ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K → ∀ d : TauCeti.ValidLieTypeIndex,
      Gen2318Index d.1 → (∃ q, d.1 = TauCeti.LieTypeIndex.E6 q ∧ IsTwoPow q 2) →
        Nonempty ((K ⧸ Subgroup.center K) ≃* (TauCeti.CFSGIndex.lie d).Group) →
          ∃ E P : Subgroup K, IsElemAbelian 3 E ∧ E ⊓ Subgroup.center K = ⊥ ∧
            rho2318 d.1 ≤ CFSG.Open.pRank 3 E ∧ P ≠ ⊥ ∧ IsPGroup 2 ↥P ∧
            E ≤ Subgroup.normalizer (P : Set K) := by
  intro K _ _ _hq d _hd hE hiso
  obtain ⟨q, hdq, hq1, hq2⟩ := hE
  obtain ⟨idx, hv⟩ := d
  obtain ⟨e⟩ := hiso
  have hdq' : idx = TauCeti.LieTypeIndex.E6 q := hdq
  subst hdq'
  have hK4 : Nat.card (GaloisField 2 2) = TauCeti.PrimePower.card q := by
    rw [TauCeti.PrimePower.card_def, GaloisField.card 2 2 (by norm_num), hq1, hq2]
  obtain ⟨ψ0⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_E6 q hv hq1 (GaloisField 2 2) hK4
  let ψ := e.trans ψ0.symm
  have hF : Nat.card (GaloisField 2 2) = 2 ^ 2 := GaloisField.card 2 2 (by norm_num)
  let ρ : K →* CFSG.Blueprint.AdjointQuotient CFSG.Blueprint.Chevalley.Tag.E6 (GaloisField 2 2) :=
    ψ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hρ : Function.Surjective ρ := ψ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hρk : ρ.ker = Subgroup.center K := by
    ext x
    rw [MonoidHom.mem_ker]
    change ψ (QuotientGroup.mk x) = 1 ↔ x ∈ Subgroup.center K
    rw [map_eq_one_iff ψ ψ.injective, QuotientGroup.eq_one_iff]
  obtain ⟨E, P, h1, h2, h3, h4, h5, h6⟩ := Gen2318LocalE64Aux.e6_four_witness hF ρ hρ hρk
  have hrk : rho2318 (⟨TauCeti.LieTypeIndex.E6 q, hv⟩ : TauCeti.ValidLieTypeIndex).1 = 5 := by
    simp [rho2318, hq1, hq2]
  exact ⟨E, P, h1, h2, hrk.le.trans h3, h4, h5, h6⟩

@[expose] def Gen2318ResidualNoE64 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K → ∀ d : TauCeti.ValidLieTypeIndex,
    Gen2318Index d.1 → Gen2318Open d.1 →
      ¬ (∃ q, d.1 = TauCeti.LieTypeIndex.E6 q ∧ IsTwoPow q 2) →
        Nonempty ((K ⧸ Subgroup.center K) ≃* (TauCeti.CFSGIndex.lie d).Group) →
          ∃ E P : Subgroup K, IsElemAbelian 3 E ∧ E ⊓ Subgroup.center K = ⊥ ∧
            rho2318 d.1 ≤ CFSG.Open.pRank 3 E ∧ P ≠ ⊥ ∧ IsPGroup 2 ↥P ∧
            E ≤ Subgroup.normalizer (P : Set K)

theorem gen2318Residual_of_noE64 (h : Gen2318ResidualNoE64) : Gen2318Residual := by
  intro K _ _ hq d hd hopen hiso
  by_cases hE : ∃ q, d.1 = TauCeti.LieTypeIndex.E6 q ∧ IsTwoPow q 2
  · exact gen2318Residual_E64 K hq d hd hE hiso
  · exact h K hq d hd hopen hE hiso

end Main

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
