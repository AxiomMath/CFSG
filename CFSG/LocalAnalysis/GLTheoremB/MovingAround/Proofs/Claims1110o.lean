module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1110n2
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxExc
public import CFSG.LocalAnalysis.StandardType.GGExcRootAsGen

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1110o

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.StandardType.ExcRootAs
  CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1110n
open scoped MatrixGroups

section Rat


@[expose] def E8TwoFiveRatNotD4 : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] (p₀ : ℕ) (S : LangSetup Tag.E8 L p₀),
    (∃ Fr : L →+* L, (∀ c, Fr c = c ^ S.D.q) ∧ S.D.Φ = Units.map (entrywiseHom Fr)) →
    S.D.q = 2 → ∀ (a : Fin Tag.E8.rank → Lˣ), rootDiagUnit Tag.E8 a ∈ S.D.torus →
      (∀ j, a j ^ 5 = 1) → rootDiagUnit Tag.E8 a ≠ 1 → ∀ i : KernelComponent (rootCharHom a),
        CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) →
          Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
            Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) ≠ 174182400

end Rat

section NoD4

@[expose] def NoD4CompAt (S : Type) [Group S] : Prop :=
  ∀ β : MulAut S, β ∈ innAutDerived S → β ^ 5 = 1 → β ≠ 1 →
    ∀ K : Subgroup S, CFSG.Open.IsComponentOf K (fixSubgroup β) →
      Nat.card (↥K ⧸ Subgroup.center ↥K) ≠ 174182400

theorem noD4CompAt_of_mulEquiv {S S' : Type} [Group S] [Group S'] (e : S ≃* S')
    (h : NoD4CompAt S) : NoD4CompAt S' := by
  intro b hbmem hb5 hb1 K' hK'
  set α : MulAut S := MulAut.congr e.symm b with hα
  have hconj : MulAut.congr e α = b := by
    rw [hα]
    ext y
    simp [MulAut.congr_apply]
  have hαmem : α ∈ innAutDerived S := by
    rw [← mem_innAutDerived_congr e, hconj]
    exact hbmem
  have hα5 : α ^ 5 = 1 := by
    apply (MulAut.congr e).injective
    rw [map_pow, map_one, hconj]
    exact hb5
  have hα1 : α ≠ 1 := by
    intro h1
    apply hb1
    rw [← hconj, h1, map_one]
  set K : Subgroup S := K'.map (e.symm : S' →* S) with hK
  have hfix : (fixSubgroup b).map (e.symm : S' →* S) = fixSubgroup α := by
    rw [← hconj, CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fixSubgroup_congr e α,
      Subgroup.map_map]
    simp
  have hKcomp : IsComponentOf K (fixSubgroup α) := by
    rw [← hfix]
    exact CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map e.symm hK'
  have hKc := h α hαmem hα5 hα1 K hKcomp
  have hKmap : K.map (e : S →* S') = K' := by
    rw [hK, Subgroup.map_map]
    simp
  let ε : ↥K ≃* ↥K' :=
    (K.equivMapOfInjective (e : S →* S') e.injective).trans (MulEquiv.subgroupCongr hKmap)
  exact fun h' => hKc ((Nat.card_congr
    (CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsL33.centerQuotCongr ε).toEquiv).trans h')

end NoD4

section Adjoint


theorem exists_langSetup_component_E8Two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    (β : MulAut ↥(adjointGroup Tag.E8 K)) (hβmem : β ∈ innAutDerived ↥(adjointGroup Tag.E8 K))
    (hβ5 : β ^ 5 = 1) (hβ1 : β ≠ 1) {J : Subgroup ↥(adjointGroup Tag.E8 K)}
    (hJ : CFSG.Open.IsComponentOf J (fixSubgroup β)) :
    ∃ (p₀ : ℕ) (S : LangSetup Tag.E8 (AlgebraicClosure K) p₀)
      (a : Fin Tag.E8.rank → (AlgebraicClosure K)ˣ)
      (ι : ↥(adjointGroup Tag.E8 K) →* ModGL Tag.E8 (AlgebraicClosure K)),
      (∃ Fr : AlgebraicClosure K →+* AlgebraicClosure K,
        (∀ c, Fr c = c ^ S.D.q) ∧ S.D.Φ = Units.map (entrywiseHom Fr)) ∧
      S.D.q = 2 ∧ rootDiagUnit Tag.E8 a ∈ S.D.torus ∧ (∀ j, a j ^ 5 = 1) ∧
      rootDiagUnit Tag.E8 a ≠ 1 ∧ Function.Injective ι ∧ ι.range = S.Γ ∧
      (fixSubgroup β).map ι = S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E8 a} ∧
      ∃ i : KernelComponent (rootCharHom a),
        CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) ∧
          J.map ι = rationalComponent S.ρ S.Γ (rootCharHom a) i := by
  classical
  obtain ⟨h, hh, hβh, hh5, hh1⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.KD264Lie.ExcUntw.exists_inndiag_of_mem_innAutDerived_E
      (Or.inr (Or.inr rfl)) Nat.prime_five β hβmem hβ5 hβ1
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓ, hcardK⟩ := FiniteField.card K (ringChar K)
  have hKpow : Nat.card K = ringChar K ^ (f : ℕ) := by
    rw [Nat.card_eq_fintype_card]
    exact hcardK
  have h5K : ¬ 5 ∣ Nat.card K := by rw [hK]; norm_num
  have h5ℓ : 5 ≠ ringChar K := fun h' =>
    h5K (by rw [hKpow, ← h']; exact dvd_pow_self 5 f.ne_zero)
  obtain ⟨p₀, hp₀, hp₀ℓ, hq₀⟩ := exists_setup_prime hℓ f.pos Nat.prime_five (by norm_num) h5ℓ
  have hp₀K : ¬ p₀ ∣ Nat.card K := fun hd =>
    hp₀ℓ ((Nat.prime_dvd_prime_iff_eq hp₀ hℓ).1 (hp₀.dvd_of_dvd_pow (hKpow ▸ hd)))
  have hq₀' : 5 ≤ p₀ ∨ 4 ≤ Nat.card K := by rw [hKpow]; exact hq₀
  have hmon : MonomialToralAt Tag.E8 5 :=
    monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five (by simp)
      Nat.prime_five (by norm_num)
  have hperf : commutator ↥(adjointGroup Tag.E8 K) = ⊤ :=
    single_edge_perfect Tag.E8 K (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  obtain ⟨S, a, ι, hSq, ⟨Fr, hFr1, hFr2⟩, hT, hap, h1, hinj, hrange, hconj⟩ :=
    exists_langSetup_of_inner_untw_of_prime (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
      Nat.prime_five h5K hp₀ hp₀K hq₀' hmon hperf β h
      (baseChange_mem_adjointGroup_of_mem_inndiag hh) hβh hh5 hh1
  have h5L : ((5 : ℕ) : AlgebraicClosure K) ≠ 0 :=
    CFSG.HardMathSupport.Timmesfeld.Torality.natCast_ne_zero_of_ringChar_ne Nat.prime_five
      (by rw [ringChar_algebraicClosure K]; exact h5ℓ.symm)
  have hTame := langSetup_hTame_of_prime S Nat.prime_five h5L
    (fun hτ => absurd hτ (by decide)) hT hap h1
  obtain ⟨i, hqs, hJR⟩ :=
    components_of_langSetup S Nat.prime_five ι hinj hrange β hconj hT hap h1 hTame hJ
  have hfix : (fixSubgroup β).map ι =
      S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E8 a} := by
    rw [map_fixSubgroup_eq_of_conj ι hinj β (rootDiagUnit Tag.E8 a) hconj, hrange]
  exact ⟨p₀, S, a, ι, ⟨Fr, fun c => by rw [hSq]; exact hFr1 c, hFr2⟩,
    by rw [hSq, hK], hT, hap, h1, hinj, hrange, hfix, i, hqs, hJR⟩

theorem noD4CompAt_adjointGroup (hres : E8TwoFiveRatNotD4) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) : NoD4CompAt ↥(adjointGroup Tag.E8 K) := by
  classical
  intro β hβmem hβ5 hβ1 J hJ
  obtain ⟨p₀, S, a, ι, ⟨Fr, hFr, hFr2⟩, hq2, hT, hap, h1, hinj, hrange, -, i, hqs, hJR⟩ :=
    exists_langSetup_component_E8Two hK β hβmem hβ5 hβ1 hJ
  have hR := hres (AlgebraicClosure K) p₀ S ⟨Fr, hFr, hFr2⟩ hq2 a hT hap h1 i hqs
  let eJ : ↥J ≃* ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
    (J.equivMapOfInjective ι hinj).trans (MulEquiv.subgroupCongr hJR)
  exact fun hJc => hR ((Nat.card_congr
    (CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsL33.centerQuotCongr eJ).toEquiv).symm.trans
      hJc)

theorem e8TwoNoD4Comp_of_rat (hres : E8TwoFiveRatNotD4) : Claims1110n.E8TwoNoD4Comp := by
  classical
  rintro ⟨e, hv⟩ hd β hβ5 hβ1 T hT
  obtain ⟨q, hq, hq2⟩ := hd
  subst hq
  obtain ⟨K, _, _, hKq, -, ⟨eK⟩⟩ :=
    CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup
      (τ := Tag.E8) CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8 q hv
  have hK : Nat.card K = 2 := by rw [hKq, hq2]
  have hβmem : β ∈ innAutDerived (TauCeti.CFSGIndex.lie ⟨.E8 q, hv⟩).Group :=
    (CFSG.ComponentClassification.OuterAutomorphisms.mem_innAutDerived_congr eK).1
      (inner_le_innAutDerived ↥(adjointGroup Tag.E8 K)
        (mem_range_conj_adjoint_E7_E8 (Or.inr rfl) hK (MulAut.congr eK β)))
  exact noD4CompAt_of_mulEquiv eK.symm (noD4CompAt_adjointGroup hres hK)
    β hβmem hβ5 hβ1 T hT

end Adjoint

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1110o
