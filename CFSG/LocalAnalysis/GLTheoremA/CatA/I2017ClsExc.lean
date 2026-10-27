module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2017ClsInn
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2017ClsExcRat
import CFSG.LocalAnalysis.GLTheoremA.CatA.T1428CensusLinearTransport
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal209TwoOuterIn

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2017Cls

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)


set_option linter.unusedSectionVars false

private theorem transport_a8 {T U : Type} [Group T] [Group U] (θ : T ≃* U) (β : MulAut T)
    (hβ3 : β ^ 3 = 1) (hβ1 : β ≠ 1) {J : Subgroup T}
    (hJc : CFSG.Open.IsComponentOf J (fixSubgroup β))
    (eJ : ↥J ⧸ Subgroup.center ↥J ≃* ↥(alternatingGroup (Fin 8))) :
    ∃ β' : MulAut U, β' ^ 3 = 1 ∧ β' ≠ 1 ∧ ∃ J' : Subgroup U,
      CFSG.Open.IsComponentOf J' (fixSubgroup β') ∧
        Nonempty (↥J' ⧸ Subgroup.center ↥J' ≃* ↥(alternatingGroup (Fin 8))) := by
  refine ⟨θ.symm.trans (β.trans θ), ?_, ?_, J.map θ.toMonoidHom, ?_, ?_⟩
  · have h3 := map_pow (MulAut.congr θ) β 3
    rw [hβ3, map_one] at h3
    exact h3.symm
  · intro h1
    apply hβ1
    exact (MulAut.congr θ).injective (by rw [map_one]; exact h1)
  · have hfix := CFSG.LocalAnalysis.GLTheoremA.map_fixSubgroup θ β
    have h1 := CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map θ hJc
    exact hfix ▸ h1
  · let eJK : ↥J ≃* ↥(J.map θ.toMonoidHom) := J.equivMapOfInjective θ.toMonoidHom θ.injective
    exact ⟨(QuotientGroup.congr _ _ eJK (Subgroup.map_center_eq eJK)).symm.trans eJ⟩

section Certs


private theorem exists_inndiag_untw_two {τ : Tag} (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) (β : MulAut ↥(adjointGroup τ K))
    (hβ3 : β ^ 3 = 1) (hβ1 : β ≠ 1) :
    ∃ h : ModGL τ K,
      baseChangeGL (algebraMap K (AlgebraicClosure K)) h ∈ adjointGroup τ (AlgebraicClosure K) ∧
        (∀ c : adjointGroup τ K, (β c : ModGL τ K) = h * c * h⁻¹) ∧ h ^ 3 = 1 ∧ h ≠ 1 := by
  classical
  have hσ1 : ∀ σ : K ≃+* K, σ = 1 := by
    intro σ
    have huniv : ({0, 1} : Set K) = Set.univ :=
      Set.eq_of_subset_of_ncard_le (Set.subset_univ _)
        (by rw [Set.ncard_univ, hK, Set.ncard_pair zero_ne_one])
    have h01 : ∀ c : K, c = 0 ∨ c = 1 := fun c => by
      have hc : c ∈ ({0, 1} : Set K) := by
        rw [huniv]
        exact Set.mem_univ c
      simpa using hc
    exact RingEquiv.ext fun c => by rcases h01 c with rfl | rfl <;> simp
  rcases hτ with hτ | hτ
  · rcases exists_field_or_inndiag_FG (Or.inl hτ) (fun h => by simp [hτ] at h) Nat.prime_three
        (by norm_num) β hβ3 hβ1 with ⟨σ, -, hσ, -⟩ | ⟨h, hh, hβ, hp1, hh1⟩
    · exact absurd (hσ1 σ) hσ
    · exact ⟨h, baseChange_mem_adjointGroup_of_mem_inndiag hh, hβ, hp1, hh1⟩
  · rcases exists_field_or_inndiag_E hτ Nat.prime_three (by norm_num) β hβ3 hβ1 with
        ⟨σ, -, hσ, -⟩ | ⟨h, hh, hβ, hp1, hh1⟩
    · exact absurd (hσ1 σ) hσ
    · exact ⟨h, baseChange_mem_adjointGroup_of_mem_inndiag hh, hβ, hp1, hh1⟩

private theorem untw_not_a8 {τ : Tag} (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hrat : ExcRatNoA8 τ) {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    (β : MulAut ↥(adjointGroup τ K)) (hβ3 : β ^ 3 = 1) (hβ1 : β ≠ 1)
    {J : Subgroup ↥(adjointGroup τ K)} (hJc : CFSG.Open.IsComponentOf J (fixSubgroup β))
    (eJ : ↥J ⧸ Subgroup.center ↥J ≃* ↥(alternatingGroup (Fin 8))) : False := by
  classical
  obtain ⟨h, hhL, hβ, hp1, hh1⟩ := exists_inndiag_untw_two hτ hK β hβ3 hβ1
  have hτ' : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
    rcases hτ with h | h | h | h <;> simp [h]
  have hτ2 : τ = .F4 ∨ τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
    rcases hτ with h | h | h | h <;> simp [h]
  have hτ3 : τ = .G2 ∨ τ = .F4 ∨ τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
    rcases hτ with h | h | h | h <;> simp [h]
  have hperf : commutator ↥(adjointGroup τ K) = ⊤ := single_edge_perfect τ K hτ2
  have h3K : ¬ 3 ∣ Nat.card K := by rw [hK]; norm_num
  have h5K : ¬ 5 ∣ Nat.card K := by rw [hK]; norm_num
  have hmon : MonomialToralAt τ 3 :=
    monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five hτ3 Nat.prime_three
      (by norm_num)
  obtain ⟨S, a, ι, hSq, -, hT, hap, h1, hinj, hrange, hconj⟩ :=
    exists_langSetup_of_inner_untw_of_prime hτ' Nat.prime_three h3K Nat.prime_five h5K
      (Or.inl le_rfl) hmon hperf β h hhL hβ hp1 hh1
  have h3L : ((3 : ℕ) : AlgebraicClosure K) ≠ 0 :=
    natCast_ne_zero_algebraicClosure Nat.prime_three h3K
  have hTame := langSetup_hTame_of_prime S Nat.prime_three h3L
    (fun h' => absurd h' (by rcases hτ with h | h | h | h <;> simp [h])) hT hap h1
  obtain ⟨i, hq, hJR⟩ := components_of_langSetup S Nat.prime_three ι hinj hrange β hconj hT hap
    h1 hTame hJc
  let eJR : ↥J ≃* ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
    (J.equivMapOfInjective ι hinj).trans (MulEquiv.subgroupCongr hJR)
  exact (hrat (AlgebraicClosure K) 5 S (hSq.trans hK) a hT hap h1 i hq).false
    ((QuotientGroup.congr _ _ eJR (Subgroup.map_center_eq eJR)).symm.trans eJ)

private theorem twE6_not_a8 {K : Type} [Field K] [Finite K] (σ : K ≃+* K) (hK : Nat.card K = 4)
    (hσ : ∀ c, σ c = c ^ 2) (α : MulAut ↥(twistedE6RootGroup K σ)) (hα3 : α ^ 3 = 1)
    (hα1 : α ≠ 1) {I : Subgroup ↥(twistedE6RootGroup K σ)}
    (hI : CFSG.Open.IsComponentOf I (fixSubgroup α))
    (eI : ↥I ⧸ Subgroup.center ↥I ≃* ↥(alternatingGroup (Fin 8))) : False := by
  classical
  have hK2 : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  have hσ2 : ∀ c, σ c = c ^ (2 ^ 1) := fun c => by rw [hσ]; norm_num
  have hmem : α ∈ (twistedE6InndiagConj K σ).range := by
    rw [range_twistedE6InndiagConj]
    exact Bal209TwoOuterInAux.mem_inn_sup_diag_of_pow_three hK σ hσ hα3
  obtain ⟨g, rfl⟩ := hmem
  have hg3 : g ^ 3 = 1 :=
    twistedE6InndiagConj_injective Nat.prime_two le_rfl hK2 σ hσ2
      (by rw [map_pow, hα3, map_one])
  have hg1 : g ≠ 1 := fun h' => hα1 (by rw [h', map_one])
  obtain ⟨p₀, hp₀, hp₀ℓ, hq₀⟩ :=
    exists_setup_prime Nat.prime_two le_rfl Nat.prime_three (by decide) (by decide)
  have hmon : MonomialToralAt Tag.E6 3 :=
    monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five (by simp)
      Nat.prime_three (by decide)
  obtain ⟨S, a, ι, hSq, -, hT, hap, h1, hinj, hrange, hconj⟩ :=
    exists_langSetup_of_inndiag_twE6_of_prime Nat.prime_two le_rfl hK2 σ hσ2 Nat.prime_three
      (by decide) hp₀ hp₀ℓ hq₀ hmon (twistedE6InndiagConj K σ g)
      (g : ModGL TwistTag.E6.tag K) g.2 (twistedE6InndiagConj_apply g)
      (by rw [← Subgroup.coe_pow, hg3]; rfl) (fun h' => hg1 (Subtype.ext h'))
  have hq2 : S.D.q = 2 := by rw [hSq]; norm_num
  have hpL : ((3 : ℕ) : AlgebraicClosure K) ≠ 0 :=
    natCast_ne_zero_algebraicClosure_of_ne Nat.prime_two Nat.prime_three hK2 (by decide)
  have hTame :=
    langSetup_hTame_of_prime S Nat.prime_three hpL (fun h' => absurd h' (by decide)) hT hap h1
  haveI : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  obtain ⟨i, hqi, hJR⟩ :=
    components_of_langSetup S Nat.prime_three ι hinj hrange (twistedE6InndiagConj K σ g)
      hconj hT hap h1 hTame hI
  let eJR : ↥I ≃* ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
    (I.equivMapOfInjective ι hinj).trans (MulEquiv.subgroupCongr hJR)
  exact (excRatNoA8_E6 (AlgebraicClosure K) p₀ S hq2 a hT hap h1 i hqi).false
    ((QuotientGroup.congr _ _ eJR (Subgroup.map_center_eq eJR)).symm.trans eI)

private theorem untwCat_not_a8 {τ : Tag} {c : TauCeti.PrimePower → TauCeti.LieTypeIndex}
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hrat : ExcRatNoA8 τ)
    (hB : CFSG.TauCetiBridge.Even.UntwistedBridgeAll τ c) (hv : (c gfTwoPP).Valid)
    (β : MulAut (TauCeti.CFSGIndex.lie ⟨c gfTwoPP, hv⟩).Group) (hβ3 : β ^ 3 = 1)
    (hβ1 : β ≠ 1) : ¬ HasA8Comp β := by
  rintro ⟨J, -, hJc, ⟨eJ⟩⟩
  obtain ⟨K, _, _, hK, -, ⟨θ⟩⟩ :=
    CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup hB gfTwoPP hv
  have hK2 : Nat.card K = 2 := by
    rw [hK, TauCeti.PrimePower.card_def]
    rfl
  obtain ⟨β', hβ'3, hβ'1, J', hJ', ⟨eJ'⟩⟩ := transport_a8 θ β hβ3 hβ1 hJc eJ
  exact untw_not_a8 hτ hrat hK2 β' hβ'3 hβ'1 hJ' eJ'

private theorem twE6Cat_not_a8 (hv : (TauCeti.LieTypeIndex.twistedE6 gfTwoPP).Valid)
    (β : MulAut (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.twistedE6 gfTwoPP, hv⟩).Group)
    (hβ3 : β ^ 3 = 1) (hβ1 : β ≠ 1) : ¬ HasA8Comp β := by
  rintro ⟨J, -, hJc, ⟨eJ⟩⟩
  obtain ⟨K, _, σ, hK, hσ, ⟨θ⟩⟩ :=
    CFSG.LieType.SeitzGeneration.exists_catEquiv_twistedE6 gfTwoPP hv
  have hK4 : Nat.card K = 4 := hK.trans rfl
  have hσ2 : ∀ c, σ c = c ^ 2 := hσ
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK4]; norm_num)
  obtain ⟨β', hβ'3, hβ'1, J', hJ', ⟨eJ'⟩⟩ := transport_a8 θ β hβ3 hβ1 hJc eJ
  exact twE6_not_a8 σ hK4 hσ2 β' hβ'3 hβ'1 hJ' eJ'

theorem excTwoNoA8_holds : ExcTwoNoA8 := by
  intro d hd
  obtain ⟨d₁, hv⟩ := d
  rcases hd with h | h | h | h | h
  · have hd₁ : d₁ = TauCeti.LieTypeIndex.E6 gfTwoPP := h
    subst hd₁
    intro _ _ β _ hβ3 hβ1
    exact untwCat_not_a8 (Or.inr (Or.inl rfl)) excRatNoA8_E6
      CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 hv β hβ3 hβ1
  · have hd₁ : d₁ = TauCeti.LieTypeIndex.E7 gfTwoPP := h
    subst hd₁
    intro _ _ β _ hβ3 hβ1
    exact untwCat_not_a8 (Or.inr (Or.inr (Or.inl rfl))) excRatNoA8_E7
      CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e7 hv β hβ3 hβ1
  · have hd₁ : d₁ = TauCeti.LieTypeIndex.E8 gfTwoPP := h
    subst hd₁
    intro _ _ β _ hβ3 hβ1
    exact untwCat_not_a8 (Or.inr (Or.inr (Or.inr rfl))) excRatNoA8_E8
      CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8 hv β hβ3 hβ1
  · have hd₁ : d₁ = TauCeti.LieTypeIndex.F4 gfTwoPP := h
    subst hd₁
    intro _ _ β _ hβ3 hβ1
    exact untwCat_not_a8 (Or.inl rfl) excRatNoA8_F4
      CFSG.TauCetiBridge.Even.chevalleyBridgesAll.f4 hv β hβ3 hβ1
  · have hd₁ : d₁ = TauCeti.LieTypeIndex.twistedE6 gfTwoPP := h
    subst hd₁
    intro _ _ β _ hβ3 hβ1
    exact twE6Cat_not_a8 hv β hβ3 hβ1

end Certs

end CFSG.LocalAnalysis.GLTheoremA.I2017Cls

end
