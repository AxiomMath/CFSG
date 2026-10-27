module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFiveG
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxNineE

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

theorem exists_pump_of_kernel (hPump : Sol78.AlternatingPumpUpInput)
    (hN1 : TwoGroupAltCoverExclusion) (h13 : Sol76T13.SolomonThm13Simple)
    (hML : Sol78.MaximalityLemmaInput) (hSch : SolAltLit.SchurAlternatingMultiplierInput)
    [Finite X] [IsSimpleGroup X] (hnab : ∃ a b : X, a * b ≠ b * a)
    (hKP : Assembly.KProper Blueprint.Catalog X)
    (hunb : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hnU : ¬ OutcomeLocal.UOutcome X) {t : X} {J : Subgroup X}
    (hpair : Sol78.IsSolomonPair t J 9) (θ : ↥J ⧸ pPrimeCore 2 ↥J ≃* alternatingGroup (Fin 9))
    {y : X} (hy : orderOf y = 2) (hyt : y * t = t * y)
    (hyK : y ∈ UnbalancedLayer.coreActionKernel J) :
    ∃ (M₁ : Subgroup X) (θ₁ : ↥M₁ ⧸ pPrimeCore 2 ↥M₁ ≃* alternatingGroup (Fin 9))
      (ρ₁ : ↥(normalizer (M₁ : Set X)) →* Perm (Fin 9)) (ε : Perm (Fin 9)),
      IsPermAction θ₁ ρ₁ ∧ ∃ hCy : centralizer ({y} : Set X) ≤ normalizer (M₁ : Set X),
        ∀ {g e₀ : X} (hgy : g ∈ centralizer ({y} : Set X)), g ∈ normalizer (J : Set X) →
          ∀ (he₀ : e₀ ∈ J), g * e₀⁻¹ ∈ UnbalancedLayer.coreActionKernel J →
            ρ₁ ⟨g, hCy hgy⟩ = ε * coreImage θ he₀ * ε⁻¹ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Cy : Subgroup X := centralizer ({y} : Set X) with hCydef
  set Ct : Subgroup X := centralizer ({t} : Set X) with hCtdef
  have ht : orderOf t = 2 := hpair.1.1
  have hy2 : y * y = 1 := by rw [← sq, ← hy, pow_orderOf_eq_one]
  have hy1 : y ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hy
    omega
  have hJC : J ≤ Ct := hpair.1.2.1
  have hJpc : IsPComponent 2 (J.subgroupOf Ct) := hpair.1.2.2.1
  have hJq : IsQuasisimple (↥J ⧸ pPrimeCore 2 ↥J) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 J Ct hJC).mp hJpc).2.2
  have hJsub : (J.subgroupOf Ct).IsSubnormal := hJpc.choose_spec.2.1
  have hE : zpowers y ≤ UnbalancedLayer.coreActionKernel J := zpowers_le.mpr hyK
  have hE2 : IsPGroup 2 (zpowers y) := isPGroup_zpowers_of_mul_self hy2
  have hyCt : y ∈ Ct := mem_centralizer_singleton_iff.mpr hyt
  have htCy : t ∈ Cy := mem_centralizer_singleton_iff.mpr hyt.symm
  have hEC : zpowers y ≤ Ct := zpowers_le.mpr hyCt
  have hCE : centralizer ((zpowers y : Subgroup X) : Set X) = Cy :=
    UnbalancedLayer.centralizer_zpowers_eq y
  have hT : zpowers y ≠ ⊥ := fun h => hy1 (zpowers_eq_bot.mp h)
  set J₁ := GSLit.fixedLayer J (zpowers y) with hJ₁def
  have hle := GSLit.fixedLayer_le_inf J (zpowers y)
  have hJ₁J : J₁ ≤ J := hle.trans inf_le_left
  obtain ⟨hsup, -⟩ := GSLit.fixedLayer_sup_pPrimeCore hJq hE hE2
  have hpc := GSLit.fixedLayer_isPComponent hJC hJsub hEC hE hE2 hJq
  rw [hCE] at hpc hle
  obtain ⟨θ₁', -⟩ := exists_coreQuot_of_sup hJ₁J hsup θ
  have hK : SectionRank.IsKGroupCat ↥Cy :=
    UnbalancedCorr.isKGroupCat_of_ne_top hKP (centralizer_ne_top_of_ne_one hnab hy1)
  have hTY : J₁ ≤ Cy ⊓ Ct := by
    rw [inf_comm]
    exact hle.trans (inf_le_inf_right _ hJC)
  have hTpc : IsPComponent 2 (J₁.subgroupOf (Cy ⊓ Ct)) := by
    rw [inf_comm]
    exact hpc
  obtain ⟨M₁, hM₁Y, hM₁pc, hJ₁M, -, htype⟩ :=
    pump_type_in hPump hK htCy ht hTY hTpc (by decide) (by norm_num) θ₁'
  have hex : ∀ (R : Subgroup X) (m : ℕ), Odd m → 9 ≤ m → R ≤ Cy →
      IsPComponent 2 (R.subgroupOf Cy) →
      Nonempty (↥R ⧸ Open.fusionZStar ↥R ≃* alternatingGroup (Fin m)) →
      Nonempty (↥R ⧸ pPrimeCore 2 ↥R ≃* alternatingGroup (Fin m)) := by
    intro R m hm hm9 hRY hRpc ⟨eR⟩
    have hRY' : R ≤ centralizer ((zpowers y : Subgroup X) : Set X) := by
      rw [hCE]
      exact hRY
    have hRpc' : IsPComponent 2 (R.subgroupOf (centralizer ((zpowers y : Subgroup X) : Set X))) :=
      by rw [hCE]; exact hRpc
    have hZ := hN1 X hnab hKP hunb hnU (zpowers y) m R hT hE2 hm hm9 hRY' hRpc' ⟨eR⟩
    exact ⟨(QuotientGroup.quotientMulEquivOfEq hZ.symm).trans eR⟩
  have hpairex : ∃ (t' : X) (J' : Subgroup X), SolAltLit.IsAltTwoComponent t' J' 9 :=
    ⟨t, J, hpair.1⟩
  have hCT : ∀ L : Subgroup X, L ≤ Cy → IsPComponent 2 (L.subgroupOf Cy) →
      FooteLit.IsTwoComponentIn L (centralizer ((zpowers y : Subgroup X) : Set X)) := by
    intro L hL hLpc
    rw [hCE]
    exact ⟨hL, hLpc⟩
  obtain ⟨hfixt, eM₁⟩ : M₁.map (MulAut.conj t).toMonoidHom = M₁ ∧
      Nonempty (↥M₁ ⧸ pPrimeCore 2 ↥M₁ ≃* alternatingGroup (Fin 9)) := by
    rcases htype with ⟨hfix, ⟨m', hm', hm'9, eM⟩ | ⟨h79, -⟩⟩ | ⟨hne, eM⟩
    · obtain ⟨eM'⟩ := hex M₁ m' hm' hm'9 hM₁Y hM₁pc eM
      have hle9 : m' ≤ 9 := hpair.2.2.2.1 y M₁ m' ⟨hy, hM₁Y, hM₁pc, ⟨eM'⟩⟩ hm'
      have h9 : m' = 9 := le_antisymm hle9 hm'9
      subst h9
      exact ⟨hfix, ⟨eM'⟩⟩
    · exact absurd h79 (by decide)
    · exfalso
      obtain ⟨eM'⟩ := hex M₁ 9 (by decide) le_rfl hM₁Y hM₁pc eM
      obtain ⟨hMtY, hMtpc⟩ := isPComponent_conj hM₁Y hM₁pc htCy
      have eMt : Nonempty (↥(M₁.map (MulAut.conj t).toMonoidHom) ⧸
          pPrimeCore 2 ↥(M₁.map (MulAut.conj t).toMonoidHom) ≃* alternatingGroup (Fin 9)) :=
        ⟨(Sol78.coreQuotCongr (M₁.equivMapOfInjective (MulAut.conj t).toMonoidHom
          (MulAut.conj t).injective)).symm.trans eM'⟩
      exact hne (Sol78H.eq_of_isTwoComponentIn_centralizer_alt h13 hML hSch hnab hKP hunb hnU
        hpair.2.1 hpair.2.2.1 hpairex hpair.2.2.2.1 hT hE2 (hCT _ hMtY hMtpc)
        (hCT _ hM₁Y hM₁pc) eMt ⟨eM'⟩)
  obtain ⟨θ₁⟩ := eM₁
  have hJ₁M₁ : J₁ ≤ M₁ := by
    have h1 := hJ₁M
    rwa [hfixt, sup_idem] at h1
  have hCyN : Cy ≤ normalizer (M₁ : Set X) := by
    have hN := Sol78H.normalizer_le_normalizer_of_isTwoComponentIn_centralizer_alt h13 hML hSch
      hnab hKP hunb hnU hpair.2.1 hpair.2.2.1 hpairex hpair.2.2.2.1 hT hE2
      (hCT _ hM₁Y hM₁pc) ⟨θ₁⟩
    intro g hg
    apply hN
    rw [mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    congr 1
    change g * y * g⁻¹ = y
    rw [mem_centralizer_singleton_iff] at hg
    rw [hg]
    group
  obtain ⟨ρ₁, hρ₁⟩ := exists_isPermAction (M := M₁) (by norm_num) (by norm_num) θ₁
  have hJ₁perf : ⁅J₁, J₁⁆ = J₁ := UnbalancedCorr.commutator_eq_of_isPComponent hTY hTpc
  have hJ₁q : Nontrivial (↥J₁ ⧸ pPrimeCore 2 ↥J₁) := by
    have : Nontrivial (alternatingGroup (Fin 9)) :=
      alternatingGroup.nontrivial_of_three_le_card (by rw [Nat.card_fin]; norm_num)
    exact θ₁'.toEquiv.nontrivial
  have hJ₁K : ¬ J₁ ≤ UnbalancedLayer.coreActionKernel M₁ :=
    not_le_coreActionKernel_of_le hJ₁M₁ hJ₁perf hJ₁q
  have hJ₁N : J₁ ≤ normalizer (M₁ : Set X) := fun z hz => le_normalizer (hJ₁M₁ hz)
  obtain ⟨hsurj, -⟩ := hρ₁.image_eq_of_le hJ₁N (by norm_num) θ₁' hJ₁perf hJ₁K
    (Q := (⊤ : Subgroup (alternatingGroup (Fin 9))).map (alternatingGroup (Fin 9)).subtype)
    (by rw [card_map_of_injective (alternatingGroup (Fin 9)).subtype_injective,
      Subgroup.card_top, nat_card_alternatingGroup, Nat.card_fin])
    (fun z hz => by
      have h1 : ρ₁ ⟨z, hJ₁N hz⟩ =
          (θ₁ ((⟨z, hJ₁M₁ hz⟩ : ↥M₁) : ↥M₁ ⧸ pPrimeCore 2 ↥M₁) : Perm (Fin 9)) :=
        hρ₁.apply_of_mem (by norm_num) ⟨z, hJ₁M₁ hz⟩
      rw [h1]
      exact ⟨_, mem_top _, rfl⟩)
  have hcov : ∀ b : alternatingGroup (Fin 9), ∃ x : ↥M₁, (x : X) ∈ J₁ ∧
      θ₁ (x : ↥M₁ ⧸ pPrimeCore 2 ↥M₁) = b := by
    intro b
    obtain ⟨z, hz, hzb⟩ := hsurj b ⟨b, mem_top _, rfl⟩
    refine ⟨⟨z, hJ₁M₁ hz⟩, hz, Subtype.ext ?_⟩
    rw [← hzb]
    exact (hρ₁.apply_of_mem (by norm_num) ⟨z, hJ₁M₁ hz⟩).symm
  have hsupM := sup_core_eq_of_cover θ₁ hJ₁M₁ hcov
  obtain ⟨ε, hε⟩ := hρ₁.exists_conj_of_cover (by norm_num) θ hJ₁J hsup hJ₁M₁ hsupM
  refine ⟨M₁, θ₁, ρ₁, ε, hρ₁, hCyN, fun {g e₀} hgy hgJ he₀ hge => ?_⟩
  have hgJ₁ : g ∈ normalizer (J₁ : Set X) :=
    mem_normalizer_fixedLayer hJq hE hE2 hgJ (mem_centralizer_singleton_iff.mp hgy)
  exact hε (hCyN hgy) hgJ₁ he₀ hge

end CFSG.ComponentClassification.SolMax
