module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma46dii
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitBlowupOdd
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitFrontier46b

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools
open scoped commutatorElement

theorem le_of_lieModel_psl_two {Y : Type} [Group Y] {p n : ℕ}
    (hm : Blueprint.LieModel Y .PSL 2 p n) (hp2 : p ≠ 2) : (if p = 3 then 2 else 1) ≤ n := by
  obtain ⟨hn, h5⟩ := TBLit.lieModel_psl_two_params hm hp2
  split_ifs with h3
  · subst h3
    rcases n with _ | _ | n
    · omega
    · norm_num at h5
    · omega
  · exact hn

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ}

namespace Standing.Setup42

variable {h : Standing t L p f} {S : Subgroup X} {hS : IsSylowOf 2 S (centralizer ({t} : Set X))}
  {w z : X}

theorem center_KBar_quotient_eq_bot (hFC : AutPSL2FieldCentralizerInput)
    (hKC : AutPSL2CentralizerInput) (hσ : Setup42 h hS w z) (i j : ℕ) :
    center (↥(KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⧸
      pPrimeCore 2 ↥(KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j))) = ⊥ := by
  obtain ⟨eK⟩ := nonempty_KBar_quotient_equiv L (w ^ (orderOf w / 2) * t ^ i * z ^ j)
  have hm := GSThmB.OddQuot.lieModel_of_equiv eK.symm (hσ.lieModel_bar_K hFC hKC i j)
  have := isSimpleGroup_of_lieModel_psl2 hm
  exact (LocalCores.isQuasisimple_of_isSimpleGroup (nonabelian_of_lieModel_psl2 hm)).2

theorem pPrimeCore_KBar_eq_bot_of_ne (hσ : Setup42 h hS w z) (i j : ℕ) :
    ∀ K₀ : Subgroup (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)), IsComponent K₀ →
      K₀.map (MulAut.conj (hσ.tBar i j)).toMonoidHom ≠ K₀ →
      KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j) =
        centralizerResidual (K₀ ⊔ K₀.map (MulAut.conj (hσ.tBar i j)).toMonoidHom)
          (hσ.tBar i j) →
      IsLemma46eOdd L (w ^ (orderOf w / 2) * t ^ i * z ^ j) := by
  intro K₀ hK₀ hne hKb
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO : pPrimeCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) = ⊥ :=
    pPrimeCore_quotient_pPrimeCore_eq_bot 2
  have htb2 : hσ.tBar i j ^ 2 = 1 := by
    have := pow_orderOf_eq_one (hσ.tBar i j)
    rwa [hσ.orderOf_tBar i j] at this
  have hc := le_centralizer_map_conj_of_isComponent hK₀ hne
  have hKbφ := hKb.trans (centralizerResidual_sup_eq_range K₀ htb2 hc hK₀.1.1)
  have hO₀ : pPrimeCore 2 ↥K₀ = ⊥ := pPrimeCore_eq_bot_of_isSubnormal hO hK₀.2
  have hOR := pPrimeCore_eq_bot_of_surjective_of_isQuasisimple hK₀.1
    (isPGroup_center_of_pPrimeCore_eq_bot hO₀) _ (swapDiag K₀ _ hc).rangeRestrict_surjective
  unfold IsLemma46eOdd
  rw [← pPrimeCore_map_iso 2 (MulEquiv.subgroupCongr hKbφ.symm), hOR, Subgroup.map_bot]

theorem isLemma46d_eOdd_of_eq [IsSimpleGroup X] (hnonab : ∃ a b : X, a * b ≠ b * a)
    (hK : Assembly.KProper Blueprint.Catalog X)
    (hSch : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput)
    (h34 : Harris81Lemma34Input) (hσ : Setup42 h hS w z) (i j : ℕ) :
    ∀ K₀ : Subgroup (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)), IsComponent K₀ →
      K₀.map (MulAut.conj (hσ.tBar i j)).toMonoidHom = K₀ →
      IsTwoComponentIn (KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j))
        (K₀ ⊓ centralizer {hσ.tBar i j}) →
      K₀ ⊔ K₀.map (MulAut.conj (hσ.tBar i j)).toMonoidHom =
        layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) →
      IsLemma46d p f L (w ^ (orderOf w / 2) * t ^ i * z ^ j) (hσ.tBar i j) ∧
        IsLemma46eOdd L (w ^ (orderOf w / 2) * t ^ i * z ^ j) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set β := w ^ (orderOf w / 2) * t ^ i * z ^ j with hβ
  set tb := hσ.tBar i j with htb
  intro K₀ hK₀ hinv hKbK hE
  have hEK₀ : layer (MBar β) = K₀ := by rw [← hE, hinv, sup_idem]
  have hO : pPrimeCore 2 (MBar β) = ⊥ := pPrimeCore_quotient_pPrimeCore_eq_bot 2
  have hEn : (layer (MBar β)).Normal := by
    have := LocalCores.layer_characteristic (G := MBar β)
    infer_instance
  have hEq : IsQuasisimple ↥(layer (MBar β)) := hEK₀ ▸ hK₀.1
  have hOE : pPrimeCore 2 ↥(layer (MBar β)) = ⊥ :=
    pPrimeCore_eq_bot_of_isSubnormal hO hEn.isSubnormal
  have hZE := isPGroup_center_of_pPrimeCore_eq_bot hOE
  have hKbE : IsTwoComponentIn (KBar L β) (layer (MBar β) ⊓ centralizer {tb}) := hEK₀ ▸ hKbK
  obtain ⟨eK⟩ := nonempty_KBar_quotient_equiv L β
  have hm := hσ.lieModel_bar_K hFC hKC i j
  have hm' := GSThmB.OddQuot.lieModel_of_equiv eK.symm hm
  have hKZ := hσ.center_KBar_quotient_eq_bot hFC hKC i j
  have : IsSimpleGroup (↥(KBar L β) ⧸ pPrimeCore 2 ↥(KBar L β)) :=
    isSimpleGroup_of_lieModel_psl2 hm'
  have hZstar : Open.fusionZStar ↥(KBar L β) = pPrimeCore 2 ↥(KBar L β) :=
    FooteLit.fusionZStar_eq_pPrimeCore _ (nonabelian_of_lieModel_psl2 hm')
  have eKb : ↥(KBar L β) ⧸ Open.fusionZStar ↥(KBar L β) ≃* Bar (centralizerResidual L β) :=
    (QuotientGroup.quotientMulEquivOfEq hZstar).trans eK
  have hbase : ∃ n : ℕ, (if p = 3 then 2 else 1) ≤ n ∧
      Blueprint.LieModel (Bar (centralizerResidual L β)) .PSL 2 p n :=
    ⟨f / 2, le_of_lieModel_psl_two hm h.config.ne_two, hm⟩
  have hTQ : IsTwoQuasisimple ↥(layer (MBar β)) :=
    ⟨hEq.1, LocalCores.isQuasisimple_of_mulEquiv (QuotientGroup.quotientBot.symm.trans
      (QuotientGroup.quotientMulEquivOfEq hOE.symm)) hEq⟩
  have htbo := hσ.orderOf_tBar i j
  have hT : zpowers tb ≤ normalizer (layer (MBar β) : Set (MBar β)) := fun x _ =>
    mem_normalizer_iff.mpr fun y => ⟨fun hy => hEn.conj_mem y hy x, fun hy => by
      have := hEn.conj_mem _ hy x⁻¹
      simpa [mul_assoc] using this⟩
  have hEK : layer (MBar β) ≤ centralizer ({tb} : Set (MBar β)) → layer (MBar β) ≤ KBar L β :=
    fun hEt => sSup_le fun J hJ => hσ.le_KBar_of_isComponent hFC hKC i j hJ
      ((le_sSup (s := {K : Subgroup (MBar β) | IsComponent K}) hJ : J ≤ layer (MBar β)).trans
        hEt)
  rcases commutator_eq_self_or_eq_bot_of_le_normalizer hT hEq with hτE | hτE
  ·
    have hKM := UnbalancedCorr.isKGroupCat_of_ne_top hK (hσ.centralizer_beta_ne_top hnonab i j)
    have hKMbar := GSThmB.OddQuot.isKGroupCat_of_surjective hKM _
      (QuotientGroup.mk'_surjective (pPrimeCore 2 ↥(centralizer ({β} : Set X))))
    have hcatY : Blueprint.Catalog (↥(layer (MBar β)) ⧸ center ↥(layer (MBar β))) :=
      hKMbar (layer (MBar β)) (center ↥(layer (MBar β))) hEq.2.1
    have hF : HarrisF p (↥(layer (MBar β)) ⧸ center ↥(layer (MBar β))) :=
      .blowup (.base hbase) hcatY (isBlowup_quotient_center hEq hZE htbo hτE hKbE hKZ ⟨eKb⟩)
    refine ⟨.inl ⟨hEq, hTQ, _, inferInstance, hF,
      ⟨QuotientGroup.quotientMulEquivOfEq (fusionZStar_eq_center_of_pPrimeCore_eq_bot hOE)⟩⟩, ?_⟩
    exact pPrimeCore_eq_bot_of_harris34 h34 hEq hZE htbo hτE hKbE hKZ h.config.prime
      h.config.ne_two hF ⟨p, f / 2, hm'⟩
  ·
    have hEt : layer (MBar β) ≤ centralizer ({tb} : Set (MBar β)) := fun x hx =>
      mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp
        (commutator_eq_bot_iff_le_centralizer.mp hτE hx) tb (mem_zpowers tb)).symm)
    have hEKb : layer (MBar β) = KBar L β :=
      le_antisymm (hEK hEt) (hσ.KBar_le_layer hnonab hK hSch hFC hKC i j)
    obtain ⟨eE⟩ := FooteLit.nonempty_quotient_fusionZStar_equiv (MulEquiv.subgroupCongr hEKb)
    refine ⟨.inl ⟨hEq, hTQ, _, inferInstance, .base hbase, ⟨eE.trans eKb⟩⟩, ?_⟩
    unfold IsLemma46eOdd
    rw [← hEKb]
    exact hOE

theorem isLemma46d_and_eOdd
    [IsSimpleGroup X] (hnonab : ∃ a b : X, a * b ≠ b * a)
    (hK : Assembly.KProper Blueprint.Catalog X) (hcat : ¬ Blueprint.Catalog X)
    (hSch : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput)
    (h219 : Harris82Lemma219Input) (hGA : TBLit.GriessMultipliersOdd)
    (hGC : TBLit.GriessMultipliersCentralCovers) (hCI : GSLit.ClassicalInvolutionInput)
    (h34 : Harris81Lemma34Input) (hσ : Setup42 h hS w z) (i j : ℕ)
    (hSD : (∀ R : Subgroup (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)),
        IsSylowOf 2 R (centralizer (KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j) :
          Set (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) →
        ∃ n : ℕ, 4 ≤ n ∧ Nonempty (↥R ≃* CFSG.Open.SemidihedralGroup n)) →
      ∀ J : Subgroup (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)), IsComponent J →
        J ≤ centralizer (KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j) :
          Set (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) →
        ⁅J, zpowers (hσ.tBar i j)⁆ ≠ J) :
    IsLemma46d p f L (w ^ (orderOf w / 2) * t ^ i * z ^ j) (hσ.tBar i j) ∧
      IsLemma46eOdd L (w ^ (orderOf w / 2) * t ^ i * z ^ j) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h46c := hσ.isLemma46c_of hnonab hK hSch hFC hKC h219 i j hSD
  have hO : pPrimeCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) = ⊥ :=
    pPrimeCore_quotient_pPrimeCore_eq_bot 2
  obtain ⟨-, hc⟩ := h219 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) (hσ.tBar i j)
    (hσ.orderOf_tBar i j)
  obtain ⟨K₀, hK₀, hcases, -, hc2, -⟩ := hc _ (hσ.isTwoComponentIn_KBar hFC hKC i j)
  rw [twoLayer_eq_layer hO] at hc2
  have hK₀c : IsComponent K₀ := (isTwoComponent_iff_isComponent hO K₀).mp hK₀
  have hE : K₀ ⊔ K₀.map (MulAut.conj (hσ.tBar i j)).toMonoidHom =
      layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) := hc2.symm.trans h46c.2.1.symm
  rcases hcases with ⟨hinv, hKbK⟩ | ⟨hne, hKb⟩
  · exact hσ.isLemma46d_eOdd_of_eq hnonab hK hSch hFC hKC h34 i j K₀ hK₀c hinv hKbK hE
  · exact ⟨hσ.isLemma46d_of_ne hnonab hK hcat hSch hFC hKC hGA hGC hCI i j K₀ hK₀c hne hKb hE,
      hσ.pPrimeCore_KBar_eq_bot_of_ne i j K₀ hK₀c hne hKb⟩

end Standing.Setup42

theorem harris46d_of
    (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput)
    (hSch : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (h219 : Harris82Lemma219Input) (hSD : Harris46SemidihedralInput)
    (hGA : TBLit.GriessMultipliersOdd) (hGC : TBLit.GriessMultipliersCentralCovers)
    (hCI : GSLit.ClassicalInvolutionInput) (h34 : Harris81Lemma34Input) : Harris46dInput := by
  intro X _ _ _ hnonab hK hcat t L p f S w z V i j hs i' j'
  exact (hs.setup.isLemma46d_and_eOdd hnonab hK hcat hSch hFC hKC h219 hGA hGC hCI h34 i' j'
    (hSD X hnonab hK hcat t L p f S w z V i j hs i' j')).1

theorem harris46eOdd_of
    (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput)
    (hSch : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (h219 : Harris82Lemma219Input) (hSD : Harris46SemidihedralInput)
    (hGA : TBLit.GriessMultipliersOdd) (hGC : TBLit.GriessMultipliersCentralCovers)
    (hCI : GSLit.ClassicalInvolutionInput) (h34 : Harris81Lemma34Input) : Harris46eOddInput := by
  intro X _ _ _ hnonab hK hcat t L p f S w z V i j hs i' j'
  exact (hs.setup.isLemma46d_and_eOdd hnonab hK hcat hSch hFC hKC h219 hGA hGC hCI h34 i' j'
    (hSD X hnonab hK hcat t L p f S w z V i j hs i' j')).2

theorem harris46d'_of
    (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput)
    (hSch : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (h219 : Harris82Lemma219Input) (hSD : Harris46SemidihedralInput)
    (hGA : TBLit.GriessMultipliersOdd) (hGC : TBLit.GriessMultipliersCentralCovers)
    (hCI : GSLit.ClassicalInvolutionInput) (h34 : Harris81Lemma34Input) : Harris46dInput' :=
  fun X _ _ _ hnonab hK hcat t L p f S w z V i j hs i' j' _ =>
    harris46d_of hFC hKC hSch h219 hSD hGA hGC hCI h34 X hnonab hK hcat t L p f S w z V i j hs i' j'

end CFSG.ComponentClassification.HarrisLit
