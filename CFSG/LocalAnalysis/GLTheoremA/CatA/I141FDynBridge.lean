module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.AssemblyAll
public import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.MultLie
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonInnBridge
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FDyn
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonSubcompIdx
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.Models.Blueprint

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I141F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.Y10F
open CFSG.LocalAnalysis.GLTheoremA.CanonSubcomp
open CFSG.LocalAnalysis.GLTheoremA.Y10GField
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.ComponentClassification.PerfectAutomorphisms
  (centerQuotientHom centerQuotientHom_injective)
open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut)
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

theorem innDiagKind_chevAut {G : Type} [Group G] {p : ℕ} {K : Subgroup G} {y : G}
    (hy : y ∈ Subgroup.normalizer (K : Set G)) (hq : CFSG.Open.IsQuasisimple (PQuot p K))
    (hInn : S10.InnDiagOn p (Subgroup.zpowers y) K) :
    ∃ labL : GLALabel, HasLabel (PQuot p K) (· = labL) ∧
      InnDiagKind (PSimple p K) labL (chevAut p K ⟨y, hy⟩) := by
  have hcen := center_centerQuot_eq_bot hq
  haveI : Group.IsPerfect (PQuot p K) := ⟨hq.1⟩
  have hS : commutator (PSimple p K) = ⊤ :=
    (Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (Subgroup.center (PQuot p K)))
      (QuotientGroup.mk'_surjective _)).commutator_eq_top
  obtain ⟨hX, labL, hlam, hraw⟩ := hInn.2
  refine ⟨labL, ⟨hX, labL, hlam, CFSG.StandardType.Canonical.largeEvenRawDatum_mono
    (fun _ _ _ _ ⟨hs, hna, θ, _⟩ => ⟨hs, hna, θ, rfl⟩) hraw⟩,
    hS, labL, hlam, CFSG.StandardType.Canonical.largeEvenRawDatum_mono ?_ hraw⟩
  rintro R _ I F ⟨hs, hna, θ, hall⟩
  obtain ⟨φ, hφ, hind⟩ := hall y⁻¹ (Subgroup.inv_mem _ (Subgroup.mem_zpowers y))
  refine ⟨hs, hna, (CFSG.LocalAnalysis.GLTheoremA.CanonInn.quotCenterEquivOfBot hcen).trans θ,
    rfl, φ, hφ, ?_⟩
  intro s s' hss'
  subst hss'
  obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective s
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply,
    CFSG.LocalAnalysis.GLTheoremA.CanonInn.quotCenterEquivOfBot_mk,
    CFSG.LocalAnalysis.GLTheoremA.CanonInn.quotCenterEquivOfBot_mk]
  have hc := chevAut_chevQuotHom p K ⟨y, hy⟩ k
  have hi := hind (QuotientGroup.mk k) (QuotientGroup.mk (K.normalizerMonoidHom ⟨y, hy⟩ k))
    ⟨k, K.normalizerMonoidHom ⟨y, hy⟩ k, rfl, rfl,
      by rw [chev_coe_normalizerMonoidHom, inv_inv]⟩
  exact hi.trans (congrArg θ hc.symm)

theorem chevAut_eq_one_iff_of_quasisimple {G : Type} [Group G] {p : ℕ} {K : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple (PQuot p K)) {a : G}
    (ha : a ∈ Subgroup.normalizer (K : Set G)) :
    chevAut p K ⟨a, ha⟩ = 1 ↔ CentMod p K a := by
  haveI : Group.IsPerfect (PQuot p K) := ⟨hq.1⟩
  rw [← chev_barAut_eq_one_iff_centMod ha]
  show centerQuotientHom (PQuot p K) (barAut p K ⟨a, ha⟩) = 1 ↔ _
  rw [← map_one (centerQuotientHom (PQuot p K))]
  exact (centerQuotientHom_injective (PQuot p K)).eq_iff

theorem centerQuot_equiv_pSimple {S : Type} [Group S] [Finite S] {p : ℕ}
    (hp : p.Prime) {X J : Subgroup S} (hJ : GLAPComponent p X J)
    (hq : CFSG.Open.IsQuasisimple ↥J) :
    Nonempty (↥J ⧸ Subgroup.center ↥J ≃* PSimple p J) := by
  have hQ := isQuasisimple_pQuot_of_glaPComponent hp hJ
  have hne : GLAPPrimeCore p ↥J ≠ ⊤ := by
    intro htop
    haveI : Nontrivial (PQuot p J) := isQuasisimple_nontrivial hQ
    haveI : Subsingleton (↥J ⧸ GLAPPrimeCore p ↥J) := by
      rw [htop]
      exact QuotientGroup.subsingleton_quotient_top
    exact not_subsingleton (PQuot p J) ‹_›
  have hle : GLAPPrimeCore p ↥J ≤ Subgroup.center ↥J :=
    le_center_of_normal_of_isQuasisimple hq inferInstance hne
  exact quotEquiv_of_perfect_central (QuotientGroup.mk' (GLAPPrimeCore p ↥J))
    (QuotientGroup.mk'_surjective _) ⟨hq.1⟩ (by rw [QuotientGroup.ker_mk']; exact hle)

section Bridge


theorem exists_sLevel_of_i141 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Γ : Type} [Group Γ] [Finite Γ] {L K A : Subgroup Γ} {y : Γ}
    (hlie : catalogIs (PSimple p L) isLie2NoTits) (hAel : IsElemAbelian p A)
    (hInn : S10.InnDiagOn p A L) (hyA : y ∈ A) (hyC : ¬ CentMod p L y)
    (hK : GLAPComponent p (L ⊓ Subgroup.centralizer ({y} : Set Γ)) K) :
    ∃ (labL : GLALabel) (β : MulAut (PSimple p L)) (J : Subgroup (PSimple p L)),
      HasLabel (PQuot p L) (· = labL) ∧
      Subgroup.center (PSimple p L) = ⊥ ∧
      InnDiagKind (PSimple p L) labL β ∧
      β ^ p = 1 ∧ β ≠ 1 ∧ CFSG.Open.IsComponentOf J (fixSubgroup β) ∧
      Nonempty (PSimple p K ≃* ↥J ⧸ Subgroup.center ↥J) := by
  have hyN : y ∈ Subgroup.normalizer (L : Set Γ) := hInn.1 hyA
  have hyp : y ^ p = 1 := hAel.2 y hyA
  have hap : IsPGroup p (Subgroup.zpowers y) := isPGroup_zpowers_of_pow_eq_one hyp
  have hInnZ : S10.InnDiagOn p (Subgroup.zpowers y) L := by
    refine ⟨fun z hz => hInn.1 (Subgroup.zpowers_le.mpr hyA hz), ?_⟩
    exact CFSG.StandardType.Canonical.largeEvenMarking_mono
      (fun _ _ _ _ _ _ hP a ha => hP a (Subgroup.zpowers_le.mpr hyA ha)) hInn.2
  have hlabAll : HasLabel (PQuot p L) (fun _ => True) :=
    CFSG.StandardType.Canonical.largeEvenMarking_mono
      (fun _ _ _ _ _ _ _ => trivial) hInn.2
  have hq : CFSG.Open.IsQuasisimple (PQuot p L) := hasLabel_isQuasisimple hlabAll
  obtain ⟨labL, hlab, hin⟩ := innDiagKind_chevAut hyN hq hInnZ
  have hcen : Subgroup.center (PSimple p L) = ⊥ := center_centerQuot_eq_bot hq
  have hβp : chevAut p L ⟨y, hyN⟩ ^ p = 1 := chevAut_pow_eq_one p L hyN hyp
  have hβ1 : chevAut p L ⟨y, hyN⟩ ≠ 1 := by
    intro h1
    exact hyC ((chevAut_eq_one_iff_of_quasisimple hq hyN).1 h1)
  have hJp : GLAPComponent p (fixSubgroup (chevAut p L ⟨y, hyN⟩)) (chevTransfer p L K) :=
    glaPComponent_chevTransfer hp hyN hap hK
  obtain ⟨i, hi, ⟨eS⟩⟩ := hlie
  cases i with
  | lie d =>
    simp only [isLie2NoTits, onLie] at hi
    have hchar : p ≠ d.1.characteristic := by rw [hi.1]; exact hp2
    have hsimple : IsSimpleGroup (PSimple p L) := hq.2
    have hnc : ∃ a b : PSimple p L, a * b ≠ b * a :=
      CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hq
    have hpil := lieSemisimpleCent (PSimple p L) hsimple hnc d ⟨eS⟩ p hp hp2 hchar
      (chevAut p L ⟨y, hyN⟩) hβp hβ1
    have hJle : chevTransfer p L K ≤ GLALayer (fixSubgroup (chevAut p L ⟨y, hyN⟩)) :=
      hpil _ hJp.1 (glaPComponent_perfect hJp)
    have hJc : CFSG.Open.IsComponentOf (chevTransfer p L K)
        (fixSubgroup (chevAut p L ⟨y, hyN⟩)) :=
      (glaPComponent_isComponent_of_le_layer hJp hJle).1
    obtain ⟨e₁⟩ := nonempty_pSimple_equiv_chevTransfer hp hyN hap hK
    obtain ⟨e₂⟩ := centerQuot_equiv_pSimple hp hJp hJc.2.2
    exact ⟨labL, chevAut p L ⟨y, hyN⟩, chevTransfer p L K, hlab, hcen, hin, hβp, hβ1, hJc,
      ⟨e₁.trans e₂.symm⟩⟩
  | _ => exact absurd hi (by simp [isLie2NoTits, onLie])

end Bridge

section Small

theorem card_eq_6048_of_isG2der {X : Type} [Group X] (h : catalogIs X isG2der) :
    Nat.card X = 6048 := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | lie d =>
    obtain ⟨idx, hv⟩ := d
    cases idx with
    | twistedA r q =>
      by_cases hr : r = 2
      · subst hr
        simp only [isG2der, onLie] at hi
        obtain ⟨hp3, hexp⟩ :=
          CFSG.LocalAnalysis.GLTheoremA.primePower_eq_of_card_eq (r := 3) (s := 1)
            Nat.prime_three (by norm_num) (by simpa using hi)
        have hM : CFSG.Models.LieModel X .PSU (2 + 1)
            (TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA 2 q, hv⟩)
            (TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA 2 q, hv⟩) :=
          CFSG.Models.lieModel_twistedA 2 q hv e
        have hc : TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA 2 q, hv⟩ = 3 :=
          (TauCeti.LieTypeIndex.characteristic_twistedA 2 q).trans hp3
        have hf : TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA 2 q, hv⟩ = 1 :=
          (TauCeti.LieTypeIndex.fieldExponent_twistedA 2 q).trans hexp
        rw [hc, hf] at hM
        norm_num at hM
        exact CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_three
          (CFSG.Models.LieModel.statedClassicalModel hM (by decide))
      · exact absurd hi (by simp [isG2der, onLie, hr])
    | _ => exact absurd hi (by simp [isG2der, onLie])
  | _ => exact absurd hi (by simp [isG2der, onLie])

end Small

section Quot


theorem catalogIs_isG2Quot_of_hasLabel_G2 {X : Type} [Group X] {lab : GLALabel}
    (h : HasLabel X (· = lab)) (ht : lab.tag = .G2) :
    catalogIs (X ⧸ Subgroup.center X) S10.isG2Quot := by
  obtain ⟨t, r, n⟩ := lab
  simp only at ht
  subst ht
  have hlam := lambda2_of_hasLabel h
  obtain ⟨-, rfl, hn2⟩ := hlam
  have hM := markedModel_of_hasLabel h
  have hLM : CFSG.Blueprint.LieModel (X ⧸ Subgroup.center X) .G2 0 2 n := hM
  have hce : CFSG.Blueprint.ChevalleyExceptionalModel (X ⧸ Subgroup.center X) .G2 2 n :=
    CFSG.GH74.chevalleyExceptionalModel_of_lieModel (by decide) hLM
  obtain ⟨hadm, hm⟩ := hce
  obtain ⟨K, hKfield, hKfin, hKcard, ⟨eK⟩⟩ := hm
  have hn0 : 0 < n := Nat.lt_of_lt_of_le (by norm_num) hn2
  let q : TauCeti.PrimePower := ⟨2, n, Nat.prime_two, hn0⟩
  have hq : q.card = 2 ^ n := TauCeti.PrimePower.card_def q
  have hv : (TauCeti.LieTypeIndex.G2 q).Valid := by
    refine (TauCeti.LieTypeIndex.valid_iff _).2 ⟨?_, ?_⟩
    · simpa [TauCeti.LieTypeIndex.inStandardRange_iff, hq] using hadm.2.2.2
    · simp [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
  obtain ⟨b⟩ := (CFSG.TauCetiBridge.Even.chevalleyBridgesAll).g2 q hv K (by rw [hKcard, hq])
  exact ⟨.lie ⟨.G2 q, hv⟩, by simp [S10.isG2Quot, onLie], ⟨eK.trans b⟩⟩

end Quot

end CFSG.LocalAnalysis.GLTheoremA.I141F
