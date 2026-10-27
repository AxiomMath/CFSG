module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1116c
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.InputsL33

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsL33

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple PSimple PQuot catalogIs onLie ambiguousChev)

set_option linter.unusedSectionVars false

section Statements

@[expose] def NoL33CompOn (P : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ idx : TauCeti.ValidLieTypeIndex, P idx.1 → idx.1.characteristic = 3 →
      idx.1.fieldOrder ≠ 3 → Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group) →
        ∀ α : MulAut S, α ^ 13 = 1 → α ≠ 1 → ∀ K : Subgroup S, IsComponentOf K (fixSubgroup α) →
          ¬ IsLpType 3 3 (↥K ⧸ Subgroup.center ↥K)

@[expose] def NoL33CompSympOrth : Prop :=
  NoL33CompOn fun d => CFSG.Yardstones.Md42047359a2a.lieFamily d = .symplecticOrthogonal

@[expose] def NoL33CompExc : Prop :=
  NoL33CompOn fun d => CFSG.Yardstones.Md42047359a2a.lieFamily d = .exceptional

@[expose] def SimpleL33DownThree : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    IsChevSimple 3 S → ∀ α : MulAut S, α ^ 13 = 1 →
      ∀ I : Subgroup S, GLAPComponent 13 (fixSubgroup α) I → IsLpType 3 3 (PSimple 13 I) →
        IsLpType 3 (3 ^ 13) S ∨ Prop1116Design.IsLieOverField 3 S

end Statements

section General

theorem fixSubgroup_one {K : Type*} [Group K] : fixSubgroup (1 : MulAut K) = ⊤ := by
  ext x
  rw [mem_fixSubgroup]
  simp

theorem fixSub_eq_fixSubgroup {K : Type} [Group K] (x : MulAut K) :
    Lemma1314.fixSub x = fixSubgroup x := by
  ext y
  exact Iff.rfl

theorem lieIndexChar_eq_characteristic (d : TauCeti.LieTypeIndex) :
    CFSG.HardMathSupport.Solomon.Coordinator.lieIndexChar d = d.characteristic := by
  cases d <;> simp [CFSG.HardMathSupport.Solomon.Coordinator.lieIndexChar]

theorem card_pSimple_dvd {S : Type} [Group S] (p : ℕ) (I : Subgroup S) :
    Nat.card (PSimple p I) ∣ Nat.card S :=
  (Subgroup.card_quotient_dvd_card _).trans
    ((Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_subgroup_dvd_card I))

theorem isLieOverField_three_of_isLpType {T : Type} [Group T] (hZ : Subgroup.center T = ⊥)
    (h : IsLpType 3 3 T) : Prop1116Design.IsLieOverField 3 T := by
  obtain ⟨F, hF, hFin, hc, ⟨f⟩⟩ := h
  haveI : Fact (3 : ℕ).Prime := ⟨Nat.prime_three⟩
  haveI : Fact Claims1116c.pp3.p.Prime := ⟨Claims1116c.pp3.prime_p⟩
  have hc' : Nat.card F = 3 ^ 1 := by rw [hc]; norm_num
  let eK := CFSG.ClassicalModels.statedLinearModelEquivGaloisPSL F 3 3 1 (by norm_num) hc'
  let eC := CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 Claims1116c.pp3
    Claims1116c.valid_A_two_pp3
  refine ⟨⟨.A 2 Claims1116c.pp3, Claims1116c.valid_A_two_pp3⟩,
    ⟨(((Prop1116Design.mulEquivQuotCenterOfEqBot hZ).symm.trans f).trans eK).trans eC.symm⟩, ?_⟩
  show (TauCeti.LieTypeIndex.A 2 Claims1116c.pp3).fieldOrder = 3
  rw [TauCeti.LieTypeIndex.fieldOrder_A, TauCeti.PrimePower.card_def]
  rfl

theorem component_of_glaPComponent {p : ℕ} (hp : p.Prime) {S : Type} [Group S] [Finite S]
    {α : MulAut S} (hlayer : CFSG.HardMathSupport.Solomon.Coordinator.PerfectInLayer α)
    {J : Subgroup S} (hJ : GLAPComponent p (fixSubgroup α) J) :
    IsComponentOf J (fixSubgroup α) ∧ Nonempty ((↥J ⧸ Subgroup.center ↥J) ≃* PSimple p J) := by
  have hperf : ⁅J, J⁆ = J := glaPComponent_perfect hJ
  have hle : J ≤ GLALayer (fixSubgroup α) := hlayer J hJ.1 hperf
  obtain ⟨hcomp, -⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.glaPComponent_isComponent_of_le_layer hJ hle
  refine ⟨hcomp, ?_⟩
  have hq : CFSG.Open.IsQuasisimple (PQuot p J) :=
    CFSG.LocalAnalysis.GLTheoremA.isQuasisimple_pQuot_of_glaPComponent hp hJ
  have hO : GLAPPrimeCore p ↥J ≤ Subgroup.center ↥J := by
    by_cases htop : GLAPPrimeCore p ↥J = ⊤
    · exfalso
      haveI := CFSG.LocalAnalysis.GLTheoremA.isQuasisimple_nontrivial hq
      obtain ⟨a, b, hab⟩ := exists_pair_ne (PQuot p J)
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
      exact hab (QuotientGroup.eq.2 (htop ▸ Subgroup.mem_top _))
    · exact CFSG.LocalAnalysis.GLTheoremA.le_center_of_normal_of_isQuasisimple hcomp.2.2
        inferInstance htop
  let π : ↥J →* PQuot p J := QuotientGroup.mk' (GLAPPrimeCore p ↥J)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hπk : π.ker ≤ Subgroup.center ↥J := by
    rw [QuotientGroup.ker_mk']
    exact hO
  exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.nonempty_centralQuotient_mulEquiv
    hcomp.2.2.1 π hπ hπk

theorem not_sixteen_dvd_orderRee (m : ℕ) : ¬ 16 ∣ CFSG.Open.orderRee (3 ^ (2 * m + 1)) := by
  have hq : (3 ^ (2 * m + 1)) % 16 = 3 ∨ (3 ^ (2 * m + 1)) % 16 = 11 := by
    induction m with
    | zero => left; norm_num
    | succ m ih =>
      have h : 3 ^ (2 * (m + 1) + 1) = 9 * 3 ^ (2 * m + 1) := by ring
      rw [h, Nat.mul_mod]
      rcases ih with h3 | h3 <;> rw [h3] <;> norm_num
  have h1 : 1 ≤ 3 ^ (2 * m + 1) := Nat.one_le_pow _ _ (by norm_num)
  generalize 3 ^ (2 * m + 1) = q at hq h1 ⊢
  rw [← ZMod.natCast_eq_zero_iff, CFSG.Open.orderRee]
  push_cast [Nat.cast_sub h1]
  rw [← ZMod.natCast_mod q 16]
  rcases hq with h3 | h3 <;> rw [h3] <;> decide

end General

section Schur

theorem natCard_center_dvd {L X : Type} [Group L] [Group X] (hL : CFSG.IsQuasisimple L)
    (e : L ⧸ Subgroup.center L ≃* X) :
    Nat.card ↥(Subgroup.center L) ∣ Nat.card (CFSG.Open.griessHopfMultiplier X) := by
  let q := CFSG.RankThree.PerfectCover.centralQuotientMap e
  have hq : Function.Surjective q := CFSG.RankThree.PerfectCover.centralQuotientMap_surjective e
  have hk : q.ker = Subgroup.center L := CFSG.RankThree.PerfectCover.centralQuotientMap_ker e
  let : Group.IsPerfect L := hL.1
  let ψ : CFSG.Open.griessHopfMultiplier X →* q.ker :=
    (CFSG.RankThree.PerfectCover.hopfMultiplierToKer q hq hk.le).comp
      (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess X).toMonoidHom
  have hψ : Function.Surjective ψ :=
    (CFSG.RankThree.PerfectCover.hopfMultiplierToKer_surjective q hq hk.le).comp
      (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess X).surjective
  have h := Subgroup.card_dvd_of_surjective hψ
  rw [hk] at h
  exact h

theorem center_eq_bot_of_l3 {Y : Type} [Group Y] (hq : CFSG.Open.IsQuasisimple Y)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = 3 ^ 13)
    (e : Y ⧸ Subgroup.center Y ≃* StatedProj (StatedSL 3 F)) : Subgroup.center Y = ⊥ := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  have hF5 : 5 ≤ Fintype.card F := by
    rw [Fintype.card_eq_nat_card, hF]
    norm_num
  obtain ⟨-, ⟨eM⟩⟩ :=
    CFSG.LieType.Steinberg.CentralExt.SLClosed.psl_hopfMultiplier (k := F) (n := 3) le_rfl hF5
  let e' : Y ⧸ Subgroup.center Y ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) F :=
    e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 F).symm
  have hq' : CFSG.IsQuasisimple Y :=
    ⟨⟨hq.1⟩, hq.2, Prop1116Design.not_isCommutative_barQuot Y hq⟩
  have hdvd := natCard_center_dvd hq' e'
  have hM : Nat.card (CFSG.Open.griessHopfMultiplier
      (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F)) = 1 := by
    rw [Nat.card_congr eM.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod,
      Fintype.card_eq_nat_card, hF]
    norm_num
  rw [hM, Nat.dvd_one] at hdvd
  exact Subgroup.eq_bot_of_card_eq _ hdvd

end Schur

section Reduction

theorem inputL33DownThree_of_simple (h : SimpleL33DownThree) : Claims1116c.InputL33DownThree := by
  intro Y _ _ hq hO hchev β hβ _ I hI hL33
  have hp13 : (13 : ℕ).Prime := by norm_num
  haveI := Inputs1315.hol_finite Y
  set a : Inputs1315.Hol Y := SemidirectProduct.inr β with ha
  have hKc : GLAPComponent 13 (Inputs1315.Kin Y) (Inputs1315.Kin Y) :=
    Inputs1315.kin_component hq hO
  obtain ⟨eS⟩ := Inputs1315.pSimple_kin_equiv (K := Y) hO
  have hnorm : a ∈ Subgroup.normalizer
      ((Inputs1315.Kin Y : Subgroup (Inputs1315.Hol Y)) : Set (Inputs1315.Hol Y)) := by
    have hN : (Inputs1315.Kin Y).Normal := by
      rw [Inputs1315.Kin, SemidirectProduct.range_inl_eq_ker_rightHom]
      exact MonoidHom.normal_ker _
    haveI := hN
    rw [Subgroup.normalizer_eq_top (Inputs1315.Kin Y)]
    exact Subgroup.mem_top _
  have hap : a ^ 13 = 1 := by rw [ha, ← map_pow, hβ, map_one]
  have hL : GLAPComponent 13
      (Inputs1315.Kin Y ⊓ Subgroup.centralizer ({a} : Set (Inputs1315.Hol Y)))
      (I.map (SemidirectProduct.inl : Y →* Inputs1315.Hol Y)) := by
    rw [ha, Inputs1315.kin_inf_centralizer]
    refine glaPComponent_map hp13 _ ?_ ?_
    · rw [(MonoidHom.ker_eq_bot_iff _).2
        (SemidirectProduct.inl_injective (φ := MonoidHom.id (MulAut Y))), inf_bot_eq,
        Subgroup.card_bot]
      exact Nat.coprime_one_right 13
    · rw [fixSub_eq_fixSubgroup]
      exact hI
  have hap' : IsPGroup 13 (Subgroup.zpowers a) :=
    CFSG.LocalAnalysis.GLTheoremA.isPGroup_zpowers_of_pow_eq_one hap
  obtain ⟨hsS, hnaS⟩ := CFSG.LocalAnalysis.GLTheoremA.chev_pSimple_simple_nonabelian hp13 hKc
  have hchevS : IsChevSimple 3 (PSimple 13 (Inputs1315.Kin Y)) :=
    Lemma1315b.isChevSimple_of_equiv eS hchev
  have hα := CFSG.LocalAnalysis.GLTheoremA.chevAut_pow_eq_one 13 (Inputs1315.Kin Y) hnorm hap
  have hI' := CFSG.LocalAnalysis.GLTheoremA.glaPComponent_chevTransfer hp13 hnorm hap' hL
  obtain ⟨eI⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.nonempty_pSimple_equiv_chevTransfer hp13 hnorm hap' hL
  let e1 : ↥(I.map (SemidirectProduct.inl : Y →* Inputs1315.Hol Y)) ≃* ↥I :=
    (Subgroup.equivMapOfInjective I _
      (SemidirectProduct.inl_injective (φ := MonoidHom.id (MulAut Y)))).symm
  let eJ : PSimple 13 (I.map (SemidirectProduct.inl : Y →* Inputs1315.Hol Y)) ≃* PSimple 13 I :=
    Lemma1315b.centerQuotEquiv (Lemma1315b.barCongr 13 e1)
  have hLS := isLpType_of_mulEquiv (eI.symm.trans eJ) hL33
  rcases h _ hsS hnaS hchevS _ hα _ hI' hLS with hS | hS
  · left
    obtain ⟨F, _, _, hF, ⟨f⟩⟩ := hS
    let eY : Y ⧸ Subgroup.center Y ≃* StatedProj (StatedSL 3 F) := eS.symm.trans f
    have hZ : Subgroup.center Y = ⊥ := center_eq_bot_of_l3 hq hF eY
    exact ⟨F, inferInstance, inferInstance, hF,
      ⟨(Prop1116Design.mulEquivQuotCenterOfEqBot hZ).trans eY⟩⟩
  · right
    obtain ⟨idx, ⟨g⟩, hfo⟩ := hS
    haveI := hsS
    have hZS := CFSG.LocalAnalysis.GLTheoremA.chev_center_eq_bot_of_simple_nonabelian hnaS
    exact ⟨idx, ⟨(eS.symm.trans (Prop1116Design.mulEquivQuotCenterOfEqBot hZS)).trans g⟩, hfo⟩

end Reduction

section Cert

theorem false_of_ambig {S : Type} [Group S] [Finite S] (h : catalogIs S (ambiguousChev 3))
    (h5616 : 5616 ∣ Nat.card S) : False := by
  have hO := CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
  rcases CrossCharOdd.ambig_cases (r := 3) (by norm_num) h with ⟨-, h35⟩ | ⟨⟨e⟩, -⟩ |
    ⟨-, -, -, hM | hM⟩
  · norm_num at h35
  · rw [Nat.card_congr e.toEquiv, Claims1116c.card_alt 6 (by norm_num)] at h5616
    revert h5616
    decide
  · have h1 := (hO S _ _ _ _ (CFSG.Blueprint.LieModel.admissible hM) hM).2.1
    simp [CFSG.ComponentClassification.CatLeaf.lieOrderNumerator,
      CFSG.ComponentClassification.CatLeaf.lieOrderDivisor] at h1
    omega
  · have h1 := (hO S _ _ _ _ (CFSG.Blueprint.LieModel.admissible hM) hM).2.1
    have hn : CFSG.ComponentClassification.CatLeaf.lieOrderNumerator .PSU 4 (2 ^ 1) = 25920 := by
      decide
    have hd : CFSG.ComponentClassification.CatLeaf.lieOrderDivisor .PSU 4 (2 ^ 1) = 1 := by
      decide
    rw [hn, hd, mul_one] at h1
    rw [h1] at h5616
    revert h5616
    decide

theorem simpleL33DownThree_of_residual (hSO : NoL33CompSympOrth) (hE : NoL33CompExc) :
    SimpleL33DownThree := by
  intro S _ _ hs hna hchev α hα I hI hL
  have hp13 : (13 : ℕ).Prime := by norm_num
  have hZ : Subgroup.center S = ⊥ :=
    CFSG.LocalAnalysis.GLTheoremA.chev_center_eq_bot_of_simple_nonabelian hna
  have h5616 : 5616 ∣ Nat.card S := by
    rw [← card_of_isLpType_three_three hL]
    exact card_pSimple_dvd 13 I
  by_cases hα1 : α = 1
  · subst hα1
    have hI' : GLAPComponent 13 (⊤ : Subgroup S) I := by
      rwa [fixSubgroup_one] at hI
    obtain ⟨e⟩ := CFSG.LocalAnalysis.GLTheoremA.chevQ_pSimple_top_equiv hp13 hna hI'
    exact Or.inr (isLieOverField_three_of_isLpType hZ (isLpType_of_mulEquiv e.symm hL))
  rcases hchev with ⟨i, hi, ⟨e⟩⟩ | ⟨i, hi, ⟨e⟩⟩
  · cases i with
    | cyclic _ _ => exact hi.elim
    | alternating _ _ => exact hi.elim
    | sporadic _ => exact hi.elim
    | lie idx =>
      have hc3 : idx.1.characteristic = 3 := hi
      by_cases hfo : idx.1.fieldOrder = 3
      · exact Or.inr ⟨idx, ⟨(Prop1116Design.mulEquivQuotCenterOfEqBot hZ).symm.trans e⟩, hfo⟩
      have hexp := CFSG.LocalAnalysis.GLTheoremA.lieCompsOn_holds hp13 (by norm_num)
        (CFSG.Yardstones.Md42047359a2a.lieFamily idx.1) S hs hna idx rfl ⟨e⟩ α hα hα1
        (Or.inl (by rw [lieIndexChar_eq_characteristic, hc3]; norm_num))
      obtain ⟨hK, ⟨eK⟩⟩ := component_of_glaPComponent hp13 hexp.layer hI
      have hLK : IsLpType 3 3 (↥I ⧸ Subgroup.center ↥I) := isLpType_of_mulEquiv eK hL
      obtain ⟨d, hv⟩ := idx
      cases d with
      | A r q =>
        exact Or.inl (linear_l33 r q hv (by simpa using hc3) (by simpa using hfo) ⟨e⟩ hα hK hLK)
      | twistedA r q =>
        exact (unitary_l33_false r q hv (by simpa using hc3) ⟨e⟩ hα hK hLK).elim
      | B r q => exact (hSO S hs hna ⟨_, hv⟩ rfl hc3 hfo ⟨e⟩ α hα hα1 I hK hLK).elim
      | C r q => exact (hSO S hs hna ⟨_, hv⟩ rfl hc3 hfo ⟨e⟩ α hα hα1 I hK hLK).elim
      | D r q => exact (hSO S hs hna ⟨_, hv⟩ rfl hc3 hfo ⟨e⟩ α hα hα1 I hK hLK).elim
      | twistedD r q => exact (hSO S hs hna ⟨_, hv⟩ rfl hc3 hfo ⟨e⟩ α hα hα1 I hK hLK).elim
      | E6 q => exact (hE S hs hna ⟨_, hv⟩ rfl hc3 hfo ⟨e⟩ α hα hα1 I hK hLK).elim
      | E7 q => exact (hE S hs hna ⟨_, hv⟩ rfl hc3 hfo ⟨e⟩ α hα hα1 I hK hLK).elim
      | E8 q => exact (hE S hs hna ⟨_, hv⟩ rfl hc3 hfo ⟨e⟩ α hα hα1 I hK hLK).elim
      | F4 q => exact (hE S hs hna ⟨_, hv⟩ rfl hc3 hfo ⟨e⟩ α hα hα1 I hK hLK).elim
      | G2 q => exact (hE S hs hna ⟨_, hv⟩ rfl hc3 hfo ⟨e⟩ α hα hα1 I hK hLK).elim
      | twistedE6 q => exact (hE S hs hna ⟨_, hv⟩ rfl hc3 hfo ⟨e⟩ α hα hα1 I hK hLK).elim
      | trialityD4 q => exact (hE S hs hna ⟨_, hv⟩ rfl hc3 hfo ⟨e⟩ α hα hα1 I hK hLK).elim
      | suzuki m => exact absurd hc3 (by simp)
      | reeF4 m => exact absurd hc3 (by simp)
      | tits => exact absurd hc3 (by simp)
      | reeG2 m =>
        exfalso
        have hcard := CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds
          ⟨.reeG2 m, hv⟩ S ⟨e⟩
        apply not_sixteen_dvd_orderRee m
        have h16 : 16 ∣ Nat.card S := (by norm_num : (16 : ℕ) ∣ 5616).trans h5616
        rwa [hcard] at h16
  · exact (false_of_ambig ⟨i, hi, ⟨e⟩⟩ h5616).elim

theorem inputL33DownThree_of_residual (hSO : NoL33CompSympOrth) (hE : NoL33CompExc) :
    Claims1116c.InputL33DownThree :=
  inputL33DownThree_of_simple (simpleL33DownThree_of_residual hSO hE)

end Cert

@[expose] def NoL33CompRest : Prop := NoL33CompSympOrth ∧ NoL33CompExc

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsL33
