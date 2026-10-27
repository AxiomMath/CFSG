module

public import CFSG.HardMathSupport.Dickson.Sec6.UpD42Aux.InnExcRank
public import CFSG.HardMathSupport.Dickson.Sec6.UpD42Aux.InnOrth
public import CFSG.HardMathSupport.Dickson.Sec6.UpD42Aux.InnClassical
public import CFSG.HardMathSupport.Dickson.KD.CharP
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.AssemblyExc
public import CFSG.LocalAnalysis.StandardType.GGCompListMarked
public import CFSG.LocalAnalysis.StandardType.GGE6TwoThreeComp
public import CFSG.LocalAnalysis.StandardType.GGE7TwoThreeComp
public import CFSG.LocalAnalysis.StandardType.GGE8TwoThreeComp
public import CFSG.LocalAnalysis.StandardType.GGF4TwoThree
public import CFSG.LocalAnalysis.StandardType.GGK0CompREMult
public import CFSG.LocalAnalysis.StandardType.GGK0ExcB3Holds
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.StandardType.GGTwistedF4DiagRaw
public import CFSG.LocalAnalysis.StandardType.GGReverseMarkingRaw
public import CFSG.GroupTheory.PCore.SubgroupCore
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.E7
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.E8
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossSp
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterIdxSymplectic
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotKleinThreePlus
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusEightInputs
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusEightInputsAniso
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusEightInputsAnisoCover
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusFiveCover

public section

namespace CFSG.StandardType.UpD42Inn

open CFSG CFSG.Assembly
open scoped commutatorElement

theorem three_dvd_two_pow_sub_one_or_add_one (n : ℕ) : 3 ∣ 2 ^ n - 1 ∨ 3 ∣ 2 ^ n + 1 := by
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | hn
  · left
    have h := Nat.sub_dvd_pow_sub_pow 4 1 k
    have h4 : (4 : ℕ) ^ k = 2 ^ (k + k) := by rw [← two_mul, pow_mul]; norm_num
    rw [one_pow, h4] at h
    exact h
  · right
    simpa using Odd.nat_add_dvd_pow_add_pow 2 1 hn

theorem ggKacRE_three {lab : LargeEvenLabel}
    (ht : lab.tag = .E6 ∨ lab.tag = .twE6 ∨ lab.tag = .E7 ∨ lab.tag = .E8 ∨ lab.tag = .F4) :
    GGKacRE lab 3 := by
  refine ⟨Nat.prime_three, by decide, three_dvd_two_pow_sub_one_or_add_one lab.n, ?_⟩
  rcases ht with h | h | h | h | h
  · exact Or.inr (Or.inl ⟨Or.inl h, Or.inl rfl⟩)
  · exact Or.inr (Or.inl ⟨Or.inr h, Or.inl rfl⟩)
  · exact Or.inr (Or.inr ⟨Or.inl h, Or.inl rfl⟩)
  · exact Or.inr (Or.inr ⟨Or.inr h, Or.inl rfl⟩)
  · exact Or.inl ⟨h, rfl⟩

theorem commutator_eq_top_of_simple {S : Type} [Group S] (hs : IsSimpleGroup S)
    (hnab : ∃ a b : S, a * b ≠ b * a) : commutator S = ⊤ := by
  rcases hs.eq_bot_or_eq_top_of_normal (commutator S) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    have hmem : ⁅a, b⁆ ∈ commutator S := by
      rw [commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h, Subgroup.mem_bot] at hmem
    exact hab (commutatorElement_eq_one_iff_mul_comm.mp hmem)
  · exact h

theorem k0_component_label {Gen : LargeEvenLabel → ℕ → Prop}
    {Valid : LargeEvenLabel → ℕ → GGKacDatum → Prop} (h : GGK0Comp Gen Valid)
    {lab : LargeEvenLabel} {p : ℕ} (hΛ : LargeEvenInLambda2 lab) (hgen : Gen lab p)
    {T : Type} [Group T] [Finite T] (hperf : commutator T = ⊤)
    {α : MulAut T} (hαp : α ^ p = 1)
    (hraw : LargeEvenRawDatum lab fun R _ I _ =>
      ∃ θ : T ⧸ Subgroup.center T ≃* R, ∃ β ∈ I,
        LargeEvenInduces θ (fun x y => y = α x) β)
    {K : Subgroup T} (hK : IsComponentOf K (ggFixSub α)) :
    ∃ labK : LargeEvenLabel, lab.n ∣ labK.n ∧ LargeEvenInLambda2 labK ∧
      GGHasLabel labK (↥K ⧸ Subgroup.center ↥K) := by
  obtain ⟨R, _, I, F, ⟨θ, β, hβ, hind⟩, hK0⟩ :=
    largeEvenRawDatum_exists (h p lab hΛ hgen _ hraw)
  let π : T →* R := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center T))
  have hπ : Function.Surjective π :=
    θ.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center T))
  have hker : π.ker ≤ Subgroup.center T := by
    intro x hx
    have hx' : θ (QuotientGroup.mk' (Subgroup.center T) x) = 1 := hx
    have hx'' : QuotientGroup.mk' (Subgroup.center T) x = 1 :=
      θ.injective (by simpa using hx')
    exact (QuotientGroup.eq_one_iff x).mp hx''
  obtain ⟨D, -, ha, -, -⟩ := hK0 T π hπ hker hperf α hαp ⟨β, hβ, fun x => hind x (α x) rfl⟩
  obtain ⟨o, -, -, hn, hΛo, hlab⟩ := ha K hK
  exact ⟨o.lab, hn, hΛo, hlab⟩

theorem eq_D41_of_ggLabelIso {lab : LargeEvenLabel} (h : GGLabelIso lab ⟨.D, 4, 1⟩) :
    lab = ⟨.D, 4, 1⟩ := by
  simpa [GGLabelIso] using h

theorem ggHasLabel_D41_of_isD42 {X : Type} [Group X]
    (h : CFSG.HardMathSupport.Solomon.Coordinator.IsCatalogLieIso X
      CFSG.HardMathSupport.Dickson.Sec6.IsD42Index) :
    GGHasLabel ⟨.D, 4, 1⟩ X := by
  obtain ⟨hs, hnab⟩ := CFSG.HardMathSupport.Dickson.Sec6.isSimpleGroup_of_isD42Type h
  haveI := hs
  obtain ⟨lab, -, htag, hrank, -, hdeg, hraw⟩ := exists_label_rawDatum_of_lieModel
    (CFSG.HardMathSupport.Dickson.Sec6.center_eq_bot_of_isSimpleGroup_noncomm hnab)
    (CFSG.HardMathSupport.Dickson.Sec6.lieModel_of_isD42 h)
  have hlab : lab = ⟨.D, 4, 1⟩ := by
    clear hraw
    rcases lab with ⟨tag, rank, n⟩
    cases tag <;> simp_all [markTag, markRank, markDeg]
    all_goals split_ifs at htag hrank <;> simp_all
  subst hlab
  exact hraw

theorem eq_of_markTag_exc {lab : LargeEvenLabel} {tag : LargeEvenLieTag}
    {t : CFSG.Open.StatedLieTag} {f : ℕ}
    (ht : (tag = .E6 ∧ t = .E6) ∨ (tag = .twE6 ∧ t = .twistedE6) ∨ (tag = .E7 ∧ t = .E7) ∨
      (tag = .E8 ∧ t = .E8) ∨ (tag = .F4 ∧ t = .F4))
    (hΛ : LargeEvenInLambda2 lab) (htag : markTag lab = t) (hdeg : markDeg lab = f) :
    lab = ⟨tag, 0, f⟩ := by
  rcases lab with ⟨tag', rank, n⟩
  rcases ht with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    cases tag' <;> simp_all [markTag, markDeg, LargeEvenInLambda2]
  all_goals split_ifs at htag


theorem rawMarking_conj {S : Type} [Group S] [Finite S]
    (hs : IsSimpleGroup S) (hnab : ∃ a b : S, a * b ≠ b * a)
    {lab : LargeEvenLabel} (hΛ : LargeEvenInLambda2 lab)
    (hraw : LargeEvenRawDatum lab fun R _ _ _ => Nonempty (S ≃* R)) (x : S) :
    LargeEvenRawDatum lab fun R _ I _ =>
      ∃ θ : S ⧸ Subgroup.center S ≃* R, ∃ β ∈ I,
        LargeEvenInduces θ (fun a b => b = MulAut.conj x a) β := by
  haveI := hs
  have hZ : Subgroup.center S = ⊥ :=
    CFSG.HardMathSupport.Dickson.Sec6.center_eq_bot_of_isSimpleGroup_noncomm hnab
  apply largeEvenRawDatum_mono _
    (ggRawInnFieldInput_holds 3 Nat.prime_three (by decide) lab hΛ _ hraw)
  rintro R _ I F ⟨⟨eR⟩, hI⟩
  haveI : IsSimpleGroup R := eR.symm.isSimpleGroup
  have hnabR : ∃ a b : R, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    exact ⟨eR a, eR b, fun h => hab (eR.injective (by rw [map_mul, map_mul, h]))⟩
  refine ⟨(CFSG.SeitzReduction.quotientCenterMulEquiv hZ).trans eR,
    MulAut.conj (((CFSG.SeitzReduction.quotientCenterMulEquiv hZ).trans eR)
      (QuotientGroup.mk x)), (hI inferInstance hnabR).2.2.1 _, ?_⟩
  intro a b hb
  subst hb
  simp [MulAut.conj_apply]

theorem field_eq_one_of_D41_component {S : Type} [Group S] [Finite S]
    (hs : IsSimpleGroup S) (hnab : ∃ a b : S, a * b ≠ b * a)
    {lab : LargeEvenLabel} (hΛ : LargeEvenInLambda2 lab) (hRE : GGKacRE lab 3)
    {α : MulAut S}
    (hmark : LargeEvenRawDatum lab fun R _ I _ =>
      ∃ θ : S ⧸ Subgroup.center S ≃* R, ∃ β ∈ I,
        LargeEvenInduces θ (fun a b => b = α a) β)
    (hα3 : α ^ 3 = 1) {K : Subgroup S} (hK : IsComponentOf K (ggFixSub α))
    (hD : GGHasLabel ⟨.D, 4, 1⟩ (↥K ⧸ Subgroup.center ↥K)) : lab.n = 1 := by
  obtain ⟨labK, hn, hΛK, hlabK⟩ := k0_component_label (Gen := GGKacRE) (Valid := GGKacValid)
    (ggK0CompRE_of_mult (ggK0CompREMult_of_excB GGK0ExcB3Prod.ggK0ExcB3_holds.toB2.toExcB))
    hΛ hRE (commutator_eq_top_of_simple hs hnab) hα3 hmark hK
  have hiso := ggLabelRigidInput_holds labK ⟨.D, 4, 1⟩ _ hΛK (by simp [LargeEvenInLambda2])
    hlabK hD
  rw [eq_D41_of_ggLabelIso hiso] at hn
  exact Nat.dvd_one.mp hn

theorem false_of_D41_component_list {S : Type} [Group S] [Finite S]
    (hs : IsSimpleGroup S) (hnab : ∃ a b : S, a * b ≠ b * a)
    {lab : LargeEvenLabel} {L : List LargeEvenLabel} (hlist : GGCompList lab 3 (· ∈ L))
    (hL : ∀ l ∈ L, LargeEvenInLambda2 l ∧ l ≠ ⟨.D, 4, 1⟩) {α : MulAut S}
    (hmark : LargeEvenRawDatum lab fun R _ I _ =>
      ∃ θ : S ⧸ Subgroup.center S ≃* R, ∃ β ∈ I,
        LargeEvenInduces θ (fun a b => b = α a) β)
    (hα3 : α ^ 3 = 1) (hα1 : α ≠ 1) {K : Subgroup S} (hK : IsComponentOf K (ggFixSub α))
    (hD : GGHasLabel ⟨.D, 4, 1⟩ (↥K ⧸ Subgroup.center ↥K)) : False := by
  obtain ⟨labK, hmem, hlabel⟩ := GGCompList.of_rawMarking hlist
    (commutator_eq_top_of_simple hs hnab) hα3 hα1 hmark hK
  obtain ⟨hΛK, hne⟩ := hL labK hmem
  exact hne (eq_D41_of_ggLabelIso (ggLabelRigidInput_holds labK ⟨.D, 4, 1⟩ _ hΛK
    (by simp [LargeEvenInLambda2]) hlabel hD))

theorem exc_field_two {S : Type} [Group S] [Finite S]
    (hs : IsSimpleGroup S) (hnab : ∃ a b : S, a * b ≠ b * a)
    {tag : LargeEvenLieTag} {t : CFSG.Open.StatedLieTag} {f : ℕ}
    (ht : (tag = .E6 ∧ t = .E6) ∨ (tag = .twE6 ∧ t = .twistedE6) ∨ (tag = .E7 ∧ t = .E7) ∨
      (tag = .E8 ∧ t = .E8) ∨ (tag = .F4 ∧ t = .F4))
    (hm : CFSG.Blueprint.LieModel S t 0 2 f) {x : S} (hα3 : MulAut.conj x ^ 3 = 1)
    {K : Subgroup S} (hK : IsComponentOf K (ggFixSub (MulAut.conj x)))
    (hD : GGHasLabel ⟨.D, 4, 1⟩ (↥K ⧸ Subgroup.center ↥K)) :
    f = 1 ∧ LargeEvenInLambda2 ⟨tag, 0, 1⟩ ∧
      LargeEvenRawDatum ⟨tag, 0, 1⟩ fun R _ _ _ => Nonempty (S ≃* R) := by
  haveI := hs
  obtain ⟨lab, hΛ, htag, -, -, hdeg, hraw⟩ := exists_label_rawDatum_of_lieModel
    (CFSG.HardMathSupport.Dickson.Sec6.center_eq_bot_of_isSimpleGroup_noncomm hnab) hm
  have htag' : tag = .E6 ∨ tag = .twE6 ∨ tag = .E7 ∨ tag = .E8 ∨ tag = .F4 := by
    rcases ht with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]
  have hlab : lab = ⟨tag, 0, f⟩ := eq_of_markTag_exc ht hΛ htag hdeg
  subst hlab
  have hf : f = 1 :=
    field_eq_one_of_D41_component hs hnab hΛ (ggKacRE_three htag')
      (rawMarking_conj hs hnab hΛ hraw x) hα3 hK hD
  subst hf
  exact ⟨rfl, hΛ, hraw⟩

end CFSG.StandardType.UpD42Inn

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Open CFSG.Blueprint CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple


theorem exists_D41_component_of_upD42Pumpup {S : Type} [Group S] [Finite S]
    (hs : IsSimpleGroup S) (hnab : ∃ a b : S, a * b ≠ b * a) (d : TauCeti.ValidLieTypeIndex)
    (hfam : CFSG.Yardstones.Md42047359a2a.lieFamily d.1 = .exceptional)
    (h3 : 3 ≠ d.1.characteristic) (he : Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group))
    {α : MulAut S} (hx : UpD42Pumpup S α) :
    ∃ K : Subgroup S, CFSG.Assembly.IsComponentOf K (CFSG.StandardType.ggFixSub α) ∧
      CFSG.StandardType.GGHasLabel ⟨.D, 4, 1⟩ (↥K ⧸ Subgroup.center ↥K) := by
  obtain ⟨hα3, hα1, I, hI, hD⟩ := hx
  have hPIL : PerfectInLayer α :=
    lieSemisimpleCentExceptional S hs hnab d hfam he 3 Nat.prime_three (by decide) h3 α hα3 hα1
  obtain ⟨hcomp, hDI⟩ := exists_component_of_isD42_two hPIL hI hD
  have hfix : CFSG.StandardType.ggFixSub α = fixSubgroup α := Subgroup.ext fun _ => Iff.rfl
  refine ⟨I, ?_, CFSG.StandardType.UpD42Inn.ggHasLabel_D41_of_isD42 hDI⟩
  rw [hfix]
  exact CFSG.Assembly.isComponentOf_iff_open.2 hcomp

theorem upD42_inner_exc_data {S : Type} [Group S] [Finite S] (hs : IsSimpleGroup S)
    (hnab : ∃ a b : S, a * b ≠ b * a) (d : TauCeti.ValidLieTypeIndex)
    (hfam : CFSG.Yardstones.Md42047359a2a.lieFamily d.1 = .exceptional)
    (h3 : 3 ≠ d.1.characteristic) (he : Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group))
    {tag : CFSG.Assembly.LargeEvenLieTag} {t : StatedLieTag} {f : ℕ}
    (ht : (tag = .E6 ∧ t = .E6) ∨ (tag = .twE6 ∧ t = .twistedE6) ∨ (tag = .E7 ∧ t = .E7) ∨
      (tag = .E8 ∧ t = .E8) ∨ (tag = .F4 ∧ t = .F4))
    (hm : CFSG.Blueprint.LieModel S t 0 2 f) {x : S} (hx : UpD42Pumpup S (MulAut.conj x)) :
    f = 1 ∧ CFSG.Assembly.LargeEvenInLambda2 ⟨tag, 0, 1⟩ ∧
      CFSG.StandardType.LargeEvenRawDatum ⟨tag, 0, 1⟩ (fun R _ _ _ => Nonempty (S ≃* R)) ∧
      ∃ K : Subgroup S,
        CFSG.Assembly.IsComponentOf K (CFSG.StandardType.ggFixSub (MulAut.conj x)) ∧
          CFSG.StandardType.GGHasLabel ⟨.D, 4, 1⟩ (↥K ⧸ Subgroup.center ↥K) := by
  obtain ⟨I, hK, hL⟩ := exists_D41_component_of_upD42Pumpup hs hnab d hfam h3 he hx
  obtain ⟨hf, hΛ, hraw⟩ := CFSG.StandardType.UpD42Inn.exc_field_two hs hnab ht hm hx.1 hK hL
  exact ⟨hf, hΛ, hraw, I, hK, hL⟩

theorem upD42Chev2Inn_nonclassical_holds :
    UpD42Chev2Inn (fun d => ¬ CFSG.HardMathSupport.Dickson.KD.IsClassicalLieIndex d) := by
  intro S _ _ hs hnab ⟨d, hv⟩ hF hc ⟨e⟩ x hx
  have hα3 := hx.1
  have hα1 := hx.2.1
  cases d with
  | E6 q =>
    have hq : q.p = 2 := hc
    have hm := blueprintLieModel_E6 q hv e
    rw [hq] at hm
    obtain ⟨-, hΛ, hraw, K, hK, hD⟩ := upD42_inner_exc_data hs hnab ⟨.E6 q, hv⟩ rfl
      (by simpa using (show (3 : ℕ) ≠ q.p by omega)) ⟨e⟩ (Or.inl ⟨rfl, rfl⟩) hm hx
    exact (CFSG.StandardType.UpD42Inn.false_of_D41_component_list hs hnab
      CFSG.StandardType.E6TwoThree.ggE6TwoThreeComp_holds
      (by simp [CFSG.Assembly.LargeEvenInLambda2])
      (CFSG.StandardType.UpD42Inn.rawMarking_conj hs hnab hΛ hraw x) hα3 hα1 hK hD).elim
  | E7 q =>
    have hq : q.p = 2 := hc
    have hm := blueprintLieModel_E7 q hv e
    rw [hq] at hm
    obtain ⟨-, hΛ, hraw, K, hK, hD⟩ := upD42_inner_exc_data hs hnab ⟨.E7 q, hv⟩ rfl
      (by simpa using (show (3 : ℕ) ≠ q.p by omega)) ⟨e⟩
      (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))) hm hx
    exact (CFSG.StandardType.UpD42Inn.false_of_D41_component_list hs hnab
      CFSG.StandardType.E7TwoThree.ggE7TwoThreeComp_holds
      (by simp [CFSG.Assembly.LargeEvenInLambda2])
      (CFSG.StandardType.UpD42Inn.rawMarking_conj hs hnab hΛ hraw x) hα3 hα1 hK hD).elim
  | E8 q =>
    have hq : q.p = 2 := hc
    have hm := blueprintLieModel_E8 q hv e
    rw [hq] at hm
    obtain ⟨-, hΛ, hraw, K, hK, hD⟩ := upD42_inner_exc_data hs hnab ⟨.E8 q, hv⟩ rfl
      (by simpa using (show (3 : ℕ) ≠ q.p by omega)) ⟨e⟩
      (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))) hm hx
    exact (CFSG.StandardType.UpD42Inn.false_of_D41_component_list hs hnab
      CFSG.StandardType.E8TwoThree.ggE8TwoThreeComp_holds
      (by simp [CFSG.Assembly.LargeEvenInLambda2])
      (CFSG.StandardType.UpD42Inn.rawMarking_conj hs hnab hΛ hraw x) hα3 hα1 hK hD).elim
  | F4 q =>
    have hq : q.p = 2 := hc
    have hm := blueprintLieModel_F4 q hv e
    rw [hq] at hm
    obtain ⟨-, hΛ, hraw, K, hK, hD⟩ := upD42_inner_exc_data hs hnab ⟨.F4 q, hv⟩ rfl
      (by simpa using (show (3 : ℕ) ≠ q.p by omega)) ⟨e⟩
      (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))) hm hx
    exact (CFSG.StandardType.UpD42Inn.false_of_D41_component_list hs hnab
      CFSG.StandardType.ggF4TwoThreeComp_holds
      (by simp [CFSG.Assembly.LargeEvenInLambda2])
      (CFSG.StandardType.UpD42Inn.rawMarking_conj hs hnab hΛ hraw x) hα3 hα1 hK hD).elim
  | twistedE6 q =>
    have hq : q.p = 2 := hc
    have hm := blueprintLieModel_twistedE6 q hv e
    rw [hq] at hm
    obtain ⟨hf, -⟩ := upD42_inner_exc_data hs hnab ⟨.twistedE6 q, hv⟩ rfl
      (by simpa using (show (3 : ℕ) ≠ q.p by omega)) ⟨e⟩ (Or.inr (Or.inl ⟨rfl, rfl⟩)) hm hx
    exact Or.inr (Or.inl ⟨⟨.twistedE6 q, hv⟩, ⟨hq, hf⟩, ⟨e⟩⟩)
  | G2 q => exact upD42Chev2Inn_g2 S hs hnab ⟨.G2 q, hv⟩ trivial hc ⟨e⟩ x hx
  | trialityD4 q => exact upD42Chev2Inn_triD4 S hs hnab ⟨.trialityD4 q, hv⟩ trivial hc ⟨e⟩ x hx
  | suzuki m => exact upD42Chev2Inn_sz S hs hnab ⟨.suzuki m, hv⟩ trivial hc ⟨e⟩ x hx
  | reeG2 m => exact hc.elim
  | reeF4 m => exact upD42Chev2Inn_reeF4 S hs hnab ⟨.reeF4 m, hv⟩ trivial hc ⟨e⟩ x hx
  | tits => exact upD42Chev2Inn_tits S hs hnab ⟨.tits, hv⟩ trivial hc ⟨e⟩ x hx
  | _ => exact (hF trivial).elim

theorem upD42Chev2Inn_holds : UpD42Chev2Inn fun _ => True :=
  UpD42Chev2Inn.mono (fun d _ => Classical.em (CFSG.HardMathSupport.Dickson.KD.IsClassicalLieIndex d))
    (upD42Chev2Inn_classical_holds.union upD42Chev2Inn_nonclassical_holds)

end CFSG.HardMathSupport.Dickson.Sec6

end
