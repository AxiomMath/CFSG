module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263CILift
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T2021LayerField
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T2021LayerOrder
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterLinear
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterUnitary
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterClassical
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterTriality
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterExc
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterExcTwisted
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263GSmall
public import CFSG.Quasithin.Vol2.Ch11SecOE5B
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10

section Generic


theorem t263CaseIx_of_exc {Q : TauCeti.CFSGIndex → Prop}
    (hQlie : ∀ i, Q i → ∃ (d : TauCeti.LieTypeIndex) (hd : d.Valid),
      i = TauCeti.CFSGIndex.lie ⟨d, hd⟩ ∧
        ∀ p : ℕ, KD264Lie.outerPLayerExc p d → p = 3 ∧ ∃ q, d = .trialityD4 q) :
    T263CaseIx Q := by
  intro p hp hp2 Ω _ _ hK S B hSn hSq hSp hSc hQ hF2 hSB hΩ hB h4 hT B₀ hB₀ hdich hCc hB₀c hBc b hb hbB₀ hfield
    hlay
  exfalso
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hBel : CFSG.Open.IsElemAbelian p B := hB.1
  have hbp : b ^ p = 1 := hBel.2 b hb
  have hbN : b ∈ Subgroup.normalizer (S : Set Ω) := t263_normalizer_of_normal hSn
  have hbN' : b⁻¹ ∈ Subgroup.normalizer (S : Set Ω) := Subgroup.inv_mem _ hbN
  have hcomp : GLAPComponent p S S := glaPComponent_self_p hSq hSp
  have e₆ : PSimple p S ≃* ↥S ⧸ Subgroup.center ↥S := pSimpleEquiv hSp
  have hchev : IsChevSimple 2 (PSimple p S) := by
    unfold IsChevSimple at hSc ⊢
    rcases hSc with h | h
    · exact Or.inl ((catalogIs_congr e₆).2 h)
    · exact Or.inr ((catalogIs_congr e₆).2 h)
  obtain ⟨x, hxB₀, hxC⟩ : ∃ x ∈ B₀, x ∉ B ⊓ Subgroup.centralizer (S : Set Ω) := by
    by_contra hcon
    push Not at hcon
    have hle : B₀ ≤ B ⊓ Subgroup.centralizer (S : Set Ω) := hcon
    have h1 := Subgroup.card_le_of_le hle
    rw [hB₀c, hCc] at h1
    have h2 : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    omega
  have hxB : x ∈ B := hB₀.1 hxB₀
  have hxC' : x ∉ Subgroup.centralizer (S : Set Ω) := fun h => hxC ⟨hxB, h⟩
  have hxp : x ^ p = 1 := hBel.2 x hxB
  have hxN : x ∈ Subgroup.normalizer (S : Set Ω) := t263_normalizer_of_normal hSn
  have hxN' : x⁻¹ ∈ Subgroup.normalizer (S : Set Ω) := Subgroup.inv_mem _ hxN
  have hInn : InnDiagOn p (Subgroup.zpowers x) S :=
    S10.innDiagOn_mono hB₀.2.1 (Subgroup.zpowers_le.2 hxB₀)
  set α := MI.indAut p S b hbN with hαdef
  set β := MI.indAut p S x hxN with hβdef
  have hαp : α ^ p = 1 := by
    show chevAut p S ⟨b⁻¹, hbN'⟩ ^ p = 1
    rw [← map_pow]
    have : (⟨b⁻¹, hbN'⟩ : ↥(Subgroup.normalizer (S : Set Ω))) ^ p = 1 :=
      Subtype.ext (by simp [inv_pow, hbp])
    rw [this, map_one]
  have hβp : β ^ p = 1 := by
    show chevAut p S ⟨x⁻¹, hxN'⟩ ^ p = 1
    rw [← map_pow]
    have : (⟨x⁻¹, hxN'⟩ : ↥(Subgroup.normalizer (S : Set Ω))) ^ p = 1 :=
      Subtype.ext (by simp [inv_pow, hxp])
    rw [this, map_one]
  have hβ1 : β ≠ 1 := by
    intro h1
    have h2 : chevAut p S ⟨x⁻¹, hxN'⟩ = 1 := h1
    have h3 := (chevAut_eq_one_iff hp hcomp hxN').1 h2
    exact hxC' (by simpa using Subgroup.inv_mem _ ((centMod_iff_centralizer hSp hxN').1 h3))
  have ha : GLAMarking (PQuot p S) fun lab _ _ I F θ =>
      GLAPrimeField p lab I F (· = MulAut.congr θ α) := by
    refine CFSG.StandardType.Canonical.largeEvenMarking_mono (fun lab R _ I F θ h => ?_) hfield.2
    obtain ⟨hne, f, hf, u, hu, hord, hind⟩ := h
    exact ⟨hne, f, hf, u, hu, hord, (MI.induces_indRel_iff hbN θ).1 hind⟩
  have hb' : GLAMarking (PQuot p S) fun _ _ _ I _ θ => MulAut.congr θ β ∈ I := by
    refine CFSG.StandardType.Canonical.largeEvenMarking_mono (fun lab R _ I F θ h => ?_) hInn.2
    obtain ⟨φ, hφ, hind⟩ := h x (Subgroup.mem_zpowers x)
    rw [(MI.induces_indRel_iff hxN θ).1 hind] at hφ
    exact hφ
  obtain ⟨hord, hnot⟩ := T2021.t2021Layer_not_mem hp hp2 ha
  have hαi : α ∉ (MulAut.conj : PSimple p S →* MulAut (PSimple p S)).range := fun h =>
    hnot (CFSG.ComponentClassification.OuterAutomorphisms.inner_le_innAutDerived _ h)
  obtain ⟨i, hi, ⟨e⟩⟩ := hQ
  obtain ⟨d, hd, rfl, hdexc⟩ := hQlie i hi
  have he : Nonempty (PSimple p S ≃* (TauCeti.CFSGIndex.lie ⟨d, hd⟩).Group) := ⟨e₆.trans e⟩
  have hexc : ¬ KD264Lie.outerPLayerExc p d := by
    intro h
    obtain ⟨hp3, q, hq⟩ := hdexc p h
    subst hq
    have hTD4 : IsTD4 p S := ⟨TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hd⟩, by simp [onLie], he⟩
    exact MI.td4_not_field_holds (hp3 ▸ hTD4 : IsTD4 3 S) (hp3 ▸ hfield : FieldOn 3 b S)
  have hdvd : p ∣ Nat.card (PSimple p S) := T2021.t2021Layer_dvd_card hp hp2 hβp hβ1 hb'
  have hL8 : ∀ (q : TauCeti.PrimePower) (hd' : (TauCeti.LieTypeIndex.A 1 q).Valid), q.card = 8 →
      ¬ (p = 3 ∧ Nonempty (PSimple p S ≃* (TauCeti.CFSGIndex.lie ⟨.A 1 q, hd'⟩).Group)) := by
    rintro q hd' hq8 ⟨-, ⟨e8⟩⟩
    exact t263Vac_l28 p hp hp2 Ω S B hSn hSq hSp
      ⟨TauCeti.CFSGIndex.lie ⟨.A 1 q, hd'⟩, hq8, ⟨e₆.symm.trans e8⟩⟩ hF2 hB h4 hT
      (by rw [hCc]; exact Nat.pow_lt_pow_right hp.one_lt (by norm_num))
  have hnc : ¬ IsChevSimple p (PSimple p S) := t263CI_not_chev hp hp2 hαp hαi hchev hL8
  have hlay' := KD264Lie.lieOuterPLayer_of_families (KD264Lie.lieOuterPLayer_linear p hp hp2)
      (KD264Lie.lieOuterPLayer_unitary p hp hp2) (KD264Lie.lieOuterPLayer_classicalBCD p hp hp2)
      (KD264Lie.lieOuterPLayer_triality p hp hp2) (KD264Lie.lieOuterPLayer_excUntwisted p hp hp2)
      (KD264Lie.lieOuterPLayer_excTwisted p hp hp2) d hd trivial hexc _ he hnc hdvd α hαp hnot
  obtain ⟨J, hJ⟩ := FR.exists_component_of_ne_bot _ hlay'
  have hJ' : GLAPComponent p (FP.fixSub α) J := hJ
  have hJperf : ⁅J, J⁆ = J := glaPComponent_perfect hJ'
  have hJ1 : J ≠ ⊥ := glaPComponent_ne_bot' hJ'
  obtain ⟨E, hEC, hEs, hEna, hperf, -, -⟩ :=
    T2021.t2021Layer_coreSub hp hp2 ha ⟨J, hJ'.1, hJperf, hJ1⟩
  have hJE : J = E := FR.eq_core_of_glaPComponent hEs hEC hperf hJ'
  have hpE : p ∣ Nat.card E :=
    hJE ▸ CFSG.HardMathSupport.Timmesfeld.ComponentBalance.i116pI_pcomp_card_dvd hp hJ'
  have hEperf : ⁅E, E⁆ = E := hJE ▸ hJperf
  have hEn : ∀ c ∈ FP.fixSub α, ∀ y ∈ E, c * y * c⁻¹ ∈ E := by
    intro c hc y hy
    have hle : E.map (MulAut.conj c).toMonoidHom ≤ E := by
      refine hperf _ ?_ (by rw [← Subgroup.map_commutator, hEperf])
      rintro _ ⟨z, hz, rfl⟩
      exact (FP.fixSub α).mul_mem ((FP.fixSub α).mul_mem hc (hEC hz)) ((FP.fixSub α).inv_mem hc)
    exact hle ⟨y, hy, rfl⟩
  haveI := hEs
  exact t263CI_layer_ne_bot_of_core hp hp2 hSp hbN hbp hEna hEC hEn hpE hlay

end Generic

end CFSG.LocalAnalysis.GLTheoremA.T263

end
