module

public import CFSG.ClassicalInvolution.Q3.Q3AMLY5Conj
public import CFSG.ClassicalInvolution.Q3.Q3AM289Nbr
public import CFSG.ClassicalInvolution.Q3.Q3T8B16C
public import CFSG.ClassicalInvolution.Q3.Q3T8B16B

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open scoped commutatorElement MatrixGroups

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Generic.DeltaClosure CFSG.ClassicalInvolution.Q3.Q3T8.AF
  CFSG.ClassicalInvolution.Balance.Bootstrap

section Vertex

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem hyp51At_of_vertexY [IsSimpleGroup G] (hinv : InvolDichSect)
    (h : Q3AM.E4SettingY Ω K J S R T W z t) (hlay : Q3AM.LayerE4 Ω K z)
    {Jc Jv : Subgroup G} {c v : G}
    (hJc : Jc ∈ omegaNbr Ω K) (hc : IsUniqueInvolution Jc c)
    (hJv : Jv ∈ omegaNbr Ω K) (hv : IsUniqueInvolution Jv v)
    {B : Subgroup G} (hB : CFSG.Open.IsElemAbelian 2 B) (hcB : c ∈ B) (hzB : z ∈ B)
    (hvB : v ∈ B) (hzc : z ≠ c) (hvc : v ≠ c) (hvz : v ≠ z) (hzvc : z * v ≠ c) :
    Hyp51At B c := by
  classical
  have hbad : BadStd8 Ω K J S R T W z t := h.bad
  have hs : Std8 Ω K J S R T W z t := hbad.std
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hΩU : HypOmegaModU (.sl2 3 1) Ω := hs.stand.modU
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  have hz : IsUniqueInvolution K z := hs.hz
  have hK : K ∈ Ω := hs.stand.mem
  have hz2 : z * z = 1 := hz.sq
  have hlayc : Q3AM.LayerE4 Ω Jc c := Q3AM.layerE4_of_mem hbad hlay hJc.1 hc
  have hKJc : K ∈ omegaNbr Ω Jc := Q3CL.T3.omegaNbr_symm l6_2 hΩ hK hJc.1 hJc
  have hKJv : K ∈ omegaNbr Ω Jv := Q3CL.T3.omegaNbr_symm l6_2 hΩ hK hJv.1 hJv
  set Y : Subgroup G := Q3AM.nbrLayer Ω Jc c with hYdef
  have hYC : Y ≤ Subgroup.centralizer ({c} : Set G) := Q3AM.nbrLayer_le_centralizer Ω Jc c
  have hKY : Q3NL.exactCore3 c K ≤ Y := Q3AM.exactCore3_le_nbrLayer hKJc
  obtain ⟨hsimple, hnab⟩ := Q3AM.layerE4_simple_of_mem hbad h.hint h.noTri hlay hJc.1 hc
  obtain ⟨D, hkind⟩ := Q3AM.exists_sysU_of_layerE4 hlayc
  have hcK : c ∈ trivialOnQuot K :=
    (xMem_of_omegaNbr hΩ hnt hc hKJc hz).trivialOnQuot3 hΩ hc.sq
  have hvt : v ∈ trivialOnQuot K :=
    (xMem_of_omegaNbr hΩ hnt hv hKJv hz).trivialOnQuot3 hΩ hv.sq
  have hKcls : IsClassicalMember3 K z := isClassicalMember3_of_uniqueInvolution hΩU hK hz
  have hc2 : IsPGroup 2 (Subgroup.zpowers c) :=
    isPGroup_zpowers_of_mul_self_eq_one hc.sq hc.ne_one
  have hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hB.1.is_comm.comm (⟨x, hx⟩ : B) ⟨y, hy⟩)
  have hzcomm : z * c = c * z := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hz hJc hc
  have hzC : z ∈ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hzcomm
  have hvC : v ∈ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm v hvB c hcB)
  have hzY : z ∈ Y := mem_nbrLayer_of_mem hKJc hz.mem hzcomm
  have hnorm : Subgroup.centralizer ({c} : Set G) ≤ Subgroup.normalizer (Y : Set G) :=
    hbad.centralizer_le_normalizer_nbrLayer hJc.1 hc
  have hCN : ∀ g ∈ Subgroup.centralizer ({c} : Set G), conjSub g Y = Y := fun g hg =>
    mem_normalizer_iff_conjSub_eq.mp (hnorm hg)
  have hcN : ∀ n ∈ Y, ⁅n, c⁆ ∈ oddCoreOf Y := by
    intro n hn
    have h1 : ⁅n, c⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_centralizer_singleton_iff.mp (hYC hn))
    rw [h1]
    exact (oddCoreOf Y).one_mem
  have hvK : ∀ x ∈ Q3NL.exactCore3 c K, ⁅v, x⁆ ∈ oddCoreOf Y := by
    intro x hx
    have h1 : ⁅v, x⁆ ∈ oddCoreOf (Q3NL.exactCore3 c K) :=
      (Q3NL.mem_trivialOnQuot_exactCore3 hKcls hc2 hcK hvt hvC).2 x hx
    exact Q3AM.oddCoreOf_le_of_card_image hKY
      (Q3AM.nbrLayer_exact_images hbad h.hint hJc.1 hc K hKJc)
      (Q3NL.isSectionMember3_exactCore3 hKcls hc2 hcK).nonempty_equiv h1
  have hvnorm : v ∈ Subgroup.normalizer (Y : Set G) := hnorm hvC
  have hznorm : z ∈ Subgroup.normalizer (Y : Set G) := Subgroup.le_normalizer hzY
  let β : MulAut (↥Y ⧸ classicalInvolutionOddCore ↥Y) := s26Act Y ⟨v, hvnorm⟩
  have hβ2 : β * β = 1 := by
    show s26Act Y ⟨v, hvnorm⟩ * s26Act Y ⟨v, hvnorm⟩ = 1
    rw [← map_mul]
    have : (⟨v, hvnorm⟩ : ↥(Subgroup.normalizer (Y : Set G))) * ⟨v, hvnorm⟩ = 1 :=
      Subtype.ext hv.sq
    rw [this, map_one]
  have hfix : ∀ x ∈ modOddIn Y (Q3NL.exactCore3 c K), β x = x := by
    rintro _ ⟨y, hy, rfl⟩
    exact s26Act_apply_eq_of_comm_mem Y ⟨v, hvnorm⟩ y (hvK _ (Subgroup.mem_subgroupOf.mp hy))
  have hKfam : modOddIn Y (Q3NL.exactCore3 c K) ∈ Q3AM.layerFam Ω Jc c :=
    Q3AM.modOddIn_mem_layerFam hKJc
  have hzL : IsUniqueInvolution (Q3NL.exactCore3 c K) z :=
    ⟨⟨hz.mem, Subgroup.mem_centralizer_singleton_iff.mpr hzcomm⟩, hz.ne_one, hz.sq,
      fun y hy hy2 => hz.unique y (Q3NL.exactCore3_le_left c K hy) hy2⟩
  have hdich := hinv _ _ D hkind _ hKfam _ (isUniqueInvolution_modOddIn hKY hzL) β hβ2 hfix
  have hQ := isComponent_modOdd hc.sq hCN hcN hsimple hnab hzY hzC hz2 hz.ne_one
  have hzQ := oddQuotMk_mem_modOdd hzY hzC
  rcases hdich with h1 | h1
  · have hvN' : ∀ n ∈ Y, ⁅v, n⁆ ∈ oddCoreOf Y := fun n hn =>
      s26_comm_mem_oddCore_of_act_eq_one Y ⟨v, hvnorm⟩ h1 hn
    exact hyp51At_of_vacuous_component hB hcB hc.ne_one hzB hz.ne_one hzc hzC hvB hv.ne_one hvc
      hvC hQ hzQ (centralizes_modOdd hCN hvC hvN')
  · have hzv1 : z * v ≠ 1 := fun h1 => hvz (by
      have : v = z⁻¹ := eq_inv_of_mul_eq_one_right h1
      rw [this]
      exact inv_eq_of_mul_eq_one_right hz2)
    have hzvC : z * v ∈ Subgroup.centralizer ({c} : Set G) := Subgroup.mul_mem _ hzC hvC
    have hzvnorm : z * v ∈ Subgroup.normalizer (Y : Set G) :=
      (Subgroup.normalizer (Y : Set G)).mul_mem hznorm hvnorm
    have hact : s26Act Y ⟨z, hznorm⟩ = MulAut.conj
        (((⟨z, hzY⟩ : ↥Y) : ↥Y ⧸ classicalInvolutionOddCore ↥Y)) := s26Act_eq_conj Y ⟨z, hzY⟩
    have h2 : s26Act Y ⟨z * v, hzvnorm⟩ = 1 := by
      have : (⟨z * v, hzvnorm⟩ : ↥(Subgroup.normalizer (Y : Set G))) =
          ⟨z, hznorm⟩ * ⟨v, hvnorm⟩ := rfl
      rw [this, map_mul]
      show s26Act Y ⟨z, hznorm⟩ * β = 1
      rw [h1, hact, ← map_mul]
      change MulAut.conj ((QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) (⟨z, hzY⟩ : ↥Y)) *
        (QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) (⟨z, hzY⟩ : ↥Y))) = 1
      rw [← map_mul]
      have : (⟨z, hzY⟩ : ↥Y) * ⟨z, hzY⟩ = 1 := Subtype.ext hz2
      rw [this, map_one, map_one]
    have hzvN' : ∀ n ∈ Y, ⁅z * v, n⁆ ∈ oddCoreOf Y := fun n hn =>
      s26_comm_mem_oddCore_of_act_eq_one Y ⟨z * v, hzvnorm⟩ h2 hn
    exact hyp51At_of_vacuous_component hB hcB hc.ne_one hzB hz.ne_one hzc hzC
      ((Subgroup.mul_mem _) hzB hvB) hzv1 hzvc hzvC hQ hzQ (centralizes_modOdd hCN hzvC hzvN')

theorem e3tY_of_dich (hinv : InvolDichSect) : Q3AM.VertexTLeafY := by
  intro G _ _ _ Ω K J S R T W z t h hlay s hs
  have hstd : Std8 Ω K J S R T W z t := h.bad.std
  have hΩ : HypOmegaMod Ω := hstd.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hstd.stand.trans hstd.noTwins hM
  have hz2 := hstd.hz.sq
  have ht2 := hstd.ht.sq
  have hzt : z * t = t * z := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hstd.hz hstd.hJ hstd.ht
  have hne : z ≠ t := fun e => by
    have : IsUniqueInvolution J z := e ▸ hstd.ht
    exact hstd.hJ.2.1 (hnt K hstd.stand.mem J ⟨hstd.hJ.1, z, hstd.hz, this⟩)
  obtain ⟨J₁, hJ₁, hv₁⟩ := hs.nbr₁
  obtain ⟨J₂, hJ₂, hv₂⟩ := hs.nbr₂
  have hB := T8T.isElemAbelian_closure_three hz2 ht2 hs.sq hzt hs.comm_z hs.comm_t
  have hzB : z ∈ Subgroup.closure ({z, t, s} : Set G) := Subgroup.subset_closure (by simp)
  have htB : t ∈ Subgroup.closure ({z, t, s} : Set G) := Subgroup.subset_closure (by simp)
  have hsB : s ∈ Subgroup.closure ({z, t, s} : Set G) := Subgroup.subset_closure (by simp)
  have hzcl : z ∈ Subgroup.closure ({z, t} : Set G) := Subgroup.subset_closure (by simp)
  have htcl : t ∈ Subgroup.closure ({z, t} : Set G) := Subgroup.subset_closure (by simp)
  have hszt : s ≠ z * t := fun e => hs.indep (e ▸ Subgroup.mul_mem _ hzcl htcl)
  have hsz : s ≠ z := fun e => hs.indep (e ▸ hzcl)
  have hst : s ≠ t := fun e => hs.indep (e ▸ htcl)
  have hz1 := hstd.hz.ne_one
  have ht1 := hstd.ht.ne_one
  refine ⟨?_, ?_, ?_⟩
  ·
    refine hyp51At_of_vertexY hinv h hlay hstd.hJ hstd.ht hJ₁ hv₁ hB htB hzB hsB hne hst hsz ?_
    intro e
    apply hs.indep
    have : s = z * t := by
      calc s = z⁻¹ * (z * s) := by group
        _ = z⁻¹ * t := by rw [e]
        _ = z * t := by rw [inv_eq_of_mul_eq_one_right hz2]
    rw [this]
    exact Subgroup.mul_mem _ hzcl htcl
  ·
    refine hyp51At_of_vertexY hinv h hlay hJ₁ hv₁ hstd.hJ hstd.ht hB hsB hzB htB (Ne.symm hsz)
      (Ne.symm hst) (Ne.symm hne) ?_
    intro e
    exact hszt e.symm
  ·
    refine hyp51At_of_vertexY hinv h hlay hJ₂ hv₂ hstd.hJ hstd.ht hB
      (Subgroup.mul_mem _ htB hsB) hzB htB ?_ ?_ (Ne.symm hne) ?_
    · intro e
      apply hs.indep
      have : s = t * z := by
        calc s = t⁻¹ * (t * s) := by group
          _ = t⁻¹ * z := by rw [← e]
          _ = t * z := by rw [inv_eq_of_mul_eq_one_right ht2]
      rw [this]
      exact Subgroup.mul_mem _ htcl hzcl
    · intro e
      apply hs.ne_one
      have : t * s = t * 1 := by rw [mul_one]; exact e.symm
      exact mul_left_cancel this
    · intro e
      apply hsz
      have : t * z = t * s := by rw [← hzt]; exact e
      exact (mul_left_cancel this).symm

end Vertex

section Final

theorem e3tY_proved : Q3AM.VertexTLeafY := e3tY_of_dich invol_dich_proved

end Final

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
