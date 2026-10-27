module

public import CFSG.ClassicalInvolution.Q3.Q3T8Bridge
public import CFSG.ClassicalInvolution.Q3.Q3T8Defs
public import CFSG.ClassicalInvolution.Q3.Q3T7Q22Base
public import CFSG.ClassicalInvolution.Q3.Q3T7EApp
public import CFSG.ClassicalInvolution.Q3.Q3T7M00
public import CFSG.ClassicalInvolution.Q3.Q3T7M01
public import CFSG.ClassicalInvolution.Q3.Q3T7P24A01
public import CFSG.ClassicalInvolution.Q3.Q3T7P25A01
public import CFSG.ClassicalInvolution.Q3.Q3T7P25X01
public import CFSG.ClassicalInvolution.Q3.Q3T7Q22Z2
public import CFSG.ClassicalInvolution.Q3.Q3T8C262Sec
public import CFSG.ClassicalInvolution.Q3.Q3T8E4Gen
public import CFSG.ClassicalInvolution.Q3.Q3T7Q2201
public import CFSG.ClassicalInvolution.Q3.Q3T7Q2202
public import CFSG.ClassicalInvolution.Asc77.AscT7BSetup
public import CFSG.ClassicalInvolution.Asc77.AscIHSectKD
public import CFSG.ClassicalInvolution.Asc77.AscIHSectL
public import CFSG.ClassicalInvolution.Asc77.AscMuTabEdge
public import CFSG.ClassicalInvolution.Asc77.AscS16E
public import CFSG.ClassicalInvolution.Asc77.AscT7BAlpha
public import CFSG.ClassicalInvolution.Asc77.AscT7FA
public import CFSG.ClassicalInvolution.Asc77.AscC22G7
public import CFSG.ClassicalInvolution.Asc77.AscMuTabResidual2
public import CFSG.ClassicalInvolution.Asc77.AscT7BHyp51
public import CFSG.ClassicalInvolution.Asc77.AscS16M
public import CFSG.ClassicalInvolution.Asc77.AscS22A
public import CFSG.ClassicalInvolution.Asc77.AscT7QFinal
public import CFSG.ClassicalInvolution.Q3.Q3T7MFin
public import CFSG.ClassicalInvolution.Q3.Q3T7P25A05
public import CFSG.ClassicalInvolution.Q3.Q3T8BendEnd
public import CFSG.ClassicalInvolution.Uniform.U4Basic

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
namespace T7B
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.T7B

theorem exists_third_sylow
    (hΩ : Q3T8.Asc77.HypOmegaMod Ω)
    {L L' L₃ R₁ R₂ : Subgroup G} {z : G} (hL : L ∈ Ω) (hL' : L' ∈ Ω) (hL₃ : L₃ ∈ Ω)
    (hz : IsUniqueInvolution L z) (hz' : IsUniqueInvolution L' z) (hz₃ : IsUniqueInvolution L₃ z)
    (hne₃ : L₃ ≠ L) (hne₃' : L₃ ≠ L') (hR₁ : IsSylow2In R₁ L)
    (hR₂ : IsSylow2In R₂ L') (hc : Commutes R₁ R₂) :
    ∃ R₃ : Subgroup G, IsSylow2In R₃ L₃ ∧ Commutes R₁ R₃ ∧ Commutes R₂ R₃ := by
  have hRn : R₁ ≤ Subgroup.normalizer (R₂ : Set G) := T7A.le_normalizer_of_commutes hc.symm
  have hP2 : IsPGroup 2 ↥(R₁ ⊔ R₂) := hR₁.2.1.to_sup_of_normal_right' hR₂.2.1 hRn
  have hLN : L ≤ Subgroup.normalizer (L₃ : Set G) :=
    hΩ.le_normalizer_of_twin hL hL₃ hne₃.symm hz hz₃
  have hL'N : L' ≤ Subgroup.normalizer (L₃ : Set G) :=
    hΩ.le_normalizer_of_twin hL' hL₃ hne₃'.symm hz' hz₃
  have hPN : R₁ ⊔ R₂ ≤ Subgroup.normalizer (L₃ : Set G) :=
    sup_le (hR₁.1.trans hLN) (hR₂.1.trans hL'N)
  obtain ⟨R₃, hR₃, hfix⟩ := exists_sylow_normalized hP2 hPN
  have hPnR₃ : R₁ ⊔ R₂ ≤ Subgroup.normalizer (R₃ : Set G) := fun r hr =>
    mem_normalizer_iff_conjSub_eq.mpr (hfix r hr)
  have hQ2 : IsPGroup 2 ↥((R₁ ⊔ R₂) ⊔ R₃) := hP2.to_sup_of_normal_right' hR₃.2.1 hPnR₃
  obtain ⟨S, hS⟩ := hQ2.exists_le_sylow
  have hR₁S : R₁ ≤ (S : Subgroup G) := le_sup_left.trans (le_sup_left.trans hS)
  have hR₂S : R₂ ≤ (S : Subgroup G) := le_sup_right.trans (le_sup_left.trans hS)
  have hR₃S : R₃ ≤ (S : Subgroup G) := le_sup_right.trans hS
  have h1set : R₁ ∈ RSet Ω := mem_RSet_of_isSylow2In hL hR₁
  have h2set : R₂ ∈ RSet Ω := mem_RSet_of_isSylow2In hL' hR₂
  have h3set : R₃ ∈ RSet Ω := mem_RSet_of_isSylow2In hL₃ hR₃
  have h13 : R₁ ≠ R₃ := by
    intro h
    have := hΩ.card_le_two_of_le_inf hL hL₃ hne₃.symm hR₁.2.1 hR₁.1 (h ▸ hR₃.1)
    have := hΩ.eight_le_of_mem_RSet h1set
    omega
  have h23 : R₂ ≠ R₃ := by
    intro h
    have := hΩ.card_le_two_of_le_inf hL' hL₃ hne₃'.symm hR₂.2.1 hR₂.1 (h ▸ hR₃.1)
    have := hΩ.eight_le_of_mem_RSet h2set
    omega
  exact ⟨R₃, hR₃, Q3T8.Asc77.l6_7_proved G Ω hΩ S R₁ h1set R₃ h3set hR₁S hR₃S h13,
    Q3T8.Asc77.l6_7_proved G Ω hΩ S R₂ h2set R₃ h3set hR₂S hR₃S h23⟩

theorem isElemAbelian2_B
    (hΩ : Q3T8.Asc77.HypOmegaMod Ω) {K K' K₃ : Subgroup G}
    {z u₁ u₂ u₃ : G} (hK : K ∈ Ω) (hK' : K' ∈ Ω) (hK₃ : K₃ ∈ Ω) (hKK' : K' ≠ K)
    (hKK₃ : K₃ ≠ K) (hK'K₃ : K₃ ≠ K') (hz : IsUniqueInvolution K z)
    (hz' : IsUniqueInvolution K' z) (hz₃ : IsUniqueInvolution K₃ z)
    (h₁ : u₁ ∈ K) (h₂ : u₂ ∈ K') (h₃ : u₃ ∈ K₃) (o₁ : orderOf u₁ = 4) (o₂ : orderOf u₂ = 4)
    (o₃ : orderOf u₃ = 4) (c₁₂ : u₁ * u₂ = u₂ * u₁) (c₁₃ : u₁ * u₃ = u₃ * u₁)
    (c₂₃ : u₂ * u₃ = u₃ * u₂) :
    IsElemAbelian2 (Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G)) 3 := by
  have s₁ : u₁ * u₁ = z := T7A.sq_eq_of_orderOf_four hz h₁ o₁
  have s₂ : u₂ * u₂ = z := T7A.sq_eq_of_orderOf_four hz' h₂ o₂
  have s₃ : u₃ * u₃ = z := T7A.sq_eq_of_orderOf_four hz₃ h₃ o₃
  have zc₁ : z * u₁ = u₁ * z := e189_commute_of_mem hz h₁
  have zc₂ : z * u₂ = u₂ * z := e189_commute_of_mem hz' h₂
  have zc₃ : z * u₃ = u₃ * z := e189_commute_of_mem hz₃ h₃
  have hz2 : z * z = 1 := hz.sq
  have q₁₂ : (u₁ * u₂) * (u₁ * u₂) = 1 := by
    calc (u₁ * u₂) * (u₁ * u₂) = u₁ * (u₂ * u₁) * u₂ := by group
      _ = u₁ * (u₁ * u₂) * u₂ := by rw [← c₁₂]
      _ = (u₁ * u₁) * (u₂ * u₂) := by group
      _ = 1 := by rw [s₁, s₂, hz2]
  have q₂₃ : (u₂ * u₃) * (u₂ * u₃) = 1 := by
    calc (u₂ * u₃) * (u₂ * u₃) = u₂ * (u₃ * u₂) * u₃ := by group
      _ = u₂ * (u₂ * u₃) * u₃ := by rw [← c₂₃]
      _ = (u₂ * u₂) * (u₃ * u₃) := by group
      _ = 1 := by rw [s₂, s₃, hz2]
  have hcu₁₂ : Commute (u₁ * u₂) z := by
    have : Commute u₁ z := zc₁.symm
    have : Commute u₂ z := zc₂.symm
    exact Commute.mul_left (by assumption) (by assumption)
  have hcu₂₃ : Commute (u₂ * u₃) z := Commute.mul_left (zc₂.symm : Commute u₂ z)
    (zc₃.symm : Commute u₃ z)
  have hc12 : Commute u₁ u₂ := c₁₂
  have hc13 : Commute u₁ u₃ := c₁₃
  have hc23 : Commute u₂ u₃ := c₂₃
  have hcomm : ∀ a ∈ ({u₁ * u₂, z, u₂ * u₃} : Set G), ∀ b ∈ ({u₁ * u₂, z, u₂ * u₃} : Set G),
      a * b = b * a := by
    intro a ha b hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
    · rfl
    · exact hcu₁₂.eq
    · exact (Commute.mul_left (hc12.mul_right hc13) ((Commute.refl u₂).mul_right hc23)).eq
    · exact hcu₁₂.symm.eq
    · rfl
    · exact hcu₂₃.symm.eq
    · exact (Commute.mul_left (hc12.mul_right hc13) ((Commute.refl u₂).mul_right hc23)).symm.eq
    · exact hcu₂₃.eq
    · rfl
  have hsq : ∀ a ∈ ({u₁ * u₂, z, u₂ * u₃} : Set G), a * a = 1 := by
    intro a ha
    rcases ha with rfl | rfl | rfl
    · exact q₁₂
    · exact hz2
    · exact q₂₃
  refine ⟨?_, fun x hx => T7A.sq_closure hsq hcomm x hx⟩
  have hne12 : u₁ * u₂ ≠ z := by
    intro he
    refine Q3T8.Asc77.T7A.not_mem_inf_of_orderOf_four hΩ hK hK' hKK' o₂ ?_ h₂
    have : u₂ = u₁⁻¹ * z := by rw [← he]; group
    rw [this]
    exact K.mul_mem (K.inv_mem h₁) hz.mem
  have hne1 : u₁ * u₂ ≠ 1 := by
    intro he
    refine Q3T8.Asc77.T7A.not_mem_inf_of_orderOf_four hΩ hK hK' hKK' o₂ ?_ h₂
    have : u₂ = u₁⁻¹ := eq_inv_of_mul_eq_one_right he
    rw [this]
    exact K.inv_mem h₁
  have hc1 : u₂ * u₃ ≠ 1 := by
    intro he
    refine Q3T8.Asc77.T7A.not_mem_inf_of_orderOf_four hΩ hK' hK₃ hK'K₃ o₃ ?_ h₃
    have : u₃ = u₂⁻¹ := eq_inv_of_mul_eq_one_right he
    rw [this]
    exact K'.inv_mem h₂
  have hnot : u₂ * u₃ ∉ Subgroup.closure ({u₁ * u₂, z} : Set G) := by
    intro hx
    rcases mem_closure_pair q₁₂ hz2 hne1 hz.ne_one hcu₁₂.eq hx with h | h | h | h
    · exact hc1 h
    · have h3 : u₃ = u₁ := mul_left_cancel (h.trans c₁₂)
      exact Q3T8.Asc77.T7A.not_mem_inf_of_orderOf_four hΩ hK hK₃ hKK₃ o₃ (h3 ▸ h₁) h₃
    · have h3 : u₃ = u₂⁻¹ * z := by rw [← h]; group
      refine Q3T8.Asc77.T7A.not_mem_inf_of_orderOf_four hΩ hK' hK₃ hK'K₃ o₃ ?_ h₃
      rw [h3]
      exact K'.mul_mem (K'.inv_mem h₂) hz'.mem
    · have h' : u₂ * u₃ = u₂ * (u₁ * z) := by rw [h, c₁₂]; group
      have h3 : u₃ = u₁ * z := mul_left_cancel h'
      refine Q3T8.Asc77.T7A.not_mem_inf_of_orderOf_four hΩ hK hK₃ hKK₃ o₃ ?_ h₃
      rw [h3]
      exact K.mul_mem h₁ hz.mem
  have := natCard_closure_three_eq_eight q₁₂ hz2 q₂₃ hne1 hz.ne_one hne12 hc1
    hcu₁₂.eq (hcomm _ (by simp) _ (by simp)) (hcomm _ (by simp) _ (by simp)) hnot
  rw [this]
  norm_num

theorem hyp22_of_sylows
    {K K' K₃ : Subgroup G} {z : G} (hs : Q3T8.Asc77.Std7 Ω K K' z)
    (hperp : KPerp Ω K = twinSet Ω K) (hK₃ : K₃ ∈ twinSet Ω K) (hK₃K : K₃ ≠ K) (hK₃K' : K₃ ≠ K')
    {R R' R₃ : Subgroup G} (hR : IsSylow2In R K) (hR' : IsSylow2In R' K')
    (hR₃ : IsSylow2In R₃ K₃) (c₁₂ : Commutes R R') (c₁₃ : Commutes R R₃)
    (c₂₃ : Commutes R' R₃) {u₁ u₂ u₃ : G} (h₁ : u₁ ∈ R) (h₂ : u₂ ∈ R') (h₃ : u₃ ∈ R₃)
    (o₁ : orderOf u₁ = 4) (o₂ : orderOf u₂ = 4) (o₃ : orderOf u₃ = 4) :
    Q3T8.Asc77.Hyp22 Ω K K' K₃ z u₁ u₂ u₃ := by
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hs.hz hs.hK'
  have hzK₃ : IsUniqueInvolution K₃ z := isUniqueInvolution_of_mem_twinSet hs.hz hK₃
  have hB := Q3T8.Asc77.T7B.isElemAbelian2_B hs.stand.hyp hs.stand.mem hs.hK'.1 hK₃.1 hs.hne
    hK₃K hK₃K' hs.hz hzK' hzK₃ (hR.1 h₁) (hR'.1 h₂) (hR₃.1 h₃) o₁ o₂ o₃ (c₁₂ u₁ h₁ u₂ h₂)
    (c₁₃ u₁ h₁ u₃ h₃) (c₂₃ u₂ h₂ u₃ h₃)
  exact
    { std := hs
      perp := hperp
      hK₃ := hK₃
      hK₃K := hK₃K
      hK₃K' := hK₃K'
      hu₁ := ⟨hR.1 h₁, o₁⟩
      hu₂ := ⟨hR'.1 h₂, o₂⟩
      hu₃ := ⟨hR₃.1 h₃, o₃⟩
      hB := hB }

theorem exists_threeTwinSylow
    (hΩ : Q3T8.Asc77.HypOmegaMod Ω)
    {K K' K₃ : Subgroup G} {z : G} (hK : K ∈ Ω) (hz : IsUniqueInvolution K z)
    (hK' : K' ∈ twinSet Ω K) (hK₃ : K₃ ∈ twinSet Ω K) (hne : K' ≠ K) (hne₃ : K₃ ≠ K)
    (hne₃' : K₃ ≠ K') :
    ∃ R R' R₃ : Subgroup G, IsSylow2In R K ∧ IsSylow2In R' K' ∧ IsSylow2In R₃ K₃ ∧
      Commutes R R' ∧ Commutes R R₃ ∧ Commutes R' R₃ := by
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hK'
  have hzK₃ : IsUniqueInvolution K₃ z := isUniqueInvolution_of_mem_twinSet hz hK₃
  obtain ⟨R, R', hR, hR', hc⟩ := Q3T8.Asc77.T7A.exists_commuting_sylow_twin hΩ hK hK'.1 hne hz hzK'
  obtain ⟨R₃, hR₃, hc₁, hc₂⟩ :=
    Q3T8.Asc77.T7B.exists_third_sylow hΩ hK hK'.1 hK₃.1 hz hzK' hzK₃ hne₃ hne₃' hR hR' hc
  exact ⟨R, R', R₃, hR, hR', hR₃, hc, hc₁, hc₂⟩
end T7B

theorem c22_setup
    : Q3T8.Asc77.C22_setup := by
  intro G _ _ _ Ω K K' z hs hperp hne
  have hΩ : Q3T7M.HM Ω := hs.stand.modU
  have hK : K ∈ Ω := hs.stand.mem
  have hex : ∃ K₃ ∈ twinSet Ω K, K₃ ≠ K ∧ K₃ ≠ K' := by
    by_contra hcon
    push Not at hcon
    apply hne
    ext J
    constructor
    · intro hJ
      have hJt : J ∈ twinSet Ω K := by rw [← hperp]; exact hJ
      by_cases hJK : J = K
      · exact Or.inl hJK
      · exact Or.inr (hcon J hJt hJK)
    · rintro (rfl | rfl)
      · exact Set.mem_insert _ _
      · rw [hperp]; exact hs.hK'
  obtain ⟨K₃, hK₃, hK₃K, hK₃K'⟩ := hex
  obtain ⟨R, R', R₃, hR, hR', hR₃, c₁₂, c₁₃, c₂₃⟩ :=
    Q3T8.Asc77.T7B.exists_threeTwinSylow hΩ hK hs.hz hs.hK' hK₃ hs.hne hK₃K hK₃K'
  obtain ⟨u₁, hu₁, o₁⟩ := hΩ.exists_orderOf_eq_four_of_mem_RSet (mem_RSet_of_isSylow2In hK hR)
  obtain ⟨u₂, hu₂, o₂⟩ :=
    hΩ.exists_orderOf_eq_four_of_mem_RSet (mem_RSet_of_isSylow2In hs.hK'.1 hR')
  obtain ⟨u₃, hu₃, o₃⟩ :=
    hΩ.exists_orderOf_eq_four_of_mem_RSet (mem_RSet_of_isSylow2In hK₃.1 hR₃)
  exact ⟨K₃, u₁, u₂, u₃, Q3T8.Asc77.T7B.hyp22_of_sylows hs hperp hK₃ hK₃K hK₃K' hR hR' hR₃ c₁₂ c₁₃
      c₂₃
    hu₁ hu₂ hu₃ o₁ o₂ o₃⟩
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
namespace S16
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.S16
set_option linter.unusedSectionVars false
open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.LieType.Universal CFSG.ClassicalInvolution.Asc77.FrameVertex
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
section Z2
variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem false_of_z2_section
    (hR1 : Q3T8.Asc77.S16.Z2NoD8) (hS : Q3T8.Asc77.GenSection Φ) (D :
    Q3T8.Asc77.OmegaLie Φ) (hcard : D.card = 1) (i : Fin D.card)
    (hZ2 : (D.tag i = .PSL ∧ D.rank i = 3 ∧ 3 % 4 = 3) ∨
      (D.tag i = .PSU ∧ D.rank i = 3 ∧ 3 % 4 = 1))
    {H : Type} [Group H] [Finite H] (ι : X →* H) (hι : Function.Injective ι) (a v : H)
    (ha : ∀ x : X, a * ι x * a⁻¹ ∈ ι.range ∧ a⁻¹ * ι x * a ∈ ι.range)
    (hv : ∀ x : X, v * ι x * v⁻¹ ∈ ι.range ∧ v⁻¹ * ι x * v ∈ ι.range)
    {A : Subgroup X} (hA : A ∈ Φ) {z : X} (hzA : IsUniqueInvolution A z)
    (haA : ∀ x ∈ A, ∃ n ∈ oddCoreOf A, a * ι x * a⁻¹ = ι (n * x))
    (hvA : ∀ x ∈ A, ∃ n ∈ oddCoreOf A, v * ι x * v⁻¹ = ι (n * x))
    (ha2 : a * a = ι z) (hv2 : v * v = 1) (hav : v * a * v⁻¹ = a⁻¹) : False := by
  classical
  have hΦ : Q3T7M.HM Φ := hS.hyp
  have hG2 : D.tag i ≠ .G2 := by
    rcases hZ2 with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> decide
  have hD4 : D.tag i ≠ .trialityD4 := by
    rcases hZ2 with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> decide
  have hexp : D.exp i = 1 := (D.exp_eq i).resolve_right fun h => hD4 h.1
  have hΦex : Q3T8.Asc77.HypOmega Φ := Q3T8.Sect.hypOmega_of_modU_exact hΦ
      (Q3T8.Asc77.OmegaLie.exactMembers hΦ D)
  obtain ⟨j, R, hRf, hAR⟩ := D.fundamental A hA
  have hsub : Subsingleton (Fin D.card) := by
    rw [hcard]
    infer_instance
  obtain rfl : i = j := Subsingleton.elim _ _
  have hT6 : AschTight.S1911.IsT6Tag (D.tag i) (D.rank i) := by
    rcases hZ2 with ⟨h, h', -⟩ | ⟨h, h', -⟩
    · exact Or.inl ⟨h, h'⟩
    · exact Or.inr (Or.inl ⟨h, h'⟩)
  obtain ⟨c, hc⟩ := AschTight.S19M.exists_isUniqueInvolution_of_mem_fund (by norm_num) hT6
      (D.admissible i) hRf
  have hfin : Finite (modelUniv (D.tag i) (D.rank i) 3 (D.exp i) Fact.out).K :=
    ModelFacts.finite_modelUniv (by norm_num) Fact.out (ih8_isFundTag_mf (D.isFundTag i))
        (D.admissible i)
  have hodd : Odd (Nat.card (D.hom i).ker) :=
    AschTight.S19M.odd_natCard_ker (D.ker_le_center i)
      (AschTight.S19M.factM3 3 (D.exp i) (Fact.out) (by norm_num) (D.tag i) (D.rank i) hT6
          (D.admissible i))
  have hfinker : Finite (D.hom i).ker := inferInstance
  have hcz : D.hom i c = z := by
    have h1 := AschTight.S19M.isUniqueInvolution_map hodd hc
    rw [← hAR] at h1
    exact h1.eq hzA
  set ψ' : (modelUniv (D.tag i) (D.rank i) 3 (D.exp i) Fact.out).K →* H := ι.comp (D.hom i)
    with hψ'
  have hker : ψ'.ker ≤ Subgroup.center (modelUniv (D.tag i) (D.rank i) 3 (D.exp i) Fact.out).K := by
    intro y hy
    apply D.ker_le_center i
    rw [MonoidHom.mem_ker] at hy ⊢
    refine hι ?_
    rw [map_one]
    exact hy
  have hsurj : Function.Surjective (D.hom i) := D.hom_surjective_of_gen hcard hS.gen i
  have hrange : ψ'.range = ι.range := by
    ext y
    simp only [ψ', MonoidHom.mem_range, MonoidHom.comp_apply]
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨x, rfl⟩
      obtain ⟨s, rfl⟩ := hsurj x
      exact ⟨s, rfl⟩
  have hnorm : ∀ w : H, (∀ x : X, w * ι x * w⁻¹ ∈ ι.range ∧ w⁻¹ * ι x * w ∈ ι.range) →
      w ∈ Subgroup.normalizer (ψ'.range : Set H) := by
    intro w hw
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [hrange]
    constructor
    · rintro ⟨x, rfl⟩
      exact (hw x).1
    · intro hy
      obtain ⟨x, hx⟩ := hy
      have : y = w⁻¹ * ι x * w := by
        rw [hx]
        group
      rw [this]
      exact (hw x).2
  have hna : a ∈ Subgroup.normalizer (ψ'.range : Set H) := hnorm a ha
  have hnv : v ∈ Subgroup.normalizer (ψ'.range : Set H) := hnorm v hv
  have hexc : ∀ w : H, (∀ x ∈ A, ∃ n ∈ oddCoreOf A, w * ι x * w⁻¹ = ι (n * x)) →
      ∀ x ∈ A, w * ι x = ι x * w := by
    intro w hh x hx
    obtain ⟨n, hn, hnx⟩ := hh x hx
    rw [oddCoreOf_eq_bot_of_exact hΦex.exact hA, Subgroup.mem_bot] at hn
    rw [hn, one_mul] at hnx
    calc w * ι x = (w * ι x * w⁻¹) * w := by group
      _ = ι x * w := by rw [hnx]
  have hψ'A : ∀ r ∈ R, ψ' r ∈ ι '' (A : Set X) := by
    intro r hr
    refine ⟨D.hom i r, ?_, rfl⟩
    rw [hAR]
    exact Subgroup.mem_map_of_mem _ hr
  have hfix : ∀ w : H, (hw : w ∈ Subgroup.normalizer (ψ'.range : Set H)) →
      (∀ x ∈ A, w * ι x = ι x * w) →
      ∀ r ∈ R, toInducedAutOn ψ'.range ⟨w, hw⟩ * innerHom ψ' r =
        innerHom ψ' r * toInducedAutOn ψ'.range ⟨w, hw⟩ := by
    intro w hw hh r hr
    obtain ⟨s, hs, hsr⟩ := hψ'A r hr
    rw [FrameVertex.innerHom_apply, ← map_mul, ← map_mul]
    congr 1
    refine Subtype.ext ?_
    show w * ψ' r = ψ' r * w
    rw [← hsr]
    exact hh s hs
  have hZ2' : (D.tag i = .PSL ∧ D.rank i = 3 ∧ 3 ^ D.exp i % 4 = 3) ∨
      (D.tag i = .PSU ∧ D.rank i = 3 ∧ 3 ^ D.exp i % 4 = 1) := by
    rw [hexp]
    exact hZ2
  refine hR1 (D.tag i) (D.rank i) (D.exp i) (D.admissible i) hZ2' ψ' hker R c hRf hc.mem
    hc.sq hc.ne_one (toInducedAutOn ψ'.range ⟨a, hna⟩) (toInducedAutOn ψ'.range ⟨v, hnv⟩)
    (hfix a hna (hexc a haA)) (hfix v hnv (hexc v hvA)) ?_ ?_ ?_
  · rw [FrameVertex.innerHom_apply, ← map_mul]
    congr 1
    refine Subtype.ext ?_
    show a * a = ψ' c
    simp only [ψ', MonoidHom.comp_apply, hcz]
    exact ha2
  · rw [← map_mul]
    have : (⟨v, hnv⟩ * ⟨v, hnv⟩ : ↥(Subgroup.normalizer (ψ'.range : Set H))) = 1 :=
      Subtype.ext hv2
    rw [this, map_one]
  · rw [← map_inv, ← map_mul, ← map_mul, ← map_inv]
    congr 1
    refine Subtype.ext ?_
    show v * a * v⁻¹ = a⁻¹
    exact hav
end Z2
end S16
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' K₃ : Subgroup G} {z u₁ u₂ u₃ : G}
namespace Hyp22
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.Hyp22

theorem comm_gen
    (h : Q3T8.Asc77.Hyp22 Ω K K' K₃ z u₁ u₂ u₃) :
    ∀ a ∈ ({u₁ * u₂, z, u₂ * u₃} : Set G), ∀ b ∈ ({u₁ * u₂, z, u₂ * u₃} : Set G),
      a * b = b * a := by
  have hc12 : Commute u₁ u₂ := h.comm₁₂
  have hc13 : Commute u₁ u₃ := h.comm₁₃
  have hc23 : Commute u₂ u₃ := h.comm₂₃
  have hcu₁₂ : Commute (u₁ * u₂) z :=
    Commute.mul_left (h.comm_z₁.symm : Commute u₁ z) (h.comm_z₂.symm : Commute u₂ z)
  have hcu₂₃ : Commute (u₂ * u₃) z :=
    Commute.mul_left (h.comm_z₂.symm : Commute u₂ z) (h.comm_z₃.symm : Commute u₃ z)
  have hmix : Commute (u₁ * u₂) (u₂ * u₃) :=
    Commute.mul_left (hc12.mul_right hc13) ((Commute.refl u₂).mul_right hc23)
  intro a ha b hb
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
  · rfl
  · exact hcu₁₂.eq
  · exact hmix.eq
  · exact hcu₁₂.symm.eq
  · rfl
  · exact hcu₂₃.symm.eq
  · exact hmix.symm.eq
  · exact hcu₂₃.eq
  · rfl

theorem isElemAbelian_B
    (h : Q3T8.Asc77.Hyp22 Ω K K' K₃ z u₁ u₂ u₃) :
    IsElemAbelian 2 (Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G)) := by
  have hcomm := T7A.commutes_closure h.comm_gen
  refine ⟨⟨⟨fun a b => Subtype.ext (hcomm _ a.2 _ b.2)⟩⟩, fun x hx => ?_⟩
  rw [pow_two]
  exact h.hB.2 x hx

theorem B_le_centralizer
    (h : Q3T8.Asc77.Hyp22 Ω K K' K₃ z u₁ u₂ u₃) :
    Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G) ≤ Subgroup.centralizer ({z} : Set G) := by
  rw [Subgroup.closure_le]
  intro x hx
  rcases hx with rfl | rfl | rfl
  · exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Commute.mul_left (h.comm_z₁.symm : Commute u₁ z) (h.comm_z₂.symm : Commute u₂ z)).eq
  · exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  · exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Commute.mul_left (h.comm_z₂.symm : Commute u₂ z) (h.comm_z₃.symm : Commute u₃ z)).eq

theorem isElemAbelian2_closure_23
    (h : Q3T8.Asc77.Hyp22 Ω K K' K₃ z u₁ u₂ u₃) :
    IsElemAbelian2 (Subgroup.closure ({u₂ * u₃, z} : Set G)) 2 :=
  h.rotate.isElemAbelian2_closure

theorem closure_23_le
    (h : Q3T8.Asc77.Hyp22 Ω K K' K₃ z u₁ u₂ u₃) :
    Subgroup.closure ({u₂ * u₃, z} : Set G) ≤
      Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G) := by
  rw [Subgroup.closure_le]
  rintro x (rfl | rfl)
  · exact T7B.mem_closure_thd
  · exact T7B.mem_closure_snd

theorem closure_12_le
    (h : Q3T8.Asc77.Hyp22 Ω K K' K₃ z u₁ u₂ u₃) :
    Subgroup.closure ({u₁ * u₂, z} : Set G) ≤
      Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G) := by
  rw [Subgroup.closure_le]
  rintro x (rfl | rfl)
  · exact T7B.mem_closure_fst
  · exact T7B.mem_closure_snd

theorem closure_13_le
    (h : Q3T8.Asc77.Hyp22 Ω K K' K₃ z u₁ u₂ u₃) :
    Subgroup.closure ({u₁ * u₃, z} : Set G) ≤
      Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G) := by
  rw [Subgroup.closure_le]
  rintro x (rfl | rfl)
  · exact h.mem_B_13
  · exact T7B.mem_closure_snd

theorem isElemAbelian2_closure_13
    (h : Q3T8.Asc77.Hyp22 Ω K K' K₃ z u₁ u₂ u₃) :
    IsElemAbelian2 (Subgroup.closure ({u₁ * u₃, z} : Set G)) 2 := by
  have h' := h.rotate.rotate.isElemAbelian2_closure
  rwa [← h.comm₁₃] at h'

theorem natCard_B
    (h : Q3T8.Asc77.Hyp22 Ω K K' K₃ z u₁ u₂ u₃) :
    Nat.card ↥(Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G)) = 8 := by
  have := h.hB.1
  norm_num at this
  exact this
section Alpha22
variable [IsSimpleGroup G]

theorem alpha_23
    (h2 : Q3T8.Asc77.C22_2) (h : Q3T8.Asc77.Hyp22 Ω K K' K₃ z u₁ u₂ u₃) :
    alphaOf (Subgroup.closure ({u₂ * u₃, z} : Set G)) =
      alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) :=
  (h2 G Ω K K' K₃ z u₁ u₂ u₃ h).2 _ h.closure_23_le h.isElemAbelian2_closure_23

theorem alpha_13
    (h2 : Q3T8.Asc77.C22_2) (h : Q3T8.Asc77.Hyp22 Ω K K' K₃ z u₁ u₂ u₃) :
    alphaOf (Subgroup.closure ({u₁ * u₃, z} : Set G)) =
      alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) :=
  (h2 G Ω K K' K₃ z u₁ u₂ u₃ h).2 _ h.closure_13_le h.isElemAbelian2_closure_13

theorem oddCore_le_normalizer_alpha
    (h2 : Q3T8.Asc77.C22_2) (h : Q3T8.Asc77.Hyp22 Ω K K' K₃ z u₁ u₂
    u₃) :
    oddCoreOf (Subgroup.centralizer ({z} : Set G)) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G) :=
  T7A.oddCore_le_normalizer_alpha h.isElemAbelian_B h.natCard_B h.B_le_centralizer
    (h2 G Ω K K' K₃ z u₁ u₂ u₃ h).2

theorem third_le_normalizer_alpha
    (h2 : Q3T8.Asc77.C22_2) (h : Q3T8.Asc77.Hyp22 Ω K K' K₃ z u₁ u₂
    u₃) :
    K₃ ≤ Subgroup.normalizer (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G) := by
  intro ℓ hℓ
  have hΩ : Q3T7M.HM Ω := h.std.stand.modU
  have hK : K ∈ Ω := h.std.stand.mem
  have hK' : K' ∈ Ω := h.std.hK'.1
  have hK₃Ω : K₃ ∈ Ω := h.hK₃.1
  have hℓC : ℓ ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (e189_commute_of_mem h.hzK₃ hℓ).symm
  have hzt : z * (u₁ * u₂) = (u₁ * u₂) * z :=
    (Commute.mul_left (h.comm_z₁.symm : Commute u₁ z) (h.comm_z₂.symm : Commute u₂ z)).eq.symm
  have hu₁C : u₁ ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr h.comm_z₁.symm
  have hsub := Q3T8.Asc77.T7A.isSubnormal_centralizer hΩ hK₃Ω h.hzK₃
  have hc₁ : ⁅u₁, ℓ⁆ ∈ oddCoreOf (Subgroup.centralizer ({z} : Set G)) := by
    have := hΩ.comm_le_oddCore_of_twin hK hK₃Ω h.hK₃K.symm h.std.hz h.hzK₃
      (Subgroup.commutator_mem_commutator h.hu₁.1 hℓ)
    exact CFSG.ClassicalInvolution.Balance.oddCoreIn_le_of_isSubnormal hsub this.2
  have hc₂ : ⁅u₂, ℓ⁆ ∈ oddCoreOf (Subgroup.centralizer ({z} : Set G)) := by
    have := hΩ.comm_le_oddCore_of_twin hK' hK₃Ω h.hK₃K'.symm h.hzK' h.hzK₃
      (Subgroup.commutator_mem_commutator h.hu₂.1 hℓ)
    exact CFSG.ClassicalInvolution.Balance.oddCoreIn_le_of_isSubnormal hsub this.2
  have hN := CFSG.ClassicalInvolution.Balance.normalizer_oddCoreIn _ hu₁C
  have hcomm : (u₁ * u₂) * ℓ * (u₁ * u₂)⁻¹ * ℓ⁻¹ ∈
      oddCoreOf (Subgroup.centralizer ({z} : Set G)) := by
    have e : (u₁ * u₂) * ℓ * (u₁ * u₂)⁻¹ * ℓ⁻¹ = (u₁ * ⁅u₂, ℓ⁆ * u₁⁻¹) * ⁅u₁, ℓ⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp hN _).mp hc₂) hc₁
  exact T7B.mem_normalizer_alphaOf_of_commutator h.sq_12 hzt hℓC hcomm
    (h.oddCore_le_normalizer_alpha h2)

theorem le_normalizer_alpha
    (h2 : Q3T8.Asc77.C22_2) (h : Q3T8.Asc77.Hyp22 Ω K K' K₃ z u₁ u₂ u₃) :
    K ≤ Subgroup.normalizer (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G) ∧
    K' ≤ Subgroup.normalizer (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G) ∧
    K₃ ≤ Subgroup.normalizer (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G) := by
  refine ⟨?_, ?_, h.third_le_normalizer_alpha h2⟩
  · have := h.rotate.third_le_normalizer_alpha h2
    rwa [h.alpha_23 h2] at this
  · have := h.rotate.rotate.third_le_normalizer_alpha h2
    rwa [← h.comm₁₃, h.alpha_13 h2] at this
end Alpha22
end Hyp22
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
    CFSG.LieType.Universal CFSG.LieType.CurtisTits
namespace C22G
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.C22G
set_option linter.unusedSectionVars false
section Linear
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem ih8_dstarConnected_psl4
    (hΩ : Q3T8.Asc77.HypOmegaMod Ω) (hq4 : 3 % 4 = 1) {t :
    StatedLieTag} {k e : ℕ} (M : Q3T8.Asc77.Ih8Model Ω t k e)
    (ht : t = .PSL) (hk : k = 4) : T3.DStarConnected Ω := absurd hq4 (by norm_num)

theorem ih8_dstarConnected_psu4
    (hΩ : Q3T7M.HM Ω) (hq3 : 3 % 4 = 3) {t : StatedLieTag} {k e : ℕ} (M
    : Q3T8.Asc77.Ih8Model Ω t k e)
    (ht : t = .PSU) (hk : k = 4) : T3.DStarConnected Ω := by
  subst ht hk
  have he : e = 1 := M.exp_eq_f (by decide)
  subst he
  exact E4G3.dstarConnected_psu43 hΩ M
end Linear
end C22G
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected

structure Hyp22Setting {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G))
    (K K' K₃ : Subgroup G) (z u₁ u₂ u₃ : G) : Prop where
  stand : Q3T8.Asc77.AscStand Ω K
  hz : IsUniqueInvolution K z
  hK' : K' ∈ twinSet Ω K
  hne : K' ≠ K
  perp : KPerp Ω K = twinSet Ω K
  hK₃ : K₃ ∈ twinSet Ω K
  hK₃K : K₃ ≠ K
  hK₃K' : K₃ ≠ K'
  hu₁ : u₁ ∈ K ∧ orderOf u₁ = 4
  hu₂ : u₂ ∈ K' ∧ orderOf u₂ = 4
  hu₃ : u₃ ∈ K₃ ∧ orderOf u₃ = 4
  hB : IsElemAbelian2 (Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G)) 3

@[expose] def Hyp22Hyp51z
    : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' K₃ : Subgroup G) (z u₁ u₂ u₃ : G), Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃ →
      Hyp51At (Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G)) z

@[expose] def Hyp22Hyp51u
    : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' K₃ : Subgroup G) (z u₁ u₂ u₃ : G), Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃ →
      ∀ c ∈ Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G), c ≠ 1 → c ≠ z →
        Hyp51At (Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G)) c

theorem Hyp22.setting
    {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    {K K' K₃ : Subgroup G} {z u₁ u₂ u₃ : G} (h : Q3T8.Asc77.Hyp22 Ω K K' K₃ z u₁ u₂ u₃) :
    Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃ where
  stand := h.std.stand
  hz := h.std.hz
  hK' := h.std.hK'
  hne := h.std.hne
  perp := h.perp
  hK₃ := h.hK₃
  hK₃K := h.hK₃K
  hK₃K' := h.hK₃K'
  hu₁ := h.hu₁
  hu₂ := h.hu₂
  hu₃ := h.hu₃
  hB := h.hB

theorem c22_2_of
    (hz : Q3T8.Asc77.Hyp22Hyp51z) (hu : Q3T8.Asc77.Hyp22Hyp51u) : Q3T8.Asc77.C22_2 :=
    by
  intro G _ _ _ Ω K K' K₃ z u₁ u₂ u₃ h
  have hs := h.setting
  have hB : Hyp51 (Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G)) := by
    refine ⟨h.isElemAbelian_B, h.natCard_B, fun c hc hc1 => ?_⟩
    by_cases hcz : c = z
    · rw [hcz]
      exact hz G Ω K K' K₃ z u₁ u₂ u₃ hs
    · exact hu G Ω K K' K₃ z u₁ u₂ u₃ hs c hc hc1 hcz
  exact lemma54_odd_and_eq hB h.closure_12_le h.isElemAbelian2_closure
end Asc77

end

end CFSG.ClassicalInvolution.Q3.Q3T8
