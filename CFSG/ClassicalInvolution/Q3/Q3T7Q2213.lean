module

public import CFSG.ClassicalInvolution.Q3.Q3T7Q2212
public import CFSG.ClassicalInvolution.Asc77.AscT7OZ

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

abbrev _root_.CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S16.V3Ab
    :=
  @CFSG.ClassicalInvolution.Asc77.S16.V3Ab

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
namespace S16
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.S16
set_option linter.unusedSectionVars false
open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
    CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
    CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement
section V3
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' K₃ : Subgroup G} {z u₁ u₂ u₃ : G}

theorem V3Ab.hV3
    (h : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃) (hv : Q3T8.Asc77.S16.V3Ab Ω K) :
    ∀ M ∈ twinSet Ω K, M = K ∨ M = K' ∨ M = K₃ := by
  intro M hM
  by_contra hcon
  push Not at hcon
  exact hv.1 (Q3T8.Asc77.S22.Big.of_four h hM hcon.1 hcon.2.1 hcon.2.2)
end V3
section C22
variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)} {K K' K₃ : Subgroup G} {z u₁ u₂ u₃ : G}

theorem invert₂
    (h : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃) :
    Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂⁻¹ u₃ := by
  obtain ⟨R, R', R₃, hR, hR', hR₃, h₁, h₂, h₃, c12, c13, c23⟩ := Q3T8.Asc77.T7J.exists_sylow_triple
      h
  exact Q3T8.Asc77.S22.hyp22Setting_of_sylows h.stand h.hz h.hK' h.hne h.perp h.hK₃ h.hK₃K h.hK₃K'
      hR hR'
    hR₃ c12 c13 c23 h₁ (R'.inv_mem h₂) h₃ h.hu₁.2 (by rw [orderOf_inv]; exact h.hu₂.2) h.hu₃.2

theorem hyp51At_B
    (h : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃) {c : G}
    (hcB : c ∈ Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G)) (hcz : c ≠ z)
    (hzs : z ∈ zStarOf (Subgroup.centralizer ({c} : Set G))) :
    Hyp51At (Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G)) c := by
  have hzB : z ∈ Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G) := T7B.mem_closure_snd
  have hcc : c * c = 1 := Lemma52Proof.mul_self_eq_one_of_mem h.isElemAbelian_B hcB
  have hcomm : z * c = c * z := by
    have := h.isElemAbelian_B.1.is_comm.comm ⟨z, hzB⟩ ⟨c, hcB⟩
    exact congrArg Subtype.val this
  exact hyp51At_of_zStar hzB h.hz.ne_one h.hz.sq hcc hcomm (Ne.symm hcz) hzs

theorem zStar_pair [Fact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S16.M11NoInverted3] (hR1 :
    Q3T8.Asc77.S16.Z2NoD8) (h : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃)
    (hv : Q3T8.Asc77.S16.V3Ab Ω K) :
    z ∈ zStarOf (Subgroup.centralizer ({u₁ * u₂} : Set G)) ∧
      z ∈ zStarOf (Subgroup.centralizer ({u₁ * u₂ * z} : Set G)) := by
  refine ⟨Q3T8.Asc77.S16.layer_zStar hR1 h (hv.hV3 h) hv.2, ?_⟩
  have h' := Q3T8.Asc77.S16.invert₂ h
  have hv' : Q3T8.Asc77.S16.V3Ab Ω K := hv
  have := Q3T8.Asc77.S16.layer_zStar hR1 h' (hv'.hV3 h') hv'.2
  have e : u₁ * u₂⁻¹ = u₁ * u₂ * z := by
    rw [inv_eq_mul_of_sq h.sq₂ h.hz.sq, mul_assoc]
  rwa [e] at this

theorem hyp51u_of_V3 [Fact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S16.M11NoInverted3] (hR1 :
    Q3T8.Asc77.S16.Z2NoD8) (h : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃)
    (hv : Q3T8.Asc77.S16.V3Ab Ω K) :
    ∀ c ∈ Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G), c ≠ 1 → c ≠ z →
      Hyp51At (Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G)) c := by
  intro c hc hc1 hcz
  have cm : T7J.Cmt z u₁ u₂ u₃ :=
    ⟨h.sq₁, h.sq₂, h.sq₃, h.hz.sq, h.comm₁₂, Q3T8.Asc77.T7J.comm₁₃ h, h.comm₂₃⟩
  have hcm := T7J.mem_closure_three cm.commute_xz cm.commute_xw cm.commute_wz.symm cm.sq_pair
    cm.z2 cm.rot.sq_pair hc
  have hB1 := Q3T8.Asc77.S16.zStar_pair hR1 h hv
  have h2 := Q3T8.Asc77.S22.rotate h
  have hv2 : Q3T8.Asc77.S16.V3Ab Ω K' := hv.of_twin h.hz h.hK'
  have hB2 := Q3T8.Asc77.S16.zStar_pair hR1 h2 hv2
  have h3 := Q3T8.Asc77.S22.rotate h2
  have hv3 : Q3T8.Asc77.S16.V3Ab Ω K₃ := hv.of_twin h.hz h.hK₃
  have hB3 := Q3T8.Asc77.S16.zStar_pair hR1 h3 hv3
  rcases hcm with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1
  · exact absurd h1 hc1
  · subst h1
    exact Q3T8.Asc77.S16.hyp51At_B h hc hcz hB1.1
  · exact absurd h1 hcz
  · subst h1
    exact Q3T8.Asc77.S16.hyp51At_B h hc hcz hB2.1
  · subst h1
    exact Q3T8.Asc77.S16.hyp51At_B h hc hcz hB1.2
  ·
    have e : c = u₃ * u₁ * z := h1.trans cm.eq_xw
    rw [e] at hc hcz ⊢
    exact Q3T8.Asc77.S16.hyp51At_B h hc hcz hB3.2
  ·
    have e : c = u₂ * u₃ * z := h1.trans cm.zc₂₃
    rw [e] at hc hcz ⊢
    exact Q3T8.Asc77.S16.hyp51At_B h hc hcz hB2.2
  ·
    have e : c = u₃ * u₁ := h1.trans cm.eq_xyw
    rw [e] at hc hcz ⊢
    exact Q3T8.Asc77.S16.hyp51At_B h hc hcz hB3.1
end C22
section Statement

@[expose] def C22_2V
    : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' K₃ : Subgroup G) (z u₁ u₂ u₃ : G), Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃ →
      Q3T8.Asc77.S16.V3Ab Ω K →
      Odd (Nat.card ↥(alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)))) ∧
        ∀ A : Subgroup G, A ≤ Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G) →
          IsElemAbelian2 A 2 →
            alphaOf A = alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G))
end Statement
section C22Thm

theorem c22_2V [Fact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.Hyp22Hyp51z] [Fact
    CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S16.M11NoInverted3] (hR1 : Q3T8.Asc77.S16.Z2NoD8) :
    Q3T8.Asc77.S16.C22_2V := by
  intro G _ _ _ Ω K K' K₃ z u₁ u₂ u₃ h hv
  have hB : Hyp51 (Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G)) := by
    refine ⟨Q3T8.Asc77.Hyp22Setting.isElemAbelian_B h, Q3T8.Asc77.S22.natCard_B h, fun c hc hc1 =>
        ?_⟩
    by_cases hcz : c = z
    · rw [hcz]
      exact Q3T8.Asc77.hyp22Hyp51z G Ω K K' K₃ z u₁ u₂ u₃ h
    · exact Q3T8.Asc77.S16.hyp51u_of_V3 hR1 h hv c hc hc1 hcz
  exact lemma54_odd_and_eq hB (Q3T8.Asc77.S22.closure_12_le h)
      (Q3T8.Asc77.S22.isElemAbelian2_closure h)
end C22Thm
end S16
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
namespace S16
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.S16
set_option linter.unusedSectionVars false
open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.S22
open scoped commutatorElement
section Alpha
variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)} {K K' K₃ : Subgroup G} {z u₁ u₂ u₃ : G}

theorem alpha_23V
    (h2 : Q3T8.Asc77.S16.C22_2V) (h : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃)
    (hb : Q3T8.Asc77.S16.V3Ab Ω K) :
    alphaOf (Subgroup.closure ({u₂ * u₃, z} : Set G)) =
      alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) :=
  (h2 G Ω K K' K₃ z u₁ u₂ u₃ h hb).2 _ (Q3T8.Asc77.S22.closure_23_le h)
      (Q3T8.Asc77.S22.isElemAbelian2_closure_23 h)

theorem alpha_13V
    (h2 : Q3T8.Asc77.S16.C22_2V) (h : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃)
    (hb : Q3T8.Asc77.S16.V3Ab Ω K) :
    alphaOf (Subgroup.closure ({u₁ * u₃, z} : Set G)) =
      alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) :=
  (h2 G Ω K K' K₃ z u₁ u₂ u₃ h hb).2 _ (Q3T8.Asc77.S22.closure_13_le h)
      (Q3T8.Asc77.S22.isElemAbelian2_closure_13 h)

theorem oddCore_le_normalizer_alphaV
    (h2 : Q3T8.Asc77.S16.C22_2V)
    (h : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃) (hb : Q3T8.Asc77.S16.V3Ab Ω K) :
    oddCoreOf (Subgroup.centralizer ({z} : Set G)) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G) :=
  T7A.oddCore_le_normalizer_alpha (Q3T8.Asc77.Hyp22Setting.isElemAbelian_B h)
      (Q3T8.Asc77.S22.natCard_B h)
    (Q3T8.Asc77.S22.B_le_centralizer h) (h2 G Ω K K' K₃ z u₁ u₂ u₃ h hb).2

theorem third_le_normalizer_alphaV
    (h2 : Q3T8.Asc77.S16.C22_2V)
    (h : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃) (hb : Q3T8.Asc77.S16.V3Ab Ω K) :
    K₃ ≤ Subgroup.normalizer (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G) := by
  intro ℓ hℓ
  have hΩ : Q3T7M.HM Ω := h.stand.modU
  have hK : K ∈ Ω := h.stand.mem
  have hK' : K' ∈ Ω := h.hK'.1
  have hK₃Ω : K₃ ∈ Ω := h.hK₃.1
  have hℓC : ℓ ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (e189_commute_of_mem h.hzK₃ hℓ).symm
  have hzt : z * (u₁ * u₂) = (u₁ * u₂) * z :=
    (Commute.mul_left (h.comm_z₁.symm : Commute u₁ z) (h.comm_z₂.symm : Commute u₂ z)).eq.symm
  have hu₁C : u₁ ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr h.comm_z₁.symm
  have hsub := Q3T8.Asc77.T7A.isSubnormal_centralizer hΩ hK₃Ω h.hzK₃
  have hc₁ : ⁅u₁, ℓ⁆ ∈ oddCoreOf (Subgroup.centralizer ({z} : Set G)) := by
    have := hΩ.comm_le_oddCore_of_twin hK hK₃Ω h.hK₃K.symm h.hz h.hzK₃
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
    (Q3T8.Asc77.S16.oddCore_le_normalizer_alphaV h2 h hb)

theorem le_normalizer_alphaV
    (h2 : Q3T8.Asc77.S16.C22_2V) (h : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z
    u₁ u₂ u₃)
    (hb : Q3T8.Asc77.S16.V3Ab Ω K) :
    K ≤ Subgroup.normalizer (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G) ∧
    K' ≤ Subgroup.normalizer (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G) ∧
    K₃ ≤ Subgroup.normalizer (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G) := by
  refine ⟨?_, ?_, Q3T8.Asc77.S16.third_le_normalizer_alphaV h2 h hb⟩
  · have := Q3T8.Asc77.S16.third_le_normalizer_alphaV h2 (Q3T8.Asc77.S22.rotate h) (V3Ab.of_twin
      h.hz h.hK' hb)
    rwa [Q3T8.Asc77.S16.alpha_23V h2 h hb] at this
  · have := Q3T8.Asc77.S16.third_le_normalizer_alphaV h2 (Q3T8.Asc77.S22.rotate
      (Q3T8.Asc77.S22.rotate h)) (V3Ab.of_twin h.hz h.hK₃ hb)
    rwa [← Q3T8.Asc77.T7J.comm₁₃ h, Q3T8.Asc77.S16.alpha_13V h2 h hb] at this

theorem twin_le_normalizer_alphaV
    (h2 : Q3T8.Asc77.S16.C22_2V) (h : Q3T8.Asc77.Hyp22Setting Ω K K'
    K₃ z u₁ u₂ u₃)
    (hb : Q3T8.Asc77.S16.V3Ab Ω K) {L : Subgroup G} (hL : L ∈ twinSet Ω K) :
    L ≤ Subgroup.normalizer (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G) := by
  by_cases hLK : L = K
  · rw [hLK]
    exact (Q3T8.Asc77.S16.le_normalizer_alphaV h2 h hb).1
  by_cases hLK' : L = K'
  · rw [hLK']
    exact (Q3T8.Asc77.S16.le_normalizer_alphaV h2 h hb).2.1
  obtain ⟨w, hw⟩ := Q3T8.Asc77.S22.exists_replace_third h hL hLK hLK'
  exact Q3T8.Asc77.S16.third_le_normalizer_alphaV h2 hw hb
end Alpha
end S16
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
namespace S16
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.S16
set_option linter.unusedSectionVars false
open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.S22
open scoped commutatorElement
section Const
variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)}

theorem const_on_familyV
    (h2 : Q3T8.Asc77.S16.C22_2V) {K K' K₃ : Subgroup G} {z u₁ u₂ u₃ : G}
    (h : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃) (hb : Q3T8.Asc77.S16.V3Ab Ω K)
    {M₀ : Set (Subgroup G)} (hM₀ : M₀ ⊆ twinSet Ω K) (hKM : K ∈ M₀) (hK'M : K' ∈ M₀)
    (hK₃M : K₃ ∈ M₀) {Q : Subgroup G} (hQ : IsPGroup 2 ↥Q)
    (hSyl : ∀ M ∈ M₀, IsSylow2In (Q ⊓ M) M) :
    ∀ M₁ ∈ M₀, ∀ M₂ ∈ M₀, ∀ N₁ ∈ M₀, ∀ N₂ ∈ M₀, M₁ ≠ M₂ → N₁ ≠ N₂ →
      ∀ x ∈ Q ⊓ M₁, ∀ y ∈ Q ⊓ M₂, ∀ x' ∈ Q ⊓ N₁, ∀ y' ∈ Q ⊓ N₂,
        orderOf x = 4 → orderOf y = 4 → orderOf x' = 4 → orderOf y' = 4 →
        alphaOf (Subgroup.closure ({x * y, z} : Set G)) =
          alphaOf (Subgroup.closure ({x' * y', z} : Set G)) := by
  have hΩ : Q3T7M.HM Ω := h.stand.modU
  have hz : IsUniqueInvolution K z := h.hz
  have hKe : K' ≠ K := h.hne
  have hzM : ∀ M ∈ M₀, IsUniqueInvolution M z := fun M hM =>
    isUniqueInvolution_of_mem_twinSet hz (hM₀ hM)
  
  have hcomm : ∀ M ∈ M₀, ∀ M' ∈ M₀, M ≠ M' → Commutes (Q ⊓ M) (Q ⊓ M') := by
    intro M hM M' hM' hne
    exact hΩ.commutes_of_twin_of_isPGroup (hM₀ hM).1 (hM₀ hM').1 hne (hzM M hM) (hzM M' hM')
      inf_le_right inf_le_right
      (hQ.to_le (sup_le inf_le_left inf_le_left))
  let E : Type := Subgroup G × G
  let valid : E → Prop := fun a => a.1 ∈ M₀ ∧ a.2 ∈ Q ⊓ a.1 ∧ orderOf a.2 = 4
  let F : E → E → Subgroup G := fun a b => alphaOf (Subgroup.closure ({a.2 * b.2, z} : Set G))
  have key := T7B.const_of_triple (m := fun a : E => a.1) valid F
    (by
      intro a b ha hb' hne
      show alphaOf _ = alphaOf _
      rw [hcomm a.1 ha.1 b.1 hb'.1 hne a.2 ha.2.1 b.2 hb'.2.1])
    (by
      intro a b c ha hb' hc hab hbc hac
      have hLa : a.1 ∈ twinSet Ω K := hM₀ ha.1
      have hLb : b.1 ∈ twinSet Ω K := hM₀ hb'.1
      have hLc : c.1 ∈ twinSet Ω K := hM₀ hc.1
      have hperp' : KPerp Ω a.1 = twinSet Ω a.1 := Q3T8.Asc77.T7S22.perp_of_twin h hLa
      have hLb' : b.1 ∈ twinSet Ω a.1 := by
        rw [twinSet_eq_of_mem_twinSet hz hLa]; exact hLb
      have hLc' : c.1 ∈ twinSet Ω a.1 := by
        rw [twinSet_eq_of_mem_twinSet hz hLa]; exact hLc
      have hd := Q3T8.Asc77.S22.hyp22Setting_of_sylows (h.stand.of_mem hLa.1)
        (isUniqueInvolution_of_mem_twinSet hz hLa) hLb' (Ne.symm hab) hperp' hLc' (Ne.symm hac)
        (Ne.symm hbc) (hSyl a.1 ha.1) (hSyl b.1 hb'.1) (hSyl c.1 hc.1)
        (hcomm a.1 ha.1 b.1 hb'.1 hab) (hcomm a.1 ha.1 c.1 hc.1 hac)
        (hcomm b.1 hb'.1 c.1 hc.1 hbc) ha.2.1 hb'.2.1 hc.2.1 ha.2.2 hb'.2.2 hc.2.2
      exact (Q3T8.Asc77.S16.alpha_23V h2 hd (V3Ab.of_twin hz hLa hb)).symm)
    (by
      intro a b ha hb'
      obtain ⟨M, hM, hMa, hMb⟩ : ∃ M ∈ M₀, M ≠ a.1 ∧ M ≠ b.1 := by
        rcases T7B.exists_ne_of_three (a := a.1) (b := b.1) hKe h.hK₃K h.hK₃K' with h | h | h
        · exact ⟨K, hKM, h.1, h.2⟩
        · exact ⟨K', hK'M, h.1, h.2⟩
        · exact ⟨K₃, hK₃M, h.1, h.2⟩
      obtain ⟨w, hw, o⟩ := hΩ.exists_orderOf_eq_four_of_mem_RSet
        (mem_RSet_of_isSylow2In (hM₀ hM).1 (hSyl M hM))
      exact ⟨(M, w), ⟨hM, hw, o⟩, hMa, hMb⟩)
  intro M₁ hM₁ M₂ hM₂ N₁ hN₁ N₂ hN₂ hne hne' x hx y hy x' hx' y' hy' ox oy ox' oy'
  exact key (M₁, x) (M₂, y) (N₁, x') (N₂, y') ⟨hM₁, hx, ox⟩ ⟨hM₂, hy, oy⟩ ⟨hN₁, hx', ox'⟩
    ⟨hN₂, hy', oy'⟩ hne hne'
end Const
section Alpha
variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)}

theorem alpha_eq_of_datumV
    (h2 : Q3T8.Asc77.S16.C22_2V) {K K' K₃ L L' L₃ : Subgroup G}
    {z u₁ u₂ u₃ x₁ x₂ x₃ : G} (h : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃)
    (h' : Q3T8.Asc77.Hyp22Setting Ω L L' L₃ z x₁ x₂ x₃) (hb : Q3T8.Asc77.S16.V3Ab Ω K) :
    alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) =
      alphaOf (Subgroup.closure ({x₁ * x₂, z} : Set G)) := by
  have hΩ : Q3T7M.HM Ω := h.stand.modU
  have hz : IsUniqueInvolution K z := h.hz
  have hKV : K ∈ twinSet Ω K := mem_twinSet_self h.stand.mem hz
  have hK'V : K' ∈ twinSet Ω K := h.hK'
  have hK₃V : K₃ ∈ twinSet Ω K := h.hK₃
  have hLV : L ∈ twinSet Ω K := ⟨h'.stand.mem, z, hz, h'.hz⟩
  have hL'V : L' ∈ twinSet Ω K := ⟨h'.hK'.1, z, hz, h'.hzK'⟩
  have hL₃V : L₃ ∈ twinSet Ω K := ⟨h'.hK₃.1, z, hz, h'.hzK₃⟩
  have hVL : twinSet Ω L = twinSet Ω K := twinSet_eq_of_mem_twinSet hz hLV
  have hbL : Q3T8.Asc77.S16.V3Ab Ω L := V3Ab.of_twin hz hLV hb
  set X : Subgroup G := ⨆ M ∈ twinSet Ω K, M with hX
  have hXM : ∀ M ∈ twinSet Ω K, M ≤ X := fun M hM => le_iSup₂_of_le M hM le_rfl
  have hzV : ∀ M ∈ twinSet Ω K, IsUniqueInvolution M z := fun M hM =>
    isUniqueInvolution_of_mem_twinSet hz hM
  have hXz : X ≤ Subgroup.centralizer ({z} : Set G) := iSup₂_le fun M hM m hm =>
    Subgroup.mem_centralizer_singleton_iff.mpr (e189_commute_of_mem (hzV M hM) hm).symm
  have hXN : ∀ M ∈ twinSet Ω K, X ≤ Subgroup.normalizer (M : Set G) := by
    intro M hM
    refine iSup₂_le fun M' hM' => ?_
    by_cases hMM : M' = M
    · rw [hMM]
      exact Subgroup.le_normalizer
    · exact hΩ.le_normalizer_of_twin hM'.1 hM.1 hMM (hzV M' hM') (hzV M hM)
  have hXα : X ≤ Subgroup.normalizer
      (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G) :=
    iSup₂_le fun M hM => Q3T8.Asc77.S16.twin_le_normalizer_alphaV h2 h hb hM
  have hXα' : X ≤ Subgroup.normalizer
      (alphaOf (Subgroup.closure ({x₁ * x₂, z} : Set G)) : Set G) :=
    iSup₂_le fun M hM => Q3T8.Asc77.S16.twin_le_normalizer_alphaV h2 h' hbL (by rw [hVL]; exact hM)
  obtain ⟨R, R', R₃, hR, hR', hR₃, h₁, h₂, h₃, c12, c13, c23⟩ := Q3T8.Asc77.T7J.exists_sylow_triple
      h
  obtain ⟨S, S', S₃, hS, hS', hS₃, k₁, k₂, k₃, d12, d13, d23⟩ := Q3T8.Asc77.T7J.exists_sylow_triple
      h'
  have hT2 := T7B.isPGroup_sup_three hR.2.1 hR'.2.1 hR₃.2.1 c12 c13 c23
  have hT2' := T7B.isPGroup_sup_three hS.2.1 hS'.2.1 hS₃.2.1 d12 d13 d23
  obtain ⟨Q, hQ, hTQ⟩ := IsSylow2In.exists_ge hT2
    (sup_le (sup_le (hR.1.trans (hXM K hKV)) (hR'.1.trans (hXM K' hK'V)))
      (hR₃.1.trans (hXM K₃ hK₃V)))
  obtain ⟨Q', hQ', hTQ'⟩ := IsSylow2In.exists_ge hT2'
    (sup_le (sup_le (hS.1.trans (hXM L hLV)) (hS'.1.trans (hXM L' hL'V)))
      (hS₃.1.trans (hXM L₃ hL₃V)))
  obtain ⟨g, hgX, hgQ⟩ := exists_conjSub_eq_of_isSylow2In hQ' hQ
  have hgz : g * z * g⁻¹ = z := by
    have := Subgroup.mem_centralizer_singleton_iff.mp (hXz hgX)
    calc g * z * g⁻¹ = (z * g) * g⁻¹ := by rw [this]
      _ = z := by group
  have hgM : ∀ M ∈ twinSet Ω K, conjSub g M = M := fun M hM =>
    mem_normalizer_iff_conjSub_eq.mp (hXN M hM hgX)
  have h'' := Q3T8.Asc77.S22.conj h' hgz
  rw [hgM L hLV, hgM L' hL'V, hgM L₃ hL₃V] at h''
  have hαg : alphaOf (Subgroup.closure ({(g * x₁ * g⁻¹) * (g * x₂ * g⁻¹), z} : Set G)) =
      alphaOf (Subgroup.closure ({x₁ * x₂, z} : Set G)) := by
    have e : (g * x₁ * g⁻¹) * (g * x₂ * g⁻¹) = g * (x₁ * x₂) * g⁻¹ := by group
    have e2 := T7A.conjSub_closure_pair g (x₁ * x₂) z
    rw [hgz] at e2
    rw [e, ← e2, alphaOf_conjSub]
    exact mem_normalizer_iff_conjSub_eq.mp (hXα' hgX)
  have hQ2 : IsPGroup 2 ↥Q := hQ.2.1
  have hSylK : ∀ {M R₀ : Subgroup G}, IsSylow2In R₀ M → R₀ ≤ Q → IsSylow2In (Q ⊓ M) M := by
    intro M R₀ hR₀ hRQ
    have : Q ⊓ M = R₀ := hR₀.eq_of_le (hQ2.to_le inf_le_left) inf_le_right (le_inf hRQ hR₀.1)
    rw [this]
    exact hR₀
  have hSylL : ∀ {M R₀ : Subgroup G}, M ∈ twinSet Ω K → IsSylow2In R₀ M → R₀ ≤ Q' →
      IsSylow2In (conjSub g R₀) M ∧ conjSub g R₀ ≤ Q ⊓ M := by
    intro M R₀ hM hR₀ hRQ
    have h1 : IsSylow2In (conjSub g R₀) M := by
      have := hR₀.conj g
      rwa [hgM M hM] at this
    refine ⟨h1, le_inf ?_ h1.1⟩
    rw [← hgQ]
    exact conjSub_mono hRQ
  have hQL : ∀ {M R₀ : Subgroup G}, M ∈ twinSet Ω K → IsSylow2In R₀ M → R₀ ≤ Q' →
      IsSylow2In (Q ⊓ M) M := by
    intro M R₀ hM hR₀ hRQ
    obtain ⟨h1, h2'⟩ := hSylL hM hR₀ hRQ
    have : Q ⊓ M = conjSub g R₀ :=
      h1.eq_of_le (hQ2.to_le inf_le_left) inf_le_right h2'
    rw [this]
    exact h1
  have hRQ : ∀ {M₁ : Subgroup G}, M₁ ≤ (R ⊔ R') ⊔ R₃ → M₁ ≤ Q := fun hM => hM.trans hTQ
  have hSQ : ∀ {M₁ : Subgroup G}, M₁ ≤ (S ⊔ S') ⊔ S₃ → M₁ ≤ Q' := fun hM => hM.trans hTQ'
  have hRK : R ≤ Q := hRQ (le_sup_left.trans le_sup_left)
  have hRK' : R' ≤ Q := hRQ (le_sup_right.trans le_sup_left)
  have hRK₃ : R₃ ≤ Q := hRQ le_sup_right
  have hSL : S ≤ Q' := hSQ (le_sup_left.trans le_sup_left)
  have hSL' : S' ≤ Q' := hSQ (le_sup_right.trans le_sup_left)
  have hSL₃ : S₃ ≤ Q' := hSQ le_sup_right
  set M₀ : Set (Subgroup G) := {K, K', K₃, L, L', L₃} with hM₀
  have hM₀V : M₀ ⊆ twinSet Ω K := by
    intro M hM
    rcases hM with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hKV
    · exact hK'V
    · exact hK₃V
    · exact hLV
    · exact hL'V
    · exact hL₃V
  have hSyl : ∀ M ∈ M₀, IsSylow2In (Q ⊓ M) M := by
    intro M hM
    rcases hM with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hSylK hR hRK
    · exact hSylK hR' hRK'
    · exact hSylK hR₃ hRK₃
    · exact hQL hLV hS hSL
    · exact hQL hL'V hS' hSL'
    · exact hQL hL₃V hS₃ hSL₃
  have hconj₁ : g * x₁ * g⁻¹ ∈ Q ⊓ L := (hSylL hLV hS hSL).2 (conj_mem_conjSub k₁)
  have hconj₂ : g * x₂ * g⁻¹ ∈ Q ⊓ L' := (hSylL hL'V hS' hSL').2 (conj_mem_conjSub k₂)
  have hu₁ : u₁ ∈ Q ⊓ K := ⟨hRK h₁, hR.1 h₁⟩
  have hu₂ : u₂ ∈ Q ⊓ K' := ⟨hRK' h₂, hR'.1 h₂⟩
  have ho₁ : orderOf (g * x₁ * g⁻¹) = 4 := by rw [T7B.orderOf_conj']; exact h'.hu₁.2
  have ho₂ : orderOf (g * x₂ * g⁻¹) = 4 := by rw [T7B.orderOf_conj']; exact h'.hu₂.2
  have hmain := Q3T8.Asc77.S16.const_on_familyV h2 h hb hM₀V
    (by simp [hM₀]) (by simp [hM₀]) (by simp [hM₀]) hQ2 hSyl K (by simp [hM₀]) K'
    (by simp [hM₀]) L (by simp [hM₀]) L' (by simp [hM₀]) h.hne.symm h'.hne.symm u₁ hu₁
    u₂ hu₂ _ hconj₁ _ hconj₂ h.hu₁.2 h.hu₂.2 ho₁ ho₂
  rw [hmain, hαg]

theorem centralizer_le_normalizer_alphaV
    (h2 : Q3T8.Asc77.S16.C22_2V) {K K' K₃ : Subgroup G}
    {z u₁ u₂ u₃ : G} (h : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃) (hb : Q3T8.Asc77.S16.V3Ab Ω
        K) :
    Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G) := by
  intro c hc
  have hcz : c * z * c⁻¹ = z := by
    have := Subgroup.mem_centralizer_singleton_iff.mp hc
    calc c * z * c⁻¹ = (z * c) * c⁻¹ := by rw [this]
      _ = z := by group
  have hd := Q3T8.Asc77.S22.conj h hcz
  have heq := (Q3T8.Asc77.S16.alpha_eq_of_datumV h2 h hd hb).symm
  have e : (c * u₁ * c⁻¹) * (c * u₂ * c⁻¹) = c * (u₁ * u₂) * c⁻¹ := by group
  have e2 := T7A.conjSub_closure_pair c (u₁ * u₂) z
  rw [hcz] at e2
  rw [e, ← e2, alphaOf_conjSub] at heq
  exact mem_normalizer_iff_conjSub_eq.mpr heq
end Alpha
end S16
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
namespace S16
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.S16
set_option linter.unusedSectionVars false
open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.S22
open scoped commutatorElement
section Main
variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)} {K K' K₃ : Subgroup G} {z u₁ u₂ u₃ : G}

theorem false_of_abelianV
    (hE : Q3T7E.ThmEWithSylow3) (h2 : Q3T8.Asc77.S16.C22_2V)
    (h : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃) (hb : Q3T8.Asc77.S16.V3Ab Ω K)
    (hsig : ∀ J ∈ dstarComp Ω K, J ∈ twinSet Ω K)
    (hcent : ∀ {L L' L₃ : Subgroup G} {x y w : G}, Q3T8.Asc77.Hyp22Setting Ω L L' L₃ z x y w →
      Subgroup.centralizer ({x * y} : Set G) ≤
        alphaOf (Subgroup.closure ({x * y, z} : Set G)) ⊔
          (Subgroup.centralizer ({x * y} : Set G) ⊓ Subgroup.centralizer ({z} : Set G))) :
    False := by
  have hΩ : Q3T7M.HM Ω := h.stand.modU
  have hK : K ∈ Ω := h.stand.mem
  
  have hcentD : ∀ {L L' L₃ : Subgroup G} {x y w : G}, Q3T8.Asc77.Hyp22Setting Ω L L' L₃ z x y w →
      Subgroup.centralizer ({x * y} : Set G) ≤
        Subgroup.normalizer (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G) ∧
      (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) = ⊥ →
        Subgroup.centralizer ({x * y} : Set G) ≤ Subgroup.centralizer ({z} : Set G)) := by
    intro L L' L₃ x y w hd
    have hc := hcent hd
    have heq := (Q3T8.Asc77.S16.alpha_eq_of_datumV h2 h hd hb).symm
    refine ⟨fun c hcC => ?_, fun hα => ?_⟩
    · have hinf : Subgroup.centralizer ({x * y} : Set G) ⊓ Subgroup.centralizer ({z} : Set G) ≤
          Subgroup.normalizer (alphaOf (Subgroup.closure ({x * y, z} : Set G)) : Set G) := by
        intro c' hc'
        have ha : c' * (x * y) = (x * y) * c' :=
          Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hc').1
        have hb' : c' * z = z * c' :=
          Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hc').2
        exact T7B.centralizer_le_normalizer_alphaOf _
          (T7B.mem_centralizer_closure_pair ha.symm hb'.symm)
      have h1 : c ∈ Subgroup.normalizer
          (alphaOf (Subgroup.closure ({x * y, z} : Set G)) : Set G) :=
        (sup_le Subgroup.le_normalizer hinf) (hc hcC)
      rwa [heq] at h1
    · rw [← heq] at hα
      rw [hα, bot_sup_eq] at hc
      exact hc.trans inf_le_right
  have htwin : ∀ L ∈ twinSet Ω K, ∀ L' ∈ twinSet Ω K, L' ≠ L → ∀ R₁ R₂ : Subgroup G,
      IsSylow2In R₁ L → IsSylow2In R₂ L' → Commutes R₁ R₂ → ∀ x ∈ R₁, ∀ y ∈ R₂,
        orderOf x = 4 → orderOf y = 4 →
          ∃ (L₃ : Subgroup G) (w : G), Q3T8.Asc77.Hyp22Setting Ω L L' L₃ z x y w :=
    fun L hL L' hL' hne R₁ R₂ hR₁ hR₂ hc x hx y hy ox oy =>
      Q3T8.Asc77.S22.exists_datum_of_pair h hL hL' hne hR₁ hR₂ hc hx hy ox oy
  
  have hstd1 : StdCent Ω K (Subgroup.normalizer
      (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G)) z :=
    Q3T8.Asc77.S22.stdCent_of_twin h (Q3T8.Asc77.S16.centralizer_le_normalizer_alphaV h2 h hb)
      fun L hL L' hL' hne R₁ R₂ hR₁ hR₂ hc x hx y hy ox oy => by
        obtain ⟨L₃, w, hd⟩ := htwin L hL L' hL' hne R₁ R₂ hR₁ hR₂ hc x hx y hy ox oy
        exact (hcentD hd).1
  have htrans1 : ∀ J ∈ dstarComp Ω K, ∃ c ∈ Subgroup.normalizer
      (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G), conjSub c K = J := by
    intro J hJ
    obtain ⟨c, hc, hcJ⟩ := Q3T8.Asc77.S22.exists_centralizer_conj h (hsig J hJ)
    exact ⟨c, Q3T8.Asc77.S16.centralizer_le_normalizer_alphaV h2 h hb hc, hcJ⟩
  have htop1 := Q3T8.Asc77.thmE_apply hE h.stand h.hz h.hK' h.hne hstd1 htrans1
  have hα : alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) = ⊥ :=
    T7B.eq_bot_of_normalizer_eq_top (h2 G Ω K K' K₃ z u₁ u₂ u₃ h hb).1 htop1
      (T7B.two_dvd_natCard h.hz)
  
  have hstd2 : StdCent Ω K (Subgroup.centralizer ({z} : Set G)) z :=
    Q3T8.Asc77.S22.stdCent_of_twin h le_rfl fun L hL L' hL' hne R₁ R₂ hR₁ hR₂ hc x hx y hy ox oy =>
        by
      obtain ⟨L₃, w, hd⟩ := htwin L hL L' hL' hne R₁ R₂ hR₁ hR₂ hc x hx y hy ox oy
      exact (hcentD hd).2 hα
  have htrans2 : ∀ J ∈ dstarComp Ω K, ∃ c ∈ Subgroup.centralizer ({z} : Set G),
      conjSub c K = J := fun J hJ => Q3T8.Asc77.S22.exists_centralizer_conj h (hsig J hJ)
  have htop2 := Q3T8.Asc77.thmE_apply hE h.stand h.hz h.hK' h.hne hstd2 htrans2
  
  obtain ⟨V, hV, -⟩ := IsSylow2In.exists_ge (isPGroup_two_bot (G := G)) (bot_le : ⊥ ≤ K)
  obtain ⟨x, -, y, -, hxy⟩ :=
    (hΩ.isQuatSub_of_mem_RSet (mem_RSet_of_isSylow2In hK hV)).exists_not_commute
  have hz1 : z = 1 := T7B.eq_one_of_central ⟨x, y, hxy⟩ fun g => by
    have : g ∈ Subgroup.centralizer ({z} : Set G) := by rw [htop2]; exact Subgroup.mem_top g
    exact Subgroup.mem_centralizer_singleton_iff.mp this
  exact h.hz.ne_one hz1
end Main
end S16
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
namespace S16
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.S16
set_option linter.unusedSectionVars false
open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
section Final

theorem hyp22FourthTwinAb_of_z2 [Fact Q3T7E.ThmEWithSylow3] [Fact
    CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.Hyp22Hyp51z] [Fact
    CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S16.M11NoInverted3] (hR1 : Q3T8.Asc77.S16.Z2NoD8) :
    Q3T8.Asc77.S22.Hyp22FourthTwinAb := by
  intro G _ _ _ Ω K K' K₃ z u₁ u₂ u₃ h heq
  by_contra hcon
  push Not at hcon
  have hnb : ¬ S22.Big Ω K := fun hb => by
    obtain ⟨t, ht, h1, h2, h3⟩ := hb.fourth K K' K₃
    exact h3 (hcon t ht h1 h2)
  have hsig : ∀ J ∈ dstarComp Ω K, J ∈ twinSet Ω K := fun J hJ =>
    Q3T8.Asc77.T7S22.dComp_subset_twinSet h (by rw [heq]; exact hJ)
  have hAall := Q3T8.Asc77.S22.hAall_of_dstarComp h hsig
  have hv : Q3T8.Asc77.S16.V3Ab Ω K := ⟨hnb, hAall⟩
  have hNT : CFSG.ClassicalInvolution.G2D4Models.G2NonToralGenerate 3 :=
    CFSG.ClassicalInvolution.G2D4Models.g2NonToralGenerate_all
  have hE : Q3T7E.ThmEWithSylow3 := Q3T8.Asc77.thmEWithSylow_of_nonToral hNT
  refine Q3T8.Asc77.S16.false_of_abelianV hE (Q3T8.Asc77.S16.c22_2V hR1) h hv hsig ?_
  intro L L' L₃ x y w hd
  have hLV : L ∈ twinSet Ω K := ⟨hd.stand.mem, z, h.hz, hd.hz⟩
  have hv' : Q3T8.Asc77.S16.V3Ab Ω L := hv.of_twin h.hz hLV
  exact Q3T8.Asc77.S22.cent_of_zstar hd (Q3T8.Asc77.S16.layer_zStar hR1 hd (hv'.hV3 hd) hv'.2)
end Final
end S16
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
namespace S16
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.S16
set_option linter.unusedSectionVars false
open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic CFSG.LieType.Universal
    CFSG.ClassicalInvolution.Asc77.FrameVertex CFSG.ClassicalInvolution.Disconnected
    CFSG.ClassicalInvolution.Disconnected.AschTight
section Final

theorem hyp22FourthTwinAb_proved [Fact Q3T7E.ThmEWithSylow3] [Fact
    CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.Hyp22Hyp51z] [Fact
    CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S16.M11NoInverted3] : Q3T8.Asc77.S22.Hyp22FourthTwinAb :=
  Q3T8.Asc77.S16.hyp22FourthTwinAb_of_z2 Q3T8.Asc77.S16.z2NoD8
end Final
end S16
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
namespace C22G
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.C22G

theorem c22_8Gen_of_alpha [Fact Q3T7E.ThmEWithSylow3] (h4 : Q3T8.Asc77.Hyp22FourTwins) (hF :
    Q3T8.Asc77.Hyp22Fuse) (h7 : Q3T8.Asc77.C22_7) :
    Q3T8.Asc77.C22_8Gen :=
  Q3T8.Asc77.C22G.c22_8Gen_of_layerStar (Q3T8.Asc77.C22G.c22_layerStar_of_alpha h4 hF h7)

theorem c22_8Gen_of_c22_7 [Fact Q3T7E.ThmEWithSylow3] [Fact
    CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.Hyp22Hyp51z] [Fact
    CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S16.M11NoInverted3] [Fact
    CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.Hyp22Hyp51u] (h7 : Q3T8.Asc77.C22_7) :
    Q3T8.Asc77.C22_8Gen :=
  let hW := Q3T8.Asc77.S22.hyp22SettingWyl_of_ab (Q3T8.Asc77.S16.hyp22FourthTwinAb_proved)
  Q3T8.Asc77.C22G.c22_8Gen_of_alpha (Q3T8.Asc77.T7V.hyp22FourTwins_of_wyl hW)
      (Q3T8.Asc77.T7V.hyp22Fuse_of_wyl hW) h7
end C22G
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
    CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
    CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Disconnected
namespace C22P
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.C22P
set_option linter.unusedSectionVars false
section Norm
variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)} {K K' K₃ : Subgroup G} {z u₁ u₂ u₃ : G}

theorem normY_of_hyp22 [Fact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.Hyp22Hyp51z] [Fact
    CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.Hyp22Hyp51u] [Fact Q3T7E.ThmEWithSylow3] [Fact
    CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S16.M11NoInverted3] (hq1 : 3 % 4 = 1) (h :
    Q3T8.Asc77.Hyp22 Ω K K' K₃ z u₁ u₂ u₃) :
    rLayer Ω (u₁ * u₂) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G) :=
  absurd hq1 (by norm_num)
end Norm
end C22P
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
namespace C22G
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.C22G
set_option linter.unusedSectionVars false

theorem c22_2_proved [Fact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.Hyp22Hyp51z] [Fact
    CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.Hyp22Hyp51u] (h4 : Q3T8.Asc77.Hyp22FourTwins) :
    Q3T8.Asc77.C22_2 :=
  Q3T8.Asc77.c22_2_of (Q3T8.Asc77.hyp22Hyp51z)
    (Q3T8.Asc77.hyp22Hyp51u_of_fourthTwin (twinSqAlphaRows_of_orth 3 (twinSqOrth_proved 3))
      (Q3T8.Asc77.hyp22FourthTwin_of_fourTwins h4))

theorem c22_7_of_layerNormAlpha_proved [Fact Q3T7E.ThmEWithSylow3] [Fact
    CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.Hyp22Hyp51z] [Fact
    CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.Hyp22Hyp51u] [Fact
    CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S16.M11NoInverted3] (hY :
    Q3T8.Asc77.C22G.C22_layerNormAlpha) : Q3T8.Asc77.C22_7 :=
  let hW := Q3T8.Asc77.S22.hyp22SettingWyl_of_ab (Q3T8.Asc77.S16.hyp22FourthTwinAb_proved)
  let h4 := Q3T8.Asc77.T7V.hyp22FourTwins_of_wyl hW
  Q3T8.Asc77.C22G.c22_7_of_layerNormAlpha
    (Q3T8.Asc77.thmEWithSylow_of_nonToral G2D4Models.g2NonToralGenerate_all) h4
    (Q3T8.Asc77.T7V.hyp22Fuse_of_wyl hW) (Q3T8.Asc77.C22G.c22_2_proved h4)
    (fun G _ _ _ Ω K K' K₃ z u₁ u₂ u₃ h => hW G Ω K K' K₃ z u₁ u₂ u₃ h.setting) hY

theorem c22_8Gen_of_layerNormAlpha [Fact Q3T7E.ThmEWithSylow3] [Fact
    CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.Hyp22Hyp51z] [Fact
    CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.Hyp22Hyp51u] [Fact
    CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S16.M11NoInverted3] (hY :
    Q3T8.Asc77.C22G.C22_layerNormAlpha) : Q3T8.Asc77.C22_8Gen :=
  Q3T8.Asc77.C22G.c22_8Gen_of_c22_7 (Q3T8.Asc77.C22G.c22_7_of_layerNormAlpha_proved hY)
end C22G
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
    CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
    CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Disconnected
namespace C22G
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.C22G
set_option linter.unusedSectionVars false
section Norm
variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)} {K K' K₃ K₄ : Subgroup G} {z u₁ u₂ u₃ : G}

theorem c22_gen_frame_psu [Fact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.C22G.PsuLayerApi3] (hq3 : 3
    % 4 = 3)
    (hs : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃) (hW : ∀ W ∈ WSet Ω, MuIsoWylD4 Ω W)
    (hK₄ : K₄ ∈ twinSet Ω K) (h41 : K₄ ≠ K) (h42 : K₄ ≠ K') (h43 : K₄ ≠ K₃)
    {R R' : Subgroup G} {b b' y : G} (hF : Q3T8.Asc77.C22P.FrameData Ω K₃ K₄ z (u₁ * u₂) R R' b b'
        y) :
    Q3T8.Asc77.ExactLayer.exactLayer Ω (u₁ * u₂) ≤
      (conjSub y K₄ ⊔ K₃ ⊔ conjSub y K₃ ⊔ K₄) ⊔ oddCoreOf (Q3T8.Asc77.ExactLayer.exactLayer Ω (u₁ *
          u₂)) := by
  have hΩ : Q3T7M.HM Ω := hs.stand.modU
  have hKΩ : K ∈ Ω := hs.stand.mem
  have hK'Ω : K' ∈ Ω := hs.hK'.1
  have hK₃Ω : K₃ ∈ Ω := hs.hK₃.1
  have hK₄Ω : K₄ ∈ Ω := hK₄.1
  have hz : IsUniqueInvolution K z := hs.hz
  have hzK' : IsUniqueInvolution K' z := hs.hzK'
  have hzK₃ : IsUniqueInvolution K₃ z := hs.hzK₃
  have hzK₄ : IsUniqueInvolution K₄ z := isUniqueInvolution_of_mem_twinSet hz hK₄
  have hπ : piSign 3 1 = false := by unfold piSign; simp [hq3]
  set u : G := u₁ * u₂ with hu
  have hu2 : u * u = 1 := hs.sq_12
  have hc2' : IsPGroup 2 (Subgroup.zpowers u) :=
      Q3T8.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hu2
  
  obtain ⟨K₄', hK₄', -, -, -, hV'⟩ := Q3T8.Asc77.C22P.fourTwins_S hs hW
  have hV : ∀ M ∈ twinSet Ω K, M = K ∨ M = K' ∨ M = K₃ ∨ M = K₄ := by
    intro M hM
    have hK₄eq : K₄ = K₄' := by
      rcases hV' K₄ hK₄ with h | h | h | h
      · exact absurd h h41
      · exact absurd h h42
      · exact absurd h h43
      · exact h
    rcases hV' M hM with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (h.trans hK₄eq.symm)))
  have hK₃t : K₃ ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω u := Q3T8.Asc77.C22P.mem_tqMembers_of_twin hs
      hs.hK₃ hs.hK₃K hs.hK₃K'
  have hK₄t : K₄ ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω u := Q3T8.Asc77.C22P.mem_tqMembers_of_twin hs
      hK₄ h41 h42
  have hyc : y ∈ Subgroup.centralizer ({u} : Set G) :=
      Q3T8.Asc77.ExactLayer.exactLayer_le_centralizer Ω u hF.hy
  have hJt : conjSub y K₃ ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω u :=
      Q3T8.Asc77.ExactLayer.conjSub_mem_tqMembers hΩ.conjInvariant hyc hK₃t
  have hJ't : conjSub y K₄ ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω u :=
      Q3T8.Asc77.ExactLayer.conjSub_mem_tqMembers hΩ.conjInvariant hyc hK₄t
  
  have hu₂K : u₂ ∈ trivialOnQuot K :=
    Q3T8.Asc77.T7J.twin_le_trivialOnQuot hΩ hK'Ω hKΩ hs.hne hzK' hz hs.hu₂.1
  have hu₁K' : u₁ ∈ trivialOnQuot K' :=
    Q3T8.Asc77.T7J.twin_le_trivialOnQuot hΩ hKΩ hK'Ω hs.hne.symm hz hzK' hs.hu₁.1
  have hnotK : K ∉ Q3T8.Asc77.ExactLayer.tqMembers Ω u :=
    Q3T8.Asc77.T7J.not_mem_tqMembers_of_mul hΩ hKΩ hz hs.hu₁.1 hs.hu₁.2 hu₂K hu
  have hnotK' : K' ∉ Q3T8.Asc77.ExactLayer.tqMembers Ω u :=
    Q3T8.Asc77.T7J.not_mem_tqMembers_of_mul hΩ hK'Ω hzK' hs.hu₂.1 hs.hu₂.2 hu₁K'
      (by rw [hu]; exact hs.comm₁₂)
  have hperp : ∀ J ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω u, J ∈ KPerp Ω K₃ → J = K₃ ∨ J = K₄ := by
    intro J hJt₀ hJperp
    rw [Q3T8.Asc77.T7S22.perp_of_twin hs hs.hK₃, twinSet_eq_of_mem_twinSet hz hs.hK₃] at hJperp
    rcases hV J hJperp with h | h | h | h
    · rw [h] at hJt₀
      exact absurd hJt₀ hnotK
    · rw [h] at hJt₀
      exact absurd hJt₀ hnotK'
    · exact Or.inl h
    · exact Or.inr h
  
  have hex₃ : IsSylow2In R (Q3T8.Asc77.ExactLayer.exactCore u K₃) :=
    (Q3T8.Asc77.ExactLayer.isSylow2In_exactCore_iff hΩ hc2' hK₃Ω hK₃t.2).mpr ⟨hF.hR, hF.hRc⟩
  have hex₄ : IsSylow2In R' (Q3T8.Asc77.ExactLayer.exactCore u K₄) :=
    (Q3T8.Asc77.ExactLayer.isSylow2In_exactCore_iff hΩ hc2' hK₄Ω hK₄t.2).mpr ⟨hF.hR', hF.hR'c⟩
  have htJ : IsUniqueInvolution (conjSub y K₃) (b * b' * u) := hF.hyz ▸ hzK₃.conj y
  have htJ' : IsUniqueInvolution (conjSub y K₄) (b * b' * u) := hF.hyz ▸ hzK₄.conj y
  
  have hperp' : ∀ J ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω u, J ∈ KPerp Ω K₄ → J = K₄ ∨ J = K₃ := by
    intro J hJt₀ hJperp
    rw [Q3T8.Asc77.T7S22.perp_of_twin hs hK₄, twinSet_eq_of_mem_twinSet hz hK₄] at hJperp
    rcases hV J hJperp with h | h | h | h
    · rw [h] at hJt₀
      exact absurd hJt₀ hnotK
    · rw [h] at hJt₀
      exact absurd hJt₀ hnotK'
    · exact Or.inr h
    · exact Or.inl h
  have hBelow : Q3T8.Generic.CITBelowU (Nat.card G) := hs.stand.below
  have hMz : Q3T8.Generic.IsClassicalMember K₃ z := Q3T8.Asc77.isClassicalMember_of_twin hΩ hK₃Ω
      hzK₃
  have hu1 : u ≠ 1 :=
    (Q3T8.Asc77.T7S22.mul_ne_one_of_twins hΩ hKΩ hK'Ω hs.hne.symm hz hs.hu₁.1 hs.hu₂.1 hs.hu₂.2).1
  have hnc : ¬ ({u} : Set G) ⊆ Subgroup.center G :=
    Balance.not_subset_center_of_ne_one (Q3T8.Asc77.exists_noncomm_of_isClassicalMember hMz) hu1
  have hLay : Q3T8.Asc77.LayerOrthType Ω u 6 false := by
    have h := Q3T8.Asc77.T7J.layer_orth_six_weak_proved hΩ hBelow hu2 hnc hK₃t hK₄t hJt hzK₃ hzK₄
      hperp hperp' htJ hF.hzt hF.htz hex₃ hex₄ hF.hRR' (hex₃.1 hF.hbR) (hex₄.1 hF.hb'R') hF.hbz
      hF.hb'z rfl
    rwa [hπ] at h
  have hgen := Q3T8.Asc77.C22G.layer_gen_psu hΩ hu2 hLay hK₃t hK₄t hJt hJ't hzK₃ hzK₄ hperp htJ
      htJ' hF.hzt
    hF.htz hex₃ hex₄ hF.hRR' (hex₃.1 hF.hbR) (hex₄.1 hF.hb'R') hF.hbz rfl hF.hy rfl rfl
  exact hgen.trans (sup_le_sup_right le_sup_left _)

theorem normY_of_hyp22Setting_psu [Fact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.C22G.PsuLayerApi3]
    [Fact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.Hyp22Hyp51z] [Fact
    CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.Hyp22Hyp51u] [Fact Q3T7E.ThmEWithSylow3] [Fact
    CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S16.M11NoInverted3] (hq3 : 3 % 4 = 3)
    (hs : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃) :
    rLayer Ω (u₁ * u₂) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G) := by
  have hΩ : Q3T7M.HM Ω := hs.stand.modU
  have hW : ∀ W ∈ WSet Ω, MuIsoWylD4 Ω W :=
    Q3T8.Asc77.S22.hyp22SettingWyl_of_ab (Q3T8.Asc77.S16.hyp22FourthTwinAb_proved) G Ω K K' K₃ z u₁
        u₂ u₃ hs
  obtain ⟨K₄, hK₄, h41, h42, h43, -⟩ := Q3T8.Asc77.C22P.fourTwins_S hs hW
  have hbig : S22.Big Ω K := Q3T8.Asc77.S22.Big.of_four hs hK₄ h41 h42 h43
  obtain ⟨R, R', b, b', y, hF, hyα⟩ := Q3T8.Asc77.C22P.frame_at_alpha hs hK₄ h41 h42 h43 hW
  have hgen := Q3T8.Asc77.C22G.c22_gen_frame_psu hq3 hs hW hK₄ h41 h42 h43 hF
  have h2 := Q3T8.Asc77.S22.c22_2S
  set α₀ := alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) with hα₀
  have hK₃N : K₃ ≤ Subgroup.normalizer (α₀ : Set G) :=
    Q3T8.Asc77.S22.twin_le_normalizer_alpha h2 hs hbig hs.hK₃
  have hK₄N : K₄ ≤ Subgroup.normalizer (α₀ : Set G) :=
    Q3T8.Asc77.S22.twin_le_normalizer_alpha h2 hs hbig hK₄
  have hconjN : ∀ {M : Subgroup G}, M ≤ Subgroup.normalizer (α₀ : Set G) →
      conjSub y M ≤ Subgroup.normalizer (α₀ : Set G) := by
    intro M hM x hx
    rw [mem_conjSub_iff] at hx
    have e : x = y * (y⁻¹ * x * y) * y⁻¹ := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hyα (hM hx)) (Subgroup.inv_mem _ hyα)
  have hu2 : (u₁ * u₂) * (u₁ * u₂) = 1 := hs.sq_12
  have hOle : oddCoreOf (Q3T8.Asc77.ExactLayer.exactLayer Ω (u₁ * u₂)) ≤
      oddCoreOf (Subgroup.centralizer ({u₁ * u₂} : Set G)) := by
    refine T8.oddCoreOf_le_oddCoreOf_of_normalized (Q3T8.Asc77.ExactLayer.exactLayer_le_centralizer
        Ω (u₁ * u₂))
      (fun c hc => ?_)
    have hcu : c * (u₁ * u₂) * c⁻¹ = u₁ * u₂ := by
      have := Subgroup.mem_centralizer_singleton_iff.mp hc
      calc c * (u₁ * u₂) * c⁻¹ = ((u₁ * u₂) * c) * c⁻¹ := by rw [← this]
        _ = u₁ * u₂ := by group
    rw [← Q3T8.Asc77.ExactLayer.exactLayer_conj hΩ.conjInvariant c (u₁ * u₂), hcu]
  have hO : oddCoreOf (Q3T8.Asc77.ExactLayer.exactLayer Ω (u₁ * u₂)) ≤ Subgroup.normalizer (α₀ :
      Set G) :=
    hOle.trans (Q3T8.Asc77.C22P.oddCore_centralizer_le_normalizer_alpha hs hbig)
  exact (Q3T8.Asc77.rLayer_le_exactLayer hΩ hu2).trans
    (hgen.trans (sup_le (sup_le (sup_le (sup_le (hconjN hK₄N) hK₃N) (hconjN hK₃N)) hK₄N) hO))

theorem normY_of_hyp22_psu [Fact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.C22G.PsuLayerApi3] [Fact
    CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.Hyp22Hyp51z] [Fact
    CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.Hyp22Hyp51u] [Fact Q3T7E.ThmEWithSylow3] [Fact
    CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S16.M11NoInverted3] (hq3 : 3 % 4 = 3) (h :
    Q3T8.Asc77.Hyp22 Ω K K' K₃ z u₁ u₂ u₃) :
    rLayer Ω (u₁ * u₂) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G) :=
  Q3T8.Asc77.C22G.normY_of_hyp22Setting_psu hq3 h.setting
end Norm
end C22G
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
namespace C22G
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.C22G
set_option linter.unusedSectionVars false
section Final

theorem c22_layerNormAlpha_proved [Fact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.C22G.PsuLayerApi3]
    [Fact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.Hyp22Hyp51z] [Fact
    CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.Hyp22Hyp51u] [Fact Q3T7E.ThmEWithSylow3] [Fact
    CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S16.M11NoInverted3] : Q3T8.Asc77.C22G.C22_layerNormAlpha
    := by
  intro G _ _ _ Ω K K' K₃ z u₁ u₂ u₃ h
  have hp2 : 3 % 2 = 1 := by norm_num
  have hodd : 3 % 2 = 1 := by norm_num
  have h4 : 3 % 4 = 1 ∨ 3 % 4 = 3 := by omega
  rcases h4 with h1 | h3
  · exact Q3T8.Asc77.C22P.normY_of_hyp22 h1 h
  · exact Q3T8.Asc77.C22G.normY_of_hyp22_psu h3 h

theorem c22_8Gen_proved [Fact Q3T7E.ThmEWithSylow3] [Fact
    CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.Hyp22Hyp51z] [Fact
    CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.Hyp22Hyp51u] [Fact
    CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S16.M11NoInverted3] [Fact
    CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.C22G.PsuLayerApi3] : Q3T8.Asc77.C22_8Gen :=
    Q3T8.Asc77.C22G.c22_8Gen_of_layerNormAlpha Q3T8.Asc77.C22G.c22_layerNormAlpha_proved
end Final
end C22G
end Asc77

end

end CFSG.ClassicalInvolution.Q3.Q3T8
