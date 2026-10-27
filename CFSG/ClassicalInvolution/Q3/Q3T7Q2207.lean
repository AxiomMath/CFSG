module

public import CFSG.ClassicalInvolution.Q3.Q3T7Q22TSFProof
public import CFSG.ClassicalInvolution.Q3.Q3T7Q22UComp
public import CFSG.ClassicalInvolution.Q3.Q3T7Q2206

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
namespace S22
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.S22
set_option linter.unusedSectionVars false
open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement
section Statement

@[expose] def C22_2S
    : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' K₃ : Subgroup G) (z u₁ u₂ u₃ : G), Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃ →
      Big Ω K →
      Odd (Nat.card ↥(alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)))) ∧
        ∀ A : Subgroup G, A ≤ Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G) →
          IsElemAbelian2 A 2 →
            alphaOf A = alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G))
end Statement
section Hyp51u
variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)} {K K' K₃ : Subgroup G} {z u₁ u₂ u₃ : G}

theorem hyp51u_of_four [Fact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.Hyp22Hyp51u] (h :
    Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃) {K₄ : Subgroup G}
    (hK₄ : K₄ ∈ twinSet Ω K) (hK₄K : K₄ ≠ K) (hK₄K' : K₄ ≠ K') (hK₄K₃ : K₄ ≠ K₃) :
    ∀ c ∈ Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G), c ≠ 1 → c ≠ z →
      Hyp51At (Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G)) c := by
  intro c hc hc1 hcz
  exact (Fact.out : Q3T8.Asc77.Hyp22Hyp51u) G Ω K K' K₃ z u₁ u₂ u₃ h c hc hc1 hcz
end Hyp51u
section C22

theorem c22_2S [Fact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.Hyp22Hyp51z] [Fact
    CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.Hyp22Hyp51u] : Q3T8.Asc77.S22.C22_2S := by
  intro G _ _ _ Ω K K' K₃ z u₁ u₂ u₃ h hb
  obtain ⟨K₄, hK₄, h1, h2, h3⟩ := hb.fourth K K' K₃
  have hB : Hyp51 (Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G)) := by
    refine ⟨Q3T8.Asc77.Hyp22Setting.isElemAbelian_B h, Q3T8.Asc77.S22.natCard_B h, fun c hc hc1 =>
        ?_⟩
    by_cases hcz : c = z
    · rw [hcz]
      exact Q3T8.Asc77.hyp22Hyp51z G Ω K K' K₃ z u₁ u₂ u₃ h
    · exact Q3T8.Asc77.S22.hyp51u_of_four h hK₄ h1 h2 h3 c hc hc1 hcz
  exact lemma54_odd_and_eq hB (Q3T8.Asc77.S22.closure_12_le h)
      (Q3T8.Asc77.S22.isElemAbelian2_closure h)
end C22
section Alpha
variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)} {K K' K₃ : Subgroup G} {z u₁ u₂ u₃ : G}

theorem alpha_23
    (h2 : Q3T8.Asc77.S22.C22_2S) (h : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃)
    (hb : Big Ω K) :
    alphaOf (Subgroup.closure ({u₂ * u₃, z} : Set G)) =
      alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) :=
  (h2 G Ω K K' K₃ z u₁ u₂ u₃ h hb).2 _ (Q3T8.Asc77.S22.closure_23_le h)
      (Q3T8.Asc77.S22.isElemAbelian2_closure_23 h)

theorem alpha_13
    (h2 : Q3T8.Asc77.S22.C22_2S) (h : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃)
    (hb : Big Ω K) :
    alphaOf (Subgroup.closure ({u₁ * u₃, z} : Set G)) =
      alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) :=
  (h2 G Ω K K' K₃ z u₁ u₂ u₃ h hb).2 _ (Q3T8.Asc77.S22.closure_13_le h)
      (Q3T8.Asc77.S22.isElemAbelian2_closure_13 h)

theorem oddCore_le_normalizer_alpha
    (h2 : Q3T8.Asc77.S22.C22_2S)
    (h : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃) (hb : Big Ω K) :
    oddCoreOf (Subgroup.centralizer ({z} : Set G)) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G) :=
  T7A.oddCore_le_normalizer_alpha (Q3T8.Asc77.Hyp22Setting.isElemAbelian_B h)
      (Q3T8.Asc77.S22.natCard_B h)
    (Q3T8.Asc77.S22.B_le_centralizer h) (h2 G Ω K K' K₃ z u₁ u₂ u₃ h hb).2

theorem third_le_normalizer_alpha
    (h2 : Q3T8.Asc77.S22.C22_2S)
    (h : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃) (hb : Big Ω K) :
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
    (Q3T8.Asc77.S22.oddCore_le_normalizer_alpha h2 h hb)

theorem le_normalizer_alpha
    (h2 : Q3T8.Asc77.S22.C22_2S) (h : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z
    u₁ u₂ u₃)
    (hb : Big Ω K) :
    K ≤ Subgroup.normalizer (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G) ∧
    K' ≤ Subgroup.normalizer (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G) ∧
    K₃ ≤ Subgroup.normalizer (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G) := by
  refine ⟨?_, ?_, Q3T8.Asc77.S22.third_le_normalizer_alpha h2 h hb⟩
  · have := Q3T8.Asc77.S22.third_le_normalizer_alpha h2 (Q3T8.Asc77.S22.rotate h) (hb.of_twin h.hz
      h.hK')
    rwa [Q3T8.Asc77.S22.alpha_23 h2 h hb] at this
  · have := Q3T8.Asc77.S22.third_le_normalizer_alpha h2 (Q3T8.Asc77.S22.rotate
      (Q3T8.Asc77.S22.rotate h)) (hb.of_twin h.hz h.hK₃)
    rwa [← Q3T8.Asc77.T7J.comm₁₃ h, Q3T8.Asc77.S22.alpha_13 h2 h hb] at this

theorem twin_le_normalizer_alpha
    (h2 : Q3T8.Asc77.S22.C22_2S) (h : Q3T8.Asc77.Hyp22Setting Ω K K'
    K₃ z u₁ u₂ u₃)
    (hb : Big Ω K) {L : Subgroup G} (hL : L ∈ twinSet Ω K) :
    L ≤ Subgroup.normalizer (alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) : Set G) := by
  by_cases hLK : L = K
  · rw [hLK]
    exact (Q3T8.Asc77.S22.le_normalizer_alpha h2 h hb).1
  by_cases hLK' : L = K'
  · rw [hLK']
    exact (Q3T8.Asc77.S22.le_normalizer_alpha h2 h hb).2.1
  obtain ⟨w, hw⟩ := Q3T8.Asc77.S22.exists_replace_third h hL hLK hLK'
  exact Q3T8.Asc77.S22.third_le_normalizer_alpha h2 hw hb
end Alpha
end S22
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Asc77.Thompson
section Chain
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem exists_W_of_isPGroup
    (hΩ : Q3T8.Asc77.HypOmegaMod Ω)
    {P : Subgroup G} (hP : IsPGroup 2 P) :
    ∃ W ∈ WSet Ω, ∀ R ∈ RSet Ω, R ≤ P → R ∈ DSet Ω W := by
  obtain ⟨S, hS⟩ := hP.exists_le_sylow
  obtain ⟨η, hη, hηinv⟩ := (Q3T8.Asc77.l6_9_proved G Ω hΩ S).1
  have hηG : η ∈ etaG Ω := ⟨S, hη, hηinv⟩
  have hηS : ∀ V ∈ η, V ≤ (S : Subgroup G) := fun V hV => (hη.1 hV).2
  refine ⟨⨆ V ∈ η, V, ⟨η, hηG, rfl⟩, fun R hR hRP => ⟨hR, ?_⟩⟩
  exact le_normalizer_biSup_of_acts
    ((Q3T8.Asc77.l6_10_proved G Ω hΩ S η hηG hηS).1 R hR (hRP.trans hS))
end Chain
end Asc77

end

section

namespace Asc77.T7J
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.T7J
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Asc77.AscE184Sect
open CFSG.ClassicalInvolution.Asc77.T7H
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem exactImg_nbr_eq_weak
    (hΩ :
    Q3T7M.HM Ω)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) {K K' : Subgroup G} (hK : K ∈
        Q3T8.Asc77.ExactLayer.tqMembers Ω c)
    (hperp : ∀ J ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω c, J ∈ KPerp Ω K → J = K ∨ J = K') {J :
        Subgroup G}
    (hJ : J ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω c)
    (h : Q3T8.Asc77.T7H.exactImg Ω c J ∈ omegaNbr (oddQuotientFamily
        (Q3T8.Asc77.ExactLayer.exactPair Ω c)) (Q3T8.Asc77.T7H.exactImg Ω c K)) :
    Q3T8.Asc77.T7H.exactImg Ω c J = Q3T8.Asc77.T7H.exactImg Ω c K' := by
  obtain ⟨n, hn, hnb⟩ := Q3T8.Asc77.T7H.exactImg_nbr_lift hΩ hc2 hK hJ h
  have hnc : (n : G) * c * (n : G)⁻¹ = c := Q3T8.Asc77.T7H.mem_centralizer_of_mem_exactLayer
  have hncent : (n : G)⁻¹ ∈ Subgroup.centralizer ({c} : Set G) :=
    inv_mem (Q3T8.Asc77.ExactLayer.exactLayer_le_centralizer Ω c n.2)
  have h1 := omegaNbr_conj hΩ.conjInvariant hnb (n : G)⁻¹
  rw [conjSub_inv_conjSub] at h1
  have h2 : conjSub (n : G)⁻¹ J ∈ KPerp Ω K := Set.mem_insert_of_mem _ h1
  have hJ' : conjSub (n : G)⁻¹ J ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω c :=
    Q3T8.Asc77.ExactLayer.conjSub_mem_tqMembers hΩ.conjInvariant hncent hJ
  have h3 : conjSub (n : G)⁻¹ J = K' := by
    rcases hperp _ hJ' h2 with h2 | h2
    · exact absurd h2 h1.2.1
    · exact h2
  have h4 : J = conjSub (n : G) K' := by
    rw [← h3, conjSub_conjSub_inv]
  rw [h4]
  exact Q3T8.Asc77.T7H.exactImg_conjSub_odd hn hnc

theorem layer_orth_six_weak
    (hTSF : Q3T8.Asc77.TwinSquareFact3) (hΩ : Q3T7M.HM Ω) (hBelow :
    Q3T8.Generic.CITBelowU (Nat.card G))
    (hc2 : c * c = 1) (hnc : ¬ ({c} : Set G) ⊆ Subgroup.center G)
    {K K' L : Subgroup G} {z t b b' : G}
    (hK : K ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω c) (hK' : K' ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω c)
        (hL : L ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω c)
    (hz : IsUniqueInvolution K z) (hz' : IsUniqueInvolution K' z)
    (hperp : ∀ J ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω c, J ∈ KPerp Ω K → J = K ∨ J = K')
    (hperp' : ∀ J ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω c, J ∈ KPerp Ω K' → J = K' ∨ J = K)
    (htL : IsUniqueInvolution L t) (hzt : z * t = t * z) (htz : t ≠ z)
    {R R' : Subgroup G} (hR : IsSylow2In R (Q3T8.Asc77.ExactLayer.exactCore c K)) (hR' : IsSylow2In
        R' (Q3T8.Asc77.ExactLayer.exactCore c K'))
    (hRR' : Commutes R R')
    (hb : b ∈ Q3T8.Asc77.ExactLayer.exactCore c K) (hb' : b' ∈ Q3T8.Asc77.ExactLayer.exactCore c
        K') (ob : b * b = z) (ob' : b' * b' = z)
    (hrel : t = b * b' * c) :
    Q3T8.Asc77.LayerOrthType Ω c 6 (piSign 3 1) := by
  classical
  have hcpg := Q3T8.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hc2
  set E := Q3T8.Asc77.ExactLayer.exactLayer Ω c with hE
  set N₀ := classicalInvolutionOddCore ↥E with hN₀
  have hN₀odd : Odd (Nat.card N₀) := CFSG.ComponentClassification.OddCore.odd_card ↥E
  have hΛ : Q3T7M.HM (Q3T8.Asc77.ExactLayer.exactPair Ω c) :=
      Q3T8.Asc77.ExactLayer.hypOmegaMod_exactPair hΩ hcpg
  have hΦ : Q3T7M.HM (oddQuotientFamily (Q3T8.Asc77.ExactLayer.exactPair Ω c)) :=
    Q3T8.Asc77.oddQuotHyp ↥E (Q3T8.Asc77.ExactLayer.exactPair Ω c) hΛ N₀ hN₀odd
  
  have hzK : z ∈ Q3T8.Asc77.ExactLayer.exactCore c K :=
      (Q3T8.Asc77.T7H.isUniqueInvolution_exactCore hΩ hcpg hK hz).mem
  have hzE : z ∈ E := Q3T8.Asc77.ExactLayer.exactCore_le_exactLayer hK hzK
  have htL' : t ∈ Q3T8.Asc77.ExactLayer.exactCore c L :=
      (Q3T8.Asc77.T7H.isUniqueInvolution_exactCore hΩ hcpg hL htL).mem
  have htE : t ∈ E := Q3T8.Asc77.ExactLayer.exactCore_le_exactLayer hL htL'
  have hbE : b ∈ E := Q3T8.Asc77.ExactLayer.exactCore_le_exactLayer hK hb
  have hb'E : b' ∈ E := Q3T8.Asc77.ExactLayer.exactCore_le_exactLayer hK' hb'
  have hcE : c ∈ E := by
    have : c = (b * b')⁻¹ * t := by rw [hrel]; group
    rw [this]
    exact E.mul_mem (E.inv_mem (E.mul_mem hbE hb'E)) htE
  have hz2 : z * z = 1 := hz.sq
  have ht2 : t * t = 1 := htL.sq
  
  have hA : Q3T8.Asc77.T7H.exactImg Ω c K ∈ oddQuotientFamily (Q3T8.Asc77.ExactLayer.exactPair Ω c)
      := Q3T8.Asc77.T7H.exactImg_mem hK
  have hA' : Q3T8.Asc77.T7H.exactImg Ω c K' ∈ oddQuotientFamily (Q3T8.Asc77.ExactLayer.exactPair Ω
      c) := Q3T8.Asc77.T7H.exactImg_mem hK'
  have hB : Q3T8.Asc77.T7H.exactImg Ω c L ∈ oddQuotientFamily (Q3T8.Asc77.ExactLayer.exactPair Ω c)
      := Q3T8.Asc77.T7H.exactImg_mem hL
  have hzA := Q3T8.Asc77.T7H.exactImg_isUnique hΩ hcpg hK hz hzE
  have hzA' := Q3T8.Asc77.T7H.exactImg_isUnique hΩ hcpg hK' hz' hzE
  have htB := Q3T8.Asc77.T7H.exactImg_isUnique hΩ hcpg hL htL htE
  have hne : Q3T8.Asc77.T7H.exactImg Ω c K ≠ Q3T8.Asc77.T7H.exactImg Ω c K' := by
    refine Q3T8.Asc77.map_ne_of_commutes_sylow (N := N₀) hΦ hN₀odd
      (M₁ := (Q3T8.Asc77.ExactLayer.exactCore c K).subgroupOf E) (M₂ :=
          (Q3T8.Asc77.ExactLayer.exactCore c K').subgroupOf E)
      (V₁ := R.subgroupOf E) (V₂ := R'.subgroupOf E)
      ⟨_, Q3T8.Asc77.ExactLayer.exactCore_mem_exactFamily hK,
          Q3T8.Asc77.ExactLayer.exactCore_le_exactLayer hK, rfl⟩
      (hR.subgroupOf (Q3T8.Asc77.ExactLayer.exactCore_le_exactLayer hK)) (hR'.subgroupOf
          (Q3T8.Asc77.ExactLayer.exactCore_le_exactLayer hK'))
      ?_
    intro x hx y hy
    exact Subtype.ext (hRR' x (Subgroup.mem_subgroupOf.mp hx) y (Subgroup.mem_subgroupOf.mp hy))
  
  have hnbA : ∀ M ∈ oddQuotientFamily (Q3T8.Asc77.ExactLayer.exactPair Ω c),
      M ∈ omegaNbr (oddQuotientFamily (Q3T8.Asc77.ExactLayer.exactPair Ω c))
          (Q3T8.Asc77.T7H.exactImg Ω c K) → M = Q3T8.Asc77.T7H.exactImg Ω c K' := by
    intro M hM hMn
    obtain ⟨J, hJ, rfl⟩ := Q3T8.Asc77.T7H.exists_exactImg_of_mem hM
    exact Q3T8.Asc77.T7J.exactImg_nbr_eq_weak hΩ hcpg hK hperp hJ hMn
  have hnbA' : ∀ M ∈ oddQuotientFamily (Q3T8.Asc77.ExactLayer.exactPair Ω c),
      M ∈ omegaNbr (oddQuotientFamily (Q3T8.Asc77.ExactLayer.exactPair Ω c))
          (Q3T8.Asc77.T7H.exactImg Ω c K') → M = Q3T8.Asc77.T7H.exactImg Ω c K := by
    intro M hM hMn
    obtain ⟨J, hJ, rfl⟩ := Q3T8.Asc77.T7H.exists_exactImg_of_mem hM
    exact Q3T8.Asc77.T7J.exactImg_nbr_eq_weak hΩ hcpg hK' hperp' hJ hMn
  
  have hbarne : Q3T8.Asc77.T7H.toBar Ω c t htE ≠ Q3T8.Asc77.T7H.toBar Ω c z hzE := fun h =>
    htz (Q3T8.Asc77.T7H.eq_of_toBar_eq htE hzE ht2 hz2 hzt.symm h)
  have hBA : Q3T8.Asc77.T7H.exactImg Ω c L ≠ Q3T8.Asc77.T7H.exactImg Ω c K := by
    intro h
    rw [h] at htB
    exact hbarne (htB.eq hzA)
  have hBA' : Q3T8.Asc77.T7H.exactImg Ω c L ≠ Q3T8.Asc77.T7H.exactImg Ω c K' := by
    intro h
    rw [h] at htB
    exact hbarne (htB.eq hzA')
  have hBn : Q3T8.Asc77.T7H.exactImg Ω c L ∉ omegaNbr (oddQuotientFamily
      (Q3T8.Asc77.ExactLayer.exactPair Ω c)) (Q3T8.Asc77.T7H.exactImg Ω c K) :=
    fun h => hBA' (hnbA _ hB h)
  have hBn' : Q3T8.Asc77.T7H.exactImg Ω c L ∉ omegaNbr (oddQuotientFamily
      (Q3T8.Asc77.ExactLayer.exactPair Ω c)) (Q3T8.Asc77.T7H.exactImg Ω c K') :=
    fun h => hBA (hnbA' _ hB h)
  
  have hpath : ∀ N, Relation.ReflTransGen (fun M N : Subgroup (↥E ⧸ N₀) =>
      N ∈ oddQuotientFamily (Q3T8.Asc77.ExactLayer.exactPair Ω c) ∧
        Disconnected.dAdj (oddQuotientFamily (Q3T8.Asc77.ExactLayer.exactPair Ω c)) M N)
      (Q3T8.Asc77.T7H.exactImg Ω c K) N → N = Q3T8.Asc77.T7H.exactImg Ω c K ∨ N =
          Q3T8.Asc77.T7H.exactImg Ω c K' := by
    intro N hN
    induction hN with
    | refl => exact Or.inl rfl
    | tail hpre hstep ih =>
      rename_i M N'
      obtain ⟨hN'Φ, hadj⟩ := hstep
      have hMΦ : M ∈ oddQuotientFamily (Q3T8.Asc77.ExactLayer.exactPair Ω c) := by
        rcases ih with rfl | rfl
        · exact hA
        · exact hA'
      rcases ih with rfl | rfl
      · refine Or.inr (hnbA N' hN'Φ ?_)
        rcases hadj with h | h
        · exact h
        · exact Q3CL.T3.omegaNbr_symm (Q3T8.Asc77.l6_2) hΦ hN'Φ hMΦ h
      · refine Or.inl (hnbA' N' hN'Φ ?_)
        rcases hadj with h | h
        · exact h
        · exact Q3CL.T3.omegaNbr_symm (Q3T8.Asc77.l6_2) hΦ hN'Φ hMΦ h
  have hdisc : ¬ Disconnected.DConnected (oddQuotientFamily (Q3T8.Asc77.ExactLayer.exactPair Ω c))
      := by
    intro hconn
    rcases hpath _ (hconn _ hA _ hB) with h | h
    · exact hBA h
    · exact hBA' h
  
  have hlt : Nat.card (↥E ⧸ N₀) < Nat.card G := by
    have h1 : Nat.card (↥E ⧸ N₀) ≤ Nat.card ↥E :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_card N₀)
    have h2 : Nat.card ↥E < Nat.card G := Q3T8.Asc77.ExactLayer.card_exactLayer_lt hnc
    omega
  obtain ⟨t₀, k₀, D, hcard, i₀, -, -⟩ := Q3T8.Asc77.exists_hasLieType_of_frame hBelow hΦ
    ⟨Q3T8.Asc77.T7H.exactImg Ω c K, hA⟩ (CFSG.ComponentClassification.OddCore.quotient_corefree ↥E)
        hlt
    hA hA' hB hnbA hBA hBA' hBn hBn' hne hzA hzA'
  have hgen : omegaGen (oddQuotientFamily (Q3T8.Asc77.ExactLayer.exactPair Ω c)) = ⊤ :=
    omegaGen_quotFamily_eq_top (Q3T8.Asc77.ExactLayer.exactPair Ω c) N₀
      (omegaGen_restrictFamily_eq_top (Q3T8.Asc77.ExactLayer.exactFamily Ω c) E
          (Q3T8.Asc77.ExactLayer.exactLayer_eq_iSup Ω c).symm)
  
  have hc1 : c ≠ 1 := by
    rintro rfl
    exact hnc (by intro x hx; rw [Set.mem_singleton_iff] at hx; subst hx; exact Subgroup.one_mem _)
  have heC : Q3T8.Asc77.T7H.toBar Ω c c hcE ∈ Subgroup.center (↥E ⧸ N₀) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨y', rfl⟩ := QuotientGroup.mk'_surjective N₀ y
    show QuotientGroup.mk' N₀ y' * QuotientGroup.mk' N₀ ⟨c, hcE⟩ =
      QuotientGroup.mk' N₀ ⟨c, hcE⟩ * QuotientGroup.mk' N₀ y'
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp
      (Q3T8.Asc77.ExactLayer.exactLayer_le_centralizer Ω c y'.2)
  have hc2' : Q3T8.Asc77.T7H.toBar Ω c c hcE * Q3T8.Asc77.T7H.toBar Ω c c hcE = 1 := by
    unfold Q3T8.Asc77.T7H.toBar
    rw [← map_mul]
    have : (⟨c, hcE⟩ : ↥E) * ⟨c, hcE⟩ = 1 := Subtype.ext hc2
    rw [this, map_one]
  have hc1' : Q3T8.Asc77.T7H.toBar Ω c c hcE ≠ 1 := by
    intro h
    have hmem : (⟨c, hcE⟩ : ↥E) ∈ N₀ := (QuotientGroup.eq_one_iff _).mp h
    have := eq_one_of_mem_odd_of_sq hN₀odd hmem (Subtype.ext hc2)
    exact hc1 (congrArg Subtype.val this)
  have hrel' : Q3T8.Asc77.T7H.toBar Ω c t htE = Q3T8.Asc77.T7H.toBar Ω c b hbE *
      Q3T8.Asc77.T7H.toBar Ω c b' hb'E * Q3T8.Asc77.T7H.toBar Ω c c hcE := by
    have h1 : (⟨t, htE⟩ : ↥E) = ⟨b, hbE⟩ * ⟨b', hb'E⟩ * ⟨c, hcE⟩ := Subtype.ext hrel
    unfold Q3T8.Asc77.T7H.toBar
    rw [h1, map_mul, map_mul]
  have ob₁ : Q3T8.Asc77.T7H.toBar Ω c b hbE * Q3T8.Asc77.T7H.toBar Ω c b hbE = Q3T8.Asc77.T7H.toBar
      Ω c z hzE := by
    have h1 : (⟨b, hbE⟩ : ↥E) * ⟨b, hbE⟩ = ⟨z, hzE⟩ := Subtype.ext ob
    unfold Q3T8.Asc77.T7H.toBar
    rw [← map_mul, h1]
  have ob₂ : Q3T8.Asc77.T7H.toBar Ω c b' hb'E * Q3T8.Asc77.T7H.toBar Ω c b' hb'E =
      Q3T8.Asc77.T7H.toBar Ω c z hzE := by
    have h1 : (⟨b', hb'E⟩ : ↥E) * ⟨b', hb'E⟩ = ⟨z, hzE⟩ := Subtype.ext ob'
    unfold Q3T8.Asc77.T7H.toBar
    rw [← map_mul, h1]
  have hframe : TwinFrame (oddQuotientFamily (Q3T8.Asc77.ExactLayer.exactPair Ω c))
      (Q3T8.Asc77.T7H.exactImg Ω c K)
      (Q3T8.Asc77.T7H.exactImg Ω c K') (Q3T8.Asc77.T7H.exactImg Ω c L) (Q3T8.Asc77.T7H.toBar Ω c z
          hzE) (Q3T8.Asc77.T7H.toBar Ω c b hbE)
      (Q3T8.Asc77.T7H.toBar Ω c b' hb'E) (Q3T8.Asc77.T7H.toBar Ω c t htE) (Q3T8.Asc77.T7H.toBar Ω c
          c hcE) :=
    ⟨hA, hA', hB, hne, hzA, hzA', Q3T8.Asc77.T7H.mem_exactImg hb hbE, Q3T8.Asc77.T7H.mem_exactImg
        hb' hb'E, ob₁, ob₂, htB,
      heC, hc2', hc1', hrel'⟩
  have htag := Q3T8.Asc77.twinFrame_tag hTSF hΦ D hcard hgen hdisc hframe i₀
  
  have hort : HasOrthType 3 1 (oddQuotientFamily (Q3T8.Asc77.ExactLayer.exactPair Ω c)) 6 (piSign 3
      1) := by
    rcases htag with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · have hπ : piSign 3 1 = true := by unfold piSign; simp [h3]
      exact ⟨.PSL, 4, Or.inr (Or.inl ⟨rfl, hπ, rfl, rfl⟩), D, hcard, i₀, h1, h2⟩
    · have hπ : piSign 3 1 = false := by unfold piSign; simp [h3]
      exact ⟨.PSU, 4, Or.inr (Or.inr (Or.inl ⟨rfl, hπ, rfl, rfl⟩)), D, hcard, i₀, h1, h2⟩
  exact sectionOrthType_of_hasOrthType hgen hort

theorem layer_orth_six_weak_proved
    (hΩ : Q3T7M.HM Ω) (hBelow : Q3T8.Generic.CITBelowU (Nat.card G))
    (hc2 : c * c = 1) (hnc : ¬ ({c} : Set G) ⊆ Subgroup.center G)
    {K K' L : Subgroup G} {z t b b' : G}
    (hK : K ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω c) (hK' : K' ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω c)
        (hL : L ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω c)
    (hz : IsUniqueInvolution K z) (hz' : IsUniqueInvolution K' z)
    (hperp : ∀ J ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω c, J ∈ KPerp Ω K → J = K ∨ J = K')
    (hperp' : ∀ J ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω c, J ∈ KPerp Ω K' → J = K' ∨ J = K)
    (htL : IsUniqueInvolution L t) (hzt : z * t = t * z) (htz : t ≠ z)
    {R R' : Subgroup G} (hR : IsSylow2In R (Q3T8.Asc77.ExactLayer.exactCore c K)) (hR' : IsSylow2In
        R' (Q3T8.Asc77.ExactLayer.exactCore c K'))
    (hRR' : Commutes R R')
    (hb : b ∈ Q3T8.Asc77.ExactLayer.exactCore c K) (hb' : b' ∈ Q3T8.Asc77.ExactLayer.exactCore c
        K') (ob : b * b = z) (ob' : b' * b' = z)
    (hrel : t = b * b' * c) :
    Q3T8.Asc77.LayerOrthType Ω c 6 (piSign 3 1) :=
  Q3T8.Asc77.T7J.layer_orth_six_weak twinSquareFact3_proved hΩ hBelow hc2 hnc hK hK' hL hz hz'
      hperp hperp'
    htL hzt htz hR hR' hRR' hb hb' ob ob' hrel
end Asc77.T7J

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped MatrixGroups commutatorElement
namespace T7V
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.T7V
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem exists_conj_mod_oddCore
    (hΩ : Q3T7M.HM Ω) {K : Subgroup G} (hK : K ∈ Ω)
    {z : G} (hz : IsUniqueInvolution K z) {a b : G} (ha : a ∈ K) (hb : b ∈ K)
    (ha4 : orderOf a = 4) (hb4 : orderOf b = 4) :
    ∃ k ∈ K, k * a * k⁻¹ * b⁻¹ ∈ oddCoreOf K := by
  obtain ⟨φ⟩ := hΩ.nonempty_equiv_sl2 hK
  have hsq : ∀ {x : G}, x ∈ K → orderOf x = 4 → x * x = z := by
    intro x hx hx4
    have h1 : (x * x) * (x * x) = 1 := by
      have := pow_orderOf_eq_one x
      rw [hx4] at this
      calc (x * x) * (x * x) = x ^ 4 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
        _ = 1 := this
    have h2 : x * x ≠ 1 := by
      intro h
      have : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
      rw [hx4] at this
      omega
    exact (hz.unique (x * x) (K.mul_mem hx hx) h1).resolve_left h2
  set mk : ↥K →* ↥K ⧸ classicalInvolutionOddCore ↥K := QuotientGroup.mk' _ with hmk
  have hzK : (⟨z, hz.mem⟩ : ↥K) * ⟨z, hz.mem⟩ = 1 := Subtype.ext hz.sq
  have hz1 : φ (mk ⟨z, hz.mem⟩) = -1 := by
    have h1 : φ (mk ⟨z, hz.mem⟩) * φ (mk ⟨z, hz.mem⟩) = 1 := by
      rw [← map_mul, ← map_mul, hzK, map_one, map_one]
    rcases sl2_sq_eq_one (two_ne_zero_galoisField (by norm_num)) h1 with h | h
    · exfalso
      have h2 : mk ⟨z, hz.mem⟩ = 1 := φ.injective (by rw [h, map_one])
      rw [hmk, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
      have h3 : z ∈ oddCoreOf K := mem_oddCoreOf_iff.mpr ⟨hz.mem, h2⟩
      exact hz.ne_one (eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard K) h3
        (isPGroup_zpowers_of_mul_self_eq_one hz.sq hz.ne_one))
    · exact h
  have hx : ∀ {x : G} (hxK : x ∈ K), orderOf x = 4 →
      φ (mk ⟨x, hxK⟩) * φ (mk ⟨x, hxK⟩) = -1 := by
    intro x hxK hx4
    rw [← map_mul, ← map_mul]
    have : (⟨x, hxK⟩ : ↥K) * ⟨x, hxK⟩ = ⟨z, hz.mem⟩ := Subtype.ext (hsq hxK hx4)
    rw [this, hz1]
  have hmat : ∀ r : SL(2, GaloisField 3 1), r * r = -1 →
      (r : Matrix (Fin 2) (Fin 2) (GaloisField 3 1)) * r = -1 := by
    intro r hr
    have := congrArg (fun m : SL(2, GaloisField 3 1) =>
      (m : Matrix (Fin 2) (Fin 2) (GaloisField 3 1))) hr
    simpa [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg] using this
  obtain ⟨h₁, hh₁⟩ := ModelFacts.Orth15.InnerL4.exists_conj_r0 (two_ne_zero_galoisField (by
      norm_num))
    (φ (mk ⟨a, ha⟩)) (hmat _ (hx ha ha4))
  obtain ⟨h₂, hh₂⟩ := ModelFacts.Orth15.InnerL4.exists_conj_r0 (two_ne_zero_galoisField (by
      norm_num))
    (φ (mk ⟨b, hb⟩)) (hmat _ (hx hb hb4))
  obtain ⟨k, hk⟩ := QuotientGroup.mk'_surjective _ (φ.symm (h₂ * h₁⁻¹))
  refine ⟨k, k.2, ?_⟩
  have hconj : mk k * mk ⟨a, ha⟩ * (mk k)⁻¹ = mk ⟨b, hb⟩ := by
    apply φ.injective
    rw [map_mul, map_mul, map_inv]
    have : φ (mk k) = h₂ * h₁⁻¹ := by
      rw [hmk, hk]; exact φ.apply_symm_apply _
    rw [this, ← hh₁, ← hh₂]
    group
  have h3 : mk (k * ⟨a, ha⟩ * k⁻¹ * ⟨b, hb⟩⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hconj]
    group
  rw [hmk, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3
  exact mem_oddCoreOf_iff.mpr ⟨by
    have := (k * ⟨a, ha⟩ * k⁻¹ * ⟨b, hb⟩⁻¹).2
    exact this, h3⟩

theorem exists_conj_pair
    (hΩ : Q3T7M.HM Ω) {K K' : Subgroup G}
    (hK : K ∈ Ω) (hK' : K' ∈ Ω) (hne : K ≠ K') {z : G} (hz : IsUniqueInvolution K z)
    (hz' : IsUniqueInvolution K' z) (hKK' : K ≤ trivialOnQuot K') (hK'K : K' ≤ trivialOnQuot K)
    {a a' b₁ b₂ : G} (ha : a ∈ K) (ha' : a' ∈ K') (hb₁ : b₁ ∈ K) (hb₂ : b₂ ∈ K')
    (ha4 : orderOf a = 4) (ha'4 : orderOf a' = 4) (hb₁4 : orderOf b₁ = 4) (hb₂4 : orderOf b₂ = 4)
    (haa' : a * a' = a' * a) (hbb : b₁ * b₂ = b₂ * b₁) :
    ∃ c ∈ K ⊔ K', c * (a * a') * c⁻¹ = b₁ * b₂ := by
  obtain ⟨k, hkK, hk⟩ := Q3T8.Asc77.T7V.exists_conj_mod_oddCore hΩ hK hz ha hb₁ ha4 hb₁4
  obtain ⟨k', hk'K', hk'⟩ := Q3T8.Asc77.T7V.exists_conj_mod_oddCore hΩ hK' hz' ha' hb₂ ha'4 hb₂4
  have hsq : ∀ {x : G}, orderOf x = 4 → x * x = z → True := fun _ _ => trivial
  have sqz : ∀ {J : Subgroup G} {w x : G}, IsUniqueInvolution J w → x ∈ J → orderOf x = 4 →
      x * x = w := by
    intro J w x hw hx hx4
    have h1 : (x * x) * (x * x) = 1 := by
      have := pow_orderOf_eq_one x
      rw [hx4] at this
      calc (x * x) * (x * x) = x ^ 4 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
        _ = 1 := this
    have h2 : x * x ≠ 1 := by
      intro h
      have : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
      rw [hx4] at this
      omega
    exact (hw.unique (x * x) (J.mul_mem hx hx) h1).resolve_left h2
  have hK_nK' : ∀ x ∈ K, x ∈ Subgroup.normalizer (K' : Set G) := fun x hx => (hKK' hx).1
  have hK'_nK : ∀ x ∈ K', x ∈ Subgroup.normalizer (K : Set G) := fun x hx => (hK'K hx).1
  have oK_K : ∀ x ∈ K, ∀ y ∈ oddCoreOf K, x * y * x⁻¹ ∈ oddCoreOf K := fun x hx y hy =>
    mem_normalizer_oddCoreOf_of_mem_normalizer (Subgroup.le_normalizer hx) hy
  have oK_K' : ∀ x ∈ K', ∀ y ∈ oddCoreOf K, x * y * x⁻¹ ∈ oddCoreOf K := fun x hx y hy =>
    mem_normalizer_oddCoreOf_of_mem_normalizer (hK'_nK x hx) hy
  have oK'_K : ∀ x ∈ K, ∀ y ∈ oddCoreOf K', x * y * x⁻¹ ∈ oddCoreOf K' := fun x hx y hy =>
    mem_normalizer_oddCoreOf_of_mem_normalizer (hK_nK' x hx) hy
  have oK'_K' : ∀ x ∈ K', ∀ y ∈ oddCoreOf K', x * y * x⁻¹ ∈ oddCoreOf K' := fun x hx y hy =>
    mem_normalizer_oddCoreOf_of_mem_normalizer (Subgroup.le_normalizer hx) hy
  obtain ⟨N₀, hN₀⟩ : ∃ N₀ : Subgroup G, N₀ = oddCoreOf K ⊔ oddCoreOf K' := ⟨_, rfl⟩
  have hN₀le : N₀ ≤ K ⊔ K' := by
    rw [hN₀]; exact sup_le_sup (oddCoreOf_le_self K) (oddCoreOf_le_self K')
  have hOK : oddCoreOf K ≤ N₀ := by rw [hN₀]; exact le_sup_left
  have hOK' : oddCoreOf K' ≤ N₀ := by rw [hN₀]; exact le_sup_right
  have hnormK : ∀ x ∈ K, x ∈ Subgroup.normalizer (N₀ : Set G) := by
    intro x hx
    rw [mem_normalizer_iff_conjSub_eq, hN₀, Thompson.conjSub_sup,
      conjSub_oddCoreOf_eq_of_mem_normalizer (Subgroup.le_normalizer hx),
      conjSub_oddCoreOf_eq_of_mem_normalizer (hK_nK' x hx)]
  have hnormK' : ∀ x ∈ K', x ∈ Subgroup.normalizer (N₀ : Set G) := by
    intro x hx
    rw [mem_normalizer_iff_conjSub_eq, hN₀, Thompson.conjSub_sup,
      conjSub_oddCoreOf_eq_of_mem_normalizer (hK'_nK x hx),
      conjSub_oddCoreOf_eq_of_mem_normalizer (Subgroup.le_normalizer hx)]
  have hnorm : K ⊔ K' ≤ Subgroup.normalizer (N₀ : Set G) :=
    sup_le (fun x hx => hnormK x hx) (fun x hx => hnormK' x hx)
  have hodd : Odd (Nat.card ↥N₀) := by
    have hle : oddCoreOf K ≤ Subgroup.normalizer (oddCoreOf K' : Set G) := fun g hg =>
      mem_normalizer_iff_conjSub_eq.mpr
        (conjSub_oddCoreOf_eq_of_mem_normalizer (hK_nK' g (oddCoreOf_le_self K hg)))
    have hcard :=
      CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen.card_sup_mul_card_inf_of_le_normalizer
        hle
    have h1 : Odd (Nat.card ↥(oddCoreOf K ⊔ oddCoreOf K') *
        Nat.card ↥(oddCoreOf K ⊓ oddCoreOf K')) := by
      rw [hcard]
      exact (oddCoreOf_odd_natCard K).mul (oddCoreOf_odd_natCard K')
    rw [hN₀]
    exact (Nat.odd_mul.mp h1).1
  have hn₁ : ⁅k', a⁆ ∈ oddCoreOf K := (hK'K hk'K').2 a ha
  have hn₂ : ⁅k, b₂⁆ ∈ oddCoreOf K' := (hKK' hkK).2 b₂ hb₂
  have hm₁ : k * a * k⁻¹ * b₁⁻¹ ∈ oddCoreOf K := hk
  have hm₂ : k' * a' * k'⁻¹ * b₂⁻¹ ∈ oddCoreOf K' := hk'
  have ho₁ : (k * ⁅k', a⁆ * k⁻¹) * (k * a * k⁻¹ * b₁⁻¹) ∈ oddCoreOf K :=
    (oddCoreOf K).mul_mem (oK_K k hkK _ hn₁) hm₁
  have ho₂ : (k * (k' * a' * k'⁻¹ * b₂⁻¹) * k⁻¹) * ⁅k, b₂⁆ ∈ oddCoreOf K' :=
    (oddCoreOf K').mul_mem (oK'_K k hkK _ hm₂) hn₂
  have ho₂' : b₁ * ((k * (k' * a' * k'⁻¹ * b₂⁻¹) * k⁻¹) * ⁅k, b₂⁆) * b₁⁻¹ ∈ oddCoreOf K' :=
    oK'_K b₁ hb₁ _ ho₂
  have hn : ((k * ⁅k', a⁆ * k⁻¹) * (k * a * k⁻¹ * b₁⁻¹)) *
      (b₁ * ((k * (k' * a' * k'⁻¹ * b₂⁻¹) * k⁻¹) * ⁅k, b₂⁆) * b₁⁻¹) ∈ N₀ :=
    N₀.mul_mem (hOK ho₁) (hOK' ho₂')
  obtain ⟨nn, hnneq⟩ : ∃ nn : G, nn = ((k * ⁅k', a⁆ * k⁻¹) * (k * a * k⁻¹ * b₁⁻¹)) *
      (b₁ * ((k * (k' * a' * k'⁻¹ * b₂⁻¹) * k⁻¹) * ⁅k, b₂⁆) * b₁⁻¹) := ⟨_, rfl⟩
  rw [← hnneq] at hn
  have hs'eq : (k * k') * (a * a') * (k * k')⁻¹ = nn * (b₁ * b₂) := by
    rw [hnneq]
    simp only [commutatorElement_def]
    group
  have hb₁b₁ : b₁ * b₁ = z := sqz hz hb₁ hb₁4
  have hb₂b₂ : b₂ * b₂ = z := sqz hz' hb₂ hb₂4
  have haa : a * a = z := sqz hz ha ha4
  have ha'a' : a' * a' = z := sqz hz' ha' ha'4
  have hs2 : (b₁ * b₂) * (b₁ * b₂) = 1 := by
    calc (b₁ * b₂) * (b₁ * b₂) = (b₁ * b₁) * (b₂ * b₂) := by
          rw [mul_assoc, ← mul_assoc b₂, ← hbb]; group
      _ = 1 := by rw [hb₁b₁, hb₂b₂, hz.sq]
  have hu2 : (a * a') * (a * a') = 1 := by
    calc (a * a') * (a * a') = (a * a) * (a' * a') := by
          rw [mul_assoc, ← mul_assoc a', ← haa']; group
      _ = 1 := by rw [haa, ha'a', hz.sq]
  have hs'2 : ((k * k') * (a * a') * (k * k')⁻¹) * ((k * k') * (a * a') * (k * k')⁻¹) = 1 := by
    calc _ = (k * k') * ((a * a') * (a * a')) * (k * k')⁻¹ := by group
      _ = 1 := by rw [hu2]; group
  have hu1 : a * a' ≠ 1 := by
    intro h1
    have ha'eq : a' = a⁻¹ := by
      have : a⁻¹ = a' := by
        calc a⁻¹ = a⁻¹ * (a * a') := by rw [h1, mul_one]
          _ = a' := by group
      exact this.symm
    have ha'K : a' ∈ K := by rw [ha'eq]; exact K.inv_mem ha
    have hin : a' ∈ K ⊓ K' := ⟨ha'K, ha'⟩
    have hdvd : 4 ∣ Nat.card ↥(K ⊓ K') := ha'4 ▸ Subgroup.orderOf_dvd_natCard (K ⊓ K') hin
    have hpos : Nat.card ↥(K ⊓ K') ≠ 0 := Nat.card_pos.ne'
    have h2 : 2 ≤ padicValNat 2 (Nat.card ↥(K ⊓ K')) :=
      (padicValNat_dvd_iff_le (p := 2) hpos).mp (by simpa using hdvd)
    have := (hΩ.omega4 K hK K' hK' hne).1
    omega
  have hs'1 : (k * k') * (a * a') * (k * k')⁻¹ ≠ 1 := by
    intro h1
    apply hu1
    have := congrArg (fun x => (k * k')⁻¹ * x * (k * k')) h1
    simpa [mul_assoc] using this
  have hbK : b₁ * b₂ ∈ K ⊔ K' := (K ⊔ K').mul_mem (Subgroup.mem_sup_left hb₁)
    (Subgroup.mem_sup_right hb₂)
  obtain ⟨n', hn', hconj⟩ := T7L.exists_conj_involution hodd hs2 hs'2 hs'1 (hnorm hbK) (by
    rw [hs'eq]
    have h1 := (Subgroup.mem_normalizer_iff.mp (hnorm ((K ⊔ K').inv_mem hbK)) nn).mp hn
    have h2 : (b₁ * b₂)⁻¹ * (nn * (b₁ * b₂)) = (b₁ * b₂)⁻¹ * nn * ((b₁ * b₂)⁻¹)⁻¹ := by
      rw [inv_inv]; group
    rw [h2]
    exact h1)
  refine ⟨n'⁻¹ * (k * k'), (K ⊔ K').mul_mem ((K ⊔ K').inv_mem (hN₀le hn'))
    ((K ⊔ K').mul_mem (Subgroup.mem_sup_left hkK) (Subgroup.mem_sup_right hk'K')), ?_⟩
  calc n'⁻¹ * (k * k') * (a * a') * (n'⁻¹ * (k * k'))⁻¹
      = n'⁻¹ * ((k * k') * (a * a') * (k * k')⁻¹) * n' := by group
    _ = n'⁻¹ * (n' * (b₁ * b₂) * n'⁻¹) * n' := by rw [hconj]
    _ = b₁ * b₂ := by group
end T7V
end Asc77

end

end CFSG.ClassicalInvolution.Q3.Q3T8
