module

public import CFSG.ClassicalInvolution.Q3.Q3T7ExNbr
public import CFSG.ClassicalInvolution.Q3.Q3T7M01
public import CFSG.ClassicalInvolution.Q3.Q3T7P24A01
public import CFSG.ClassicalInvolution.Q3.Q3T7P25B00

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

abbrev _root_.CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.TwinFrameData :=
  @CFSG.ClassicalInvolution.Asc77.TwinFrameData

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

abbrev Thm7TypedBelow (n : ℕ) : Prop := Uniform.Thm7TypedBelowU 3 1 n

end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected

structure Hyp21 {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z u : G) (J : Subgroup G) (t : G) (W : Subgroup G) : Prop where
  std : Q3T8.Asc77.Std7 Ω K K' z
  hu : u ∈ K ⊔ K'
  hu2 : u * u = 1
  hu1 : u ≠ 1
  huz : u ≠ z
  hJ : J ∈ omegaOfSet Ω (twinSet Ω K)
  ht : IsUniqueInvolution J t
  htu : t * u = u * t
  hW : W ∈ WSet Ω
  hzW : z ∈ W
  htW : t ∈ W

@[expose] def C21_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z u : G) (J : Subgroup G) (t : G) (W : Subgroup G), Q3T8.Asc77.Hyp21 Ω K K' z u J t W →
      Odd (Nat.card ↥(alphaOf (Subgroup.closure {u, z}))) ∧
        ∀ A : Subgroup G, A ≤ Subgroup.closure {z, u, t} → IsElemAbelian2 A 2 →
          alphaOf A = alphaOf (Subgroup.closure {u, z})

@[expose] def C21_12 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z u : G) (J : Subgroup G) (t : G) (W : Subgroup G), Q3T8.Asc77.Hyp21 Ω K K' z u J t W →
      dComp Ω K = dstarComp Ω K ∨ MuIsoWylD4 Ω W

@[expose] def C21_15 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z u : G) (J : Subgroup G) (t : G) (W : Subgroup G), Q3T8.Asc77.Hyp21 Ω K K' z u J t W →
      alphaOf (Subgroup.closure {u, z}) = ⊥ → ¬ rLayer Ω (t * z) ≤ sigmaGen Ω K →
        ∀ M ∈ dComp Ω K, M ≤ Subgroup.centralizer ({t * z} : Set G)

@[expose] def C21_16 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z u : G) (J : Subgroup G) (t : G) (W : Subgroup G), Q3T8.Asc77.Hyp21 Ω K K' z u J t W →
      alphaOf (Subgroup.closure {u, z}) = ⊥

@[expose] def C21_17 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z u : G) (J : Subgroup G) (t : G) (W : Subgroup G), Q3T8.Asc77.Hyp21 Ω K K' z u J t W →
      ¬ rLayer Ω (t * z) ≤ sigmaGen Ω K

@[expose] def C21_E : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z u : G) (J : Subgroup G) (t : G) (W : Subgroup G), Q3T8.Asc77.Hyp21 Ω K K' z u J t W →
      alphaOf (Subgroup.closure {u, z}) = ⊥ → ¬ rLayer Ω (t * z) ≤ sigmaGen Ω K →
        (∀ M ∈ dComp Ω K, M ≤ Subgroup.centralizer ({t * z} : Set G)) → MuIsoWylD4 Ω W → False

@[expose] def C21_setup : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z : G), Q3T8.Asc77.Std7 Ω K K' z → KPerp Ω K ≠ twinSet Ω K →
      ∃ (u : G) (J : Subgroup G) (t : G) (W : Subgroup G), Q3T8.Asc77.Hyp21 Ω K K' z u J t W

@[expose] def C21_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z : G), Q3T8.Asc77.Std7 Ω K K' z → KPerp Ω K = twinSet Ω K

theorem c21_2_of_steps
    (hsetup : Q3T8.Asc77.C21_setup)
    (hfalse : ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
      (K K' : Subgroup G) (z u : G) (J : Subgroup G) (t : G) (W : Subgroup G),
      Q3T8.Asc77.Hyp21 Ω K K' z u J t W → False) : Q3T8.Asc77.C21_2 := by
  intro G _ _ _ Ω K K' z hs
  by_contra hne
  obtain ⟨u, J, t, W, h⟩ := hsetup G Ω K K' z hs hne
  exact hfalse G Ω K K' z u J t W h
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
variable {G : Type} [Group G]
section Conversions
variable [Finite G] {Ω : Set (Subgroup G)} {K K' J W : Subgroup G}
  {z u t : G}

theorem Hyp21.twinFrameData
    (h
    : Q3T8.Asc77.Hyp21 Ω K K' z u J t W) : Q3T8.Asc77.TwinFrameData Ω K K' z u J t where
  mem := h.std.stand.mem
  hz := h.std.hz
  hK' := h.std.hK'
  hne := h.std.hne
  hu := h.hu
  hu2 := h.hu2
  hu1 := h.hu1
  huz := h.huz
  hJ := h.hJ
  ht := h.ht
  htu := h.htu

theorem Hyp21.of_twinFrameData
    (hs
    : Q3T8.Asc77.Std7 Ω K K' z) (h : Q3T8.Asc77.TwinFrameData Ω K K' z u J t)
    (hW : W ∈ WSet Ω) (hzW : z ∈ W) (htW : t ∈ W) : Q3T8.Asc77.Hyp21 Ω K K' z u J t W where
  std := hs
  hu := h.hu
  hu2 := h.hu2
  hu1 := h.hu1
  huz := h.huz
  hJ := h.hJ
  ht := h.ht
  htu := h.htu
  hW := hW
  hzW := hzW
  htW := htW
end Conversions
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected

structure TwinFrameSetting {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G))
    (K K' J : Subgroup G) (z u t : G) : Prop where
  hyp : Q3T7M.HM Ω
  aEmpty : ∀ M ∈ Ω, AEmpty Ω M
  trans : ∀ M ∈ Ω, ∃ g : G, conjSub g K = M
  below : Q3T8.Generic.CITBelowU (Nat.card G)
  thm7 : Q3T8.Asc77.Thm7TypedBelow (Nat.card G)
  frame : Q3T8.Asc77.TwinFrameData Ω K K' z u J t

@[expose] def TwinFrameHyp51z : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' J : Subgroup G) (z u t : G), Q3T8.Asc77.TwinFrameSetting Ω K K' J z u t →
      Hyp51At (Subgroup.closure {z, u, t}) z

@[expose] def TwinFrameHyp51t : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' J : Subgroup G) (z u t : G), Q3T8.Asc77.TwinFrameSetting Ω K K' J z u t →
      Hyp51At (Subgroup.closure {z, u, t}) t ∧ Hyp51At (Subgroup.closure {z, u, t}) (t * z)

@[expose] def TwinFrameHyp51u : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' J : Subgroup G) (z u t : G), Q3T8.Asc77.TwinFrameSetting Ω K K' J z u t →
      Hyp51At (Subgroup.closure {z, u, t}) u ∧ Hyp51At (Subgroup.closure {z, u, t}) (u * z) ∧
        Hyp51At (Subgroup.closure {z, u, t}) (u * t) ∧
          Hyp51At (Subgroup.closure {z, u, t}) (u * t * z)

@[expose] def TwinFrameHyp51 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' J : Subgroup G) (z u t : G), Q3T8.Asc77.TwinFrameSetting Ω K K' J z u t →
      Hyp51 (Subgroup.closure {z, u, t})
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
theorem exists_twinSylow
    (hΩ
    : Q3T7M.HM Ω)
    {K K' J : Subgroup G} {z : G} (hK : K ∈ Ω) (hz : IsUniqueInvolution K z)
    (hK' : K' ∈ twinSet Ω K) (hne : K' ≠ K) (hJ : J ∈ omegaOfSet Ω (twinSet Ω K)) :
    ∃ (S : Sylow 2 G) (R R' T : Subgroup G), IsSylow2In R K ∧ IsSylow2In R' K' ∧
      IsSylow2In T J ∧ R ≤ (S : Subgroup G) ∧ R' ≤ (S : Subgroup G) ∧ T ≤ (S : Subgroup G) ∧
      Commutes R R' ∧ Commutes R T ∧ Commutes R' T := by
  have hK'Ω : K' ∈ Ω := hK'.1
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hK'
  have hJΩ : J ∈ Ω := hJ.1
  have hJK : J ∈ omegaNbr Ω K := hJ.2 K (mem_twinSet_self hK hz)
  have hJK' : J ∈ omegaNbr Ω K' := hJ.2 K' hK'
  obtain ⟨-, hJneK, T, hT, hTJ, hTN⟩ := hJK
  have hJneK' : J ≠ K' := hJK'.2.1
  have hTsyl : IsSylow2In T J := hΩ.isSylow2In_of_mem_RSet_of_le hJΩ hT hTJ
  have hT2 : IsPGroup 2 ↥T := hTsyl.2.1
  have hT8 : 8 ≤ Nat.card T := hΩ.eight_le_of_mem_RSet hT
  have hTc : T ≤ Subgroup.centralizer ({z} : Set G) := le_centralizer_of_le_normalizer hz hTN
  have hTN' : T ≤ Subgroup.normalizer (K' : Set G) :=
    hΩ.le_normalizer_of_le_centralizer hK'Ω hJΩ hJneK'.symm hzK' hTJ hT2 (by omega) hTc
  obtain ⟨R, hRsyl, hRfix⟩ := exists_sylow_normalized hT2 hTN
  have hRset : R ∈ RSet Ω := mem_RSet_of_isSylow2In hK hRsyl
  have hTnR : T ≤ Subgroup.normalizer (R : Set G) := fun t ht =>
    mem_normalizer_iff_conjSub_eq.mpr (hRfix t ht)
  have hTR2 : IsPGroup 2 ↥(T ⊔ R) := hT2.to_sup_of_normal_right' hRsyl.2.1 hTnR
  have hKN : K ≤ Subgroup.normalizer (K' : Set G) :=
    hΩ.le_normalizer_of_twin hK hK'Ω hne.symm hz hzK'
  have hPN : T ⊔ R ≤ Subgroup.normalizer (K' : Set G) := sup_le hTN' (hRsyl.1.trans hKN)
  obtain ⟨R', hR'syl, hR'fix⟩ := exists_sylow_normalized hTR2 hPN
  have hR'set : R' ∈ RSet Ω := mem_RSet_of_isSylow2In hK'Ω hR'syl
  have hPnR' : T ⊔ R ≤ Subgroup.normalizer (R' : Set G) := fun t ht =>
    mem_normalizer_iff_conjSub_eq.mpr (hR'fix t ht)
  have hQ2 : IsPGroup 2 ↥((T ⊔ R) ⊔ R') := hTR2.to_sup_of_normal_right' hR'syl.2.1 hPnR'
  obtain ⟨S, hS⟩ := hQ2.exists_le_sylow
  have hTS : T ≤ (S : Subgroup G) := le_sup_left.trans (le_sup_left.trans hS)
  have hRS : R ≤ (S : Subgroup G) := le_sup_right.trans (le_sup_left.trans hS)
  have hR'S : R' ≤ (S : Subgroup G) := le_sup_right.trans hS
  have hRR' : R ≠ R' := by
    intro h
    have := hΩ.card_le_two_of_le_inf hK hK'Ω hne.symm hRsyl.2.1 hRsyl.1 (h ▸ hR'syl.1)
    have := hΩ.eight_le_of_mem_RSet hRset
    omega
  have hRT : R ≠ T := by
    intro h
    have := hΩ.card_le_two_of_le_inf hK hJΩ hJneK.symm hRsyl.2.1 hRsyl.1 (h ▸ hTsyl.1)
    have := hΩ.eight_le_of_mem_RSet hRset
    omega
  have hR'T : R' ≠ T := by
    intro h
    have := hΩ.card_le_two_of_le_inf hK'Ω hJΩ hJneK'.symm hR'syl.2.1 hR'syl.1 (h ▸ hTsyl.1)
    have := hΩ.eight_le_of_mem_RSet hR'set
    omega
  exact ⟨S, R, R', T, hRsyl, hR'syl, hTsyl, hRS, hR'S, hTS,
    Q3T8.Asc77.l6_7_proved G Ω hΩ S R hRset R' hR'set hRS hR'S hRR',
    Q3T8.Asc77.l6_7_proved G Ω hΩ S R hRset T hT hRS hTS hRT,
    Q3T8.Asc77.l6_7_proved G Ω hΩ S R' hR'set T hT hR'S hTS hR'T⟩

theorem exists_mem_eta_of_sylow
    (hΩ
    : Q3T8.Asc77.HypOmegaMod Ω) {S : Sylow 2 G}
    {η : Set (Subgroup G)} (hη : η ∈ etaSet Ω (S : Subgroup G)) {M T : Subgroup G} {w : G}
    (hM : M ∈ Ω) (hw : IsUniqueInvolution M w) (hT : IsSylow2In T M)
    (hTS : T ≤ (S : Subgroup G)) : w ∈ ⨆ U ∈ η, U := by
  have hTset : T ∈ RSet Ω := mem_RSet_of_isSylow2In hM hT
  have hquat := hΩ.isQuatSub_of_mem_RSet hTset
  obtain ⟨U₀, hU₀T, hcyc, hcard⟩ := hquat.exists_cyclic_index_two
  have hU₀ : U₀ ∈ USet Ω := mem_USet_of_natCard hM hT hU₀T hcyc hcard
  obtain ⟨V, hVη, hVM⟩ :=
      CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen.exists_mem_of_mem_etaSet hΩ hη hM
      ⟨hU₀, hU₀T.trans hTS⟩
    (hU₀T.trans hT.1)
  have hVU : V ∈ USet Ω := (hη.1 hVη).1
  obtain ⟨-, -, -, -, -, -, -, -, h4⟩ := hΩ.exists_data_of_mem_USet hVU
  have hwV : w ∈ V :=
    mem_of_isUniqueInvolution_of_isPGroup hw hVM (hΩ.isPGroup_of_mem_USet hVU) (by omega)
  have hVW : V ≤ ⨆ U ∈ η, U := le_iSup₂_of_le V hVη le_rfl
  exact hVW hwV

theorem exists_twinFrameData
    (hΩ
    : Q3T7M.HM Ω)
    {K K' J : Subgroup G} {z t : G} (hK : K ∈ Ω) (hz : IsUniqueInvolution K z)
    (hK' : K' ∈ twinSet Ω K) (hne : K' ≠ K) (hJ : J ∈ omegaOfSet Ω (twinSet Ω K))
    (ht : IsUniqueInvolution J t) :
    ∃ (u : G) (W : Subgroup G), Q3T8.Asc77.TwinFrameData Ω K K' z u J t ∧ W ∈ WSet Ω ∧ z ∈ W ∧ t ∈
        W := by
  obtain ⟨S, R, R', T, hRsyl, hR'syl, hTsyl, hRS, hR'S, hTS, hRR', hRT, hR'T⟩ :=
    Q3T8.Asc77.exists_twinSylow hΩ hK hz hK' hne hJ
  have hK'Ω : K' ∈ Ω := hK'.1
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hK'
  have hRset : R ∈ RSet Ω := mem_RSet_of_isSylow2In hK hRsyl
  have hR'set : R' ∈ RSet Ω := mem_RSet_of_isSylow2In hK'Ω hR'syl
  obtain ⟨u₁, hu₁R, hu₁4⟩ := hΩ.exists_orderOf_eq_four_of_mem_RSet hRset
  obtain ⟨u₂, hu₂R', hu₂4⟩ := hΩ.exists_orderOf_eq_four_of_mem_RSet hR'set
  have hu₁K : u₁ ∈ K := hRsyl.1 hu₁R
  have hu₂K' : u₂ ∈ K' := hR'syl.1 hu₂R'
  have hsq₁ : u₁ * u₁ = z := T7A.sq_eq_of_orderOf_four hz hu₁K hu₁4
  have hsq₂ : u₂ * u₂ = z := T7A.sq_eq_of_orderOf_four hzK' hu₂K' hu₂4
  have hc : u₁ * u₂ = u₂ * u₁ := hRR' u₁ hu₁R u₂ hu₂R'
  have hu₁K' : u₁ ∉ K' := fun h => Q3T8.Asc77.T7A.not_mem_inf_of_orderOf_four (hΩ :
      Q3T8.Asc77.HypOmegaMod Ω) hK hK'Ω hne hu₁4 hu₁K h
  have hu₂K : u₂ ∉ K := fun h => Q3T8.Asc77.T7A.not_mem_inf_of_orderOf_four (hΩ :
      Q3T8.Asc77.HypOmegaMod Ω) hK hK'Ω hne hu₂4 h hu₂K'
  have hu2 : (u₁ * u₂) * (u₁ * u₂) = 1 := by
    calc (u₁ * u₂) * (u₁ * u₂) = u₁ * (u₂ * u₁) * u₂ := by group
      _ = u₁ * (u₁ * u₂) * u₂ := by rw [← hc]
      _ = (u₁ * u₁) * (u₂ * u₂) := by group
      _ = 1 := by rw [hsq₁, hsq₂, hz.sq]
  have hu1 : u₁ * u₂ ≠ 1 := by
    intro h
    apply hu₁K'
    have : u₁ = u₂⁻¹ := by rw [eq_inv_iff_mul_eq_one]; exact h
    rw [this]
    exact K'.inv_mem hu₂K'
  have huz : u₁ * u₂ ≠ z := by
    intro h
    apply hu₁K'
    have : u₁ = z * u₂⁻¹ := by rw [← h]; group
    rw [this]
    exact K'.mul_mem hzK'.mem (K'.inv_mem hu₂K')
  have hT2 : IsPGroup 2 ↥T := hTsyl.2.1
  have hT8 : 8 ≤ Nat.card T := hΩ.eight_le_of_mem_RSet (mem_RSet_of_isSylow2In hJ.1 hTsyl)
  have htT : t ∈ T := mem_of_isUniqueInvolution_of_isPGroup ht hTsyl.1 hT2 (by omega)
  have htu : t * (u₁ * u₂) = (u₁ * u₂) * t := by
    have h1 : u₁ * t = t * u₁ := hRT u₁ hu₁R t htT
    have h2 : u₂ * t = t * u₂ := hR'T u₂ hu₂R' t htT
    calc t * (u₁ * u₂) = (t * u₁) * u₂ := by group
      _ = (u₁ * t) * u₂ := by rw [h1]
      _ = u₁ * (t * u₂) := by group
      _ = u₁ * (u₂ * t) := by rw [h2]
      _ = (u₁ * u₂) * t := by group
  obtain ⟨η, hη, hηinv⟩ :=
      CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen.exists_invariant_mem_etaSet
      (Q3T7.modU_toGen3 hΩ) S
  have hWmem : (⨆ U ∈ η, U) ∈ WSet Ω := ⟨η, ⟨S, hη, hηinv⟩, rfl⟩
  have hzW := Q3T8.Asc77.exists_mem_eta_of_sylow hΩ hη hK hz hRsyl hRS
  have htW := Q3T8.Asc77.exists_mem_eta_of_sylow hΩ hη hJ.1 ht hTsyl hTS
  refine ⟨u₁ * u₂, ⨆ U ∈ η, U, ?_, hWmem, hzW, htW⟩
  exact
    { mem := hK
      hz := hz
      hK' := hK'
      hne := hne
      hu := Subgroup.mul_mem _ (Subgroup.mem_sup_left hu₁K) (Subgroup.mem_sup_right hu₂K')
      hu2 := hu2
      hu1 := hu1
      huz := huz
      hJ := hJ
      ht := ht
      htu := htu }

theorem exists_mem_omegaOfSet_twinSet
    (hΩ
    : Q3T7M.HM Ω)
    {K : Subgroup G} {z : G} (hK : K ∈ Ω) (hz : IsUniqueInvolution K z)
    (hne : KPerp Ω K ≠ twinSet Ω K) : ∃ J ∈ omegaOfSet Ω (twinSet Ω K), J ∉ twinSet Ω K := by
  have hsub : twinSet Ω K ⊆ KPerp Ω K := fun L hL =>
    CFSG.ClassicalInvolution.Q3.Q3T7M.mem_kPerp_of_twin hΩ hL.1 hK
        (isUniqueInvolution_of_mem_twinSet hz hL) hz
  by_contra hcon
  push Not at hcon
  have hJ : ∀ J ∈ KPerp Ω K, J ∈ twinSet Ω K := by
    intro J hJ
    by_contra hJnot
    have hJΩ : J ∈ Ω := by
      rcases Set.mem_insert_iff.mp hJ with h | h
      · exact h ▸ hK
      · exact h.1
    have hmem : J ∈ omegaOfSet Ω (twinSet Ω K) := by
      refine ⟨hJΩ, fun L hL => ?_⟩
      have hKL := (CFSG.ClassicalInvolution.Q3.Q3T7M.l6_3 G Ω hΩ K hK L hL).1
      have hJL : J ∈ KPerp Ω L := hKL ▸ hJ
      rcases Set.mem_insert_iff.mp hJL with h | h
      · exact absurd (h ▸ hL) hJnot
      · exact h
    exact hJnot (hcon J hmem)
  exact hne (Set.Subset.antisymm (fun J hJ' => hJ J hJ') hsub)

theorem c21_setup :
    Q3T8.Asc77.C21_setup := by
  intro G _ _ _ Ω K K' z hs hne
  have hΩ : Q3T7M.HM Ω := hs.stand.modU
  have hK : K ∈ Ω := hs.stand.mem
  obtain ⟨J, hJ, -⟩ := Q3T8.Asc77.exists_mem_omegaOfSet_twinSet hΩ hK hs.hz hne
  obtain ⟨t, ht⟩ := hΩ.exists_uniqueInvolution hJ.1
  obtain ⟨u, W, hframe, hW, hzW, htW⟩ :=
    Q3T8.Asc77.exists_twinFrameData hΩ hK hs.hz hs.hK' hs.hne hJ ht
  exact ⟨u, J, t, W, Q3T8.Asc77.Hyp21.of_twinFrameData hs hframe hW hzW htW⟩
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
namespace T7A
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.T7A

theorem exists_conj_sylow_pair
    (hΩ
    : Q3T8.Asc77.HypOmegaMod Ω)
    {K K' R R' R₀ R₀' : Subgroup G} {z : G} (hK : K ∈ Ω) (hK' : K' ∈ Ω) (hne : K' ≠ K)
    (hz : IsUniqueInvolution K z) (hz' : IsUniqueInvolution K' z) (hR : IsSylow2In R K)
    (hR' : IsSylow2In R' K') (hc : Commutes R R') (hR₀ : IsSylow2In R₀ K)
    (hR₀' : IsSylow2In R₀' K') (hc₀ : Commutes R₀ R₀') :
    ∃ g ∈ K ⊔ K', conjSub g R₀ = R ∧ conjSub g R₀' = R' := by
  have hQ := Q3T8.Asc77.T7A.isSylow2In_sup_of_twin hΩ hK hK' hne hz hz' hR hR' hc
  have hQ₀ := Q3T8.Asc77.T7A.isSylow2In_sup_of_twin hΩ hK hK' hne hz hz' hR₀ hR₀' hc₀
  obtain ⟨g, hgQ, hg⟩ := exists_conjSub_eq_of_isSylow2In hQ₀ hQ
  have hKN : K' ≤ Subgroup.normalizer (K : Set G) := hΩ.le_normalizer_of_twin hK' hK hne hz' hz
  have hK'N : K ≤ Subgroup.normalizer (K' : Set G) :=
    hΩ.le_normalizer_of_twin hK hK' hne.symm hz hz'
  have hgK : conjSub g K = K :=
    mem_normalizer_iff_conjSub_eq.mp ((sup_le Subgroup.le_normalizer hKN) hgQ)
  have hgK' : conjSub g K' = K' :=
    mem_normalizer_iff_conjSub_eq.mp ((sup_le hK'N Subgroup.le_normalizer) hgQ)
  have hP2 : IsPGroup 2 ↥(R ⊔ R') := hQ.2.1
  refine ⟨g, hgQ, ?_, ?_⟩
  · have h1 : IsSylow2In (conjSub g R₀) K := by
      have := hR₀.conj g
      rwa [hgK] at this
    have h1le : conjSub g R₀ ≤ R ⊔ R' := by
      rw [← hg, conjSub_sup_eq]
      exact le_sup_left
    have hT2 : IsPGroup 2 ↥((R ⊔ R') ⊓ K) := hP2.to_le inf_le_left
    have hTR : (R ⊔ R') ⊓ K = R := hR.eq_of_le hT2 inf_le_right (le_inf le_sup_left hR.1)
    have h2 : conjSub g R₀ ≤ R := by
      rw [← hTR]
      exact le_inf h1le h1.1
    exact Subgroup.eq_of_le_of_card_ge h2 (h1.natCard_eq hR).ge
  · have h1 : IsSylow2In (conjSub g R₀') K' := by
      have := hR₀'.conj g
      rwa [hgK'] at this
    have h1le : conjSub g R₀' ≤ R ⊔ R' := by
      rw [← hg, conjSub_sup_eq]
      exact le_sup_right
    have hT2 : IsPGroup 2 ↥((R ⊔ R') ⊓ K') := hP2.to_le inf_le_left
    have hTR : (R ⊔ R') ⊓ K' = R' := hR'.eq_of_le hT2 inf_le_right (le_inf le_sup_right hR'.1)
    have h2 : conjSub g R₀' ≤ R' := by
      rw [← hTR]
      exact le_inf h1le h1.1
    exact Subgroup.eq_of_le_of_card_ge h2 (h1.natCard_eq hR').ge
end T7A

theorem exists_twinFrameData_of_sylows
    (hΩ
    : Q3T7M.HM Ω)
    {K K' J R₁ R₂ : Subgroup G} {z t : G} (hK : K ∈ Ω) (hz : IsUniqueInvolution K z)
    (hK' : K' ∈ twinSet Ω K) (hne : K' ≠ K) (hJ : J ∈ omegaOfSet Ω (twinSet Ω K))
    (ht : IsUniqueInvolution J t) (hR₁ : IsSylow2In R₁ K) (hR₂ : IsSylow2In R₂ K')
    (hc : Commutes R₁ R₂) :
    ∃ g ∈ K ⊔ K', ∃ W : Subgroup G, conjSub g J ∈ omegaOfSet Ω (twinSet Ω K) ∧
      IsUniqueInvolution (conjSub g J) (g * t * g⁻¹) ∧ W ∈ WSet Ω ∧ z ∈ W ∧ g * t * g⁻¹ ∈ W ∧
      ∀ x ∈ R₁, ∀ y ∈ R₂, orderOf x = 4 → orderOf y = 4 →
        Q3T8.Asc77.TwinFrameData Ω K K' z (x * y) (conjSub g J) (g * t * g⁻¹) := by
  have hK'Ω : K' ∈ Ω := hK'.1
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hK'
  have hJΩ : J ∈ Ω := hJ.1
  obtain ⟨S₀, R₀, R₀', T₀, hR₀, hR₀', hT₀, hR₀S, hR₀'S, hT₀S, hc₀, hRT₀, hR'T₀⟩ :=
    Q3T8.Asc77.exists_twinSylow hΩ hK hz hK' hne hJ
  obtain ⟨g, hgQ, hgR, hgR'⟩ := Q3T8.Asc77.T7A.exists_conj_sylow_pair hΩ hK hK'Ω hne hz hzK' hR₁
      hR₂ hc
    hR₀ hR₀' hc₀
  have hKN : K' ≤ Subgroup.normalizer (K : Set G) := hΩ.le_normalizer_of_twin hK'Ω hK hne hzK' hz
  have hgK : conjSub g K = K :=
    mem_normalizer_iff_conjSub_eq.mp ((sup_le Subgroup.le_normalizer hKN) hgQ)
  have hgiK : conjSub g⁻¹ K = K :=
    mem_normalizer_iff_conjSub_eq.mp (Subgroup.inv_mem _ ((sup_le Subgroup.le_normalizer hKN) hgQ))
  have hJΩ' : conjSub g J ∈ Ω := hΩ.conjInvariant g J hJΩ
  have ht' : IsUniqueInvolution (conjSub g J) (g * t * g⁻¹) := ht.conj g
  have hJ' : conjSub g J ∈ omegaOfSet Ω (twinSet Ω K) := by
    refine ⟨hJΩ', fun L hL => ?_⟩
    have hL' : conjSub g⁻¹ L ∈ twinSet Ω K := by
      have := twinSet_conj hΩ.conjInvariant hL g⁻¹
      rwa [hgiK] at this
    have := omegaNbr_conj hΩ.conjInvariant (hJ.2 _ hL') g
    rwa [conjSub_conjSub_inv] at this
  have hTsyl : IsSylow2In (conjSub g T₀) (conjSub g J) := hT₀.conj g
  have hT8 : 8 ≤ Nat.card ↥(conjSub g T₀) :=
    hΩ.eight_le_of_mem_RSet (mem_RSet_of_isSylow2In hJΩ' hTsyl)
  have htT : g * t * g⁻¹ ∈ conjSub g T₀ :=
    mem_of_isUniqueInvolution_of_isPGroup ht' hTsyl.1 hTsyl.2.1 (by omega)
  have hcRT : Commutes R₁ (conjSub g T₀) := by
    have := hRT₀.conjSub g
    rwa [hgR] at this
  have hcR'T : Commutes R₂ (conjSub g T₀) := by
    have := hR'T₀.conjSub g
    rwa [hgR'] at this
  obtain ⟨S₁, hS₁⟩ : ∃ S₁ : Sylow 2 G, conjSub g (S₀ : Subgroup G) ≤ (S₁ : Subgroup G) :=
    (isPGroup_conjSub g S₀.isPGroup').exists_le_sylow
  have hS₀ : ∀ {A : Subgroup G}, A ≤ (S₀ : Subgroup G) → conjSub g A ≤ (S₁ : Subgroup G) :=
    fun hA => (conjSub_mono hA).trans hS₁
  have hR₁S : R₁ ≤ (S₁ : Subgroup G) := by rw [← hgR]; exact hS₀ hR₀S
  have hTS : conjSub g T₀ ≤ (S₁ : Subgroup G) := hS₀ hT₀S
  obtain ⟨η, hη, hηinv⟩ :=
      CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen.exists_invariant_mem_etaSet
      (Q3T7.modU_toGen3 hΩ) S₁
  have hWmem : (⨆ U ∈ η, U) ∈ WSet Ω := ⟨η, ⟨S₁, hη, hηinv⟩, rfl⟩
  have hzW := Q3T8.Asc77.exists_mem_eta_of_sylow hΩ hη hK hz hR₁ hR₁S
  have htW := Q3T8.Asc77.exists_mem_eta_of_sylow hΩ hη hJΩ' ht' hTsyl hTS
  refine ⟨g, hgQ, ⨆ U ∈ η, U, hJ', ht', hWmem, hzW, htW, ?_⟩
  intro x hx y hy hx4 hy4
  have hxK : x ∈ K := hR₁.1 hx
  have hyK' : y ∈ K' := hR₂.1 hy
  have hsqx : x * x = z := T7A.sq_eq_of_orderOf_four hz hxK hx4
  have hsqy : y * y = z := T7A.sq_eq_of_orderOf_four hzK' hyK' hy4
  have hcxy : x * y = y * x := hc x hx y hy
  have hxK' : x ∉ K' := fun h => Q3T8.Asc77.T7A.not_mem_inf_of_orderOf_four (hΩ :
      Q3T8.Asc77.HypOmegaMod Ω) hK hK'Ω hne hx4 hxK h
  have hyK : y ∉ K := fun h => Q3T8.Asc77.T7A.not_mem_inf_of_orderOf_four (hΩ :
      Q3T8.Asc77.HypOmegaMod Ω) hK hK'Ω hne hy4 h hyK'
  have hu2 : (x * y) * (x * y) = 1 := by
    calc (x * y) * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [← hcxy]
      _ = (x * x) * (y * y) := by group
      _ = 1 := by rw [hsqx, hsqy, hz.sq]
  have hu1 : x * y ≠ 1 := by
    intro h
    apply hxK'
    have : x = y⁻¹ := by rw [eq_inv_iff_mul_eq_one]; exact h
    rw [this]
    exact K'.inv_mem hyK'
  have huz : x * y ≠ z := by
    intro h
    apply hxK'
    have : x = z * y⁻¹ := by rw [← h]; group
    rw [this]
    exact K'.mul_mem hzK'.mem (K'.inv_mem hyK')
  have htu : (g * t * g⁻¹) * (x * y) = (x * y) * (g * t * g⁻¹) := by
    have h1 : x * (g * t * g⁻¹) = (g * t * g⁻¹) * x := hcRT x hx _ htT
    have h2 : y * (g * t * g⁻¹) = (g * t * g⁻¹) * y := hcR'T y hy _ htT
    calc (g * t * g⁻¹) * (x * y) = ((g * t * g⁻¹) * x) * y := by group
      _ = (x * (g * t * g⁻¹)) * y := by rw [h1]
      _ = x * ((g * t * g⁻¹) * y) := by group
      _ = x * (y * (g * t * g⁻¹)) := by rw [h2]
      _ = (x * y) * (g * t * g⁻¹) := by group
  exact
    { mem := hK
      hz := hz
      hK' := hK'
      hne := hne
      hu := Subgroup.mul_mem _ (Subgroup.mem_sup_left hxK) (Subgroup.mem_sup_right hyK')
      hu2 := hu2
      hu1 := hu1
      huz := huz
      hJ := hJ'
      ht := ht'
      htu := htu }
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
theorem exists_twinFrameData_at
    (hΩ
    : Q3T7M.HM Ω)
    {K K' J' : Subgroup G} {z u t' : G} (hK : K ∈ Ω) (hz : IsUniqueInvolution K z)
    (hK' : K' ∈ twinSet Ω K) (hne : K' ≠ K) (hu : u ∈ K ⊔ K') (hu2 : u * u = 1) (hu1 : u ≠ 1)
    (huz : u ≠ z) (hJ' : J' ∈ omegaOfSet Ω (twinSet Ω K)) (ht' : IsUniqueInvolution J' t') :
    ∃ g ∈ K ⊔ K', ∃ W : Subgroup G, Q3T8.Asc77.TwinFrameData Ω K K' z u (conjSub g J') (g * t' *
        g⁻¹) ∧
      W ∈ WSet Ω ∧ z ∈ W ∧ g * t' * g⁻¹ ∈ W := by
  have hK'Ω : K' ∈ Ω := hK'.1
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hK'
  obtain ⟨R₁, R₂, hR₁, hR₂, hc, huR⟩ :=
    Q3T8.Asc77.T7A.exists_sylow_pair_of_mem (hΩ : Q3T8.Asc77.HypOmegaMod Ω) hK hK'Ω hne hz hzK' hu
        hu2 hu1
  obtain ⟨g, hgQ, W, hJ'', ht'', hW, hzW, htW, hfr⟩ :=
    Q3T8.Asc77.exists_twinFrameData_of_sylows hΩ hK hz hK' hne hJ' ht' hR₁ hR₂ hc
  obtain ⟨x, hx, y, hy, rfl⟩ := AscE186.exists_mul_of_mem_sup_of_commutes hc huR
  have hcxy : x * y = y * x := hc x hx y hy
  have hsq : (x * x) * (y * y) = 1 := by
    calc (x * x) * (y * y) = x * (x * y) * y := by group
      _ = x * (y * x) * y := by rw [hcxy]
      _ = (x * y) * (x * y) := by group
      _ = 1 := hu2
  have hxK : x ∈ K := hR₁.1 hx
  have hyK' : y ∈ K' := hR₂.1 hy
  have hcard : Nat.card ↥(R₁ ⊓ R₂) ≤ 2 :=
    hΩ.card_le_two_of_le_inf hK hK'Ω hne.symm (hR₁.2.1.to_le inf_le_left)
      (inf_le_left.trans hR₁.1) (inf_le_right.trans hR₂.1)
  have hA : ∀ e ∈ R₁ ⊓ R₂, e * e = 1 := by
    intro e he
    have hd : orderOf e ∣ Nat.card ↥(R₁ ⊓ R₂) := Subgroup.orderOf_dvd_natCard _ he
    have hpos : 0 < Nat.card ↥(R₁ ⊓ R₂) := Nat.card_pos
    have h2 : orderOf e ∣ 2 := by
      interval_cases hc2 : Nat.card ↥(R₁ ⊓ R₂)
      · exact hd.trans (one_dvd 2)
      · exact hd
    have := orderOf_dvd_iff_pow_eq_one.mp h2
    rwa [pow_two] at this
  have hxxA : x * x ∈ R₁ ⊓ R₂ := by
    refine ⟨R₁.mul_mem hx hx, ?_⟩
    have : x * x = (y * y)⁻¹ := eq_inv_of_mul_eq_one_left hsq
    rw [this]
    exact R₂.inv_mem (R₂.mul_mem hy hy)
  have hx2 : x * x = z := by
    rcases hz.unique (x * x) (K.mul_mem hxK hxK) (hA _ hxxA) with h1 | h1
    · exfalso
      have hy2 : y * y = 1 := by rwa [h1, one_mul] at hsq
      rcases hz.unique x hxK h1 with h2 | h2 <;> rcases hzK'.unique y hyK' hy2 with h3 | h3
      · exact hu1 (by rw [h2, h3, one_mul])
      · exact huz (by rw [h2, h3, one_mul])
      · exact huz (by rw [h2, h3, mul_one])
      · exact hu1 (by rw [h2, h3]; exact hz.sq)
    · exact h1
  have hy2 : y * y = z := by
    have h1 : y * y = z⁻¹ := eq_inv_of_mul_eq_one_right (by rwa [hx2] at hsq)
    rw [h1]
    exact inv_eq_of_mul_eq_one_right hz.sq
  exact ⟨g, hgQ, W, hfr x hx y hy (T7A.orderOf_eq_four_of_sq hz hx2)
    (T7A.orderOf_eq_four_of_sq hz hy2), hW, hzW, htW⟩

theorem Hyp21.conj
    {K
    K' J W : Subgroup G} {z u t : G} (h : Q3T8.Asc77.Hyp21 Ω K K' z u J t W)
    (g : G) :
    Q3T8.Asc77.Hyp21 Ω (conjSub g K) (conjSub g K') (g * z * g⁻¹) (g * u * g⁻¹) (conjSub g J)
      (g * t * g⁻¹) (conjSub g W) := by
  have hΩc : ConjInvariant Ω := h.std.stand.hyp.conjInvariant
  have hinj : ∀ a b : G, g * a * g⁻¹ = g * b * g⁻¹ → a = b := fun a b hab => by
    simpa using hab
  refine
    { std :=
        { stand := h.std.stand.of_mem (hΩc g K h.std.stand.mem)
          disconnected := h.std.disconnected
          hz := h.std.hz.conj g
          hK' := twinSet_conj hΩc h.std.hK' g
          hne := fun e => h.std.hne (conjSub_injective g e)
          cex := h.std.cex }
      hu := ?_
      hu2 := ?_
      hu1 := ?_
      huz := fun e => h.huz (hinj _ _ e)
      hJ := ?_
      ht := h.ht.conj g
      htu := ?_
      hW := WSet.conj hΩc h.hW g
      hzW := conj_mem_conjSub h.hzW
      htW := conj_mem_conjSub h.htW }
  · have := conj_mem_conjSub (n := g) h.hu
    rwa [T7A.conjSub_sup_eq] at this
  · calc (g * u * g⁻¹) * (g * u * g⁻¹) = g * (u * u) * g⁻¹ := by group
      _ = 1 := by rw [h.hu2]; group
  · intro e
    apply h.hu1
    have := congrArg (fun x => g⁻¹ * x * g) e
    simpa [mul_assoc] using this
  · refine ⟨hΩc g J h.hJ.1, fun L hL => ?_⟩
    have hL' : conjSub g⁻¹ L ∈ twinSet Ω K := by
      have := twinSet_conj hΩc hL g⁻¹
      rwa [conjSub_inv_conjSub] at this
    have := omegaNbr_conj hΩc (h.hJ.2 _ hL') g
    rwa [conjSub_conjSub_inv] at this
  · calc (g * t * g⁻¹) * (g * u * g⁻¹) = g * (t * u) * g⁻¹ := by group
      _ = g * (u * t) * g⁻¹ := by rw [h.htu]
      _ = (g * u * g⁻¹) * (g * t * g⁻¹) := by group
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
section Frame
variable {K K' J : Subgroup G} {z u t : G}

theorem TwinFrameData.comm_zt
    (hΩ
    : Q3T7M.HM Ω)
    (h : Q3T8.Asc77.TwinFrameData Ω K K' z u J t) : z * t = t * z := by
  obtain ⟨-, -, R, hR, hRJ, hRN⟩ := h.hJ.2 K (mem_twinSet_self h.mem h.hz)
  have hRsyl : IsSylow2In R J := hΩ.isSylow2In_of_mem_RSet_of_le h.hJ.1 hR hRJ
  have h8 := hΩ.eight_le_of_mem_RSet hR
  have htR : t ∈ R := mem_of_isUniqueInvolution_of_isPGroup h.ht hRsyl.1 hRsyl.2.1 (by omega)
  exact (Subgroup.mem_centralizer_singleton_iff.mp
    (le_centralizer_of_le_normalizer h.hz hRN htR)).symm

theorem TwinFrameData.t_not_mem_closure
    (hΩ
    : Q3T7M.HM Ω)
    (h : Q3T8.Asc77.TwinFrameData Ω K K' z u J t) : t ∉ Subgroup.closure ({z, u} : Set G) := by
  intro htcl
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet h.hz h.hK'
  obtain ⟨S, R, R', T, hRsyl, hR'syl, hTsyl, hRS, hR'S, hTS, hRR', hRT, hR'T⟩ :=
    Q3T8.Asc77.exists_twinSylow hΩ h.mem h.hz h.hK' h.hne h.hJ
  have hQ := Q3T8.Asc77.T7A.isSylow2In_sup_of_twin (hΩ : Q3T8.Asc77.HypOmegaMod Ω) h.mem h.hK'.1
      h.hne h.hz hzK' hRsyl hR'syl hRR'
  have hT8 : 8 ≤ Nat.card T := hΩ.eight_le_of_mem_RSet (mem_RSet_of_isSylow2In h.hJ.1 hTsyl)
  have htT : t ∈ T := mem_of_isUniqueInvolution_of_isPGroup h.ht hTsyl.1 hTsyl.2.1 (by omega)
  have htQ : t ∈ K ⊔ K' := by
    have : Subgroup.closure ({z, u} : Set G) ≤ K ⊔ K' := by
      rw [Subgroup.closure_le]
      intro x hx
      rcases hx with rfl | rfl
      · exact Subgroup.mem_sup_left h.hz.mem
      · exact h.hu
    exact this htcl
  have hS2 : IsPGroup 2 ↥((S : Subgroup G) ⊓ (K ⊔ K')) :=
    (Sylow.isPGroup' S).to_le inf_le_left
  have heq : (S : Subgroup G) ⊓ (K ⊔ K') = R ⊔ R' :=
    hQ.eq_of_le hS2 inf_le_right (le_inf (sup_le hRS hR'S) hQ.1)
  have htRR' : t ∈ R ⊔ R' := by
    rw [← heq]
    exact ⟨hTS htT, htQ⟩
  obtain ⟨x, hx, y, hy, hxy⟩ := AscE186.exists_mul_of_mem_sup_of_commutes hRR' htRR'
  have hxc : ∀ r ∈ R, r * x = x * r := by
    intro r hr
    have h1 : r * t = t * r := hRT r hr t htT
    have h2 : r * y = y * r := hRR' r hr y hy
    have : (r * x) * y = (x * r) * y := by
      calc (r * x) * y = r * (x * y) := by group
        _ = r * t := by rw [hxy]
        _ = t * r := h1
        _ = (x * y) * r := by rw [hxy]
        _ = x * (y * r) := by group
        _ = x * (r * y) := by rw [h2]
        _ = (x * r) * y := by group
    exact mul_right_cancel this
  have hyc : ∀ r ∈ R', r * y = y * r := by
    intro r hr
    have h1 : r * t = t * r := hR'T r hr t htT
    have h2 : x * r = r * x := hRR' x hx r hr
    have : x * (r * y) = x * (y * r) := by
      calc x * (r * y) = (x * r) * y := by group
        _ = (r * x) * y := by rw [h2]
        _ = r * (x * y) := by group
        _ = r * t := by rw [hxy]
        _ = t * r := h1
        _ = (x * y) * r := by rw [hxy]
        _ = x * (y * r) := by group
    exact mul_left_cancel this
  have hxz := T7A.eq_one_or_eq_of_central h.hz
    (hΩ.isQuatSub_of_mem_RSet (mem_RSet_of_isSylow2In h.mem hRsyl)) hRsyl.1 hx hxc
  have hyz := T7A.eq_one_or_eq_of_central hzK'
    (hΩ.isQuatSub_of_mem_RSet (mem_RSet_of_isSylow2In h.hK'.1 hR'syl)) hR'syl.1 hy hyc
  have htz := h.t_ne_z
  have ht1 := h.ht.ne_one
  rcases hxz with h1 | h1 <;> rcases hyz with h2 | h2
  · exact ht1 (by rw [← hxy, h1, h2, one_mul])
  · exact htz (by rw [← hxy, h1, h2, one_mul])
  · exact htz (by rw [← hxy, h1, h2, mul_one])
  · exact ht1 (by rw [← hxy, h1, h2]; exact h.hz.sq)

theorem TwinFrameData.comm_gen
    (hΩ
    : Q3T7M.HM Ω)
    (h : Q3T8.Asc77.TwinFrameData Ω K K' z u J t) :
    ∀ a ∈ ({z, u, t} : Set G), ∀ b ∈ ({z, u, t} : Set G), a * b = b * a := by
  have hzu := h.comm_zu
  have hzt := h.comm_zt hΩ
  have hut : u * t = t * u := h.htu.symm
  intro a ha b hb
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
  · rfl
  · exact hzu
  · exact hzt
  · exact hzu.symm
  · rfl
  · exact hut
  · exact hzt.symm
  · exact hut.symm
  · rfl

theorem twinFrame_isElemAbelian
    (hΩ
    : Q3T7M.HM Ω)
    (h : Q3T8.Asc77.TwinFrameData Ω K K' z u J t) :
    IsElemAbelian 2 (Subgroup.closure ({z, u, t} : Set G)) := by
  have hcomm := T7A.commutes_closure (h.comm_gen hΩ)
  have hsq : ∀ a ∈ ({z, u, t} : Set G), a * a = 1 := by
    intro a ha
    rcases ha with rfl | rfl | rfl
    · exact h.hz.sq
    · exact h.hu2
    · exact h.ht.sq
  refine ⟨⟨⟨fun a b => Subtype.ext (hcomm _ a.2 _ b.2)⟩⟩, fun x hx => ?_⟩
  rw [pow_two]
  exact T7A.sq_closure hsq (h.comm_gen hΩ) x hx

theorem twinFrame_natCard_eight
    (hΩ
    : Q3T7M.HM Ω)
    (h : Q3T8.Asc77.TwinFrameData Ω K K' z u J t) :
    Nat.card ↥(Subgroup.closure ({z, u, t} : Set G)) = 8 := by
  have hzt := h.comm_zt hΩ
  have hD := T7A.isElemAbelian2_closure_pair h.hu2 h.hz.sq h.hu1 h.hz.ne_one h.huz h.comm_zu.symm
  have ht2 : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact h.ht.sq) h.ht.ne_one
  have hcl : Subgroup.closure ({z, u, t} : Set G) =
      Subgroup.closure ({u, z} : Set G) ⊔ Subgroup.zpowers t := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      intro x hx
      rcases hx with rfl | rfl | rfl
      · exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
      · exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
      · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    · refine sup_le ?_ (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)))
      rw [Subgroup.closure_le]
      intro x hx
      rcases hx with rfl | rfl
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.subset_closure (by simp)
  have hcomm : Commutes (Subgroup.closure ({u, z} : Set G)) (Subgroup.zpowers t) := by
    have hle : Subgroup.closure ({u, z} : Set G) ≤ Subgroup.centralizer ({t} : Set G) := by
      rw [Subgroup.closure_le]
      intro x hx
      rcases hx with rfl | rfl
      · exact Subgroup.mem_centralizer_singleton_iff.mpr h.htu.symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hzt
    intro x hx y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have : Commute x t := Subgroup.mem_centralizer_singleton_iff.mp (hle hx)
    exact (this.zpow_right i).eq
  have hinf : Subgroup.closure ({u, z} : Set G) ⊓ Subgroup.zpowers t = ⊥ := by
    rw [eq_bot_iff]
    intro e he
    rcases T7A.eq_one_or_eq_of_mem_zpowers ht2 he.2 with h1 | h1
    · rw [h1]
      exact Subgroup.one_mem _
    · exfalso
      apply h.t_not_mem_closure hΩ
      rw [Set.pair_comm]
      rw [← h1]
      exact he.1
  have hN := T7A.card_sup_mul_card_inf (T7A.le_normalizer_of_commutes hcomm)
  rw [hinf, Subgroup.card_bot, Nat.card_zpowers, ht2, hD.1, mul_one] at hN
  rw [hcl, sup_comm, hN]
  norm_num
end Frame
section C21_3

theorem TwinFrameSetting.of_hyp21
    {K
    K' J W : Subgroup G} {z u t : G}
    (h : Q3T8.Asc77.Hyp21 Ω K K' z u J t W) : Q3T8.Asc77.TwinFrameSetting Ω K K' J z u t where
  hyp := h.std.stand.modU
  aEmpty := h.std.stand.aEmpty
  trans := h.std.stand.trans
  below := h.std.stand.below
  thm7 := h.std.stand.ih.thm7
  frame := h.twinFrameData

theorem c21_3_of
    (hH
    : Q3T8.Asc77.TwinFrameHyp51) : Q3T8.Asc77.C21_3 := by
  intro G _ _ _ Ω K K' z u J t W h
  have hB : Hyp51 (Subgroup.closure ({z, u, t} : Set G)) :=
    hH G Ω K K' J z u t (Q3T8.Asc77.TwinFrameSetting.of_hyp21 h)
  have hD : IsElemAbelian2 (Subgroup.closure ({u, z} : Set G)) 2 :=
    T7A.isElemAbelian2_closure_pair h.hu2 h.std.hz.sq h.hu1 h.std.hz.ne_one h.huz
      h.twinFrameData.comm_zu.symm
  have hDB : Subgroup.closure ({u, z} : Set G) ≤ Subgroup.closure ({z, u, t} : Set G) := by
    apply Subgroup.closure_mono
    intro x hx
    rcases hx with rfl | rfl <;> simp
  exact lemma54_odd_and_eq hB hDB hD
end C21_3
end Asc77

end

end CFSG.ClassicalInvolution.Q3.Q3T8
