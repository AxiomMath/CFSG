module

public import CFSG.ClassicalInvolution.Asc77.AscT7ABasic
public import CFSG.ClassicalInvolution.Asc77.AscL62Final
public import CFSG.ClassicalInvolution.Asc77.AscE189Basic
public import CFSG.ClassicalInvolution.Asc77.AscSix63
public import CFSG.ClassicalInvolution.Asc77.AscSteps182
public import CFSG.ClassicalInvolution.Asc77.AscSteps185

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

namespace T7A

omit [Finite G] in
theorem sq_eq_of_orderOf_four {K : Subgroup G} {z u : G} (hz : IsUniqueInvolution K z)
    (hu : u ∈ K) (hu4 : orderOf u = 4) : u * u = z := by
  have h1 : (u * u) * (u * u) = 1 := by
    have : u ^ 4 = 1 := by rw [← hu4]; exact pow_orderOf_eq_one u
    calc u * u * (u * u) = u ^ 4 := by simp [pow_succ, mul_assoc]
      _ = 1 := this
  rcases hz.unique (u * u) (K.mul_mem hu hu) h1 with h | h
  · exfalso
    have : u ^ 2 = 1 := by rw [pow_two]; exact h
    have h2 := orderOf_dvd_of_pow_eq_one this
    rw [hu4] at h2
    omega
  · exact h

omit [Finite G] in
theorem isPGroup_zpowers_of_orderOf_four {u : G} (hu4 : orderOf u = 4) :
    IsPGroup 2 (Subgroup.zpowers u) :=
  IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hu4]; norm_num)

theorem not_mem_inf_of_orderOf_four (hΩ : HypOmegaMod p f Ω) {K K' : Subgroup G}
    (hK : K ∈ Ω) (hK' : K' ∈ Ω) (hne : K' ≠ K) {u : G} (hu4 : orderOf u = 4) (huK : u ∈ K)
    (huK' : u ∈ K') : False := by
  have := hΩ.eq_of_le_of_le hK hK' (isPGroup_zpowers_of_orderOf_four hu4)
    (by rw [Nat.card_zpowers, hu4]) (Subgroup.zpowers_le.mpr huK) (Subgroup.zpowers_le.mpr huK')
  exact hne this.symm

end T7A

theorem exists_twinSylow (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
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
  have hTsyl : IsSylow2In T J := hΩ.isSylow2In_of_mem_RSet_of_le hp hJΩ hT hTJ
  have hT2 : IsPGroup 2 ↥T := hTsyl.2.1
  have hT8 : 8 ≤ Nat.card T := hΩ.eight_le_of_mem_RSet hp hT
  have hTc : T ≤ Subgroup.centralizer ({z} : Set G) := le_centralizer_of_le_normalizer hz hTN
  have hTN' : T ≤ Subgroup.normalizer (K' : Set G) :=
    hΩ.le_normalizer_of_le_centralizer hp hq hK'Ω hJΩ hJneK'.symm hzK' hTJ hT2 (by omega) hTc
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
    have := hΩ.eight_le_of_mem_RSet hp hRset
    omega
  have hRT : R ≠ T := by
    intro h
    have := hΩ.card_le_two_of_le_inf hK hJΩ hJneK.symm hRsyl.2.1 hRsyl.1 (h ▸ hTsyl.1)
    have := hΩ.eight_le_of_mem_RSet hp hRset
    omega
  have hR'T : R' ≠ T := by
    intro h
    have := hΩ.card_le_two_of_le_inf hK'Ω hJΩ hJneK'.symm hR'syl.2.1 hR'syl.1 (h ▸ hTsyl.1)
    have := hΩ.eight_le_of_mem_RSet hp hR'set
    omega
  exact ⟨S, R, R', T, hRsyl, hR'syl, hTsyl, hRS, hR'S, hTS,
    l6_7_proved p f hp hq G Ω hΩ S R hRset R' hR'set hRS hR'S hRR',
    l6_7_proved p f hp hq G Ω hΩ S R hRset T hT hRS hTS hRT,
    l6_7_proved p f hp hq G Ω hΩ S R' hR'set T hT hR'S hTS hR'T⟩

theorem exists_mem_eta_of_sylow (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω) {S : Sylow 2 G}
    {η : Set (Subgroup G)} (hη : η ∈ etaSet Ω (S : Subgroup G)) {M T : Subgroup G} {w : G}
    (hM : M ∈ Ω) (hw : IsUniqueInvolution M w) (hT : IsSylow2In T M)
    (hTS : T ≤ (S : Subgroup G)) : w ∈ ⨆ U ∈ η, U := by
  have hTset : T ∈ RSet Ω := mem_RSet_of_isSylow2In hM hT
  have hquat := hΩ.isQuatSub_of_mem_RSet hp hTset
  obtain ⟨U₀, hU₀T, hcyc, hcard⟩ := hquat.exists_cyclic_index_two
  have hU₀ : U₀ ∈ USet Ω := mem_USet_of_natCard hM hT hU₀T hcyc hcard
  obtain ⟨V, hVη, hVM⟩ := exists_mem_of_mem_etaSet hp hΩ hη hM ⟨hU₀, hU₀T.trans hTS⟩
    (hU₀T.trans hT.1)
  have hVU : V ∈ USet Ω := (hη.1 hVη).1
  obtain ⟨-, -, -, -, -, -, -, -, h4⟩ := hΩ.exists_data_of_mem_USet hp hVU
  have hwV : w ∈ V :=
    mem_of_isUniqueInvolution_of_isPGroup hw hVM (hΩ.isPGroup_of_mem_USet hp hVU) (by omega)
  have hVW : V ≤ ⨆ U ∈ η, U := le_iSup₂_of_le V hVη le_rfl
  exact hVW hwV

theorem exists_twinFrameData (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    {K K' J : Subgroup G} {z t : G} (hK : K ∈ Ω) (hz : IsUniqueInvolution K z)
    (hK' : K' ∈ twinSet Ω K) (hne : K' ≠ K) (hJ : J ∈ omegaOfSet Ω (twinSet Ω K))
    (ht : IsUniqueInvolution J t) :
    ∃ (u : G) (W : Subgroup G), TwinFrameData Ω K K' z u J t ∧ W ∈ WSet Ω ∧ z ∈ W ∧ t ∈ W := by
  obtain ⟨S, R, R', T, hRsyl, hR'syl, hTsyl, hRS, hR'S, hTS, hRR', hRT, hR'T⟩ :=
    exists_twinSylow hp hq hΩ hK hz hK' hne hJ
  have hK'Ω : K' ∈ Ω := hK'.1
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hK'
  have hRset : R ∈ RSet Ω := mem_RSet_of_isSylow2In hK hRsyl
  have hR'set : R' ∈ RSet Ω := mem_RSet_of_isSylow2In hK'Ω hR'syl
  obtain ⟨u₁, hu₁R, hu₁4⟩ := hΩ.exists_orderOf_eq_four_of_mem_RSet hp hRset
  obtain ⟨u₂, hu₂R', hu₂4⟩ := hΩ.exists_orderOf_eq_four_of_mem_RSet hp hR'set
  have hu₁K : u₁ ∈ K := hRsyl.1 hu₁R
  have hu₂K' : u₂ ∈ K' := hR'syl.1 hu₂R'
  have hsq₁ : u₁ * u₁ = z := T7A.sq_eq_of_orderOf_four hz hu₁K hu₁4
  have hsq₂ : u₂ * u₂ = z := T7A.sq_eq_of_orderOf_four hzK' hu₂K' hu₂4
  have hc : u₁ * u₂ = u₂ * u₁ := hRR' u₁ hu₁R u₂ hu₂R'
  have hu₁K' : u₁ ∉ K' := fun h => T7A.not_mem_inf_of_orderOf_four hΩ hK hK'Ω hne hu₁4 hu₁K h
  have hu₂K : u₂ ∉ K := fun h => T7A.not_mem_inf_of_orderOf_four hΩ hK hK'Ω hne hu₂4 h hu₂K'
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
  have hT8 : 8 ≤ Nat.card T := hΩ.eight_le_of_mem_RSet hp (mem_RSet_of_isSylow2In hJ.1 hTsyl)
  have htT : t ∈ T := mem_of_isUniqueInvolution_of_isPGroup ht hTsyl.1 hT2 (by omega)
  have htu : t * (u₁ * u₂) = (u₁ * u₂) * t := by
    have h1 : u₁ * t = t * u₁ := hRT u₁ hu₁R t htT
    have h2 : u₂ * t = t * u₂ := hR'T u₂ hu₂R' t htT
    calc t * (u₁ * u₂) = (t * u₁) * u₂ := by group
      _ = (u₁ * t) * u₂ := by rw [h1]
      _ = u₁ * (t * u₂) := by group
      _ = u₁ * (u₂ * t) := by rw [h2]
      _ = (u₁ * u₂) * t := by group
  obtain ⟨η, hη, hηinv⟩ := exists_invariant_mem_etaSet hp hq hΩ S
  have hWmem : (⨆ U ∈ η, U) ∈ WSet Ω := ⟨η, ⟨S, hη, hηinv⟩, rfl⟩
  have hzW := exists_mem_eta_of_sylow hp hΩ hη hK hz hRsyl hRS
  have htW := exists_mem_eta_of_sylow hp hΩ hη hJ.1 ht hTsyl hTS
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

theorem exists_mem_omegaOfSet_twinSet (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    {K : Subgroup G} {z : G} (hK : K ∈ Ω) (hz : IsUniqueInvolution K z)
    (hne : KPerp Ω K ≠ twinSet Ω K) : ∃ J ∈ omegaOfSet Ω (twinSet Ω K), J ∉ twinSet Ω K := by
  have hsub : twinSet Ω K ⊆ KPerp Ω K := fun L hL =>
    mem_kPerp_of_twin hΩ hL.1 hK (isUniqueInvolution_of_mem_twinSet hz hL) hz
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
      have hKL := (l6_3 p f hp hq G Ω hΩ K hK L hL).1
      have hJL : J ∈ KPerp Ω L := hKL ▸ hJ
      rcases Set.mem_insert_iff.mp hJL with h | h
      · exact absurd (h ▸ hL) hJnot
      · exact h
    exact hJnot (hcon J hmem)
  exact hne (Set.Subset.antisymm (fun J hJ' => hJ J hJ') hsub)

variable (p f)

theorem c21_setup : C21_setup p f := by
  intro G _ _ _ Ω K K' z hs hne
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  obtain ⟨J, hJ, -⟩ := exists_mem_omegaOfSet_twinSet hp hq hΩ hK hs.hz hne
  obtain ⟨t, ht⟩ := hΩ.exists_uniqueInvolution hp hq hJ.1
  obtain ⟨u, W, hframe, hW, hzW, htW⟩ :=
    exists_twinFrameData hp hq hΩ hK hs.hz hs.hK' hs.hne hJ ht
  exact ⟨u, J, t, W, Hyp21.of_twinFrameData hs hframe hW hzW htW⟩

end CFSG.ClassicalInvolution.Asc77
