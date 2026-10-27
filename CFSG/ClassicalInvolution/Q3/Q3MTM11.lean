module

public import CFSG.ClassicalInvolution.Uniform.U3Thm8
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Asc77.AscMuTabKind
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerGaussUnitary
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.Q3.Q3MT

open CFSG.Blueprint CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Uniform

section Group

theorem m11Sd_no_c4_c2 : ∀ p q : Fin 8 × Fin 2, m11SdMap p ^ 4 = 1 → m11SdMap p ^ 2 ≠ 1 →
    m11SdMap q * m11SdMap q = 1 → m11SdMap q ≠ 1 →
    m11SdMap p * m11SdMap q = m11SdMap q * m11SdMap p → m11SdMap q = m11SdMap p ^ 2 := by
  decide +kernel

theorem exists_conj_mem_m11SdS_of_pGroup {H : Subgroup ↥NativeSporadic.M11} (hH : IsPGroup 2 H) :
    ∃ g : ↥NativeSporadic.M11, ∀ x ∈ H, g⁻¹ * x * g ∈ m11SdS := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS : IsPGroup 2 m11SdS := IsPGroup.of_card (n := 4) (by rw [card_m11SdS]; norm_num)
  have hidx : ¬ 2 ∣ m11SdS.index := by
    have h := Subgroup.card_mul_index m11SdS
    rw [card_m11SdS, card_m11_kernel] at h
    have : m11SdS.index = 495 := by omega
    rw [this]
    norm_num
  obtain ⟨P, hP⟩ := hH.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥NativeSporadic.M11 (hS.toSylow hidx) P
  refine ⟨g, fun x hx => ?_⟩
  have hxP : x ∈ ((g • hS.toSylow hidx : Sylow 2 ↥NativeSporadic.M11) : Subgroup _) := by
    rw [hg]
    exact hP hx
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hxP
  obtain ⟨s, hs, hsx⟩ := hxP
  have hx' : x = g * s * g⁻¹ := by simpa [MulAut.smul_def, MulAut.conj_apply] using hsx.symm
  rw [hx']
  simpa [mul_assoc] using hs

theorem m11_no_c4_c2 {u z : ↥NativeSporadic.M11} (hu4 : u ^ 4 = 1) (hu2 : u ^ 2 ≠ 1)
    (hz2 : z * z = 1) (hz1 : z ≠ 1) (hcomm : z * u = u * z) : z = u ^ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hou : orderOf u = 2 ^ 2 := by
    have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := u) (by simpa using hu2)
      (by simpa using hu4)
    simpa using this
  have hzo : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1
  have hA : IsPGroup 2 (Subgroup.zpowers u) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hou])
  have hB : IsPGroup 2 (Subgroup.zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hzo]; norm_num)
  have hcom : ∀ h ∈ Subgroup.zpowers u, z * h = h * z := by
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact (Commute.zpow_right (show Commute z u from hcomm) k).eq
  have hN : Subgroup.zpowers z ≤ Subgroup.normalizer (Subgroup.zpowers u : Set _) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact (hcom h hh).symm
  have hH : IsPGroup 2 ↥(Subgroup.zpowers u ⊔ Subgroup.zpowers z) :=
    hA.to_sup_of_normal_left' hB hN
  obtain ⟨g, hg⟩ := exists_conj_mem_m11SdS_of_pGroup hH
  obtain ⟨p, hp⟩ := exists_m11SdMap_eq_of_mem
    (hg u (Subgroup.mem_sup_left (Subgroup.mem_zpowers u)))
  obtain ⟨q, hq⟩ := exists_m11SdMap_eq_of_mem
    (hg z (Subgroup.mem_sup_right (Subgroup.mem_zpowers z)))
  have hu'4 : (g⁻¹ * u * g) ^ 4 = 1 := by
    have : (g⁻¹ * u * g) ^ 4 = g⁻¹ * u ^ 4 * g := by
      simpa using conj_pow (a := g⁻¹) (b := u) (i := 4)
    rw [this, hu4]
    group
  have hu'2 : (g⁻¹ * u * g) ^ 2 ≠ 1 := by
    intro h
    apply hu2
    have : (g⁻¹ * u * g) ^ 2 = g⁻¹ * u ^ 2 * g := by
      simpa using conj_pow (a := g⁻¹) (b := u) (i := 2)
    rw [this] at h
    have h2 : u ^ 2 = g * (g⁻¹ * u ^ 2 * g) * g⁻¹ := by group
    rw [h2, h]
    group
  have hz'2 : (g⁻¹ * z * g) * (g⁻¹ * z * g) = 1 := by
    have : (g⁻¹ * z * g) * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g := by group
    rw [this, hz2]
    group
  have hz'1 : g⁻¹ * z * g ≠ 1 := by
    intro h
    apply hz1
    have h2 : z = g * (g⁻¹ * z * g) * g⁻¹ := by group
    rw [h2, h]
    group
  have hc' : (g⁻¹ * z * g) * (g⁻¹ * u * g) = (g⁻¹ * u * g) * (g⁻¹ * z * g) := by
    have e1 : (g⁻¹ * z * g) * (g⁻¹ * u * g) = g⁻¹ * (z * u) * g := by group
    have e2 : (g⁻¹ * u * g) * (g⁻¹ * z * g) = g⁻¹ * (u * z) * g := by group
    rw [e1, e2, hcomm]
  have key := m11Sd_no_c4_c2 p q
    (by rw [hp, ← Subgroup.coe_pow, hu'4]; rfl)
    (by
      rw [hp, ← Subgroup.coe_pow]
      exact fun h => hu'2 (Subtype.ext h))
    (by rw [hq, ← Subgroup.coe_mul, hz'2]; rfl)
    (by
      rw [hq]
      exact fun h => hz'1 (Subtype.ext h))
    (by rw [hp, hq, ← Subgroup.coe_mul, ← Subgroup.coe_mul, hc'])
  rw [hp, hq, ← Subgroup.coe_pow] at key
  have key' : g⁻¹ * z * g = (g⁻¹ * u * g) ^ 2 := Subtype.ext key
  have hz : z = g * ((g⁻¹ * u * g) ^ 2) * g⁻¹ := by
    rw [← key']
    group
  have e : (g⁻¹ * u * g) ^ 2 = g⁻¹ * u ^ 2 * g := by
    simpa using conj_pow (a := g⁻¹) (b := u) (i := 2)
  rw [hz, e]
  group

end Group

section Shape

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Asc77.MuTab


theorem m11Shape3 : ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)),
    HypOmegaModU (.sl2 3 1) Ω → (∀ J ∈ Ω, AEmpty Ω J) → Ω.Nonempty →
      (∀ K ∈ Ω, ∀ J ∈ Ω, ∃ g : G, conjSub g K = J) → HasM11TypeU 3 1 Ω → ShapeZ2 Ω := by
  intro G _ _ _ Ω hΩ hA hne htrans hM
  obtain ⟨h3, D, hD1, i, hi⟩ := hM
  obtain ⟨e⟩ := exists_mulEquiv_m11 D hΩ hne i hi
  have hcard := D.card_eq h3
  have h24 : (2 : ℕ) ^ (Nat.factorization 24) 2 = 8 := by
    have h : (Nat.factorization 24) 2 = 3 := by
      rw [Nat.factorization_def _ Nat.prime_two]
      have h1 : (24 : ℕ) = 2 ^ 3 * 3 := by norm_num
      rw [h1, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow]
      have h0 : padicValNat 2 3 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
      omega
    rw [h]
    norm_num
  intro K hK
  refine Set.eq_empty_of_forall_notMem fun J hJ => ?_
  obtain ⟨hJΩ, hJK, U, hU, hUJ, hUN⟩ := hJ
  obtain ⟨R', hR', hUR', hcyc, hidx⟩ := hU
  obtain ⟨J', hJ', P, rfl⟩ := hR'
  have hR8 : Nat.card ((P : Subgroup ↥J').map J'.subtype) = 8 := by
    rw [Subgroup.card_map_of_injective J'.subtype_injective, Sylow.card_eq_multiplicity,
      hcard J' hJ', h24]
  have h1 := Subgroup.relIndex_mul_card U ((P : Subgroup ↥J').map J'.subtype)
  rw [inf_eq_left.mpr hUR', hidx, hR8] at h1
  have hUc : Nat.card U = 4 := by omega
  obtain ⟨u, hu⟩ := IsCyclic.exists_generator (α := U)
  have hordu : orderOf (u : G) = 4 := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hu, hUc]
  have hu4 : (u : G) ^ 4 = 1 := by rw [← hordu]; exact pow_orderOf_eq_one _
  have hu2 : (u : G) ^ 2 ≠ 1 := by
    intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hordu] at this
    norm_num at this
  obtain ⟨zK, hzK⟩ := hΩ.classical K hK
  obtain ⟨zJ, hzJ⟩ := hΩ.classical J hJΩ
  have iK := hzK.isUniqueInvolution_sl2
  have iJ := hzJ.isUniqueInvolution_sl2
  have huJ : (u : G) ∈ J := hUJ u.2
  have huN : (u : G) ∈ Subgroup.normalizer (K : Set G) := hUN u.2
  have hJu : (u : G) ^ 2 = zJ := by
    refine (iJ.unique _ (J.pow_mem huJ 2) ?_).resolve_left hu2
    rw [← pow_add]
    exact hu4
  have hKc : zK * (u : G) = (u : G) * zK := by
    have hmem : (u : G) * zK * (u : G)⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp huN zK).mp iK.mem
    have hsq : ((u : G) * zK * (u : G)⁻¹) * ((u : G) * zK * (u : G)⁻¹) = 1 := by
      calc ((u : G) * zK * (u : G)⁻¹) * ((u : G) * zK * (u : G)⁻¹)
          = (u : G) * (zK * zK) * (u : G)⁻¹ := by group
        _ = 1 := by rw [iK.sq]; group
    rcases iK.unique _ hmem hsq with h | h
    · exact absurd (by simpa using h) iK.ne_one
    · have h' : (u : G) * zK = zK * (u : G) := by
        calc (u : G) * zK = ((u : G) * zK * (u : G)⁻¹) * (u : G) := by group
          _ = zK * (u : G) := by rw [h]
      exact h'.symm
  have hz : e.symm zK = (e.symm (u : G)) ^ 2 :=
    m11_no_c4_c2 (u := e.symm (u : G)) (z := e.symm zK)
      (by rw [← map_pow, hu4, map_one])
      (by rw [← map_pow]; exact fun h => hu2 (e.symm.injective (by rw [h, map_one])))
      (by rw [← map_mul, iK.sq, map_one])
      (fun h => iK.ne_one (e.symm.injective (by rw [h, map_one])))
      (by rw [← map_mul, ← map_mul, hKc])
  have hzz : zK = zJ := by
    rw [← hJu]
    apply e.symm.injective
    rw [hz, map_pow]
  exact hJK (classical_eq_of_mulEquiv_m11 e (hzJ.toQ3 (by norm_num))
    (hzz ▸ hzK.toQ3 (by norm_num)))

end Shape

end CFSG.ClassicalInvolution.Q3.Q3MT
