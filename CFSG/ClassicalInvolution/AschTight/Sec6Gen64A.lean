module

public import CFSG.ClassicalInvolution.Asc77.AscSixModCent
public import CFSG.ClassicalInvolution.AschTight.Sec6GenAPI2
public import CFSG.ClassicalInvolution.AschTight.Sec6GenL62

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

omit [Finite G] in
theorem le_centralizer_of_le_normalizer' {K A : Subgroup G} {z : G} (hz : IsUniqueInvolution K z)
    (h : A ≤ Subgroup.normalizer (K : Set G)) : A ≤ Subgroup.centralizer ({z} : Set G) := by
  intro a ha
  rw [Subgroup.mem_centralizer_singleton_iff]
  have := hz.conj_eq (mem_normalizer_iff_conjSub_eq.mp (h ha))
  calc a * z = (a * z * a⁻¹) * a := by group
    _ = z * a := by rw [this]

omit [Finite G] in
theorem not_mem_twinSet {K J : Subgroup G} {z t : G} (hz : IsUniqueInvolution K z)
    (ht : IsUniqueInvolution J t) (hzt : z ≠ t) : J ∉ twinSet Ω K := by
  rintro ⟨-, z', hz', ht'⟩
  exact hzt ((hz.eq hz').trans (ht'.eq ht))

theorem sylow_cent_mem_USet (hΩ : HypOmegaGen Ω) {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω)
    {z t : G} (hz : IsUniqueInvolution K z) (ht : IsUniqueInvolution J t) (hzt : z ≠ t)
    (hnot : J ∉ omegaNbr Ω K) {V' : Subgroup G}
    (hV' : IsSylow2In V' (J ⊓ Subgroup.centralizer ({z} : Set G))) (htV : t ∈ V')
    (h3 : 3 ≤ Nat.card V') : V' ∈ USet Ω := by
  have hJK : J ≠ K := by
    rintro rfl
    exact hzt (hz.eq ht)
  have h2 : Nat.card (Subgroup.zpowers t) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact ht.sq) ht.ne_one
  rcases l6_2Gen G Ω hΩ K hK z hz J hJ (not_mem_twinSet hz ht hzt) t ht V' hV' htV with
    ⟨hVeq, -⟩ | ⟨hVeq, -⟩ | ⟨hVU, -⟩ | ⟨hVR, hcomm⟩
  · rw [hVeq] at h3
    omega
  · rw [hVeq] at h3
    omega
  · exact hVU
  · exfalso
    exact hnot ⟨hJ, hJK, V', hVR, hV'.1.trans inf_le_left,
      le_normalizer_of_commutator_le_oddCoreOf hcomm⟩

theorem isSylow2In_of_mem_RSet_of_le (hΩ : HypOmegaGen Ω) {K R : Subgroup G} (hK : K ∈ Ω)
    (hR : R ∈ RSet Ω) (hRK : R ≤ K) : IsSylow2In R K := by
  obtain ⟨K₀, hK₀, hRK₀⟩ := exists_isSylow2In_of_mem_RSet hR
  have h8 := eight_le_of_mem_RSet hΩ hR
  have e : K₀ = K := eq_of_le_of_le hΩ hK₀ hK hRK₀.2.1 (by omega) hRK₀.1 hRK
  exact e ▸ hRK₀

theorem not_mem_omegaNbr_symm (hΩ : HypOmegaGen Ω) {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω)
    {z t : G} (hz : IsUniqueInvolution K z) (ht : IsUniqueInvolution J t) (hzt : z ≠ t)
    (hnot : J ∉ omegaNbr Ω K) : K ∉ omegaNbr Ω J := by
  rintro ⟨-, hKJ, R', hR', hR'K, hR'N⟩
  have hR'syl : IsSylow2In R' K := isSylow2In_of_mem_RSet_of_le hΩ hK hR' hR'K
  have hR'c : R' ≤ Subgroup.centralizer ({t} : Set G) := le_centralizer_of_le_normalizer' ht hR'N
  obtain ⟨V', hV', hR'V'⟩ := IsSylow2In.exists_ge hR'syl.2.1 (le_inf hR'K hR'c)
  have hV'eq : V' = R' := hR'syl.eq_of_le hV'.2.1 (hV'.1.trans inf_le_left) hR'V'
  subst hV'eq
  have h8 := eight_le_of_mem_RSet hΩ hR'
  have hzR' : z ∈ V' := mem_of_isSylow2In hz hR'syl
  have h2 : Nat.card (Subgroup.zpowers z) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one
  rcases l6_2Gen G Ω hΩ J hJ t ht K hK (not_mem_twinSet ht hz hzt.symm) z hz V' hV' hzR' with
    ⟨hVeq, -⟩ | ⟨hVeq, -⟩ | ⟨hVU, -⟩ | ⟨-, hcomm⟩
  · rw [hVeq] at h8
    omega
  · rw [hVeq] at h8
    omega
  · obtain ⟨R₀, -, K₀, hK₀, hR₀K₀, hVR₀, -, hcard, -⟩ := exists_data_of_mem_USet hΩ hVU
    have e : K₀ = K := eq_of_mem_USet hΩ hVU hK₀ hK (hVR₀.trans hR₀K₀.1) hR'K
    subst e
    have := hR₀K₀.natCard_eq hR'syl
    omega
  ·
    have hVN : V' ≤ Subgroup.normalizer (J : Set G) :=
      le_normalizer_of_commutator_le_oddCoreOf hcomm
    obtain ⟨T', hT', hT'inv⟩ := AscL62.exists_sylow_normalized hR'syl.2.1 hVN
    have hcomm' : ∀ x ∈ T', ∀ y ∈ V', x * y = y * x := by
      intro x hx y hy
      have h1 : ⁅y, x⁆ ∈ oddCoreOf J := hcomm (Subgroup.commutator_mem_commutator hy (hT'.1 hx))
      have h2 : ⁅y, x⁆ ∈ T' := by
        rw [commutatorElement_def]
        have h3 : y * x * y⁻¹ ∈ T' := by
          have := conj_mem_conjSub (n := y) hx
          rwa [hT'inv y hy] at this
        exact T'.mul_mem h3 (T'.inv_mem hx)
      have h3 : IsPGroup 2 (Subgroup.zpowers ⁅y, x⁆) := hT'.2.1.to_le (Subgroup.zpowers_le.mpr h2)
      have h4 := eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard J) h1 h3
      exact (commutatorElement_eq_one_iff_mul_comm.mp h4).symm
    have hT'c : T' ≤ Subgroup.centralizer ({z} : Set G) := fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hcomm' x hx z hzR')
    have hT'8 := eight_le_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hJ hT')
    have hJK : J ≠ K := fun h => hKJ h.symm
    exact hnot ⟨hJ, hJK, T', mem_RSet_of_isSylow2In hJ hT', hT'.1,
      le_normalizer_of_le_centralizer hΩ hK hJ hKJ hz hT'.1 hT'.2.1 (by omega) hT'c⟩

structure Cfg64 (Ω : Set (Subgroup G)) (K J : Subgroup G) (z j u v : G) (R T : Subgroup G) :
    Prop where
  hΩ : HypOmegaGen Ω
  hK : K ∈ Ω
  hJ : J ∈ Ω
  hKJ : K ≠ J
  hz : IsUniqueInvolution K z
  hj : IsUniqueInvolution J j
  notJ : J ∉ omegaNbr Ω K
  notK : K ∉ omegaNbr Ω J
  hU : Subgroup.zpowers u ∈ USet Ω
  hUK : Subgroup.zpowers u ≤ K
  hV : Subgroup.zpowers v ∈ USet Ω
  hVJ : Subgroup.zpowers v ≤ J
  hUV : Commutes (Subgroup.zpowers u) (Subgroup.zpowers v)
  hR : IsSylow2In R K
  hT : IsSylow2In T J
  huR : Subgroup.zpowers u ≤ R
  hvT : Subgroup.zpowers v ≤ T
  hRN : R ≤ Subgroup.normalizer ((Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup G) : Set G)
  hTN : T ≤ Subgroup.normalizer ((Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup G) : Set G)

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen
