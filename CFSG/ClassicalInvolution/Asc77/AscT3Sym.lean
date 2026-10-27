module

public import CFSG.ClassicalInvolution.Asc77.AscT3Wreath
public import CFSG.ClassicalInvolution.Asc77.WP1Section6
public import CFSG.ClassicalInvolution.Asc77.AscE189SD
public import CFSG.ClassicalInvolution.Asc77.AscT3Basic

public section

namespace CFSG.ClassicalInvolution.Asc77.T3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.AscL62
open scoped commutatorElement

variable {G : Type} [Group G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

omit [Fact p.Prime] in
theorem le_centralizer_of_le_normalizer' {K R : Subgroup G} {z : G} (hz : IsUniqueInvolution K z)
    (h : R ≤ Subgroup.normalizer (K : Set G)) : R ≤ Subgroup.centralizer ({z} : Set G) := by
  intro r hr
  rw [Subgroup.mem_centralizer_singleton_iff]
  have := hz.conj_eq (mem_normalizer_iff_conjSub_eq.mp (h hr))
  rw [mul_inv_eq_iff_eq_mul] at this
  exact this

theorem isSylow2In_of_mem_RSet_of_le [Finite G] (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω)
    {K R : Subgroup G} (hK : K ∈ Ω) (hR : R ∈ RSet Ω) (hRK : R ≤ K) : IsSylow2In R K := by
  obtain ⟨J, hJ, hRJ⟩ := exists_isSylow2In_of_mem_RSet hR
  have h8 := hΩ.eight_le_of_mem_RSet hp hR
  have hJK : J = K := hΩ.eq_of_le_of_le hJ hK hRJ.2.1 (by omega) hRJ.1 hRK
  exact hJK ▸ hRJ

theorem exists_sq_eq_of_cyclic [Finite G] {J V : Subgroup G} {j : G} (hj : IsUniqueInvolution J j)
    (hVJ : V ≤ J) (hV : IsCyclic ↥V) (hV2 : IsPGroup 2 V) (h4 : 4 ≤ Nat.card V) :
    ∃ w ∈ V, w * w = j := by
  obtain ⟨g, hg⟩ := hV.exists_generator
  have hgord : orderOf g = Nat.card V := orderOf_eq_card_of_forall_mem_zpowers hg
  obtain ⟨m, hm⟩ := hV2.exists_card_eq
  have hm2 : 2 ≤ m := by
    by_contra hlt
    have : 2 ^ m ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hn0 : 2 ^ (m - 2) ≠ 0 := by positivity
  have hdvd : 2 ^ (m - 2) ∣ orderOf g := by
    rw [hgord, hm]
    exact pow_dvd_pow 2 (by omega)
  have hord : orderOf (g ^ 2 ^ (m - 2)) = 4 := by
    rw [orderOf_pow_of_dvd hn0 hdvd, hgord, hm, Nat.pow_div (by omega : m - 2 ≤ m) (by norm_num)]
    have : m - (m - 2) = 2 := by omega
    rw [this]
  set w : G := ((g ^ 2 ^ (m - 2) : ↥V) : G) with hw
  have hwV : w ∈ V := (g ^ 2 ^ (m - 2)).2
  have hwo : orderOf w = 4 := by rw [hw, Subgroup.orderOf_coe, hord]
  have hw4 : w ^ 4 = 1 := by
    have := pow_orderOf_eq_one w
    rwa [hwo] at this
  have hsq : (w * w) * (w * w) = 1 := by
    rw [← hw4]
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  have hne : w * w ≠ 1 := by
    intro h
    have h2 : w ^ 2 = 1 := by rw [pow_two]; exact h
    have := orderOf_dvd_of_pow_eq_one h2
    rw [hwo] at this
    omega
  refine ⟨w, hwV, ?_⟩
  rcases hj.unique (w * w) (J.mul_mem (hVJ hwV) (hVJ hwV)) hsq with h | h
  · exact absurd h hne
  · exact h

theorem le_normalizer_of_commutator_le' {M L : Subgroup G} (h : ⁅M, L⁆ ≤ L) :
    M ≤ Subgroup.normalizer (L : Set G) := by
  have key : ∀ m ∈ M, ∀ l ∈ L, m * l * m⁻¹ ∈ L := by
    intro m hm l hl
    have h1 : ⁅m, l⁆ ∈ L := h (Subgroup.commutator_mem_commutator hm hl)
    have e : m * l * m⁻¹ = ⁅m, l⁆ * l := by rw [commutatorElement_def]; group
    rw [e]
    exact L.mul_mem h1 hl
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  intro l
  refine ⟨fun hl => key m hm l hl, fun hl => ?_⟩
  have := key m⁻¹ (M.inv_mem hm) _ hl
  have e : m⁻¹ * (m * l * m⁻¹) * m⁻¹⁻¹ = l := by group
  rwa [e] at this

theorem omegaNbr_symm [Finite G] (h62 : L6_2 p f) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmegaMod p f Ω) {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω)
    (h : J ∈ omegaNbr Ω K) : K ∈ omegaNbr Ω J := by
  obtain ⟨-, hJK, R, hR, hRJ, hRN⟩ := h
  have hRs : IsSylow2In R J := isSylow2In_of_mem_RSet_of_le hp hΩ hJ hR hRJ
  obtain ⟨zK, hzK⟩ := hΩ.exists_uniqueInvolution hp hq hK
  obtain ⟨zJ, hzJ⟩ := hΩ.exists_uniqueInvolution hp hq hJ
  have h8 := hΩ.eight_le_of_mem_RSet hp hR
  have hzJR : zJ ∈ R := mem_of_isPGroup hzJ hRJ hRs.2.1 (by omega)
  have hRc : R ≤ Subgroup.centralizer ({zK} : Set G) := le_centralizer_of_le_normalizer' hzK hRN
  by_cases hz : zK = zJ
  · exact twin_mem_omegaNbr hΩ hJ hK (Ne.symm hJK) hzJ (hz ▸ hzK)
  · have hnt : J ∉ twinSet Ω K := by
      rintro ⟨-, z', hz'K, hz'J⟩
      exact hz ((hzK.eq hz'K).trans (hzJ.eq hz'J).symm)
    have hV : IsSylow2In R (J ⊓ Subgroup.centralizer ({zK} : Set G)) :=
      ⟨le_inf hRJ hRc, hRs.2.1, fun V' hV'P hV'2 hle =>
        hRs.2.2 V' (hV'P.trans inf_le_left) hV'2 hle⟩
    have hcomm : ⁅R, K⁆ ≤ oddCoreOf K := by
      rcases h62 hp hq G Ω hΩ K hK zK hzK J hJ hnt zJ hzJ R hV hzJR with
        ⟨hR1, -⟩ | ⟨hR1, -⟩ | ⟨hRU, -⟩ | ⟨-, hc⟩
      · exfalso
        have : Nat.card R = 2 := by
          rw [hR1, Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact hzJ.sq) hzJ.ne_one]
        omega
      · exfalso
        have : Nat.card R = 2 := by
          rw [hR1, Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact hzJ.sq) hzJ.ne_one]
        omega
      · exfalso
        obtain ⟨R', -, J', hJ', hR'J', hRR', -, hcard, -⟩ := hΩ.exists_data_of_mem_USet hp hRU
        have e1 := hΩ.natCard_isSylow2In hJ' hR'J'
        have e2 := hΩ.natCard_isSylow2In hJ hRs
        have h0 : 0 < Nat.card R := Nat.card_pos
        omega
      · exact hc
    obtain ⟨RK, hRK, hRKinv⟩ := exists_sylow_normalized hRs.2.1 hRN
    have hRK2 : IsPGroup 2 RK := hRK.2.1
    have hcRK : ∀ r ∈ R, ∀ x ∈ RK, r * x = x * r := by
      intro r hr x hx
      have h1 : ⁅r, x⁆ ∈ oddCoreOf K := hcomm (Subgroup.commutator_mem_commutator hr (hRK.1 hx))
      have h2 : ⁅r, x⁆ ∈ RK := by
        have : r * x * r⁻¹ ∈ conjSub r RK := conj_mem_conjSub hx
        rw [hRKinv r hr] at this
        rw [commutatorElement_def]
        exact RK.mul_mem this (RK.inv_mem hx)
      have h3 : ⁅r, x⁆ = 1 :=
        eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard K) h1
          (hRK2.to_le (Subgroup.zpowers_le.mpr h2))
      exact commutatorElement_eq_one_iff_mul_comm.mp h3
    have hRKc : RK ≤ Subgroup.centralizer ({zJ} : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hcRK zJ hzJR x hx).symm
    have hRKR : RK ∈ RSet Ω := mem_RSet_of_isSylow2In hK hRK
    have h8K := hΩ.eight_le_of_mem_RSet hp hRKR
    have hRKN : RK ≤ Subgroup.normalizer (J : Set G) :=
      hΩ.le_normalizer_of_le_centralizer hp hq hJ hK hJK hzJ hRK.1 hRK2 (by omega) hRKc
    exact ⟨hK, Ne.symm hJK, RK, hRKR, hRK.1, hRKN⟩

theorem exists_wreathed_of_omegaStar [Finite G] (h62 : L6_2 p f) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmegaMod p f Ω) {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) {z j : G}
    (hz : IsUniqueInvolution K z) (hj : IsUniqueInvolution J j) (hstar : J ∈ omegaStarNbr Ω K)
    (hnot : J ∉ omegaNbr Ω K) :
    ∃ V R : Subgroup G, V ≤ J ∧ j ∈ V ∧ V ∈ USet Ω ∧ V ≤ Subgroup.normalizer (K : Set G) ∧
      R ∈ RSet Ω ∧ R ≤ K ∧ V ≤ Subgroup.normalizer (R : Set G) ∧ IsWreathed (R ⊔ V) ∧ j ≠ z := by
  have hne : J ≠ K := hstar.2.1
  obtain ⟨-, -, U₀, hU₀, hU₀J, hU₀N⟩ := hstar
  obtain ⟨-, -, -, -, -, -, -, -, h4⟩ := hΩ.exists_data_of_mem_USet hp hU₀
  have hU₀2 : IsPGroup 2 U₀ := hΩ.isPGroup_of_mem_USet hp hU₀
  have hjU₀ : j ∈ U₀ := mem_of_isPGroup hj hU₀J hU₀2 (by omega)
  have hU₀c : U₀ ≤ Subgroup.centralizer ({z} : Set G) := le_centralizer_of_le_normalizer' hz hU₀N
  have hnt : J ∉ twinSet Ω K := fun ht =>
    hnot (by
      obtain ⟨-, z', hz'K, hz'J⟩ := ht
      exact twin_mem_omegaNbr hΩ hK hJ hne hz'K hz'J)
  have hjz : j ≠ z := by
    intro he
    exact hnt ⟨hJ, z, hz, he ▸ hj⟩
  obtain ⟨V, hV, hU₀V⟩ := IsSylow2In.exists_ge hU₀2 (le_inf hU₀J hU₀c)
  have hjV : j ∈ V := hU₀V hjU₀
  have hVJ : V ≤ J := hV.1.trans inf_le_left
  rcases h62 hp hq G Ω hΩ K hK z hz J hJ hnt j hj V hV hjV with
    ⟨-, hne1⟩ | ⟨hV1, -⟩ | ⟨hVU, hVN, R, hR, hRK, hVR, hwr⟩ | ⟨hVR, hcomm⟩
  · exact absurd (mem_normalizer_iff_conjSub_eq.mp (hU₀N hjU₀)) hne1
  · exfalso
    have h1 : Nat.card V = 2 := by
      rw [hV1, Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact hj.sq) hj.ne_one]
    have h2 := Subgroup.card_le_of_le hU₀V
    omega
  · exact ⟨V, R, hVJ, hjV, hVU, hVN, hR, hRK, hVR, hwr, hjz⟩
  · exfalso
    have hVN : V ≤ Subgroup.normalizer (K : Set G) :=
      le_normalizer_of_commutator_le' (hcomm.trans (oddCoreOf_le_self K))
    exact hnot ⟨hJ, hne, V, hVR, hVJ, hVN⟩

theorem exists_mem_conj_eq_mul [Finite G] (h62 : L6_2 p f) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmegaMod p f Ω) {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) {z j : G}
    (hz : IsUniqueInvolution K z) (hj : IsUniqueInvolution J j) (hstar : J ∈ omegaStarNbr Ω K)
    (hnot : J ∉ omegaNbr Ω K) : ∃ r ∈ K, r * z * r⁻¹ = z ∧ r * j * r⁻¹ = z * j := by
  obtain ⟨V, R, hVJ, hjV, hVU, hVN, hR, hRK, hVR, hwr, hjz⟩ :=
    exists_wreathed_of_omegaStar h62 hp hq hΩ hK hJ hz hj hstar hnot
  have hR2 : IsPGroup 2 R := by
    obtain ⟨J', -, hRJ'⟩ := exists_isSylow2In_of_mem_RSet hR
    exact hRJ'.2.1
  have hV2 : IsPGroup 2 V := hΩ.isPGroup_of_mem_USet hp hVU
  have hP2 : IsPGroup 2 ↥(R ⊔ V) := by
    have := hV2.to_sup_of_normal_right' hR2 hVR
    rwa [sup_comm] at this
  have h8 := hΩ.eight_le_of_mem_RSet hp hR
  have hzR : z ∈ R := mem_of_isPGroup hz hRK hR2 (by omega)
  have hzc : ∀ x ∈ R ⊔ V, z * x = x * z := by
    have hle : R ⊔ V ≤ Subgroup.centralizer ({z} : Set G) :=
      sup_le (fun r hr => by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hz.commute_of_mem (hRK hr)).symm)
        (le_centralizer_of_le_normalizer' hz hVN)
    intro x hx
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hx)).symm
  obtain ⟨g, hgP, hg⟩ := exists_conj_of_isWreathed hwr hP2 (Subgroup.mem_sup_left hzR) hz.sq
    hz.ne_one hzc (Subgroup.mem_sup_right hjV) hj.sq hj.ne_one hjz
  obtain ⟨r, hrR, v, hvV, rfl⟩ := exists_mul_of_mem_sup hVR hgP
  have hVc : IsCyclic ↥V := by
    obtain ⟨-, -, -, -, -, -, hc, -, -⟩ := hΩ.exists_data_of_mem_USet hp hVU
    exact hc
  have hvj : v * j = j * v := cyclic_comm hVc hvV hjV
  refine ⟨r, hRK hrR, ?_, ?_⟩
  · have := hz.commute_of_mem (hRK hrR)
    rw [mul_inv_eq_iff_eq_mul]
    exact this.symm
  · rw [← hg]
    calc r * j * r⁻¹ = r * (v * j * v⁻¹) * r⁻¹ := by rw [hvj]; group
      _ = r * v * j * (r * v)⁻¹ := by group

theorem omegaStarNbr_symm [Finite G] (h62 : L6_2 p f) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmegaMod p f Ω) {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω)
    (h : J ∈ omegaStarNbr Ω K) : K ∈ omegaStarNbr Ω J := by
  by_cases hnbr : J ∈ omegaNbr Ω K
  · exact omegaNbr_subset_omegaStarNbr hp hΩ J (omegaNbr_symm h62 hp hq hΩ hK hJ hnbr)
  · obtain ⟨zK, hzK⟩ := hΩ.exists_uniqueInvolution hp hq hK
    obtain ⟨zJ, hzJ⟩ := hΩ.exists_uniqueInvolution hp hq hJ
    obtain ⟨V, R, hVJ, hjV, hVU, hVN, hR, hRK, hVR, hwr, hjz⟩ :=
      exists_wreathed_of_omegaStar h62 hp hq hΩ hK hJ hzK hzJ h hnbr
    have hRs : IsSylow2In R K := isSylow2In_of_mem_RSet_of_le hp hΩ hK hR hRK
    have h8 := hΩ.eight_le_of_mem_RSet hp hR
    have hzR : zK ∈ R := mem_of_isPGroup hzK hRK hRs.2.1 (by omega)
    have hzR' : IsUniqueInvolution R zK :=
      ⟨hzR, hzK.ne_one, hzK.sq, fun y hy hy2 => hzK.unique y (hRK hy) hy2⟩
    have hquat : IsQuatSub R := hΩ.isQuatSub_of_mem_RSet hp hR
    obtain ⟨-, -, -, -, -, -, hVc, -, h4V⟩ := hΩ.exists_data_of_mem_USet hp hVU
    obtain ⟨w, hwV, hww⟩ := exists_sq_eq_of_cyclic hzJ hVJ hVc (hΩ.isPGroup_of_mem_USet hp hVU)
      h4V
    obtain ⟨U, hUR, hUc, hrel, hUz⟩ := exists_cyclic_index_two_le_centralizer hquat hzR' hwr
      (Subgroup.mem_sup_right hwV) hww
    have hcard : Nat.card U * U.relIndex R = Nat.card R := by
      have := Subgroup.relIndex_mul_card U R
      rwa [inf_eq_left.mpr hUR, mul_comm] at this
    rw [hrel] at hcard
    have hU2 : IsPGroup 2 U := hRs.2.1.to_le hUR
    have hUN : U ≤ Subgroup.normalizer (J : Set G) :=
      hΩ.le_normalizer_of_le_centralizer hp hq hJ hK h.2.1 hzJ (hUR.trans hRs.1) hU2 (by omega) hUz
    exact ⟨hK, Ne.symm h.2.1, U, ⟨R, hR, hUR, hUc, hrel⟩, hUR.trans hRs.1, hUN⟩

end CFSG.ClassicalInvolution.Asc77.T3
