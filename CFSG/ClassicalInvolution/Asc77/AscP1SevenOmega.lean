module

public import CFSG.ClassicalInvolution.Asc77.AscP1SevenBasic
public import CFSG.ClassicalInvolution.Asc77.AscT3Sym

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77.Thompson
open scoped commutatorElement

namespace Thompson

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

theorem le_centralizer_of_mem (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hW : W ∈ WSet Ω) {R : Subgroup G} (hR : R ∈ DSet Ω W) {r j : G} (hr : r ∈ R) (hrW : r ∉ W)
    (hjW : j ∈ W) (hrj : r * j = j * r) : R ≤ Subgroup.centralizer ({j} : Set G) := by
  have hWab := commutes_of_mem_WSet hp hq hΩ hW
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  by_cases hxW : x ∈ W
  · exact hWab x hxW j hjW
  · have hw : r⁻¹ * x ∈ W := D_inv_mul_mem hp hq hΩ hW hR hr hx hrW hxW
    calc x * j = r * ((r⁻¹ * x) * j) := by group
      _ = r * (j * (r⁻¹ * x)) := by rw [hWab _ hw j hjW]
      _ = (r * j) * (r⁻¹ * x) := by group
      _ = (j * r) * (r⁻¹ * x) := by rw [hrj]
      _ = j * x := by group

theorem conj_involution_eq_mul (h62 : L6_2 p f) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmegaMod p f Ω) (hW : W ∈ WSet Ω) {K J R T : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω)
    (hKJ : K ≠ J) (hR : R ∈ DSet Ω W) (hT : T ∈ DSet Ω W) (hRK : IsSylow2In R K)
    (hTJ : IsSylow2In T J) (hnot : J ∉ omegaNbr Ω K) {z j : G} (hz : IsUniqueInvolution K z)
    (hj : IsUniqueInvolution J j) {r : G} (hr : r ∈ R) (hrW : r ∉ W) :
    r * j * r⁻¹ = z * j := by
  have hWab := commutes_of_mem_WSet hp hq hΩ hW
  have hjW : j ∈ J ⊓ W := uniqueInvolution_mem_W hp hq hΩ hW hJ hT hTJ hj
  have hc := comm_mem_inf_W hp hq hΩ hW hK hJ hKJ hR hT hRK hTJ hr hjW
  set c := r * j * r⁻¹ * j⁻¹ with hcdef
  have hcj : c * j = r * j * r⁻¹ := by rw [hcdef]; group
  have hcc : c * c = 1 := by
    have h1 : (c * j) * (c * j) = 1 := by
      rw [hcj]
      calc r * j * r⁻¹ * (r * j * r⁻¹) = r * (j * j) * r⁻¹ := by group
        _ = 1 := by rw [hj.sq]; group
    have h2 : c * j = j * c := hWab c hc.2 j hjW.2
    calc c * c = c * c * (j * j) := by rw [hj.sq, mul_one]
      _ = c * (c * j) * j := by group
      _ = c * (j * c) * j := by rw [h2]
      _ = (c * j) * (c * j) := by group
      _ = 1 := h1
  rcases hz.unique c hc.1 hcc with h | h
  · exfalso
    have hrj : r * j = j * r := by
      have : r * j * r⁻¹ = j := by rw [← hcj, h, one_mul]
      calc r * j = (r * j * r⁻¹) * r := by group
        _ = j * r := by rw [this]
    have hRc := le_centralizer_of_mem hp hq hΩ hW hR hr hrW hjW.2 hrj
    have hRN : R ≤ Subgroup.normalizer (J : Set G) :=
      hΩ.le_normalizer_of_le_centralizer hp hq hJ hK (Ne.symm hKJ) hj hRK.1 hRK.2.1
        (by have := hΩ.eight_le_of_mem_RSet hp hR.1; omega) hRc
    have hKJ' : K ∈ omegaNbr Ω J := ⟨hK, hKJ, R, hR.1, hRK.1, hRN⟩
    exact hnot (T3.omegaNbr_symm h62 hp hq hΩ hJ hK hKJ')
  · rw [← hcj, h]

theorem conj_involution_eq_mul' (h62 : L6_2 p f) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmegaMod p f Ω) (hW : W ∈ WSet Ω) {K J R T : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω)
    (hKJ : K ≠ J) (hR : R ∈ DSet Ω W) (hT : T ∈ DSet Ω W) (hRK : IsSylow2In R K)
    (hTJ : IsSylow2In T J) (hnot : J ∉ omegaNbr Ω K) {z j : G} (hz : IsUniqueInvolution K z)
    (hj : IsUniqueInvolution J j) {t : G} (ht : t ∈ T) (htW : t ∉ W) :
    t * z * t⁻¹ = z * j := by
  have hnot' : K ∉ omegaNbr Ω J := fun h => hnot (T3.omegaNbr_symm h62 hp hq hΩ hJ hK h)
  have hWab := commutes_of_mem_WSet hp hq hΩ hW
  have hzW : z ∈ K ⊓ W := uniqueInvolution_mem_W hp hq hΩ hW hK hR hRK hz
  have hjW : j ∈ J ⊓ W := uniqueInvolution_mem_W hp hq hΩ hW hJ hT hTJ hj
  rw [hWab z hzW.2 j hjW.2]
  exact conj_involution_eq_mul h62 hp hq hΩ hW hJ hK (Ne.symm hKJ) hT hR hTJ hRK hnot' hj hz ht htW

theorem comm_le_oddCore_of_isSylow2In (h62 : L6_2 p f) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmegaMod p f Ω) {K J V : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J)
    {z j : G} (hz : IsUniqueInvolution K z) (hj : IsUniqueInvolution J j)
    (hV : IsSylow2In V J) (hVz : V ≤ Subgroup.centralizer ({z} : Set G)) :
    ⁅V, K⁆ ≤ oddCoreOf K := by
  have hVR : V ∈ RSet Ω := mem_RSet_of_isSylow2In hJ hV
  have h8 := hΩ.eight_le_of_mem_RSet hp hVR
  by_cases hzj : z = j
  · have hzJ : z ∈ J := hzj ▸ hj.mem
    have hord : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one
    have hdvd : 2 ∣ Nat.card ↥(K ⊓ J) := by
      have := Subgroup.orderOf_dvd_natCard (K ⊓ J) (⟨hz.mem, hzJ⟩ : z ∈ K ⊓ J)
      rwa [hord] at this
    have hval : padicValNat 2 (Nat.card ↥(K ⊓ J)) = 1 := by
      have h1 := (hΩ.omega4 K hK J hJ hKJ).1
      have h2 : 1 ≤ padicValNat 2 (Nat.card ↥(K ⊓ J)) :=
        one_le_padicValNat_of_dvd Nat.card_pos.ne' hdvd
      omega
    have hcomm := (hΩ.omega4 K hK J hJ hKJ).2 hval
    calc ⁅V, K⁆ ≤ ⁅J, K⁆ := Subgroup.commutator_mono hV.1 le_rfl
      _ = ⁅K, J⁆ := Subgroup.commutator_comm J K
      _ ≤ oddCoreOf K ⊓ oddCoreOf J := hcomm
      _ ≤ oddCoreOf K := inf_le_left
  · have hnt : J ∉ twinSet Ω K := by
      rintro ⟨-, z', hz'K, hz'J⟩
      exact hzj ((hz.eq hz'K).trans (hj.eq hz'J).symm)
    have hjV : j ∈ V := T3.mem_of_isPGroup hj hV.1 hV.2.1 (by omega)
    have hVs : IsSylow2In V (J ⊓ Subgroup.centralizer ({z} : Set G)) :=
      ⟨le_inf hV.1 hVz, hV.2.1, fun V' hV'P hV'2 hle =>
        hV.2.2 V' (hV'P.trans inf_le_left) hV'2 hle⟩
    rcases h62 hp hq G Ω hΩ K hK z hz J hJ hnt j hj V hVs hjV with
      ⟨hV1, -⟩ | ⟨hV1, -⟩ | ⟨hVU, -⟩ | ⟨-, hc⟩
    · exfalso
      have : Nat.card V = 2 := by
        rw [hV1, Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact hj.sq) hj.ne_one]
      omega
    · exfalso
      have : Nat.card V = 2 := by
        rw [hV1, Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact hj.sq) hj.ne_one]
      omega
    · exfalso
      obtain ⟨R', -, J', hJ', hR'J', hVR', -, hcard, -⟩ := hΩ.exists_data_of_mem_USet hp hVU
      have e1 := hΩ.natCard_isSylow2In hJ' hR'J'
      have e2 := hΩ.natCard_isSylow2In hJ hV
      have h0 : 0 < Nat.card V := Nat.card_pos
      omega
    · exact hc

theorem centralizes_inf_W_of_mem_omegaNbr (h62 : L6_2 p f) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmegaMod p f Ω) (hW : W ∈ WSet Ω) {K J R T : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω)
    (hKJ : K ≠ J) (hR : R ∈ DSet Ω W) (hT : T ∈ DSet Ω W) (hRK : IsSylow2In R K)
    (hTJ : IsSylow2In T J) (hnbr : J ∈ omegaNbr Ω K) {r v : G} (hr : r ∈ R) (hv : v ∈ J ⊓ W) :
    r * v = v * r := by
  obtain ⟨z, hz⟩ := hΩ.exists_uniqueInvolution hp hq hK
  obtain ⟨j, hj⟩ := hΩ.exists_uniqueInvolution hp hq hJ
  have hWab := commutes_of_mem_WSet hp hq hΩ hW
  have hzW : z ∈ K ⊓ W := uniqueInvolution_mem_W hp hq hΩ hW hK hR hRK hz
  obtain ⟨-, -, R₁, hR₁, hR₁J, hR₁N⟩ := hnbr
  have hR₁s : IsSylow2In R₁ J := T3.isSylow2In_of_mem_RSet_of_le hp hΩ hJ hR₁ hR₁J
  have hR₁c : R₁ ≤ Subgroup.centralizer ({z} : Set G) := T3.le_centralizer_of_le_normalizer' hz hR₁N
  have hR₁' : IsSylow2In R₁ (J ⊓ Subgroup.centralizer ({z} : Set G)) :=
    ⟨le_inf hR₁J hR₁c, hR₁s.2.1, fun V' hV'P hV'2 hle =>
      hR₁s.2.2 V' (hV'P.trans inf_le_left) hV'2 hle⟩
  have hU₂le : J ⊓ W ≤ J ⊓ Subgroup.centralizer ({z} : Set G) := fun x hx =>
    ⟨hx.1, Subgroup.mem_centralizer_singleton_iff.mpr (hWab x hx.2 z hzW.2)⟩
  obtain ⟨V₁, hV₁, hU₂V₁⟩ := IsSylow2In.exists_ge (isPGroup_of_mem_WSet hW).to_inf_right hU₂le
  have hcard : Nat.card R₁ ≤ Nat.card V₁ := (hV₁.natCard_eq hR₁').symm.le
  have hV₁J : IsSylow2In V₁ J :=
    hR₁s.of_natCard_le hV₁.2.1 (hV₁.1.trans inf_le_left) hcard
  have hcomm := comm_le_oddCore_of_isSylow2In h62 hp hq hΩ hK hJ hKJ hz hj hV₁J
    (hV₁.1.trans inf_le_right)
  have h1 : ⁅v, r⁆ ∈ oddCoreOf K :=
    hcomm (Subgroup.commutator_mem_commutator (hU₂V₁ hv) (hRK.1 hr))
  have h2 : ⁅v, r⁆ ∈ R := by
    rw [commutatorElement_def]
    exact R.mul_mem (conj_mem_of_mem_inf_W hp hq hΩ hW hK hJ hKJ hR hT hRK hTJ hr hv)
      (R.inv_mem hr)
  have h3 : ⁅v, r⁆ = 1 :=
    eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard K) h1
      (hRK.2.1.to_le (Subgroup.zpowers_le.mpr h2))
  exact (commutatorElement_eq_one_iff_mul_comm.mp h3).symm

end Thompson

end CFSG.ClassicalInvolution.Asc77
