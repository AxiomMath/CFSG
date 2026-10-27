module

public import CFSG.ClassicalInvolution.Q3.Q3CLBasic
public import CFSG.ClassicalInvolution.AschTight.Sec6Gen610
public import CFSG.ClassicalInvolution.AschTight.Sec6Gen64C

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3CL

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {W : Subgroup G}

namespace Thompson

open CFSG.ClassicalInvolution.Asc77.Thompson

theorem uniqueInvolution_mem_W (hΩ : HypOmegaGen Ω)
    (hW : W ∈ WSet Ω) {K R : Subgroup G} (hK : K ∈ Ω) (hR : R ∈ DSet Ω W) (hRK : IsSylow2In R K)
    {z : G} (hz : IsUniqueInvolution K z) : z ∈ K ⊓ W := by
  have hinfo := inf_W_of_mem_D hΩ hW hR hK hRK
  have hKW : K ⊓ W ≤ K := inf_le_left
  have hA2 : IsPGroup 2 ↥(K ⊓ W) := (isPGroup_of_mem_WSet hW).to_inf_right
  have hcard : 2 ≤ Nat.card ↥(K ⊓ W) := by
    have := hinfo.2.2.2.1
    rw [← hinfo.1]
    omega
  exact T3.mem_of_isPGroup hz hKW hA2 hcard

theorem inf_W_le_normalizer_left (hΩ : HypOmegaGen Ω)
    (hW : W ∈ WSet Ω) {K J R T : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J)
    (hR : R ∈ DSet Ω W) (hT : T ∈ DSet Ω W) (hRK : IsSylow2In R K) (hTJ : IsSylow2In T J) :
    K ⊓ W ≤ Subgroup.normalizer (J : Set G) := by
  obtain ⟨zJ, hzJ⟩ := Sec6Gen.exists_uniqueInvolution hΩ hJ
  have hzW : zJ ∈ J ⊓ W := uniqueInvolution_mem_W hΩ hW hJ hT hTJ hzJ
  have hWab := commutes_of_mem_WSet hΩ hW
  have hinfo := inf_W_of_mem_D hΩ hW hR hK hRK
  refine Sec6Gen.le_normalizer_of_le_centralizer hΩ hJ hK (Ne.symm hKJ) hzJ inf_le_left
    (isPGroup_of_mem_WSet hW).to_inf_right ?_ ?_
  · have := hinfo.2.2.2.1
    rw [← hinfo.1]
    omega
  · intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hWab x hx.2 zJ hzW.2

theorem inf_W_le_normalizer_of_ne (hΩ : HypOmegaGen Ω)
    (hW : W ∈ WSet Ω) {K J R T : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J)
    (hR : R ∈ DSet Ω W) (hT : T ∈ DSet Ω W) (hRK : IsSylow2In R K) (hTJ : IsSylow2In T J) :
    K ⊓ W ≤ Subgroup.normalizer (J : Set G) ∧ J ⊓ W ≤ Subgroup.normalizer (K : Set G) :=
  ⟨inf_W_le_normalizer_left hΩ hW hK hJ hKJ hR hT hRK hTJ,
    inf_W_le_normalizer_left hΩ hW hJ hK (Ne.symm hKJ) hT hR hTJ hRK⟩

theorem mem_omegaStarNbr_of_inf_W (hΩ : HypOmegaGen Ω)
    (hW : W ∈ WSet Ω) {K J R T : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J)
    (hR : R ∈ DSet Ω W) (hT : T ∈ DSet Ω W) (hRK : IsSylow2In R K) (hTJ : IsSylow2In T J) :
    J ∈ omegaStarNbr Ω K ∧ K ∈ omegaStarNbr Ω J := by
  have hN := inf_W_le_normalizer_of_ne hΩ hW hK hJ hKJ hR hT hRK hTJ
  have hKU := (inf_W_of_mem_D hΩ hW hR hK hRK).2.1
  have hJU := (inf_W_of_mem_D hΩ hW hT hJ hTJ).2.1
  exact ⟨⟨hJ, Ne.symm hKJ, J ⊓ W, hJU, inf_le_left, hN.2⟩,
    ⟨hK, hKJ, K ⊓ W, hKU, inf_le_left, hN.1⟩⟩

theorem comm_mem_inf_W (hΩ : HypOmegaGen Ω)
    (hW : W ∈ WSet Ω) {K J R T : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J)
    (hR : R ∈ DSet Ω W) (hT : T ∈ DSet Ω W) (hRK : IsSylow2In R K) (hTJ : IsSylow2In T J)
    {r v : G} (hr : r ∈ R) (hv : v ∈ J ⊓ W) : r * v * r⁻¹ * v⁻¹ ∈ K ⊓ W := by
  have hN := (inf_W_le_normalizer_of_ne hΩ hW hK hJ hKJ hR hT hRK hTJ).2 hv
  have hrK : r ∈ K := hRK.1 hr
  refine ⟨?_, ?_⟩
  · have h1 : v * r⁻¹ * v⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hN r⁻¹).mp (K.inv_mem hrK)
    have : r * v * r⁻¹ * v⁻¹ = r * (v * r⁻¹ * v⁻¹) := by group
    rw [this]
    exact K.mul_mem hrK h1
  · have h1 := comm_mem_of_mem hv.2 (hR.2 hr)
    have e : r * v * r⁻¹ * v⁻¹ = (v * r * v⁻¹ * r⁻¹)⁻¹ := by group
    rw [e]
    exact W.inv_mem h1

theorem conj_mem_of_mem_inf_W (hΩ : HypOmegaGen Ω)
    (hW : W ∈ WSet Ω) {K J R T : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J)
    (hR : R ∈ DSet Ω W) (hT : T ∈ DSet Ω W) (hRK : IsSylow2In R K) (hTJ : IsSylow2In T J)
    {r v : G} (hr : r ∈ R) (hv : v ∈ J ⊓ W) : v * r * v⁻¹ ∈ R := by
  have hc := comm_mem_inf_W hΩ hW hK hJ hKJ hR hT hRK hTJ hr hv
  have hinfo := inf_W_of_mem_D hΩ hW hR hK hRK
  have hcR : r * v * r⁻¹ * v⁻¹ ∈ R := (hinfo.1 ▸ hc : r * v * r⁻¹ * v⁻¹ ∈ R ⊓ W).1
  have e : v * r * v⁻¹ = (r * v * r⁻¹ * v⁻¹)⁻¹ * r := by group
  rw [e]
  exact R.mul_mem (R.inv_mem hcR) hr

theorem le_centralizer_of_mem (hΩ : HypOmegaGen Ω)
    (hW : W ∈ WSet Ω) {R : Subgroup G} (hR : R ∈ DSet Ω W) {r j : G} (hr : r ∈ R) (hrW : r ∉ W)
    (hjW : j ∈ W) (hrj : r * j = j * r) : R ≤ Subgroup.centralizer ({j} : Set G) := by
  have hWab := commutes_of_mem_WSet hΩ hW
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  by_cases hxW : x ∈ W
  · exact hWab x hxW j hjW
  · have hw : r⁻¹ * x ∈ W := D_inv_mul_mem hΩ hW hR hr hx hrW hxW
    calc x * j = r * ((r⁻¹ * x) * j) := by group
      _ = r * (j * (r⁻¹ * x)) := by rw [hWab _ hw j hjW]
      _ = (r * j) * (r⁻¹ * x) := by group
      _ = (j * r) * (r⁻¹ * x) := by rw [hrj]
      _ = j * x := by group

theorem conj_involution_eq_mul (h62 : Sec6Gen.L6_2Gen) (hΩ : HypOmegaGen Ω) (hW : W ∈ WSet Ω)
    {K J R T : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω)
    (hKJ : K ≠ J) (hR : R ∈ DSet Ω W) (hT : T ∈ DSet Ω W) (hRK : IsSylow2In R K)
    (hTJ : IsSylow2In T J) (hnot : J ∉ omegaNbr Ω K) {z j : G} (hz : IsUniqueInvolution K z)
    (hj : IsUniqueInvolution J j) {r : G} (hr : r ∈ R) (hrW : r ∉ W) :
    r * j * r⁻¹ = z * j := by
  have hWab := commutes_of_mem_WSet hΩ hW
  have hjW : j ∈ J ⊓ W := uniqueInvolution_mem_W hΩ hW hJ hT hTJ hj
  have hc := comm_mem_inf_W hΩ hW hK hJ hKJ hR hT hRK hTJ hr hjW
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
    have hRc := le_centralizer_of_mem hΩ hW hR hr hrW hjW.2 hrj
    have hRN : R ≤ Subgroup.normalizer (J : Set G) :=
      Sec6Gen.le_normalizer_of_le_centralizer hΩ hJ hK (Ne.symm hKJ) hj hRK.1 hRK.2.1
        (by have := Sec6Gen.eight_le_of_mem_RSet hΩ hR.1; omega) hRc
    have hKJ' : K ∈ omegaNbr Ω J := ⟨hK, hKJ, R, hR.1, hRK.1, hRN⟩
    exact hnot (T3.omegaNbr_symm h62 hΩ hJ hK hKJ')
  · rw [← hcj, h]

theorem conj_involution_eq_mul' (h62 : Sec6Gen.L6_2Gen) (hΩ : HypOmegaGen Ω) (hW : W ∈ WSet Ω)
    {K J R T : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω)
    (hKJ : K ≠ J) (hR : R ∈ DSet Ω W) (hT : T ∈ DSet Ω W) (hRK : IsSylow2In R K)
    (hTJ : IsSylow2In T J) (hnot : J ∉ omegaNbr Ω K) {z j : G} (hz : IsUniqueInvolution K z)
    (hj : IsUniqueInvolution J j) {t : G} (ht : t ∈ T) (htW : t ∉ W) :
    t * z * t⁻¹ = z * j := by
  have hnot' : K ∉ omegaNbr Ω J := fun h => hnot (T3.omegaNbr_symm h62 hΩ hJ hK h)
  have hWab := commutes_of_mem_WSet hΩ hW
  have hzW : z ∈ K ⊓ W := uniqueInvolution_mem_W hΩ hW hK hR hRK hz
  have hjW : j ∈ J ⊓ W := uniqueInvolution_mem_W hΩ hW hJ hT hTJ hj
  rw [hWab z hzW.2 j hjW.2]
  exact conj_involution_eq_mul h62 hΩ hW hJ hK (Ne.symm hKJ) hT hR hTJ hRK hnot' hj hz ht htW

theorem comm_le_oddCore_of_isSylow2In (h62 : Sec6Gen.L6_2Gen) (hΩ : HypOmegaGen Ω)
    {K J V : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J)
    {z j : G} (hz : IsUniqueInvolution K z) (hj : IsUniqueInvolution J j)
    (hV : IsSylow2In V J) (hVz : V ≤ Subgroup.centralizer ({z} : Set G)) :
    ⁅V, K⁆ ≤ oddCoreOf K := by
  have hVR : V ∈ RSet Ω := mem_RSet_of_isSylow2In hJ hV
  have h8 := Sec6Gen.eight_le_of_mem_RSet hΩ hVR
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
    rcases h62 G Ω hΩ K hK z hz J hJ hnt j hj V hVs hjV with
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
      obtain ⟨R', -, J', hJ', hR'J', hVR', -, hcard, -⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hVU
      have e1 := Sec6Gen.natCard_isSylow2In_eq hΩ hJ' hJ hR'J' hV
      have h0 : 0 < Nat.card V := Nat.card_pos
      omega
    · exact hc

theorem centralizes_inf_W_of_mem_omegaNbr (h62 : Sec6Gen.L6_2Gen) (hΩ : HypOmegaGen Ω)
    (hW : W ∈ WSet Ω) {K J R T : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω)
    (hKJ : K ≠ J) (hR : R ∈ DSet Ω W) (hT : T ∈ DSet Ω W) (hRK : IsSylow2In R K)
    (hTJ : IsSylow2In T J) (hnbr : J ∈ omegaNbr Ω K) {r v : G} (hr : r ∈ R) (hv : v ∈ J ⊓ W) :
    r * v = v * r := by
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution hΩ hK
  obtain ⟨j, hj⟩ := Sec6Gen.exists_uniqueInvolution hΩ hJ
  have hWab := commutes_of_mem_WSet hΩ hW
  have hzW : z ∈ K ⊓ W := uniqueInvolution_mem_W hΩ hW hK hR hRK hz
  obtain ⟨-, -, R₁, hR₁, hR₁J, hR₁N⟩ := hnbr
  have hR₁s : IsSylow2In R₁ J := T3.isSylow2In_of_mem_RSet_of_le hΩ hJ hR₁ hR₁J
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
  have hcomm := comm_le_oddCore_of_isSylow2In h62 hΩ hK hJ hKJ hz hj hV₁J
    (hV₁.1.trans inf_le_right)
  have h1 : ⁅v, r⁆ ∈ oddCoreOf K :=
    hcomm (Subgroup.commutator_mem_commutator (hU₂V₁ hv) (hRK.1 hr))
  have h2 : ⁅v, r⁆ ∈ R := by
    rw [commutatorElement_def]
    exact R.mul_mem (conj_mem_of_mem_inf_W hΩ hW hK hJ hKJ hR hT hRK hTJ hr hv)
      (R.inv_mem hr)
  have h3 : ⁅v, r⁆ = 1 :=
    eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard K) h1
      (hRK.2.1.to_le (Subgroup.zpowers_le.mpr h2))
  exact (commutatorElement_eq_one_iff_mul_comm.mp h3).symm

theorem inf_centralizer_le_normalizer' (hΩ : HypOmegaGen Ω)
    {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J) {j : G}
    (hj : IsUniqueInvolution J j) {U V : Subgroup G}
    (hU : IsSylow2In U (K ⊓ Subgroup.centralizer ({j} : Set G))) (hUc : IsCyclic ↥U)
    (hU4 : 4 ≤ Nat.card U) (hVJ : V ≤ J) (hV2 : IsPGroup 2 ↥V) (hV4 : 4 ≤ Nat.card V)
    (hVK : V ≤ Subgroup.normalizer (K : Set G)) (hVj : V ≤ Subgroup.centralizer ({j} : Set G)) :
    K ⊓ Subgroup.centralizer ({j} : Set G) ≤ Subgroup.normalizer (J : Set G) :=
  CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen.inf_centralizer_le_normalizer hΩ hK hJ
    hKJ hj hU hUc hU4 hVJ hV2 hV4 hVK hVj

theorem isSylow2In_inf_W_centralizer (h62 : Sec6Gen.L6_2Gen) (hΩ : HypOmegaGen Ω) (hW : W ∈ WSet Ω)
    {K J R T : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω)
    (hKJ : K ≠ J) (hR : R ∈ DSet Ω W) (hT : T ∈ DSet Ω W) (hRK : IsSylow2In R K)
    (hTJ : IsSylow2In T J) (hnot : J ∉ omegaNbr Ω K) {j : G} (hj : IsUniqueInvolution J j) :
    IsSylow2In (K ⊓ W) (K ⊓ Subgroup.centralizer ({j} : Set G)) := by
  have hWab := commutes_of_mem_WSet hΩ hW
  have hjW : j ∈ J ⊓ W := uniqueInvolution_mem_W hΩ hW hJ hT hTJ hj
  obtain ⟨hRWeq, -, -, -, hcard⟩ := inf_W_of_mem_D hΩ hW hR hK hRK
  have hKW2 : IsPGroup 2 ↥(K ⊓ W) := (isPGroup_of_mem_WSet hW).to_inf_right
  have hle : K ⊓ W ≤ K ⊓ Subgroup.centralizer ({j} : Set G) := fun x hx =>
    ⟨hx.1, Subgroup.mem_centralizer_singleton_iff.mpr (hWab x hx.2 j hjW.2)⟩
  obtain ⟨V₀, hV₀, hKWV₀⟩ := IsSylow2In.exists_ge hKW2 hle
  obtain ⟨R', hR', hV₀R'⟩ := IsSylow2In.exists_ge hV₀.2.1 (hV₀.1.trans inf_le_left)
  have hRR' : Nat.card R = Nat.card R' := hRK.natCard_eq hR'
  have hKWcard : Nat.card ↥(K ⊓ W) = Nat.card ↥(R ⊓ W) := by rw [hRWeq]
  have hd1 : Nat.card ↥(K ⊓ W) ∣ Nat.card V₀ := Subgroup.card_dvd_of_le hKWV₀
  have hd2 : Nat.card V₀ ∣ Nat.card R' := Subgroup.card_dvd_of_le hV₀R'
  obtain ⟨m, hm⟩ := hd1
  have ha0 : 0 < Nat.card ↥(K ⊓ W) := Nat.card_pos
  have hR'a : Nat.card R' = Nat.card ↥(K ⊓ W) * 2 := by
    rw [← hRR', hcard, ← hKWcard, mul_comm]
  have hm2 : m ∣ 2 := by
    rw [hR'a, hm] at hd2
    exact Nat.dvd_of_mul_dvd_mul_left ha0 hd2
  rcases (Nat.dvd_prime Nat.prime_two).mp hm2 with h1 | h2
  · have hc : Nat.card V₀ = Nat.card ↥(K ⊓ W) := by rw [hm, h1, mul_one]
    have heq : K ⊓ W = V₀ := Subgroup.eq_of_le_of_card_ge hKWV₀ hc.le
    rw [heq]
    exact hV₀
  · exfalso
    have hcardV₀ : Nat.card V₀ = Nat.card R' := by rw [hm, h2, hR'a]
    have hV₀eq : V₀ = R' := Subgroup.eq_of_le_of_card_ge hV₀R' hcardV₀.ge
    have hR'c : R' ≤ Subgroup.centralizer ({j} : Set G) := hV₀eq ▸ hV₀.1.trans inf_le_right
    have h8 : 8 ≤ Nat.card R' := by
      rw [← hRR']
      exact Sec6Gen.eight_le_of_mem_RSet hΩ hR.1
    have hR'N : R' ≤ Subgroup.normalizer (J : Set G) :=
      Sec6Gen.le_normalizer_of_le_centralizer hΩ hJ hK hKJ.symm hj hR'.1 hR'.2.1 (by omega) hR'c
    have hKnbr : K ∈ omegaNbr Ω J := ⟨hK, hKJ, R', mem_RSet_of_isSylow2In hK hR', hR'.1, hR'N⟩
    exact hnot (T3.omegaNbr_symm h62 hΩ hJ hK hKnbr)

theorem inf_centralizer_le_normalizer_of_D (h62 : Sec6Gen.L6_2Gen) (hΩ : HypOmegaGen Ω)
    (hW : W ∈ WSet Ω) {K J R T : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω)
    (hKJ : K ≠ J) (hR : R ∈ DSet Ω W) (hT : T ∈ DSet Ω W) (hRK : IsSylow2In R K)
    (hTJ : IsSylow2In T J) (hnot : J ∉ omegaNbr Ω K) {j : G} (hj : IsUniqueInvolution J j) :
    K ⊓ Subgroup.centralizer ({j} : Set G) ≤ Subgroup.normalizer (J : Set G) := by
  have hSyl := isSylow2In_inf_W_centralizer h62 hΩ hW hK hJ hKJ hR hT hRK hTJ hnot hj
  obtain ⟨hRWeq, -, hcyc, h4, -⟩ := inf_W_of_mem_D hΩ hW hR hK hRK
  obtain ⟨hTWeq, -, -, hV4, -⟩ := inf_W_of_mem_D hΩ hW hT hJ hTJ
  refine inf_centralizer_le_normalizer' hΩ hK hJ hKJ hj hSyl ?_ ?_ inf_le_left
    (isPGroup_of_mem_WSet hW).to_inf_right ?_
    (inf_W_le_normalizer_of_ne hΩ hW hK hJ hKJ hR hT hRK hTJ).2 ?_
  · rw [← hRWeq]
    exact hcyc
  · rw [← hRWeq]
    exact h4
  · rw [← hTWeq]
    exact hV4
  · intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hj.commute_of_mem hx.1).symm

theorem mem_DSet_of_le_sylow (hΩ : HypOmegaGen Ω)
    (hW : W ∈ WSet Ω) {S : Sylow 2 G} (hWS : W ≤ (S : Subgroup G)) {R : Subgroup G}
    (hR : R ∈ RSet Ω) (hRS : R ≤ (S : Subgroup G)) : R ∈ DSet Ω W := by
  obtain ⟨η, hηG, hWη⟩ := id hW
  have hηS : ∀ V ∈ η, V ≤ (S : Subgroup G) := fun V hV =>
    (hWη ▸ le_iSup₂ (f := fun U (_ : U ∈ η) => U) V hV : V ≤ W).trans hWS
  refine ⟨hR, ?_⟩
  have := le_normalizer_biSup_of_acts ((Sec6Gen.l6_10Gen G Ω hΩ S η hηG hηS).1 R hR hRS)
  rwa [← hWη] at this

theorem exists_sylow_mem_DSet (hΩ : HypOmegaGen Ω)
    (hW : W ∈ WSet Ω) {S : Sylow 2 G} (hWS : W ≤ (S : Subgroup G)) {J U : Subgroup G}
    (hJ : J ∈ Ω) (hU : U ∈ USet Ω) (hUJ : U ≤ J) (hUS : U ≤ (S : Subgroup G)) :
    ∃ T ∈ DSet Ω W, IsSylow2In T J := by
  obtain ⟨-, -, -, -, -, -, -, -, hU4⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hU
  obtain ⟨η, hηG, hWη⟩ := id hW
  obtain ⟨S₀, hη, -⟩ := id hηG
  have hWle : ∀ V ∈ η, V ≤ W := fun V hV => hWη ▸ le_iSup₂ (f := fun U (_ : U ∈ η) => U) V hV
  have hηS : ∀ V ∈ η, V ≤ (S : Subgroup G) := fun V hV => (hWle V hV).trans hWS
  have hJS : 2 < Nat.card ↥(J ⊓ (S : Subgroup G)) :=
    lt_of_lt_of_le (by omega) (hU4.trans (Subgroup.card_le_of_le (le_inf hUJ hUS)))
  have hV₀ : J ⊓ W ∈ η := by
    have := Sec6Gen.l6_11Gen G Ω hΩ S η hηG hηS J hJ hJS
    rwa [← hWη] at this
  have hV₀U : J ⊓ W ∈ USet Ω := (hη.1 hV₀).1
  have hV₀2 : IsPGroup 2 ↥(J ⊓ W) := Sec6Gen.isPGroup_of_mem_USet hΩ hV₀U
  obtain ⟨-, -, -, -, -, -, -, -, hV₀4⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hV₀U
  obtain ⟨zJ, hzJ⟩ := Sec6Gen.exists_uniqueInvolution hΩ hJ
  have hzV₀ : zJ ∈ J ⊓ W := T3.mem_of_isPGroup hzJ inf_le_left hV₀2 (by omega)
  have hWab := commutes_of_mem_WSet hΩ hW
  have hWJ' : (⨆ V ∈ η, V : Subgroup G) ≤ Subgroup.normalizer (J : Set G) := by
    refine iSup₂_le fun V hV => ?_
    by_cases hVeq : V = J ⊓ W
    · rw [hVeq]
      exact inf_le_left.trans Subgroup.le_normalizer
    · obtain ⟨Rv, -, J', hJ', hRvJ', hVRv, -, -, hV4⟩ :=
        Sec6Gen.exists_data_of_mem_USet hΩ (hη.1 hV).1
      have hVJ' : V ≤ J' := hVRv.trans hRvJ'.1
      have hV2 : IsPGroup 2 V := Sec6Gen.isPGroup_of_mem_USet hΩ (hη.1 hV).1
      have hJJ' : J ≠ J' := by
        intro hJJ'
        rw [← hJJ'] at hVJ'
        exact hη.2.1 V hV (J ⊓ W) hV₀ hVeq J hJ ⟨hVJ', inf_le_left⟩
      refine Sec6Gen.le_normalizer_of_le_centralizer hΩ hJ hJ' hJJ' hzJ hVJ' hV2 (by omega) ?_
      intro v hv
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hWab v (hWle V hV hv) zJ hzV₀.2
  have hWJ : W ≤ Subgroup.normalizer (J : Set G) := hWη.le.trans hWJ'
  have hW2 : IsPGroup 2 W := isPGroup_of_mem_WSet hW
  obtain ⟨T, hTJ, hTW⟩ := T3.exists_sylow_normalized hW2 hWJ
  have hWT : W ≤ Subgroup.normalizer (T : Set G) := fun w hw =>
    mem_normalizer_iff_conjSub_eq.mpr (hTW w hw)
  obtain ⟨S', hS'⟩ := (hW2.to_sup_of_normal_right' hTJ.2.1 hWT).exists_le_sylow
  have hWS' : W ≤ (S' : Subgroup G) := le_sup_left.trans hS'
  have hTS' : T ≤ (S' : Subgroup G) := le_sup_right.trans hS'
  exact ⟨T, mem_DSet_of_le_sylow hΩ hW hWS' (mem_RSet_of_isSylow2In hJ hTJ) hTS', hTJ⟩

end Thompson


end CFSG.ClassicalInvolution.Q3.Q3CL
