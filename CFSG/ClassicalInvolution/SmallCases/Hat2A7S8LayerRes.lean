module

public import CFSG.ClassicalInvolution.Asc77.AscT8LayerCl
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.AschTight.Sec6GenL33
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7Tight
public import CFSG.Fischer.Classification.Recognition.PSU6

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Hat2A7S8.Asc77.T8

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T8
  CFSG.ClassicalInvolution.Asc77.Thompson CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.RankThreeCoreUniqueness.Helpers (perfectResidualOf finite_perfectResidualOf_isPerfect
  perfectResidualOf_normalizer_contains)
open scoped commutatorElement

section Single

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {x : G} {K J : Subgroup G}

theorem isClassical2A7_of_isUniqueInvolution
    (hcls : ∀ L ∈ Ω, ∃ u : G, Hat2A7.IsClassical2A7 ⊤ L u) (hK : K ∈ Ω) {z : G}
    (hz : IsUniqueInvolution K z) : Hat2A7.IsClassical2A7 ⊤ K z := by
  obtain ⟨u, hu⟩ := hcls K hK
  rcases hz.unique u hu.mem hu.mul_self with h | h
  · exfalso
    have := hu.orderOf_eq_two
    rw [h, orderOf_one] at this
    omega
  · rw [← h]
    exact hu

omit [Finite G] in
theorem XMem.conj (hΩ : HypOmegaGen Ω) (h : XMem Ω x K) {n : G} (hn : n ∈ cenZ x) :
    XMem Ω x (conjSub n K) := by
  obtain ⟨hK, hN, R, hR, hRx⟩ := h
  have hnx : n * x = x * n := mem_cenZ_iff.mp hn
  have hnx' : n⁻¹ * x = x * n⁻¹ := by
    calc n⁻¹ * x = n⁻¹ * (x * n) * n⁻¹ := by group
      _ = n⁻¹ * (n * x) * n⁻¹ := by rw [hnx]
      _ = x * n⁻¹ := by group
  refine ⟨hΩ.conjInvariant n K hK, ?_, conjSub n R, hR.conj n, ?_⟩
  · rw [mem_normalizer_iff_conjSub_eq] at hN ⊢
    rw [← conjSub_mul, ← hnx, conjSub_mul, hN]
  · intro r hr
    rw [mem_conjSub_iff] at hr
    have h1 := hRx _ hr
    calc r * x = n * (n⁻¹ * r * n) * (n⁻¹ * x) := by group
      _ = n * (n⁻¹ * r * n) * (x * n⁻¹) := by rw [hnx']
      _ = n * ((n⁻¹ * r * n) * x) * n⁻¹ := by group
      _ = n * (x * (n⁻¹ * r * n)) * n⁻¹ := by rw [h1]
      _ = (n * x) * (n⁻¹ * r * n) * n⁻¹ := by group
      _ = (x * n) * (n⁻¹ * r * n) * n⁻¹ := by rw [hnx]
      _ = x * r := by group

theorem layerSet_conj (hΩ : HypOmegaGen Ω) {L : Subgroup G} (hL : L ∈ layerSet Ω x) {n : G}
    (hn : n ∈ cenZ x) : conjSub n L ∈ layerSet Ω x := by
  obtain ⟨K, hK, rfl⟩ := hL
  exact ⟨conjSub n K, XMem.conj hΩ hK hn, layerRes_conj K hn⟩

theorem XMem.zpowers_le_trivialOnQuot (hΩ : HypOmegaGen Ω) (hx : x * x = 1) (h : XMem Ω x K) :
    Subgroup.zpowers x ≤ trivialOnQuot K := by
  obtain ⟨hK, hN, R, hR, hRx⟩ := h
  have hV : IsPGroup 2 ↥(Subgroup.zpowers x) := isPGroup_zpowers_of_sq hx
  refine Subgroup.zpowers_le.mpr ⟨hN, fun k hk => ?_⟩
  exact Sec6Gen.centSylow hΩ hK hR hV
    (fun y hy => mem_normalizer_iff_conjSub_eq.mp (Subgroup.zpowers_le.mpr hN hy))
    (fun r hr v hv => by
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
      exact (Commute.zpow_right (show Commute r x from hRx r hr) m).eq) k hk x
    (Subgroup.mem_zpowers x)

theorem XMem.axisResidual (hΩ : HypOmegaGen Ω) (hx : x * x = 1) (h : XMem Ω x K) {z : G}
    (hz : Hat2A7.IsClassical2A7 ⊤ K z) :
    AxisResidual K (Subgroup.zpowers x) (layerRes x K) z := by
  have hzc : ∀ y ∈ K, y * z = z * y := fun y hy => hz.mul_comm_of_mem hy
  have hsub : IsSubnormal K (Subgroup.centralizer ({z} : Set G)) := by
    have := hz.subnormal
    rwa [top_inf_eq] at this
  exact axisResidual_perfectResidual hz.perfect hz.mem hz.mul_self hzc hsub
    (isPGroup_zpowers_of_sq hx) (XMem.zpowers_le_trivialOnQuot hΩ hx h)

theorem XMem.isClassical2A7 (hΩ : HypOmegaGen Ω) (hx : x * x = 1) (h : XMem Ω x K) {z : G}
    (hz : Hat2A7.IsClassical2A7 ⊤ K z) :
    Hat2A7.IsClassical2A7 (cenZ x) (layerRes x K) z := by
  have ar := XMem.axisResidual hΩ hx h hz
  refine ⟨hz.orderOf_eq_two, ar.mem, finite_perfectResidualOf_isPerfect (K ⊓ cenZ x), ?_, ?_⟩
  · have := ar.subnormal
    rwa [inf_comm] at this
  · obtain ⟨φ⟩ := ar.nonempty_equiv
    exact Hat2A7.A7Witness.of_quotientEquiv φ.symm hz.witness

theorem XMem.exists_data (hΩ : HypOmegaGen Ω) (hcls : ∀ L ∈ Ω, ∃ u : G, Hat2A7.IsClassical2A7 ⊤ L u)
    (hx : x * x = 1) (h : XMem Ω x K) :
    ∃ z : G, IsUniqueInvolution K z ∧ Hat2A7.IsClassical2A7 ⊤ K z ∧
      AxisResidual K (Subgroup.zpowers x) (layerRes x K) z := by
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution hΩ h.1
  have hzc := isClassical2A7_of_isUniqueInvolution hcls h.1 hz
  exact ⟨z, hz, hzc, XMem.axisResidual hΩ hx h hzc⟩

theorem XMem.isUniqueInvolution_layerRes (hΩ : HypOmegaGen Ω)
    (hcls : ∀ L ∈ Ω, ∃ u : G, Hat2A7.IsClassical2A7 ⊤ L u) (hx : x * x = 1) (h : XMem Ω x K)
    {z : G} (hz : IsUniqueInvolution K z) : IsUniqueInvolution (layerRes x K) z := by
  have hzc := isClassical2A7_of_isUniqueInvolution hcls h.1 hz
  exact ⟨(XMem.axisResidual hΩ hx h hzc).mem, hz.ne_one, hz.sq,
    fun y hy hy2 => hz.unique y (layerRes_le x K hy) hy2⟩

theorem XMem.isUniqueInvolution_of_layerRes (hΩ : HypOmegaGen Ω)
    (hcls : ∀ L ∈ Ω, ∃ u : G, Hat2A7.IsClassical2A7 ⊤ L u) (hx : x * x = 1) (h : XMem Ω x K)
    {z : G} (hz : IsUniqueInvolution (layerRes x K) z) : IsUniqueInvolution K z := by
  obtain ⟨z', hz'⟩ := Sec6Gen.exists_uniqueInvolution hΩ h.1
  have hz'L := XMem.isUniqueInvolution_layerRes hΩ hcls hx h hz'
  have hzz' : z' = z := hz'L.eq hz
  rw [← hzz']
  exact hz'

theorem layerRes_omega4 (hΩ : HypOmegaGen Ω) (hcls : ∀ L ∈ Ω, ∃ u : G, Hat2A7.IsClassical2A7 ⊤ L u)
    (hx : x * x = 1) {K J : Subgroup G} (hK : XMem Ω x K) (hJ : XMem Ω x J)
    (hne : layerRes x K ≠ layerRes x J) :
    padicValNat 2 (Nat.card ↥(layerRes x K ⊓ layerRes x J)) ≤ 1 ∧
      (padicValNat 2 (Nat.card ↥(layerRes x K ⊓ layerRes x J)) = 1 →
        ⁅layerRes x K, layerRes x J⁆ ≤ oddCoreOf (layerRes x K) ⊓ oddCoreOf (layerRes x J)) := by
  have hKJ : K ≠ J := fun h => hne (by rw [h])
  obtain ⟨zK, -, -, hRK⟩ := XMem.exists_data hΩ hcls hx hK
  obtain ⟨zJ, -, -, hRJ⟩ := XMem.exists_data hΩ hcls hx hJ
  have hLK : layerRes x K ≤ K ⊓ cenZ x := Subgroup.map_subtype_le _
  have hLJ : layerRes x J ≤ J ⊓ cenZ x := Subgroup.map_subtype_le _
  obtain ⟨h1, h2⟩ := hΩ.omega4 K hK.1 J hJ.1 hKJ
  have hdvd : Nat.card ↥(layerRes x K ⊓ layerRes x J) ∣ Nat.card ↥(K ⊓ J) :=
    Subgroup.card_dvd_of_le (inf_le_inf (hLK.trans inf_le_left) (hLJ.trans inf_le_left))
  have hle := padicValNat_two_le_of_dvd Nat.card_pos.ne' hdvd
  refine ⟨hle.trans h1, fun h => ?_⟩
  have hcomm := h2 (le_antisymm h1 (h ▸ hle))
  have hcK : ∀ j ∈ J, ∀ k ∈ K, j * k * j⁻¹ ∈ K := by
    intro j hj k hk
    have h3 : ⁅j, k⁆ ∈ ⁅K, J⁆ := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator hj hk
    have h4 : ⁅j, k⁆ * k = j * k * j⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [← h4]
    exact K.mul_mem (oddCoreOf_le_self K (hcomm h3).1) hk
  have hcJ : ∀ k ∈ K, ∀ j ∈ J, k * j * k⁻¹ ∈ J := by
    intro k hk j hj
    have h3 : ⁅k, j⁆ ∈ ⁅K, J⁆ := Subgroup.commutator_mem_commutator hk hj
    have h4 : ⁅k, j⁆ * j = k * j * k⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [← h4]
    exact J.mul_mem (oddCoreOf_le_self J (hcomm h3).2) hj
  have hJNK := le_normalizer_of_conj_mem hcK
  have hKNJ := le_normalizer_of_conj_mem hcJ
  have hLJN : ∀ b ∈ layerRes x J, b ∈ Subgroup.normalizer (layerRes x K : Set G) := fun b hb =>
    mem_normalizer_layerRes (hJNK (hLJ hb).1) (hLJ hb).2
  have hLKN : ∀ a ∈ layerRes x K, a ∈ Subgroup.normalizer (layerRes x J : Set G) := fun a ha =>
    mem_normalizer_layerRes (hKNJ (hLK ha).1) (hLK ha).2
  refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
  have h5 : ⁅a, b⁆ ∈ ⁅K, J⁆ := Subgroup.commutator_mem_commutator (hLK ha).1 (hLJ hb).1
  have h6 : ⁅a, b⁆ ∈ layerRes x K := by
    have h7 : b * a⁻¹ * b⁻¹ ∈ layerRes x K :=
      (Subgroup.mem_normalizer_iff.1 (hLJN b hb) a⁻¹).1 ((layerRes x K).inv_mem ha)
    have h8 : ⁅a, b⁆ = a * (b * a⁻¹ * b⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [h8]
    exact (layerRes x K).mul_mem ha h7
  have h9 : ⁅a, b⁆ ∈ layerRes x J := by
    have h7 : a * b * a⁻¹ ∈ layerRes x J :=
      (Subgroup.mem_normalizer_iff.1 (hLKN a ha) b).1 hb
    have h8 : ⁅a, b⁆ = (a * b * a⁻¹) * b⁻¹ := by
      simp only [commutatorElement_def]
    rw [h8]
    exact (layerRes x J).mul_mem h7 ((layerRes x J).inv_mem hb)
  have hoK : oddCoreOf (layerRes x K) = layerRes x K ⊓ oddCoreOf K := hRK.oddCoreIn_eq
  have hoJ : oddCoreOf (layerRes x J) = layerRes x J ⊓ oddCoreOf J := hRJ.oddCoreIn_eq
  rw [hoK, hoJ]
  exact ⟨⟨h6, (hcomm h5).1⟩, ⟨h9, (hcomm h5).2⟩⟩

theorem layerRes_omega5 (hΩ : HypOmegaGen Ω) (hcls : ∀ L ∈ Ω, ∃ u : G, Hat2A7.IsClassical2A7 ⊤ L u)
    (hx : x * x = 1) {K J : Subgroup G} (hK : XMem Ω x K) (hJ : XMem Ω x J)
    (hne : layerRes x K ≠ layerRes x J) {z : G} (hz : IsUniqueInvolution (layerRes x K) z)
    {v : G} (hv : v ∈ layerRes x J) (hnc : ¬ ∀ w ∈ layerRes x J, v * w = w * v)
    (hv2 : IsPGroup 2 (Subgroup.zpowers v)) (hvz : v * z = z * v) :
    v ∈ Subgroup.normalizer (layerRes x K : Set G) := by
  have hKJ : K ≠ J := fun h => hne (by rw [h])
  have hLJ : layerRes x J ≤ J ⊓ cenZ x := Subgroup.map_subtype_le _
  have hzK : IsUniqueInvolution K z := XMem.isUniqueInvolution_of_layerRes hΩ hcls hx hK hz
  have hnc' : ¬ ∀ w ∈ J, v * w = w * v := fun h =>
    hnc fun w hw => h w (hLJ hw).1
  have hvK : v ∈ Subgroup.normalizer (K : Set G) :=
    hΩ.omega5 K hK.1 J hJ.1 hKJ z hzK v (hLJ hv).1 hnc' hv2 hvz
  exact mem_normalizer_layerRes hvK (hLJ hv).2

theorem XMem.isSylow2In_of_layerRes (hΩ : HypOmegaGen Ω)
    (hcls : ∀ L ∈ Ω, ∃ u : G, Hat2A7.IsClassical2A7 ⊤ L u) (hx : x * x = 1) (h : XMem Ω x K)
    {T : Subgroup G} (hT : IsSylow2In T (layerRes x K)) : IsSylow2In T K := by
  obtain ⟨z, -, -, ar⟩ := XMem.exists_data hΩ hcls hx h
  exact isSylow2In_of_cover (layerRes_le x K) ar.cover hT

theorem XMem.eq_of_layerRes_eq (hΩ : HypOmegaGen Ω)
    (hcls : ∀ L ∈ Ω, ∃ u : G, Hat2A7.IsClassical2A7 ⊤ L u) (hx : x * x = 1) {K J : Subgroup G}
    (hK : XMem Ω x K) (hJ : XMem Ω x J) (h : layerRes x K = layerRes x J) : K = J := by
  obtain ⟨V, hV, -⟩ := IsSylow2In.exists_ge (IsPGroup.of_bot : IsPGroup 2 (⊥ : Subgroup G))
    (bot_le : (⊥ : Subgroup G) ≤ layerRes x K)
  have hVK := XMem.isSylow2In_of_layerRes hΩ hcls hx hK hV
  have hVJ := XMem.isSylow2In_of_layerRes hΩ hcls hx hJ (h ▸ hV)
  have h8 := Sec6Gen.eight_le_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hK.1 hVK)
  exact Sec6Gen.eq_of_le_of_le hΩ hK.1 hJ.1 hVK.2.1 (by omega) hVK.1 hVJ.1

theorem XMem.isSylow2In_layerRes_of_le (hΩ : HypOmegaGen Ω)
    (hcls : ∀ L ∈ Ω, ∃ u : G, Hat2A7.IsClassical2A7 ⊤ L u) (hx : x * x = 1) (h : XMem Ω x K)
    {P : Subgroup G} (hP : IsSylow2In P K) (hPx : P ≤ cenZ x) : IsSylow2In P (layerRes x K) := by
  have hCK : K ⊓ cenZ x ≤ K := inf_le_left
  have hP' : IsSylow2In P (K ⊓ cenZ x) := isSylow2In_of_le_of_le hP (le_inf hP.1 hPx) hCK
  obtain ⟨Q, hQ, -⟩ := IsSylow2In.exists_ge (IsPGroup.of_bot : IsPGroup 2 (⊥ : Subgroup G))
    (bot_le : (⊥ : Subgroup G) ≤ layerRes x K)
  have hQK : IsSylow2In Q K := XMem.isSylow2In_of_layerRes hΩ hcls hx h hQ
  have hQC : IsSylow2In Q (K ⊓ cenZ x) :=
    isSylow2In_of_le_of_le hQK (hQ.1.trans (layerRes_le_inf x K)) hCK
  obtain ⟨c, hcC, hcQ⟩ := exists_conj_of_isSylow2In hQC hP'
  have hcN : c ∈ Subgroup.normalizer (layerRes x K : Set G) :=
    mem_normalizer_layerRes (Subgroup.le_normalizer hcC.1) hcC.2
  have hPle : P ≤ layerRes x K := by
    rw [← hcQ]
    calc conjSub c Q ≤ conjSub c (layerRes x K) := conjSub_mono hQ.1
      _ = layerRes x K := mem_normalizer_iff_conjSub_eq.mp hcN
  exact isSylow2In_of_le_of_le hP hPle (layerRes_le x K)

end Single

end CFSG.ClassicalInvolution.Hat2A7S8.Asc77.T8
