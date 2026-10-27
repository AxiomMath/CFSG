module

public import CFSG.ClassicalInvolution.Q3.Q3T7T2Core
public import CFSG.ClassicalInvolution.Q3.Q3CPSix67
public import CFSG.ClassicalInvolution.Q3.Q3T7T2Mem

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7T2

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem member_data (hΩ : HypOmegaModU (.sl2 3 1) Ω) {J : Subgroup G} (hJ : J ∈ Ω) {w : G}
    (hw : IsUniqueInvolution J w) : IsClassicalMemberU (.sl2 3 1) J w := by
  obtain ⟨w', hw'⟩ := hΩ.classical J hJ
  have h := hw.eq hw'.isUniqueInvolution_sl2
  rw [h]
  exact hw'

theorem member_facts (hΩ : HypOmegaModU (.sl2 3 1) Ω) {J : Subgroup G} (hJ : J ∈ Ω) {w : G}
    (hw : IsUniqueInvolution J w) :
    Nonempty (↥J ⧸ classicalInvolutionOddCore ↥J ≃* SL(2, ZMod 3)) ∧
      IsSubnormal J (Subgroup.centralizer ({w} : Set G)) ∧ ∀ j ∈ J, w * j = j * w := by
  have hm := member_data hΩ hJ hw
  exact ⟨hm.nonempty_equiv_sl2Three (MemberType.isSolvableType_sl2.mpr (by norm_num)),
    hm.subnormal, fun j hj => hm.comm_of_mem hj⟩

theorem inf_normalized {N J : Subgroup G} [N.Normal] :
    ∀ j ∈ J, ∀ d ∈ J ⊓ N, j * d * j⁻¹ ∈ J ⊓ N := fun j hj d hd =>
  ⟨J.mul_mem (J.mul_mem hj hd.1) (J.inv_mem hj), (inferInstance : N.Normal).conj_mem d hd.2 j⟩

theorem member_dichotomy (hΩ : HypOmegaModU (.sl2 3 1) Ω) {N : Subgroup G} [N.Normal]
    (hN2 : IsPGroup 2 N) {J : Subgroup G} (hJ : J ∈ Ω) {w : G} (hw : IsUniqueInvolution J w)
    (hwN : w ∈ N) : (∀ d ∈ J ⊓ N, d = 1 ∨ d = w) ∨ IsSylow2In (J ⊓ N) J := by
  obtain ⟨⟨e⟩, -, -⟩ := member_facts hΩ hJ hw
  exact dichotomy e hw inf_le_left (hN2.to_le inf_le_right) inf_normalized ⟨hw.mem, hwN⟩

theorem member_A (hΩ : HypOmegaModU (.sl2 3 1) Ω) {N : Subgroup G} [N.Normal]
    (hN2 : IsPGroup 2 N) {J : Subgroup G} (hJ : J ∈ Ω) {w : G} (hw : IsUniqueInvolution J w)
    (hwN : w ∈ N) (hA : ∀ d ∈ J ⊓ N, d = 1 ∨ d = w) : ∀ j ∈ J, ∀ n ∈ N, j * n = n * j := by
  obtain ⟨⟨e⟩, hsub, hcomm⟩ := member_facts hΩ hJ hw
  obtain ⟨π, hsurj, hker⟩ := exists_proj e
  exact centralizes_of_forall_eq hN2 hw.mem hw.ne_one hw.sq hwN hcomm hsub
    (odd_closure_of_proj π hsurj hker) hA

theorem member_B (hΩ : HypOmegaModU (.sl2 3 1) Ω) (hΩg : HypOmegaGen Ω) {N : Subgroup G}
    [N.Normal] (hN2 : IsPGroup 2 N) {J : Subgroup G} (hJ : J ∈ Ω) {w : G}
    (hw : IsUniqueInvolution J w) (hwN : w ∈ N) (hS : IsSylow2In (J ⊓ N) J) {a : G}
    (haN : a ∈ N) (ha : ∀ d ∈ J ⊓ N, a * d = d * a) : ∀ j ∈ J, j * a = a * j := by
  obtain ⟨⟨e⟩, hsub, hcomm⟩ := member_facts hΩ hJ hw
  obtain ⟨π, hsurj, hker⟩ := exists_proj e
  have hq : IsQuatSub (J ⊓ N) :=
    Sec6Gen.isQuatSub_of_mem_RSet hΩg (mem_RSet_of_isSylow2In hJ hS)
  have hZ : ∀ c ∈ J ⊓ N, (∀ d ∈ J ⊓ N, c * d = d * c) → c = 1 ∨ c = w := fun c hc hcc =>
    hw.unique c hc.1 (hq.sq_eq_one_of_central hc hcc)
  exact core_centralizes hN2 hw.mem hw.ne_one hw.sq hwN hcomm hsub
    (odd_closure_of_proj π hsurj hker) hZ haN ha

theorem commutes_of_sylow (hΩg : HypOmegaGen Ω) {N : Subgroup G} (hN2 : IsPGroup 2 N)
    {J K : Subgroup G} (hJ : J ∈ Ω) (hK : K ∈ Ω) (hJK : J ≠ K) (hSJ : IsSylow2In (J ⊓ N) J)
    (hSK : IsSylow2In (K ⊓ N) K) : ∀ x ∈ J ⊓ N, ∀ y ∈ K ⊓ N, x * y = y * x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hNS⟩ := IsPGroup.exists_le_sylow hN2
  have hRJ := mem_RSet_of_isSylow2In hJ hSJ
  have hRK := mem_RSet_of_isSylow2In hK hSK
  have hne : J ⊓ N ≠ K ⊓ N := by
    intro h
    have h8 := Sec6Gen.eight_le_of_mem_RSet hΩg hRJ
    exact hJK (Sec6Gen.eq_of_le_of_le hΩg hJ hK (hN2.to_le inf_le_right) (by omega)
      inf_le_left (h ▸ inf_le_left))
  exact Q3CP.l67Gen G Ω hΩg S (J ⊓ N) hRJ (K ⊓ N) hRK (inf_le_right.trans hNS)
    (inf_le_right.trans hNS) hne

theorem forall_eq_conj {K N : Subgroup G} [N.Normal] {z : G} (g : G)
    (h : ∀ d ∈ K ⊓ N, d = 1 ∨ d = z) : ∀ d ∈ conjSub g K ⊓ N, d = 1 ∨ d = g * z * g⁻¹ := by
  intro d hd
  have hdK : g⁻¹ * d * g ∈ K := mem_conjSub_iff.mp hd.1
  have hdN : g⁻¹ * d * g ∈ N := by
    have := (inferInstance : N.Normal).conj_mem d hd.2 g⁻¹
    simpa using this
  rcases h _ ⟨hdK, hdN⟩ with h1 | h1
  · left
    calc d = g * (g⁻¹ * d * g) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group
  · right
    calc d = g * (g⁻¹ * d * g) * g⁻¹ := by group
      _ = g * z * g⁻¹ := by rw [h1]

theorem thm2_three : ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)),
    HypOmegaModU (.sl2 3 1) Ω → classicalInvolutionOddCore G = ⊥ → (⨆ J ∈ Ω, J) = ⊤ →
    ∀ K ∈ Ω, (∀ J ∈ Ω, ∃ g : G, conjSub g K = J) →
      ∀ z : G, IsUniqueInvolution K z → (∃ N : Subgroup G, N.Normal ∧ IsPGroup 2 N ∧ z ∈ N) →
        K.Normal := by
  intro G _ _ Ω hΩ _ hgen K hK htrans z hz hN
  obtain ⟨N, hNn, hN2, hzN⟩ := hN
  have : N.Normal := hNn
  have hΩg : HypOmegaGen Ω := hypOmegaGenU_of_modU (MemberType.cert_sl2 3 1) hΩ
  have hmem : ∀ J ∈ Ω, ∃ g : G, J = conjSub g K := fun J hJ =>
    let ⟨g, hg⟩ := htrans J hJ
    ⟨g, hg.symm⟩
  have hcent : ∀ J ∈ Ω, ∀ j ∈ J, j * z = z * j := by
    by_cases hφ : ∀ d ∈ K ⊓ N, d = 1 ∨ d = z
    · intro J hJ j hj
      obtain ⟨g, rfl⟩ := hmem J hJ
      exact member_A hΩ hN2 hJ (hz.conj g) (hNn.conj_mem z hzN g) (forall_eq_conj g hφ) j hj z hzN
    · have hSK : IsSylow2In (K ⊓ N) K :=
        (member_dichotomy hΩ hN2 hK hz hzN).resolve_left hφ
      have hS : ∀ J ∈ Ω, IsSylow2In (J ⊓ N) J := by
        intro J hJ
        obtain ⟨g, rfl⟩ := hmem J hJ
        refine (member_dichotomy hΩ hN2 hJ (hz.conj g) (hNn.conj_mem z hzN g)).resolve_left ?_
        intro hφJ
        apply hφ
        have h1 := forall_eq_conj g⁻¹ hφJ
        rw [conjSub_inv_conjSub] at h1
        have h2 : g⁻¹ * (g * z * g⁻¹) * g⁻¹⁻¹ = z := by group
        rwa [h2] at h1
      intro J hJ j hj
      obtain ⟨g, rfl⟩ := hmem J hJ
      by_cases hJK : conjSub g K = K
      · rw [hJK] at hj
        exact (member_facts hΩ hK hz).2.2 j hj |>.symm
      · have hcomm := commutes_of_sylow hΩg hN2 hJ hK hJK (hS _ hJ) hSK
        exact member_B hΩ hΩg hN2 hJ (hz.conj g) (hNn.conj_mem z hzN g) (hS _ hJ) hzN
          (fun d hd => (hcomm d hd z ⟨hz.mem, hzN⟩).symm) j hj
  have hle : (⨆ J ∈ Ω, J) ≤ Subgroup.centralizer ({z} : Set G) :=
    iSup₂_le fun J hJ j hj => Subgroup.mem_centralizer_singleton_iff.mpr (hcent J hJ j hj)
  rw [hgen] at hle
  have hzc : ∀ g : G, g * z = z * g := fun g =>
    Subgroup.mem_centralizer_singleton_iff.mp (hle (Subgroup.mem_top g))
  have hinv : ∀ J ∈ Ω, IsUniqueInvolution J z := by
    intro J hJ
    obtain ⟨g, rfl⟩ := hmem J hJ
    have h1 := hz.conj g
    have hgz : g * z * g⁻¹ = z := by rw [hzc g]; group
    rwa [hgz] at h1
  have hnorm : ∀ J ∈ Ω, J ≤ Subgroup.normalizer (K : Set G) := by
    intro J hJ
    by_cases hJK : J = K
    · rw [hJK]
      exact Subgroup.le_normalizer
    have hcomm := Sec6Gen.comm_le_oddCore_of_twin hΩg hK hJ (Ne.symm hJK) (hinv K hK) (hinv J hJ)
    have hoK : oddCoreOf K ≤ K := Subgroup.map_subtype_le _
    have hKle : ⁅K, J⁆ ≤ K := hcomm.trans (inf_le_left.trans hoK)
    have hconj : ∀ j ∈ J, ∀ k ∈ K, j * k * j⁻¹ ∈ K := by
      intro j hj k hk
      have h1 : ⁅j, k⁆ ∈ K := by
        have := hKle (Subgroup.commutator_mem_commutator hk hj)
        have h2 : ⁅j, k⁆ = ⁅k, j⁆⁻¹ := (commutatorElement_inv k j).symm
        rw [h2]
        exact K.inv_mem this
      have h3 : j * k * j⁻¹ = ⁅j, k⁆ * k := by
        rw [commutatorElement_def]
        group
      rw [h3]
      exact K.mul_mem h1 hk
    intro j hj
    rw [Subgroup.mem_normalizer_iff]
    intro k
    constructor
    · exact fun hk => hconj j hj k hk
    · intro hk
      have := hconj j⁻¹ (J.inv_mem hj) _ hk
      simpa [mul_assoc] using this
  have : Subgroup.normalizer (K : Set G) = ⊤ := by
    rw [eq_top_iff, ← hgen]
    exact iSup₂_le hnorm
  exact Subgroup.normalizer_eq_top_iff.mp this

end CFSG.ClassicalInvolution.Q3.Q3T7T2
