module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.LThreeEpsGroup

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott

open CFSG.Open Subgroup
open CFSG.RankThreeCoreUniqueness.Helpers (normal_pGroup_le_pCore)

section Setup

variable {X : Type} [Group X] [Finite X] {L : Subgroup X} {x : X}

theorem T29Setup.pow_three (h : T29Setup X L x) : x ^ 3 = 1 := by
  rw [← h.ord]
  exact pow_orderOf_eq_one x

theorem T29Setup.ne_one (h : T29Setup X L x) : x ≠ 1 := by
  intro h1
  have := h.ord
  rw [h1, orderOf_one] at this
  omega

theorem T29Setup.centralizer_le_of_card_pCore (h : T29Setup X L x)
    (hO : Nat.card (CFSG.pCore 3 X) < 9) : centralizer (L : Set X) ≤ L := by
  haveI hLn : L.Normal := h.normal
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases hZ : center ↥L = ⊥
  · rw [h.centralizer_eq_bot hZ]
    exact bot_le
  set Z : Subgroup X := (center ↥L).map L.subtype with hZdef
  haveI hZn : Z.Normal := normal_map_center_subtype L
  have hZp : IsPGroup 3 Z := h.center_isPGroup.map L.subtype
  have hZO : Z ≤ CFSG.pCore 3 X := normal_pGroup_le_pCore 3 Z hZn hZp
  have hZL : Z ≤ L := Subgroup.map_subtype_le _
  have hOp : IsPGroup 3 (CFSG.pCore 3 X) := CFSG.pCore_isPGroup
  have hOZ : CFSG.pCore 3 X = Z := by
    obtain ⟨k, hk⟩ := hOp.exists_card_eq
    obtain ⟨j, hj⟩ := hZp.exists_card_eq
    have hj0 : j ≠ 0 := by
      rintro rfl
      apply hZ
      have h1 : Z = ⊥ := Subgroup.eq_bot_of_card_eq Z (by rw [hj, pow_zero])
      rw [eq_bot_iff]
      intro c hc
      have : (c : X) ∈ Z := ⟨c, hc, rfl⟩
      rw [h1, Subgroup.mem_bot] at this
      exact (Subgroup.mem_bot).2 (Subtype.ext this)
    have hdvd : 3 ^ j ∣ 3 ^ k := by
      rw [← hj, ← hk]
      exact Subgroup.card_dvd_of_le hZO
    have hjk : j ≤ k := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 hdvd
    have hk1 : k ≤ 1 := by
      by_contra hk2
      have : 3 ^ 2 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hle : Nat.card (CFSG.pCore 3 X) ≤ Nat.card Z := by
      rw [hk, hj]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    exact (Subgroup.eq_of_le_of_card_ge hZO hle).symm
  intro c hc
  set C : Subgroup X := centralizer (L : Set X) with hCdef
  have hcO := h.centralizer_pCore_le
  have hmapO := h.map_pCore_centralizer_le
  have hmem : (⟨c, hc⟩ : ↥C) ∈
      centralizer ((CFSG.pCore 3 ↥C : Subgroup ↥C) : Set ↥C) := by
    rw [mem_centralizer_iff]
    intro o ho
    have hoX : (o : X) ∈ CFSG.pCore 3 X := hmapO ⟨o, ho, rfl⟩
    rw [hOZ] at hoX
    apply Subtype.ext
    exact mem_centralizer_iff.1 hc (o : X) (hZL hoX)
  have hcX : c ∈ CFSG.pCore 3 X := hmapO ⟨⟨c, hc⟩, hcO hmem, rfl⟩
  rw [hOZ] at hcX
  exact hZL hcX

end Setup

section NormalE9

variable {X : Type} [Group X] [Finite X]

theorem exists_E27_le_sylow (hX : CFSG.Open.pRank 3 (⊤ : Subgroup X) = 3) (P : Sylow 3 X) :
    ∃ V : Subgroup X, V ≤ P ∧ IsElemAbelian 3 V ∧ Nat.card V = 27 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨V₀, hV₀, hV27⟩ := exists_elemAbelian_27 hX
  have hp : IsPGroup 3 V₀ := IsPGroup.of_card (n := 3) (by rw [hV27]; norm_num)
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X Q P
  refine ⟨V₀.map (MulAut.conj g).toMonoidHom, ?_, CFSG.SectionRank.isElemAbelian_map hV₀ _, ?_⟩
  · rintro _ ⟨v, hv, rfl⟩
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    exact ⟨v, hQ hv, rfl⟩
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hV27]

theorem three_le_of_mem_normal_E9 (hX : CFSG.Open.pRank 3 (⊤ : Subgroup X) = 3)
    {P : Sylow 3 X} {z : X} (hz : IsOmegaCentral (P : Subgroup X) z) {U : Subgroup X}
    (hUP : U ≤ P) (hU : IsElemAbelian 3 U) (hU9 : Nat.card U = 9)
    (hnorm : (P : Subgroup X) ≤ normalizer (U : Set X)) {u : X} (hu : u ∈ U) :
    3 ≤ CFSG.Open.pRank 3 (centralizer ({u} : Set X)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP3 : IsPGroup 3 (P : Subgroup X) := P.isPGroup'
  have hU1 : U ≠ ⊥ := by
    intro h1
    rw [h1, Subgroup.card_bot] at hU9
    omega
  have hzU : z ∈ U := hz.mem_of_normal hP3 hUP hnorm hU1
  have hcomm := hz.commutator_mem hP3 hUP hU hU9 hzU hnorm
  obtain ⟨V, hVP, hV, hV27⟩ := exists_E27_le_sylow hX P
  have hz3 : z ^ 3 = 1 := by
    rw [← hz.order]
    exact pow_orderOf_eq_one z
  have hz1 : z ≠ 1 := by
    intro h1
    have := hz.order
    rw [h1, orderOf_one] at this
    omega
  have hzV' : ∀ v ∈ V, v * z = z * v := fun v hv => (hz.central v (hVP hv)).symm
  have hzV : z ∈ V := by
    by_contra hzV
    have hZ : IsElemAbelian 3 (zpowers z) := by
      rw [Subgroup.zpowers_eq_closure]
      refine IsElemAbelian.closure_of_commute (fun a ha b hb => ?_) (fun a ha => ?_)
      · rw [Set.mem_singleton_iff] at ha hb
        rw [ha, hb]
      · rw [Set.mem_singleton_iff] at ha
        rw [ha, hz3]
    have hcomm' : ∀ v ∈ V, ∀ c ∈ zpowers z, v * c = c * v := by
      intro v hv c hc
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
      exact (Commute.zpow_right (hzV' v hv) k).eq
    have hW := hV.sup_of_commute hZ hcomm'
    have hW81 : Nat.card ↥(V ⊔ zpowers z) = 3 ^ 4 := by
      rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers Nat.prime_three V hz3 hzV hzV', hV27]
      norm_num
    have h4 := CFSG.SectionRank.le_pRank (by norm_num) (le_top : V ⊔ zpowers z ≤ ⊤) hW hW81
    omega
  have hu3 : u ^ 3 = 1 := hU.2 u hu
  have hcomm2 : ∀ v ∈ V, u * v * u⁻¹ * v⁻¹ ∈ zpowers z := by
    intro v hv
    have h1 := hcomm v (hVP hv) u hu
    have h2 : u * v * u⁻¹ * v⁻¹ = (v * u * v⁻¹ * u⁻¹)⁻¹ := by group
    rw [h2]
    exact inv_mem h1
  have huV : u ∈ normalizer (V : Set X) := by
    refine mem_normalizer_of_conj_mem fun v hv => ?_
    have h1 : u * v * u⁻¹ = (u * v * u⁻¹ * v⁻¹) * v := by group
    rw [h1]
    refine mul_mem ?_ hv
    exact (zpowers_le.2 hzV) (hcomm2 v hv)
  exact three_le_pRank_centralizer_of_unipotent hu3 hz1 hz3 hV hV27 (fun v hv => (hzV' v hv).symm)
    huV hcomm2

end NormalE9

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott
