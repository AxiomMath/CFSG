module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Remark31

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Subgroup

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G} {s : G}

theorem not_mem_normalizer_pCore (hcs : ConstrainedSetting G T M H S L)
    (hB : Basic31 T M H S L s) {t : G} (htT : t ∈ T) (htS : t ∉ S) :
    t ∉ normalizer (pCoreOf 2 H : Set G) := by
  intro htN
  apply C56.not_conj_le_of_mem_diff hcs hcs.le_T le_rfl hB.idx_T htT htS
  have hUU0 : blockU L ≤ blockU0 S L := C56.le_conjJoin (blockU L) (one_mem S)
  have hU0Q : blockU0 S L ≤ pCoreOf 2 H := by rw [hB.hQ]; exact le_sup_right
  have h1 := C5.conjSubgroup_mono (hUU0.trans hU0Q) t
  rwa [C5.conjSubgroup_eq_self htN] at h1

theorem exists_mem_normalizer_of_lt {X S : Subgroup G} (hX : IsPGroup 2 ↥X) (hSX : S ≤ X)
    (hne : ¬ X ≤ S) : ∃ g ∈ X, g ∈ normalizer (S : Set G) ∧ g ∉ S := by
  classical
  let IP : Subgroup ↥X := S.subgroupOf X
  have hIPne : IP ≠ ⊤ := by
    intro htop
    apply hne
    intro x hx
    have hxIP : (⟨x, hx⟩ : ↥X) ∈ IP := by
      rw [htop]
      trivial
    exact Subgroup.mem_subgroupOf.mp hxIP
  have hIPlt : IP < ⊤ := lt_of_le_of_ne le_top hIPne
  have : Group.IsNilpotent ↥X := hX.isNilpotent
  have hnc : NormalizerCondition ↥X := Group.normalizerCondition_of_isNilpotent (G := ↥X)
  have hlt : IP < Subgroup.normalizer (IP : Set ↥X) := hnc IP hIPlt
  obtain ⟨x, hxN, hxnotIP⟩ := IsConcreteLE.exists_of_lt hlt
  refine ⟨(x : G), x.2, ?_, fun hxS => hxnotIP (Subgroup.mem_subgroupOf.mpr hxS)⟩
  have hxsub : x ∈ (Subgroup.normalizer (S : Set G)).subgroupOf X := by
    rw [Subgroup.subgroupOf_normalizer_eq hSX]
    exact hxN
  exact Subgroup.mem_subgroupOf.mp hxsub

theorem centralizer_pCore_le (hD : AppC.C56DoubleA3) (h27_1 : Lemma2_4_27_1A3)
    (hcfg : A3A3 T M H S L s) {z : G} (hzQ : z ∈ pCoreOf 2 H) (hz1 : z ≠ 1)
    (hzT : z ∈ T ⊓ Subgroup.centralizer (T : Set G)) :
    Subgroup.centralizer (pCoreOf 2 H : Set G) ≤ pCoreOf 2 H := by
  classical
  have hcs := hcfg.cs
  have hB := basic31 hD h27_1 hcfg
  have h3 := hcfg.a3
  have hne : conjJoin S L ≠ L := hcfg.conjJoin_ne
  have hidx : S.relIndex T = 2 := hB.idx_T
  have hTN : T ≤ normalizer (S : Set G) := normalizer_of_relIndex_two hcs.le_T hidx
  obtain ⟨-, -, -, -, hQmax, -, -⟩ := hD G T M H S L hcs h3 hne T hcs.le_T le_rfl hidx
  have h30 := (lemma2_4_30_core hD h27_1 hcfg).2.2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x₀, hx₀T, hx₀S⟩ : ∃ x ∈ T, x ∉ S := by
    by_contra hcon
    push Not at hcon
    have h1 : S.relIndex T = 1 := Subgroup.relIndex_eq_one.mpr hcon
    omega
  have hQ2 : IsPGroup 2 (pCoreOf 2 H) := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H
  have hHN : H ≤ normalizer (pCoreOf 2 H : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H
  have hSH : S ≤ H := hcs.sylow.le
  have hct : CharTwo (normalizer (pCoreOf 2 H : Set G)) := by
    refine charTwo_normalizer_of_inf_center hcs.setting.qtke.2.1 hcs.setting.sylow hQ2 ?_
    intro h
    have hmem : z ∈ pCoreOf 2 H ⊓ (T ⊓ Subgroup.centralizer (T : Set G)) := ⟨hzQ, hzT⟩
    rw [h] at hmem
    exact hz1 (Subgroup.mem_bot.mp hmem)
  set Q := pCoreOf 2 H with hQdef
  set N := normalizer (Q : Set G) with hNdef
  set P := pCoreOf 2 N with hPdef
  have hP2 : IsPGroup 2 P := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 N
  have hNP : N ≤ normalizer (P : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 N
  have hQP : Q ≤ P := le_pCoreOf_of_normalizes Subgroup.le_normalizer le_rfl hQ2
  have hSN : S ≤ N := hSH.trans hHN
  have hPS : P ≤ S := by
    by_contra hPS
    have hSnP : S ≤ normalizer (P : Set G) := hSN.trans hNP
    have hmul := C5.card_sup_mul_card_inf_of_le_normalizer hSnP
    have hX2 : IsPGroup 2 ↥(S ⊔ P) := by
      obtain ⟨n, hn⟩ := hP2.exists_card_eq
      obtain ⟨m, hm⟩ := hcs.sylow.isPGroup.exists_card_eq
      have hdvd : Nat.card ↥(S ⊔ P) ∣ 2 ^ (m + n) := by
        have h1 : Nat.card ↥(S ⊔ P) ∣ Nat.card ↥S * Nat.card ↥P := Dvd.intro _ hmul
        have h2 : Nat.card ↥S * Nat.card ↥P = 2 ^ (m + n) := by rw [hn, hm, pow_add]
        rwa [h2] at h1
      obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
      exact IsPGroup.of_card hk
    obtain ⟨g, hgX, hgNS, hgS⟩ :=
      exists_mem_normalizer_of_lt hX2 le_sup_left (fun h => hPS (le_sup_right.trans h))
    have hPN : P ≤ N := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 N
    have hgN : g ∈ N := (sup_le hSN hPN) hgX
    have hz2 : IsPGroup 2 ↥(zpowers g) := hX2.to_le ((zpowers_le).mpr hgX)
    obtain ⟨n, hnNS, hn⟩ := BenderStart.exists_mem_conj_mem_of_isSylowTwoOf hcs.setting.sylow hTN
      ((zpowers_le).mpr hgNS) hz2
    have htT : n⁻¹ * g * n ∈ T := hn g (mem_zpowers g)
    have htS : n⁻¹ * g * n ∉ S := by
      intro ht
      apply hgS
      have h1 := (Subgroup.mem_normalizer_iff.mp hnNS (n⁻¹ * g * n)).mp ht
      have e : n * (n⁻¹ * g * n) * n⁻¹ = g := by group
      rwa [e] at h1
    have hBmax : IsMaxElemAbelian S (conjR Q n) :=
      C56.isMaxElemAbelian_conjSubgroup hQmax hnNS
    have hBbaum : IsMaxElemAbelian (baum S) (conjR Q n) :=
      (isMaxElemAbelian_iff_of_thompsonJ_le inf_le_left (C5.thompsonJ_le_baum' S)).mpr hBmax
    have hBinv : ∀ g' ∈ S, conjR (conjR Q n) g' = conjR Q n := by
      intro g' hg'
      have hng : n * g' * n⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp hnNS g').mp hg'
      show conjSubgroup (conjSubgroup Q n) g' = conjSubgroup Q n
      rw [conjSubgroup_conjSubgroup]
      have e : n * g' = (n * g' * n⁻¹) * n := by group
      rw [e, ← conjSubgroup_conjSubgroup]
      have h1 := C5.conjSubgroup_eq_self (hSN hng)
      rw [show conjSubgroup Q (n * g' * n⁻¹) = Q from h1]
    have htB : n⁻¹ * g * n ∈ normalizer (conjR Q n : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      rw [mem_conjR, mem_conjR]
      have e : n * ((n⁻¹ * g * n) * y * (n⁻¹ * g * n)⁻¹) * n⁻¹ = g * (n * y * n⁻¹) * g⁻¹ := by
        group
      rw [e]
      exact Subgroup.mem_normalizer_iff.mp hgN (n * y * n⁻¹)
    rcases (h30 x₀ hx₀T hx₀S _ hBbaum).mp hBinv with hBQ | hBQ
    · rw [hBQ] at htB
      exact not_mem_normalizer_pCore hcs hB htT htS htB
    · rw [hBQ] at htB
      have ht' : x₀ * (n⁻¹ * g * n) * x₀⁻¹ ∈ normalizer (Q : Set G) := by
        rw [Subgroup.mem_normalizer_iff]
        intro y
        have h1 := Subgroup.mem_normalizer_iff.mp htB (x₀⁻¹ * y * x₀)
        rw [mem_conjR, mem_conjR] at h1
        have e1 : x₀ * (x₀⁻¹ * y * x₀) * x₀⁻¹ = y := by group
        have e2 : x₀ * ((n⁻¹ * g * n) * (x₀⁻¹ * y * x₀) * (n⁻¹ * g * n)⁻¹) * x₀⁻¹ =
            (x₀ * (n⁻¹ * g * n) * x₀⁻¹) * y * (x₀ * (n⁻¹ * g * n) * x₀⁻¹)⁻¹ := by group
        rwa [e1, e2] at h1
      have ht'T : x₀ * (n⁻¹ * g * n) * x₀⁻¹ ∈ T :=
        T.mul_mem (T.mul_mem hx₀T htT) (T.inv_mem hx₀T)
      have ht'S : x₀ * (n⁻¹ * g * n) * x₀⁻¹ ∉ S := by
        intro h
        apply htS
        have h1 := (Subgroup.mem_normalizer_iff.mp (hTN (T.inv_mem hx₀T))
          (x₀ * (n⁻¹ * g * n) * x₀⁻¹)).mp h
        have e : x₀⁻¹ * (x₀ * (n⁻¹ * g * n) * x₀⁻¹) * x₀⁻¹⁻¹ = n⁻¹ * g * n := by group
        rwa [e] at h1
      exact not_mem_normalizer_pCore hcs hB ht'T ht'S ht'
  have hPQ : P ≤ Q := le_pCoreOf_of_normalizes (hPS.trans hSH) (hHN.trans hNP) hP2
  have hPeq : P = Q := le_antisymm hPQ hQP
  have hct' : N ⊓ Subgroup.centralizer (P : Set G) ≤ P := hct
  intro y hy
  have hyN : y ∈ N := Subgroup.centralizer_le_normalizer _ hy
  have hyP : y ∈ N ⊓ Subgroup.centralizer (P : Set G) := ⟨hyN, by rw [hPeq]; exact hy⟩
  exact hPQ (hct' hyP)

end CFSG.QuasithinUnique.DoubleA3
