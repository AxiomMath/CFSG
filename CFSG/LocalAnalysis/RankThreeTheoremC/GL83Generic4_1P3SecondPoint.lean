module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3A6Residues
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L28Shape
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3M11P34Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3SylowLift
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3P34Type
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1P34
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1P34e
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1P34f
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3U3Lemma42
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3U3Proved
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3U3Q
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3PlaneCount

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def SecondPointAbel (P : Subgroup G) (u : G) : Prop :=
  ∃ K₀ : Subgroup G, K₀ ≤ P ∧ IsElemAbelian 3 K₀ ∧ Nat.card K₀ = 3 ^ 2 ∧ u ∉ K₀ ∧
    (∀ k ∈ K₀, k * u = u * k) ∧
    (∀ y ∈ P ⊓ centralizer ({u} : Set G), y ^ 3 = 1 → y ∈ K₀ ⊔ zpowers u) ∧
    ∀ k ∈ K₀, k ≠ 1 → ∃ n ∈ centralizer ({u} : Set G),
      n ∈ normalizer (K₀ : Set G) ∧ n * k * n⁻¹ ∉ zpowers k

theorem exists_mem_not_mem_zpowers {K₀ : Subgroup G} (hK₀card : Nat.card K₀ = 3 ^ 2) {k : G}
    (hk1 : k ≠ 1) (hk3 : k ^ 3 = 1) : ∃ k' ∈ K₀, k' ∉ zpowers k := by
  by_contra hno
  push Not at hno
  have h1 : K₀ ≤ zpowers k := fun z hz => hno z hz
  have h2 := Subgroup.card_le_of_le h1
  rw [hK₀card, Nat.card_zpowers, orderOf_eq_prime hk3 hk1] at h2
  omega

theorem exists_move_of_transitive {K₀ : Subgroup G} (hK₀card : Nat.card K₀ = 3 ^ 2)
    {R : G → Prop} (htr : ∀ a ∈ K₀, ∀ b ∈ K₀, a ≠ 1 → b ≠ 1 → ∃ n, R n ∧ n * a * n⁻¹ = b)
    {k : G} (hk : k ∈ K₀) (hk1 : k ≠ 1) (hk3 : k ^ 3 = 1) : ∃ n, R n ∧ n * k * n⁻¹ ∉ zpowers k := by
  obtain ⟨k', hk', hk'n⟩ := exists_mem_not_mem_zpowers hK₀card hk1 hk3
  have hk'1 : k' ≠ 1 := fun h => hk'n (h ▸ one_mem _)
  obtain ⟨n, hn, hnk⟩ := htr k hk k' hk' hk1 hk'1
  exact ⟨n, hn, by rw [hnk]; exact hk'n⟩

theorem linesNotWeaklyClosed_of_secondPointAbel {P : Subgroup G} {u : G} (huP : u ∈ P)
    (hu1 : u ≠ 1) (hu3 : u ^ 3 = 1) (h : SecondPointAbel P u) :
    LinesNotWeaklyClosed 3 u (P ⊓ centralizer ({u} : Set G)) := by
  obtain ⟨K₀, hK₀P, hK₀el, hK₀card, huK₀, hK₀u, hΩ, hmove⟩ := h
  have huo : orderOf u = 3 := orderOf_eq_prime hu3 hu1
  have huC : u ∈ centralizer ({u} : Set G) := mem_centralizer_singleton_iff.mpr rfl
  have hKz : ∀ t ∈ K₀, ∀ c ∈ zpowers u, t * c = c * t := fun t ht c hc => by
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hc
    exact (Commute.zpow_right (show Commute t u from hK₀u t ht) j).eq
  have hKu : ∀ w ∈ zpowers u, w ∈ K₀ → w = 1 := by
    intro w hw hwK
    by_contra hw1
    have hzw := p34_zpowers_eq_of_mem huo hw hw1
    exact huK₀ (zpowers_le.mpr hwK (hzw ▸ mem_zpowers u))
  rintro y hyQ hy1 hy3 hne - hwc
  have hyE : y ∈ K₀ ⊔ zpowers u := hΩ y hyQ hy3
  obtain ⟨k, hk, v, hv, rfl⟩ := u3l42_decomp hKz hyE
  have hkv : k * v = v * k := hKz k hk v hv
  have hk1 : k ≠ 1 := by
    rintro rfl
    have hv1 : v ≠ 1 := by simpa using hy1
    exact hne (by simpa using p34_zpowers_eq_of_mem huo hv hv1)
  have hk3 : k ^ 3 = 1 := hK₀el.2 k hk
  obtain ⟨n, hnC, hnN, hnk⟩ := hmove k hk hk1
  have hnz : n * u = u * n := mem_centralizer_singleton_iff.mp hnC
  have hnv : n * v = v * n := by
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hv
    exact (Commute.zpow_right (show Commute n u from hnz) j).eq
  have hnv' : n * v * n⁻¹ = v := mul_inv_eq_iff_eq_mul.mpr hnv
  set k' : G := n * k * n⁻¹ with hk'
  have hk'K₀ : k' ∈ K₀ := (mem_normalizer_iff.mp hnN k).mp hk
  have hconj : n * (k * v) * n⁻¹ = k' * v := by
    calc n * (k * v) * n⁻¹ = (n * k * n⁻¹) * (n * v * n⁻¹) := by group
      _ = k' * v := by rw [hnv']
  have hk'vQ : k' * v ∈ P ⊓ centralizer ({u} : Set G) := by
    refine Subgroup.mul_mem _ ⟨hK₀P hk'K₀, ?_⟩ ⟨?_, ?_⟩
    · exact mem_centralizer_singleton_iff.mpr (hK₀u k' hk'K₀)
    · exact (zpowers_le.mpr huP) hv
    · exact (zpowers_le.mpr huC) hv
  have hle : (zpowers (k * v)).map (MulAut.conj n).toMonoidHom ≤ P ⊓ centralizer ({u} : Set G) := by
    rw [MonoidHom.map_zpowers]
    refine zpowers_le.mpr ?_
    show n * (k * v) * n⁻¹ ∈ P ⊓ centralizer ({u} : Set G)
    rw [hconj]
    exact hk'vQ
  have hclosed := hwc n hle
  have hmem : k' * v ∈ zpowers (k * v) := by
    have h : n * (k * v) * n⁻¹ ∈ (zpowers (k * v)).map (MulAut.conj n).toMonoidHom :=
      ⟨k * v, mem_zpowers _, rfl⟩
    rw [hclosed, hconj] at h
    exact h
  obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hmem
  have hpow : (k * v) ^ j = k ^ j * v ^ j := Commute.mul_zpow hkv j
  have hj' : k ^ j * v ^ j = k' * v := hpow ▸ hj
  have hKm : k'⁻¹ * k ^ j ∈ K₀ := K₀.mul_mem (K₀.inv_mem hk'K₀) (K₀.zpow_mem hk j)
  have hzm : k'⁻¹ * k ^ j ∈ zpowers u := by
    have h : k'⁻¹ * k ^ j = v * (v ^ j)⁻¹ := by
      calc k'⁻¹ * k ^ j = k'⁻¹ * (k ^ j * v ^ j) * (v ^ j)⁻¹ := by group
        _ = k'⁻¹ * (k' * v) * (v ^ j)⁻¹ := by rw [hj']
        _ = v * (v ^ j)⁻¹ := by group
    rw [h]
    exact Subgroup.mul_mem _ hv (inv_mem (Subgroup.zpow_mem _ hv j))
  have hk'eq : k' = k ^ j := inv_mul_eq_one.mp (hKu _ hzm hKm)
  exact hnk (mem_zpowers_iff.mpr ⟨j, hk'eq.symm⟩)

theorem exists_isElemAbelian_card_of_pRank {H : Subgroup G} {k : ℕ} (hk : 0 < k)
    (h : CFSG.Open.pRank 3 H = k) :
    ∃ E : Subgroup G, E ≤ H ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ k := by
  have hbdd := pRank_set_bddAbove 3 (by norm_num) H
  have hne : {k | ∃ E : Subgroup G, E ≤ H ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ k}.Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    unfold CFSG.Open.pRank at h
    rw [hemp] at h
    simp at h
    omega
  have hmem := Nat.sSup_mem hne hbdd
  unfold CFSG.Open.pRank at h
  rw [h] at hmem
  exact hmem

theorem secondPointAbel_of_a6 (hS : Setting G) (hU0 : FullCoreLocal G) (hA1 : A6SylowData)
    (hAct : KFactA6SylowAction) (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} {M : Subgroup G}
    (hM : IsCoreMaxLocal 3 P M) {u : G} (hugen : IsGenericPoint 3 P M u) {J : Subgroup G}
    (hJ : IsA6Normal M u J) (hR : A6Prop34 3 P J u) : SecondPointAbel (P : Subgroup G) u := by
  have hJC := hJ.le_centralizer
  refine ⟨(P : Subgroup G) ⊓ J, inf_le_left, a6_inf_isElemAbelian hA1 hugen hJ,
    (a6_T_data hS hU0 hA1 hp hM hugen hJ).2.2,
    fun h => a6_x_not_mem_J hS hU0 hp hM hugen hJ h.2,
    fun k hk => mem_centralizer_singleton_iff.mp (hJC hk.2), hR.2.1, fun k hk hk1 => ?_⟩
  obtain ⟨n, hnC, hnN, hnmv⟩ := a6_exists_moving hAct hugen hJ hk hk1
  exact ⟨n, hnC, hnN, hnmv⟩

theorem secondPointAbel_of_l34 (hS : Setting G) (hU0 : FullCoreLocal G) (hL : KFactsL34Full)
    (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M)
    {u : G} (hugen : IsGenericPoint 3 P M u) {J : Subgroup G} (hJ : IsL34Normal M u J)
    (hR : L34Prop34 3 P J u) : SecondPointAbel (P : Subgroup G) u := by
  obtain ⟨hPC, hEel, -, hΩ, -⟩ := hR
  have hJC := hJ.le_centralizer
  have hK₀E : (P : Subgroup G) ⊓ J ≤ ((P : Subgroup G) ⊓ J) ⊔ zpowers u := le_sup_left
  have hK₀el : IsElemAbelian 3 ((P : Subgroup G) ⊓ J) :=
    ⟨⟨⟨fun a b => Subtype.ext (by
      have h := congrArg Subtype.val (hEel.1.is_comm.comm (⟨a, hK₀E a.2⟩ :
        ↥(((P : Subgroup G) ⊓ J) ⊔ zpowers u)) ⟨b, hK₀E b.2⟩)
      exact h)⟩⟩, fun a ha => hEel.2 a (hK₀E ha)⟩
  have hK₀c := l34Sign_card_inf hS hU0 hL.twoSignalizer hL.three hp hM hugen hJ
  have htr := l34_transitive hL.sylowTransitive hugen hJ
  refine ⟨(P : Subgroup G) ⊓ J, inf_le_left, hK₀el, hK₀c,
    fun h => l34_x_not_mem_J hS hU0 hL.twoSignalizer hL.three hp hM hugen hJ h.2,
    fun k hk => mem_centralizer_singleton_iff.mp (hJC hk.2),
    fun y hy hy3 => hΩ y hy.1 hy3, fun k hk hk1 => ?_⟩
  obtain ⟨n, hn, hnk⟩ := exists_move_of_transitive (R := fun n => n ∈ centralizer ({u} : Set G) ∧
    n ∈ normalizer ((((P : Subgroup G) ⊓ J : Subgroup G)) : Set G)) hK₀c
    (fun a ha b hb ha1 hb1 => by
      obtain ⟨n, hnC, hnN, hnab⟩ := htr a ha b hb ha1 hb1
      exact ⟨n, ⟨hnC, hnN⟩, hnab⟩) hk hk1 (hK₀el.2 k hk)
  exact ⟨n, hn.1, hn.2, hnk⟩

theorem secondPointAbel_of_m11 (hS : Setting G) (hU0 : FullCoreLocal G) (hD1 : TheoremD1 G)
    (hKM : CFSG.AGLEmbeddingD2.KFactM11Three) (hKA : KFactM11TwoSignalizer)
    (hKT : KFactM11SylowTransitive) (hSig : SignalizerTwoGroupKFact)
    (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M)
    {u : G} (hugen : IsGenericPoint 3 P M u) {J : Subgroup G} (hJ : IsM11Normal M u J) :
    SecondPointAbel (P : Subgroup G) u := by
  have hPab : IsMulCommutative (P : Subgroup G) :=
    (m11_prop34 hS hU0 hD1 hKM hKA hKT hSig hp hM hugen hJ).1
  obtain ⟨K₀, hK₀Q, hK₀el, hK₀c, huK₀, hK₀tr⟩ :=
    p34_exists_K₀ hS hU0 hKM hKA hKT hp hM hugen hJ
  obtain ⟨huP, ⟨-, hu1, hu3, -, -⟩, -, hrank⟩ := id hugen
  have hK₀C : K₀ ≤ centralizer ({u} : Set G) := hK₀Q.trans inf_le_right
  have hK₀comm : ∀ k ∈ K₀, k * u = u * k := fun k hk =>
    mem_centralizer_singleton_iff.mp (hK₀C hk)
  have hKz : K₀ ≤ centralizer ((zpowers u : Subgroup G) : Set G) := fun k hk => by
    rw [mem_centralizer_iff]
    intro a ha
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp ha
    exact ((Commute.zpow_right (show Commute k u from hK₀comm k hk) j).eq).symm
  have huQ : u ∈ (P : Subgroup G) ⊓ centralizer ({u} : Set G) :=
    ⟨huP, mem_centralizer_singleton_iff.mpr rfl⟩
  have hEel : IsElemAbelian 3 (K₀ ⊔ zpowers u) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_sup_of_commuting 3 hK₀el
      (CFSG.AGLEmbedding.isElemAbelian_zpowers hu3) hKz
  have hEcard : Nat.card ↥(K₀ ⊔ zpowers u) = 3 ^ 3 := by
    rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers Nat.prime_three K₀ hu3 huK₀ hK₀comm, hK₀c]
    norm_num
  have hEQ : K₀ ⊔ zpowers u ≤ (P : Subgroup G) ⊓ centralizer ({u} : Set G) :=
    sup_le hK₀Q (zpowers_le.mpr huQ)
  have hQc : ∀ a ∈ (P : Subgroup G) ⊓ centralizer ({u} : Set G),
      ∀ b ∈ (P : Subgroup G) ⊓ centralizer ({u} : Set G), a * b = b * a := fun a ha b hb =>
    p34_comm_of_isMulCommutative hPab ha.1 hb.1
  refine ⟨K₀, hK₀Q.trans inf_le_left, hK₀el, hK₀c, huK₀, hK₀comm,
    fun y hy hy3 => mem_elem27_of_pow_three hQc hrank hEQ hEel hEcard hy hy3,
    fun k hk hk1 => ?_⟩
  obtain ⟨n, hn, hnk⟩ := exists_move_of_transitive (R := fun n => n ∈ centralizer ({u} : Set G) ∧
    n ∈ normalizer (K₀ : Set G)) hK₀c
    (fun a ha b hb ha1 hb1 => by
      obtain ⟨n, hnC, hnN, hnab⟩ := hK₀tr a ha b hb ha1 hb1
      exact ⟨n, ⟨hnC, hnN⟩, hnab⟩) hk hk1 (hK₀el.2 k hk)
  exact ⟨n, hn.1, hn.2, hnk⟩

theorem second_point_cases (hS : Setting G) (hU0 : FullCoreLocal G) (hD1 : TheoremD1 G)
    (K1 : StronglyEmbeddedRankTwoKFactNoBM) (K2 : StronglyEmbeddedCyclicOuterKFact)
    (K3 : KFactOutCyclic) (K4 : KFactComponentPCoreThree) (hno : NoExcludedSection3 G)
    (hKM : CFSG.AGLEmbeddingD2.KFactM11Three) (hKA : KFactM11TwoSignalizer)
    (hKT : KFactM11SylowTransitive) (hSig : SignalizerTwoGroupKFact) (hL : KFactsL34Full)
    (hA1 : A6SylowData) (hAct : KFactA6SylowAction) (hA34 : GL83GenericPrimeThreeA6Prop34 G)
    (hU34 : GL83GenericPrimeThreeU3Fusion G) (hE34 : GL83GenericPrimeThreeL28Prop34S G)
    (hp : 3 ∈ rankThreeSigmaA G) (hIH : LargerPrimesUnique G 3) {P : Sylow 3 G} {M : Subgroup G}
    (hM : IsCoreMaxLocal 3 P M) (hfail : ¬ rankThreeGamma 1 3 (P : Subgroup G) ≤ M) {u : G}
    (hugen : IsGenericPoint 3 P M u) :
    SecondPointAbel (P : Subgroup G) u ∨ (∃ J : Subgroup G, U3Prop34 3 P J u) ∨
      ∃ J : Subgroup G, L28Prop34S 3 P J u := by
  obtain ⟨J', hJ'C, hCJ', hperf', hlt', hmin', hnot', Q', _, ψ', hψ', hker', hQ'⟩ :=
    exists_isPrimeThreeType_of_generic hS hU0 K1 K2 K3 K4 hno hp hM hugen rfl
  rcases hQ' with hA6 | hU3 | hM11 | hL34 | hL28
  · have hJ : IsA6Normal M u J' :=
      ⟨hJ'C, hCJ', hperf', hnot', hlt', hmin', Q', inferInstance, ψ', hψ', hker', hA6⟩
    exact Or.inl (secondPointAbel_of_a6 hS hU0 hA1 hAct hp hM hugen hJ
      (hA34 3 hp P M hM hfail hIH u hugen rfl J' hJ'C hCJ' hperf' hlt' hmin' hnot' Q' ψ' hψ'
        hker' hA6))
  · have hJ : IsU3Normal M u J' :=
      ⟨hJ'C, hCJ', hperf', hnot', hlt', hmin', Q', inferInstance, ψ', hψ', hker', hU3⟩
    have hf := hU34 3 hp P M hM hfail hIH u hugen rfl J' hJ'C hCJ' hperf' hlt' hmin' hnot' Q' ψ'
      hψ' hker' hU3
    exact Or.inr (Or.inl ⟨J', u3_prop34_of_fusion hS hU0 u3SylowData_proved u3AutData_proved hp hM
      hugen hJ hf.1 hf.2⟩)
  · exact Or.inl (secondPointAbel_of_m11 hS hU0 hD1 hKM hKA hKT hSig hp hM hugen
      ⟨hJ'C, hCJ', hperf', hnot', hlt', hmin', Q', inferInstance, ψ', hψ', hker', hM11⟩)
  · have hJ : IsL34Normal M u J' :=
      ⟨hJ'C, hCJ', hperf', hnot', hlt', hmin', Q', inferInstance, ψ', hψ', hker', hL34⟩
    exact Or.inl (secondPointAbel_of_l34 hS hU0 hL hp hM hugen hJ
      (GL83GenericPrimeThreeL34Prop34.of_kfacts hS hU0 hD1 hSig hL 3 hp P M hM hfail hIH u hugen
        rfl J' hJ'C hCJ' hperf' hlt' hmin' hnot' Q' ψ' hψ' hker' hL34))
  · exact Or.inr (Or.inr ⟨J', hE34 3 hp P M hM hfail hIH u hugen rfl J' hJ'C hCJ' hperf' hlt' hmin'
      hnot' Q' ψ' hψ' hker' hL28⟩)

theorem linesNotWeaklyClosed_of_abelian (hS : Setting G) (hU0 : FullCoreLocal G)
    (hD1 : TheoremD1 G) (K1 : StronglyEmbeddedRankTwoKFactNoBM)
    (K2 : StronglyEmbeddedCyclicOuterKFact) (K3 : KFactOutCyclic) (K4 : KFactComponentPCoreThree)
    (hno : NoExcludedSection3 G) (hKM : CFSG.AGLEmbeddingD2.KFactM11Three)
    (hKA : KFactM11TwoSignalizer) (hKT : KFactM11SylowTransitive)
    (hSig : SignalizerTwoGroupKFact) (hL : KFactsL34Full) (hA1 : A6SylowData)
    (hAct : KFactA6SylowAction) (hA34 : GL83GenericPrimeThreeA6Prop34 G)
    (hU34 : GL83GenericPrimeThreeU3Fusion G) (hE34 : GL83GenericPrimeThreeL28Prop34S G)
    (hp : 3 ∈ rankThreeSigmaA G) (hIH : LargerPrimesUnique G 3) {P : Sylow 3 G} {M : Subgroup G}
    (hM : IsCoreMaxLocal 3 P M) (hfail : ¬ rankThreeGamma 1 3 (P : Subgroup G) ≤ M)
    (hPab : IsMulCommutative (P : Subgroup G)) {u : G} (hugen : IsGenericPoint 3 P M u) :
    LinesNotWeaklyClosed 3 u ((P : Subgroup G) ⊓ centralizer ({u} : Set G)) := by
  have hPc : ∀ a ∈ (P : Subgroup G), ∀ b ∈ (P : Subgroup G), a * b = b * a := fun a ha b hb =>
    p34_comm_of_isMulCommutative hPab ha hb
  obtain ⟨huP, ⟨-, hu1, hu3, -, -⟩, -, hrank⟩ := id hugen
  have hPC : (P : Subgroup G) ≤ centralizer ({u} : Set G) := fun g hg =>
    mem_centralizer_singleton_iff.mpr (hPc g hg u huP)
  rcases second_point_cases hS hU0 hD1 K1 K2 K3 K4 hno hKM hKA hKT hSig hL hA1 hAct hA34 hU34 hE34
    hp hIH hM hfail hugen with h | ⟨J, hR⟩ | ⟨J, hR⟩
  · exact linesNotWeaklyClosed_of_secondPointAbel huP hu1 hu3 h
  ·
    exact absurd ⟨⟨fun a b => Subtype.ext (hPc a (a.2.1) b (b.2.1))⟩⟩ hR.2.2.2.1
  ·
    exfalso
    have hZc := hR.1.2.1
    have hPQ : (P : Subgroup G) ⊓ centralizer ({u} : Set G) = (P : Subgroup G) :=
      inf_eq_left.mpr hPC
    rw [hPQ] at hrank
    obtain ⟨E, hEP, -, hEc⟩ := exists_isElemAbelian_card_of_pRank (by norm_num) hrank
    have hZtop : center ↥(P : Subgroup G) = ⊤ := eq_top_iff.mpr fun a _ =>
      Subgroup.mem_center_iff.mpr fun b => Subtype.ext (hPc _ b.2 _ a.2)
    have hZcard : Nat.card (L28Z (P : Subgroup G)) = Nat.card (P : Subgroup G) := by
      rw [L28Z, Subgroup.card_map_of_injective (P : Subgroup G).subtype_injective, hZtop,
        Subgroup.card_top]
    have h27 := Subgroup.card_le_of_le hEP
    rw [hEc, ← hZcard, hZc] at h27
    omega

end CFSG.LocalAnalysis.RankThreeTheoremC
