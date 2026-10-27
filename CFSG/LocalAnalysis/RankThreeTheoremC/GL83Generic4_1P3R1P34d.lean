module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1P34c
import CFSG.LocalAnalysis.RankFourTheoremC.PPointPlane
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericCaseSetup
import CFSG.LocalAnalysis.RankThreeTheoremC.InvariantTwoConstrained
import CFSG.RankThree.PartOne.HNB.Tools

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem p34_mem_normalizer_commutator {A D : Subgroup G} {g : G}
    (hA : g ∈ normalizer (A : Set G)) (hD : g ∈ normalizer (D : Set G)) :
    g ∈ normalizer ((⁅A, D⁆ : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq] at hA hD ⊢
  rw [Subgroup.map_commutator, hA, hD]

omit [Finite G] in
theorem p34_mem_normalizer_inf {A B : Subgroup G} {g : G} (hA : g ∈ normalizer (A : Set G))
    (hB : g ∈ normalizer (B : Set G)) : g ∈ normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective, hA, hB]

omit [Finite G] in
theorem p34_mem_normalizer_centralizer_of_le {L : Subgroup G} {g : G}
    (hg : g ∈ centralizer (L : Set G)) :
    g ∈ normalizer ((centralizer (L : Set G) : Subgroup G) : Set G) :=
  normalizer_le_normalizer_centralizer L (centralizer_le_normalizer L hg)

theorem p34_false_of_bad_conj_line (hS : Setting G) (hU0 : FullCoreLocal G) (hD1 : TheoremD1 G)
    (hKM : CFSG.AGLEmbeddingD2.KFactM11Three) (hKA : KFactM11TwoSignalizer)
    (hSig : SignalizerTwoGroupKFact) (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G}
    {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M) {x : G} (hgen : IsGenericPoint 3 P M x)
    {J : Subgroup G} (hJ : IsM11Normal M x J) {D L₀ : Subgroup G}
    (hDQ : D ≤ (P : Subgroup G) ⊓ centralizer ({x} : Set G)) (hD : IsElemAbelian 3 D)
    (hL₀D : L₀ ≤ D) (hL₀bad : ⁅pCoreOf 2 M ⊓ centralizer (L₀ : Set G), D⁆ ≠ ⊥) {g : G}
    (hg : L₀ = (zpowers x).map (MulAut.conj g).toMonoidHom) : False := by
  have hY := p34_yData hS hU0 hKM hKA hp hM hgen hJ
  obtain ⟨hPM, -⟩ := sylow_le_of_isCoreMaxLocal hS hp hM
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  set Q : Subgroup G := (P : Subgroup G) ⊓ C with hQ
  have hQM : Q ≤ M := inf_le_left.trans hPM
  have hQsyl : IsSylowOf 3 Q C := hgen.2.2.1
  have hQab : IsMulCommutative Q := p34_isMulCommutative_of_isSylowOf hY hKM hKA hQsyl
  have hQc : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := fun a ha b hb =>
    p34_comm_of_isMulCommutative hQab ha hb
  set T₀ : Subgroup G := pCoreOf 2 M with hT₀
  have hT₀2 : IsPGroup 2 T₀ := CFSG.PreuniquenessRankFour.Helpers.pCoreOf_isPGroup 2 M
  have hMT₀ : M ≤ normalizer (T₀ : Set G) :=
    CFSG.PreuniquenessRankFour.Helpers.subgroup_normalizes_pCoreOf 2 M
  have hDp : IsPGroup 3 D := CFSG.RankThreeCoreUniqueness.Helpers.elementary_isPGroup 3 D hD
  set A : Subgroup G := T₀ ⊓ centralizer (L₀ : Set G) with hA
  set T : Subgroup G := ⁅A, D⁆ with hT
  have hL₀Q : L₀ ≤ Q := hL₀D.trans hDQ
  have hQL : Q ≤ centralizer (L₀ : Set G) := fun q hq =>
    mem_centralizer_iff.mpr fun l hl => hQc l (hL₀Q hl) q hq
  have hQA : Q ≤ normalizer (A : Set G) := fun q hq =>
    p34_mem_normalizer_inf (hMT₀ (hQM hq)) (p34_mem_normalizer_centralizer_of_le (hQL hq))
  have hQD : Q ≤ normalizer (D : Set G) := fun q hq =>
    centralizer_le_normalizer D (mem_centralizer_iff.mpr fun d hd => hQc d (hDQ hd) q hq)
  have hDA : D ≤ normalizer (A : Set G) := fun d hd => hQA (hDQ hd)
  have hA2 : IsPGroup 2 A := hT₀2.to_le inf_le_left
  have hTA : T ≤ A := Subgroup.commutator_le.mpr fun a ha d hd => by
    have h1 := (mem_normalizer_iff.mp (hDA hd) a⁻¹).mp (A.inv_mem ha)
    have h2 : ⁅a, d⁆ = a * (d * a⁻¹ * d⁻¹) := by
      rw [commutatorElement_def]; group
    rw [h2]
    exact A.mul_mem ha h1
  have hTT : ⁅T, D⁆ = T := by
    have hcop : Nat.Coprime (Nat.card D) (Nat.card A) := by
      obtain ⟨a, ha⟩ := hDp.exists_card_eq
      obtain ⟨b, hb⟩ := hA2.exists_card_eq
      rw [ha, hb]
      exact Nat.Coprime.pow _ _ (by norm_num)
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hnil : Group.IsNilpotent A := hA2.isNilpotent
    exact CFSG.RankThree.PartOne.HNB.commutator_double_eq_self_of_coprime_solvable D A hDA hcop
      inferInstance
  have hT2 : IsPGroup 2 T := hA2.to_le hTA
  have hTL : T ≤ centralizer (L₀ : Set G) := hTA.trans inf_le_right
  have hQT : Q ≤ normalizer (T : Set G) := fun q hq =>
    p34_mem_normalizer_commutator (hQA hq) (hQD hq)
  set κ : G →* G := (MulAut.conj g⁻¹).toMonoidHom with hκ
  have hκinj : Function.Injective κ := (MulAut.conj g⁻¹).injective
  have hxL : g * x * g⁻¹ ∈ L₀ := hg ▸ ⟨x, mem_zpowers x, rfl⟩
  have hκx : κ (g * x * g⁻¹) = x := by
    change g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x
    group
  have hCL : ∀ y ∈ centralizer (L₀ : Set G), κ y ∈ C := by
    intro y hy
    rw [hC, mem_centralizer_singleton_iff]
    have h1 := mem_centralizer_iff.mp hy (g * x * g⁻¹) hxL
    have h2 : κ (g * x * g⁻¹ * y) = κ (y * (g * x * g⁻¹)) := congrArg κ h1
    rw [map_mul κ (g * x * g⁻¹) y, map_mul κ y (g * x * g⁻¹), hκx] at h2
    exact h2.symm
  have hTsC : T.map κ ≤ C := by
    rintro _ ⟨t, ht, rfl⟩
    exact hCL t (hTL ht)
  have hQsC : Q.map κ ≤ C := by
    rintro _ ⟨q, hq, rfl⟩
    exact hCL q (hQL hq)
  have hQs : IsSylowOf 3 (Q.map κ) C := by
    refine isSylowOf_of_card hQsC ?_
    rw [Subgroup.card_map_of_injective hκinj]
    exact hQsyl.card_eq
  have hTs2 : IsPGroup 2 (T.map κ) := hT2.map κ
  have hQsTs : Q.map κ ≤ normalizer ((T.map κ : Subgroup G) : Set G) := by
    rintro _ ⟨q, hq, rfl⟩
    exact Subgroup.le_normalizer_map κ ⟨q, hQT hq, rfl⟩
  have hcomm := p34_commutator_mem hY hKM hKA hSig hQs hTsC hTs2 hQsTs
  have hTsDs : ⁅T.map κ, D.map κ⁆ = T.map κ := by
    rw [← Subgroup.map_commutator, hTT]
  have hTsO : T.map κ ≤ GLBPrimeCore 3 C := by
    calc T.map κ = ⁅T.map κ, D.map κ⁆ := hTsDs.symm
      _ ≤ GLBPrimeCore 3 C := Subgroup.commutator_le.mpr fun t ht d hd =>
        hcomm t ht d (Subgroup.map_mono (hDQ : D ≤ Q) hd)
  have hTsne : T.map κ ≠ ⊥ := fun hb => hL₀bad
    ((Subgroup.map_eq_bot_iff_of_injective T hκinj).mp hb)
  obtain ⟨n, hn⟩ := hTs2.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hTsne (Subgroup.card_eq_one.mp (by simpa using hn))
  have h2dvd : 2 ∣ Nat.card (T.map κ) := by
    rw [hn]
    exact dvd_pow_self 2 hn0
  exact odd_card_pPrimeCoreIn_of_not_le hS hD1 hp hM hgen.2.2.2.ge hgen.2.1.2.2.2.2
    (h2dvd.trans (Subgroup.card_dvd_of_le (hTsO.trans (glbPrimeCore_le_pPrimeCoreIn 3 C))))

theorem p34_not_exists_conj_lines (hS : Setting G) (hU0 : FullCoreLocal G) (hD1 : TheoremD1 G)
    (hKM : CFSG.AGLEmbeddingD2.KFactM11Three) (hKA : KFactM11TwoSignalizer)
    (hSig : SignalizerTwoGroupKFact) (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G}
    {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M) {x : G} (hgen : IsGenericPoint 3 P M x)
    {J : Subgroup G} (hJ : IsM11Normal M x J) {D : Subgroup G}
    (hDQ : D ≤ (P : Subgroup G) ⊓ centralizer ({x} : Set G)) (hD : IsElemAbelian 3 D)
    (hDcard : Nat.card D = 3 ^ 2) :
    ¬ ∃ S : Finset (Subgroup G), S.card = 3 ∧ ∀ L ∈ S, L ≤ D ∧ Nat.card L = 3 ∧
        ∃ g : G, L = (zpowers x).map (MulAut.conj g).toMonoidHom := by
  classical
  rintro ⟨S, hScard, hS'⟩
  obtain ⟨hPM, -⟩ := sylow_le_of_isCoreMaxLocal hS hp hM
  have hDM : D ≤ M := (hDQ.trans inf_le_left).trans hPM
  set T₀ : Subgroup G := pCoreOf 2 M with hT₀
  have hT₀2 : IsPGroup 2 T₀ := CFSG.PreuniquenessRankFour.Helpers.pCoreOf_isPGroup 2 M
  have hMT₀ : M ≤ normalizer (T₀ : Set G) :=
    CFSG.PreuniquenessRankFour.Helpers.subgroup_normalizes_pCoreOf 2 M
  have hcop : Nat.Coprime 3 (Nat.card T₀) := by
    obtain ⟨b, hb⟩ := hT₀2.exists_card_eq
    rw [hb]
    exact Nat.Coprime.pow_right _ (by norm_num)
  have hC : ∀ d ∈ D, (∀ t ∈ T₀, d * t = t * d) → d = 1 := by
    intro d hd hdc
    have hdT : d ∈ T₀ := hS.charTwo M hM.1.1
      ⟨hDM hd, mem_centralizer_iff.mpr fun t ht => (hdc t ht).symm⟩
    obtain ⟨k, hk⟩ := hT₀2 ⟨d, hdT⟩
    have h2 : orderOf d ∣ 2 ^ k :=
      orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
    have hp' : orderOf d ∣ 3 := orderOf_dvd_of_pow_eq_one (hD.2 d hd)
    have hcoprime : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right _ (by norm_num)
    exact orderOf_eq_one_iff.mp
      (Nat.eq_one_of_dvd_one (hcoprime.gcd_eq_one ▸ Nat.dvd_gcd hp' h2))
  obtain ⟨L₁, L₂, hne, ⟨hL₁D, hL₁c, hL₁b⟩, ⟨hL₂D, hL₂c, hL₂b⟩⟩ :=
    CFSG.LocalAnalysis.RankFourTheoremC.exists_two_bad_lines Nat.prime_three hD hDcard
      (fun d hd => hMT₀ (hDM hd)) hcop hC
  have hkey : ∀ L ∈ S, ⁅T₀ ⊓ centralizer (L : Set G), D⁆ ≠ ⊥ → False := fun L hL hbad => by
    obtain ⟨hLD, -, g, hg⟩ := hS' L hL
    exact p34_false_of_bad_conj_line hS hU0 hD1 hKM hKA hSig hp hM hgen hJ hDQ hD hLD hbad hg
  by_cases h1 : L₁ ∈ S
  · exact hkey L₁ h1 hL₁b
  by_cases h2 : L₂ ∈ S
  · exact hkey L₂ h2 hL₂b
  have hcard : (insert L₁ (insert L₂ S)).card = 3 + 2 := by
    rw [Finset.card_insert_of_notMem (by simp [hne, h1]), Finset.card_insert_of_notMem h2,
      hScard]
  have := CFSG.LocalAnalysis.RankFourTheoremC.card_lines_le Nat.prime_three hDcard
    (insert L₁ (insert L₂ S)) (by
      intro L hL
      rcases Finset.mem_insert.mp hL with rfl | hL
      · exact ⟨hL₁D, hL₁c⟩
      rcases Finset.mem_insert.mp hL with rfl | hL
      · exact ⟨hL₂D, hL₂c⟩
      obtain ⟨hLD, hLc, -⟩ := hS' L hL
      exact ⟨hLD, hLc⟩)
  omega

end CFSG.LocalAnalysis.RankThreeTheoremC
