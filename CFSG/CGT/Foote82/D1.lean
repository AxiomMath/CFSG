module

public import CFSG.CGT.Foote82.Statements
public import CFSG.CGT.Foote82.Thm66
public import CFSG.CGT.Foote82.D1Lemma71
import CFSG.CGT.Foote82.D1Bridge
import CFSG.CGT.Foote82.D1Core
import CFSG.CGT.Foote82.D1Steps
import CFSG.CGT.Foote82.FPrime
import CFSG.CGT.Foote82.FTypeMap
import CFSG.CGT.Foote82.TheoremD
import CFSG.LocalAnalysis.WeakClosure81.Eleven
import CFSG.RankThree.PartTwo.Sec19.SimsTheoremCTI

public section

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.QuasithinUnique CFSG.AGLEmbedding CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec19.SimsTheoremC

variable {G : Type} [Group G] [Finite G]

theorem false_of_two_climbs {M K₀ L₁ L₂ Q : Subgroup G} (hL₁ : IsFooteBlock M L₁)
    (hL₂ : IsFooteBlock M L₂) (hne : L₁ ≠ L₂) (hQ : IsPGroup 2 Q)
    (hQK : Q ≤ Subgroup.normalizer (K₀ : Set G)) (h₁ : L₁ ≤ K₀) (h₂ : L₂ ≤ K₀)
    (hc₁ : K₀ = L₁ ∨ (IsComponentOf (barIn K₀ L₁) (centralizerBarIn K₀ Q) ∧
      ((∃ n : ℕ, 8 ≤ n ∧ IsAltNaturalType K₀ n) ∨
        (IsOmegaMinusType K₀ 2 ∧ IsAltNaturalType L₁ 6))))
    (hc₂ : K₀ = L₂ ∨ IsComponentOf (barIn K₀ L₂) (centralizerBarIn K₀ Q))
    (hA6 : IsAltNaturalType L₁ 6 → IsAltNaturalType L₂ 6) : False := by
  have hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a := fun a ha b hb =>
    (Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp (blocks_commute hL₁ hL₂ hne) ha) b hb).symm
  rcases hc₁ with rfl | ⟨hcomp₁, htype⟩
  · exact not_comm_of_isFooteBlock hL₂ fun a ha b hb => hcomm a (h₂ ha) b hb
  rcases hc₂ with rfl | hcomp₂
  · exact not_comm_of_isFooteBlock hL₁ fun a ha b hb => hcomm a ha b (h₁ hb)
  rcases htype with ⟨n, hn, hA⟩ | ⟨hO, h6⟩
  ·
    have hbar := eq_of_isComponentOf_alt (by omega) hA hQ hQK hcomp₁ hcomp₂
    have hB : ∀ u ∈ barIn K₀ L₁, ∀ v ∈ barIn K₀ L₁, u * v = v * u := by
      intro u hu v hv
      rw [hbar] at hv
      obtain ⟨a, ha, rfl⟩ := hu
      obtain ⟨b, hb, rfl⟩ := hv
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hcomm a (Subgroup.mem_subgroupOf.mp ha) b (Subgroup.mem_subgroupOf.mp hb))
    have hq := hcomp₁.2.2
    haveI := hq.2
    have hc : Subgroup.center ↥(barIn K₀ L₁) = ⊤ := by
      rw [eq_top_iff]
      intro x _
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (hB y y.2 x x.2)
    obtain ⟨u, v, huv⟩ := exists_pair_ne (↥(barIn K₀ L₁) ⧸ Subgroup.center ↥(barIn K₀ L₁))
    apply huv
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective u
    obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective v
    rw [QuotientGroup.eq, hc]
    exact Subgroup.mem_top _
  ·
    exact false_of_commute_omegaMinus hO h₁ h₂ hcomm h6 (hA6 h6)

theorem isSubnormal_of_normalizer_le (hG : IsCharTwoType G)
    (hKP : CFSG.Assembly.KProper CFSG.Assembly.InCatalog G) (he : evenRank G = 3) (h66 : Thm66F)
    {M N J : Subgroup G} (hM : GLBIsMaxTwoLocal M) (hN : GLBIsMaxTwoLocal N)
    (hJ : IsFooteBlock M J) (hJF : IsFType J) (hJN : Subgroup.normalizer (J : Set G) ≤ N) :
    IsSubnormal J N := by
  have hP := d1_core_le hM hJ hJN
  have hQN := core_le_of_normalizer_le hJ hJN
  have climb := fun {L : Subgroup G} (hL : IsFooteBlock M L) (hLF : IsFType L) =>
    (d1_chiefHyp hG hM hN hL hLF (block_le_of_normalizer_le hJ hL hJN) hQN hP).climb hKP h66
      (isFPrimeType_of_isFooteBlock he hL hLF)
  have hconj : ∀ y ∈ M, IsFooteBlock M (J.map (MulAut.conj y).toMonoidHom) := fun y hy =>
    isFooteBlock_conj hJ (Subgroup.le_normalizer hy)
  set K₁ := kClosure N J with hK₁def
  obtain ⟨hK₁, hJK₁, hQK₁, -, hc₁⟩ := climb hJ hJF
  have hcomm : ∀ y ∈ M, J.map (MulAut.conj y).toMonoidHom ≠ J →
      ∀ a ∈ J.map (MulAut.conj y).toMonoidHom, ∀ b ∈ K₁, a * b = b * a := by
    intro y hy hne a ha b hb
    obtain ⟨hKy, hJKy, -, -, hcy⟩ := climb (hconj y hy) (hJF.map_conj y)
    have hneK : kClosure N (J.map (MulAut.conj y).toMonoidHom) ≠ K₁ := by
      intro heq
      rw [heq] at hJKy hcy
      refine false_of_two_climbs hJ (hconj y hy) hne.symm
        (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M) hQK₁ hJK₁ hJKy
        ?_ ?_ fun h6 => h6.map (MulAut.conj y)
      · rcases hc₁ with h | ⟨-, -, hcomp, htype⟩
        · exact Or.inl h
        · exact Or.inr ⟨hcomp, htype⟩
      · rcases hcy with h | ⟨-, -, hcomp, -⟩
        · exact Or.inl h
        · exact Or.inr hcomp
    exact (Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp (blocks_commute hKy hK₁ hneK) (hJKy ha))
        b hb).symm
  have hKmN : ∀ m ∈ M, ∀ k ∈ K₁, m * k * m⁻¹ ∈ N := by
    intro m hm k hk
    by_cases hmJ : J.map (MulAut.conj m⁻¹).toMonoidHom = J
    · have hmN : m ∈ N := by
        have h1 : m⁻¹ ∈ Subgroup.normalizer (J : Set G) := mem_normalizer_of_map_conj_eq hmJ
        simpa using hJN (Subgroup.inv_mem _ h1)
      exact N.mul_mem (N.mul_mem hmN (hK₁.le hk)) (N.inv_mem hmN)
    · apply hJN
      apply Subgroup.centralizer_le_normalizer
      rw [Subgroup.mem_centralizer_iff]
      intro j hj
      have h1 := hcomm m⁻¹ (M.inv_mem hm) hmJ (m⁻¹ * j * m) ⟨j, hj, by simp⟩ k hk
      calc j * (m * k * m⁻¹) = m * ((m⁻¹ * j * m) * k) * m⁻¹ := by group
        _ = m * (k * (m⁻¹ * j * m)) * m⁻¹ := by rw [h1]
        _ = m * k * m⁻¹ * j := by group
  set E := Subgroup.closure {g : G | ∃ m ∈ M, ∃ k ∈ K₁, g = m * k * m⁻¹} with hEdef
  have hEN : E ≤ N := (Subgroup.closure_le N).mpr (by
    rintro g ⟨m, hm, k, hk, rfl⟩
    exact hKmN m hm k hk)
  have hK₁E : K₁ ≤ E := fun k hk => Subgroup.subset_closure ⟨1, M.one_mem, k, hk, by group⟩
  have hME : M ≤ Subgroup.normalizer (E : Set G) := by
    have key : ∀ c ∈ M, ∀ g ∈ E, c * g * c⁻¹ ∈ E := by
      intro c hc g hg
      induction hg using Subgroup.closure_induction with
      | mem g hg =>
        obtain ⟨m, hm, k, hk, rfl⟩ := hg
        exact Subgroup.subset_closure ⟨c * m, M.mul_mem hc hm, k, hk, by group⟩
      | one => simp
      | mul a b _ _ ha hb =>
        have : c * (a * b) * c⁻¹ = (c * a * c⁻¹) * (c * b * c⁻¹) := by group
        rw [this]
        exact E.mul_mem ha hb
      | inv a _ ha =>
        have : c * a⁻¹ * c⁻¹ = (c * a * c⁻¹)⁻¹ := by group
        rw [this]
        exact E.inv_mem ha
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro g
    refine ⟨key c hc g, fun hg => ?_⟩
    have := key c⁻¹ (M.inv_mem hc) _ hg
    simpa [mul_assoc] using this
  have hsubE : IsSubnormal K₁ E := by
    have := hK₁.subnormal.inf_of_le hEN
    rwa [inf_eq_left.mpr hK₁E] at this
  have hE2 : pCoreOf 2 E ≠ ⊥ := fun h =>
    pCoreOf_ne_bot_of_isFooteBlock hK₁ (le_bot_iff.mp (h ▸ pCoreOf_le_pCoreOf_of_isSubnormal hsubE))
  have hK₁M : K₁ ≤ M :=
    hK₁E.trans (Subgroup.le_normalizer.trans (normalizer_le_of_glbIsMaxTwoLocal hM hME hE2))
  have hK₁J : K₁ ≤ J :=
    le_of_isSubnormal_of_isFooteBlock hJ.subnormal hK₁M (IsFooteBlock.self hK₁) le_rfl hJK₁
      (IsFooteBlock.commutator_eq hJ) (not_isPGroup_of_block (IsFooteBlock.self hJ))
  have hK₁eq : K₁ = J := le_antisymm hK₁J hJK₁
  rw [← hK₁eq]
  exact hK₁.subnormal

theorem footeSixF_of_thm66F (h66 : Thm66F) : FooteSixF := by
  intro G _ _ _ _ hKP hG he M J hM hJ hJF
  obtain ⟨N, hN, hJN⟩ : ∃ N : Subgroup G, GLBIsMaxTwoLocal N ∧
      Subgroup.normalizer (J : Set G) ≤ N := by
    have h2l : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 J : Set G)) :=
      ⟨pCoreOf 2 J, pCoreOf_ne_bot_of_isFooteBlock hJ,
        CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 J, rfl⟩
    obtain ⟨N, hN, hNN⟩ := CFSG.LocalAnalysis.WeakClosure81.exists_isMaxTwoLocalSubgroup_le h2l
    exact ⟨N, hN, (normalizer_le_normalizer_pCoreOf J).trans hNN⟩
  exact footeSix_of_D1 hG hJ
    ⟨N, hN, hJN, isSubnormal_of_normalizer_le hG hKP he h66 hM hN hJ hJF hJN⟩

end CFSG.CGT.Foote82
