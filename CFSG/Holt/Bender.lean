module

public import CFSG.Holt.BenderBasic
import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureFixedPointModelRecognition
import CFSG.RankThree.PartTwo.Sec21.HoltCatalog
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.BenderLinearBorel
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.BenderSuzukiBorel
public import CFSG.StronglyEmbedded.BenderNormalSeries

public section

namespace CFSG.Holt

open MulAction CFSG.Open
open scoped MatrixGroups

variable {K : Type*} [Group K] {Ω : Type*} [MulAction K Ω]

theorem exists_isBenderNormal [Finite K] [Finite Ω] [FaithfulSMul K Ω] [IsPretransitive K Ω]
    (hinv : ∀ g : K, orderOf g = 2 → ∃! ω : Ω, g • ω = ω)
    {V : Subgroup K} (hV : Nat.card V = 4) (hV2 : ∀ v ∈ V, v ^ 2 = 1) :
    ∃ (N : Subgroup K) (q i : ℕ), IsBenderNormal Ω N q i := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨α, -⟩ := exists_le_stabilizer_of_fourGroup hinv hV hV2
  obtain ⟨v, hvV, hv1⟩ := exists_mem_ne_one_of_card_eq_four hV
  have hvo : orderOf v = 2 := orderOf_eq_prime (hV2 v hvV) hv1
  have : Nontrivial Ω := nontrivial_of_faithfulSMul hv1
  have hH := fusionStronglyEmbedded_stabilizer_of_forall_existsUnique
    (even_card_of_card_eq_four hV) hinv α
  rcases bender_strongly_embedded_normal_series K _ hH with hcq |
    ⟨M, N, hM, hN, hMN, -, hModd, hNodd, hB⟩
  · exact absurd hcq (not_forall_sylow_cyclic_or_quaternion hV hV2)
  have hMbot : M = ⊥ := eq_bot_of_normal_of_odd_card hinv hV hV2 hM hModd
  have hVN : V ≤ N := le_of_isPGroup_of_odd_index hNodd (isPGroup_of_sq_eq_one hV2)
  have hNtrans : IsPretransitive N Ω := isPretransitive_of_normal hN hvo (hVN hvV) (hinv v hvo)
  have hinvN : ∀ g : N, orderOf g = 2 → ∃! ω : Ω, g • ω = ω := fun g hg =>
    hinv g (by rwa [Subgroup.orderOf_coe])
  have : FaithfulSMul N Ω := ⟨fun h => Subtype.ext (eq_of_smul_eq_smul (α := Ω) h)⟩
  have hVN4 : Nat.card (V.subgroupOf N) = 4 := by
    rw [← hV]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVN).toEquiv
  have hVN2 : ∀ w ∈ V.subgroupOf N, w ^ 2 = 1 := fun w hw => Subtype.ext (hV2 _ hw)
  have hSE : ∀ ω : Ω, fusionStronglyEmbedded (stabilizer N ω) := fun ω =>
    fusionStronglyEmbedded_stabilizer_of_forall_existsUnique (even_card_of_card_eq_four hVN4)
      hinvN ω
  have hcore : CFSG.oddCore N = ⊥ := fusionOddCore_eq_bot hinvN hVN4 hVN2
  have hsub : M.subgroupOf N = CFSG.oddCore N := by
    rw [hMbot, Subgroup.bot_subgroupOf, hcore]
  have hBN : fusionIsBenderGroup (N ⧸ CFSG.oddCore N) :=
    CFSG.RankThree.PartTwo.Sec21.fusionIsBenderGroup_of_mulEquiv
      (QuotientGroup.quotientMulEquivOfEq hsub) hB
  let ι : N ≃* N ⧸ CFSG.oddCore N := MulEquiv.ofBijective (QuotientGroup.mk' (CFSG.oddCore N))
    ⟨(MonoidHom.ker_eq_bot_iff _).mp (by rw [QuotientGroup.ker_mk', hcore]),
      QuotientGroup.mk'_surjective _⟩
  obtain ⟨q, hq⟩ : ∃ q : ℕ,
      q = Nat.card {x : N | x ∈ stabilizer N α ∧ orderOf x = 2} + 1 := ⟨_, rfl⟩
  obtain ⟨-, -, i, hmodel, hindex⟩ :=
    CFSG.ShultStronglyClosedTI.FixedPointModel.fixed_point_model_recognition (hSE α)
      (by rw [hcore]; exact bot_le) (by rw [hcore]; exact bot_le) hBN (q := q)
      (by rw [hq, Nat.add_sub_cancel])
  have hmodel' : (i = 1 ∧ ∃ f : ℕ, 2 ≤ f ∧ q = 2 ^ f ∧ Nonempty (N ≃* PSL(2, GaloisField 2 f))) ∨
      (i = 2 ∧ ∃ a : ℕ, 1 ≤ a ∧ q = 2 ^ (2 * a + 1) ∧ Nonempty (N ≃* Sz a)) ∨
      (i = 3 ∧ ∃ f : ℕ, 2 ≤ f ∧ q = 2 ^ f ∧ Nonempty (N ≃* PSU3 2 f)) := by
    rcases hmodel with ⟨hi, f, hf, hqf, e, -⟩ | ⟨hi, a, ha, hqa, ⟨e⟩, -⟩ |
      ⟨hi, f, hf, hqf, ⟨e⟩, -⟩
    · exact Or.inl ⟨hi, f, hf, hqf, ⟨ι.trans e⟩⟩
    · exact Or.inr (Or.inl ⟨hi, a, ha, hqa, ⟨ι.trans e⟩⟩)
    · exact Or.inr (Or.inr ⟨hi, f, hf, hqf, ⟨ι.trans e⟩⟩)
  have hBB : fusionBenderBorel N q i := by
    rcases hmodel' with ⟨rfl, f, hf, rfl, ⟨e⟩⟩ | ⟨rfl, a, ha, rfl, ⟨e⟩⟩ |
      ⟨rfl, f, hf, rfl, ⟨e⟩⟩
    · have : Finite PSL(2, GaloisField 2 f) := Finite.of_equiv _ e.toEquiv
      exact (bender_psl2_borel_full f hf).map_mulEquiv e.symm
    · have : Finite (Sz a) := Finite.of_equiv _ e.toEquiv
      exact (bender_suzuki_borel_full a ha).map_mulEquiv e.symm
    · have : Finite (PSU3 2 f) := Finite.of_equiv _ e.toEquiv
      exact (bender_psu3_borel_full f hf).map_mulEquiv e.symm
  have hqi : 2 ∣ q ∧ 1 ≤ i := by
    rcases hmodel' with ⟨rfl, f, hf, rfl, -⟩ | ⟨rfl, a, -, rfl, -⟩ | ⟨rfl, f, hf, rfl, -⟩
    · exact ⟨dvd_pow_self 2 (by omega), le_rfl⟩
    · exact ⟨dvd_pow_self 2 (by omega), by norm_num⟩
    · exact ⟨dvd_pow_self 2 (by omega), by norm_num⟩
  have hnat : ∀ f : ℕ, i = 1 → q = 2 ^ f →
      IsNaturalPSL2 (N.map (MulAction.toPermHom K Ω)) f := by
    intro f hi hqf
    rcases hmodel with ⟨-, f₀, -, hqf₀, e, φ, -, -, hφ⟩ | ⟨h2, -⟩ | ⟨h3, -⟩
    · obtain rfl : f = f₀ := Nat.pow_right_injective le_rfl (hqf.symm.trans hqf₀)
      exact isNaturalPSL2_of_equiv (ι.trans e) φ hφ
    · omega
    · omega
  have hrank : CFSG.BenderSuzuki.PFchapter1section1.TwoRankAtLeastTwo N :=
    ⟨V.subgroupOf N, hVN4, fun x => Subtype.ext (hVN2 x x.2)⟩
  refine ⟨N, q, i, ⟨hN, hNodd, hmodel', hBB, hNtrans, ?_, fun ω Q hQω => ?_, hnat⟩⟩
  · rw [← index_stabilizer_of_transitive N α, hindex]
  · have h2Q : 2 ∣ Nat.card (Q : Subgroup N) := by
      rw [(hBB Q).2.2.2.2]
      exact dvd_pow hqi.1 (by omega)
    obtain ⟨d, hd⟩ := exists_prime_orderOf_dvd_card' 2 h2Q
    obtain ⟨β, hβ⟩ := exists_fixes_exactly (hinvN _ (by rw [Subgroup.orderOf_coe, hd]))
    have hβω : ω = β := (hβ ω).mp (hQω d.2)
    have hdω : ∀ ω' : Ω, (d : N) • ω' = ω' ↔ ω' = ω := fun ω' => by rw [hβ, ← hβω]
    have hle := normalizer_le_stabilizer_of_mem d.2 hdω hQω
    rcases (CFSG.ShultStronglyClosedTI.rank_two_strongEmbedding_isCoatom hrank _
      (hBB Q).1).le_iff.mp hle with htop | heq
    · exact absurd htop (hSE ω).1
    · exact heq

section Coset

variable {X : Type*} [Group X] [Finite X] {H : Subgroup X}

theorem exists_isBenderNormal_quotient (hH : fusionStronglyEmbedded H)
    (hO : ∀ R : Subgroup X, R.Normal → Odd (Nat.card R) → R = ⊥)
    {V : Subgroup X} (hV : Nat.card V = 4) (hV2 : ∀ v ∈ V, v ^ 2 = 1) :
    ∃ (N : Subgroup X) (q i : ℕ), IsBenderNormal (X ⧸ H) N q i := by
  have := faithfulSMul_quotient hH hO
  exact exists_isBenderNormal (fun _ ht => existsUnique_fixed_quotient hH ht) hV hV2

theorem isSolvable_of_fusionStronglyEmbedded (hH : fusionStronglyEmbedded H)
    (hO : ∀ R : Subgroup X, R.Normal → Odd (Nat.card R) → R = ⊥)
    {V : Subgroup X} (hV : Nat.card V = 4) (hV2 : ∀ v ∈ V, v ^ 2 = 1) :
    Group.IsSolvable H := by
  obtain ⟨N, q, i, h⟩ := exists_isBenderNormal_quotient hH hO hV hV2
  have := h.isSolvable_stabilizer_ambient ((1 : X) : X ⧸ H)
  rwa [MulAction.stabilizer_quotient] at this

end Coset

end CFSG.Holt
