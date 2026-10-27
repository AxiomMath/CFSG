module

public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBXDeltaSeededCentralizer
public import CFSG.LocalAnalysis.LargeEvenClassification.LocalRank
public import CFSG.RankThree.GroupTheory.SteinbergBMSimplePlaneFixedTwoCommutator

public section

namespace CFSG.LocalAnalysis.GorensteinLyons

open Subgroup CFSG.Open
open scoped Pointwise commutatorElement

variable {G : Type*} [Group G]

namespace DeltaNormalizer

theorem ncard_le_succ_of_card_eq_prime [Finite G] {p : ℕ} (hp : p.Prime) {A : Subgroup G}
    (hA : Nat.card A = p ^ 2) {L : Set (Subgroup G)} (hL : ∀ D ∈ L, D ≤ A ∧ Nat.card D = p) :
    L.ncard ≤ p + 1 := by
  classical
  have hcard : ∀ D : Subgroup G, ((D : Set G) \ {1}).ncard = Nat.card D - 1 := by
    intro D
    rw [Set.ncard_sdiff_singleton_of_mem D.one_mem, ← Nat.card_coe_set_eq]
    rfl
  have hdisj : L.PairwiseDisjoint (fun D : Subgroup G => (D : Set G) \ {1}) := by
    intro D hD E hE hDE
    rw [Function.onFun, Set.disjoint_left]
    rintro x ⟨hxD, hx1⟩ ⟨hxE, -⟩
    apply hDE
    have hle : D ⊓ E ≤ D := inf_le_left
    have hdvd : Nat.card (D ⊓ E : Subgroup G) ∣ p := (hL D hD).2 ▸ card_dvd_of_le hle
    rcases (Nat.dvd_prime hp).mp hdvd with h | h
    · rw [card_eq_one] at h
      have : x ∈ D ⊓ E := ⟨hxD, hxE⟩
      rw [h, mem_bot] at this
      exact absurd this hx1
    · have h1 : D ⊓ E = D := eq_of_le_of_card_ge hle (by rw [h, (hL D hD).2])
      have h2 : D ⊓ E = E := eq_of_le_of_card_ge inf_le_right (by rw [h, (hL E hE).2])
      exact h1.symm.trans h2
  have hsub : (⋃ D ∈ L, (D : Set G) \ {1}) ⊆ (A : Set G) \ {1} :=
    Set.iUnion₂_subset fun D hD => Set.sdiff_subset_sdiff_left (hL D hD).1
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [(Set.toFinite L).ncard_biUnion (fun _ _ => Set.toFinite _) hdisj, hcard A, hA,
    finsum_mem_congr rfl (fun D hD => by rw [hcard D, (hL D hD).2]),
    finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite L), Finset.sum_const, smul_eq_mul,
    ← Set.ncard_eq_toFinset_card L (Set.toFinite L)] at h1
  have hp1 : 0 < p - 1 := by have := hp.two_le; omega
  have h2 : p ^ 2 - 1 = (p + 1) * (p - 1) := by
    have h3 : 1 ≤ p := hp.one_lt.le
    have h4 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp.pos
    zify [h3, h4]
    ring
  rw [h2] at h1
  exact Nat.le_of_mul_le_mul_right h1 hp1

theorem inf_centralizer_self_eq (S : Subgroup G) :
    S ⊓ centralizer (S : Set G) = (center S).map S.subtype := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxS, hxC⟩ := mem_inf.mp hx
    refine mem_map.mpr ⟨⟨x, hxS⟩, mem_center_iff.mpr fun g => ?_, rfl⟩
    exact Subtype.ext (mem_centralizer_iff.mp hxC g g.2)
  · intro hx
    obtain ⟨y, hy, rfl⟩ := mem_map.mp hx
    refine mem_inf.mpr ⟨y.2, mem_centralizer_iff.mpr fun g hg => ?_⟩
    exact congrArg Subtype.val (mem_center_iff.mp hy ⟨g, hg⟩)

theorem pRank_eq_twoLocalRank_of_isBmax [Finite G] {p : ℕ} (hp : 1 < p) {B : Subgroup G}
    (hB : GLAIsBmax p B) : CFSG.Open.pRank p B = GLATwoLocalRank p G ∧
      ∀ Y : Subgroup G, IsPLocal 2 Y → B ≤ Y → CFSG.Open.pRank p Y = GLATwoLocalRank p G := by
  have hup : ∀ Y : Subgroup G, IsPLocal 2 Y → CFSG.Open.pRank p Y ≤ GLATwoLocalRank p G :=
    fun Y hY => CFSG.LargeEvenClassification.Helpers.pRank_le_twoLocalPRank hp Y hY
  have hlow : GLATwoLocalRank p G ≤ CFSG.Open.pRank p B := by
    refine le_csSup ⟨Nat.card G, ?_⟩ ⟨B, le_rfl, hB.1, hB.2.1⟩
    rintro k ⟨E, -, -, hE⟩
    exact CFSG.LargeEvenClassification.Helpers.rank_exponent_le_card hp E hE
  have hY : ∀ Y : Subgroup G, IsPLocal 2 Y → B ≤ Y →
      CFSG.Open.pRank p Y = GLATwoLocalRank p G := fun Y hY hBY =>
    le_antisymm (hup Y hY) (hlow.trans (CFSG.LargeEvenClassification.Helpers.pRank_mono hp hBY))
  obtain ⟨U, hU1, hU2, hBU⟩ := hB.2.2
  exact ⟨le_antisymm ((CFSG.LargeEvenClassification.Helpers.pRank_mono hp hBU).trans
    (hup _ ⟨U, hU1, hU2, rfl⟩)) hlow, hY⟩

end DeltaNormalizer

open DeltaNormalizer

theorem delta_normalizer_central_product_and_line_fixed_subgroups [Finite G] [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hchar : IsCharacteristicPType G 2) {p : ℕ}
    (hp : p ∈ GLABeta 4 G) (hfail : ¬ GLADeltaZero G p) {B D₀ S₀ : Subgroup G}
    (hB : GLAIsBmax p B) (hD₀B : D₀ ≤ B) (hD₀ : IsElemAbelian p D₀)
    (hD₀card : Nat.card D₀ = p ^ 2) (hW : IsDeltaSeedWitness p B D₀ S₀) {S : Subgroup G}
    (hS : Maximal (· ∈ deltaSeededFamily p B S₀) S) {A H Q R U : Subgroup G}
    (hA : A = B ⊓ centralizer (S : Set G)) (hH : H = normalizer (S : Set G))
    (hQ : Q = CFSG.inSubgroup (CFSG.pCore 2) H) (hR : R = Q ⊓ centralizer (S : Set G))
    (hU : U = ⁅Q, A⁆) {F : Subgroup G → Subgroup G}
    (hF : ∀ D : Subgroup G, F D = Q ⊓ centralizer (D : Set G)) {L : Set (Subgroup G)}
    (hL : L = {D | D ≤ A ∧ Nat.card D = p ∧ S < F D}) :
    (R.subgroupOf H).Normal ∧ U ≤ R ∧ ⁅U, A⁆ = U ∧
    (S : Set G) * (U : Set G) = (Q : Set G) ∧ (S : Set G) * (R : Set G) = (Q : Set G) ∧
    S ⊔ U = Q ∧ S ⊔ R = Q ∧ ⁅S, R⁆ = ⊥ ∧ S ⊓ R = (center S).map S.subtype ∧
    R ⊓ centralizer (A : Set G) = (center S).map S.subtype ∧ A ⊓ centralizer (R : Set G) = ⊥ ∧
    (∃ (_ : (S.subgroupOf Q).Normal) (_ : (((center S).map S.subtype).subgroupOf R).Normal),
      (∃ e : R ⧸ ((center S).map S.subtype).subgroupOf R ≃* Q ⧸ S.subgroupOf Q,
        ∀ (r : R) (q : Q), (r : G) = q → e (QuotientGroup.mk r) = QuotientGroup.mk q) ∧
      ∀ D ∈ L, ∀ E ∈ L, D ≠ E →
        ((F D).subgroupOf Q).map (QuotientGroup.mk' (S.subgroupOf Q)) ⊓
          ((F E).subgroupOf Q).map (QuotientGroup.mk' (S.subgroupOf Q)) = ⊥) ∧
    2 ≤ L.ncard ∧ L.ncard ≤ p + 1 ∧ Q = ⨆ D ∈ L, F D ∧
    (∀ D ∈ L, S < F D ∧ F D < Q ∧ B ≤ normalizer (F D : Set G) ∧
      B ⊓ centralizer (F D : Set G) = D ∧ IsPLocal 2 (normalizer (F D : Set G)) ∧
      normalizer (F D : Set G) < ⊤ ∧
      CFSG.Open.pRank p (normalizer (F D : Set G)) = GLATwoLocalRank p G) ∧
    (∀ D ∈ L, ∀ E ∈ L, D ≠ E → F D ⊓ F E = S) ∧
    CFSG.Open.pRank p B = GLATwoLocalRank p G ∧
    (∀ Y : Subgroup G, IsPLocal 2 Y → B ≤ Y → CFSG.Open.pRank p Y = GLATwoLocalRank p G) ∧
    CFSG.Open.pRank p H = GLATwoLocalRank p G ∧
    ∀ M ∈ maximalTwoLocalsContaining (H : Set G),
      CFSG.Open.pRank p M = GLATwoLocalRank p G := by
  classical
  have hpp : p.Prime := hp.1
  have hp2 : p ≠ 2 := hp.2.1
  have := Fact.mk hpp
  have hBX := ((delta_seeded_maximal_local_rank_two_centralizer hnab hchar hp hfail).2 B D₀ S₀ hB
    hD₀B hD₀ hD₀card hW).2 S hS
  rw [← hA, ← hH, ← hQ] at hBX
  obtain ⟨hAcard, -, -, -, hSQ, hCQA, -, hSQlt⟩ := hBX
  obtain ⟨-, -, -, -, hS₀ne, -⟩ := hW
  obtain ⟨⟨hS2, hS₀S, hBS, -⟩, hSmax⟩ := hS
  have hSne : S ≠ ⊥ := fun h => hS₀ne (le_bot_iff.mp (h ▸ hS₀S))
  have hHloc : IsPLocal 2 H := ⟨S, hSne, hS2, hH⟩
  have hcharH : IsCharacteristicP 2 H := hchar H hHloc
  have hQ2 : IsPGroup 2 Q := by rw [hQ]; exact isPGroup_inSubgroup_pCore 2 H
  have hHQ : H ≤ normalizer (Q : Set G) := by rw [hQ]; exact le_normalizer_inSubgroup_pCore 2 H
  have hQH : Q ≤ H := by rw [hQ]; exact map_subtype_le _
  have hHS : H ≤ normalizer (S : Set G) := hH.le
  have hAB : A ≤ B := by rw [hA]; exact inf_le_left
  have hAS : A ≤ centralizer (S : Set G) := by rw [hA]; exact inf_le_right
  have hBH : B ≤ H := by rw [hH]; exact hBS
  have hAH : A ≤ H := hAB.trans hBH
  have hAQ : A ≤ normalizer (Q : Set G) := hAH.trans hHQ
  have hAel : IsElemAbelian p A := isElemAbelian_of_le_elem hAB hB.1
  have hRQ : R ≤ Q := by rw [hR]; exact inf_le_left
  have hRS : R ≤ centralizer (S : Set G) := by rw [hR]; exact inf_le_right
  have hRH : R ≤ H := hRQ.trans hQH
  have hSF : ∀ D : Subgroup G, D ≤ A → S ≤ F D := fun D hDA => by
    rw [hF]
    exact le_inf hSQ (le_centralizer_iff.mp (hDA.trans hAS))
  have hFQ' : ∀ D : Subgroup G, F D ≤ Q := fun D => by rw [hF]; exact inf_le_left
  have hconjS : ∀ q ∈ Q, ∀ s ∈ S, q * s * q⁻¹ ∈ S := fun q hq s hs =>
    (mem_normalizer_iff.mp (hHS (hQH hq)) s).mp hs
  have hcentQ : ∀ X : Subgroup G, X ≤ H → X ≤ centralizer (Q : Set G) → IsPGroup p X →
      X = ⊥ := by
    intro X hXH hXC hXp
    have hXQ : X ≤ Q := by
      rw [hQ] at hXC ⊢
      exact le_inSubgroup_pCore_of_le_centralizer hcharH hXH hXC
    exact eq_bot_of_isPGroup_of_le hpp hp2 hXp hQ2 hXQ
  have hHR : H ≤ normalizer (R : Set G) := fun h hh => by
    rw [hR]
    exact mem_normalizer_inf_of_mem' (hHQ hh) (mem_normalizer_centralizer_of_mem' (hHS hh))
  have hUR : U ≤ R := by
    rw [hU, commutator_le]
    intro q hq a ha
    have hqa : a * q⁻¹ * a⁻¹ ∈ Q := (mem_normalizer_iff.mp (hAQ ha) _).mp (inv_mem hq)
    rw [hR, commutatorElement_def]
    refine mem_inf.mpr ⟨by simpa only [mul_assoc] using mul_mem hq hqa,
      mem_centralizer_iff.mpr fun s hs => ?_⟩
    have hs₁ : q⁻¹ * s * q ∈ S := by simpa using hconjS _ (inv_mem hq) s hs
    have hsa : s * a = a * s := mem_centralizer_iff.mp (hAS ha) s hs
    have hs₁a : q⁻¹ * s * q * a = a * (q⁻¹ * s * q) := mem_centralizer_iff.mp (hAS ha) _ hs₁
    calc s * (q * a * q⁻¹ * a⁻¹) = q * (q⁻¹ * s * q * a) * q⁻¹ * a⁻¹ := by group
      _ = q * (a * (q⁻¹ * s * q)) * q⁻¹ * a⁻¹ := by rw [hs₁a]
      _ = q * a * q⁻¹ * (a⁻¹ * (a * s) * a⁻¹) := by group
      _ = q * a * q⁻¹ * (a⁻¹ * (s * a) * a⁻¹) := by rw [hsa]
      _ = q * a * q⁻¹ * a⁻¹ * s := by group
  have hUQ : U ≤ Q := hUR.trans hRQ
  have hA2 : ¬ 2 ∣ Nat.card A := by
    rw [hAcard]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hpp).mp
      (Nat.prime_two.dvd_of_dvd_pow h)).symm
  let _ : MulDistribMulAction A Q := MulDistribMulAction.compHom Q (Subgroup.inclusion hAQ)
  have hfac := ComponentInitial.coprime_pgroup_commutator_factorization (A := A) (Q := Q)
    Nat.prime_two hQ2 hA2
  have hTopQ : (⊤ : Subgroup Q).map Q.subtype = Q := by
    rw [← MonoidHom.range_eq_map, range_subtype]
  have e1 := RankThree.GroupTheory.SteinbergBM.map_actionCommutator_conj hAQ (⊤ : Subgroup Q)
  rw [hTopQ, ← hU] at e1
  have hUA : ⁅U, A⁆ = U := by
    have e2 := RankThree.GroupTheory.SteinbergBM.map_actionCommutator_conj hAQ
      (ComponentInitial.actionCommutator A (⊤ : Subgroup Q))
    rw [hfac.2, e1] at e2
    exact e2.symm
  have hfacQ : ∀ q ∈ Q, ∃ u ∈ U, ∃ s ∈ S, q = u * s := by
    intro q hq
    obtain ⟨d, hd, c, hc, hdc⟩ := hfac.1 ⟨q, hq⟩
    refine ⟨d, ?_, c, ?_, congrArg Subtype.val hdc⟩
    · rw [← e1]
      exact mem_map_of_mem _ hd
    · rw [← hCQA]
      refine mem_inf.mpr ⟨c.2, mem_centralizer_iff.mpr fun a ha => ?_⟩
      have h1 := congrArg Subtype.val (hc ⟨a, ha⟩)
      change a * (c : G) * a⁻¹ = c at h1
      calc a * (c : G) = a * c * a⁻¹ * a := by group
        _ = c * a := by rw [h1]
  have hSU : ∀ q ∈ Q, ∃ s ∈ S, ∃ u ∈ U, s * u = q := by
    intro q hq
    obtain ⟨u, hu, s, hs, rfl⟩ := hfacQ q hq
    exact ⟨u * s * u⁻¹, hconjS u (hUQ hu) s hs, u, hu, by group⟩
  have hSUset : (S : Set G) * (U : Set G) = (Q : Set G) := by
    ext x
    refine ⟨fun hx => ?_, fun hx => Set.mem_mul.mpr (hSU x hx)⟩
    obtain ⟨s, hs, u, hu, rfl⟩ := Set.mem_mul.mp hx
    exact mul_mem (hSQ hs) (hUQ hu)
  have hSRset : (S : Set G) * (R : Set G) = (Q : Set G) := by
    ext x
    refine ⟨fun hx => ?_, fun hx => ?_⟩
    · obtain ⟨s, hs, r, hr, rfl⟩ := Set.mem_mul.mp hx
      exact mul_mem (hSQ hs) (hRQ hr)
    · obtain ⟨s, hs, u, hu, hsu⟩ := hSU x hx
      exact Set.mem_mul.mpr ⟨s, hs, u, hUR hu, hsu⟩
  have hSUsup : S ⊔ U = Q := le_antisymm (sup_le hSQ hUQ) fun x hx => by
    obtain ⟨s, hs, u, hu, rfl⟩ := hSU x hx
    exact mul_mem (mem_sup_left hs) (mem_sup_right hu)
  have hSRsup : S ⊔ R = Q := le_antisymm (sup_le hSQ hRQ) fun x hx => by
    obtain ⟨s, hs, u, hu, rfl⟩ := hSU x hx
    exact mul_mem (mem_sup_left hs) (mem_sup_right (hUR hu))
  have hZ := inf_centralizer_self_eq S
  have hSR : S ⊓ R = (center S).map S.subtype := by
    rw [hR, ← inf_assoc, inf_of_le_left hSQ, hZ]
  have hRA : R ⊓ centralizer (A : Set G) = (center S).map S.subtype := by
    rw [hR, inf_right_comm, hCQA, hZ]
  have hfaith : A ⊓ centralizer (R : Set G) = ⊥ := by
    refine hcentQ _ (inf_le_left.trans hAH) (fun x hx => ?_)
      (isPGroup_of_isElemAbelian' (isElemAbelian_of_le_elem inf_le_left hAel))
    rw [mem_centralizer_iff]
    intro q hq
    obtain ⟨u, hu, s, hs, rfl⟩ := hfacQ q hq
    have h1 : u * x = x * u := mem_centralizer_iff.mp (mem_inf.mp hx).2 u (hUR hu)
    have h2 : s * x = x * s := mem_centralizer_iff.mp (hAS (mem_inf.mp hx).1) s hs
    rw [mul_assoc, h2, ← mul_assoc, h1, mul_assoc]
  have hLmem : ∀ D ∈ L, D ≤ A ∧ Nat.card D = p ∧ S < F D := fun D hD => by
    rw [hL] at hD
    exact hD
  have hAne : A ≠ ⊥ := fun h => by
    rw [h, card_bot] at hAcard
    have := Nat.one_lt_pow two_ne_zero hpp.one_lt
    omega
  have hQp : ¬ p ∣ Nat.card Q := by
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hQ2
    rw [hm]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp (hpp.dvd_of_dvd_pow h))
  have hQgen : ∀ X : Subgroup G, S ≤ X → (∀ D ∈ L, F D ≤ X) → Q ≤ X := by
    intro X hSX hLX
    refine le_of_forall_hyperplane_centralizer_le hpp hAel hAne hAQ hQp fun E hEA hEidx => ?_
    have hEcard : Nat.card E = p := by
      have h1 := card_mul_index (E.subgroupOf A)
      rw [Nat.card_congr (subgroupOfEquivOfLe hEA).toEquiv, ← relIndex, hEidx, hAcard,
        pow_two] at h1
      exact Nat.eq_of_mul_eq_mul_right hpp.pos h1
    rw [← hF E]
    by_cases hlt : S < F E
    · exact hLX E (by rw [hL]; exact ⟨hEA, hEcard, hlt⟩)
    · rw [← (hSF E hEA).lt_or_eq.resolve_left hlt]
      exact hSX
  have hFQ : ∀ D ∈ L, F D < Q := by
    intro D hD
    obtain ⟨hDA, hDcard, -⟩ := hLmem D hD
    refine lt_of_le_of_ne (hFQ' D) fun hDQ => ?_
    have hDC : D ≤ centralizer (Q : Set G) := by
      rw [← hDQ, hF]
      exact le_centralizer_iff.mp inf_le_right
    have hD1 := hcentQ D (hDA.trans hAH) hDC
      (isPGroup_of_isElemAbelian' (isElemAbelian_of_le_elem hDA hAel))
    rw [hD1, card_bot] at hDcard
    exact hpp.one_lt.ne hDcard
  have hLp : L.ncard ≤ p + 1 :=
    ncard_le_succ_of_card_eq_prime hpp hAcard fun D hD => ⟨(hLmem D hD).1, (hLmem D hD).2.1⟩
  have hL2 : 2 ≤ L.ncard := by
    by_contra hlt
    rcases (by omega : L.ncard = 0 ∨ L.ncard = 1) with h | h
    · rw [Set.ncard_eq_zero] at h
      exact not_le_of_gt hSQlt (hQgen S le_rfl fun D hD => by rw [h] at hD; exact absurd hD id)
    · obtain ⟨D₁, hD₁⟩ := Set.ncard_eq_one.mp h
      have hD₁L : D₁ ∈ L := by rw [hD₁]; exact Set.mem_singleton D₁
      refine not_le_of_gt (hFQ D₁ hD₁L) (hQgen _ (hSF D₁ (hLmem D₁ hD₁L).1) fun D hD => ?_)
      rw [hD₁, Set.mem_singleton_iff] at hD
      rw [hD]
  obtain ⟨D₁, hD₁⟩ : L.Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
  have hQsup : Q = ⨆ D ∈ L, F D :=
    le_antisymm (hQgen _ ((hSF D₁ (hLmem D₁ hD₁).1).trans (le_iSup₂_of_le D₁ hD₁ le_rfl))
      fun D hD => le_iSup₂_of_le D hD le_rfl) (iSup₂_le fun D _ => hFQ' D)
  have hBrank := pRank_eq_twoLocalRank_of_isBmax hpp.one_lt hB
  have hBcomm : ∀ D : Subgroup G, D ≤ B → B ≤ centralizer (D : Set G) := fun D hDB b hb =>
    mem_centralizer_iff.mpr fun d hd =>
      congrArg Subtype.val (hB.1.1.is_comm.comm ⟨d, hDB hd⟩ ⟨b, hb⟩)
  have hLines : ∀ D ∈ L, S < F D ∧ F D < Q ∧ B ≤ normalizer (F D : Set G) ∧
      B ⊓ centralizer (F D : Set G) = D ∧ IsPLocal 2 (normalizer (F D : Set G)) ∧
      normalizer (F D : Set G) < ⊤ ∧
      CFSG.Open.pRank p (normalizer (F D : Set G)) = GLATwoLocalRank p G := by
    intro D hD
    obtain ⟨hDA, hDcard, hSD⟩ := hLmem D hD
    have hDB : D ≤ B := hDA.trans hAB
    have hBN : B ≤ normalizer (F D : Set G) := fun b hb => by
      rw [hF]
      exact mem_normalizer_inf_of_mem' (hHQ (hBH hb)) (le_normalizer (hBcomm D hDB hb))
    have hF2 : IsPGroup 2 (F D) := hQ2.to_le (hFQ' D)
    have hFne : F D ≠ ⊥ := fun h => not_lt_bot (h ▸ hSD)
    have hloc : IsPLocal 2 (normalizer (F D : Set G)) := ⟨F D, hFne, hF2, rfl⟩
    have hCD : B ⊓ centralizer (F D : Set G) = D := by
      have hDle : D ≤ B ⊓ centralizer (F D : Set G) := by
        refine le_inf hDB (le_centralizer_iff.mp ?_)
        rw [hF]
        exact inf_le_right
      have hXA : B ⊓ centralizer (F D : Set G) ≤ A := by
        rw [hA]
        exact inf_le_inf_left B (centralizer_le (hSF D hDA))
      by_contra hne
      obtain ⟨i, hi, hXcard⟩ := (Nat.dvd_prime_pow hpp).mp (hAcard ▸ card_dvd_of_le hXA)
      have hpX : ¬ Nat.card (B ⊓ centralizer (F D : Set G) : Subgroup G) ≤ p := fun h =>
        hne (eq_of_le_of_card_ge hDle (h.trans hDcard.symm.le)).symm
      have hi2 : i = 2 := by
        interval_cases i
        · exact (hpX ((hXcard.trans (pow_zero p)).le.trans hpp.one_lt.le)).elim
        · exact (hpX (hXcard.trans (pow_one p)).le).elim
        · rfl
      rw [hi2] at hXcard
      have hfam : F D ∈ deltaSeededFamily p B S₀ :=
        ⟨hF2, hS₀S.trans hSD.le, hBN, two_le_pRank_of_plane hpp.one_lt le_rfl
          (isElemAbelian_of_le_elem inf_le_left hB.1) hXcard⟩
      exact not_le_of_gt hSD (hSmax hfam hSD.le)
    exact ⟨hSD, hFQ D hD, hBN, hCD, hloc,
      lt_top_iff_ne_top.mpr (CFSG.LargeEvenClassification.Helpers.twoLocal_ne_top G hnab _ hloc),
      hBrank.2 _ hloc hBN⟩
  have hDEinf : ∀ D ∈ L, ∀ E ∈ L, D ≠ E → F D ⊓ F E = S := by
    intro D hD E hE hDE
    obtain ⟨hDA, hDcard, -⟩ := hLmem D hD
    obtain ⟨hEA, hEcard, -⟩ := hLmem E hE
    have hDEA : D ⊔ E = A := by
      have hle : D ⊔ E ≤ A := sup_le hDA hEA
      have hne : D ≠ D ⊔ E := fun h =>
        hDE (eq_of_le_of_card_ge (le_sup_right.trans h.symm.le)
          (hDcard.trans hEcard.symm).le).symm
      obtain ⟨i, hi, hcard⟩ := (Nat.dvd_prime_pow hpp).mp (hAcard ▸ card_dvd_of_le hle)
      interval_cases i
      · exact (hne (eq_of_le_of_card_ge le_sup_left
          ((hcard.trans (pow_zero p)).le.trans (hpp.one_lt.le.trans hDcard.symm.le)))).elim
      · exact (hne (eq_of_le_of_card_ge le_sup_left
          ((hcard.trans (pow_one p)).le.trans hDcard.symm.le))).elim
      · exact eq_of_le_of_card_ge hle (hAcard.trans hcard.symm).le
    refine le_antisymm (fun x hx => ?_) (le_inf (hSF D hDA) (hSF E hEA))
    have hxD : x ∈ F D := (mem_inf.mp hx).1
    have hxE : x ∈ F E := (mem_inf.mp hx).2
    rw [hF] at hxD hxE
    rw [← hCQA]
    refine mem_inf.mpr ⟨(mem_inf.mp hxD).1, ?_⟩
    have h1 : D ⊔ E ≤ centralizer (zpowers x : Set G) :=
      sup_le (le_centralizer_iff.mp (zpowers_le.mpr (mem_inf.mp hxD).2))
        (le_centralizer_iff.mp (zpowers_le.mpr (mem_inf.mp hxE).2))
    rw [hDEA] at h1
    exact zpowers_le.mp (le_centralizer_iff.mp h1)
  have hSnQ : (S.subgroupOf Q).Normal :=
    (normal_subgroupOf_iff_le_normalizer hSQ).mpr (hQH.trans hHS)
  have hZR : (center S).map S.subtype ≤ R := hSR ▸ inf_le_right
  have hZS : (center S).map S.subtype ≤ S := map_subtype_le _
  have hZnR : (((center S).map S.subtype).subgroupOf R).Normal := by
    rw [normal_subgroupOf_iff hZR]
    intro z r hz hr
    have hzr : z * r = r * z := mem_centralizer_iff.mp (hRS hr) z (hZS hz)
    have h1 : r * z * r⁻¹ = z := by rw [← hzr, mul_inv_cancel_right]
    rw [h1]
    exact hz
  have hiso : ∃ e : R ⧸ ((center S).map S.subtype).subgroupOf R ≃* Q ⧸ S.subgroupOf Q,
      ∀ (r : R) (q : Q), (r : G) = q → e (QuotientGroup.mk r) = QuotientGroup.mk q := by
    set φ : R →* Q ⧸ S.subgroupOf Q :=
      (QuotientGroup.mk' (S.subgroupOf Q)).comp (inclusion hRQ) with hφ
    have hφs : Function.Surjective φ := by
      intro y
      obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective y
      obtain ⟨u, hu, s, hs, hq⟩ := hfacQ q q.2
      refine ⟨⟨u, hUR hu⟩, ?_⟩
      rw [hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, mem_subgroupOf]
      have h1 : (((inclusion hRQ ⟨u, hUR hu⟩)⁻¹ * q : Q) : G) = s := by
        rw [coe_mul, coe_inv, coe_inclusion, hq]
        group
      rw [h1]
      exact hs
    have hker : φ.ker = ((center S).map S.subtype).subgroupOf R := by
      ext r
      rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff, mem_subgroupOf, mem_subgroupOf, coe_inclusion, ← hSR]
      exact ⟨fun h => mem_inf.mpr ⟨h, r.2⟩, fun h => (mem_inf.mp h).1⟩
    refine ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφs), fun r q hrq => ?_⟩
    have h1 : inclusion hRQ r = q := Subtype.ext hrq
    show φ r = QuotientGroup.mk q
    rw [hφ, MonoidHom.comp_apply, h1, QuotientGroup.mk'_apply]
  have himage : ∀ D ∈ L, ∀ E ∈ L, D ≠ E →
      ((F D).subgroupOf Q).map (QuotientGroup.mk' (S.subgroupOf Q)) ⊓
        ((F E).subgroupOf Q).map (QuotientGroup.mk' (S.subgroupOf Q)) = ⊥ := by
    intro D hD E hE hDE
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨hz1, hz2⟩ := mem_inf.mp hz
    obtain ⟨x, hx, rfl⟩ := mem_map.mp hz1
    obtain ⟨y, hy, hyx⟩ := mem_map.mp hz2
    rw [mem_subgroupOf] at hx hy
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, mem_subgroupOf] at hyx
    rw [mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf,
      ← hDEinf D hD E hE hDE]
    refine mem_inf.mpr ⟨hx, ?_⟩
    have hxy : (x : G) = y * ((y⁻¹ * x : Q) : G) := by simp
    rw [hxy]
    exact mul_mem hy (hSF E (hLmem E hE).1 hyx)
  exact ⟨(normal_subgroupOf_iff_le_normalizer hRH).mpr hHR, hUR, hUA, hSUset, hSRset, hSUsup,
    hSRsup, commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hRS), hSR, hRA,
    hfaith, ⟨hSnQ, hZnR, hiso, himage⟩, hL2, hLp, hQsup, hLines, hDEinf, hBrank.1, hBrank.2,
    hBrank.2 H hHloc hBH, fun M hM => hBrank.2 M hM.1.1 fun b hb => hM.2 (hBH hb)⟩

end CFSG.LocalAnalysis.GorensteinLyons
