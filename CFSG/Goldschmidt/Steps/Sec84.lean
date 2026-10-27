module

public import CFSG.Goldschmidt.StatementsG3
import CFSG.Goldschmidt.Steps.Sec8Basic
import CFSG.Goldschmidt.Steps.Sec8Tools
import CFSG.Goldschmidt.Steps.Sec81a
import CFSG.Goldschmidt.Steps.Sec83a
import CFSG.Goldschmidt.Steps.Sec84b
import CFSG.Goldschmidt.Steps.Sec8Bender
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeAmbientCentralizerGeneration
import CFSG.Walter.Bender1970.S4.Rank
import CFSG.Walter.Bender1970.S38.JR
public import CFSG.Goldschmidt.StatementsG
public import CFSG.Goldschmidt.StatementsG2

public section

namespace CFSG.Goldschmidt

open CFSG.Open CFSG.GorensteinWalter

namespace Sec8

variable {G : Type} [Group G] [Finite G]

theorem commutator_mem_centralizer_fstar {K : Subgroup G} {x a : G} (hxK : x ∈ K)
    (ha2 : a * a = 1) (haE : componentLayerOf K ≤ Subgroup.centralizer ({a} : Set G))
    (hcore : ∀ s : ℕ, s.Prime → qCoreOf K s ≤ Subgroup.centralizer ({a} : Set G) ∨
      ∀ y ∈ qCoreOf K s, a * y * a⁻¹ = y⁻¹) :
    x * a * x⁻¹ * a⁻¹ ∈ Subgroup.centralizer (generalizedFittingSubgroupOf K : Set G) := by
  have hcK : ∀ N : Subgroup G, IsNormalIn N K → (N ≤ Subgroup.centralizer ({a} : Set G) ∨
      ∀ y ∈ N, a * y * a⁻¹ = y⁻¹) →
      N ≤ Subgroup.centralizer ({x * a * x⁻¹ * a⁻¹} : Set G) := by
    intro N hN hNa y hy
    have hxN := le_normalizer_of_isNormalIn hN hxK
    have hcy : x * a * x⁻¹ * a⁻¹ ∈ Subgroup.centralizer (N : Set G) := by
      rcases hNa with h | h
      · exact commutator_mem_centralizer_of_le hxN h
      · exact commutator_mem_centralizer_of_inv ha2 hxN h
    exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hcy y hy)
  have hle : generalizedFittingSubgroupOf K ≤
      Subgroup.centralizer ({x * a * x⁻¹ * a⁻¹} : Set G) := by
    refine sup_le ?_ (hcK _ (componentLayerOf_isNormalIn K) (Or.inl haE))
    rw [fittingSubgroupOf_eq_iSup_qCoreOf]
    exact iSup_le fun q => hcK _ (qCoreOf_normal_in K _)
      (hcore _ (Nat.prime_of_mem_primeFactors q.1.2))
  exact Subgroup.mem_centralizer_iff.mpr fun y hy =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hle hy))

omit [Finite G] in
theorem exists_commutator_eq {x a : G} (hodd : Odd (orderOf x))
    (hinv : ∀ k : ℕ, a * (x ^ k)⁻¹ * a⁻¹ = x ^ k) :
    ∃ m : ℕ, x ^ m * a * (x ^ m)⁻¹ * a⁻¹ = x := by
  obtain ⟨j, hj⟩ := hodd
  refine ⟨j + 1, ?_⟩
  have h1 : x ^ (j + 1) * a * (x ^ (j + 1))⁻¹ * a⁻¹ =
      x ^ (j + 1) * (a * (x ^ (j + 1))⁻¹ * a⁻¹) := by group
  rw [h1, hinv, ← pow_add]
  have : j + 1 + (j + 1) = orderOf x + 1 := by omega
  rw [this, pow_succ, pow_orderOf_eq_one, one_mul]

end Sec8

open Sec8 in
theorem G84_of (h64 : S_G64) (h31 : S_G31) (h37 : S_G37) (h83 : S_G83) : S_G84 := by
  intro G _ _ S A hset h4 a ha ha1 H hH V hVF hVp
  have hsimple := hset.isSimpleGroup
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set p := Nat.card V with hpdef
  have : Fact p.Prime := ⟨hVp⟩
  have hVpg : IsPGroup p V := IsPGroup.of_card (n := 1) (by rw [pow_one])
  have hV1 : V ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hpdef
    exact Nat.not_prime_one (hpdef ▸ hVp)
  by_contra hNV
  have hNtop : Subgroup.normalizer (V : Set G) ≠ ⊤ := fun htop => by
    have : V.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal V with h | h
    · exact hV1 h
    · obtain ⟨x, y, hxy⟩ := hset.nonabelian
      have hcard : Nat.card G = p := by rw [hpdef, h, Subgroup.card_top]
      have := isCyclic_of_prime_card hcard
      exact hxy (IsCyclic.commGroup.mul_comm x y)
  obtain ⟨M, hM, hVM⟩ := (IsCoatomic.eq_top_or_exists_le_coatom
    (Subgroup.normalizer (V : Set G))).resolve_left hNtop
  have hMH : M ≠ H := fun h => hNV (h ▸ hVM)
  have haF := not_mem_fstar h64 h31 h37 h83 hset h4 ha ha1 hH hVF hVp hM hVM hMH
  obtain ⟨ha2H, hHa⟩ := mem_qCoreOf_two_and_eq h64 hset h4 ha ha1 hH
  have hHco := Walter.isCoatom_of_mem_benderM hH
  have hVO : V ≤ qCoreOf H p := Walter.le_qCoreOf_of_le_fittingSubgroupOf hVp hVF hVpg
  have hAM : A ≤ M := (le_normalizer_of_le_qCoreOf h83 hset h4 ha ha1 hH hVp hVO).trans hVM
  have hS := sstar_of_le hset hM.1 hAM
  have haM : a ∈ M := hAM ha
  have ha2 : a * a = 1 := mul_self_eq_one hset.elem ha
  set Q := normalClosureIn M A with hQ
  have hQM : IsNormalIn Q M :=
    ⟨normalClosureIn_le_self M A, fun h hh k hk =>
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_normalClosureIn M A hh) k).mp hk⟩
  have hOFQ : oddCoreOf (CFSG.fittingSubgroupOf Q) ≤ CFSG.fittingSubgroupOf M :=
    ((oddCoreOf_le _).trans (Walter.fittingSubgroupOf_le_of_isSubnormal hQM.1
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hQM.1).mpr
        (le_normalizer_of_isNormalIn hQM)).isSubnormal))
  obtain ⟨r, hr, hrO⟩ : ∃ r : ℕ, r.Prime ∧
      ¬ qCoreOf M r ≤ Subgroup.centralizer ({a} : Set G) := by
    by_contra hall
    simp only [not_exists, not_and, not_not] at hall
    apply haF
    refine (h31 G M A hS).2 ⟨le_normalClosureIn hAM ha, ?_⟩
    have hFa : CFSG.fittingSubgroupOf M ≤ Subgroup.centralizer ({a} : Set G) := by
      rw [(show CFSG.fittingSubgroupOf M = _ from CFSG.GorensteinWalter.fittingSubgroupOf_eq_iSup_qCoreOf M)]
      exact iSup_le fun q => hall _ (Nat.prime_of_mem_primeFactors q.1.2)
    exact Subgroup.mem_centralizer_iff.mpr fun y hy =>
      Subgroup.mem_centralizer_singleton_iff.mp (hFa (hOFQ hy))
  have hPle : V ≤ qCoreOf H p := hVO
  have hrπ : r ∉ primesOfOrder (CFSG.fittingSubgroupOf H) := fun hrπ =>
    hrO (hHa ▸ qCoreOf_le_of_mem hsimple hHco hVp hPle hVM hr hrπ
      (pResidualOf_ne_bot h64 hset h4 ha ha1 hH hr))
  have h2π : 2 ∈ primesOfOrder (CFSG.fittingSubgroupOf H) :=
    mem_primesOfOrder_fitting Nat.prime_two (Subgroup.zpowers_le.mpr ha2H)
      (fun h => ha1 (Subgroup.zpowers_eq_bot.mp h))
  have hr2 : r ≠ 2 := fun h => hrπ (h ▸ h2π)
  have hrM := le_normalizer_of_isNormalIn (qCoreOf_normal_in M r)
  have hinv : ∀ y ∈ qCoreOf M r, a * y * a⁻¹ = y⁻¹ := fun y hy =>
    inv_of_inf_eq_bot ha2 (hrM haM) (hHa ▸ qCoreOf_inf_eq_bot hsimple hHco hVp hPle hVM hr hrπ)
      hy
  have : Fact r.Prime := ⟨hr⟩
  have hgen := RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane 2
    Nat.prime_two A (qCoreOf M r) (fun x => Subtype.ext (hset.elem.2 x x.2))
    (by rw [h4]; norm_num) (by
      obtain ⟨k, hk⟩ := (qCoreOf_isPGroup M r).exists_card_eq
      rw [hk]
      intro h
      exact hr2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hr).mp
        (Nat.prime_two.dvd_of_dvd_pow h)).symm) (hAM.trans hrM)
  have hOr1 : qCoreOf M r ≠ ⊥ := fun h => hrO (h ▸ bot_le)
  obtain ⟨a₁, ha₁A, ha₁1, hQ₀⟩ : ∃ a₁ ∈ A, a₁ ≠ 1 ∧
      qCoreOf M r ⊓ Subgroup.centralizer ({a₁} : Set G) ≠ ⊥ := by
    by_contra hno
    simp only [not_exists, not_and, not_not] at hno
    apply hOr1
    rw [hgen]
    exact le_bot_iff.mp (iSup₂_le fun b hb => (hno b b.2 fun h => hb (Subtype.ext h)).le)
  have hOrH : qCoreOf M r ⊓ H = ⊥ := qCoreOf_inf_eq_bot hsimple hHco hVp hPle hVM hr hrπ
  have ha₁a : a₁ ≠ a := by
    rintro rfl
    exact hQ₀ (le_bot_iff.mp (hOrH ▸ inf_le_inf_left _ (hHa ▸ le_rfl)))
  set H₁ := Subgroup.centralizer ({a₁} : Set G) with hH₁def
  have hH₁ := centralizer_mem_benderM hset h4 ha ha1 ha₁A ha₁1 hH hHa
  obtain ⟨h83a, h83E⟩ := h83 G S A hset h4 a₁ ha₁A ha₁1 H₁ hH₁
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hEa : componentLayerOf H₁ ≤ Subgroup.centralizer ({a} : Set G) :=
    (Subgroup.le_centralizer_iff.mp (Subgroup.le_centralizer_iff.mpr
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h83E))).trans
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ha))
  have hcoreH₁ : ∀ s : ℕ, s.Prime → qCoreOf H₁ s ≤ Subgroup.centralizer ({a} : Set G) ∨
      ∀ y ∈ qCoreOf H₁ s, a * y * a⁻¹ = y⁻¹ := by
    intro s hs
    rcases h83a a ha ha1 s hs with h | h
    · refine Or.inl fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr ?_
      calc y * a = a * (a⁻¹ * y * a) := by group
        _ = a * y := by rw [h y hy]
    · refine Or.inr fun y hy => ?_
      have := h y hy
      rw [hai] at this ⊢
      exact this
  have hOrodd : Odd (Nat.card (qCoreOf M r)) := by
    obtain ⟨k, hk⟩ := (qCoreOf_isPGroup M r).exists_card_eq
    rw [hk]
    exact (hr.odd_of_ne_two hr2).pow
  have hQ₀F : qCoreOf M r ⊓ Subgroup.centralizer ({a₁} : Set G) ≤
      CFSG.fittingSubgroupOf H₁ := by
    intro x hx
    have hxH₁ : x ∈ H₁ := hx.2
    have hxodd : Odd (orderOf x) := by
      have := orderOf_dvd_natCard (⟨x, hx.1⟩ : qCoreOf M r)
      rw [Subgroup.orderOf_mk] at this
      exact hOrodd.of_dvd_nat this
    obtain ⟨m, hm⟩ := exists_commutator_eq hxodd fun k => by
      rw [hinv _ (Subgroup.inv_mem _ (Subgroup.pow_mem _ hx.1 k)), inv_inv]
    have hc := commutator_mem_centralizer_fstar (K := H₁) (Subgroup.pow_mem _ hxH₁ m) ha2 hEa
      hcoreH₁
    rw [hm] at hc
    have hxF : x ∈ generalizedFittingSubgroupOf H₁ :=
      Walter.inf_centralizer_generalizedFitting_le H₁ ⟨hxH₁, hc⟩
    exact Walter.generalizedFittingSubgroupOf_inf_centralizer_le H₁
      ⟨hxF, Subgroup.centralizer_le (le_sup_right : componentLayerOf H₁ ≤ _) hc⟩
  have hQ₀O : qCoreOf M r ⊓ Subgroup.centralizer ({a₁} : Set G) ≤ qCoreOf H₁ r :=
    Walter.le_qCoreOf_of_le_fittingSubgroupOf hr hQ₀F ((qCoreOf_isPGroup M r).to_le inf_le_left)
  have hrπ₁ := mem_primesOfOrder_fitting hr hQ₀O hQ₀
  obtain ⟨n, -, hn⟩ := exists_conj_eq hset h4 ha ha₁A ha1 ha₁1
  have hH₁H : H₁ = H.map (MulAut.conj n).toMonoidHom := by
    rw [hH₁def, ← hn, ← Walter.map_conj_centralizer_singleton, ← hHa]
  have hcardF : Nat.card (CFSG.fittingSubgroupOf H₁) = Nat.card (CFSG.fittingSubgroupOf H) := by
    rw [hH₁H, Walter.fittingSubgroupOf_map_conj,
      Subgroup.card_map_of_injective (MulAut.conj n).injective]
  apply hrπ
  have h1 : r ∈ (Nat.card (CFSG.fittingSubgroupOf H₁)).primeFactors := hrπ₁
  rw [hcardF] at h1
  exact h1

end CFSG.Goldschmidt
