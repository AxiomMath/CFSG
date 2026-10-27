module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig.J2Elts
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig.A7
public import CFSG.Quasithin.Vol2.KGFactC31RuRef
public import CFSG.Foundations
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.B2Thompson
public import CFSG.Quasithin.Vol2.KGFactC31RuRefBase
public import CFSG.RankThree.PartTwo.NotationBlocks
public import CFSG.RankThree.PartTwo.Sec14.Item148Res7ProofSig
public import CFSG.RankThree.PartTwo.Sec8.Pairs
public import CFSG.RankThree.PartTwo.Sec8.Statements
public import CFSG.Sporadic.HeldB.Common
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.Sporadic.Schreier.RuPair
public import CFSG.Sporadic.Schreier.RuSylow
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43
public import Certificates.Certificate7233Base

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig.J2

open Subgroup CFSG.ComponentClassification.J2Cover CFSG.Certificates.Native
  CFSG.Monster.B.Co2.Native CFSG.RankThree.Native CFSG.RankThree.PartTwo.Sec4.Sporadic.J2
  CFSG.Monster.B.Fischer CFSG.Monster.B.Mathieu CFSG.Monster.B.Co2 CFSG.GH74.GLS

set_option linter.unusedSectionVars false


@[expose] noncomputable def evalG (f : ℕ → GJ) (w : List ℕ) : GJ :=
  w.foldl (fun g i => g * f i) 1

theorem rep_foldl {L : Array (Array ℕ)} {f : ℕ → GJ} :
    ∀ (w : List ℕ), (∀ i ∈ w, Rep 315 L[i]! (f i).1) → ∀ {acc : Array ℕ} {g : GJ},
      Rep 315 acc g.1 → Rep 315 (w.foldl (fun acc i => compA 315 acc L[i]!) acc)
        (w.foldl (fun g i => g * f i) g).1
  | [], _, _, _, h => h
  | i :: w, hw, _, _, h => by
    simp only [List.foldl_cons]
    exact rep_foldl w (fun j hj => hw j (List.mem_cons_of_mem _ hj))
      (rep_mul h (hw i List.mem_cons_self))

theorem rep_evalG {L : Array (Array ℕ)} {f : ℕ → GJ} {w : List ℕ}
    (hw : ∀ i ∈ w, Rep 315 L[i]! (f i).1) : Rep 315 (evalA L w) (evalG f w).1 :=
  rep_foldl w hw rep_one

theorem foldl_mem {H : Subgroup GJ} {f : ℕ → GJ} :
    ∀ (w : List ℕ), (∀ i ∈ w, f i ∈ H) → ∀ {g : GJ}, g ∈ H →
      w.foldl (fun g i => g * f i) g ∈ H
  | [], _, _, h => h
  | i :: w, hw, _, h => by
    simp only [List.foldl_cons]
    exact foldl_mem w (fun j hj => hw j (List.mem_cons_of_mem _ hj))
      (H.mul_mem h (hw i List.mem_cons_self))

theorem evalG_mem {H : Subgroup GJ} {f : ℕ → GJ} {w : List ℕ} (hw : ∀ i ∈ w, f i ∈ H) :
    evalG f w ∈ H :=
  foldl_mem w hw H.one_mem

theorem witWords_lt : ∀ w ∈ witWords, ∀ i ∈ w, i < 3 := by decide

theorem not_three_dvd_orderOf {G : Type*} [Group G] [Finite G] {H : Subgroup G} {u : G}
    (hu : u ∈ pPrimeCoreOf 3 H) : ¬ 3 ∣ orderOf u := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨c, hc, rfl⟩ := hu
  show ¬ 3 ∣ orderOf (c : G)
  rw [Subgroup.orderOf_coe]
  have h1 : orderOf c = orderOf (⟨c, hc⟩ : CFSG.pPrimeCore 3 H) := (Subgroup.orderOf_mk c hc).symm
  rw [h1]
  intro h3
  have h2 := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1
    (CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥H))
  exact h2 (h3.trans (orderOf_dvd_natCard _))

theorem mem_of_mem_pPrimeCoreOf {G : Type*} [Group G] {H : Subgroup G} {u : G}
    (hu : u ∈ pPrimeCoreOf 3 H) : u ∈ H := by
  obtain ⟨c, -, rfl⟩ := hu
  exact c.2

theorem dvd_twenty_of_dvd_sixty {n : ℕ} (h60 : n ∣ 60) (h3 : ¬ 3 ∣ n) : n ∣ 20 := by
  have hn : n ≤ 60 := Nat.le_of_dvd (by norm_num) h60
  revert h60 h3
  interval_cases n <;> decide

theorem core_w {K : Subgroup GJ} {k : ℕ} (hk : k < 3) {u : GJ}
    (hu : u ∈ pPrimeCoreOf 3 (K ⊓ centralizer ({wJ k} : Set GJ))) :
    u = 1 ∨ ∃ p < 3, u = tJ (3 * k + p) := by
  have hm := mem_inf.1 (mem_of_mem_pPrimeCoreOf hu)
  exact cent_w hk (mem_centralizer_singleton_iff.1 hm.2) (not_three_dvd_orderOf hu)

theorem not_mem_core_of_cube {H : Subgroup GJ} {v : GJ} (hv : v ∈ pPrimeCoreOf 3 H)
    (h3 : v ^ 3 = 1) (h1 : v ≠ 1) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact not_three_dvd_orderOf hv (by rw [orderOf_eq_prime h3 h1])

theorem core_z {K : Subgroup GJ} {u : GJ}
    (hU : ∀ v ∈ pPrimeCoreOf 3 (K ⊓ centralizer ({zJ} : Set GJ)),
      xJ * v * xJ⁻¹ ∈ pPrimeCoreOf 3 (K ⊓ centralizer ({zJ} : Set GJ)))
    (hu : u ∈ pPrimeCoreOf 3 (K ⊓ centralizer ({zJ} : Set GJ))) :
    u = 1 ∨ ∃ j, 3 ≤ j ∧ j < 6 ∧ ∃ p < 3, u = tJ (3 * j + p) := by
  set U := pPrimeCoreOf 3 (K ⊓ centralizer ({zJ} : Set GJ)) with hUdef
  have hm := mem_inf.1 (mem_of_mem_pPrimeCoreOf hu)
  rcases cent_z (mem_centralizer_singleton_iff.1 hm.2) (not_three_dvd_orderOf hu) with
    h | h | ⟨v, hv, hv3⟩
  · exact Or.inl h
  · exact Or.inr h
  · exfalso
    have hx1 : xJ * u * xJ⁻¹ ∈ U := hU u hu
    have hx2 : (xJ * xJ) * u * (xJ * xJ)⁻¹ ∈ U := by
      have := hU _ hx1
      convert this using 1
      group
    have hle : Subgroup.closure ({u, xJ * u * xJ⁻¹, (xJ * xJ) * u * (xJ * xJ)⁻¹} : Set GJ) ≤ U := by
      rw [closure_le]
      rintro _ (rfl | rfl | rfl)
      · exact hu
      · exact hx1
      · exact hx2
    exact not_three_dvd_orderOf (hle hv) (by rw [hv3])

theorem all_mem {H : Subgroup GJ} {j p : ℕ} (hj : j < 6) (hp : p < 3)
    (hN : actJ j ∈ normalizer (H : Set GJ)) (h : tJ (3 * j + p) ∈ H) :
    ∀ q < 3, tJ (3 * j + q) ∈ H := by
  intro q hq
  obtain ⟨e, -, he⟩ := orb_spec hj hp hq
  rw [← he]
  exact (mem_normalizer_iff.1 (pow_mem hN e) _).1 h

theorem two_of_pair {H : Subgroup GJ} (hH : ∀ v ∈ H, ¬ (v ^ 3 = 1 ∧ v ≠ 1)) {p q : ℕ}
    (hpq : (p, q) ∈ pairA) (hp : p < 18) (hq : q < 18) (hpH : tJ p ∈ H) (hqH : tJ q ∈ H) :
    False :=
  hH _ (H.mul_mem hpH hqH) (pair_spec hpq hp hq)

theorem core_z_single {K : Subgroup GJ}
    (hU : ∀ v ∈ pPrimeCoreOf 3 (K ⊓ centralizer ({zJ} : Set GJ)),
      xJ * v * xJ⁻¹ ∈ pPrimeCoreOf 3 (K ⊓ centralizer ({zJ} : Set GJ))) :
    ∃ j, 3 ≤ j ∧ j < 6 ∧ ∀ u ∈ pPrimeCoreOf 3 (K ⊓ centralizer ({zJ} : Set GJ)),
      u = 1 ∨ ∃ p < 3, u = tJ (3 * j + p) := by
  set U := pPrimeCoreOf 3 (K ⊓ centralizer ({zJ} : Set GJ)) with hUdef
  have hN : ∀ j, 3 ≤ j → actJ j ∈ normalizer (U : Set GJ) := by
    intro j hj
    have : actJ j = xJ := by simp [actJ, show ¬ j < 3 by omega]
    rw [this, mem_normalizer_iff]
    intro v
    refine ⟨fun hv => hU v hv, fun hv => ?_⟩
    have h1 := hU _ hv
    have h2 := hU _ h1
    have e : xJ * (xJ * (xJ * v * xJ⁻¹) * xJ⁻¹) * xJ⁻¹ =
        (xJ * xJ * xJ) * v * (xJ * xJ * xJ)⁻¹ := by group
    rw [e, ← pow_three', x_cube] at h2
    simpa using h2
  have hH : ∀ v ∈ U, ¬ (v ^ 3 = 1 ∧ v ≠ 1) := fun v hv h => not_mem_core_of_cube hv h.1 h.2
  by_cases h0 : ∀ u ∈ U, u = 1
  · exact ⟨3, le_refl _, by norm_num, fun u hu => Or.inl (h0 u hu)⟩
  obtain ⟨u0, hu0, hu01⟩ : ∃ u ∈ U, u ≠ 1 := by
    by_contra hc
    exact h0 fun u hu => by_contra fun hne => hc ⟨u, hu, hne⟩
  rcases core_z hU hu0 with h | ⟨j0, hj0, hj06, p0, hp0, rfl⟩
  · exact absurd h hu01
  refine ⟨j0, hj0, hj06, fun u hu => ?_⟩
  rcases core_z hU hu with h | ⟨j, hj, hj6, p, hp, rfl⟩
  · exact Or.inl h
  · right
    by_contra hne
    have hjj : j ≠ j0 := fun h => hne ⟨p, hp, by rw [h]⟩
    have hA := all_mem (by omega) hp0 (hN j0 hj0) hu0
    have hB := all_mem (by omega) hp (hN j hj) hu
    have m1 : ((9 : ℕ), (14 : ℕ)) ∈ pairA := by simp [pairA]
    have m2 : ((9 : ℕ), (17 : ℕ)) ∈ pairA := by simp [pairA]
    have m3 : ((12 : ℕ), (16 : ℕ)) ∈ pairA := by simp [pairA]
    have hj0' : j0 = 3 ∨ j0 = 4 ∨ j0 = 5 := by omega
    have hj' : j = 3 ∨ j = 4 ∨ j = 5 := by omega
    rcases hj0' with rfl | rfl | rfl <;> rcases hj' with rfl | rfl | rfl
    · exact hjj rfl
    · exact two_of_pair hH m1 (by norm_num) (by norm_num) (hA 0 (by norm_num)) (hB 2 (by norm_num))
    · exact two_of_pair hH m2 (by norm_num) (by norm_num) (hA 0 (by norm_num)) (hB 2 (by norm_num))
    · exact two_of_pair hH m1 (by norm_num) (by norm_num) (hB 0 (by norm_num)) (hA 2 (by norm_num))
    · exact hjj rfl
    · exact two_of_pair hH m3 (by norm_num) (by norm_num) (hA 0 (by norm_num)) (hB 1 (by norm_num))
    · exact two_of_pair hH m2 (by norm_num) (by norm_num) (hB 0 (by norm_num)) (hA 2 (by norm_num))
    · exact two_of_pair hH m3 (by norm_num) (by norm_num) (hB 0 (by norm_num)) (hA 1 (by norm_num))
    · exact hjj rfl

theorem genSets_lt {s : ℕ} (hs : s < 4) : ∀ j ∈ genSets.getD s [], j < 6 := by
  interval_cases s <;> decide

theorem eq_top_of_gen {K : Subgroup GJ} {s : ℕ} (hs : s < 4)
    (hK : ∀ j ∈ genSets.getD s [], ∀ q < 3, tJ (3 * j + q) ∈ K) : K = ⊤ :=
  gen_spec hs hK

theorem twoSets_lt {s : ℕ} (hs : s < 6) : ∀ j ∈ twoSets.getD s [], j < 6 := by
  interval_cases s <;> decide

theorem mem_twoGens {s : ℕ} {t : Array ℕ} (ht : t ∈ (twoGens s).toList) :
    ∃ j ∈ twoSets.getD s [], ∃ p < 3, t = vA[3 * j + p]! := by
  unfold twoGens at ht
  rw [List.toList_toArray, List.mem_flatMap] at ht
  obtain ⟨j, hj, ht⟩ := ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · exact ⟨j, hj, 0, by norm_num, by simp⟩
  · exact ⟨j, hj, 1, by norm_num, rfl⟩
  · exact ⟨j, hj, 2, by norm_num, rfl⟩

theorem tJ_mem_two {s : ℕ} (_hs : s < 6) {j p : ℕ} (hj : j ∈ twoSets.getD s []) (hp : p < 3) :
    tJ (3 * j + p) ∈ S2 s :=
  Subgroup.subset_closure ⟨j, hj, p, hp, rfl⟩

theorem false_of_le_two {K : Subgroup GJ} (hKp : Group.IsPerfect K) (hK1 : K ≠ ⊥) {s : ℕ}
    (hs : s < 6) (hle : K ≤ S2 s) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card (S2 s) = 2 ^ 6 := by
    rw [card_S2 hs]
    norm_num
  have hT : IsPGroup 2 (S2 s) := IsPGroup.of_card hcard
  have hK : IsPGroup 2 K := hT.to_le hle
  have : Nontrivial K := (nontrivial_iff_ne_bot K).2 hK1
  exact Group.IsPerfect.not_isNilpotent K hK.isNilpotent

end CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig.J2
