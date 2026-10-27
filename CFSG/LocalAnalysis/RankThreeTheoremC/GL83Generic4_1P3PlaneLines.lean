module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3PlaneCount
import CFSG.LocalAnalysis.RankFourTheoremC.PPointPlane
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3U3Lemma42

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

theorem isLargeObstruction_of_mem_zpowers {M : Subgroup G} {a b : G}
    (ha : IsLargeObstruction 3 M a) (hb : b ∈ zpowers a) (hb1 : b ≠ 1) :
    IsLargeObstruction 3 M b := by
  rcases eq_or_eq_inv_of_mem_zpowers ha.2.2.1 (mem_zpowers a) hb ha.2.1 hb1 with rfl | rfl
  · exact ha
  · exact isLargeObstruction_inv ha

omit [Finite G] in
theorem zpowers_ne_of_not_mem {u v : G} (h : v ∉ zpowers u) : zpowers u ≠ zpowers v :=
  fun heq => h (by rw [heq]; exact mem_zpowers v)

theorem exists_not_mem_three_lines {D : Subgroup G} (hDc : Nat.card D = 3 ^ 2) {a b c : G}
    (ha : Nat.card (zpowers a) = 3) (hb : Nat.card (zpowers b) = 3)
    (hc : Nat.card (zpowers c) = 3) :
    ∃ z ∈ D, z ∉ zpowers a ∧ z ∉ zpowers b ∧ z ∉ zpowers c := by
  classical
  have : Fintype G := Fintype.ofFinite G
  by_contra hno
  push Not at hno
  let s : Subgroup G → Finset G := fun L => (Finset.univ.filter (· ∈ L)).erase 1
  have hcardfilter : ∀ L : Subgroup G, (Finset.univ.filter (· ∈ L)).card = Nat.card L := by
    intro L
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hscard : ∀ L : Subgroup G, (s L).card = Nat.card L - 1 := by
    intro L
    simp only [s]
    rw [Finset.card_erase_of_mem (by simp [one_mem]), hcardfilter]
  have hsub : s D ⊆ s (zpowers a) ∪ s (zpowers b) ∪ s (zpowers c) := by
    intro y hy
    simp only [s, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union] at hy ⊢
    obtain ⟨hy1, hyD⟩ := hy
    by_cases hya : y ∈ zpowers a
    · exact Or.inl (Or.inl ⟨hy1, hya⟩)
    by_cases hyb : y ∈ zpowers b
    · exact Or.inl (Or.inr ⟨hy1, hyb⟩)
    exact Or.inr ⟨hy1, hno y hyD hya hyb⟩
  have hle := Finset.card_le_card hsub
  have h1 := Finset.card_union_le (s (zpowers a) ∪ s (zpowers b)) (s (zpowers c))
  have h2 := Finset.card_union_le (s (zpowers a)) (s (zpowers b))
  have e0 := hscard D
  have e1 := hscard (zpowers a)
  have e2 := hscard (zpowers b)
  have e3 := hscard (zpowers c)
  rw [hDc] at e0
  rw [ha] at e1
  rw [hb] at e2
  rw [hc] at e3
  omega

theorem false_of_three_lines (hS : Setting G) (hU0 : FullCoreLocal G) (hD1 : TheoremD1 G)
    (K1 : StronglyEmbeddedRankTwoKFactNoBM) (K2 : StronglyEmbeddedCyclicOuterKFact)
    (K3 : KFactOutCyclic) (K4 : KFactComponentPCoreThree) (hno : NoExcludedSection3 G)
    (hKM : CFSG.AGLEmbeddingD2.KFactM11Three) (hKA : KFactM11TwoSignalizer)
    (hL : KFactsL34Full) (hA1 : A6SylowData) (hA3 : A6BorelCore) (hE1 : KFactL28Three)
    (hE3 : KFactL28BorelCore) (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} {M : Subgroup G}
    (hM : IsCoreMaxLocal 3 P M) {D : Subgroup G} (hDM : D ≤ M) (hDel : IsElemAbelian 3 D)
    (hDc : Nat.card D = 3 ^ 2) {a b c : G} (ha : a ∈ D) (hb : b ∈ D) (hc : c ∈ D) (ha1 : a ≠ 1)
    (hb1 : b ≠ 1) (hc1 : c ≠ 1) (hab : zpowers a ≠ zpowers b) (hac : zpowers a ≠ zpowers c)
    (hbc : zpowers b ≠ zpowers c) (hLa : IsLargeObstruction 3 M a)
    (hLb : IsLargeObstruction 3 M b) (hLc : IsLargeObstruction 3 M c) : False := by
  classical
  have hline : ∀ y ∈ D, y ≠ 1 → Nat.card (zpowers y) = 3 := fun y hy hy1 =>
    CFSG.LocalAnalysis.RankFourTheoremC.card_zpowers_of_isElemAbelian Nat.prime_three hDel hy hy1
  obtain ⟨z, hzD, hza, hzb, hzc⟩ :=
    exists_not_mem_three_lines hDc (hline a ha ha1) (hline b hb hb1) (hline c hc hc1)
  have hz1 : z ≠ 1 := fun h => hza (h ▸ one_mem _)
  refine false_of_plane_lines hS hU0 hD1 K1 K2 K3 K4 hno hKM hKA hL hA1 hA3 hE1 hE3 hp hM hDM
    hDel hDc hzD hz1 fun y hyD hyz => ?_
  have hy1 : y ≠ 1 := fun h => hyz (h ▸ one_mem _)
  have hcover : y ∈ zpowers a ∨ y ∈ zpowers b ∨ y ∈ zpowers c := by
    by_contra hcon
    push Not at hcon
    obtain ⟨hya, hyb, hyc⟩ := hcon
    have hcard := CFSG.LocalAnalysis.RankFourTheoremC.card_lines_le Nat.prime_three hDc
      ({zpowers a, zpowers b, zpowers c, zpowers z, zpowers y} : Finset (Subgroup G)) (by
        intro L hL'
        simp only [Finset.mem_insert, Finset.mem_singleton] at hL'
        rcases hL' with rfl | rfl | rfl | rfl | rfl
        · exact ⟨zpowers_le.mpr ha, hline a ha ha1⟩
        · exact ⟨zpowers_le.mpr hb, hline b hb hb1⟩
        · exact ⟨zpowers_le.mpr hc, hline c hc hc1⟩
        · exact ⟨zpowers_le.mpr hzD, hline z hzD hz1⟩
        · exact ⟨zpowers_le.mpr hyD, hline y hyD hy1⟩)
    have haz := zpowers_ne_of_not_mem hza
    have hbz := zpowers_ne_of_not_mem hzb
    have hcz := zpowers_ne_of_not_mem hzc
    have hay := zpowers_ne_of_not_mem hya
    have hby := zpowers_ne_of_not_mem hyb
    have hcy := zpowers_ne_of_not_mem hyc
    have hzy := zpowers_ne_of_not_mem hyz
    rw [Finset.card_insert_of_notMem (by simp [hab, hac, haz, hay]),
      Finset.card_insert_of_notMem (by simp [hbc, hbz, hby]),
      Finset.card_insert_of_notMem (by simp [hcz, hcy]),
      Finset.card_insert_of_notMem (by simp [hzy]), Finset.card_singleton] at hcard
    omega
  rcases hcover with h | h | h
  · exact isLargeObstruction_of_mem_zpowers hLa h hy1
  · exact isLargeObstruction_of_mem_zpowers hLb h hy1
  · exact isLargeObstruction_of_mem_zpowers hLc h hy1

omit [Finite G] in
theorem eq_one_of_mul_self_eq_one_of_pow_three {t : G} (h2 : t * t = 1) (h3 : t ^ 3 = 1) :
    t = 1 := by
  calc t = t ^ 3 := by rw [pow_three, h2, mul_one]
    _ = 1 := h3

theorem plane_zpowers_sup {x k : G} (hx3 : x ^ 3 = 1) (hk1 : k ≠ 1) (hk3 : k ^ 3 = 1)
    (hxk : x ∉ zpowers k) (hkx : k * x = x * k) :
    IsElemAbelian 3 (zpowers k ⊔ zpowers x) ∧ Nat.card ↥(zpowers k ⊔ zpowers x) = 3 ^ 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hkx' : ∀ e ∈ zpowers k, e * x = x * e := fun e he => by
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp he
    exact (Commute.zpow_left (show Commute k x from hkx) j).eq
  refine ⟨CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_sup_of_commuting 3
      (CFSG.AGLEmbedding.isElemAbelian_zpowers hk3)
      (CFSG.AGLEmbedding.isElemAbelian_zpowers hx3) (fun e he => by
        rw [mem_centralizer_iff]
        intro a ha
        obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp ha
        exact ((Commute.zpow_right (show Commute e x from hkx' e he) j).eq).symm), ?_⟩
  rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers Nat.prime_three (zpowers k) hx3 hxk hkx',
    Nat.card_zpowers, orderOf_eq_prime hk3 hk1]
  norm_num

theorem false_of_mixed_pair (hS : Setting G) (hU0 : FullCoreLocal G) (hD1 : TheoremD1 G)
    (K1 : StronglyEmbeddedRankTwoKFactNoBM) (K2 : StronglyEmbeddedCyclicOuterKFact)
    (K3 : KFactOutCyclic) (K4 : KFactComponentPCoreThree) (hno : NoExcludedSection3 G)
    (hKM : CFSG.AGLEmbeddingD2.KFactM11Three) (hKA : KFactM11TwoSignalizer)
    (hL : KFactsL34Full) (hA1 : A6SylowData) (hA3 : A6BorelCore) (hE1 : KFactL28Three)
    (hE3 : KFactL28BorelCore) (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} {M : Subgroup G}
    (hM : IsCoreMaxLocal 3 P M) {x k n : G} (hxLO : IsLargeObstruction 3 M x) (hkM : k ∈ M)
    (hk1 : k ≠ 1) (hk3 : k ^ 3 = 1) (hxk : x ∉ zpowers k) (hkx : k * x = x * k) (hnM : n ∈ M)
    (hnx : n * x * n⁻¹ = x) (hnk : n * k * n⁻¹ = k⁻¹) {y : G} (hy : y ∈ zpowers k ⊔ zpowers x)
    (hyk : y ∉ zpowers k) (hyx : y ∉ zpowers x) (hyLO : IsLargeObstruction 3 M y) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hxM, hx1, hx3, -, -⟩ := id hxLO
  obtain ⟨hDel, hDc⟩ := plane_zpowers_sup hx3 hk1 hk3 hxk hkx
  have hDM : zpowers k ⊔ zpowers x ≤ M := sup_le (zpowers_le.mpr hkM) (zpowers_le.mpr hxM)
  have hKz : ∀ t ∈ zpowers k, ∀ c ∈ zpowers x, t * c = c * t := fun t ht c hc => by
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hc
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ht
    exact (Commute.zpow_zpow (show Commute k x from hkx) i j).eq
  obtain ⟨t, ht, c, hc, rfl⟩ := u3l42_decomp hKz hy
  have ht1 : t ≠ 1 := by
    rintro rfl
    exact hyx (by simpa using hc)
  have hc1 : c ≠ 1 := by
    rintro rfl
    exact hyk (by simpa using ht)
  have hnt : n * t * n⁻¹ = t⁻¹ := by
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ht
    have h := map_zpow (MulAut.conj n) k i
    simp only [MulAut.conj_apply] at h
    rw [h, hnk, inv_zpow]
  have hnc : n * c * n⁻¹ = c := by
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hc
    have h := map_zpow (MulAut.conj n) x j
    simp only [MulAut.conj_apply] at h
    rw [h, hnx]
  have hy' : IsLargeObstruction 3 M (t⁻¹ * c) := by
    have h := hyLO.conj hnM
    rw [MulAut.conj_apply] at h
    have h' : n * (t * c) * n⁻¹ = t⁻¹ * c := by
      rw [show n * (t * c) * n⁻¹ = (n * t * n⁻¹) * (n * c * n⁻¹) by group, hnt, hnc]
    rwa [h'] at h
  have htc : t * c = c * t := hKz t ht c hc
  have htD : t ∈ zpowers k ⊔ zpowers x := Subgroup.mem_sup_left ht
  have hcD : c ∈ zpowers k ⊔ zpowers x := Subgroup.mem_sup_right hc
  have hyD : t * c ∈ zpowers k ⊔ zpowers x := Subgroup.mul_mem _ htD hcD
  have hy'D : t⁻¹ * c ∈ zpowers k ⊔ zpowers x := Subgroup.mul_mem _ (Subgroup.inv_mem _ htD) hcD
  have hty3 : (t * c) ^ 3 = 1 := hDel.2 _ hyD
  have hy'1 : t⁻¹ * c ≠ 1 := hy'.2.1
  have hxy' : t⁻¹ * c ∉ zpowers x := fun h => hyx (by
    have h1 : t⁻¹ ∈ zpowers x := by
      have := Subgroup.mul_mem _ h (Subgroup.inv_mem _ hc)
      simpa using this
    have h2 : t ∈ zpowers x := by simpa using Subgroup.inv_mem _ h1
    exact Subgroup.mul_mem _ h2 hc)
  have hyy' : t⁻¹ * c ∉ zpowers (t * c) := by
    intro hmem
    rcases eq_or_eq_inv_of_mem_zpowers hty3 (mem_zpowers _) hmem hyLO.2.1 hy'1 with h | h
    ·
      have h1 : t⁻¹ = t := mul_right_cancel h
      have h2 : t * t = 1 := by
        calc t * t = t * t⁻¹ := by rw [h1]
          _ = 1 := mul_inv_cancel t
      exact ht1 (eq_one_of_mul_self_eq_one_of_pow_three h2 (hDel.2 t htD))
    ·
      have h1 : t⁻¹ * c = t⁻¹ * c⁻¹ := by
        rw [h, mul_inv_rev]
        exact (Commute.inv_inv (show Commute c t from htc.symm)).eq
      have h2 : c = c⁻¹ := mul_left_cancel h1
      have h3 : c * c = 1 := by
        calc c * c = c * c⁻¹ := by rw [← h2]
          _ = 1 := mul_inv_cancel c
      exact hc1 (eq_one_of_mul_self_eq_one_of_pow_three h3 (hDel.2 c hcD))
  refine false_of_three_lines hS hU0 hD1 K1 K2 K3 K4 hno hKM hKA hL hA1 hA3 hE1 hE3 hp hM hDM
    hDel hDc (a := x) (b := t * c) (c := t⁻¹ * c) (Subgroup.mem_sup_right (mem_zpowers x)) hyD
    hy'D hx1 hyLO.2.1 hy'1 (zpowers_ne_of_not_mem hyx) (zpowers_ne_of_not_mem hxy')
    (zpowers_ne_of_not_mem hyy') hxLO hyLO hy'

theorem exists_mem_normalizer_conj {x : G} {Q : Subgroup G}
    (hQ : IsSylowOf 3 Q (centralizer ({x} : Set G)))
    (hQc : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a) {g : G} (hg : g * x * g⁻¹ ∈ Q) :
    ∃ h ∈ normalizer (Q : Set G), h * x * h⁻¹ = g * x * g⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  set Q' : Subgroup G := Q.map (MulAut.conj g⁻¹).toMonoidHom with hQ'
  have hQ'mem : ∀ y : G, y ∈ Q' ↔ g * y * g⁻¹ ∈ Q := by
    intro y
    constructor
    · rintro ⟨q, hq, rfl⟩
      simpa [mul_assoc] using hq
    · intro hy
      exact ⟨g * y * g⁻¹, hy, by simp [mul_assoc]⟩
  have hQ'C : Q' ≤ C := fun y hy => by
    have h1 : (g * y * g⁻¹) * (g * x * g⁻¹) = (g * x * g⁻¹) * (g * y * g⁻¹) :=
      hQc _ ((hQ'mem y).mp hy) _ hg
    rw [mem_centralizer_singleton_iff]
    have h2 : g * (y * x) * g⁻¹ = g * (x * y) * g⁻¹ := by
      calc g * (y * x) * g⁻¹ = (g * y * g⁻¹) * (g * x * g⁻¹) := by group
        _ = (g * x * g⁻¹) * (g * y * g⁻¹) := h1
        _ = g * (x * y) * g⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h2)
  have hQ'card : Nat.card Q' = 3 ^ (Nat.card C).factorization 3 := by
    rw [hQ', Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
    exact hQ.card_eq
  have hQ'syl : IsSylowOf 3 Q' C := isSylowOf_of_card hQ'C hQ'card
  obtain ⟨k, hkC, hk⟩ := hQ.exists_mem_conj hQ'syl
  have hkx : k * x = x * k := mem_centralizer_singleton_iff.mp hkC
  refine ⟨g * k, ?_, ?_⟩
  · rw [mem_normalizer_iff]
    intro q
    have h1 : k * q * k⁻¹ ∈ Q' ↔ k⁻¹ * (k * q * k⁻¹) * k ∈ Q := hk _
    have h2 : k⁻¹ * (k * q * k⁻¹) * k = q := by group
    rw [h2] at h1
    have h3 := hQ'mem (k * q * k⁻¹)
    have h4 : g * k * q * (g * k)⁻¹ = g * (k * q * k⁻¹) * g⁻¹ := by group
    rw [h4]
    rw [h3] at h1
    exact h1.symm
  · have : g * k * x * (g * k)⁻¹ = g * (k * x * k⁻¹) * g⁻¹ := by group
    rw [this, hkx]
    group

end CFSG.LocalAnalysis.RankThreeTheoremC
