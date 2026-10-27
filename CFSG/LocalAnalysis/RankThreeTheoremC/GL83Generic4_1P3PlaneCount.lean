module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3Lem44Generic
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L28Lem42
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3U3Lemma42
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerRank
import CFSG.LocalAnalysis.RankFourTheoremC.PPointPlane

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

theorem isLargeObstruction_inv {p : ℕ} {M : Subgroup G} {y : G} (h : IsLargeObstruction p M y) :
    IsLargeObstruction p M y⁻¹ := by
  obtain ⟨hyM, hy1, hyp, hrk, hCM⟩ := h
  refine ⟨M.inv_mem hyM, inv_ne_one.mpr hy1, by rw [inv_pow, hyp, inv_one], ?_, ?_⟩
  · rwa [l28lem42_centralizer_inv]
  · rwa [l28lem42_centralizer_inv]

omit [Finite G] in
theorem zpow_two_eq_inv_of_pow_three {x : G} (hx3 : x ^ 3 = 1) : x ^ (2 : ℤ) = x⁻¹ := by
  rw [zpow_two]
  refine eq_inv_of_mul_eq_one_left ?_
  calc x * x * x = x ^ 3 := (pow_three' x).symm
    _ = 1 := hx3

omit [Finite G] in
theorem eq_or_eq_inv_of_mem_zpowers {x : G} (hx3 : x ^ 3 = 1) {a b : G} (ha : a ∈ zpowers x)
    (hb : b ∈ zpowers x) (ha1 : a ≠ 1) (hb1 : b ≠ 1) : b = a ∨ b = a⁻¹ := by
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ha
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hb
  have hx2 := zpow_two_eq_inv_of_pow_three hx3
  rw [l28lem42_zpow_emod hx3 i] at ha1 ⊢
  rw [l28lem42_zpow_emod hx3 j] at hb1 ⊢
  rcases (by omega : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2) with hi | hi | hi <;>
  rcases (by omega : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2) with hj | hj | hj <;>
  simp only [hi, hj, zpow_zero, zpow_one, hx2, ne_eq, not_true_eq_false] at ha1 hb1 ⊢ <;>
  simp [inv_inv]

theorem false_of_plane_lines (hS : Setting G) (hU0 : FullCoreLocal G) (hD1 : TheoremD1 G)
    (K1 : StronglyEmbeddedRankTwoKFactNoBM) (K2 : StronglyEmbeddedCyclicOuterKFact)
    (K3 : KFactOutCyclic) (K4 : KFactComponentPCoreThree) (hno : NoExcludedSection3 G)
    (hKM : CFSG.AGLEmbeddingD2.KFactM11Three) (hKA : KFactM11TwoSignalizer)
    (hL : KFactsL34Full) (hA1 : A6SylowData) (hA3 : A6BorelCore) (hE1 : KFactL28Three)
    (hE3 : KFactL28BorelCore) (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} {M : Subgroup G}
    (hM : IsCoreMaxLocal 3 P M) {D : Subgroup G} (hDM : D ≤ M) (hDel : IsElemAbelian 3 D)
    (hDc : Nat.card D = 3 ^ 2) {z : G} (hzD : z ∈ D) (hz1 : z ≠ 1)
    (hLO : ∀ y ∈ D, y ∉ zpowers z → IsLargeObstruction 3 M y) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hz3 : z ^ 3 = 1 := hDel.2 z hzD
  set T₀ : Subgroup G := pCoreOf 2 M with hT₀
  have hT₀2 : IsPGroup 2 T₀ := CFSG.PreuniquenessRankFour.Helpers.pCoreOf_isPGroup 2 M
  have hMT₀ : M ≤ normalizer (T₀ : Set G) :=
    CFSG.PreuniquenessRankFour.Helpers.subgroup_normalizes_pCoreOf 2 M
  have hcop : Nat.Coprime 3 (Nat.card T₀) := by
    obtain ⟨b, hb⟩ := hT₀2.exists_card_eq
    rw [hb]
    exact Nat.Coprime.pow_right _ (by norm_num)
  have hcommD : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := fun a ha b hb => l28lem42_comm hDel ha hb
  have hgood : ∀ y ∈ D, y ≠ 1 →
      T₀ ⊓ centralizer ({y} : Set G) ≤ centralizer ({z} : Set G) := by
    intro y hyD hy1
    by_cases hyz : y ∈ zpowers z
    ·
      have hy3 : y ^ 3 = 1 := hDel.2 y hyD
      have hyz' : zpowers y = zpowers z := Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hyz) (by
        rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hy3 hy1,
          orderOf_eq_prime hz3 hz1])
      have hzy : z ∈ zpowers y := by rw [hyz']; exact mem_zpowers z
      obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hzy
      intro a ha
      have hay : a * y = y * a := mem_centralizer_singleton_iff.mp ha.2
      rw [mem_centralizer_singleton_iff, ← hj]
      exact (Commute.zpow_right (show Commute a y from hay) j).eq
    · have hcard := card_pCore_inf_centralizer_le_two hS hU0 hD1 K1 K2 K3 K4 hno hKM hKA hL hA1 hA3
        hE1 hE3 hp hM (hLO y hyD hyz)
      intro a ha
      have hzC : z ∈ centralizer ({y} : Set G) :=
        mem_centralizer_singleton_iff.mpr (hcommD z hzD y hyD)
      have hza : z * a * z⁻¹ ∈ T₀ ⊓ centralizer ({y} : Set G) :=
        ⟨(mem_normalizer_iff.mp (hMT₀ (hDM hzD)) a).mp ha.1,
          (mem_normalizer_iff.mp (Subgroup.le_normalizer hzC) a).mp ha.2⟩
      have hax := l28lem42_conj_eq hcard ha hza
      rw [mem_centralizer_singleton_iff]
      calc a * z = (z * a * z⁻¹) * z := by rw [hax]
        _ = z * a := by group
  have hT₀C : T₀ ≤ centralizer ({z} : Set G) :=
    CFSG.LocalAnalysis.RankFourTheoremC.le_of_forall_inf_centralizer_le_plane Nat.prime_three hDel
      hDc (fun d hd => hMT₀ (hDM hd)) hcop hgood
  have hzT : z ∈ T₀ := hS.charTwo M hM.1.1
    ⟨hDM hzD, mem_centralizer_iff.mpr fun t ht => mem_centralizer_singleton_iff.mp (hT₀C ht)⟩
  obtain ⟨k, hk⟩ := hT₀2 ⟨z, hzT⟩
  have h2 : orderOf z ∣ 2 ^ k :=
    orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
  have h3 : orderOf z ∣ 3 := orderOf_dvd_of_pow_eq_one hz3
  have hcoprime : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right _ (by norm_num)
  exact hz1 (orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_one (hcoprime.gcd_eq_one ▸ Nat.dvd_gcd h3 h2)))

theorem not_largeObstruction_of_transitive_plane (hS : Setting G) (hU0 : FullCoreLocal G)
    (hD1 : TheoremD1 G) (K1 : StronglyEmbeddedRankTwoKFactNoBM)
    (K2 : StronglyEmbeddedCyclicOuterKFact) (K3 : KFactOutCyclic) (K4 : KFactComponentPCoreThree)
    (hno : NoExcludedSection3 G) (hKM : CFSG.AGLEmbeddingD2.KFactM11Three)
    (hKA : KFactM11TwoSignalizer) (hL : KFactsL34Full) (hA1 : A6SylowData) (hA3 : A6BorelCore)
    (hE1 : KFactL28Three) (hE3 : KFactL28BorelCore) (hp : 3 ∈ rankThreeSigmaA G)
    {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M) {x : G}
    (hxLO : IsLargeObstruction 3 M x) {K₀ : Subgroup G} (hK₀M : K₀ ≤ M)
    (hK₀el : IsElemAbelian 3 K₀) (hK₀c : Nat.card K₀ = 3 ^ 2) (hxK₀ : x ∉ K₀)
    (hcomm : ∀ k ∈ K₀, k * x = x * k)
    (htr : ∀ a ∈ K₀, ∀ b ∈ K₀, a ≠ 1 → b ≠ 1 →
      ∃ n ∈ M, n * x * n⁻¹ = x ∧ n * a * n⁻¹ = b)
    {y : G} (hy : y ∈ K₀ ⊔ zpowers x) (hyx : y ∉ zpowers x) :
    ¬ IsLargeObstruction 3 M y := by
  intro hyLO
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hxM, hx1, hx3, -, -⟩ := id hxLO
  have hKz : ∀ k ∈ K₀, ∀ c ∈ zpowers x, k * c = c * k := fun k hk c hc => by
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hc
    exact (Commute.zpow_right (show Commute k x from hcomm k hk) j).eq
  obtain ⟨k, hk, v, hv, rfl⟩ := u3l42_decomp hKz hy
  have hk1 : k ≠ 1 := by
    rintro rfl
    exact hyx (by simpa using hv)
  have hk3 : k ^ 3 = 1 := hK₀el.2 k hk
  have hconj : ∀ b ∈ K₀, b ≠ 1 → ∀ w ∈ zpowers x, IsLargeObstruction 3 M (k * w) →
      IsLargeObstruction 3 M (b * w) := by
    intro b hb hb1 w hwx hw
    obtain ⟨n, hnM, hnx, hnk⟩ := htr k hk b hb hk1 hb1
    have hnw : n * w * n⁻¹ = w := by
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hwx
      have h := map_zpow (MulAut.conj n) x j
      simp only [MulAut.conj_apply] at h
      rw [h, hnx]
    have h := hw.conj hnM
    rw [MulAut.conj_apply] at h
    have h' : n * (k * w) * n⁻¹ = b * w := by
      rw [show n * (k * w) * n⁻¹ = (n * k * n⁻¹) * (n * w * n⁻¹) by group, hnk, hnw]
    rwa [h'] at h
  have hxpow : ∀ c ∈ zpowers x, c ≠ 1 → IsLargeObstruction 3 M c := by
    intro c hc hc1
    rcases eq_or_eq_inv_of_mem_zpowers hx3 (mem_zpowers x) hc hx1 hc1 with rfl | rfl
    · exact hxLO
    · exact isLargeObstruction_inv hxLO
  by_cases hv1 : v = 1
  ·
    subst hv1
    have hS1 : ∀ b ∈ K₀, b ≠ 1 → IsLargeObstruction 3 M b := fun b hb hb1 => by
      simpa using hconj b hb hb1 1 (one_mem _) (by simpa using hyLO)
    refine false_of_plane_lines hS hU0 hD1 K1 K2 K3 K4 hno hKM hKA hL hA1 hA3 hE1 hE3 hp hM hK₀M
      hK₀el hK₀c hk hk1 fun w hw hwk => hS1 w hw ?_
    rintro rfl
    exact hwk (one_mem _)
  ·
    have hmix : ∀ t ∈ K₀, t ≠ 1 → ∀ c ∈ zpowers x, c ≠ 1 → IsLargeObstruction 3 M (t * c) := by
      intro t ht ht1 c hc hc1
      rcases eq_or_eq_inv_of_mem_zpowers hx3 hv hc hv1 hc1 with rfl | rfl
      · exact hconj t ht ht1 c hv hyLO
      · have h := isLargeObstruction_inv (hconj t⁻¹ (K₀.inv_mem ht) (inv_ne_one.mpr ht1) v hv hyLO)
        have hc : t * v⁻¹ = v⁻¹ * t :=
          (Commute.inv_right (show Commute t v from hKz t ht v hv)).eq
        rwa [mul_inv_rev, inv_inv, ← hc] at h
    have hxk : x ∉ zpowers k := fun hx => hxK₀ (zpowers_le.mpr hk hx)
    have hkx : ∀ e ∈ zpowers k, e * x = x * e := fun e he => by
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp he
      exact (Commute.zpow_left (show Commute k x from hcomm k hk) j).eq
    have hD'c : Nat.card ↥(zpowers k ⊔ zpowers x) = 3 ^ 2 := by
      rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers Nat.prime_three (zpowers k) hx3 hxk hkx,
        Nat.card_zpowers, orderOf_eq_prime hk3 hk1]
      norm_num
    have hD'el : IsElemAbelian 3 (zpowers k ⊔ zpowers x) :=
      CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_sup_of_commuting 3
        (CFSG.AGLEmbedding.isElemAbelian_zpowers hk3)
        (CFSG.AGLEmbedding.isElemAbelian_zpowers hx3) (fun e he => by
          rw [mem_centralizer_iff]
          intro a ha
          obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp ha
          exact ((Commute.zpow_right (show Commute e x from hkx e he) j).eq).symm)
    refine false_of_plane_lines hS hU0 hD1 K1 K2 K3 K4 hno hKM hKA hL hA1 hA3 hE1 hE3 hp hM
      (sup_le (zpowers_le.mpr (hK₀M hk)) (zpowers_le.mpr hxM)) hD'el hD'c
      (z := k) (Subgroup.mem_sup_left (mem_zpowers k)) hk1 fun w hw hwk => ?_
    obtain ⟨t, ht, c, hc, rfl⟩ := u3l42_decomp (T := zpowers k) (Z := zpowers x)
      (fun t ht c hc => hKz t (zpowers_le.mpr hk ht) c hc) hw
    have hc1 : c ≠ 1 := by
      rintro rfl
      exact hwk (by simpa using ht)
    by_cases ht1 : t = 1
    · subst ht1
      simpa using hxpow c hc hc1
    · exact hmix t (zpowers_le.mpr hk ht) ht1 c hc hc1

theorem mem_elem27_of_pow_three {Q E : Subgroup G} (hQc : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a)
    (hrank : CFSG.Open.pRank 3 Q = 3) (hEQ : E ≤ Q) (hEel : IsElemAbelian 3 E)
    (hEcard : Nat.card E = 3 ^ 3) {y : G} (hyQ : y ∈ Q) (hy3 : y ^ 3 = 1) : y ∈ E := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hyE
  have hcomm : ∀ e ∈ E, e * y = y * e := fun e he => hQc e (hEQ he) y hyQ
  have hcard := CFSG.RankThree.PartOne.Planes.card_sup_zpowers Nat.prime_three E hy3 hyE hcomm
  have hcent : E ≤ centralizer ((zpowers y : Subgroup G) : Set G) := fun e he => by
    rw [zpowers_eq_closure, centralizer_closure]
    exact mem_centralizer_singleton_iff.mpr (hcomm e he)
  have hel := CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_sup_of_commuting 3 hEel
    (CFSG.AGLEmbedding.isElemAbelian_zpowers hy3) hcent
  have hle : E ⊔ zpowers y ≤ Q := sup_le hEQ (zpowers_le.mpr hyQ)
  have h4 := le_pRank_of_elemAbelian_card (p := 3) hle hel (k := 4)
    (by rw [hcard, hEcard]; norm_num)
  omega

theorem lemma42_of_transitive_plane (hS : Setting G) (hU0 : FullCoreLocal G) (hD1 : TheoremD1 G)
    (K1 : StronglyEmbeddedRankTwoKFactNoBM) (K2 : StronglyEmbeddedCyclicOuterKFact)
    (K3 : KFactOutCyclic) (K4 : KFactComponentPCoreThree) (hno : NoExcludedSection3 G)
    (hKM : CFSG.AGLEmbeddingD2.KFactM11Three) (hKA : KFactM11TwoSignalizer)
    (hL : KFactsL34Full) (hA1 : A6SylowData) (hA3 : A6BorelCore) (hE1 : KFactL28Three)
    (hE3 : KFactL28BorelCore) (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} {M : Subgroup G}
    (hM : IsCoreMaxLocal 3 P M) {x : G} (hxLO : IsLargeObstruction 3 M x) {K₀ : Subgroup G}
    (hK₀M : K₀ ≤ M) (hK₀el : IsElemAbelian 3 K₀) (hK₀c : Nat.card K₀ = 3 ^ 2) (hxK₀ : x ∉ K₀)
    (hcomm : ∀ k ∈ K₀, k * x = x * k)
    (htr : ∀ a ∈ K₀, ∀ b ∈ K₀, a ≠ 1 → b ≠ 1 →
      ∃ n ∈ M, n * x * n⁻¹ = x ∧ n * a * n⁻¹ = b)
    {u : G} (huE : u ∈ K₀ ⊔ zpowers x) (hux : u ∉ zpowers x) :
    centralizer ({u} : Set G) ≤ M := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hCu
  obtain ⟨hxM, hx1, hx3, -, -⟩ := id hxLO
  have hcentx : K₀ ≤ centralizer ((zpowers x : Subgroup G) : Set G) := fun k hk => by
    rw [mem_centralizer_iff]
    intro a ha
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp ha
    exact ((Commute.zpow_right (show Commute k x from hcomm k hk) j).eq).symm
  have hEel : IsElemAbelian 3 (K₀ ⊔ zpowers x) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_sup_of_commuting 3 hK₀el
      (CFSG.AGLEmbedding.isElemAbelian_zpowers hx3) hcentx
  have hEcard : Nat.card ↥(K₀ ⊔ zpowers x) = 3 ^ 3 := by
    rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers Nat.prime_three K₀ hx3 hxK₀ hcomm, hK₀c]
    norm_num
  have hEM : K₀ ⊔ zpowers x ≤ M := sup_le hK₀M (zpowers_le.mpr hxM)
  have hEC : K₀ ⊔ zpowers x ≤ centralizer ({u} : Set G) := fun e he =>
    mem_centralizer_singleton_iff.mpr (l28lem42_comm hEel he huE)
  have hu1 : u ≠ 1 := fun h => hux (h ▸ one_mem _)
  have hLO : IsLargeObstruction 3 M u :=
    ⟨hEM huE, hu1, hEel.2 u huE, le_pRank_of_elemAbelian_card hEC hEel hEcard, hCu⟩
  exact not_largeObstruction_of_transitive_plane hS hU0 hD1 K1 K2 K3 K4 hno hKM hKA hL hA1 hA3 hE1
    hE3 hp hM hxLO hK₀M hK₀el hK₀c hxK₀ hcomm htr huE hux hLO

end CFSG.LocalAnalysis.RankThreeTheoremC
