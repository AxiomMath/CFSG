module

public import CFSG.RankThree.PartOne.S9.Planes.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {X : Type*} [Group X] [Finite X]

omit [Finite X] in
private lemma mul_eq_of_mem_zpowers {x y g : X} (hxy : x * y = y * x) (hg : g ∈ zpowers x) :
    g * y = y * g := by
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hg
  exact (Commute.zpow_left (show Commute x y from hxy) n).eq

omit [Finite X] in
private lemma mul_eq_of_mem_sup {S T : Subgroup X} {y g : X} (hS : ∀ s ∈ S, s * y = y * s)
    (hT : ∀ s ∈ T, s * y = y * s) (hg : g ∈ S ⊔ T) : g * y = y * g := by
  have h : S ⊔ T ≤ centralizer ({y} : Set X) :=
    sup_le (fun s hs => mem_centralizer_singleton_iff.2 (hS s hs))
      (fun s hs => mem_centralizer_singleton_iff.2 (hT s hs))
  exact mem_centralizer_singleton_iff.1 (h hg)

omit [Finite X] in
private lemma isElemAbelian_zpowers_of_orderOf {x : X} (hx : orderOf x = 3) :
    CFSG.Open.IsElemAbelian 3 (zpowers x) ∧ Nat.card (zpowers x) = 3 ^ 1 := by
  refine ⟨(CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 _).1 ?_, ?_⟩
  · exact CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one (hx ▸ pow_orderOf_eq_one x)
  · rw [Nat.card_zpowers, hx, pow_one]

private lemma isElemAbelian_sup_zpowers {E : Subgroup X} {f : X} {k : ℕ}
    (hE : CFSG.Open.IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ k) (hf : f ^ 3 = 1)
    (hfE : f ∉ E) (hcomm : ∀ e ∈ E, e * f = f * e) :
    CFSG.Open.IsElemAbelian 3 (E ⊔ zpowers f) ∧
      Nat.card (E ⊔ zpowers f : Subgroup X) = 3 ^ (k + 1) := by
  refine ⟨?_, ?_⟩
  · have : CFSG.IsElementaryAbelian 3 E :=
      (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 E).2 hE
    have : CFSG.IsElementaryAbelian 3 (zpowers f) :=
      CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one hf
    refine (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 _).1
      (CFSG.IsElementaryAbelian.sup_of_le_centralizer ?_)
    rw [zpowers_le, mem_centralizer_iff]
    exact hcomm
  · rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers Nat.prime_three E hf hfE hcomm, hcard,
      pow_succ]

theorem le_rankThreeAschCore_of_le_centralizer {P E Y K : Subgroup X} (hEP : E ≤ P)
    (hE : CFSG.Open.IsElemAbelian 3 E) (hE3 : 3 ≤ CFSG.Open.pRank 3 E) (hYE : Y ≤ E)
    (hY2 : 2 ≤ CFSG.Open.pRank 3 Y) (hKY : K ≤ centralizer (Y : Set X)) :
    K ≤ rankThreeAschCore 2 3 P := by
  have hcomm := hE.1
  have hEc : E ≤ P ⊓ centralizer (Y : Set X) := by
    refine le_inf hEP fun e he => mem_centralizer_iff.2 fun y hy => ?_
    exact congrArg Subtype.val (mul_comm' (⟨y, hYE hy⟩ : E) ⟨e, he⟩)
  have hrank : 3 ≤ CFSG.Open.pRank 3 (Y ⊔ (P ⊓ centralizer (Y : Set X))) :=
    hE3.trans (CFSG.RankThreeCoreUniqueness.Helpers.pRank_mono 3 (by norm_num)
      (hEc.trans le_sup_right))
  exact hKY.trans ((centralizer_le_normalizer (Y : Set X)).trans
    (aschCore_normalizer_le 2 3 P Y (hYE.trans hEP) hY2 hrank))

theorem le_rankThreeAschCore_of_commuting_triple {P K : Subgroup X} {z a t : X}
    (hz : z ∈ P) (ha : a ∈ P) (ht : t ∈ P) (hz3 : orderOf z = 3) (ha3 : orderOf a = 3)
    (ht3 : orderOf t = 3) (hza : z * a = a * z) (hzt : z * t = t * z) (hat : a * t = t * a)
    (haz : a ∉ zpowers z) (htza : t ∉ zpowers z ⊔ zpowers a)
    (hKz : ∀ k ∈ K, z * k = k * z) (hKa : ∀ k ∈ K, a * k = k * a) :
    K ≤ rankThreeAschCore 2 3 P := by
  have ha1 : a ^ 3 = 1 := ha3 ▸ pow_orderOf_eq_one a
  have ht1 : t ^ 3 = 1 := ht3 ▸ pow_orderOf_eq_one t
  obtain ⟨hZ, hZc⟩ := isElemAbelian_zpowers_of_orderOf hz3
  obtain ⟨hY, hYc⟩ := isElemAbelian_sup_zpowers hZ hZc ha1 haz
    (fun e he => mul_eq_of_mem_zpowers hza he)
  obtain ⟨hE, hEc⟩ := isElemAbelian_sup_zpowers hY hYc ht1 htza
    (fun e he => mul_eq_of_mem_sup (fun s hs => mul_eq_of_mem_zpowers hzt hs)
      (fun s hs => mul_eq_of_mem_zpowers hat hs) he)
  have hEP : zpowers z ⊔ zpowers a ⊔ zpowers t ≤ P :=
    sup_le (sup_le (zpowers_le.2 hz) (zpowers_le.2 ha)) (zpowers_le.2 ht)
  have hE3 : 3 ≤ CFSG.Open.pRank 3 (zpowers z ⊔ zpowers a ⊔ zpowers t) :=
    CFSG.SectionRank.le_pRank (by norm_num) le_rfl hE hEc
  have hY2 : 2 ≤ CFSG.Open.pRank 3 (zpowers z ⊔ zpowers a) :=
    CFSG.SectionRank.le_pRank (by norm_num) le_rfl hY hYc
  have hKY : K ≤ centralizer ((zpowers z ⊔ zpowers a : Subgroup X) : Set X) := by
    refine Subgroup.le_centralizer_iff.1 (sup_le ?_ ?_)
    · exact zpowers_le.2 (mem_centralizer_iff.2 fun k hk => (hKz k hk).symm)
    · exact zpowers_le.2 (mem_centralizer_iff.2 fun k hk => (hKa k hk).symm)
  exact le_rankThreeAschCore_of_le_centralizer hEP hE hE3 le_sup_left hY2 hKY

theorem mem_rankThreeAschCore_of_commute {P A : Subgroup X} {z f k : X} (hAP : A ≤ P)
    (hA : CFSG.Open.IsElemAbelian 3 A) (hA3 : 3 ≤ CFSG.Open.pRank 3 A) (hzP : z ∈ P)
    (hzc : ∀ g ∈ P, z * g = g * z) (hz3 : orderOf z = 3) (hf : f ∈ A) (hfz : f ∉ zpowers z)
    (hzk : z * k = k * z) (hfk : f * k = k * f) : k ∈ rankThreeAschCore 2 3 P := by
  have hf1 : f ^ 3 = 1 := hA.2 f hf
  obtain ⟨hZ, hZc⟩ := isElemAbelian_zpowers_of_orderOf hz3
  obtain ⟨hY, hYc⟩ := isElemAbelian_sup_zpowers hZ hZc hf1 hfz
    (fun e he => mul_eq_of_mem_zpowers (hzc f (hAP hf)) he)
  have hZA : zpowers z ≤ centralizer (A : Set X) :=
    zpowers_le.2 (mem_centralizer_iff.2 fun g hg => (hzc g (hAP hg)).symm)
  have hE : CFSG.Open.IsElemAbelian 3 (A ⊔ zpowers z) := by
    have : CFSG.IsElementaryAbelian 3 A :=
      (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 A).2 hA
    have : CFSG.IsElementaryAbelian 3 (zpowers z) :=
      (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 _).2 hZ
    exact (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 _).1
      (CFSG.IsElementaryAbelian.sup_of_le_centralizer hZA)
  have hE3 : 3 ≤ CFSG.Open.pRank 3 (A ⊔ zpowers z) :=
    hA3.trans (CFSG.RankThreeCoreUniqueness.Helpers.pRank_mono 3 (by norm_num) le_sup_left)
  have hEP : A ⊔ zpowers z ≤ P := sup_le hAP (zpowers_le.2 hzP)
  have hYE : zpowers z ⊔ zpowers f ≤ A ⊔ zpowers z :=
    sup_le le_sup_right (le_sup_of_le_left (zpowers_le.2 hf))
  have hY2 : 2 ≤ CFSG.Open.pRank 3 (zpowers z ⊔ zpowers f) :=
    CFSG.SectionRank.le_pRank (by norm_num) le_rfl hY hYc
  have hKY : zpowers k ≤ centralizer ((zpowers z ⊔ zpowers f : Subgroup X) : Set X) := by
    refine Subgroup.le_centralizer_iff.1 (sup_le ?_ ?_)
    · exact zpowers_le.2 (mem_centralizer_iff.2 fun g hg => mul_eq_of_mem_zpowers hzk.symm hg)
    · exact zpowers_le.2 (mem_centralizer_iff.2 fun g hg => mul_eq_of_mem_zpowers hfk.symm hg)
  exact le_rankThreeAschCore_of_le_centralizer hEP hE hE3 hYE hY2 hKY (mem_zpowers k)

end CFSG.LocalAnalysis.RankThreeTheoremC
