module

public import CFSG.LocalAnalysis.RankThreeTheoremC.NGK3Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.ObstructionElements

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {X : Type} [Group X] [Finite X] {P D : Subgroup X} {z : X}

omit [Finite X] in
private lemma mul_eq_of_mem_zpowers_aux {x y g : X} (hxy : x * y = y * x) (hg : g ∈ zpowers x) :
    g * y = y * g := by
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hg
  exact (Commute.zpow_left (show Commute x y from hxy) n).eq

omit [Finite X] in
private lemma mul_eq_of_mem_sup_aux {S T : Subgroup X} {y g : X} (hS : ∀ s ∈ S, s * y = y * s)
    (hT : ∀ s ∈ T, s * y = y * s) (hg : g ∈ S ⊔ T) : g * y = y * g := by
  have h : S ⊔ T ≤ centralizer ({y} : Set X) :=
    sup_le (fun s hs => mem_centralizer_singleton_iff.2 (hS s hs))
      (fun s hs => mem_centralizer_singleton_iff.2 (hT s hs))
  exact mem_centralizer_singleton_iff.1 (h hg)

omit [Finite X] in
private lemma isElemAbelian_zpowers_of_orderOf_aux {x : X} (hx : orderOf x = 3) :
    CFSG.Open.IsElemAbelian 3 (zpowers x) ∧ Nat.card (zpowers x) = 3 ^ 1 := by
  refine ⟨(CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 _).1 ?_, ?_⟩
  · exact CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one (hx ▸ pow_orderOf_eq_one x)
  · rw [Nat.card_zpowers, hx, pow_one]

private lemma isElemAbelian_sup_zpowers_aux {E : Subgroup X} {f : X} {k : ℕ}
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

private lemma isElemAbelian_triple_aux {a b c : X} (ha : orderOf a = 3) (hb : b ^ 3 = 1)
    (hc : c ^ 3 = 1) (hab : a * b = b * a) (hac : a * c = c * a) (hbc : b * c = c * b)
    (hba : b ∉ zpowers a) (hcab : c ∉ zpowers a ⊔ zpowers b) :
    CFSG.Open.IsElemAbelian 3 (zpowers a ⊔ zpowers b ⊔ zpowers c) ∧
      Nat.card (zpowers a ⊔ zpowers b ⊔ zpowers c : Subgroup X) = 3 ^ 3 := by
  obtain ⟨hA, hAc⟩ := isElemAbelian_zpowers_of_orderOf_aux ha
  obtain ⟨hY, hYc⟩ := isElemAbelian_sup_zpowers_aux hA hAc hb hba
    (fun e he => mul_eq_of_mem_zpowers_aux hab he)
  exact isElemAbelian_sup_zpowers_aux hY hYc hc hcab
    (fun e he => mul_eq_of_mem_sup_aux (fun s hs => mul_eq_of_mem_zpowers_aux hac hs)
      (fun s hs => mul_eq_of_mem_zpowers_aux hbc hs) he)

private lemma PlaneData.card_center (h : PlaneData P D z) : Nat.card (center D) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk0, hk⟩ := IsPGroup.card_center_eq_prime_pow h.card (by norm_num : 0 < 3)
  have hdvd : 3 ^ k ∣ 3 ^ 3 := h.card ▸ hk ▸ card_subgroup_dvd_card (center D)
  have hk3 : k ≤ 3 := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 hdvd
  have hmul := (center D).card_mul_index
  rw [hk, h.card] at hmul
  have hnc : ¬ IsMulCommutative D := h.plane.2.1
  interval_cases k
  · simpa using hk
  · exfalso
    have hidx : (center D).index = 3 := by norm_num at hmul; omega
    have hq : Nat.card (D ⧸ center D) = 3 := by rw [← index_eq_card, hidx]
    have : IsCyclic (D ⧸ center D) := isCyclic_of_prime_card hq
    exact hnc (isMulCommutative_of_isCyclic_quotient_center_self D)
  · exfalso
    have htop : center D = ⊤ := eq_top_of_card_eq _ (by rw [hk, h.card])
    exact hnc (Subgroup.center_eq_top_iff.1 htop)

private lemma PlaneData.center_eq (h : PlaneData P D z) :
    center D = zpowers (⟨z, h.zD⟩ : D) := by
  symm
  refine eq_of_le_of_card_ge ?_ ?_
  · rw [zpowers_le, mem_center_iff]
    intro g
    exact Subtype.ext (h.zc g (h.plane.1 g.2)).symm
  · rw [h.card_center, Nat.card_zpowers, Subgroup.orderOf_mk, h.zo]

private lemma PlaneData.mem_zpowers_of_mem_center (h : PlaneData P D z) {d : D}
    (hd : d ∈ center D) : (d : X) ∈ zpowers z := by
  rw [h.center_eq] at hd
  obtain ⟨n, hn⟩ := mem_zpowers_iff.1 hd
  exact mem_zpowers_iff.2 ⟨n, by simpa using congrArg Subtype.val hn⟩

theorem PlaneData.comm_mem (h : PlaneData P D z) :
    ∀ a ∈ D, ∀ b ∈ D, a * b * a⁻¹ * b⁻¹ ∈ zpowers z := by
  intro a ha b hb
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hq : Nat.card (D ⧸ center D) = 3 ^ 2 := by
    rw [← index_eq_card]
    have hmul := (center D).card_mul_index
    rw [h.card_center, h.card] at hmul
    norm_num at hmul ⊢
    omega
  have hcomm : IsMulCommutative (D ⧸ center D) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq hq
  have hmem : (⟨a, ha⟩ * ⟨b, hb⟩ * ⟨a, ha⟩⁻¹ * ⟨b, hb⟩⁻¹ : D) ∈ center D := by
    rw [← QuotientGroup.eq_one_iff]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [mul_comm' ((⟨a, ha⟩ : D) : D ⧸ center D) ((⟨b, hb⟩ : D) : D ⧸ center D)]
    group
  exact h.mem_zpowers_of_mem_center hmem

theorem PlaneData.center_le (h : PlaneData P D z) :
    ∀ d ∈ D, (∀ e ∈ D, d * e = e * d) → d ∈ zpowers z := by
  intro d hd hc
  refine h.mem_zpowers_of_mem_center (d := ⟨d, hd⟩) (mem_center_iff.2 fun g => ?_)
  exact Subtype.ext (hc g g.2).symm

theorem PlaneData.omega_cent (h : PlaneData P D z) :
    ∀ c ∈ P, (∀ d ∈ D, c * d = d * c) → c ^ 3 = 1 → c ∈ zpowers z := by
  intro c hcP hcD hc3
  by_contra hcz
  have hDz : ¬ D ≤ zpowers z := by
    intro hle
    have := card_le_of_le hle
    rw [Nat.card_zpowers, h.zo, h.card] at this
    norm_num at this
  obtain ⟨d, hdD, hdz⟩ := IsConcreteLE.not_le_iff_exists.1 hDz
  have hd3 : d ^ 3 = 1 := h.plane.2.2.1 d hdD
  have hzd : z * d = d * z := h.zc d (h.plane.1 hdD)
  have hzc : z * c = c * z := h.zc c hcP
  have hdc : d * c = c * d := (hcD d hdD).symm
  have hcnot : c ∉ zpowers z ⊔ zpowers d := by
    intro hmem
    have hcD' : c ∈ D := (sup_le (zpowers_le.2 h.zD) (zpowers_le.2 hdD)) hmem
    exact hcz (h.center_le c hcD' fun e he => hcD e he)
  obtain ⟨hE, hEc⟩ := isElemAbelian_triple_aux h.zo hd3 hc3 hzd hzc hdc hdz hcnot
  have hle : zpowers z ⊔ zpowers d ⊔ zpowers c ≤ D ⊔ (P ⊓ centralizer (D : Set X)) := by
    refine sup_le (sup_le ?_ ?_) ?_
    · exact le_sup_of_le_left (zpowers_le.2 h.zD)
    · exact le_sup_of_le_left (zpowers_le.2 hdD)
    · exact le_sup_of_le_right (zpowers_le.2 (mem_inf.2 ⟨hcP,
        mem_centralizer_iff.2 fun e he => (hcD e he).symm⟩))
  have h3 : 3 ≤ CFSG.Open.pRank 3 (D ⊔ (P ⊓ centralizer (D : Set X))) :=
    (CFSG.SectionRank.le_pRank (by norm_num) le_rfl hE hEc).trans
      (pRank_mono 3 (by norm_num) hle)
  have h2 := h.plane.2.2.2
  omega

theorem PlaneData.cent_cyclic (h : PlaneData P D z) : IsCyclic ↥(P ⊓ centralizer (D : Set X)) := by
  by_contra hnc
  have hCp : IsPGroup 3 ↥(P ⊓ centralizer (D : Set X)) := h.pgroup.to_inf_left
  have h2 : 2 ≤ CFSG.Open.pRank 3 (P ⊓ centralizer (D : Set X)) :=
    two_le_pRank_of_not_isCyclic Nat.prime_three (by norm_num) hCp hnc
  obtain ⟨E, hEC, hE, hcard⟩ := pRank_attained 3 (P ⊓ centralizer (D : Set X)) (by omega)
  have hEz : E ≤ zpowers z := by
    intro x hx
    have hxC := mem_inf.1 (hEC hx)
    exact h.omega_cent x hxC.1 (fun d hd => (mem_centralizer_iff.1 hxC.2 d hd).symm)
      (hE.2 x hx)
  have h9 : 3 ^ 2 ≤ Nat.card E := hcard ▸ Nat.pow_le_pow_right (by norm_num) h2
  have h3 : Nat.card E ≤ 3 := (card_le_of_le hEz).trans (by rw [Nat.card_zpowers, h.zo])
  omega

end CFSG.LocalAnalysis.RankThreeTheoremC
