module

public import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.LocalAnalysis.PreuniquenessRankFour.RankTwo
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CoprimeRankTwo
import CFSG.RankThree.PartOne.S9.Planes.Basic
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type*} [Group G] [Finite G]

theorem card_lines_le {p : ℕ} (hp : p.Prime) {D : Subgroup G} (hDcard : Nat.card D = p ^ 2)
    (S : Finset (Subgroup G)) (hS : ∀ L ∈ S, L ≤ D ∧ Nat.card L = p) : S.card ≤ p + 1 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype G := Fintype.ofFinite G
  let s : Subgroup G → Finset G := fun L => (Finset.univ.filter (· ∈ L)).erase 1
  have hcardfilter : ∀ L : Subgroup G, (Finset.univ.filter (· ∈ L)).card = Nat.card L := by
    intro L
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hscard : ∀ L ∈ S, (s L).card = p - 1 := by
    intro L hL
    simp only [s]
    rw [Finset.card_erase_of_mem (by simp [one_mem]), hcardfilter, (hS L hL).2]
  have hdisj : ∀ L₁ ∈ S, ∀ L₂ ∈ S, L₁ ≠ L₂ → Disjoint (s L₁) (s L₂) := by
    intro L₁ h₁ L₂ h₂ hne
    rw [Finset.disjoint_left]
    intro y hy1 hy2
    simp only [s, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at hy1 hy2
    have hyp : orderOf y = p := by
      refine (Nat.dvd_prime hp).mp ?_ |>.resolve_left ?_
      · rw [← (hS L₁ h₁).2]
        exact orderOf_dvd_natCard (⟨y, hy1.2⟩ : L₁) |> fun h => by
          rwa [Subgroup.orderOf_mk] at h
      · intro h1
        exact hy1.1 (orderOf_eq_one_iff.mp h1)
    have hz : ∀ L : Subgroup G, y ∈ L → Nat.card L = p → zpowers y = L := fun L hyL hLc =>
      Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hyL) (by
        rw [Nat.card_zpowers, hyp, hLc])
    exact hne ((hz L₁ hy1.2 (hS L₁ h₁).2).symm.trans (hz L₂ hy2.2 (hS L₂ h₂).2))
  have hsub : S.biUnion s ⊆ (Finset.univ.filter (· ∈ D)).erase 1 := by
    intro y hy
    obtain ⟨L, hL, hyL⟩ := Finset.mem_biUnion.mp hy
    simp only [s, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at hyL ⊢
    exact ⟨hyL.1, (hS L hL).1 hyL.2⟩
  have hDc : ((Finset.univ.filter (· ∈ D)).erase 1).card = p ^ 2 - 1 := by
    rw [Finset.card_erase_of_mem (by simp [one_mem]), hcardfilter, hDcard]
  have hle := Finset.card_le_card hsub
  rw [Finset.card_biUnion hdisj, Finset.sum_const_nat hscard, hDc] at hle
  have hp1 := hp.one_lt
  have : (p - 1) * (p + 1) = p ^ 2 - 1 := by
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring_nf
    omega
  rw [← this, mul_comm] at hle
  exact Nat.le_of_mul_le_mul_left hle (by omega)

theorem le_of_forall_inf_centralizer_le_plane {p : ℕ} (hp : p.Prime) {B R O : Subgroup G}
    (hB : IsElemAbelian p B) (hBc : Nat.card B = p ^ 2) (hBR : B ≤ normalizer (R : Set G))
    (hcop : p.Coprime (Nat.card R))
    (h : ∀ y ∈ B, y ≠ 1 → R ⊓ centralizer ({y} : Set G) ≤ O) : R ≤ O := by
  obtain ⟨φ, hinj, hrange⟩ :=
    elementary_rank_two_has_coordinate_embedding p hp B hB 2 hBc le_rfl
  refine embedded_rank_two_signalizer_le_of_line_centralizers p hp φ R O (hrange.trans hBR)
    hcop fun v hv => ?_
  have hmem : φ (Multiplicative.ofAdd v) ∈ (φ.comp (coordinatePairLineHom v)).range :=
    ⟨Multiplicative.ofAdd 1, by simp [coordinatePairLineHom]⟩
  have hne : φ (Multiplicative.ofAdd v) ≠ 1 := fun h1 =>
    hv (by simpa using hinj (h1.trans (map_one φ).symm))
  exact (inf_le_inf_left R (centralizer_le (Set.singleton_subset_iff.mpr hmem))).trans
    (h _ (hrange ⟨_, rfl⟩) hne)

omit [Finite G] in
theorem card_zpowers_of_isElemAbelian {p : ℕ} (hp : p.Prime) {D : Subgroup G}
    (hD : IsElemAbelian p D) {y : G} (hyD : y ∈ D) (hy1 : y ≠ 1) : Nat.card (zpowers y) = p := by
  have : Fact p.Prime := ⟨hp⟩
  rw [Nat.card_zpowers, orderOf_eq_prime (hD.2 y hyD) hy1]

theorem exists_two_bad_lines {p : ℕ} (hp : p.Prime) {D T : Subgroup G} (hD : IsElemAbelian p D)
    (hDcard : Nat.card D = p ^ 2) (hDT : D ≤ normalizer (T : Set G))
    (hcop : p.Coprime (Nat.card T)) (hC : ∀ d ∈ D, (∀ t ∈ T, d * t = t * d) → d = 1) :
    ∃ L₁ L₂ : Subgroup G, L₁ ≠ L₂ ∧ (L₁ ≤ D ∧ Nat.card L₁ = p ∧
      ⁅T ⊓ centralizer (L₁ : Set G), D⁆ ≠ ⊥) ∧ (L₂ ≤ D ∧ Nat.card L₂ = p ∧
      ⁅T ⊓ centralizer (L₂ : Set G), D⁆ ≠ ⊥) := by
  by_contra hno
  have hone : ∀ L₁ L₂ : Subgroup G, (L₁ ≤ D ∧ Nat.card L₁ = p ∧
      ⁅T ⊓ centralizer (L₁ : Set G), D⁆ ≠ ⊥) → (L₂ ≤ D ∧ Nat.card L₂ = p ∧
      ⁅T ⊓ centralizer (L₂ : Set G), D⁆ ≠ ⊥) → L₁ = L₂ := fun L₁ L₂ h1 h2 => by
    by_contra hne
    exact hno ⟨L₁, L₂, hne, h1, h2⟩
  obtain ⟨Ls, hLsD, hLsc, hgood⟩ : ∃ Ls : Subgroup G, Ls ≤ D ∧ Nat.card Ls = p ∧
      ∀ L : Subgroup G, L ≤ D → Nat.card L = p → L ≠ Ls → ⁅T ⊓ centralizer (L : Set G), D⁆ = ⊥ := by
    by_cases hb : ∃ L : Subgroup G, L ≤ D ∧ Nat.card L = p ∧ ⁅T ⊓ centralizer (L : Set G), D⁆ ≠ ⊥
    · obtain ⟨L, hL⟩ := hb
      refine ⟨L, hL.1, hL.2.1, fun L' hL' hc hne => ?_⟩
      by_contra hnb
      exact hne (hone L' L ⟨hL', hc, hnb⟩ hL)
    · push Not at hb
      have hDne : D ≠ ⊥ := by
        intro hbot
        rw [hbot, Subgroup.card_bot] at hDcard
        have := hp.one_lt
        have : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) this
        omega
      obtain ⟨⟨y, hyD⟩, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hDne
      have hy1' : y ≠ 1 := fun h => hy1 (Subtype.ext h)
      exact ⟨zpowers y, zpowers_le.mpr hyD, card_zpowers_of_isElemAbelian hp hD hyD hy1',
        fun L hL hc _ => hb L hL hc⟩
  have hTLs : T ≤ centralizer (Ls : Set G) := by
    refine le_of_forall_inf_centralizer_le_plane hp hD hDcard hDT hcop fun y hyD hy1 => ?_
    have hcz : centralizer ((zpowers y : Subgroup G) : Set G) = centralizer ({y} : Set G) := by
      rw [zpowers_eq_closure, centralizer_closure]
    by_cases heq : zpowers y = Ls
    · rw [← hcz, heq]
      exact inf_le_right
    · have hbot := hgood (zpowers y) (zpowers_le.mpr hyD)
        (card_zpowers_of_isElemAbelian hp hD hyD hy1) heq
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hbot
      rw [← hcz]
      exact hbot.trans (Subgroup.centralizer_le hLsD)
  have hLs1 : Ls = ⊥ := by
    rw [eq_bot_iff]
    intro l hl
    have := hC l (hLsD hl) fun t ht => mem_centralizer_iff.mp (hTLs ht) l hl
    exact (mem_bot).mpr this
  rw [hLs1, Subgroup.card_bot] at hLsc
  exact hp.one_lt.ne hLsc

theorem exists_elemAbelian_sup {p : ℕ} (hp : p.Prime) {Q D A E₃ : Subgroup G}
    (hD : IsElemAbelian p D) (hDQ : D ≤ Q) (hA : IsElemAbelian p A) (hAcard : Nat.card A = p ^ 2)
    (hAQ : A ≤ Q) (hAz : ∀ a ∈ A, ∀ q ∈ Q, a * q = q * a) (hE₃ : IsElemAbelian p E₃)
    (hE₃Q : E₃ ≤ Q) (hE₃c : p ^ 3 ≤ Nat.card E₃) :
    ∃ E : Subgroup G, D ≤ E ∧ E ≤ Q ∧ IsElemAbelian p E ∧ p ^ 3 ≤ Nat.card E := by
  by_cases hDA : D ≤ A
  · refine ⟨D ⊔ E₃, le_sup_left, sup_le hDQ hE₃Q, ?_, hE₃c.trans
      (Subgroup.card_le_of_le le_sup_right)⟩
    refine CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_sup_of_commuting p hD hE₃ ?_
    intro d hd
    refine mem_centralizer_iff.mpr fun e he => ?_
    exact (hAz d (hDA hd) e (hE₃Q he)).symm
  · obtain ⟨d, hdD, hdA⟩ := Set.not_subset.mp hDA
    have hdp : d ^ p = 1 := hD.2 d hdD
    have hcard : Nat.card ↥(A ⊔ zpowers d) = p ^ 3 := by
      rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers hp A hdp hdA
        (fun a ha => hAz a ha d (hDQ hdD)), hAcard]
      ring
    refine ⟨D ⊔ A, le_sup_left, sup_le hDQ hAQ, ?_, ?_⟩
    · refine CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_sup_of_commuting p hD hA ?_
      intro d' hd'
      exact mem_centralizer_iff.mpr fun a ha => hAz a ha d' (hDQ hd')
    · rw [← hcard]
      refine Subgroup.card_le_of_le (sup_le le_sup_right ?_)
      exact (zpowers_le.mpr hdD).trans le_sup_left

theorem exists_conj_le_of_isSylowOf {p : ℕ} [Fact p.Prime] {C Q E : Subgroup G}
    (hQ : CFSG.ABGLocalTools.IsSylowOf p Q C) (hEC : E ≤ C) (hE : IsPGroup p E) :
    ∃ c ∈ C, E.map (MulAut.conj c).toMonoidHom ≤ Q := by
  obtain ⟨T, hT⟩ := hQ
  have hE' : IsPGroup p (E.subgroupOf C) := hE.comap_subtype
  obtain ⟨S, hS⟩ := hE'.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.IsPretransitive.exists_smul_eq (M := C) S T
  refine ⟨c, c.2, ?_⟩
  rintro _ ⟨e, he, rfl⟩
  have heS : (⟨e, hEC he⟩ : C) ∈ S := hS he
  have hmem : (MulAut.conj c) ⟨e, hEC he⟩ ∈ ((c • S : Sylow p C) : Subgroup C) := by
    rw [sylow_conjugate_eq_map]
    exact Subgroup.mem_map_of_mem _ heS
  rw [hc] at hmem
  rw [← hT]
  exact ⟨_, hmem, rfl⟩

end CFSG.LocalAnalysis.RankFourTheoremC
