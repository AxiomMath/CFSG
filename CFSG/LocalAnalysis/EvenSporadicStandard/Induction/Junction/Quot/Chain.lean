module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Quot.Std
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Quot.Incl
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.PGroups
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Chain.Links
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Quot.Link5a

public section

namespace CFSG.EvenSporadicStandard.Induction.Junction

open Subgroup CFSG.EvenSporadicStandard.Induction CFSG.EvenSporadicStandard.Solomon78
  CFSG.EvenSporadicStandard.Induction.Hyp
open scoped commutatorElement

variable {G : Type} [Group G]

theorem Lq_le_of_chain {Q : Type} [Group Q] {Mq : Subgroup Q} (hMq : Mq.Normal) {n : ℕ}
    {Lq Tq : ℕ → Subgroup Q} {sq : ℕ → Q} (hl : Sol78Links Q n Lq Tq sq) (hlast : Lq n = Mq) :
    ∀ i ≤ n, Lq i ≤ Mq := by
  have key : ∀ k, ∀ i, i + k = n → Lq i ≤ Mq := by
    intro k
    induction k with
    | zero =>
      intro i hi
      rw [Nat.add_zero] at hi
      rw [hi, hlast]
    | succ k ih =>
      intro i hi
      have h1 : Lq (i + 1) ≤ Mq := ih (i + 1) (by omega)
      have h2 := (hl.incl (i + 1) (by omega) (by omega)).1
      simp only [Nat.add_sub_cancel] at h2
      refine h2.trans (sup_le h1 ?_)
      rintro _ ⟨x, hx, rfl⟩
      exact hMq.conj_mem x (h1 hx) _
  exact fun i hi => key (n - i) i (by omega)

variable [Finite G] (M : Subgroup G) [M.Normal]

theorem lift_links (hMq : CFSG.IsQuasisimple ↥M)
    (hperf : ∀ P : Subgroup (CQ M), ⁅P, P⁆ = P → P ≤ M.map (cq M))
    {V T K : Subgroup G} (hV : IsPGroup 2 V) (hTn : T.Normal) (hT2 : IsPGroup 2 T)
    (hTM : T ≤ centralizer (M : Set G)) (hKM : K ≤ M)
    (hKV : IsCompIn K (centralizer (V : Set G))) {n : ℕ}
    {Lq Tq : ℕ → Subgroup (CQ M)} {sq : ℕ → CQ M} (hl : Sol78Links (CQ M) n Lq Tq sq)
    (hlast : Lq n = M.map (cq M)) (hfirst : Lq 0 = K.map (cq M)) :
    ∃ (L T' : ℕ → Subgroup G) (s : ℕ → G), Sol78Links G n L T' s ∧ L 0 = K ∧ L n = M ∧
      (∀ i, L i ≤ M) ∧ T' 0 = V ∧ (∀ i, 1 ≤ i → i ≤ n → T ≤ T' i) := by
  classical
  have hMqn : (M.map (cq M)).Normal := Subgroup.Normal.map ‹_› _ (QuotientGroup.mk'_surjective _)
  have hLM := Lq_le_of_chain hMqn hl hlast
  have hqs : ∀ i ≤ n, CFSG.IsQuasisimple ↥(Lq i) := fun i hi => (hl.comp i hi).2.isQuasisimple
  have hperfq : ∀ i ≤ n, ⁅Lq i, Lq i⁆ = Lq i := fun i hi =>
    Subgroup.isPerfect_iff.1 (hqs i hi).1
  have hMp : ⁅M, M⁆ = M := Subgroup.isPerfect_iff.1 hMq.1
  have hKq : CFSG.IsQuasisimple ↥K := hKV.isQuasisimple
  have hKp : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.1 hKq.1
  have hKmap : ⁅K.map (cq M), K.map (cq M)⁆ = K.map (cq M) := commutator_map_of_perfect _ hKp
  have hKMq : K.map (cq M) ≤ M.map (cq M) := Subgroup.map_mono hKM
  have hTk : T ≤ (cq M).ker := fun x hx => (mem_ker_cq M).2 (hTM hx)
  have hsel : ∀ i, ∃ (Ti : Subgroup G) (si : G), 1 ≤ i → i ≤ n →
      (IsPGroup 2 Ti ∧ T ≤ Ti ∧ Ti.map (cq M) = Tq i ∧ IsPGroup 2 (zpowers si) ∧
        si ∈ normalizer (Ti : Set G) ∧ cq M si = sq i ∧ si ^ 2 ∈ Ti) := by
    intro i
    by_cases hi : 1 ≤ i ∧ i ≤ n
    · obtain ⟨hp, hs, hs2, -⟩ := hl.elem i hi.1 hi.2
      obtain ⟨Ti, si, h⟩ := sylow_select (cq M) (QuotientGroup.mk'_surjective _) hT2 hTk
        (hl.comp i hi.2).1 hs hp hs2
      exact ⟨Ti, si, fun _ _ => h⟩
    · exact ⟨⊥, 1, fun h1 h2 => absurd ⟨h1, h2⟩ hi⟩
  choose Tf sf hspec using hsel
  let T' : ℕ → Subgroup G := fun i => if i = 0 then V else Tf i
  have hT'pos : ∀ i, 1 ≤ i → T' i = Tf i := fun i hi => by simp [T', Nat.pos_iff_ne_zero.1 hi]
  have hT'zero : T' 0 = V := by simp [T']
  refine ⟨fun i => lf M (Lq i), T', sf, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, fun i => lf_le M _, hT'zero, ?_⟩
  ·
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · have hL0 : lf M (Lq 0) = K := by
        rw [hfirst]
        refine eq_of_map_eq_cq M (lf_le M _) hKM (commutator_lf M hKmap hKMq) hKp ?_
        rw [map_lf M hKmap hKMq]
      rw [hT'zero, hL0]
      exact ⟨hV, hKV⟩
    · obtain ⟨hp, -, hmap, -⟩ := hspec i hpos hi
      rw [hT'pos i hpos]
      exact ⟨hp, isCompIn_lf_of_map M hmap (hLM i hi) (hqs i hi) (hl.comp i hi).2⟩
  ·
    intro i hi1 hi
    obtain ⟨hp, -, hmap, hzp, hsn, hπs, hsq⟩ := hspec i hi1 hi
    rw [hT'pos i hi1]
    refine ⟨hzp, hsn, hsq, ?_⟩
    have hel := (hl.elem i hi1 hi).2.2.2
    rw [← hπs] at hel
    exact isCompIn_lf_sup_zpowers M hmap (hLM (i - 1) (by omega)) (hqs (i - 1) (by omega)) hel
  ·
    intro i hi1 hi
    obtain ⟨hp, -, hmap, hzp, hsn, hπs, hsq⟩ := hspec i hi1 hi
    rw [hT'pos i hi1]
    have hincl := hl.incl i hi1 hi
    rw [← hπs] at hincl
    refine ⟨lf_le_lf_sup_conj M (hperfq _ (by omega)) (hperfq i hi) (hLM _ (by omega)) (hLM i hi)
      _ hincl.1, ?_⟩
    exact lf_sup_conj_eq_conjClosure M hperf hmap hsn (hqs _ (by omega)) (hqs i hi)
      (hLM _ (by omega)) (hLM i hi) (hl.comp i hi).2 hincl.1 hincl.2
  ·
    intro i hi1 hi
    obtain ⟨hp, -, hmap, hzp, hsn, hπs, hsq⟩ := hspec i hi1 hi
    have hLp := hperfq (i - 1) (by omega)
    have hLi := hperfq i hi
    rcases hl.link i hi1 hi with ⟨hne, hiso⟩ | ⟨heq, hstd⟩
    · rw [← hπs] at hne
      exact Or.inl (link5a_lf M hLp hLi (hLM _ (by omega)) (hLM i hi) _ hne hiso)
    · rw [← hπs] at heq hstd
      have hincl := (hl.incl i hi1 hi).1
      rw [← hπs] at hincl
      have hLpLi : Lq (i - 1) ≤ Lq i := by
        have : Lq i ⊔ (Lq i).map (MulAut.conj (cq M (sf i))).toMonoidHom = Lq i := by
          rw [← heq, sup_idem]
        rwa [this] at hincl
      exact Or.inr ⟨((lf_conj_eq_iff M hLi (hLM i hi) _).2 heq.symm).symm,
        jstdModulo_lf M hLp hLi (hLM _ (by omega)) (hLM i hi) hLpLi _ hstd⟩
  ·
    show lf M (Lq 0) = K
    rw [hfirst]
    refine eq_of_map_eq_cq M (lf_le M _) hKM (commutator_lf M hKmap hKMq) hKp ?_
    rw [map_lf M hKmap hKMq]
  ·
    show lf M (Lq n) = M
    rw [hlast]
    have hMmap : ⁅M.map (cq M), M.map (cq M)⁆ = M.map (cq M) := commutator_map_of_perfect _ hMp
    refine eq_of_map_eq_cq M (lf_le M _) le_rfl (commutator_lf M hMmap le_rfl) hMp ?_
    rw [map_lf M hMmap le_rfl]
  · intro i hi1 hi
    rw [hT'pos i hi1]
    exact (hspec i hi1 hi).2.1

end CFSG.EvenSporadicStandard.Induction.Junction
