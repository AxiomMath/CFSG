module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3BL34Outer
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma511L34
import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.RankThree.PartTwo.KFacts.L34

theorem le_pRank_of_elemAbelian {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : 1 < p)
    {H E : Subgroup G} (hEH : E ≤ H) (hE : CFSG.Open.IsElemAbelian p E) {k : ℕ}
    (hk : Nat.card E = p ^ k) : k ≤ CFSG.Open.pRank p H := CFSG.SectionRank.le_pRank hp hEH hE hk

theorem exists_equiv_projectiveSL {Y : Type} [Group Y] (h : IsLThreeFour Y) :
    ∃ (k : Type) (_ : Field k), Nat.card k = 4 ∧ Nonempty (Y ≃* projectiveSL 3 k) := by
  obtain ⟨F, hF, _, hcard, ⟨e⟩⟩ := h
  exact ⟨F, hF, hcard, ⟨(e.trans
    (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 F).symm).trans
    (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 F)⟩⟩

theorem l3b34_isElemAbelian_map {A B : Type*} [Group A] [Group B] (ψ : A ≃* B) {E : Subgroup A}
    (hE : CFSG.Open.IsElemAbelian 3 E) :
    CFSG.Open.IsElemAbelian 3 (E.map ψ.toMonoidHom) := CFSG.Open.IsElemAbelian.map hE _

theorem mem_normalizer_map {A B : Type*} [Group A] [Group B] (ψ : A ≃* B) {S : Subgroup A} {e : A}
    (he : e ∈ Subgroup.normalizer (S : Set A)) :
    ψ e ∈ Subgroup.normalizer ((S.map ψ.toMonoidHom : Subgroup B) : Set B) := by
  rw [Subgroup.mem_normalizer_iff] at he ⊢
  intro h
  rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv]
  have := he (ψ.symm h)
  simpa [map_mul, map_inv] using this

theorem inputL34AutInner_holds : LocalBalance.Lemma511L34Ns.InputL34AutInner := by
  intro Y _ _ hY E S x hE hE9 hinn hx1 hxE hS hN
  obtain ⟨k, _, hk, ⟨φ⟩⟩ := exists_equiv_projectiveSL hY
  have hfin : Finite k := CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour.finite_of_card_eq_four hk
  set ψ : MulAut Y ≃* MulAut (projectiveSL 3 k) := MulAut.congr φ with hψ
  have hE9' : Nat.card (E.map ψ.toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective ψ.injective, hE9]
  have hinn' : E.map ψ.toMonoidHom ≤
      (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k)).range := by
    rintro _ ⟨e, he, rfl⟩
    obtain ⟨y, hy⟩ := hinn he
    refine ⟨φ y, ?_⟩
    show MulAut.conj (φ y) = ψ e
    rw [← hy, hψ, CFSG.RankThree.PartTwo.KFacts.congr_mulAutConj]
  have hxE' : MulAut.conj (φ x) ∈ E.map ψ.toMonoidHom :=
    ⟨MulAut.conj x, hxE, by
      show ψ (MulAut.conj x) = _
      rw [hψ, CFSG.RankThree.PartTwo.KFacts.congr_mulAutConj]⟩
  have hS' : ¬ 3 ∣ Nat.card (S.map ψ.toMonoidHom) := by
    rw [Subgroup.card_map_of_injective ψ.injective]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hS
  have hN' : E.map ψ.toMonoidHom ≤
      Subgroup.normalizer ((S.map ψ.toMonoidHom : Subgroup _) : Set (MulAut (projectiveSL 3 k))) := by
    rintro _ ⟨e, he, rfl⟩
    exact mem_normalizer_map ψ (hN he)
  intro s hs c hc
  have key := inner_core hk hE9' hinn' (by simpa using hx1) hxE' hS' hN' (ψ s) ⟨s, hs, rfl⟩ (φ c)
    (by rw [← map_mul, ← map_mul, hc])
  have : ψ s (φ c) = φ (s c) := by
    rw [hψ]; simp [MulAut.congr_apply]
  rw [this] at key
  exact φ.injective key

theorem inputL34AutOuter_holds : LocalBalance.Lemma511L34Ns.InputL34AutOuter := by
  intro Y _ _ hY E E' S x hEE hE' hE9 hx1 hxE' hS hcomm
  obtain ⟨k, _, hk, ⟨φ⟩⟩ := exists_equiv_projectiveSL hY
  have hfin : Finite k := CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour.finite_of_card_eq_four hk
  have hrank := pRank_mulAut_le_two_of_isLThreeFour hY
  have hE'p : IsPGroup 3 E' := fun y => ⟨1, by rw [pow_one]; exact Subtype.ext (hE'.2 y y.2)⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 3)).1 hE'p
  have hn2 : n ≤ 2 := (le_pRank_of_elemAbelian (by norm_num) le_top hE' hn).trans hrank
  have hle : 9 ≤ Nat.card E' := by
    rw [← hE9]; exact Subgroup.card_le_of_le hEE
  have hEE' : E = E' := by
    have h3n : 3 ^ n ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hn2
    exact Subgroup.eq_of_le_of_card_ge hEE (by rw [hn]; omega)
  subst hEE'
  set ψ : MulAut Y ≃* MulAut (projectiveSL 3 k) := MulAut.congr φ with hψ
  have hE9' : Nat.card (E.map ψ.toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective ψ.injective, hE9]
  have hxE'' : MulAut.conj (φ x) ∈ E.map ψ.toMonoidHom :=
    ⟨MulAut.conj x, hxE', by
      show ψ (MulAut.conj x) = _
      rw [hψ, CFSG.RankThree.PartTwo.KFacts.congr_mulAutConj]⟩
  have hS' : ¬ 3 ∣ Nat.card (S.map ψ.toMonoidHom) := by
    rw [Subgroup.card_map_of_injective ψ.injective]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hS
  have hcomm' : ∀ e ∈ E.map ψ.toMonoidHom, ∀ t ∈ S.map ψ.toMonoidHom, t * e = e * t := by
    rintro _ ⟨e, he, rfl⟩ _ ⟨t, ht, rfl⟩
    show ψ t * ψ e = ψ e * ψ t
    rw [← map_mul, ← map_mul, hcomm e he t ht]
  intro s hs c hc
  have key := outer_core hk (l3b34_isElemAbelian_map ψ hE') hE9' (by simpa using hx1) hxE'' hS' hcomm'
    (ψ s) ⟨s, hs, rfl⟩ (φ c) (by rw [← map_mul, ← map_mul, hc])
  have : ψ s (φ c) = φ (s c) := by
    rw [hψ]; simp [MulAut.congr_apply]
  rw [this] at key
  exact φ.injective key

end CFSG.HardMathSupport.Solomon.Coordinator
