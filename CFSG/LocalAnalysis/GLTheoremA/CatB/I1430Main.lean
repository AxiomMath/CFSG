module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430Lift
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430Trans

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S8.L84

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

theorem I1430At_of_facts (G : Type) [Group G] [Finite G]
    (hCls : I1430Cls) (hA : I1430M23Alt) (hS : I1430M23Suz) (hO : I1430M23ON) (hC : I1430M23Chev) :
    I1430At G := by
  intro X E D J I hX hEX hE hE27 hDE hD9 hXD hJ hEJ hI hIt hnot hrk
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  have hJX : J ≤ X := hJ.1
  have hJQ : CFSG.Open.IsQuasisimple (PQuot 3 J) := isQuasisimple_pQuot_of_glaPComponent hp hJ
  have hXJ : CFSG.Open.IsKGroup ↥J := CFSG.Open.IsKGroup.of_le hX hJ.1
  have hKq : CFSG.Open.IsKGroup (PQuot 3 J) := CFSG.Open.IsKGroup.quotient hXJ _
  have hcatJ : IsCatalogGroup (PSimple 3 J) :=
    CFSG.LocalAnalysis.GLTheoremA.I2611.isCatalogGroup_center_quotient' hKq hJQ
  have hDel : IsElemAbelian 3 D := isElemAbelian_mono hE hDE
  have hDJ : ∀ d ∈ D, ∀ j ∈ J, d * j = j * d := fun d hd j hj =>
    Subgroup.mem_centralizer_iff.1 (hXD (hJX hj)) d hd
  obtain ⟨x, hxE, hxD⟩ : ∃ x ∈ E, x ∉ D := by
    by_contra h
    push_neg at h
    have h1 : Nat.card E ≤ Nat.card D := Subgroup.card_le_of_le h
    rw [hE27, hD9] at h1
    norm_num at h1
  have hx3 : x ^ 3 = 1 := hE.2 x hxE
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact hxD (D.one_mem)
  have hxJ : x ∈ Subgroup.normalizer (J : Set G) := hEJ hxE
  have hxD_comm : ∀ d ∈ D, d * x = x * d := fun d hd =>
    isElemAbelian_commute hE (hDE hd) hxE
  have hxnorm : x ∈ Subgroup.normalizer (D : Set G) := mem_normalizer_of_commute
    (fun d hd => (hxD_comm d hd).symm)
  have hcardx : Nat.card (Subgroup.zpowers x) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hx3 hx1]
  have hcard_mul := card_sup_mul_card_inf_of_le_normalizer (A := D) (B := Subgroup.zpowers x)
    (Subgroup.zpowers_le.2 hxnorm)
  rw [hD9, hcardx] at hcard_mul
  have hsupE : D ⊔ Subgroup.zpowers x ≤ E := sup_le hDE
    (Subgroup.zpowers_le.2 hxE)
  have hsupE_card : Nat.card ↥(D ⊔ Subgroup.zpowers x) ≤ Nat.card E :=
    Subgroup.card_le_of_le hsupE
  have hsubD : D ≤ D ⊔ Subgroup.zpowers x := le_sup_left
  have hne9 : Nat.card ↥(D ⊔ Subgroup.zpowers x) ≠ Nat.card D := by
    intro heq
    have hDeq : D = D ⊔ Subgroup.zpowers x :=
      Subgroup.eq_of_le_of_card_ge hsubD (le_of_eq heq)
    have hxmem : x ∈ D ⊔ Subgroup.zpowers x := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
    rw [← hDeq] at hxmem
    exact hxD hxmem
  have hge9 : Nat.card D ≤ Nat.card ↥(D ⊔ Subgroup.zpowers x) := Subgroup.card_le_of_le hsubD
  have hgt9 : 9 < Nat.card ↥(D ⊔ Subgroup.zpowers x) := by
    rw [hD9] at hge9 hne9
    norm_num at hge9 hne9
    omega
  have hdvd : Nat.card ↥(D ⊔ Subgroup.zpowers x) ∣ 3 ^ 3 :=
    ⟨Nat.card ↥(D ⊓ Subgroup.zpowers x), by rw [hcard_mul]; norm_num⟩
  obtain ⟨i, hi, hieq⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
  have hi3 : i = 3 := by
    rw [hieq] at hgt9
    interval_cases i <;> first | rfl | norm_num at hgt9
  have hcardsup : Nat.card ↥(D ⊔ Subgroup.zpowers x) = 27 := by
    rw [hieq, hi3]
    norm_num
  have hEeq : D ⊔ Subgroup.zpowers x = E :=
    Subgroup.eq_of_le_of_card_ge hsupE (by rw [hcardsup, hE27]; norm_num)
  have hCE : J ⊓ Subgroup.centralizer (E : Set G) = J ⊓ Subgroup.centralizer ({x} : Set G) := by
    ext j
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨hj, hjE⟩
      refine ⟨hj, ?_⟩
      have h1 := Subgroup.mem_centralizer_iff.1 hjE x hxE
      exact Subgroup.mem_centralizer_iff.2 (fun h hh => by
        rw [Set.mem_singleton_iff.1 hh]
        exact h1)
    · rintro ⟨hj, hjx⟩
      refine ⟨hj, ?_⟩
      have h1 : x * j = j * x := Subgroup.mem_centralizer_iff.1 hjx x (Set.mem_singleton x)
      have hsub : D ⊔ Subgroup.zpowers x ≤ Subgroup.centralizer ({j} : Set G) := by
        apply sup_le
        · intro d hd
          refine Subgroup.mem_centralizer_iff.2 (fun h hh => ?_)
          rw [Set.mem_singleton_iff.1 hh]
          exact (hDJ d hd j hj).symm
        · apply Subgroup.zpowers_le.2
          refine Subgroup.mem_centralizer_iff.2 (fun h hh => ?_)
          rw [Set.mem_singleton_iff.1 hh]
          exact h1.symm
      apply Subgroup.mem_centralizer_iff.2
      intro e he
      rw [← hEeq] at he
      have := hsub he
      exact (Subgroup.mem_centralizer_iff.1 this j (Set.mem_singleton j)).symm
  have hI' : GLAPComponent 3 (J ⊓ Subgroup.centralizer ({x} : Set G)) I := by
    rw [← hCE]
    exact hI
  have hD9' : Nat.card D = 9 := by rw [hD9]; norm_num
  have hcenter : ∀ z ∈ Subgroup.center (PQuot 3 J), ∃ n : ℕ, z ^ 3 ^ n = 1 :=
    CFSG.LocalAnalysis.GLTheoremA.I106TGroup.center_pQuot_three_pow J
  have key : I1430TwoLocal (PQuot 3 J) (3 + CFSG.Open.pRank 3 (Subgroup.center (PQuot 3 J))) →
      False := by
    intro hw
    have := two_local_lift hDel hD9' hDJ hw
    omega
  obtain ⟨Q, instQ, instF, K, I', y, e, hmod, hinner⟩ :=
    model_of_component hJQ hcatJ hx3 hxJ hI' hIt hnot
  obtain ⟨hOut, hOcard, hSp⟩ := hCls Q K I' y hmod
  have hOutJ : catalogIs (PSimple 3 J) I1430Out := catalogIs_center_quot_of_equiv e I1430Out hOut
  have hO1 : catalogIs (PSimple 3 J) (sporIs .ONan) → Nat.card (Subgroup.center (PQuot 3 J)) = 1 := by
    intro h
    rw [← card_center_eq_of_equiv e]
    exact hOcard (catalogIs_center_quot_of_equiv e.symm _ h)
  obtain ⟨i, hi, hiso⟩ := hOutJ
  unfold T1430
  rcases hi with h1 | ⟨n, hn, hAn⟩ | hSuz | hON | ⟨ℓ, hℓ, hB⟩
  · refine ⟨⟨i, h1, hiso⟩, fun hsp => ⟨x, hxE, fun hInner => ?_⟩⟩
    exact hSp (catalogIs_center_quot_of_equiv e.symm _ hsp) (hinner hInner)
  · exact (key (hA (PQuot 3 J) hJQ hcenter n hn ⟨i, hAn, hiso⟩)).elim
  · exact (key (hS (PQuot 3 J) hJQ hcenter ⟨i, hSuz, hiso⟩)).elim
  · exact (key (hO (PQuot 3 J) hJQ hcenter ⟨i, hON, hiso⟩ (hO1 ⟨i, hON, hiso⟩))).elim
  · exact (key (hC (PQuot 3 J) hJQ hcenter ℓ hℓ ⟨i, hB, hiso⟩)).elim

end CFSG.LocalAnalysis.GLTheoremA.S8.L84
