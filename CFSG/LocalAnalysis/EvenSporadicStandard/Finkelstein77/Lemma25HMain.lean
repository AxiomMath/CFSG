module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Finkelstein77.Lemma25HFour

public section

namespace CFSG.EvenSporadicStandard.Finkelstein77.Lemma25HProof

open Subgroup CFSG CFSG.ABGLocalTools CFSG.ComponentClassification
  CFSG.ComponentClassification.FooteLit.F5 CFSG.EvenSporadicStandard.Finkelstein77.Lemma25Proof

@[expose] def CorB4Big : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Subgroup G),
    AschbacherTheorem3.IsDihedralTwoGroup D → 8 ≤ Nat.card D →
    (∀ x ∈ normalizer (D : Set G), x ∉ D → orderOf x = 2 →
      ∀ d ∈ D, orderOf d = 2 → ∀ g : G, g⁻¹ * x * g ≠ d) →
    ∀ P : Subgroup G, IsSylowOf 2 P (normalClosure (D : Set G)) →
      AschbacherTheorem3.IsDihedralTwoGroup P ∨ AschbacherTheorem3.IsSemidihedralTwoGroup P

theorem asc76Lemma25_of_big
    (hbig : CorB4Big) : Asc76Lemma25 := by
  intro G _ _ x hx hwc
  by_cases hnz : InZStar (x ^ 2)
  · exact Or.inl hnz
  · right
    obtain ⟨e, w, t, hd, hsic⟩ := exists_sic_datum hx hwc (exists_datum_zero hx hwc hnz)
    set D : Subgroup G := dsub w t with hD
    have hdih : AschbacherTheorem3.IsDihedralTwoGroup D :=
      ⟨e + 2, by omega, by simpa using hd.nonempty_mulEquiv_dihedral⟩
    have hsic' : ∀ y ∈ normalizer (D : Set G), y ∉ D → orderOf y = 2 →
        ∀ d ∈ D, orderOf d = 2 → ∀ g : G, g⁻¹ * y * g ≠ d := by
      intro y hyN hyD hy2 d hdD hd2 g hg
      have hd2' : d * d = 1 := by
        have := pow_orderOf_eq_one d
        rwa [hd2, sq] at this
      have hd1 : d ≠ 1 := by
        intro h
        rw [h, orderOf_one] at hd2
        omega
      have hdC : IsConj (x ^ 2) d := hd.inv_mem d hdD hd2' hd1
      have hyC : IsConj (x ^ 2) y := by
        have : y = g * d * g⁻¹ := by rw [← hg]; group
        rw [this]
        exact isConj_conj g hdC
      exact hyD (hsic y hyN hyC)
    obtain ⟨P, hP⟩ := exists_isSylowOf 2 (normalClosure (D : Set G))
    have hres : AschbacherTheorem3.IsDihedralTwoGroup P ∨
        AschbacherTheorem3.IsSemidihedralTwoGroup P := by
      rcases Nat.eq_zero_or_pos e with he | he
      · subst he
        exact Or.inl (isDihedral_of_fourgroup hx hwc hd hsic hP)
      · have h8 : 8 ≤ Nat.card D := by
          obtain ⟨φ⟩ := hd.nonempty_mulEquiv_dihedral
          rw [Nat.card_congr φ.toEquiv, DihedralGroup.nat_card]
          have : 2 ^ 1 ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
          have h2 : 2 ^ (e + 1) = 2 * 2 ^ e := by ring
          omega
        exact hbig G D hdih h8 hsic' P hP
    rw [hD, normalClosure_dsub hd] at hP
    obtain ⟨Q, hQ⟩ := hP.exists_sylow_eq_subgroupOf
    have hequiv : ↥(Q : Subgroup (normalClosure {x ^ 2} : Subgroup G)) ≃* ↥P :=
      (MulEquiv.subgroupCongr hQ).trans (Subgroup.subgroupOfEquivOfLe hP.le)
    rcases hres with ⟨n, hn, ⟨φ⟩⟩ | ⟨n, hn, ⟨φ⟩⟩
    · exact Or.inl ⟨Q, n, hn, ⟨hequiv.trans φ⟩⟩
    · exact Or.inr ⟨Q, n, hn, ⟨hequiv.trans φ⟩⟩

end CFSG.EvenSporadicStandard.Finkelstein77.Lemma25HProof
