module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5Asc25Four
public import CFSG.LocalAnalysis.ComponentClassification.Foote5Asc25Eight

public section

namespace CFSG.ComponentClassification.Foote5.Asc25

open CFSG Subgroup CFSG.ABGLocalTools CFSG.EvenSporadicStandard.Finkelstein77
  CFSG.EvenSporadicStandard.Finkelstein77.Lemma25Proof

theorem asc76Lemma25 :
    Asc76Lemma25 := by
  intro G _ _ x hx hwc
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hnz : InZStar (x ^ 2)
  · exact Or.inl hnz
  right
  obtain ⟨e, w, t, hd, hsic⟩ := exists_sic_datum hx hwc (exists_datum_zero hx hwc hnz)
  set D : Subgroup G := dsub w t with hD
  obtain ⟨eD⟩ := hd.nonempty_mulEquiv_dihedral
  have hdih : AschbacherTheorem3.IsDihedralTwoGroup D :=
    ⟨e + 2, by omega, by simpa using hd.nonempty_mulEquiv_dihedral⟩
  have hcardD : Nat.card D = 2 * 2 ^ (e + 1) := by
    rw [Nat.card_congr eD.toEquiv, DihedralGroup.nat_card]
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
    rcases Nat.eq_zero_or_pos e with rfl | he
    ·
      have hD4 : Nat.card D = 4 := by rw [hcardD]; rfl
      have hsq : ∀ d ∈ D, d * d = 1 := by
        intro d hdD
        have h1 : ∀ g : DihedralGroup 2, g * g = 1 := by decide
        have h2 := h1 (eD ⟨d, hdD⟩)
        rw [← map_mul, ← map_one eD] at h2
        exact congrArg Subtype.val (eD.injective h2)
      have hD𝒞 : ∀ d ∈ D, d ≠ 1 → IsConj (x ^ 2) d := fun d hdD hd1 =>
        hd.inv_mem d hdD (hsq d hdD) hd1
      rcases fourgroup_cases hx hwc hD4 hD𝒞 hsic with h1 | h1
      · left
        obtain ⟨g, -, hg⟩ := h1.exists_mem_conj hP
        have hPmap : P = D.map (MulAut.conj g).toMonoidHom := by
          ext y
          rw [hg y, mem_map_equiv]
          simp
        have eP : ↥D ≃* ↥P := (D.equivMapOfInjective _ (MulAut.conj g).injective).trans
          (MulEquiv.subgroupCongr hPmap.symm)
        exact ⟨2, le_rfl, ⟨eP.symm.trans eD⟩⟩
      · left
        obtain ⟨φ⟩ := h1 P hP
        exact ⟨3, by omega, ⟨φ⟩⟩
    · refine dihedral_or_semidihedral hdih ?_ hsic' hP
      rw [hcardD]
      have : 2 ^ 1 ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
      rw [pow_succ]
      omega
  rw [hD, normalClosure_dsub hd] at hP
  obtain ⟨Q, hQ⟩ := hP.exists_sylow_eq_subgroupOf
  have hequiv : ↥(Q : Subgroup (normalClosure {x ^ 2} : Subgroup G)) ≃* ↥P :=
    (MulEquiv.subgroupCongr hQ).trans (Subgroup.subgroupOfEquivOfLe hP.le)
  rcases hres with ⟨n, hn, ⟨φ⟩⟩ | ⟨n, hn, ⟨φ⟩⟩
  · exact Or.inl ⟨Q, n, hn, ⟨hequiv.trans φ⟩⟩
  · exact Or.inr ⟨Q, n, hn, ⟨hequiv.trans φ⟩⟩

end CFSG.ComponentClassification.Foote5.Asc25
