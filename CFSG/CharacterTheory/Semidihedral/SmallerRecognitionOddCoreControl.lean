module

public import CFSG.CharacterTheory.Semidihedral.DegreeThreeMathieuOddCore
public import CFSG.CharacterTheory.Semidihedral.Local.CentralizerOddCoreAction

public section

namespace CFSG.Semidihedral.SmallerRecognitionOddCoreControl

open CFSG.Open
open CFSG.Semidihedral.ProperSubgroupRegularity

@[expose] def centralizerInfEquiv {Q : Type*} [Group Q] (L : Subgroup Q) (y : L) :
    Subgroup.centralizer ({y} : Set L) ≃*
      ↥(L ⊓ Subgroup.centralizer ({(y : Q)} : Set Q)) where
  toFun c := ⟨((c : L) : Q), (c : L).2, by
    have hc := Subgroup.mem_centralizer_singleton_iff.mp c.2
    exact Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hc)⟩
  invFun d := ⟨⟨d, d.2.1⟩, by
    have hd := Subgroup.mem_centralizer_singleton_iff.mp d.2.2
    exact Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext hd)⟩
  left_inv c := rfl
  right_inv d := rfl
  map_mul' c d := rfl

theorem pPrimeCore_inf_centralizer_le_center {Q : Type*} [Group Q] (L : Subgroup Q) (y : L)
    (h : CFSG.pPrimeCore 2 (Subgroup.centralizer ({y} : Set L)) ≤
      Subgroup.center (Subgroup.centralizer ({y} : Set L))) :
    CFSG.pPrimeCore 2 ↥(L ⊓ Subgroup.centralizer ({(y : Q)} : Set Q)) ≤
      Subgroup.center ↥(L ⊓ Subgroup.centralizer ({(y : Q)} : Set Q)) := by
  set θ := centralizerInfEquiv L y
  have hmap := CFSG.pPrimeCore_map_iso 2 θ
  intro g hg
  rw [← hmap] at hg
  obtain ⟨c, hc, rfl⟩ := hg
  have hcen := h hc
  rw [Subgroup.mem_center_iff] at hcen ⊢
  intro a
  obtain ⟨b, rfl⟩ := θ.surjective a
  change θ b * θ c = θ c * θ b
  rw [← map_mul, ← map_mul, hcen b]

theorem degree_three_or_mathieu_of_smallerSimpleModel {A : Type} [Group A]
    (h : SmallerSimpleModel A) :
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
        CFSG.Assembly.LowTwoRank.StatedClassicalModel A .PSL 3 p f) ∨
      (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
        CFSG.Assembly.LowTwoRank.StatedClassicalModel A .PSU 3 p f) ∨
      Nonempty (A ≃* CFSG.Assembly.LowTwoRank.StatedM11) := by
  have hne : ∀ l : ℕ, Odd l → l ≠ 2 := by
    rintro l hl rfl
    exact absurd hl (by decide)
  rcases h with ⟨l, a, hl, hlodd, ha, -, hm⟩ | ⟨l, a, hl, hlodd, ha, -, hm⟩ | hm
  · exact Or.inl ⟨l, a, hl, hne l hlodd, ha, hm⟩
  · exact Or.inr (Or.inl ⟨l, a, hl, hne l hlodd, ha, hm⟩)
  · exact Or.inr (Or.inr hm)

theorem smaller_simple_recognition_produces_proper_subgroup_odd_core_control
    (X : Type) [Group X] [Finite X] (hrecognition : SmallerSimpleRecognition X)
    (H : Subgroup X) (hproper : H ≠ ⊤) (hH : ∀ U : Subgroup H, U.index ≠ 2)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 H) (fS : SemidihedralGroup n ≃* S) :
    ∀ t : H, orderOf t = 2 → ∀ P : Subgroup H, P ≤ Subgroup.centralizer {t} → IsPGroup 2 P →
      ⁅P, (CFSG.pPrimeCore 2 (Subgroup.centralizer ({t} : Set H))).map
        (Subgroup.centralizer ({t} : Set H)).subtype⁆ ≤ CFSG.pPrimeCore 2 H := by
  intro t ht P hPt hP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := CFSG.pPrimeCore 2 H with hR
  obtain ⟨-, L, ⟨hLn, -, -⟩, -, hsimple, hnonab, -, hodd, -, hsylow, hcard, -⟩ :=
    CFSG.Semidihedral.Local.semidihedral_odd_core_quotient_simple_odd_index_subgroup hH n hn S fS
  have : L.Normal := hLn
  have ht2 : t ^ 2 = 1 := ht ▸ pow_orderOf_eq_one t
  have hL2 : ¬ 2 ∣ L.index := Nat.odd_iff.mp hodd |> fun h => by omega
  have hHX : Nat.card H < Nat.card X := by
    rw [← Subgroup.card_top (G := X)]
    exact Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hproper)
  have hLX : Nat.card L < Nat.card X := lt_of_le_of_lt hcard hHX
  obtain ⟨T⟩ : Nonempty (Sylow 2 L) := inferInstance
  obtain ⟨eT⟩ := hsylow T
  have hmodel := degree_three_or_mathieu_of_smallerSimpleModel
    (hrecognition L hnonab hLX n hn T ⟨eT⟩)
  have hcentral :=
    (DegreeThreeMathieuOddCore.degree_three_and_Mathieu_model_centralizer_odd_core_central
      L hmodel).1
  have htL : QuotientGroup.mk' R t ∈ L :=
    CFSG.Semidihedral.Local.mem_of_pow_eq_one_of_index L hL2 (k := 1) (by
      rw [← map_pow, pow_one, ht2, map_one])
  have hRodd : Odd (Nat.card R) :=
    Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := H))
  have htR : t ∉ R := by
    intro htR
    have hdvd : orderOf (⟨t, htR⟩ : R) ∣ Nat.card R := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, ht] at hdvd
    exact (Nat.not_even_iff_odd.mpr hRodd) (even_iff_two_dvd.mpr hdvd)
  have hord : orderOf (⟨QuotientGroup.mk' R t, htL⟩ : L) = 2 := by
    rw [Subgroup.orderOf_mk]
    apply orderOf_eq_prime
    · rw [← map_pow, ht2, map_one]
    · intro h1
      exact htR ((QuotientGroup.eq_one_iff t).mp h1)
  have hcore := hcentral _ hord
  rw [CFSG.Wreathed.weakClosure_oddCore_eq_pPrimeCore] at hcore
  have hcore' := pPrimeCore_inf_centralizer_le_center L _ hcore
  exact CFSG.Semidihedral.Local.centralizer_odd_core_action_from_odd_index_subgroup 2 R
    (fun h2 => (Nat.not_even_iff_odd.mpr hRodd) (even_iff_two_dvd.mpr h2)) L hL2 t
    ⟨1, by rw [ht, pow_one]⟩ hcore' P hPt hP

end CFSG.Semidihedral.SmallerRecognitionOddCoreControl
