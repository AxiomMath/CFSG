module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X10Sp4Sq
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X10SpTwo
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4X81Conf
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X10R

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.UnbalancedLayer
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

namespace X10Rec

variable {H : Type} [Group H] [Finite H] {h : Hyp59 H} {H₁ : h.L81Hyp}

theorem conf_of (d : H₁.Data) {p f : ℕ}
    (hJ : Blueprint.LieModel (h.J ⧸ pPrimeCore 2 h.J) .PSL 2 p (2 * f))
    (hK : Blueprint.LieModel (h.K ⧸ pPrimeCore 2 h.K) .PSp 2 p f) :
    Conf H (generalizedFitting H) p f := by
  have F := d.fstarFacts
  exact ⟨F.normal, F.centralizer_eq, F.simple, h.a, d.b, h.J, h.K, h.P, h.orderOf_a, d.b_ord,
    F.a_mul_b, F.J_le, h.J_le, h.isPComponent_J, hJ, F.b_mem, F.P_le, F.P_sylow,
    ⟨d.p, d.p_mem, d.card_P.symm⟩, F.K_le_V.trans F.V_le, F.K_ne, F.K_le_C,
    F.isPComponent_K, hK⟩

theorem exists_not_comm_of_isQuasisimple {X : Type*} [Group X] (hX : IsQuasisimple X) :
    ∃ x y : X, x * y ≠ y * x := by
  obtain ⟨-, -, x, y, hxy⟩ := hX
  obtain ⟨x', rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective y
  exact ⟨x', y', fun h => hxy (by rw [← QuotientGroup.mk_mul, h, QuotientGroup.mk_mul])⟩

theorem five_le_of_three_lt {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : 3 < p ^ f) :
    5 ≤ p ^ f := by
  have hodd : p ^ f % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2).pow
  omega

theorem cf81Exit10Recognition_of
    (hGLS : CatLeaf.GLS3OddLieAutComponentsInput) (hO : CatLeaf.LieOrderFormulasInput)
    (hExc : CF81X10RowExc) (hLin : CF81X10RowLin) (hSpHigh : CF81X10RowSpHigh)
    (hOrth : CF81X10RowOrth) : CF81Exit10Recognition := by
  intro H _ _ h H₁ d v _ p f hp hp2 hf hJ hK hq hM
  have F := d.fstarFacts
  have : (generalizedFitting H).Normal := F.normal
  have : IsSimpleGroup ↥(generalizedFitting H) := F.simple
  have h5 := five_le_of_three_lt hp hp2 hq
  have hKM : h.K ≤ generalizedFitting H := F.K_le_V.trans F.V_le
  have hconf := conf_of d hJ hK
  have hKcard := CatFactsSp4.two_mul_card_of_lieModel_psp hp2 hK
  have hKleM : Nat.card (↥h.K ⧸ pPrimeCore 2 ↥h.K) ∣ Nat.card ↥(generalizedFitting H) :=
    (Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_dvd_of_le hKM)
  rcases hM with hodd | hM11
  swap
  ·
    exfalso
    obtain ⟨e⟩ : Nonempty (↥(generalizedFitting H) ≃* ↥Blueprint.NativeSporadic.M11) := hM11
    have h1 : Nat.card ↥(generalizedFitting H) ∣ 39916800 :=
      (Nat.card_congr e.toEquiv) ▸ card_M11_dvd
    have hq2 : Nat.Coprime ((p ^ f) ^ 4) 2 :=
      Nat.Coprime.pow_left 4 (Nat.coprime_two_right.mpr (hp.odd_of_ne_two hp2).pow)
    have h2 : (p ^ f) ^ 4 ∣ Nat.card (↥h.K ⧸ pPrimeCore 2 ↥h.K) :=
      hq2.dvd_of_dvd_mul_right (hKcard ▸ dvd_mul_right _ _)
    exact not_pow_four_dvd h5 (Nat.odd_iff.mp (hp.odd_of_ne_two hp2).pow)
      (h2.trans (hKleM.trans h1))
  obtain ⟨τ, n, r, f', hr, hr2, hadm, hmod⟩ := hodd
  have hna := exists_not_comm_of_isQuasisimple F.isComponent.1
  obtain ⟨hβ2, hβ1⟩ := conjNormal_involutive F.centralizer_eq d.b_ord
  obtain ⟨hα2, hα1⟩ := conjNormal_involutive F.centralizer_eq h.orderOf_a
  obtain ⟨K', hK'p, ⟨eK⟩⟩ := fixed_pComponent hKM F.K_le_C F.isPComponent_K
  obtain ⟨J', hJ'p, ⟨eJ⟩⟩ := fixed_pComponent F.J_le h.J_le h.isPComponent_J
  have hK'm : Blueprint.LieModel (↥K' ⧸ pPrimeCore 2 ↥K') .PSp 2 p f :=
    LieType.CurtisTits.lieModel_of_mulEquiv
      (QuotientGroup.congr _ _ eK.symm (pPrimeCore_map_iso 2 eK.symm)) hK
  have hJ'm : Blueprint.LieModel (↥J' ⧸ pPrimeCore 2 ↥J') .PSL 2 p (2 * f) :=
    LieType.CurtisTits.lieModel_of_mulEquiv
      (QuotientGroup.congr _ _ eJ.symm (pPrimeCore_map_iso 2 eJ.symm)) hJ
  obtain rfl : r = p :=
    char_eq_of_fixed_psp hGLS hO hna hr hr2 hadm hmod hβ2 hβ1 hK'p hp hp2 h5 hK'm
  cases τ with
  | PSL =>
    obtain ⟨hk, -⟩ := hLin _ .PSL n r f' f hr hr2 (Or.inl rfl) hadm hmod hf h5 _ hβ2 hβ1 K' hK'p
    rcases hk hK'm with ⟨rfl, rfl⟩ | hn5
    · exact Or.inr ⟨r, f', hr, hr2, hf, Or.inl hJ, Or.inl hmod⟩
    · exact absurd hJ'm
        ((hLin _ .PSL n r f' f hr hr2 (Or.inl rfl) hadm hmod hf h5 _ hα2 hα1 J' hJ'p).2 hn5)
  | PSU =>
    obtain ⟨hk, -⟩ := hLin _ .PSU n r f' f hr hr2 (Or.inr rfl) hadm hmod hf h5 _ hβ2 hβ1 K' hK'p
    rcases hk hK'm with ⟨rfl, rfl⟩ | hn5
    · exact Or.inr ⟨r, f', hr, hr2, hf, Or.inl hJ, Or.inr hmod⟩
    · exact absurd hJ'm
        ((hLin _ .PSU n r f' f hr hr2 (Or.inr rfl) hadm hmod hf h5 _ hα2 hα1 J' hJ'p).2 hn5)
  | PSp =>
    by_cases hn2 : n = 2
    ·
      subst hn2
      obtain rfl := X10Sp4.cf81X10RowSpTwo _ r f' f hr hr2 hmod hf h5 _ hβ2 hβ1 K' hK'p hK'm
      exact absurd hmod (X10Sp4.cf81X10RowSp4Sq H _ r f hr hr2 hf hq hconf)
    · have hn3 : 3 ≤ n := by
        have := hadm.2.2.1
        omega
      have hn4 := (hSpHigh _ n r f' f hr hr2 hn3 hadm hmod hf h5 _ hβ2 hβ1 K' hK'p).1 hK'm
      exact absurd hJ'm ((hSpHigh _ n r f' f hr hr2 hn3 hadm hmod hf h5 _ hα2 hα1 J' hJ'p).2 hn4)
  | POmegaOdd =>
    exact absurd hmod (hOrth H _ .POmegaOdd n r f' f hr hr2 hf hq hconf (Or.inl rfl) hadm)
  | POmegaPlus =>
    exact absurd hmod (hOrth H _ .POmegaPlus n r f' f hr hr2 hf hq hconf (Or.inr (Or.inl rfl))
      hadm)
  | POmegaMinus =>
    exact absurd hmod (hOrth H _ .POmegaMinus n r f' f hr hr2 hf hq hconf (Or.inr (Or.inr rfl))
      hadm)
  | G2 =>
    obtain rfl : n = 0 := hadm.2.2.1
    exact absurd hK'm (hExc _ _ r f' f hr hr2 (Or.inl (by decide)) hadm hmod hf h5 _ hβ2 hβ1 K'
      hK'p)
  | F4 | E6 | E7 | E8 | twistedE6 | trialityD4 =>
    obtain rfl : n = 0 := hadm.2.2
    exact absurd hK'm (hExc _ _ r f' f hr hr2 (Or.inl (by decide)) hadm hmod hf h5 _ hβ2 hβ1 K'
      hK'p)
  | twistedG2 =>
    obtain rfl : n = 0 := hadm.2.2.1
    exact absurd hK'm (hExc _ _ r f' f hr hr2 (Or.inr rfl) hadm hmod hf h5 _ hβ2 hβ1 K' hK'p)
  | twistedB2 => exact absurd hadm.2.2.2.1 hr2
  | twistedF4 => exact absurd hadm.2.2.2.1 hr2
  | Tits => exact absurd hadm.2.2.2.1 hr2

end X10Rec

end CFSG.ComponentClassification.GSThmB
