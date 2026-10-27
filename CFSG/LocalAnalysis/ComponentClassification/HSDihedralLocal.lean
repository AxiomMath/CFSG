module

public import CFSG.LocalAnalysis.ComponentClassification.HSDihedralSetup

public noncomputable section

namespace CFSG.ComponentClassification.HSDihedral

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools
open CFSG.ComponentClassification.HarrisLit

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ}

abbrev rhoOf (h : Config t L p f) {S : Subgroup X}
    (hS : IsSylowOf 2 S (centralizer ({t} : Set X))) (s : X) (hs : s ∈ S) : MulAut (Bar L) :=
  rho h ⟨s, hS.le hs⟩

theorem eq_one_of_rho_eq_one (h : Config t L p f) {S : Subgroup X}
    (hS : IsSylowOf 2 S (centralizer ({t} : Set X))) {d : X} (hd : d ∈ S ⊓ L)
    (h1 : rhoOf h hS d (mem_inf.mp hd).1 = 1) : d = 1 := by
  have hdL : d ∈ L := (mem_inf.mp hd).2
  have h2 : MulAut.conj (QuotientGroup.mk (⟨d, hdL⟩ : L) : Bar L) = 1 := by
    rw [← rho_of_mem h ⟨d, hdL⟩]
    exact h1
  have h3 : (QuotientGroup.mk (⟨d, hdL⟩ : L) : Bar L) ∈ center (Bar L) := by
    rw [mem_center_iff]
    intro y
    have := congrArg (fun φ : MulAut (Bar L) => φ y) h2
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc y * (QuotientGroup.mk (⟨d, hdL⟩ : L) : Bar L) =
        (QuotientGroup.mk (⟨d, hdL⟩ : L) : Bar L) * y * (QuotientGroup.mk (⟨d, hdL⟩ : L))⁻¹ *
          (QuotientGroup.mk (⟨d, hdL⟩ : L) : Bar L) := by rw [this]
      _ = (QuotientGroup.mk (⟨d, hdL⟩ : L) : Bar L) * y := by group
  rw [h.center_bar_eq_bot, mem_bot, QuotientGroup.eq_one_iff] at h3
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hS.isPGroup) ⟨d, (mem_inf.mp hd).1⟩
  have hdvd1 : orderOf (⟨⟨d, hdL⟩, h3⟩ : pPrimeCore 2 L) ∣ 2 ^ k := by
    apply orderOf_dvd_of_pow_eq_one
    have := pow_orderOf_eq_one (⟨d, (mem_inf.mp hd).1⟩ : S)
    rw [hk] at this
    apply Subtype.ext; apply Subtype.ext
    simpa using congrArg Subtype.val this
  have hdvd2 := orderOf_dvd_natCard (⟨⟨d, hdL⟩, h3⟩ : pPrimeCore 2 L)
  have hcop : Nat.Coprime (2 ^ k) (Nat.card (pPrimeCore 2 L)) :=
    Nat.Coprime.pow_left _ pPrimeCore_coprime_card
  have := Nat.eq_one_of_dvd_coprimes hcop hdvd1 hdvd2
  rw [orderOf_eq_one_iff] at this
  exact congrArg (fun x : pPrimeCore 2 L => ((x : L) : X)) this

theorem conj_mem_D (h : Config t L p f) {S : Subgroup X}
    (hS : IsSylowOf 2 S (centralizer ({t} : Set X))) {s d : X} (hs : s ∈ S) (hd : d ∈ S ⊓ L) :
    s * d * s⁻¹ ∈ S ⊓ L :=
  mem_inf.mpr ⟨mul_mem (mul_mem hs (mem_inf.mp hd).1) (inv_mem hs),
    (mem_normalizer_iff.mp (le_normalizer h (hS.le hs)) d).mp (mem_inf.mp hd).2⟩

end CFSG.ComponentClassification.HSDihedral
