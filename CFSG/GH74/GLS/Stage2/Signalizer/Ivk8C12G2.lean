module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8C12D4
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8C12Sl2
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8C12Cbar
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8C12G2Aut

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Signalizer.Odd87
  CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.Open
open scoped MatrixGroups

theorem not_pow6_dvd_fact (p : ℕ) (hp3 : 3 ≤ p) : ¬ p ^ 6 ∣ Nat.factorial 11 := by
  intro h
  by_cases hp : p < 20
  · have : ∀ q < 20, 3 ≤ q → ¬ q ^ 6 ∣ Nat.factorial 11 := by decide
    exact this p hp hp3 h
  · have h20 : 20 ^ 6 ≤ p ^ 6 := Nat.pow_le_pow_left (by omega) 6
    have := Nat.le_of_dvd (by positivity) h
    have h11 : Nat.factorial 11 < 20 ^ 6 := by decide
    omega

theorem shape_cbar_false {A : Type} [Group A] [Finite A] {zb : A} {Sb Vb : Subgroup A}
    (hfr : AFrame A zb Sb Vb) {Y : Type} [Group Y] (ι : Y →* A) (hι : Function.Injective ι)
    {t : A} (ht : orderOf t = 2) (hcomm : ∀ y : Y, ι y * t = t * ι y) {F : Type} [Field F]
    [Finite F] (S : Shape Y F F) (hq : Nat.card F = 7 ∨ Nat.card F = 9 ∨ Nat.card F = 11) :
    False := by
  have hodd : Odd (Nat.card F) := by rcases hq with h | h | h <;> rw [h] <;> decide
  have h4 : 4 ≤ Nat.card F := by omega
  set I₁ : Subgroup A := S.I₁.map ι with hI₁
  set I₂ : Subgroup A := S.I₂.map ι with hI₂
  have e₁ : ↥I₁ ≃* SL(2, F) := (S.I₁.equivMapOfInjective ι hι).symm.trans S.e₁
  have e₂ : ↥I₂ ≃* SL(2, F) := (S.I₂.equivMapOfInjective ι hι).symm.trans S.e₂
  have hcommI : ∀ a ∈ I₁, ∀ b ∈ I₂, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, S.comm a ha b hb]
  have hcore : pPrimeCore 2 ↥(I₁ ⊔ I₂) = ⊥ :=
    pPrimeCore_sl2_prod hodd hodd h4 h4 e₁ e₂ hcommI
  have hR : I₁ ⊔ I₂ ≤ centralizer ({t} : Set A) := by
    refine sup_le ?_ ?_
    · rintro _ ⟨a, _, rfl⟩
      exact Subgroup.mem_centralizer_singleton_iff.2 (hcomm a)
    · rintro _ ⟨a, _, rfl⟩
      exact Subgroup.mem_centralizer_singleton_iff.2 (hcomm a)
  have hmap : S.I₁ ⊔ S.I₂ ≤ S.I₁ ⊔ S.I₂ := le_rfl
  have hP : ∀ p : ℕ, p.Prime → p ≠ 2 → (∃ a, Nat.card F = p ^ a) →
      ∃ P : Subgroup A, P ≤ I₁ ⊔ I₂ ∧ (∀ x ∈ P, ∀ y ∈ P, x * y = y * x) ∧
        Nat.card P = Nat.card F * Nat.card F := by
    intro p hp hp2 ha
    obtain ⟨P, hPle, hPc, -, hPcard⟩ := exists_unip_prod S hp hp2 ha ha
    refine ⟨P.map ι, ?_, ?_, ?_⟩
    · rw [hI₁, hI₂, ← Subgroup.map_sup]
      exact Subgroup.map_mono hPle
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul, hPc a ha b hb]
    · rw [Nat.card_congr (P.equivMapOfInjective ι hι).toEquiv.symm]
      exact hPcard
  rcases hq with h | h | h
  · obtain ⟨P, hPR, -, hPcard⟩ := hP 7 (by norm_num) (by norm_num) ⟨1, by rw [h]; norm_num⟩
    have h1 := (Subgroup.card_dvd_of_le hPR).trans (card_dvd_of_cbar hfr ht hR hcore)
    rw [hPcard, h] at h1
    revert h1; decide
  · obtain ⟨P, hPR, hPc, hPcard⟩ := hP 3 (by norm_num) (by norm_num) ⟨2, by rw [h]; norm_num⟩
    rw [h] at hPcard
    exact no_abelian_81_of_cbar hfr ht hR hcore hPR hPc (by rw [hPcard])
  · obtain ⟨P, hPR, -, hPcard⟩ := hP 11 (by norm_num) (by norm_num) ⟨1, by rw [h]; norm_num⟩
    have h1 := (Subgroup.card_dvd_of_le hPR).trans (card_dvd_of_cbar hfr ht hR hcore)
    rw [hPcard, h] at h1
    revert h1; decide

section G2


theorem not_kfa_G2 {Y : Type} [Group Y] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hM : LieModel Y .G2 0 p f) : ¬ KindFactorAll Kind.ly Y := by
  obtain ⟨K, hK, hKfin, hcard, ⟨φ⟩⟩ := exists_equiv_of_lieModel hM
  have hY : Nat.card Y = ordG2 (p ^ f) := by
    rw [Nat.card_congr φ.toEquiv, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hcard]
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  refine notKFA_of_card (p := p) (k := f * 6) ?_ ?_
  · rw [hY, pow_mul]
    unfold ordG2
    exact (Dvd.intro _ rfl : (p ^ f) ^ 6 ∣ (p ^ f) ^ 6 * ((p ^ f) ^ 6 - 1)).mul_right _
  · intro h
    exact not_pow6_dvd_fact p hp3 ((pow_dvd_pow p (by omega : 6 ≤ f * 6)).trans h)

theorem cellAbs_G2 : CellAbs FG2 := by
  intro A _ _ zb Sb Vb J hfr hJ _ hF
  exfalso
  obtain ⟨p, f, hp, hf, hp2, hm⟩ := hF
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hns : ¬ Group.IsSolvable (↥J ⧸ center ↥J) := not_isSolvable_quot_of_quasisimple hJ.1
  have hnk : ¬ KindFactorAll Kind.ly (↥J ⧸ center ↥J) := not_kfa_G2 hp hp2 hf hm
  obtain ⟨hZ, hcomp, -⟩ := hfr.reduce hJ hnk
  obtain ⟨φ, hφinj, -⟩ := hfr.embed_aut hJ hZ hcomp
  let e : (↥J ⧸ center ↥J) ≃* ↥J :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have hmJ : LieModel ↥J .G2 0 p f := CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e hm
  have hnsJ : ¬ Group.IsSolvable ↥J := not_isSolvable_of_quot (center ↥J) hns
  obtain ⟨u, hu⟩ := exists_involution_of_not_solvable hnsJ
  by_cases hq5 : p ^ f ≤ 5
  ·
    have hf1 : f = 1 := by
      by_contra hne
      have h2 : 2 ≤ f := by omega
      have : p ^ 2 ≤ p ^ f := Nat.pow_le_pow_right (by omega) h2
      nlinarith
    subst hf1
    rw [pow_one] at hq5
    have hAut := card_mulAut_G2_dvd hp hp2 hmJ
    have h256 : 2 ^ 8 ∣ Nat.card (MulAut ↥J) := by
      have h1 : Nat.card ↥Sb = 2 ^ 8 := hfr.card
      rw [← h1]
      exact Subgroup.card_dvd_of_injective φ hφinj
    have h2 := h256.trans hAut
    have hp' : p = 3 ∨ p = 5 := by
      have hp4 : p ≠ 4 := by rintro rfl; norm_num at hp
      omega
    rcases hp' with rfl | rfl
    · revert h2; unfold ordG2; decide
    · revert h2; unfold ordG2; decide
  ·
    have hq6 : 6 ≤ p ^ f := by omega
    obtain ⟨F, hF, hFin, S, hcard, hSz⟩ := CFSG.GH74.GLS.IVK.GHInv.exists_shape_G2 hp hp2 hmJ u hu
    have hodd : Odd (Nat.card F) := by
      rw [hcard]
      exact (hp.odd_of_ne_two hp2).pow
    have h5 : 5 ≤ Nat.card F := by omega
    have hsec := psl2_section_of_shape S
    have := psl2_simple (F := F) (by omega)
    have hkfa := kfa_of_cent_section hfr J u hu (psl2_not_isSolvable (by omega)) hsec
    have hq : Nat.card F = 7 ∨ Nat.card F = 9 ∨ Nat.card F = 11 := by
      rcases card_of_kfa_psl2 hodd h5 hkfa with h | h | h | h
      · omega
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    refine shape_cbar_false hfr (J.subtype.comp (centralizer ({u} : Set ↥J)).subtype)
      ((Subgroup.subtype_injective _).comp (Subgroup.subtype_injective _))
      (t := (u : A)) ((Subgroup.orderOf_coe u).trans hu) ?_ S hq
    intro y
    have hy := Subgroup.mem_centralizer_singleton_iff.1 y.2
    exact congrArg Subtype.val hy

end G2

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
