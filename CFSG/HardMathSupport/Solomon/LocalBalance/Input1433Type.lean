module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Input1433SameField
import CFSG.Assembly.OrderReductions.LinearOrders
import CFSG.LieType.Universal.Unitary.Clause0
import CFSG.LinearAlgebra.LinearGroups.UnitaryScalarKernel
import CFSG.LieType.Universal.SpinOmega.Center

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

@[expose] def Input14_33TypeSameField : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K Q₁ Q J : Subgroup X) (t : X) (q : ℕ),
    Input14_33Setup K Q₁ Q t →
    IsComponentOf J (GLAPLayer 3 (K ⊓ Subgroup.centralizer
      (((Subgroup.center ↥Q).map Q.subtype : Subgroup X) : Set X))) →
    (Subgroup.center ↥Q).map Q.subtype ≤ J →
    IsSL3EpsOver (↥J ⧸ GLAPPrimeCore 3 ↥J) q →
    (((Subgroup.center ↥Q).map Q.subtype).subgroupOf J).map
        (QuotientGroup.mk' (GLAPPrimeCore 3 ↥J)) = Subgroup.center (↥J ⧸ GLAPPrimeCore 3 ↥J) →
    (Nat.card J).factorization 3 = 3 → IsD4Over ↥K q

private theorem normal_eq_top_or_le_center {Q : Type*} [Group Q] (hQ : CFSG.Open.IsQuasisimple Q)
    {N : Subgroup Q} (hN : N.Normal) : N = ⊤ ∨ N ≤ Subgroup.center Q := by
  obtain ⟨hp, hs⟩ := hQ
  have := hN.map (QuotientGroup.mk' (Subgroup.center Q)) (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (N.map (QuotientGroup.mk' (Subgroup.center Q))) with h | h
  · right
    rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
  · left
    have hsup : N ⊔ Subgroup.center Q = ⊤ := by
      have := Subgroup.comap_map_eq (QuotientGroup.mk' (Subgroup.center Q)) N
      rw [h, Subgroup.comap_top, QuotientGroup.ker_mk'] at this
      exact this.symm
    have hZ : ⁅Subgroup.center Q, Subgroup.center Q⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.center_le_centralizer _)
    have hmap : (⊤ : Subgroup Q).map (QuotientGroup.mk' N) =
        (Subgroup.center Q).map (QuotientGroup.mk' N) := by
      rw [← hsup, Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
    have hcomm : commutator Q ≤ N := by
      rw [_root_.commutator_def, ← QuotientGroup.ker_mk' N, ← Subgroup.map_eq_bot_iff,
        Subgroup.map_commutator, hmap, ← Subgroup.map_commutator, hZ, Subgroup.map_bot]
    rw [hp] at hcomm
    exact eq_top_iff.mpr hcomm

private theorem glaPPrimeCore_eq_bot_of_card_center_dvd {J : Type} [Group J] [Finite J]
    (hq : CFSG.Open.IsQuasisimple J) (h3 : 3 ∣ Nat.card J)
    (hc : Nat.card (Subgroup.center J) ∣ 27) : GLAPPrimeCore 3 J = ⊥ := by
  refine eq_bot_iff.mpr (sSup_le fun N hN => ?_)
  obtain ⟨hNn, hNc⟩ := hN
  rcases normal_eq_top_or_le_center hq hNn with h | h
  · exfalso
    subst h
    rw [Subgroup.card_top] at hNc
    exact absurd (Nat.Coprime.eq_one_of_dvd hNc h3) (by norm_num)
  · have hd : Nat.card N ∣ 27 := (Subgroup.card_dvd_of_le h).trans hc
    have h1 : Nat.card N = 1 :=
      Nat.Coprime.eq_one_of_dvd
        (Nat.Coprime.pow_right 3 hNc.symm : Nat.Coprime (Nat.card N) (3 ^ 3)) (by simpa using hd)
    exact le_of_eq (Subgroup.eq_bot_of_card_eq N h1)

private theorem isSL3EpsOver_of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')
    {q : ℕ} (h : IsSL3EpsOver Y q) : IsSL3EpsOver Y' q := by
  obtain ⟨hty, h3⟩ := h
  refine ⟨?_, ?_⟩
  · rcases hty with ⟨F, hF, hfin, hc, ⟨e'⟩⟩ | ⟨F, hF, hfin, hc, ⟨e'⟩⟩
    · exact Or.inl ⟨F, hF, hfin, hc, ⟨e.symm.trans e'⟩⟩
    · exact Or.inr ⟨F, hF, hfin, hc, ⟨e.symm.trans e'⟩⟩
  · rwa [← Nat.card_congr (Subgroup.centerCongr e).toEquiv]

private theorem not_three_dvd_of_isSL3EpsOver {Y : Type} [Group Y] {q : ℕ}
    (h : IsSL3EpsOver Y q) : ¬ 3 ∣ q := by
  obtain ⟨hty, h3⟩ := h
  rcases hty with ⟨F, hF, hfin, hc, ⟨e⟩⟩ | ⟨F, hF, hfin, hc, ⟨e⟩⟩
  · have e' : Matrix.SpecialLinearGroup (Fin 3) F ≃* Y :=
      (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F).trans e.symm
    have h1 : Nat.card (Subgroup.center Y) = Nat.gcd 3 (Nat.card F - 1) := by
      rw [← Nat.card_congr (Subgroup.centerCongr e').toEquiv]
      exact CFSG.OrderReductions.LinearOrders.card_specialLinear_center F 3 (by norm_num)
    rw [h1] at h3
    have h4 : 3 ∣ Nat.card F - 1 := (Nat.dvd_gcd_iff.1 h3).2
    have h5 : 0 < Nat.card F := Nat.card_pos
    omega
  · intro h3q
    obtain ⟨p, f, hp, rfl⟩ : ∃ p f : ℕ, p.Prime ∧ q = p ^ f := by
      obtain ⟨p, hp⟩ := CharP.exists F
      letI : Fintype F := Fintype.ofFinite F
      obtain ⟨n, hpp, hn0⟩ := FiniteField.card F p
      have hn : Nat.card F = p ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn0
      have hqd : q ∣ p ^ (n : ℕ) := by
        rw [← hn, hc]
        exact Dvd.intro_left q (sq q).symm
      obtain ⟨f, -, hf⟩ := (Nat.dvd_prime_pow hpp).1 hqd
      exact ⟨p, f, hpp, hf⟩
    haveI : Fact p.Prime := ⟨hp⟩
    have hq2 : (3, p ^ f) ≠ (3, 2) := fun hh => by
      have : p ^ f = 2 := (Prod.mk.inj hh).2
      omega
    obtain ⟨-, hcen⟩ :=
      CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hc (le_refl 3) hq2
    have hk := (CFSG.LinearGroups.unitary_scalar_kernel hp hc (by norm_num : 1 ≤ 3)).2.2
    rw [← hcen] at hk
    rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv, hk] at h3
    have h4 : 3 ∣ p ^ f + 1 := (Nat.dvd_gcd_iff.1 h3).2
    omega

private theorem isD4Type_of_isD4Over {Y : Type} [Group Y] {q : ℕ} (h : IsD4Over Y q)
    (h3 : ¬ 3 ∣ q) : IsD4Type Y := by
  obtain ⟨F, hF, hfin, hc, ⟨e⟩⟩ := h
  have hperf : Group.IsPerfect (StatedOmega (StatedQuadPlus 4 F)) :=
    CFSG.LieType.Universal.Spin.isPerfect_statedOmega_quadPlus (by norm_num)
  have hcen : Subgroup.center (StatedOmega (StatedQuadPlus 4 F)) =
      (StatedScalars _ F).subgroupOf (StatedOmega (StatedQuadPlus 4 F)) :=
    CFSG.LieType.Universal.Spin.center_statedOmega_quadPlus (by norm_num)
  have hZ : Subgroup.center (StatedProj (StatedOmega (StatedQuadPlus 4 F))) = ⊥ := by
    let e2 : StatedOmega (StatedQuadPlus 4 F) ⧸
        Subgroup.center (StatedOmega (StatedQuadPlus 4 F)) ≃*
        StatedProj (StatedOmega (StatedQuadPlus 4 F)) := QuotientGroup.quotientMulEquivOfEq hcen
    rw [← Subgroup.map_center_eq e2, Group.IsPerfect.center_quotient_center_eq_bot,
      Subgroup.map_bot]
  have hZY : Subgroup.center Y = ⊥ := by
    refine (Subgroup.map_eq_bot_iff_of_injective (Subgroup.center Y)
      (f := e.toMonoidHom) e.injective).1 ?_
    exact (Subgroup.map_center_eq e).trans hZ
  let e' : Y ⧸ Subgroup.center Y ≃* StatedProj (StatedOmega (StatedQuadPlus 4 F)) :=
    ((QuotientGroup.quotientMulEquivOfEq hZY).trans QuotientGroup.quotientBot).trans e
  letI : Fintype F := Fintype.ofFinite F
  obtain ⟨n, hp, hn0⟩ := FiniteField.card F (ringChar F)
  have hn : Nat.card F = (ringChar F) ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn0
  refine ⟨ringChar F, n, ?_, ⟨⟨hp, n.pos, le_refl 4⟩, F, hF, hfin, hn, ⟨e'⟩⟩⟩
  intro h3'
  apply h3
  rw [← hc, hn, h3']
  exact dvd_pow_self 3 n.ne_zero

theorem input14_33LiteralSameField_of_type (h : Input14_33TypeSameField) :
    Input14_33LiteralSameField := by
  intro X _ _ K Q₁ Q J t q hS hJ hSL hZ hf3
  have h3J : 3 ∣ Nat.card J := Nat.dvd_of_factorization_pos (by rw [hf3]; norm_num)
  have hcJ : Nat.card (Subgroup.center ↥J) ∣ 27 := by
    have h1 : Nat.card ((Subgroup.center ↥J).map J.subtype) = Nat.card (Subgroup.center ↥J) :=
      Subgroup.card_map_of_injective J.subtype_injective
    have h2 : Nat.card ((Subgroup.center ↥Q).map Q.subtype) = Nat.card (Subgroup.center ↥Q) :=
      Subgroup.card_map_of_injective Q.subtype_injective
    rw [← h1, ← hZ, h2]
    exact (Subgroup.card_subgroup_dvd_card _).trans (hS.orderQ ▸ dvd_refl _)
  have hbot : GLAPPrimeCore 3 ↥J = ⊥ := glaPPrimeCore_eq_bot_of_card_center_dvd hJ.2.2 h3J hcJ
  have hbij : Function.Bijective (QuotientGroup.mk' (GLAPPrimeCore 3 ↥J)) := by
    refine ⟨?_, QuotientGroup.mk'_surjective _⟩
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hbot]
  let e : ↥J ≃* (↥J ⧸ GLAPPrimeCore 3 ↥J) := MulEquiv.ofBijective _ hbij
  refine h X K Q₁ Q J t q hS hJ ?_ (isSL3EpsOver_of_mulEquiv e hSL) ?_ hf3
  · rw [hZ]
    exact Subgroup.map_subtype_le _
  · have h1 : ((Subgroup.center ↥Q).map Q.subtype).subgroupOf J = Subgroup.center ↥J := by
      rw [hZ]
      exact Subgroup.comap_map_eq_self_of_injective J.subtype_injective _
    rw [h1]
    exact Subgroup.map_center_eq e

theorem input14_33SameField_of_type (h : Input14_33TypeSameField) : Input14_33SameField :=
  input14_33LiteralSameField_of_type h

theorem input14_33_of_type (h : Input14_33TypeSameField) : Input14_33 := by
  intro X _ _ K Q₁ Q t hgen hnorm hqs hKg hcore hrank hloc h3 h2 hnorm' hinv hQ hQn hcard hnab
    hexp hnc hcont hJ hcent
  obtain ⟨J, hJc, hZJ, hSL, hZc, hf3⟩ := hJ
  obtain ⟨q, hq⟩ := isSL3Eps_exists_over hSL
  have hS : Input14_33Setup K Q₁ Q t :=
    ⟨hgen, hnorm, hqs, hKg, hcore, hrank, hloc, h3, h2, hnorm', hinv, hQ, hQn, hcard, hnab, hexp,
      hnc, hcont, hcent⟩
  exact isD4Type_of_isD4Over (h X K Q₁ Q J t q hS hJc hZJ hq hZc hf3)
    (not_three_dvd_of_isSL3EpsOver hq)

theorem lemma27_of_type_inputs (h24 : Lemma24) (h25 : Lemma25Strong)
    (i112 : Input11_2Full) (i112f : Input11_2Four) (i112t : Input11_2Two)
    (iB0 : InputB0T) (i302 : Input30_2)
    (i183 : CFSG.HardMathSupport.Solomon.UniquenessMaximal.Input18_3_4)
    (i145 : Input14_5) (i253 : Input25_3) (i1433 : Input14_33TypeSameField)
    (iD4 : InputD4) : Lemma27 :=
  lemma27_of_inputs h24 h25 i112 i112f i112t iB0 i302 i183 i145 i253 (input14_33_of_type i1433)
    iD4

end CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns
