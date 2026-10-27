module

public import CFSG.HardMathSupport.Solomon.Coordinator.I27_1Fam
public import CFSG.GH74.GLS.C3.Layer1.BkA6K
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434AltSixAut
public import CFSG.GH74.GLS.C3.Layer1.BkL27K

public section

namespace CFSG.HardMathSupport.Solomon.Proving.AutSixBalance

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GorensteinWalter
open CFSG.GH74.GLS.C3.Layer1.Bk
open CFSG.RankThree.PartTwo.Sec4.Item434AltPerm
open CFSG.ComponentClassification.CatalogueSchreierAlternating

theorem card_mulAut_alt6 : Nat.card (MulAut (alternatingGroup (Fin 6))) = 1440 := by
  obtain ⟨F, _, _, e', hF9⟩ := exists_L2_nine_equiv (MulEquiv.refl (alternatingGroup (Fin 6)))
  have hF : L2Field F := ⟨by rw [hF9]; decide, by rw [hF9]; norm_num⟩
  have h360 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  rw [card_mulAut_eq e', card_innDiagSub e' hF, card_fieldAutSub_nine hF hF9 e', h360]

theorem card_dvd_nine_of_isPGroup {P : Subgroup (MulAut (alternatingGroup (Fin 6)))}
    (hP : IsPGroup 3 P) : Nat.card P ∣ 9 := by
  have : Finite (MulAut (alternatingGroup (Fin 6))) :=
    Nat.finite_of_card_ne_zero (by rw [card_mulAut_alt6]; norm_num)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 3)).mp hP
  have hdvd : 3 ^ k ∣ 1440 := by
    rw [← hk, ← card_mulAut_alt6]
    exact Subgroup.card_subgroup_dvd_card P
  rw [hk]
  rcases Nat.lt_or_ge k 3 with h | h
  · exact (pow_dvd_pow 3 (by omega : k ≤ 2)).trans (by norm_num)
  · exfalso
    have h27 : 3 ^ 3 ∣ 3 ^ k := pow_dvd_pow 3 h
    have := h27.trans hdvd
    norm_num at this

theorem card_F06_map_conj :
    Nat.card (F06.map (MulAut.conj : alternatingGroup (Fin 6) →*
      MulAut (alternatingGroup (Fin 6)))) = 9 := by
  rw [Subgroup.card_map_of_injective DegreeSix.inner_conjugation_injective, card_F06]

end CFSG.HardMathSupport.Solomon.Proving.AutSixBalance

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.HardMathSupport.Solomon.Proving.AutSixBalance
open CFSG.RankThree.PartTwo.Sec4.Item434AltPerm
open Subgroup

theorem i271AutBalanceAltSix_holds : I271AutBalanceAltSix := by
  intro A hA hA9 T hT hAT
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (MulAut (alternatingGroup (Fin 6))) :=
    Nat.finite_of_card_ne_zero (by rw [card_mulAut_alt6]; norm_num)
  have : Finite (Sylow 3 (MulAut (alternatingGroup (Fin 6)))) :=
    Finite.of_injective
      (fun P : Sylow 3 (MulAut (alternatingGroup (Fin 6))) =>
        (P : Set (MulAut (alternatingGroup (Fin 6)))))
      (fun P Q h => SetLike.coe_injective h)
  set H0 : Subgroup (MulAut (alternatingGroup (Fin 6))) :=
    F06.map (MulAut.conj : alternatingGroup (Fin 6) →* MulAut (alternatingGroup (Fin 6))) with hH0def
  have hH0card : Nat.card H0 = 9 := card_F06_map_conj
  have hH0p : IsPGroup 3 H0 := IsPGroup.of_card (n := 2) (by rw [hH0card]; norm_num)
  obtain ⟨S0, hH0S0⟩ := hH0p.exists_le_sylow
  have hA9' : (9 : ℕ) ≤ Nat.card A := by simpa using hA9
  have hApow : ∀ a ∈ A, a ^ 3 = 1 := hA.2
  have hAp : IsPGroup 3 A := by
    rw [isPGroup_iff_orderOf_dvd_pow]
    intro g
    have hg3 : g ^ 3 = 1 := Subtype.ext (by simpa using hApow g.1 g.2)
    exact ⟨1, by rw [pow_one]; exact orderOf_dvd_of_pow_eq_one hg3⟩
  obtain ⟨Q, hAQ⟩ := hAp.exists_le_sylow
  have hQdvd : Nat.card Q.toSubgroup ∣ 9 := card_dvd_nine_of_isPGroup Q.isPGroup'
  have hAle : Nat.card A ≤ Nat.card Q.toSubgroup :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hAQ)
  have hQle9 : Nat.card Q.toSubgroup ≤ 9 := Nat.le_of_dvd (by norm_num) hQdvd
  have hQA : A = Q.toSubgroup := Subgroup.eq_of_le_of_card_ge hAQ (by omega)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (MulAut (alternatingGroup (Fin 6))) S0 Q
  have hconj : ∀ h ∈ S0, g * h * g⁻¹ ∈ A := by
    intro h hh
    have hmem : MulAut.conj g h ∈ ((g • S0 : Sylow 3 (MulAut (alternatingGroup (Fin 6)))) :
        Set (MulAut (alternatingGroup (Fin 6)))) := by
      rw [Sylow.coe_smul]
      exact Set.smul_mem_smul_set hh
    rw [hg] at hmem
    rw [hQA]
    exact hmem
  set X : Subgroup (MulAut (alternatingGroup (Fin 6))) :=
    T.map (MulAut.conj g⁻¹ : MulAut (MulAut (alternatingGroup (Fin 6)))).toMonoidHom with hXdef
  have hmemX : ∀ x, x ∈ X ↔ g * x * g⁻¹ ∈ T := by
    intro x
    rw [hXdef, Subgroup.mem_map]
    constructor
    · rintro ⟨t, ht, rfl⟩
      convert ht using 1
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    · intro hx
      refine ⟨g * x * g⁻¹, hx, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  have hXcard : Nat.card X = Nat.card T := by
    rw [hXdef, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
  have hN : F06.map (MulAut.conj : alternatingGroup (Fin 6) →*
      MulAut (alternatingGroup (Fin 6))) ≤ normalizer (X : Set (MulAut (alternatingGroup (Fin 6)))) := by
    intro h hh
    have hS : h ∈ S0 := hH0S0 hh
    have hkA : g * h * g⁻¹ ∈ A := hconj h hS
    have hkN := hAT hkA
    rw [mem_normalizer_iff]
    intro x
    rw [hmemX, hmemX]
    have hkeq : g * h * g⁻¹ * (g * x * g⁻¹) * (g * h * g⁻¹)⁻¹ = g * (h * x * h⁻¹) * g⁻¹ := by
      group
    have := mem_normalizer_iff.mp hkN (g * x * g⁻¹)
    rw [hkeq] at this
    exact this
  have hXbot : X = ⊥ :=
    eq_bot_of_F06_le_normalizer
      (by rw [hXcard]; exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hT) hN
  have hTcard : Nat.card T = 1 := by
    rw [← hXcard, hXbot, Subgroup.card_bot]
  exact Subgroup.eq_bot_of_card_eq T hTcard

end CFSG.HardMathSupport.Solomon.Coordinator
