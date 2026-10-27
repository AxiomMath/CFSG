module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1015OneRes
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIIISp48TwentySeven
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Bridges

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.I1015PSp4Out

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 TauCeti CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.CatB.I1015OneRes
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

theorem sp4eight_equiv {K : Type} [Group K] (h : catalogIs K S9.isSp4eight) :
    Nonempty (K ≃* StatedProj (StatedSp 2 (GaloisField 2 3))) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨d, hv, hP, ⟨e⟩⟩ := exists_lieIndex h
  cases d with
  | B r q =>
    rcases r with _ | _ | _ | r
    · exact hP.elim
    · exact hP.elim
    · have hq : q.card = 2 ^ 3 := hP
      obtain ⟨hp, hf⟩ := primePower_eq_of_card_eq Nat.prime_two (s := 3) (by norm_num) hq
      haveI : Finite ↥(ValidLieTypeIndex.fixedField ⟨.B 2 q, hv⟩) :=
        CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
      have hcardF : Nat.card ↥(ValidLieTypeIndex.fixedField ⟨.B 2 q, hv⟩) = 2 ^ 3 := by
        rw [ValidLieTypeIndex.card_fixedField, ValidLieTypeIndex.fieldOrder_eq_characteristic_pow,
          show ValidLieTypeIndex.characteristic ⟨.B 2 q, hv⟩ = q.p from
            LieTypeIndex.characteristic_B 2 q,
          show ValidLieTypeIndex.fieldExponent ⟨.B 2 q, hv⟩ = q.exponent from
            LieTypeIndex.fieldExponent_B 2 q, hp, hf]
      let φ : ↥(ValidLieTypeIndex.fixedField ⟨.B 2 q, hv⟩) ≃+* GaloisField 2 3 :=
        CFSG.ClassicalModels.finiteFieldEquivGaloisField _ 2 3 (by norm_num) hcardF
      exact ⟨e.trans ((CFSG.QuasithinUnique.SQTK.typeB2GroupEquivStatedProj q hv).trans
        (CFSG.Adapters.RankTwoModelTransports.statedProjCongr
          (CFSG.Adapters.RankTwoModelTransports.glCongr φ)
          (CFSG.Adapters.RankTwoModelTransports.glCongr_statedSp φ 2)
          (CFSG.Adapters.RankTwoModelTransports.glCongr_statedScalars φ)))⟩
    · exact hP.elim
  | _ => exact hP.elim

theorem card_outer_sp4eight_le {K : Type} [Group K] (h : catalogIs K S9.isSp4eight) :
    Nat.card (Outer K) ≤ 6 := by
  obtain ⟨e⟩ := sp4eight_equiv h
  rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
  exact CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.card_outer_sp48_le

theorem card_le_three_mul_inf_of_outer {M : Type} [Group M] [Finite M] (N : Subgroup M) [N.Normal]
    {A : Subgroup M} (hA : IsPGroup 3 A) (hN : Nat.card (M ⧸ N) ≤ 6) :
    Nat.card A ≤ 3 * Nat.card ↥(A ⊓ N) := by
  set ψ : A →* M ⧸ N := (QuotientGroup.mk' N).comp A.subtype with hψ
  have hset : ψ.ker.map A.subtype = A ⊓ N := by
    ext x
    simp only [Subgroup.mem_map, MonoidHom.mem_ker, hψ, MonoidHom.comp_apply, Subgroup.coe_subtype,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_inf]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a.2, ha⟩
    · rintro ⟨hxA, hxN⟩
      exact ⟨⟨x, hxA⟩, hxN, rfl⟩
  have hker : Nat.card ψ.ker = Nat.card ↥(A ⊓ N) := by
    rw [← hset]
    exact (Subgroup.card_map_of_injective (f := A.subtype) Subtype.val_injective).symm
  have hsplit : Nat.card A = Nat.card (A ⧸ ψ.ker) * Nat.card ψ.ker :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
  have hrange : Nat.card (A ⧸ ψ.ker) = Nat.card ψ.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv
  have hrle : Nat.card ψ.range ≤ 6 :=
    (Subgroup.card_le_card_group ψ.range).trans hN
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hA
  have hdvd : Nat.card (A ⧸ ψ.ker) ∣ 3 ^ k := by
    rw [← hk]
    exact ⟨Nat.card ψ.ker, hsplit⟩
  rw [hrange] at hdvd
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (hdvd)
  have hj1 : j ≤ 1 := by
    by_contra hcon
    have h9 : 3 ^ 2 ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [← hj] at h9
    omega
  have h3 : Nat.card ψ.range ≤ 3 := by
    rw [hj]
    interval_cases j <;> norm_num
  rw [hsplit, hrange, hker]
  exact Nat.mul_le_mul_right _ h3

theorem i1015oneSp4Out_holds : I1015oneSp4Out := by
  intro K _ _ hK A hA
  have hO := card_outer_sp4eight_le hK
  have hp : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hA.2 g g.2)⟩
  exact card_le_three_mul_inf_of_outer (inner K) hp hO

end CFSG.LocalAnalysis.GLTheoremA.CatB.I1015PSp4Out
