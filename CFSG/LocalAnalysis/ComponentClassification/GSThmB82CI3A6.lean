module

public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsStab
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog82A10Sym
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB8Action
public import CFSG.LieType.CentralExt.SL2Lift
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSBRankOneCover
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog8Sp4

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped MatrixGroups

namespace Eight2.Three

theorem isPGroup_stabilizer {Y : Type} [Group Y] [Finite Y] (hY : IsSec8JType Y 3 1) {t : Y}
    (ht : orderOf t = 2) : IsPGroup 2 ↥(MulAction.stabilizer (MulAut Y) t) := by
  have hL : Blueprint.LieModel Y .PSL 2 3 (2 * 1) := by
    rcases hY with h | ⟨-, -, ⟨e⟩⟩
    · exact h
    · exact LieType.CurtisTits.lieModel_of_mulEquiv e.symm
        Catalog82A10.lieModel_alternatingGroup_six
  exact (AutL2Facts.autL2Stab_conclusions Nat.prime_three (by norm_num) le_rfl hL t ht).2
    (by norm_num)

theorem eq_one_of_two_elements {N T : Type} [Group N] [Finite N] [Group T]
    (eN : N ⧸ pPrimeCore 2 N ≃* SL(2, ZMod 3)) (ψ : N →* T)
    (hψ : ∀ n : N, ∃ k : ℕ, ψ n ^ 2 ^ k = 1) (n : N) : ψ n = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO : ∀ m ∈ pPrimeCore 2 N, ψ m = 1 := by
    intro m hm
    obtain ⟨k, hk⟩ := hψ m
    refine UnbalancedGS.RankOneCover.eq_one_of_odd_orderOf_of_pow ?_ hk
    have h1 : orderOf m ∣ Nat.card (pPrimeCore 2 N) := by
      rw [← Subgroup.orderOf_mk m hm]
      exact orderOf_dvd_natCard _
    exact Odd.of_dvd_nat (Nat.coprime_two_left.1 pPrimeCore_coprime_card)
      ((orderOf_map_dvd ψ m).trans h1)
  have hO' : pPrimeCore 2 N ≤ ψ.ker := fun m hm => MonoidHom.mem_ker.mpr (hO m hm)
  set ψ' : N ⧸ pPrimeCore 2 N →* T := QuotientGroup.lift (pPrimeCore 2 N) ψ hO' with hψ'
  set θ : SL(2, ZMod 3) →* T := ψ'.comp eN.symm.toMonoidHom with hθ
  have htr : Set.range (Matrix.TransvectionStruct.toSpecialLinearGroup :
      Matrix.TransvectionStruct (Fin 2) (ZMod 3) → SL(2, ZMod 3)) ⊆ θ.ker := by
    rintro _ ⟨t, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (eN.symm t.toSpecialLinearGroup)
    have hθt : θ t.toSpecialLinearGroup = ψ m := by
      rw [hθ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← hm, hψ',
        QuotientGroup.lift_mk]
    obtain ⟨k, hk⟩ := hψ m
    rw [hθt]
    refine UnbalancedGS.RankOneCover.eq_one_of_odd_orderOf_of_pow ?_ hk
    have h3 : ψ m ^ 3 = 1 := by
      have ht3 := LieType.CentralExt.toSpecialLinearGroup_pow_ringChar t
      rw [ZMod.ringChar_zmod_n] at ht3
      rw [← hθt, ← map_pow, ht3, map_one]
    exact Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one h3)
  have hθ1 : ∀ g : SL(2, ZMod 3), θ g = 1 := by
    intro g
    have hle : Subgroup.closure (Set.range (Matrix.TransvectionStruct.toSpecialLinearGroup :
        Matrix.TransvectionStruct (Fin 2) (ZMod 3) → SL(2, ZMod 3))) ≤ θ.ker :=
      (Subgroup.closure_le _).mpr htr
    rw [Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field] at hle
    exact hle (mem_top g)
  have h1 := hθ1 (eN (n : N ⧸ pPrimeCore 2 N))
  rwa [hθ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply, hψ',
    QuotientGroup.lift_mk] at h1

variable {X : Type} [Group X] [Finite X]

theorem le_coreActionKernel {J N : Subgroup X} {z : X}
    (hJt : IsSec8JType (↥J ⧸ pPrimeCore 2 ↥J) 3 1) (hzJ : z ∈ J) (hzz : z * z = 1)
    (hz1 : z ≠ 1) (hNJ : N ≤ normalizer (J : Set X)) (hNz : N ≤ centralizer ({z} : Set X))
    (eN : ↥N ⧸ pPrimeCore 2 ↥N ≃* SL(2, ZMod 3)) : N ≤ coreActionKernel J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ψ : ↥N →* MulAut (↥J ⧸ pPrimeCore 2 ↥J) := (Eight.oddBarAction J).comp (inclusion hNJ)
    with hψ
  set zb : ↥J ⧸ pPrimeCore 2 ↥J := ((⟨z, hzJ⟩ : ↥J) : ↥J ⧸ pPrimeCore 2 ↥J) with hzb
  have hz2 : orderOf (⟨z, hzJ⟩ : ↥J) = 2 :=
    orderOf_eq_prime (Subtype.ext (by simpa [sq] using hzz)) fun h => hz1 (congrArg Subtype.val h)
  have hzb2 : orderOf zb = 2 :=
    UnbalancedLayer.orderOf_mk_eq_two (Nat.coprime_two_left.1 pPrimeCore_coprime_card) hz2
  have hfix : ∀ n : ↥N, ψ n zb = zb := by
    intro n
    rw [hψ, MonoidHom.comp_apply, hzb, Eight.oddBarAction_apply_mk]
    congr 1
    apply Subtype.ext
    change (n : X) * z * (n : X)⁻¹ = z
    rw [mem_centralizer_singleton_iff.mp (hNz n.2), mul_inv_cancel_right]
  have h2 : ∀ n : ↥N, ∃ k : ℕ, ψ n ^ 2 ^ k = 1 := by
    intro n
    have hst : ψ n ∈ MulAction.stabilizer (MulAut (↥J ⧸ pPrimeCore 2 ↥J)) zb := by
      rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
      exact hfix n
    obtain ⟨k, hk⟩ := isPGroup_stabilizer hJt hzb2 ⟨ψ n, hst⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  intro n hn
  have h1 := eq_one_of_two_elements eN ψ h2 ⟨n, hn⟩
  exact (Eight.mem_ker_oddBarAction (g := ⟨n, hNJ hn⟩)).mp (MonoidHom.mem_ker.mpr h1)

end Eight2.Three

end CFSG.ComponentClassification.GSThmB
