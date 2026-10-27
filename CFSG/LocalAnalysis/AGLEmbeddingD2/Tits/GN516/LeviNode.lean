module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.LeviBQ
import CFSG.Quasithin.EmptyFaithful.R3c21A
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.LeviTransport

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516

open CFSG.Open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.Steinberg
  CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime
  CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.QuasithinUnique

@[expose] def NodeLevi {K : Type*} [Group K] (D : UniversalRootDatum K) (i : Fin D.rank) : Prop :=
  Group.IsSolvable ↥(rankOne D.rootGroup i) ∨ Open.IsQuasisimple ↥(rankOne D.rootGroup i)

section Node

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {i : Fin D.rank}

theorem nodeLevi_of_equiv_sl2 {F : Type} [Field F] [Finite F] [CharP F 2]
    (e : Matrix.SpecialLinearGroup (Fin 2) F ≃* ↥(rankOne D.rootGroup i)) : NodeLevi D i := by
  have hF2 : 2 ≤ Nat.card F := Finite.one_lt_card
  by_cases h2 : Nat.card F = 2
  · left
    have : Fintype F := Fintype.ofFinite F
    have hs : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) F) :=
      CFSG.Quasithin.R3c21.S0.isSolvable_sl2_of_card_two (by rw [← Nat.card_eq_fintype_card]; exact h2)
    exact Group.isSolvable_of_isSolvable_injective (f := e.symm.toMonoidHom) e.symm.injective
  · right
    have h4 : 4 ≤ Nat.card F := by
      have : Fintype F := Fintype.ofFinite F
      obtain ⟨m, -, hm⟩ := FiniteField.card (K := F) 2
      rw [Nat.card_eq_fintype_card, hm] at hF2 h2 ⊢
      have hm1 : 2 ≤ (m : ℕ) := by
        by_contra hm1
        have : (m : ℕ) = 1 := by have := m.pos; omega
        rw [this] at h2
        simp at h2
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (m : ℕ) := Nat.pow_le_pow_right (by norm_num) hm1
    have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) F) := sl2_isSimpleGroup h4
    have hq : Open.IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) F) :=
      ⟨(sl2_isPerfect h4).commutator_eq_top,
        ((QuotientGroup.quotientMulEquivOfEq sl2_center_eq_bot).trans
          QuotientGroup.quotientBot).isSimpleGroup⟩
    exact isQuasisimple_of_mulEquiv_open e hq

theorem nodeLevi_of_range_sl2 {F : Type} [Field F] [Finite F] [CharP F 2]
    {φ : Matrix.SpecialLinearGroup (Fin 2) F →* K} (hφ : Function.Injective φ)
    (hr : rankOne D.rootGroup i = φ.range) : NodeLevi D i :=
  nodeLevi_of_equiv_sl2 ((MonoidHom.ofInjective hφ).trans (MulEquiv.subgroupCongr hr.symm))

end Node

@[expose] def HasBQLevi (Y : Type) [Group Y] : Prop :=
  ∃ (K : Type) (_ : Group K) (_ : Finite K) (D : UniversalRootDatum K) (n : Fin D.rank → K)
    (H : Fin D.rank → Subgroup K) (π : K →* Y) (M : ℕ),
    BorelQuotient D n H π M ∧ ∀ i, NodeLevi D i

theorem leviAlt_of_hasBQLevi {W : Type} [Group W] [Finite W] {L S₀ A : Subgroup W}
    (hS : IsSylowTwoOf S₀ L) (hA : IsMinOverBorel L S₀ A)
    (h : HasBQLevi (↥L ⧸ Subgroup.center ↥L)) : LeviAlt ↥(pElementSubgroup 2 A) := by
  obtain ⟨K, _, _, D, n, H, π, M, hπ, hnodes⟩ := h
  obtain ⟨π', hπ', hT⟩ := exists_borelQuotient_conj hS hπ
  have hmin := isMinOverBorel_map_of_isMinOverBorel hS hA
  rw [hT] at hmin
  obtain ⟨i, hi⟩ := exists_eq_map_parJ hπ' hmin
  refine leviAlt_of_isMinOverBorel_of_quotient hS hA ?_
  rw [hi]
  exact leviAlt_map_parJ_singleton hπ' i (hnodes i)

end CFSG.AGLEmbeddingD2.Tits.GN516
