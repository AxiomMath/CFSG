module

public import CFSG.CGT.PushingUpLit.CGT6.SixFourA8
public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter.PSLnPlane
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagAccidental
public import CFSG.LocalAnalysis.QuasithinUnique.CatalogBridgeLinear
public import CFSG.Sporadic.He.Setup

public section

namespace CFSG.Adapters.CatalogueFieldBridges

open Matrix CFSG.GorensteinWalter
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.HardMathSupport.Solomon.Coordinator

theorem nonempty_projectiveSL_mulEquiv_lie {n : ℕ} {k : Type} [Field k] [Finite k]
    (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.A n q).Valid)
    (hk : Nat.card k = q.card) :
    Nonempty (projectiveSL (n + 1) k ≃*
      (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.A n q, hv⟩).Group) := by
  obtain ⟨p, e, hp, he⟩ := q
  have hq : Nat.card k = p ^ e := hk.trans (TauCeti.PrimePower.card_def ⟨p, e, hp, he⟩)
  exact ⟨(CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter.catEquivProjectiveSL
    (m := n) (k := k) (ℓ := p) (e := e) hp he hq hv).symm⟩

theorem nonempty_projectiveSL_three_mulEquiv_catalogue {k : Type} [Field k] [Finite k]
    (hk : Nat.card k = 2) :
    ∃ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.A 1 q).Valid),
      q.card = 7 ∧
        Nonempty (projectiveSL 3 k ≃*
          (TauCeti.CFSGIndex.lie ⟨.A 1 q, hv⟩).Group) := by
  haveI : Fintype k := Fintype.ofFinite k
  have hk2 : Fintype.card k = Fintype.card (ZMod 2) := by
    rw [← Nat.card_eq_fintype_card, hk]
    simp
  let φ : k ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq hk2
  have hq2 : Nat.card (ZMod 7) = 7 ^ 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card]
    rfl
  have hv : (TauCeti.LieTypeIndex.A 1 ⟨7, 1, Nat.prime_seven, Nat.one_pos⟩).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    refine ⟨⟨le_rfl, fun _ => by norm_num⟩, ?_⟩
    rintro (⟨-, h | h | h⟩ | ⟨h, -⟩ | ⟨h, -⟩) <;> norm_num at h
  obtain ⟨e⟩ := nonempty_psl2_seven_equiv_projectiveSL_three_two
  exact ⟨⟨7, 1, Nat.prime_seven, Nat.one_pos⟩, hv, by norm_num,
    ⟨(CFSG.EvenSmallLie.Child3.SelL39.projectiveSLCongr φ).trans
      ((e.symm.trans (LinearCover.projectiveSpecialLinearEquivProjectiveSL 2 (ZMod 7))).trans
        (CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter.catEquivProjectiveSL (m := 1)
          Nat.prime_seven Nat.one_pos hq2 hv).symm)⟩⟩

theorem nonempty_projectiveSL_four_mulEquiv_alternating_eight {k : Type} [Field k]
    [Finite k] (hk : Nat.card k = 2) :
    Nonempty (projectiveSL 4 k ≃* alternatingGroup (Fin 8)) := by
  have hk2 : Nat.card k = 2 ^ 1 := by rw [hk]; norm_num
  obtain ⟨e⟩ := CFSG.CGT.PushingUpLit.CGT6.nonempty_mulEquiv_alt_eight_of_psl_four_two
    ⟨⟨Nat.prime_two, le_rfl, by norm_num, by simp, by simp⟩, k, inferInstance, inferInstance,
      hk2, ⟨(LinearCover.projectiveSpecialLinearEquivProjectiveSL 4 k).symm.trans
        (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 4 k)⟩⟩
  exact ⟨e⟩

theorem nonempty_psl2_mulEquiv_alternating_five {k : Type} [Field k] [Finite k]
    (hk : Nat.card k = 4 ∨ Nat.card k = 5) :
    Nonempty (PSL2 k ≃* alternatingGroup (Fin 5)) := by
  have h60 : Nat.card (PSL2 k) = 60 := by
    rcases hk with h | h
    · exact CFSG.ClassicalModels.projectiveSpecialLinear_two_card_of_card_four k h
    · exact CFSG.ClassicalModels.projectiveSpecialLinear_two_card_of_card_five k h
  haveI : IsSimpleGroup (PSL2 k) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple
    (by rcases hk with h | h <;> omega)
  obtain ⟨e⟩ := CFSG.QuasithinUnique.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty h60
  exact ⟨e⟩

theorem nonempty_psl2_nine_mulEquiv_alternating_six {k : Type} [Field k] [Finite k]
    (hk : Nat.card k = 9) :
    Nonempty (PSL2 k ≃* alternatingGroup (Fin 6)) := by
  haveI : Fintype k := Fintype.ofFinite k
  exact unique_field_nine_projective_linear_alternating_six_isomorphism k
    (by rwa [← Nat.card_eq_fintype_card])

end CFSG.Adapters.CatalogueFieldBridges

end
