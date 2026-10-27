module

public import CFSG.GH74.Generic.BProg.B3.LocBalSL4Inst
public import CFSG.GH74.Generic.BProg.B3.LocBalSL4ThreeMain
public import CFSG.GH74.Generic.BProg.B1.PilotS1Three

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.L5U5 CFSG.GH74.Generic.BProg
  CFSG.GH74.Generic.BProg.B1.PilotS1 Subgroup

namespace LocBalSL4Final

theorem locBal32_quot_of_equiv {K P : Type} [Group K] [Group P] (e : K ≃* P)
    (h : ∀ {Ab' : Subgroup P}, CFSG.IsElementaryAbelian 2 ↥Ab' → Nat.card ↥Ab' = 8 →
      ∀ B' : Subgroup (MulAut (P ⧸ Subgroup.center P)),
        B' ≤ (Ab'.map (QuotientGroup.mk' (Subgroup.center P))).map
          (MulAut.conj : (P ⧸ Subgroup.center P) →* MulAut (P ⧸ Subgroup.center P)) →
        IsLocBal32 (P ⧸ Subgroup.center P) B')
    {Ab : Subgroup K} (hAe : CFSG.IsElementaryAbelian 2 ↥Ab) (hA8 : Nat.card ↥Ab = 8)
    (B : Subgroup (MulAut (K ⧸ Subgroup.center K)))
    (hB : B ≤ (Ab.map (QuotientGroup.mk' (Subgroup.center K))).map
      (MulAut.conj : (K ⧸ Subgroup.center K) →* MulAut (K ⧸ Subgroup.center K))) :
    IsLocBal32 (K ⧸ Subgroup.center K) B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let φ : K ⧸ Subgroup.center K ≃* P ⧸ Subgroup.center P :=
    QuotientGroup.congr (Subgroup.center K) (Subgroup.center P) e
      (CFSG.LieType.Universal.Unitary.map_center_mulEquiv e)
  let Ab' : Subgroup P := Ab.map e.toMonoidHom
  have hAe' : CFSG.IsElementaryAbelian 2 ↥Ab' := IsElementaryAbelian.map e.toMonoidHom
  have hA8' : Nat.card ↥Ab' = 8 := by
    rw [Subgroup.card_map_of_injective e.injective]
    exact hA8
  let B' : Subgroup (MulAut (P ⧸ Subgroup.center P)) := B.map (MulAut.congr φ).toMonoidHom
  have hB' : B' ≤ (Ab'.map (QuotientGroup.mk' (Subgroup.center P))).map
      (MulAut.conj : (P ⧸ Subgroup.center P) →* MulAut (P ⧸ Subgroup.center P)) := by
    rintro _ ⟨b, hb, rfl⟩
    obtain ⟨y, ⟨a, haA, rfl⟩, hya⟩ := Subgroup.mem_map.mp (hB hb)
    refine ⟨QuotientGroup.mk' (Subgroup.center P) (e a), ⟨e a, ⟨a, haA, rfl⟩, rfl⟩, ?_⟩
    rw [← hya]
    show MulAut.conj (QuotientGroup.mk' (Subgroup.center P) (e a)) =
      MulAut.congr φ (MulAut.conj (QuotientGroup.mk' _ a))
    rw [LocBalSL4Basic.congr_conj]
    rfl
  have h2 := isLocBal32_of_mulEquiv φ.symm (h hAe' hA8' B' hB')
  have hBB : B'.map (MulAut.congr φ.symm).toMonoidHom = B := by
    rw [Subgroup.map_map]
    have : (MulAut.congr φ.symm).toMonoidHom.comp (MulAut.congr φ).toMonoidHom =
        MonoidHom.id _ := by
      ext x y
      simp [MulAut.congr_apply]
    rw [this, Subgroup.map_id]
  rwa [hBB] at h2

theorem locBal32_SL4_three {Kt : Type} [Group Kt] [Finite Kt] (hK : QShape1Three Kt)
    {Ab : Subgroup Kt} (hAe : CFSG.IsElementaryAbelian 2 ↥Ab) (hA8 : Nat.card ↥Ab = 8)
    (B : Subgroup (MulAut (Kt ⧸ Subgroup.center Kt)))
    (hB : B ≤ (Ab.map (QuotientGroup.mk' (Subgroup.center Kt))).map
      (MulAut.conj : (Kt ⧸ Subgroup.center Kt) →* MulAut (Kt ⧸ Subgroup.center Kt))) :
    IsLocBal32 (Kt ⧸ Subgroup.center Kt) B := by
  have hq : CFSG.IsQuasisimple Kt := by
    obtain ⟨F, _, _, hF3, ⟨e⟩⟩ := hK
    exact CFSG.LieType.Universal.Unitary.isQuasisimple_of_mulEquiv e.symm
      (CFSG.LieType.Universal.Unitary.isQuasisimple_of_mulEquiv
        (specialLinearGroupEquivStatedSL (3 + 1) F)
        (CFSG.LieType.Universal.SpecialLinear.isQuasisimple 3 F (by norm_num)))
  have hQ1 : QShape1 Kt := hK.qShape1
  obtain ⟨P, _, F', _, _, z, ⟨e⟩, hF3, hG⟩ := exists_grpS1_of_three hK
  have : Finite P := Finite.of_equiv Kt e.toEquiv
  have hqP : CFSG.IsQuasisimple P :=
    CFSG.LieType.Universal.Unitary.isQuasisimple_of_mulEquiv e hq
  have hQP : QShape1 P := IsSL4Model.of_mulEquiv hQ1 e
  refine LocBalSL4Final.locBal32_quot_of_equiv e ?_ hAe hA8 B hB
  intro Ab' hAe' hA8' B' hB'
  exact LocBalSL4ThreeMain.locBal32_of_grpS1_three hF3 hG hqP
    (fun Ab'' hAe'' hA8'' => CFSG.GH74.Generic.BProg.B2.shapeGen_1_proved P hQP Ab'' hAe'' hA8'')
    hAe' hA8' B' hB'

end LocBalSL4Final


theorem locBal32_SL4 {Kt : Type} [Group Kt] [Finite Kt] (hK : QShape1 Kt) {Ab : Subgroup Kt}
    (hAe : CFSG.IsElementaryAbelian 2 ↥Ab) (hA8 : Nat.card ↥Ab = 8)
    (B : Subgroup (MulAut (Kt ⧸ center Kt)))
    (hB : B ≤ (Ab.map (QuotientGroup.mk' (center Kt))).map
      (MulAut.conj : (Kt ⧸ center Kt) →* MulAut (Kt ⧸ center Kt))) :
    IsLocBal32 (Kt ⧸ center Kt) B := by
  rcases qShape1_split hK with hBig | hThree
  · exact LocBalSL4Inst.locBal32_SL4_big hBig hAe hA8 B hB
  · exact LocBalSL4Final.locBal32_SL4_three hThree hAe hA8 B hB

end CFSG.GH74.Generic.BProg.B3
