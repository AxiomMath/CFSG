module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.U6Local
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.U6Rank
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.U6RankCount
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.U6Elem
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.U6Comps
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.U6Heis

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSFourU

open OuterFourInAux (IsU6EightIndex FieldAutU)

section Assembly

open CFSG.HardMathSupport.Dickson.I271 (autImage mem_autImage actHom_eq_one_of_mem_centralizer)
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87 (innSub)
open CFSG.ComponentClassification.Burgoyne.Proj (projH)
open Bal209F4Aux (InnerAt)

theorem u6Sel (h207 : CFSG.HardMathSupport.Dickson.Bal207.Bal207Corr) :
    FourUSel IsU6EightIndex (FieldAutU 6) := by
  intro X _ _ hKG K B x hK hBSC hBN hrank hLie hxB hxI hdec hFx
  classical
  have hperf : commutator ↥K = ⊤ := hK.2.2.1
  have hBel : CFSG.Open.IsElemAbelian 3 B := hBSC.2.1
  obtain ⟨K0, fK0, h, e, -, -, -, -, -⟩ := U6Bridge.exists_uFieldAut_of_fieldAutU6 hFx
  haveI := h.finite
  letI : Fintype K0 := Fintype.ofFinite K0
  have hW := u6_twoLocal_witness hKG hK hBel hBN hLie hxB hxI hFx
  have hr : CFSG.Open.pRank 3 (B ⊓ Subgroup.centralizer (K : Set X) : Subgroup X) + (3 + 1) ≤
      CFSG.Open.pRank 3 B :=
    hW.trans hrank
  have h27 := card_innerPart_ge hperf hBel hBN hxB hxI hdec hr
  set P := CFSG.Open.StatedProj (CFSG.Open.StatedSU 6 (2 ^ 3) K0)
  have hcenS : Subgroup.center (↥K ⧸ Subgroup.center ↥K) = ⊥ := center_quot_eq_bot hK.2.2
  have hcenP : Subgroup.center P = ⊥ := by
    rw [← Subgroup.map_center_eq e, hcenS, Subgroup.map_bot]
  have hinj : Function.Injective (MulAut.conj : P →* MulAut P) := conj_inj_of_center_bot hcenP
  let Ebar : Subgroup (MulAut P) :=
    (autImage B K ⊓ innSub (↥K ⧸ Subgroup.center ↥K)).map (MulAut.congr e).toMonoidHom
  have hEbar_le : Ebar ≤ (MulAut.conj : P →* MulAut P).range := by
    rintro _ ⟨a, ⟨-, s, rfl⟩, rfl⟩
    exact ⟨e s, by simpa using (congr_conj' e s).symm⟩
  let E : Subgroup P := Ebar.comap (MulAut.conj : P →* MulAut P)
  have hBelAut : CFSG.Open.IsElemAbelian 3 (autImage B K) := by
    unfold autImage
    exact ((hBel.mono inf_le_left).subgroupOf _).map _
  have hEl : CFSG.Open.IsElemAbelian 3 E :=
    ((hBelAut.mono inf_le_left).map _).comap hinj
  have hEcard : 27 ≤ Nat.card E := by
    have hmap : E.map (MulAut.conj : P →* MulAut P) = Ebar :=
      Subgroup.map_comap_eq_self hEbar_le
    have h1 : Nat.card (E.map (MulAut.conj : P →* MulAut P)) = Nat.card E :=
      Subgroup.card_map_of_injective hinj
    have h2 : Nat.card Ebar = Nat.card ↥(autImage B K ⊓ innSub (↥K ⧸ Subgroup.center ↥K)) :=
      Subgroup.card_map_of_injective (MulAut.congr e).injective
    have h3 : (27 : ℕ) ≤ 3 ^ 3 := le_rfl
    rw [← h1, hmap, h2]
    exact h3.trans h27
  have hexists : ∀ g : CFSG.Open.StatedSU 6 (2 ^ 3) K0, projH _ g ∈ E →
      ∃ y ∈ B, ActsAs K e y g := by
    intro g hg
    obtain ⟨a, ⟨haA, -⟩, hae⟩ := hg
    obtain ⟨y, hyN, hyB, hya⟩ := mem_autImage.1 haA
    exact ⟨y, hyB, hyN, by rw [hya]; exact hae⟩
  have hinner : ∀ (y : X) (_ : y ∈ B) (g : CFSG.Open.StatedSU 6 (2 ^ 3) K0),
      ActsAs K e y g → InnerAt K y := by
    intro y _ g ⟨hyN, hact⟩
    exact (innerAt_iff_congr_mem_innSub hperf e hyN).2 (by rw [hact]; exact ⟨_, rfl⟩)
  have hnotC : ∀ (y : X) (g : CFSG.Open.StatedSU 6 (2 ^ 3) K0), ActsAs K e y g →
      projH _ g ≠ 1 → y ∉ Subgroup.centralizer (K : Set X) := by
    intro y g ⟨hyN, hact⟩ hg1 hyC
    apply hg1
    have h1 := actHom_eq_one_of_mem_centralizer K hyC
    have h2 : MulAut.conj (projH _ g : P) = 1 := by rw [← hact, h1, map_one]
    exact hinj (by rw [h2, map_one])
  rcases exists_good_of_card_ge_27 h E hEl hEcard with
    ⟨g, hgE, hg1, hbig⟩ | ⟨g₁, g₂, g₃, h₁E, h₂E, h₃E, hg₃1, hH⟩
  · obtain ⟨y, hyB, hact⟩ := hexists g hgE
    have hy3 : y ^ 3 = 1 := hBel.2 y hyB
    have hnotscal : ¬ ∃ c : K0ˣ, (g : GL (Fin 6) K0) =
        Matrix.GeneralLinearGroup.scalar (Fin 6) c := by
      rintro ⟨c, hc⟩
      apply hg1
      rw [show projH _ g = (QuotientGroup.mk g : P) from rfl, QuotientGroup.eq_one_iff]
      exact Subgroup.mem_subgroupOf.2 ⟨c, hc.symm⟩
    obtain ⟨hshape, h3⟩ := u6_shape_big hK h e hact hy3 hbig hnotscal
    refine ⟨y, hyB, hinner y hyB g hact, hnotC y g hact hg1, ?_⟩
    intro J hJ
    have hBJ := normalizer_of_card_le_two_comps hBel hBN hyB h3 hJ
    refine ⟨hBJ, ?_⟩
    obtain ⟨hJq, d, hd, ed⟩ := hshape J hJ
    obtain ⟨q, hq, hd | hd | hd⟩ := hd
    · have hL : IsLieQuot ↥J IsL2EightIndex :=
        ⟨d, by rw [hd]; exact ⟨rfl, hq⟩, ed⟩
      exact sLOB_of_l2Eight_component hK.2.1 hBSC hyB hJ hBJ hL
    · exact KSCompSLOB.sLOB_of_bal207_component h207 hKG hBSC hyB
        (KSF4Kit.isComponentOf_centralizer_of_glaPComponent hK hJ hJq) hBJ
        (P := IsU6Bal207CompIndex) isU6Bal207Comp_bal207
        ⟨d, ⟨q, hq, Or.inl hd⟩, ed⟩
    · exact KSCompSLOB.sLOB_of_bal207_component h207 hKG hBSC hyB
        (KSF4Kit.isComponentOf_centralizer_of_glaPComponent hK hJ hJq) hBJ
        (P := IsU6Bal207CompIndex) isU6Bal207Comp_bal207
        ⟨d, ⟨q, hq, Or.inr hd⟩, ed⟩
  · obtain ⟨b₁, hb₁, hact₁⟩ := hexists g₁ h₁E
    obtain ⟨b₂, hb₂, hact₂⟩ := hexists g₂ h₂E
    obtain ⟨y, hyB, hact⟩ := hexists g₃ h₃E
    have hy3 : y ^ 3 = 1 := hBel.2 y hyB
    have hdiv : ∀ c : K0, 3 ∣ eigMult (g₃ : GL (Fin 6) K0) c := hH.2.2.2
    have hnotscal : ¬ ∃ c : K0ˣ, (g₃ : GL (Fin 6) K0) =
        Matrix.GeneralLinearGroup.scalar (Fin 6) c := by
      rintro ⟨c, hc⟩
      apply hg₃1
      rw [show projH _ g₃ = (QuotientGroup.mk g₃ : P) from rfl, QuotientGroup.eq_one_iff]
      exact Subgroup.mem_subgroupOf.2 ⟨c, hc.symm⟩
    obtain ⟨hshape, h3⟩ := u6_shape_three hK h e hact hy3 hdiv hnotscal
    refine ⟨y, hyB, hinner y hyB g₃ hact, hnotC y g₃ hact hg₃1, ?_⟩
    intro J hJ
    have hBJ := normalizer_of_card_le_two_comps hBel hBN hyB h3 hJ
    refine ⟨hBJ, ?_⟩
    obtain ⟨-, hJL⟩ := hshape J hJ
    exact KSF4SU3.isStronglyLocallyOneBalanced_of_autImageRankThree
      (CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hJ) hJL
      (u6_heis_rank_three hK hBel hBN h e hxB hFx hb₁ hb₂ hyB hact₁ hact₂ hact hH hJ hBJ)

theorem bal209FourUAt_u6 (h207 : CFSG.HardMathSupport.Dickson.Bal207.Bal207Corr) :
    Bal209FourUAt IsU6EightIndex (FieldAutU 6) :=
  bal209FourUAt_of_inputs u6FourUField u6Fixed u6Local (u6Sel h207) (fourUFixedSLOB_u6 h207)

end Assembly

end KSFourU

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

end
