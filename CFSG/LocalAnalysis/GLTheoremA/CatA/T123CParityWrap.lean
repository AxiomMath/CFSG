module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T123CFacts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T123CParityCore
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T123CParityOrbit
public import CFSG.LocalAnalysis.GL83PartI.I_27_9.Count
public import CFSG.GroupTheory.ElemAbelianRank

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T123C

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA

variable {G : Type} [Group G] [Finite G]

theorem exists_twoSubgroup_of_type167J (hcore : Aut167JCore) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {X K E : Subgroup G} (hK : GLAPComponent p X K) (hT : Type167J p K)
    (hE : IsElemAbelian p E) (hEX : E ≤ Subgroup.normalizer (X : Set G)) :
    ∃ T : Subgroup G, T ≤ X ∧ T ≠ ⊥ ∧ IsPGroup 2 T ∧ E ≤ Subgroup.normalizer (T : Set G) := by
  haveI : Fact p.Prime := ⟨hp⟩
  set E₁ : Subgroup G := E ⊓ Subgroup.normalizer (K : Set G)
  have hE₁el : IsElemAbelian p E₁ := isElemAbelian_mono hE inf_le_left
  have hE₁K : E₁ ≤ Subgroup.normalizer (K : Set G) := inf_le_right
  set A : Subgroup (MulAut (PSimple p K)) :=
    (E₁.subgroupOf (Subgroup.normalizer (K : Set G))).map (chevAut p K)
  have hAp : IsPGroup p A :=
    (IsPGroup.comap_subtype (K := Subgroup.normalizer (K : Set G))
      (isPGroup_of_isElemAbelian hE₁el)).map (chevAut p K)
  obtain ⟨U, hU, hU2, hUinv⟩ := hcore p (PSimple p K) hp hp2 (type167JAt_of_type167J hT) A hAp
  obtain ⟨T, hTK, hT1, hT2, hET⟩ := exists_twoSubgroup_le_of_chevAut hp hp2 hE₁el hE₁K hU hU2
    (fun e he u hu => hUinv _ ⟨⟨e, hE₁K he⟩, Subgroup.mem_subgroupOf.2 he, rfl⟩ u hu)
  exact exists_twoSubgroup_of_pComponent_orbit hp hp2 hK hTK hT1 hT2 hE hEX hET

theorem parityFact_of_core (hcore : Aut167JCore) : ParityFact := by
  intro p Ω _ _ S B K₁ x y hp hp2 hSn _ _ hK₁ hT hBel _ hxB _ _ _ _ _ hrank
  haveI : Fact p.Prime := ⟨hp⟩
  refine (S9.isSC_of_isMaxRankIn hp hBel hxB fun E hE hEel => ?_).2
  have hEX : E ≤ Subgroup.normalizer
      ((S ⊓ Subgroup.centralizer ({x} : Set Ω) : Subgroup Ω) : Set Ω) := by
    refine le_normalizer_of_conj_mem fun e he z hz => ?_
    obtain ⟨hzS, hzx⟩ := Subgroup.mem_inf.1 hz
    have hex : Commute e x := Subgroup.mem_centralizer_singleton_iff.1 (hE he)
    have hzx' : Commute z x := Subgroup.mem_centralizer_singleton_iff.1 hzx
    exact Subgroup.mem_inf.2 ⟨hSn.conj_mem z hzS e,
      Subgroup.mem_centralizer_singleton_iff.2 ((hex.mul_left hzx').mul_left hex.inv_left)⟩
  obtain ⟨T, -, hT1, hT2, hET⟩ := exists_twoSubgroup_of_type167J hcore hp hp2 hK₁ hT hEel hEX
  calc Nat.card E ≤ p ^ GLATwoLocalRank p Ω :=
        GL83.PiGen.card_le_pow_twoLocalRank hEel hT2 hT1 hET
    _ ≤ p ^ CFSG.Open.pRank p B := Nat.pow_le_pow_right hp.pos hrank
    _ = Nat.card B := (CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian hp hBel).symm

end CFSG.LocalAnalysis.GLTheoremA.T123C

end
