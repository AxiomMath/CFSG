module

public import CFSG.GH74.Generic.S3.LyPump
public import CFSG.GH74.Generic.JMaxShapes
public import CFSG.GH74.GLS.TwoThin.G.Reduction

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.L5U5 CFSG.Blueprint CFSG.ABGLocalTools
  CFSG.Assembly.LowTwoRank Subgroup CFSG.GH74.GLS.TwoThin CFSG.LocalAnalysis.ComponentInitial
open CFSG.GH74.GLS (InG2 InC2 InT2 InB2 InCalK2)
open scoped MatrixGroups commutatorElement

theorem ofLieType_of_sp4 {K : Type} [Group K] {F : Type} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) (e : K ≃* StatedSp 2 F) : OfLieType K := by
  obtain ⟨p, f, hp, hf, hcard⟩ := exists_prime_pow_card F
  have hp2 : p ≠ 2 := by
    rintro rfl
    rw [hcard] at hodd
    exact (Nat.not_even_iff_odd.2 hodd) (Nat.even_pow.2 ⟨even_two, by omega⟩)
  have hadm : StatedLieAdmissible .PSp 2 p f := by
    refine ⟨hp, hf, le_rfl, ?_⟩
    intro h
    have : p ^ f = 2 := (Prod.mk.inj h).2
    have hodd' : Odd (p ^ f) := by rw [← hcard]; exact hodd
    rw [this] at hodd'
    exact absurd hodd' (by decide)
  have hmap : (center K).map e.toMonoidHom = center (StatedSp 2 F) := Subgroup.map_center_eq e
  refine ⟨.PSp, 2, p, f, Or.inl ⟨by decide, ?_⟩⟩
  refine ⟨hadm, F, inferInstance, inferInstance, hcard, ⟨?_⟩⟩
  exact (QuotientGroup.congr (center K) (center (StatedSp 2 F)) e hmap).trans
    (CFSG.LieType.Universal.Symplectic.centerQuotientEquiv 2 F)

theorem d2_le_six_of_shapeS2 {G : Type} [Group G] {x : G} {K : Subgroup (CentralizerBar x)}
    (hc : IsComponent K) (hG2 : InG2 ↥K) (hZ : center ↥K ≠ ⊥) (hsh : ShapeS2 x K) : d2 ↥K ≤ 6 := by
  obtain ⟨⟨F, _, _, hodd, ⟨e⟩⟩, -⟩ := hsh
  refine Nat.sInf_le ⟨hG2, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    ⟨rfl, ofLieType_of_sp4 hodd e, ?_⟩)))))⟩
  rintro ⟨p, f, -, -, hmod⟩
  exact hZ (center_eq_bot_of_quasisimple_lieModel_L3 hc.1 hmod)

theorem false_of_vertical_g2
    (hF : GenericKnownFacts) {G : Type} [Group G] [Finite G]
    {x : G} {K : Subgroup (CentralizerBar x)} (hset : S3Setup G x K) (hmax : IsJMax x K)
    {y : G} (hy : orderOf y = 2) {L : Subgroup (CentralizerBar y)} (hL : IsComponent L)
    (hG2 : InG2 ↥L) (hyL : xbar y ∈ L) (hZ : center ↥L ≠ ⊥) : False := by
  have hsh := generic_shapes_of_inG2 hF hset.simple hset.nonab hset.gen4 hset.kgh hy hG2
  have h7 : d2 ↥K = 7 := d2_eq_seven_of_shapeS3 hset.comp hset.g2 hset.shape
  have hle := (hmax.2 y L ⟨hy, hL, hG2⟩).1
  rcases hsh with h1 | h2 | h3 | h4 | h5
  · have := d2_le_six_of_shapeS1 hL hG2 h1
    omega
  · have := d2_le_six_of_shapeS2 hL hG2 hZ h2
    omega
  · exact h3.2 hyL
  · exact h4.2 hyL
  · exact h5.2 hyL

section Table

variable {G : Type} [Group G] [Finite G] {t : StatedLieTag} {p f : ℕ} {x y : G} {Iw Iv : Subgroup G}

theorem NbrData.vertical_inB2 (hKG : TwoThinKGroupVerticalQ Gen4Cen) (hgen : Gen4 G)
    (hnd : NbrData G t p f x y Iw Iv)
    {L : Subgroup (barQ ↥(centralizer ({y} : Set G)))} (hC2T2 : InC2 ↥L ∨ InT2 ↥L)
    (hL : CFSG.IsComponent L)
    (hv : conjSub (barMk _ ⟨x, hnd.x_mem_centralizer_y⟩)⁻¹ L = L)
    (hle : S45.barSub y Iv ≤ L) : InB2 ↥L := by
  have hso := orderOf_mk_centralizer hnd.x_mem_centralizer_y hnd.x_inv
  have hB := hnd.isPCompIn_Iv
  have hΛC := le_centralizer_mk hB.1 hnd.x_mem_centralizer_y
  have hΛ := isTwoComponent_centralizer_mk hB hnd.x_mem_centralizer_y
  have hIC : S45.barSub y Iv ≤
      centralizer ({barMk ↥(centralizer ({y} : Set G)) ⟨x, hnd.x_mem_centralizer_y⟩} :
        Set (barQ ↥(centralizer ({y} : Set G)))) :=
    (Subgroup.map_mono hΛC).trans (map_centralizer_barMk hso).le
  have hIpc : CFSG.GH74.GLS.IsPCompIn 2
      (centralizer ({barMk ↥(centralizer ({y} : Set G)) ⟨x, hnd.x_mem_centralizer_y⟩} :
        Set (barQ ↥(centralizer ({y} : Set G))))) (S45.barSub y Iv) :=
    isPCompIn_two_iff.mpr ⟨hIC, isTwoComponent_map_barMk hso hΛC hΛ⟩
  refine hKG (barQ ↥(centralizer ({y} : Set G))) (gen4Cen_barQ hgen hnd.y_inv)
    (barMk ↥(centralizer ({y} : Set G)) ⟨x, hnd.x_mem_centralizer_y⟩) L (S45.barSub y Iv)
    ↥(S45.barSub y Iv) (orderOf_barMk hso) hL hC2T2 hv hIpc hle hnd.barSub_inB2
    ⟨MonoidHom.id _, Function.surjective_id, ?_⟩
  rw [MonoidHom.ker_id]
  simp

end Table

end CFSG.GH74.Generic.S3
