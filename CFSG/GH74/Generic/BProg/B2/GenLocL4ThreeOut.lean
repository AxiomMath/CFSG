module

public import CFSG.GH74.Generic.BProg.B2.GenLocL4OutAsm
public import CFSG.GH74.Generic.BProg.B2.GenLocL4ThreeSplit
public import CFSG.GH74.Generic.BProg.B2.GenLocL4ThreeExt
public import CFSG.GH74.Generic.BProg.B2.GenLocL4ThreeDa
public import CFSG.GH74.Generic.BProg.B2.GenLocL4ThreeDbLoc

public section

open CFSG CFSG.GH74 Subgroup Matrix
open scoped MatrixGroups

namespace CFSG.GH74.Generic.BProg.B2

local notation "K3" => ZMod 3

local notation "Mat" => Matrix (Fin 4) (Fin 4) K3

namespace GenLocL4ThreeOut

open GenLocL4Out

section Rank2

variable {A : Type} [Group A]

theorem rank2_three [Finite A] (hA : CFSG.IsElementaryAbelian 2 A) (hcard : Nat.card A = 4)
    (α : A →* MulAut SL(4, K3)) (hinj : Function.Injective α)
    (hsect : SectionalTwoRankLE ↥(innJoin α) 4) {u : A} (hu : ¬ IsInnerDiag4 (α u)) :
    gammaAct α = ⊤ := by
  have hF4 : Nat.card K3 % 4 = 3 := by rw [Nat.card_zmod]
  have hu1 : u ≠ 1 := fun h => hu (by rw [h, map_one]; exact isInnerDiag4_one)
  have hin := card_le_two_mul_innerSub hF4 hA α hsect hu
  obtain ⟨t, ht, ht1⟩ := exists_ne_one_of_one_lt (innerSub α) (by omega)
  have htin : IsInnerDiag4 (α t) := ht
  have ht2 : t * t = 1 := WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hA t
  have hα2 : α t * α t = 1 := by rw [← map_mul, ht2, map_one]
  obtain ⟨g, hg⟩ := htin
  have hout' : ¬ IsInnerDiag4 (α (t * u)) := by
    rw [map_mul]
    exact not_isInnerDiag4_mul hu ⟨g, hg⟩
  have htu1 : t * u ≠ 1 := fun h => hout' (by rw [h, map_one]; exact isInnerDiag4_one)
  obtain ⟨B, hB, hBt, hBd⟩ := graph_minus_of_sectional hF4 hA α u hu hsect
  obtain ⟨B', hB', hB't, hB'd⟩ := graph_minus_of_sectional hF4 hA α (t * u) hout' hsect
  rw [map_mul] at hB'
  obtain ⟨⟨μ, hμ, hgg⟩, hgB, hdetg⟩ := type_data (show GraphForm (α u) B from hB) hBt hBd hg hα2
    (show GraphForm (α t * α u) B' from hB') hB't hB'd
  have hnsc : ∀ c : K3, (g : Mat) ≠ c • (1 : Mat) := fun c hc =>
    ht1 (hinj (by rw [map_one]; exact eq_one_of_innerLift_scalar hg c hc))
  have hBdet0 : (B : Mat).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 B.isUnit).ne_zero
  have hfixB : ∀ x : SL(4, K3), (x : Mat) * B * (x : Mat)ᵀ = B → x ∈ gammaAct α := fun x hx =>
    mem_gamma_single hA (by omega) α hu1 x
      (graphEq_fix (coe_mul_inv B) (show GraphForm (α u) B from hB).graphEq x hx)
  have hfixg : ∀ x : SL(4, K3), (x : Mat) * g = g * (x : Mat) → x ∈ gammaAct α := fun x hx =>
    mem_gamma_single hA (by omega) α ht1 x (innerLift_fix hg x hx)
  have hfixgB : ∀ x : SL(4, K3), (x : Mat) * (g * B) * (x : Mat)ᵀ = g * B → x ∈ gammaAct α :=
    fun x hx => by
    have hMi : (g : Mat) * B * (((B⁻¹ : GL (Fin 4) K3) : Mat) *
        ((g⁻¹ : GL (Fin 4) K3) : Mat)) = 1 := by
      calc (g : Mat) * B * (((B⁻¹ : GL (Fin 4) K3) : Mat) * ((g⁻¹ : GL (Fin 4) K3) : Mat))
          = g * (B * ((B⁻¹ : GL (Fin 4) K3) : Mat)) * ((g⁻¹ : GL (Fin 4) K3) : Mat) := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [coe_mul_inv B, Matrix.mul_one, coe_mul_inv g]
    have := graphEq_fix hMi (graphEq_inner_mul (show GraphForm (α u) B from hB) hg) x hx
    refine mem_gamma_single hA (by omega) α htu1 x ?_
    rw [map_mul]
    exact this
  by_cases hsq : IsSquare μ
  · obtain ⟨ν, hν0, hεε, hεdet⟩ := split_norm hF4 hμ hgg hdetg hsq
    have hgε : (g : Mat) = ν • (ν⁻¹ • (g : Mat)) := by
      rw [smul_smul, mul_inv_cancel₀ hν0, one_smul]
    refine gen_split_three B (ν⁻¹ • (g : Mat)) hBt hBdet0 hεε ?_ ?_ hεdet ?_ (gammaAct α)
      (fun x hx => hfixg x (by rw [hgε, Matrix.mul_smul, Matrix.smul_mul, hx])) hfixB
    · intro h
      exact hnsc ν (by rw [hgε, h])
    · intro h
      exact hnsc (-ν) (by rw [hgε, h]; simp)
    · rw [Matrix.smul_mul, hgB, Matrix.transpose_smul, Matrix.mul_smul]
  · obtain ⟨l, hl0, hii⟩ := ext_norm hF4 hμ hgg hsq
    refine classExt_three B (l • (g : Mat)) hBt hBdet0 hBd hii ?_ (gammaAct α) ?_ hfixB ?_
    · rw [Matrix.smul_mul, hgB, Matrix.transpose_smul, Matrix.mul_smul]
    · intro x hx
      refine hfixg x ?_
      have := hx
      rw [Matrix.mul_smul, Matrix.smul_mul] at this
      exact (smul_right_injective _ hl0) this
    · intro x hx
      refine hfixgB x ?_
      rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul] at hx
      exact smul_right_injective _ hl0 hx

end Rank2

section Rank3

variable {A : Type} [Group A]

theorem rank3_Da_three [Finite A] (hA : CFSG.IsElementaryAbelian 2 A) (hcard : Nat.card A = 8)
    (α : A →* MulAut SL(4, K3)) (hinj : Function.Injective α) {u a b : A}
    (hu : ¬ IsInnerDiag4 (α u)) (ha1 : a ≠ 1) (hb1 : b ≠ 1) {B : GL (Fin 4) K3}
    (hB : GraphForm (α u) B) (hBt : (B : Mat)ᵀ = B) (hBd : ¬ IsSquare (B : Mat).det)
    (hain : IsInnerDiag4 (α a)) (hbin : IsInnerDiag4 (α b))
    (da : LiftData α (B : Mat) a) (db : LiftData α (B : Mat) b)
    (hcomm : (da.g : Mat) * db.g = db.g * da.g)
    (hμa : IsSquare da.μ) (hμb : ¬ IsSquare db.μ) : gammaAct α = ⊤ := by
  have hF4 : Nat.card K3 % 4 = 3 := by rw [Nat.card_zmod]
  have hu1 := one_ne_outer hu
  have hBdet0 : (B : Mat).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 B.isUnit).ne_zero
  have hnsc_a : ∀ c : K3, (da.g : Mat) ≠ c • (1 : Mat) := fun c hc =>
    ha1 (hinj (by rw [map_one]; exact eq_one_of_innerLift_scalar da.lift c hc))
  obtain ⟨νa, hνa0, hX2, hXdet⟩ := split_norm hF4 da.μ_ne da.sq da.detsq hμa
  obtain ⟨l, hl0, hi2⟩ := ext_norm hF4 db.μ_ne db.sq hμb
  have hga : (da.g : Mat) = νa • (νa⁻¹ • (da.g : Mat)) := by
    rw [smul_smul, mul_inv_cancel₀ hνa0, one_smul]
  have hBt' : ∀ (c : K3) (g : Mat), g * (B : Mat) = (B : Mat) * gᵀ →
      (c • g) * (B : Mat) = (B : Mat) * (c • g)ᵀ := fun c g h => by
    rw [Matrix.smul_mul, h, Matrix.transpose_smul, Matrix.mul_smul]
  have hcomm' : (νa⁻¹ • (da.g : Mat)) * (l • (db.g : Mat)) =
      (l • (db.g : Mat)) * (νa⁻¹ • (da.g : Mat)) := by
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hcomm, mul_comm]
  have fixA : ∀ x : SL(4, K3), (x : Mat) * (νa⁻¹ • (da.g : Mat)) =
      (νa⁻¹ • (da.g : Mat)) * (x : Mat) → α a x = x := fun x hx =>
    innerLift_fix da.lift x (by rw [hga]; exact comm_smul_of_comm νa hx)
  have fixB : ∀ x : SL(4, K3), (x : Mat) * (l • (db.g : Mat)) =
      (l • (db.g : Mat)) * (x : Mat) → α b x = x := fun x hx =>
    innerLift_fix db.lift x (comm_smul_cancel hl0 hx)
  have fixU : ∀ x : SL(4, K3), (x : Mat) * (B : Mat) * (x : Mat)ᵀ = B → α u x = x :=
    fun x hx => graphEq_fix (coe_mul_inv B) hB.graphEq x hx
  have fixBU : ∀ x : SL(4, K3), (x : Mat) * ((l • (db.g : Mat)) * (B : Mat)) * (x : Mat)ᵀ =
      (l • (db.g : Mat)) * (B : Mat) → α (b * u) x = x := fun x hx =>
    fix_au hB db x (by
      rw [Matrix.smul_mul] at hx
      exact form_smul_cancel hl0 hx)
  refine classDa_three (B : Mat) (νa⁻¹ • (da.g : Mat)) (l • (db.g : Mat)) hBt hBdet0 hBd hX2
    hXdet ?_ ?_ hi2 hcomm' (hBt' _ _ da.comp) (hBt' _ _ db.comp) (gammaAct α) ?_ ?_ ?_
  · exact fun h => hnsc_a νa (by rw [hga, h])
  · exact fun h => hnsc_a (-νa) (by rw [hga, h]; simp)
  · exact fun x hxa hxB => mem_gamma_pair hA (by omega) α ha1 hu1 (ne_of_inner_outer hain hu) x
      (fixA x hxa) (fixU x hxB)
  · exact fun x hxa hxM => mem_gamma_pair hA (by omega) α ha1 (outer_mul_ne_one hbin hu)
      (inner_ne_outer_mul hain hbin hu) x (fixA x hxa) (fixBU x hxM)
  · exact fun x hxb hxB => mem_gamma_pair hA (by omega) α hb1 hu1 (ne_of_inner_outer hbin hu) x
      (fixB x hxb) (fixU x hxB)

def liftMul {α : A →* MulAut SL(4, K3)} {B : Mat} {a b : A} (da : LiftData α B a)
    (db : LiftData α B b) (h : (da.g : Mat) * db.g = db.g * da.g) : LiftData α B (a * b) where
  g := da.g * db.g
  lift := by rw [map_mul]; exact innerLift_mul da.lift db.lift
  μ := da.μ * db.μ
  μ_ne := mul_ne_zero da.μ_ne db.μ_ne
  sq := by
    rw [Units.val_mul]
    have hsa := da.sq
    have hsb := db.sq
    have hh := h
    set ga : Mat := (da.g : Mat)
    set gb : Mat := (db.g : Mat)
    calc ga * gb * (ga * gb) = ga * (gb * ga) * gb := by simp only [Matrix.mul_assoc]
      _ = ga * (ga * gb) * gb := by rw [← hh]
      _ = (ga * ga) * (gb * gb) := by simp only [Matrix.mul_assoc]
      _ = (da.μ * db.μ) • (1 : Mat) := by
          rw [hsa, hsb, Matrix.smul_mul, Matrix.one_mul, smul_smul]
  comp := by
    rw [Units.val_mul]
    have hca := da.comp
    have hcb := db.comp
    have hh := h
    set ga : Mat := (da.g : Mat)
    set gb : Mat := (db.g : Mat)
    calc ga * gb * B = ga * (gb * B) := by rw [Matrix.mul_assoc]
      _ = ga * (B * gbᵀ) := by rw [hcb]
      _ = (ga * B) * gbᵀ := by rw [Matrix.mul_assoc]
      _ = B * gaᵀ * gbᵀ := by rw [hca]
      _ = B * (gb * ga)ᵀ := by rw [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = B * (ga * gb)ᵀ := by rw [hh]
  detsq := by
    rw [Units.val_mul, Matrix.det_mul]
    exact da.detsq.mul db.detsq

theorem rank3_main_three [Finite A] (hA : CFSG.IsElementaryAbelian 2 A) (hcard : Nat.card A = 8)
    (α : A →* MulAut SL(4, K3)) (hinj : Function.Injective α)
    (hsect : SectionalTwoRankLE ↥(innJoin α) 4) {u : A} (hu : ¬ IsInnerDiag4 (α u)) :
    gammaAct α = ⊤ ∨ (LocE1 α ∧ LocE2 α ∧ LocE3 α) := by
  have hF4 : Nat.card K3 % 4 = 3 := by rw [Nat.card_zmod]
  have hF2 : (2 : K3) ≠ 0 := Ring.two_ne_zero (ringChar_ne_two_of_card_mod hF4)
  have hin := card_le_two_mul_innerSub hF4 hA α hsect hu
  obtain ⟨t, s, ht, hs, ht1, hs1, hts⟩ := exists_two_ne_one (innerSub α) (by omega)
  have htin : IsInnerDiag4 (α t) := ht
  have hsin : IsInnerDiag4 (α s) := hs
  obtain ⟨B, hB, hBt, hBd⟩ := graph_minus_of_sectional hF4 hA α u hu hsect
  have hB' : GraphForm (α u) B := hB
  obtain ⟨dt⟩ := exists_liftData hF4 hA α hsect hu htin hB' hBt hBd
  obtain ⟨ds⟩ := exists_liftData hF4 hA α hsect hu hsin hB' hBt hBd
  have hcommA : t * s = s * t := by
    have := hA
    exact mul_comm' t s
  have hcomm := LiftData.comm hF2 dt ds hcommA hBt hBd
  by_cases hμt : IsSquare dt.μ
  · by_cases hμs : IsSquare ds.μ
    · exact Or.inr (rank3_Db_loc_three hA hcard α hinj hu ht1 hs1 hts hB' hBt hBd htin hsin dt ds
        hcomm hμt hμs)
    · exact Or.inl (rank3_Da_three hA hcard α hinj hu ht1 hs1 hB' hBt hBd htin hsin dt ds hcomm
        hμt hμs)
  · by_cases hμs : IsSquare ds.μ
    · exact Or.inl (rank3_Da_three hA hcard α hinj hu hs1 ht1 hB' hBt hBd hsin htin ds dt
        hcomm.symm hμs hμt)
    · have hts1 : t * s ≠ 1 := fun h => hts (by
        have ht2 : t * t = 1 := WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hA t
        exact (mul_left_cancel (h.trans ht2.symm)).symm)
      have hcomm2 : ((liftMul dt ds hcomm).g : Mat) * dt.g = dt.g * (liftMul dt ds hcomm).g := by
        show ((dt.g * ds.g : GL (Fin 4) K3) : Mat) * dt.g =
          dt.g * ((dt.g * ds.g : GL (Fin 4) K3) : Mat)
        simp only [Units.val_mul, Matrix.mul_assoc]
        rw [← hcomm]
      have hμts : IsSquare (liftMul dt ds hcomm).μ := isSquare_mul_of_not_isSquare hμt hμs
      have htsin : IsInnerDiag4 (α (t * s)) := by
        rw [map_mul]
        exact isInnerDiag4_mul htin hsin
      exact Or.inl (rank3_Da_three hA hcard α hinj hu hts1 ht1 hB' hBt hBd htsin htin
        (liftMul dt ds hcomm) dt hcomm2 hμts hμt)

end Rank3

end GenLocL4ThreeOut

variable {A : Type} [Group A]

theorem genOrLoc_sl4_outer_three [Finite A] (α : A →* MulAut SL(4, K3)) (hA : IsRank23 A)
    (hout : ∃ a : A, ¬ GenLocL4Out.IsInnerDiag4 (α a))
    (hsect : SectionalTwoRankLE ↥(innJoin α) 4) :
    gammaAct α = ⊤ ∨ (LocE1 α ∧ LocE2 α ∧ LocE3 α) := by
  by_cases hex : ∃ E : Subgroup A, pRank 2 A - 1 ≤ pRank 2 ↥E ∧ E ≤ α.ker
  · obtain ⟨E, hE, hk⟩ := hex
    exact Or.inl (gammaAct_eq_top_of_le_ker α hE hk)
  · simp only [not_exists, not_and] at hex
    obtain ⟨hR, hg, h1, h2, h3⟩ := range_reduction α hA hex
    rw [hg, h1, h2, h3]
    have hfin : Finite ↥α.range := Finite.of_surjective _ α.rangeRestrict_surjective
    obtain ⟨a, ha⟩ := hout
    have hsectD : SectionalTwoRankLE ↥(innJoin α.range.subtype) 4 := by
      have : innJoin α.range.subtype = innJoin α := by
        unfold innJoin
        rw [Subgroup.range_subtype]
      rw [this]
      exact hsect
    have huD : ¬ GenLocL4Out.IsInnerDiag4 (α.range.subtype ⟨α a, a, rfl⟩) := ha
    have hcard := GenLocBasic.card_eq_two_pow_pRank_type hR.1
    rcases hR.2 with hr2 | hr3
    · exact Or.inl (GenLocL4ThreeOut.rank2_three hR.1 (by rw [hcard, hr2]; norm_num)
        α.range.subtype Subtype.val_injective hsectD huD)
    · exact GenLocL4ThreeOut.rank3_main_three hR.1 (by rw [hcard, hr3]; norm_num)
        α.range.subtype Subtype.val_injective hsectD huD

end CFSG.GH74.Generic.BProg.B2
