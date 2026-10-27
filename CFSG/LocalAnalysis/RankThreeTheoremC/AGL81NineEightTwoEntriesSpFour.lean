module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineEightTwoEntries
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenSp4LocalModel
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.KlingenSpFour
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineEightTwoCriteria
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineEightTwoEntriesThree
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenSp4LocalAutCent

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

open Matrix CFSG.Open CFSG.AGLEmbedding.KlingenSpFour
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
open CFSG.AGLEmbedding (IsSpFourIndex)

section Matrix

variable {F : Type} [Field F]

theorem entry_inr_inl_eq_zero_of_commute_siegel {M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F}
    {S : Matrix (Fin 2) (Fin 2) F} (hS : IsUnit S.det)
    (h : M * fromBlocks 1 S 0 1 = fromBlocks 1 S 0 1 * M) (i j : Fin 2) :
    M (Sum.inr i) (Sum.inl j) = 0 := by
  obtain ⟨P, Q, R, T, rfl⟩ : ∃ P Q R T : Matrix (Fin 2) (Fin 2) F, M = fromBlocks P Q R T :=
    ⟨_, _, _, _, (fromBlocks_toBlocks M).symm⟩
  simp only [fromBlocks_multiply, Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero,
    Matrix.zero_mul, add_zero, zero_add] at h
  have hSR : S * R = 0 := by simpa using ((fromBlocks_inj.mp h).1).symm
  have hR : R = 0 := by
    calc R = S⁻¹ * (S * R) := by
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul S hS, Matrix.one_mul]
      _ = 0 := by rw [hSR, Matrix.mul_zero]
  rw [fromBlocks_apply₂₁, hR, Matrix.zero_apply]

theorem mulVec_mem_flag_two_of_entry {M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F}
    (hM : ∀ i j, M (Sum.inr i) (Sum.inl j) = 0) {v : Fin 2 ⊕ Fin 2 → F}
    (hv : v ∈ flag 2 F 2) : M *ᵥ v ∈ flag 2 F 2 := by
  rw [mem_flag_of_le le_rfl, mem_isoFlag] at hv ⊢
  refine ⟨fun i => ?_, fun j hj => absurd j.2 (not_lt.mpr hj)⟩
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, hM, hv.1]

theorem mem_stabilizer_flag_two_of_commute_xEl {g : StatedSp 2 F} {a b c : F}
    (hdet : a * c - b * b ≠ 0) (hg : g * xEl a b c = xEl a b c * g) :
    g ∈ stabilizer 2 F (flag 2 F 2) := by
  have hS : IsUnit (S2 a b c).det := by
    rw [isUnit_iff_ne_zero, Matrix.det_fin_two]
    simpa [S2] using hdet
  have key : ∀ h : StatedSp 2 F, h * xEl a b c = xEl a b c * h → ∀ v ∈ flag 2 F 2,
      ((h : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ v ∈
        flag 2 F 2 := by
    intro h hh v hv
    refine mulVec_mem_flag_two_of_entry (entry_inr_inl_eq_zero_of_commute_siegel hS ?_) hv
    have := congrArg (fun k : StatedSp 2 F =>
      ((k : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) hh
    simpa only [Subgroup.coe_mul, Units.val_mul, coe_xEl] using this
  have hg' : g⁻¹ * xEl a b c = xEl a b c * g⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hg, mul_inv_cancel_right]
  exact mem_stabilizer_of_mulVec_mem (key g hg) (key g⁻¹ hg')

end Matrix

variable {p : ℕ} [Fact p.Prime]

theorem centralizer_xS_le_normalizer_xS (hp2 : p ≠ 2) {a b c : ZMod p}
    (hdet : a * c - b * b ≠ 0) :
    Subgroup.centralizer ({(xS p).x a b c} : Set (PSp4 p)) ≤
      Subgroup.normalizer ((xS p).U : Set (PSp4 p)) := by
  intro y hy
  rw [normalizer_xS p hp2]
  obtain ⟨g, rfl⟩ := proj_surjective (r := 2) (K := ZMod p) y
  rw [← Subgroup.mem_comap, comap_projStabilizer]
  rw [Subgroup.mem_centralizer_singleton_iff, xS_x, ← map_mul, ← map_mul] at hy
  have h1 := QuotientGroup.eq.mp hy.symm
  rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at h1
  obtain ⟨t, ht⟩ := h1
  have h4 : (4 : ZMod p) ≠ 0 := by
    have : (4 : ZMod p) = 2 * 2 := by norm_num
    rw [this]
    exact mul_ne_zero (two_ne_zero_zmod p hp2) (two_ne_zero_zmod p hp2)
  have h3 : ((g * xEl a b c : StatedSp 2 (ZMod p)) : GL (Fin 2 ⊕ Fin 2) (ZMod p)) =
      ((xEl a b c * g : StatedSp 2 (ZMod p)) : GL (Fin 2 ⊕ Fin 2) (ZMod p)) *
        GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) t := by
    rw [ht, ← Subgroup.coe_mul, mul_inv_cancel_left]
  have h5 := congrArg (fun u : GL (Fin 2 ⊕ Fin 2) (ZMod p) =>
    (u : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod p))) h3
  simp only [Subgroup.coe_mul, Units.val_mul, coe_xEl, ac_coe_scalar, Matrix.mul_smul,
    Matrix.mul_one] at h5
  have hcomm := ac_comm_of_scalar _ _ (Units.mul_inv _) (Units.inv_mul _) h4 _ _ h5
  refine mem_stabilizer_flag_two_of_commute_xEl hdet (Subtype.ext (Units.ext ?_))
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_xEl]
  exact hcomm

theorem center_psp4_eq_bot (hp2 : p ≠ 2) : Subgroup.center (PSp4 p) = ⊥ := by
  have hp : p.Prime := Fact.out
  haveI : IsSimpleGroup (PSp4 p) := by
    refine CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp (ZMod p) 2
      (by norm_num) ?_
    rw [Nat.card_zmod]
    rcases Nat.lt_or_ge p 4 with h4 | h4
    · have hp3 : p = 3 := by
        have := hp.two_le
        omega
      exact Or.inr (Or.inl ⟨hp3, le_rfl⟩)
    · exact Or.inl (Or.inr h4)
  refine (IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (PSp4 p))).resolve_right
    fun h => (isCoatom_normalizer_xS p hp2).1 (eq_top_iff.mpr fun g _ => ?_)
  have hg : g ∈ Subgroup.center (PSp4 p) := h ▸ Subgroup.mem_top g
  refine Subgroup.mem_normalizer_iff.mpr fun n => ?_
  rw [← Subgroup.mem_center_iff.mp hg n, mul_inv_cancel_right]

theorem centralizer_conj_xS_le (hp2 : p ≠ 2) :
    Subgroup.centralizer (((xS p).U.map (MulAut.conj : PSp4 p →* MulAut (PSp4 p)) :
      Subgroup (MulAut (PSp4 p))) : Set (MulAut (PSp4 p))) ≤
        (xS p).U.map (MulAut.conj : PSp4 p →* MulAut (PSp4 p)) := by
  intro α hα
  have hZ := center_psp4_eq_bot hp2
  have hfix : ∀ u ∈ (xS p).U, α u = u := by
    intro u hu
    have h1 := Subgroup.mem_centralizer_iff.mp hα (MulAut.conj u) ⟨u, hu, rfl⟩
    have h2 : α * MulAut.conj u = MulAut.conj (α u) * α := by
      ext x
      simp [MulAut.conj_apply]
    have h3 : MulAut.conj (α u) = MulAut.conj u := (mul_right_cancel (h1.trans h2)).symm
    have h4 : (α u)⁻¹ * u ∈ Subgroup.center (PSp4 p) := by
      rw [Subgroup.mem_center_iff]
      intro x
      have h5 := congrArg (fun f : MulAut (PSp4 p) => f x) h3
      simp only [MulAut.conj_apply] at h5
      calc x * ((α u)⁻¹ * u) = (α u)⁻¹ * (α u * x * (α u)⁻¹) * u := by group
        _ = (α u)⁻¹ * (u * x * u⁻¹) * u := by rw [h5]
        _ = (α u)⁻¹ * u * x := by group
    rw [hZ, Subgroup.mem_bot, inv_mul_eq_one] at h4
    exact h4
  obtain ⟨k, hk, hαk⟩ := autCent_xS p hp2 α hfix
  exact ⟨k, hk, hαk.symm⟩

variable (p) in
@[expose] noncomputable def siegelPlane (ν : ZMod p) : Subgroup (PSp4 p) where
  carrier := {g | ∃ a b : ZMod p, g = (xS p).x a b (ν * a)}
  one_mem' := ⟨0, 0, by rw [mul_zero]; exact (xS p).x_zero.symm⟩
  mul_mem' := by
    rintro _ _ ⟨a, b, rfl⟩ ⟨a', b', rfl⟩
    exact ⟨a + a', b + b', by rw [(xS p).x_mul]; exact (xS p).x_congr rfl rfl (by ring)⟩
  inv_mem' := by
    rintro _ ⟨a, b, rfl⟩
    exact ⟨-a, -b, by rw [(xS p).x_inv]; exact (xS p).x_congr rfl rfl (mul_neg ν a).symm⟩

theorem siegelPlane_le (ν : ZMod p) : siegelPlane p ν ≤ (xS p).U := by
  rintro _ ⟨a, b, rfl⟩
  exact ⟨a, b, ν * a, rfl⟩

theorem card_siegelPlane (ν : ZMod p) : Nat.card (siegelPlane p ν) = p ^ 2 := by
  have hinj : Function.Injective (fun v : ZMod p × ZMod p => (xS p).x v.1 v.2 (ν * v.1)) := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    obtain ⟨rfl, rfl, -⟩ := (xS p).x_inj _ _ _ _ _ _ h
    rfl
  rw [card_eq_of_mem_iff_range (siegelPlane p ν) _ hinj
    (fun g => ⟨fun ⟨a, b, h⟩ => ⟨(a, b), h⟩, fun ⟨⟨a, b⟩, h⟩ => ⟨a, b, h⟩⟩),
    Nat.card_prod, Nat.card_zmod]
  ring

theorem det_ne_zero_of_siegelPlane {ν : ZMod p} (hν : ¬ IsSquare ν) {a b : ZMod p}
    (h1 : (xS p).x a b (ν * a) ≠ 1) : a * (ν * a) - b * b ≠ 0 := by
  intro h
  by_cases ha : a = 0
  · subst ha
    have hb : b = 0 := mul_self_eq_zero.mp (by linear_combination -h)
    subst hb
    exact h1 (by rw [mul_zero]; exact (xS p).x_zero)
  · refine hν ⟨b / a, ?_⟩
    rw [div_mul_div_comm, eq_div_iff (mul_ne_zero ha ha)]
    linear_combination h

theorem mulAut_eq_bot_of_conj_xS (hp2 : p ≠ 2) (V : Subgroup (MulAut (PSp4 p)))
    (hV : Nat.Coprime p (Nat.card V))
    (hUV : ∀ u ∈ (xS p).U, MulAut.conj u ∈ Subgroup.normalizer (V : Set (MulAut (PSp4 p)))) :
    V = ⊥ := by
  have hp : p.Prime := Fact.out
  obtain ⟨ν, hν⟩ := FiniteField.exists_nonsquare (F := ZMod p)
    (by rw [ZMod.ringChar_zmod_n]; exact hp2)
  have hU := (xS p).isElemAbelian_U
  refine mulAut_eq_bot_of_sig (center_psp4_eq_bot hp2) hp (T := (xS p).U)
    (B := siegelPlane p ν) (Q := (xS p).U) (siegelPlane_le ν) le_rfl
    (fun b hb => hU.2 b (siegelPlane_le ν hb)) (card_siegelPlane ν) hU.isPGroup
    (fun x hx => Subgroup.mem_centralizer_iff.mpr fun b hb => hU.comm (siegelPlane_le ν hb) hx)
    ?_ (centralizer_conj_xS_le hp2) V hV hUV
  rintro _ ⟨a, b, rfl⟩ h1
  exact centralizer_xS_le_normalizer_xS hp2 (det_ne_zero_of_siegelPlane hν h1)

theorem kFactNineThreeNoTwoAt_spFour {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {d : TauCeti.ValidLieTypeIndex} (hd : IsSpFourIndex p d) :
    KFactNineThreeNoTwoAt p (.lie d) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨ψ⟩ := nonempty_mulEquiv_psp4 hp2
    (statedClassicalModel_of_spFourIndex d hd (MulEquiv.refl (TauCeti.CFSGIndex.lie d).Group))
  exact kFactNineThreeNoTwoAt_of_model hp ⟨ψ.symm⟩ (xS p).isElemAbelian_U.isPGroup
    fun V hV hN => mulAut_eq_bot_of_conj_xS hp2 V
      (coprime_card_of_isPGroup hp Nat.prime_two hp2 hV) fun u hu => hN ⟨u, hu, rfl⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
