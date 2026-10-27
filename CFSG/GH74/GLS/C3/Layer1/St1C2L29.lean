module

public import CFSG.GH74.GLS.C3.Layer1.St1Thm7
public import CFSG.GH74.Generic.ComponentBranches

public section

namespace CFSG.GH74.GLS

open CFSG Subgroup CFSG.Assembly.LowTwoRank
open scoped Matrix

section Central

variable {F : Type} [Field F]

theorem scalar_neg_one_val {ι : Type} [Fintype ι] [DecidableEq ι] :
    (((Matrix.GeneralLinearGroup.scalar ι (-1 : Fˣ) : GL ι F)) : Matrix ι ι F) = -1 := by
  rw [Matrix.GeneralLinearGroup.coe_scalar, Units.val_neg, Units.val_one, map_neg, map_one]

theorem scalar_neg_one_mem_SL {n : ℕ} (hn : Even n) :
    Matrix.GeneralLinearGroup.scalar (Fin n) (-1 : Fˣ) ∈ StatedSL n F := by
  apply Subgroup.subset_closure
  show (((Matrix.GeneralLinearGroup.scalar (Fin n) (-1 : Fˣ) : GL (Fin n) F)) :
    Matrix (Fin n) (Fin n) F).det = 1
  rw [scalar_neg_one_val, Matrix.det_neg, Matrix.det_one, Fintype.card_fin, hn.neg_one_pow]
  simp

theorem scalar_neg_one_mem_SU (q : ℕ) (hq : Odd q) :
    Matrix.GeneralLinearGroup.scalar (Fin 4) (-1 : Fˣ) ∈ StatedSU 4 q F := by
  apply Subgroup.subset_closure
  refine ⟨?_, ?_⟩
  · show (((Matrix.GeneralLinearGroup.scalar (Fin 4) (-1 : Fˣ) : GL (Fin 4) F)) :
      Matrix (Fin 4) (Fin 4) F).det = 1
    rw [scalar_neg_one_val, Matrix.det_neg, Matrix.det_one, Fintype.card_fin]
    norm_num
  · show ((((Matrix.GeneralLinearGroup.scalar (Fin 4) (-1 : Fˣ) : GL (Fin 4) F)) :
        Matrix (Fin 4) (Fin 4) F).map (· ^ q))ᵀ *
      (((Matrix.GeneralLinearGroup.scalar (Fin 4) (-1 : Fˣ) : GL (Fin 4) F)) :
        Matrix (Fin 4) (Fin 4) F) = 1
    rw [scalar_neg_one_val]
    have hmap : ((-1 : Matrix (Fin 4) (Fin 4) F).map (· ^ q)) = -1 := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [hq.neg_pow]
      · simp [hij, hq.pos.ne']
    rw [hmap]
    simp

theorem scalar_neg_one_mem_Sp (n : ℕ) :
    Matrix.GeneralLinearGroup.scalar (Fin n ⊕ Fin n) (-1 : Fˣ) ∈ StatedSp n F := by
  apply Subgroup.subset_closure
  show (((Matrix.GeneralLinearGroup.scalar (Fin n ⊕ Fin n) (-1 : Fˣ) : GL (Fin n ⊕ Fin n) F)) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)ᵀ * Matrix.fromBlocks 0 1 (-1) 0 *
    (((Matrix.GeneralLinearGroup.scalar (Fin n ⊕ Fin n) (-1 : Fˣ) : GL (Fin n ⊕ Fin n) F)) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) = Matrix.fromBlocks 0 1 (-1) 0
  rw [scalar_neg_one_val]
  simp

theorem false_of_center_bot_of_equiv {K : Type} [Group K] (hc : center K = ⊥) {ι : Type}
    [Fintype ι] [DecidableEq ι] [Nonempty ι] (hF : (-1 : F) ≠ 1)
    (H : Subgroup (GL ι F)) (hH : Matrix.GeneralLinearGroup.scalar ι (-1 : Fˣ) ∈ H)
    (e : K ≃* H) : False := by
  set s : H := ⟨Matrix.GeneralLinearGroup.scalar ι (-1 : Fˣ), hH⟩ with hs
  have hcent : e.symm s ∈ center K := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact Subtype.ext (Matrix.GeneralLinearGroup.scalar_commute _ _).symm
  have hne : s ≠ 1 := by
    intro h
    have h1 : Matrix.GeneralLinearGroup.scalar ι (-1 : Fˣ) = (1 : GL ι F) := congrArg Subtype.val h
    have h2 := congrArg (fun A : GL ι F => (A : Matrix ι ι F)) h1
    obtain ⟨i⟩ := ‹Nonempty ι›
    have h3 := congrFun (congrFun h2 i) i
    simp [Matrix.scalar_apply] at h3
    exact hF h3
  rw [hc, Subgroup.mem_bot] at hcent
  exact hne (e.symm.injective (hcent.trans e.symm.map_one.symm))

end Central

theorem not_excludedFromC2_of_center_eq_bot {K : Type} [Group K]
    (hZ : center K = ⊥) : ¬ ExcludedFromC2 K := by
  intro h
  rcases h with hSL2 | hAlt8 | hSL43 | hSU43 | hSp43 | hL34
  · obtain ⟨F, _, _, hFq, ⟨e⟩⟩ := hSL2
    exact false_of_center_bot_of_equiv (ι := Fin 2) hZ
      (neg_one_ne_one_of_odd_card F (isFM9_odd hFq)) _ (scalar_neg_one_mem_SL ⟨1, rfl⟩) e
  · obtain ⟨-, hcard, -⟩ := hAlt8
    rw [hZ, Subgroup.card_bot] at hcard
    omega
  · obtain ⟨F, _, _, hF3, ⟨e⟩⟩ := hSL43
    exact false_of_center_bot_of_equiv (ι := Fin 4) hZ
      (neg_one_ne_one_of_odd_card F (by rw [hF3]; exact (by decide : Odd 3))) _
      (scalar_neg_one_mem_SL ⟨2, rfl⟩) e
  · obtain ⟨F, _, _, hF9, ⟨e⟩⟩ := hSU43
    exact false_of_center_bot_of_equiv (ι := Fin 4) hZ
      (neg_one_ne_one_of_odd_card F (by rw [hF9]; exact (by decide : Odd 9))) _
      (scalar_neg_one_mem_SU 3 (by decide : Odd 3)) e
  · obtain ⟨F, _, _, hF3, ⟨e⟩⟩ := hSp43
    exact false_of_center_bot_of_equiv (ι := Fin 2 ⊕ Fin 2) hZ
      (neg_one_ne_one_of_odd_card F (by rw [hF3]; exact (by decide : Odd 3))) _
      (scalar_neg_one_mem_Sp 2) e
  · obtain ⟨-, hexp⟩ := hL34
    have : Subsingleton ↥(center K) := by
      refine ⟨fun a b => ?_⟩
      have ha : (a : K) ∈ (⊥ : Subgroup K) := hZ ▸ a.2
      have hb : (b : K) ∈ (⊥ : Subgroup K) := hZ ▸ b.2
      exact Subtype.ext ((Subgroup.mem_bot.mp ha).trans (Subgroup.mem_bot.mp hb).symm)
    rw [Monoid.exp_eq_one_of_subsingleton] at hexp
    omega

section Main

theorem pCore_eq_bot_of_simple {K : Type} [Group K] [Finite K] (hs : IsSimpleGroup K)
    (hc : center K = ⊥) : pCore 2 K = ⊥ := by
  have : (pCore 2 K).Normal := pCore_normal
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (pCore 2 K) with h | h
  · exact h
  · exfalso
    have hP : IsPGroup 2 ↥(⊤ : Subgroup K) := h ▸ pCore_isPGroup (p := 2) (G := K)
    have hP' : IsPGroup 2 K := hP.of_surjective (⊤ : Subgroup K).subtype Subgroup.topEquiv.surjective
    have hnil : Group.IsNilpotent K := hP'.isNilpotent
    have hcomm : ∀ a b : K, a * b = b * a :=
      IsSimpleGroup.comm_iff_isSolvable.mpr (inferInstance : Group.IsSolvable K)
    have hall : center K = ⊤ := by
      rw [eq_top_iff]
      intro a _
      exact Subgroup.mem_center_iff.mpr fun g => hcomm g a
    rw [hc] at hall
    exact absurd hall (bot_ne_top (α := Subgroup K))

theorem b_inC2_L29
    : B_inC2_L29 := by
  intro K _ hU2 hL29
  obtain ⟨p, f, hp, hf, h9, hL⟩ := hL29
  obtain ⟨hfin, -, hs⟩ := CFSG.LieType.Catalog.lieModel_finite_simple K _ _ p f hL
  have hq : IsQuasisimple K := hU2.1
  have hc : center K = ⊥ := center_eq_bot_of_simple_quasisimple hs hq
  have hp2 : pCore 2 K = ⊥ := pCore_eq_bot_of_simple hs hc
  refine ⟨hq, hc.trans hp2.symm, ?_, ?_⟩
  · have e : K ⧸ center K ≃* K :=
      (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
    exact E2.simpleInC2_of_mulEquiv e.symm
      (Generic.simpleInC2_of_fm9 hs hp hf (Or.inl h9) hL)
  · exact not_excludedFromC2_of_center_eq_bot hc

end Main

end CFSG.GH74.GLS
