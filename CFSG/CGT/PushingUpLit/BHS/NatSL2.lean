module

public import CFSG.CGT.PushingUpLit.BHS.GlaubOne
public import CFSG.CGT.PushingUpLit.BHS.GlaubSylow
public import CFSG.CGT.PushingUpLit.BHS.NaturalDefs
public import CFSG.CGT.PushingUpLit.BHS.Replacement
public import CFSG.RankThree.PartOne.S9.Defs
public import CFSG.Quasithin.Background.A1bBasic
public import CFSG.Quasithin.Background.D2Offenders
public import CFSG.Timmesfeld.ARS.NaturalModule
public import CFSG.CGT.PushingUpLit.BHS.SymNatDefs
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.SectionRank.Ccomm.OddCritical
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.RankThree.PartOne

variable {V : Type} [CommGroup V] [Finite V]

@[expose] def SylowGood (L : Subgroup (MulAut V)) : Prop :=
  ∀ S : Subgroup (MulAut V), IsSylowOf 2 S L →
    IsQuadratic S ∧ Nat.card V = Nat.card S * Nat.card (fixV S)

namespace NatSL2

open Matrix CFSG.Timmesfeld.RankOne CFSG.Timmesfeld.ARS.NaturalModule
open CFSG.Timmesfeld (upperUnipotent lowerUnipotent)

section SL2

variable {F : Type*} [Field F]

local instance slAct : DistribMulAction (SpecialLinearGroup (Fin 2) F) (Fin 2 → F) where
  smul g w := (g : Matrix (Fin 2) (Fin 2) F) *ᵥ w
  one_smul w := by
    show ((1 : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ w = w
    rw [Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  mul_smul g h w := by
    show ((g * h : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ w =
      (g : Matrix (Fin 2) (Fin 2) F) *ᵥ ((h : Matrix (Fin 2) (Fin 2) F) *ᵥ w)
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mulVec_mulVec]
  smul_zero g := Matrix.mulVec_zero _
  smul_add g v w := Matrix.mulVec_add _ _ _

theorem smul_def' (g : SpecialLinearGroup (Fin 2) F) (w : Fin 2 → F) :
    g • w = (g : Matrix (Fin 2) (Fin 2) F) *ᵥ w := rfl

theorem smul_scalar_comm (g : SpecialLinearGroup (Fin 2) F) (c : F) (w : Fin 2 → F) :
    g • (c • w) = c • (g • w) := Matrix.mulVec_smul _ _ _

@[expose] def stabVec (w : Fin 2 → F) : Subgroup (SpecialLinearGroup (Fin 2) F) :=
  MulAction.stabilizer (SpecialLinearGroup (Fin 2) F) w

theorem mem_stabVec {g : SpecialLinearGroup (Fin 2) F} {w : Fin 2 → F} :
    g ∈ stabVec w ↔ g • w = w := MulAction.mem_stabilizer_iff

theorem stabVec_smul (h : SpecialLinearGroup (Fin 2) F) (w : Fin 2 → F) :
    stabVec (h • w) = conjSub h (stabVec w) :=
  MulAction.stabilizer_smul_eq_stabilizer_map_conj h w

theorem mem_stabVec_smul (h g : SpecialLinearGroup (Fin 2) F) (w : Fin 2 → F) :
    g ∈ stabVec (h • w) ↔ h⁻¹ * g * h ∈ stabVec w := by
  rw [stabVec_smul]
  exact mem_conjSub_iff

theorem stabVec_e₁ : stabVec (![1, 0] : Fin 2 → F) = upperUnipotent F := by
  ext g
  rw [mem_stabVec, mem_upperUnipotent_iff]
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp only [smul_def', mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, mul_one, mul_zero, add_zero] at h0 h1
    have hdet := g.2
    rw [det_fin_two, h0, h1, mul_zero, sub_zero, one_mul] at hdet
    refine ⟨(g : Matrix (Fin 2) (Fin 2) F) 0 1, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [coe_upperElt, h0, h1, hdet]
  · rintro ⟨t, rfl⟩
    rw [smul_def', upperElt_mulVec]
    ext i
    fin_cases i <;> simp

theorem exists_smul_e₁ {w : Fin 2 → F} (hw : w ≠ 0) :
    ∃ h : SpecialLinearGroup (Fin 2) F, h • (![1, 0] : Fin 2 → F) = w :=
  exists_mulVec_eq hw

theorem mem_stabVec_iff_exists (h g : SpecialLinearGroup (Fin 2) F) :
    g ∈ stabVec (h • (![1, 0] : Fin 2 → F)) ↔ ∃ t : F, g = h * upperElt F t * h⁻¹ := by
  rw [mem_stabVec_smul, stabVec_e₁, mem_upperUnipotent_iff]
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t, by rw [← ht]; group⟩
  · rintro ⟨t, rfl⟩
    exact ⟨t, by group⟩

theorem e₁_ne_zero : (![1, 0] : Fin 2 → F) ≠ 0 := by
  intro h
  have := congrFun h 0
  simp at this

theorem card_stabVec {w : Fin 2 → F} (hw : w ≠ 0) : Nat.card (stabVec w) = Nat.card F := by
  obtain ⟨h, rfl⟩ := exists_smul_e₁ hw
  rw [stabVec_smul, stabVec_e₁, conjSub,
    Subgroup.card_map_of_injective (MulAut.conj h).injective, card_upperUnipotent]

theorem forall_smul_eq_iff {w : Fin 2 → F} (hw : w ≠ 0) (y : Fin 2 → F) :
    (∀ g ∈ stabVec w, g • y = y) ↔ ∃ c : F, y = c • w := by
  obtain ⟨h, rfl⟩ := exists_smul_e₁ hw
  constructor
  · intro H
    obtain ⟨z, rfl⟩ : ∃ z, y = h • z := ⟨h⁻¹ • y, (smul_inv_smul h y).symm⟩
    have hu : ∀ t : F, (upperElt F t : Matrix (Fin 2) (Fin 2) F) *ᵥ z = z := by
      intro t
      have hg := H _ ((mem_stabVec_iff_exists h _).2 ⟨t, rfl⟩)
      rw [mul_smul, mul_smul, inv_smul_smul] at hg
      exact MulAction.injective h hg
    have hz1 := (forall_upperElt_mulVec_eq_iff z).1 hu
    refine ⟨z 0, ?_⟩
    have hz : z = z 0 • (![1, 0] : Fin 2 → F) := by
      ext i
      fin_cases i <;> simp [hz1]
    exact (congrArg (fun x => h • x) hz).trans (smul_scalar_comm h (z 0) _)
  · rintro ⟨c, rfl⟩ g hg
    rw [smul_scalar_comm, mem_stabVec.1 hg]

theorem stabVec_eq_iff {w w' : Fin 2 → F} (hw : w ≠ 0) (hw' : w' ≠ 0) :
    stabVec w' = stabVec w ↔ ∃ c : F, w' = c • w := by
  constructor
  · intro h
    refine (forall_smul_eq_iff hw w').1 fun g hg => ?_
    rw [← h] at hg
    exact mem_stabVec.1 hg
  · rintro ⟨c, rfl⟩
    have hc : c ≠ 0 := by
      rintro rfl
      exact hw' (zero_smul F w)
    ext g
    rw [mem_stabVec, mem_stabVec, smul_scalar_comm]
    constructor
    · intro h
      exact smul_right_injective (Fin 2 → F) hc h
    · intro h
      rw [h]

theorem second_coord_ne_zero {h : SpecialLinearGroup (Fin 2) F} {z : Fin 2 → F}
    (hne : ¬ ∃ c : F, h • z = c • (h • (![1, 0] : Fin 2 → F))) : z 1 ≠ 0 := by
  intro h1
  apply hne
  refine ⟨z 0, ?_⟩
  have hz : z = z 0 • (![1, 0] : Fin 2 → F) := by
    ext i
    fin_cases i <;> simp [h1]
  exact (congrArg (fun x => h • x) hz).trans (smul_scalar_comm h (z 0) _)

theorem stabVec_inf_eq_bot {w w' : Fin 2 → F} (hw : w ≠ 0) (hw' : w' ≠ 0)
    (hne : ¬ ∃ c : F, w' = c • w) : stabVec w ⊓ stabVec w' = ⊥ := by
  obtain ⟨h, rfl⟩ := exists_smul_e₁ hw
  obtain ⟨z, rfl⟩ : ∃ z, w' = h • z := ⟨h⁻¹ • w', (smul_inv_smul h w').symm⟩
  have hz : z 1 ≠ 0 := second_coord_ne_zero hne
  rw [eq_bot_iff]
  rintro g ⟨hg, hg'⟩
  rw [Subgroup.mem_bot]
  obtain ⟨t, rfl⟩ := (mem_stabVec_iff_exists h g).1 hg
  have h2 := mem_stabVec.1 hg'
  rw [mul_smul, mul_smul, inv_smul_smul] at h2
  have h3 : (upperElt F t : Matrix (Fin 2) (Fin 2) F) *ᵥ z = z := MulAction.injective h h2
  have h4 : t * z 1 = 0 := by
    have := congrFun h3 0
    rw [upperElt_mulVec] at this
    simpa using this
  have ht : t = 0 := (mul_eq_zero.1 h4).resolve_right hz
  rw [ht, upperElt_zero]
  group

theorem eq_upper_mul_lower_mul_upper (M : SpecialLinearGroup (Fin 2) F)
    (hc : (M : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0) :
    M = upperElt F (((M : Matrix (Fin 2) (Fin 2) F) 0 0 - 1) /
        (M : Matrix (Fin 2) (Fin 2) F) 1 0) *
      lowerElt F ((M : Matrix (Fin 2) (Fin 2) F) 1 0) *
      upperElt F (((M : Matrix (Fin 2) (Fin 2) F) 1 1 - 1) /
        (M : Matrix (Fin 2) (Fin 2) F) 1 0) := by
  have hdet := M.2
  rw [det_fin_two] at hdet
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_upperElt, coe_lowerElt, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp <;> first | ring1 | linear_combination hdet | linear_combination -hdet

@[expose] def mkSL (a b c d : F) (h : a * d - b * c = 1) : SpecialLinearGroup (Fin 2) F :=
  ⟨!![a, b; c, d], by simp [det_fin_two, h]⟩

theorem coe_mkSL (a b c d : F) (h : a * d - b * c = 1) :
    (mkSL a b c d h : Matrix (Fin 2) (Fin 2) F) = !![a, b; c, d] := rfl

theorem upperUnipotent_sup_stabVec_eq_top {z : Fin 2 → F} (hz : z 1 ≠ 0) :
    upperUnipotent F ⊔ stabVec z = ⊤ := by
  have hl : ∀ s : F, lowerElt F s ∈ upperUnipotent F ⊔ stabVec z := by
    intro s
    by_cases hs : s = 0
    · rw [hs, lowerElt_zero]
      exact one_mem _
    obtain ⟨t, ht⟩ : ∃ t : F, t * z 1 ^ 2 = -s := ⟨-s / z 1 ^ 2, by field_simp⟩
    obtain ⟨g, hg, hg10⟩ : ∃ g : SpecialLinearGroup (Fin 2) F, g ∈ stabVec z ∧
        (g : Matrix (Fin 2) (Fin 2) F) 1 0 = s := by
      refine ⟨mkSL (1 - t * z 0 * z 1) (t * z 0 ^ 2) (-(t * z 1 ^ 2)) (1 + t * z 0 * z 1)
        (by ring), mem_stabVec.2 ?_, ?_⟩
      · rw [smul_def', coe_mkSL]
        ext i
        fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_two] <;> ring
      · rw [coe_mkSL, ht]
        simp
    have hdec := eq_upper_mul_lower_mul_upper g (hg10 ▸ hs)
    rw [hg10] at hdec
    obtain ⟨x, y, hxy⟩ : ∃ x y : F, g = upperElt F x * lowerElt F s * upperElt F y :=
      ⟨_, _, hdec⟩
    have hls : lowerElt F s = (upperElt F x)⁻¹ * g * (upperElt F y)⁻¹ := by
      rw [hxy]
      group
    rw [hls]
    exact mul_mem (mul_mem (inv_mem (Subgroup.mem_sup_left ((mem_upperUnipotent_iff F).2
      ⟨x, rfl⟩))) (Subgroup.mem_sup_right hg)) (inv_mem (Subgroup.mem_sup_left
        ((mem_upperUnipotent_iff F).2 ⟨y, rfl⟩)))
  have hlow : lowerUnipotent F ≤ upperUnipotent F ⊔ stabVec z := by
    intro g hg
    obtain ⟨s, rfl⟩ := (mem_lowerUnipotent_iff F).1 hg
    exact hl s
  rw [eq_top_iff, ← upperUnipotent_sup_lowerUnipotent (K := F)]
  exact sup_le le_sup_left hlow

theorem stabVec_sup_eq_top {w w' : Fin 2 → F} (hw : w ≠ 0) (hw' : w' ≠ 0)
    (hne : ¬ ∃ c : F, w' = c • w) : stabVec w ⊔ stabVec w' = ⊤ := by
  obtain ⟨h, rfl⟩ := exists_smul_e₁ hw
  obtain ⟨z, rfl⟩ : ∃ z, w' = h • z := ⟨h⁻¹ • w', (smul_inv_smul h w').symm⟩
  have hz : z 1 ≠ 0 := second_coord_ne_zero hne
  rw [stabVec_smul, stabVec_smul, stabVec_e₁, conjSub, conjSub, ← Subgroup.map_sup,
    upperUnipotent_sup_stabVec_eq_top hz, Subgroup.map_top,
    MonoidHom.range_eq_top.2 (MulAut.conj h).surjective]

theorem exists_smul_sub_eq {w : Fin 2 → F} (hw : w ≠ 0) {g : SpecialLinearGroup (Fin 2) F}
    (hg : g ∈ stabVec w) (hg1 : g ≠ 1) (c : F) : ∃ x : Fin 2 → F, g • x - x = c • w := by
  obtain ⟨h, rfl⟩ := exists_smul_e₁ hw
  obtain ⟨t, rfl⟩ := (mem_stabVec_iff_exists h g).1 hg
  have ht : t ≠ 0 := by
    rintro rfl
    apply hg1
    rw [upperElt_zero]
    group
  refine ⟨h • ![0, c / t], ?_⟩
  rw [mul_smul, mul_smul, inv_smul_smul, ← smul_sub]
  have key : (upperElt F t : Matrix (Fin 2) (Fin 2) F) *ᵥ ![0, c / t] - ![0, c / t] =
      c • (![1, 0] : Fin 2 → F) := by
    rw [upperElt_mulVec_sub]
    ext i
    fin_cases i
    · simp
      field_simp
    · simp
  rw [show upperElt F t • (![0, c / t] : Fin 2 → F) - ![0, c / t] = c • (![1, 0] : Fin 2 → F)
    from key]
  exact smul_scalar_comm h c _

theorem exists_smul_of_smul_eq {w : Fin 2 → F} (hw : w ≠ 0) {g : SpecialLinearGroup (Fin 2) F}
    (hg : g ∈ stabVec w) (hg1 : g ≠ 1) {y : Fin 2 → F} (hy : g • y = y) :
    ∃ c : F, y = c • w := by
  obtain ⟨h, rfl⟩ := exists_smul_e₁ hw
  obtain ⟨t, rfl⟩ := (mem_stabVec_iff_exists h g).1 hg
  have ht : t ≠ 0 := by
    rintro rfl
    apply hg1
    rw [upperElt_zero]
    group
  refine (forall_smul_eq_iff hw y).1 fun g' hg' => ?_
  obtain ⟨s, rfl⟩ := (mem_stabVec_iff_exists h g').1 hg'
  obtain ⟨z, rfl⟩ : ∃ z, y = h • z := ⟨h⁻¹ • y, (smul_inv_smul h y).symm⟩
  rw [mul_smul, mul_smul, inv_smul_smul] at hy ⊢
  have hu : (upperElt F t : Matrix (Fin 2) (Fin 2) F) *ᵥ z = z := MulAction.injective h hy
  have h1 : z 1 = 0 := by
    have h2 := congrFun hu 0
    rw [upperElt_mulVec] at h2
    have h4 : t * z 1 = 0 := by simpa using h2
    exact (mul_eq_zero.1 h4).resolve_left ht
  exact congrArg (fun x => h • x) ((forall_upperElt_mulVec_eq_iff z).2 h1 s)

theorem exists_eq_diagElt_mul_upperElt {g : SpecialLinearGroup (Fin 2) F}
    (hg : g ∈ Subgroup.normalizer (upperUnipotent F : Set (SpecialLinearGroup (Fin 2) F))) :
    ∃ (c : Fˣ) (t : F), g = diagElt c * upperElt F t := by
  have h1 : g * upperElt F 1 * g⁻¹ ∈ upperUnipotent F :=
    (Subgroup.mem_normalizer_iff.1 hg _).1 ((mem_upperUnipotent_iff F).2 ⟨1, rfl⟩)
  obtain ⟨t, ht⟩ := (mem_upperUnipotent_iff F).1 h1
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [upperElt_zero] at ht
    have h2 : upperElt F 1 = 1 := by
      have h3 : upperElt F 1 = g⁻¹ * (g * upperElt F 1 * g⁻¹) * g := by group
      rw [h3, ht]
      group
    exact one_ne_zero (upperElt_injective F (h2.trans (upperElt_zero F).symm))
  have hu1 : upperElt F 1 • (![1, 0] : Fin 2 → F) = ![1, 0] := by
    rw [smul_def', upperElt_mulVec]
    ext i
    fin_cases i <;> simp
  have hfix : upperElt F t • (g • (![1, 0] : Fin 2 → F)) = g • ![1, 0] := by
    calc upperElt F t • (g • (![1, 0] : Fin 2 → F))
        = (g * upperElt F 1 * g⁻¹ * g) • (![1, 0] : Fin 2 → F) := by rw [ht, mul_smul]
      _ = g • (upperElt F 1 • (![1, 0] : Fin 2 → F)) := by
        rw [show g * upperElt F 1 * g⁻¹ * g = g * upperElt F 1 by group, mul_smul]
      _ = g • ![1, 0] := by rw [hu1]
  have hg10 : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
    have h2 := congrFun hfix 0
    rw [smul_def', upperElt_mulVec] at h2
    have h3 : t * (g • (![1, 0] : Fin 2 → F)) 1 = 0 := by
      simpa using h2
    have h4 := (mul_eq_zero.1 h3).resolve_left ht0
    simpa [smul_def', mulVec, dotProduct, Fin.sum_univ_two] using h4
  have hdet := g.2
  rw [det_fin_two, hg10, mul_zero, sub_zero] at hdet
  have ha : (g : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdet
  have hd : (g : Matrix (Fin 2) (Fin 2) F) 1 1 = ((g : Matrix (Fin 2) (Fin 2) F) 0 0)⁻¹ :=
    eq_inv_of_mul_eq_one_right hdet
  refine ⟨Units.mk0 _ ha, (g : Matrix (Fin 2) (Fin 2) F) 0 1 * (g : Matrix (Fin 2) (Fin 2) F) 1 1,
    ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, coe_diagElt, coe_upperElt, Matrix.mul_apply,
      Fin.sum_univ_two, hg10, hd]
  field_simp

theorem eq_zero_of_diagElt_smul {c : Fˣ} (hc : c ≠ 1) {z : Fin 2 → F}
    (h : diagElt c • z = z) : z = 0 := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [smul_def', diagElt_mulVec, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  have hc' : (c : F) ≠ 1 := fun h => hc (Units.ext h)
  ext i
  fin_cases i
  · have h2 : ((c : F) - 1) * z 0 = 0 := by linear_combination h0
    simpa [sub_eq_zero, hc'] using h2
  · have h2 : (((c⁻¹ : Fˣ) : F) - 1) * z 1 = 0 := by linear_combination h1
    simpa [sub_eq_zero, hc] using h2

theorem diagElt_injective : Function.Injective (diagElt : Fˣ → SpecialLinearGroup (Fin 2) F) := by
  intro c d h
  apply Units.ext
  have := congrArg (fun g : SpecialLinearGroup (Fin 2) F =>
    (g : Matrix (Fin 2) (Fin 2) F) 0 0) h
  simpa [coe_diagElt] using this

@[expose] def diagHom : Fˣ →* SpecialLinearGroup (Fin 2) F :=
  MonoidHom.mk' diagElt fun a b => (diagElt_mul_diagElt a b).symm

theorem stabVec_comm {w : Fin 2 → F} (hw : w ≠ 0) {a b : SpecialLinearGroup (Fin 2) F}
    (ha : a ∈ stabVec w) (hb : b ∈ stabVec w) : a * b = b * a := by
  obtain ⟨h, rfl⟩ := exists_smul_e₁ hw
  obtain ⟨s, rfl⟩ := (mem_stabVec_iff_exists h a).1 ha
  obtain ⟨t, rfl⟩ := (mem_stabVec_iff_exists h b).1 hb
  have e1 : h * upperElt F s * h⁻¹ * (h * upperElt F t * h⁻¹) =
      h * (upperElt F s * upperElt F t) * h⁻¹ := by group
  have e2 : h * upperElt F t * h⁻¹ * (h * upperElt F s * h⁻¹) =
      h * (upperElt F t * upperElt F s) * h⁻¹ := by group
  rw [e1, e2, upperElt_mul, upperElt_mul, add_comm]

theorem stabVec_sq [CharP F 2] {w : Fin 2 → F} (hw : w ≠ 0) {a : SpecialLinearGroup (Fin 2) F}
    (ha : a ∈ stabVec w) : a ^ 2 = 1 := by
  obtain ⟨h, rfl⟩ := exists_smul_e₁ hw
  obtain ⟨s, rfl⟩ := (mem_stabVec_iff_exists h a).1 ha
  rw [pow_two, show h * upperElt F s * h⁻¹ * (h * upperElt F s * h⁻¹) =
    h * (upperElt F s * upperElt F s) * h⁻¹ by group, upperElt_mul_self]
  group

@[expose] def line (w : Fin 2 → F) : Subgroup (Multiplicative (Fin 2 → F)) where
  carrier := {x | ∃ c : F, Multiplicative.toAdd x = c • w}
  one_mem' := ⟨0, by simp⟩
  mul_mem' := by
    rintro a b ⟨c, hc⟩ ⟨d, hd⟩
    exact ⟨c + d, by rw [toAdd_mul, hc, hd, add_smul]⟩
  inv_mem' := by
    rintro a ⟨c, hc⟩
    exact ⟨-c, by rw [toAdd_inv, hc, neg_smul]⟩

theorem card_line {w : Fin 2 → F} (hw : w ≠ 0) : Nat.card (line w) = Nat.card F := by
  refine Nat.card_congr (Equiv.symm (Equiv.ofBijective
    (fun c : F => (⟨Multiplicative.ofAdd (c • w), c, rfl⟩ : line w)) ⟨?_, ?_⟩))
  · intro c d h
    have := congrArg (fun x : line w => Multiplicative.toAdd (x : Multiplicative (Fin 2 → F))) h
    exact smul_left_injective F hw this
  · rintro ⟨x, c, hc⟩
    refine ⟨c, Subtype.ext ?_⟩
    show Multiplicative.ofAdd (c • w) = x
    rw [← hc]
    rfl

theorem card_sl2_arith (Q : ℕ) (hQ : 2 ≤ Q) :
    (Q ^ 2 - Q ^ 0) * (Q ^ 2 - Q ^ 1) / (Q - 1) = Q * (Q ^ 2 - 1) := by
  obtain ⟨P, rfl⟩ : ∃ P, Q = P + 2 := ⟨Q - 2, by omega⟩
  have e1 : (P + 2) ^ 2 - 1 = (P + 1) * (P + 3) :=
    Nat.sub_eq_of_eq_add (by ring)
  have e2 : (P + 2) ^ 2 - (P + 2) = (P + 1) * (P + 2) :=
    Nat.sub_eq_of_eq_add (by ring)
  have e3 : P + 2 - 1 = P + 1 := by omega
  rw [pow_zero, pow_one, e1, e2, e3]
  exact Nat.div_eq_of_eq_mul_left (by omega) (by ring)

theorem card_comap_of_surjective {G H : Type*} [Group G] [Group H] [Finite G] (f : G →* H)
    (hf : Function.Surjective f) (K : Subgroup H) :
    Nat.card (K.comap f) = Nat.card f.ker * Nat.card K := by
  have h1 := Subgroup.card_mul_index (K.comap f)
  have h2 := Subgroup.card_mul_index K
  have h3 := Subgroup.card_ker_mul_card_of_surjective hf
  rw [Subgroup.index_comap_of_surjective K hf] at h1
  have : Finite H := Finite.of_surjective f hf
  have hpos : 0 < K.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  apply Nat.eq_of_mul_eq_mul_right hpos
  calc Nat.card (K.comap f) * K.index = Nat.card G := h1
    _ = Nat.card f.ker * Nat.card H := h3.symm
    _ = Nat.card f.ker * (Nat.card K * K.index) := by rw [h2]
    _ = _ := by ring

theorem sylow_conj_aux {L S S' : Subgroup (MulAut V)} (hS : IsSylowOf 2 S L)
    (hS' : IsSylowOf 2 S' L) : ∃ x ∈ L, S' = conjSub x S := by
  obtain ⟨k, hk, hle⟩ := Glauberman.exists_conj_le_of_isSylowOf hS hS'.2.1 hS'.1
  have hcard : Nat.card S' = Nat.card S := by
    rw [(CFSG.ABGLocalTools.isSylowOf_iff.2 hS).card_eq,
      (CFSG.ABGLocalTools.isSylowOf_iff.2 hS').card_eq]
  have hk' : conjSub k S' = S := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    show Nat.card S ≤ Nat.card (S'.map (MulAut.conj k).toMonoidHom)
    rw [Glauberman.card_map_conj k S', hcard]
  refine ⟨k⁻¹, L.inv_mem hk, ?_⟩
  rw [← hk', ← conjSub_mul, inv_mul_cancel, conjSub_one]

end SL2

section Data

omit [Finite V]

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

@[expose] def commMap (s : MulAut V) : V →* V :=
  MonoidHom.mk' (fun v => s v * v⁻¹) fun x y => by
    rw [map_mul, mul_inv, mul_mul_mul_comm]

theorem commV_zpowers_eq_range (s : MulAut V) :
    commV (Subgroup.zpowers s) = (commMap s).range := by
  have key : ∀ x ∈ Subgroup.zpowers s, ∀ v : V, x v * v⁻¹ ∈ (commMap s).range := by
    intro x hx
    rw [Subgroup.zpowers_eq_closure] at hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      intro v
      rw [Set.mem_singleton_iff.1 hy]
      exact ⟨v, rfl⟩
    | one =>
      intro v
      simp
    | mul y z _ _ hy hz =>
      intro v
      have h1 := Subgroup.mul_mem _ (hy (z v)) (hz v)
      simpa [MulAut.mul_apply, mul_assoc] using h1
    | inv y _ hy =>
      intro v
      have h1 := hy (y⁻¹ v)
      rw [MulAut.apply_inv_self] at h1
      simpa using Subgroup.inv_mem _ h1
  apply le_antisymm
  · rw [commV, Subgroup.closure_le]
    rintro _ ⟨x, hx, v, rfl⟩
    exact key x hx v
  · rintro _ ⟨v, rfl⟩
    exact Subgroup.subset_closure ⟨s, Subgroup.mem_zpowers s, v, rfl⟩

theorem ker_commMap (s : MulAut V) : (commMap s).ker = fixV (Subgroup.zpowers s) := by
  ext v
  rw [MonoidHom.mem_ker, Glauberman.mem_fixV_zpowers]
  show s v * v⁻¹ = 1 ↔ s v = v
  exact mul_inv_eq_one

structure NatData (L : Subgroup (MulAut V)) (F : Type*) [Field F] [Finite F] [CharP F 2]
    (n : ℕ) where
  ι : SpecialLinearGroup (Fin 2) F →* MulAut V
  β : V →* Multiplicative (Fin 2 → F)
  injective_ι : Function.Injective ι
  range_ι : ι.range = L
  surjective_β : Function.Surjective β
  ker_β : β.ker = fixV L
  β_ι : ∀ (g : SpecialLinearGroup (Fin 2) F) (v : V),
    Multiplicative.toAdd (β (ι g v)) = g • Multiplicative.toAdd (β v)
  card_F : Nat.card F = 2 ^ n
  one_le : 1 ≤ n

namespace NatData

variable {L : Subgroup (MulAut V)} {n : ℕ} (D : NatData L F n)

include D

theorem ι_mem (g : SpecialLinearGroup (Fin 2) F) : D.ι g ∈ L := by
  have h : D.ι g ∈ D.ι.range := MonoidHom.mem_range.2 ⟨g, rfl⟩
  rwa [D.range_ι] at h

theorem exists_ι_eq {x : MulAut V} (hx : x ∈ L) : ∃ g, D.ι g = x := by
  rw [← D.range_ι] at hx
  exact MonoidHom.mem_range.1 hx

@[expose] def vec (v : V) : Fin 2 → F := Multiplicative.toAdd (D.β v)

theorem vec_mul (v w : V) : D.vec (v * w) = D.vec v + D.vec w := by
  simp [vec]

theorem vec_inv (v : V) : D.vec v⁻¹ = - D.vec v := by
  simp [vec]

theorem vec_div (v w : V) : D.vec (v * w⁻¹) = D.vec v - D.vec w := by
  rw [vec_mul, vec_inv, sub_eq_add_neg]

theorem vec_ι (g : SpecialLinearGroup (Fin 2) F) (v : V) : D.vec (D.ι g v) = g • D.vec v :=
  D.β_ι g v

theorem vec_eq_zero_iff (v : V) : D.vec v = 0 ↔ v ∈ fixV L := by
  rw [← D.ker_β, MonoidHom.mem_ker]
  simp [vec]

theorem exists_vec (w : Fin 2 → F) : ∃ v : V, D.vec v = w := by
  obtain ⟨v, hv⟩ := D.surjective_β (Multiplicative.ofAdd w)
  exact ⟨v, by simp [vec, hv]⟩

@[expose] def Vw (w : Fin 2 → F) : Subgroup V := (line w).comap D.β

theorem mem_Vw {w : Fin 2 → F} {v : V} : v ∈ D.Vw w ↔ ∃ c : F, D.vec v = c • w := Iff.rfl

theorem card_V : Nat.card V = 4 ^ n * Nat.card (fixV L) := by
  have h := Subgroup.card_ker_mul_card_of_surjective D.surjective_β
  rw [D.ker_β] at h
  have hF : Nat.card (Multiplicative (Fin 2 → F)) = 4 ^ n := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_fin, D.card_F,
      ← pow_mul, mul_comm, pow_mul]
    norm_num
  rw [← h, hF, mul_comm]

theorem card_L : Nat.card L = 2 ^ n * (4 ^ n - 1) := by
  have h1 : Nat.card L = Nat.card (SpecialLinearGroup (Fin 2) F) := by
    rw [← D.range_ι]
    exact (Nat.card_congr (MonoidHom.ofInjective D.injective_ι).toEquiv).symm
  have : Fintype F := Fintype.ofFinite F
  have h2 := Matrix.card_SL_field (𝔽 := F) 2
  rw [Fintype.card_eq_nat_card, D.card_F] at h2
  rw [h1, h2, Fin.prod_univ_two]
  have h4 : (4 : ℕ) ^ n = (2 ^ n) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  rw [h4]
  have := D.one_le
  exact card_sl2_arith (2 ^ n) (by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) this)

@[expose] def stab (w : Fin 2 → F) : Subgroup (MulAut V) := (stabVec w).map D.ι

theorem mem_stab {w : Fin 2 → F} {x : MulAut V} :
    x ∈ D.stab w ↔ ∃ g ∈ stabVec w, D.ι g = x := Subgroup.mem_map

theorem ι_mem_stab_iff {w : Fin 2 → F} {g : SpecialLinearGroup (Fin 2) F} :
    D.ι g ∈ D.stab w ↔ g ∈ stabVec w :=
  Subgroup.mem_map_iff_mem D.injective_ι

theorem stab_le (w : Fin 2 → F) : D.stab w ≤ L := by
  intro x hx
  obtain ⟨g, -, rfl⟩ := D.mem_stab.1 hx
  exact D.ι_mem g

theorem card_stab {w : Fin 2 → F} (hw : w ≠ 0) : Nat.card (D.stab w) = 2 ^ n := by
  rw [stab, Subgroup.card_map_of_injective D.injective_ι, card_stabVec hw, D.card_F]

theorem conjSub_map (g : SpecialLinearGroup (Fin 2) F)
    (A : Subgroup (SpecialLinearGroup (Fin 2) F)) :
    conjSub (D.ι g) (A.map D.ι) = (conjSub g A).map D.ι := by
  unfold conjSub
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext a
  simp [MulAut.conj_apply]

theorem stab_eq_iff {w w' : Fin 2 → F} (hw : w ≠ 0) (hw' : w' ≠ 0) :
    D.stab w' = D.stab w ↔ ∃ c : F, w' = c • w := by
  rw [← stabVec_eq_iff hw hw']
  exact (Subgroup.map_injective D.injective_ι).eq_iff

theorem mem_normalizer_of_ι_mem {A : Subgroup (SpecialLinearGroup (Fin 2) F)}
    {g : SpecialLinearGroup (Fin 2) F}
    (hg : D.ι g ∈ Subgroup.normalizer ((A.map D.ι : Subgroup (MulAut V)) : Set (MulAut V))) :
    g ∈ Subgroup.normalizer (A : Set (SpecialLinearGroup (Fin 2) F)) := by
  rw [Subgroup.mem_normalizer_iff] at hg ⊢
  intro y
  have h := hg (D.ι y)
  rw [← map_inv, ← map_mul, ← map_mul, Subgroup.mem_map_iff_mem D.injective_ι,
    Subgroup.mem_map_iff_mem D.injective_ι] at h
  exact h

theorem ι_mem_normalizer_map {A : Subgroup (SpecialLinearGroup (Fin 2) F)}
    {g : SpecialLinearGroup (Fin 2) F}
    (hg : g ∈ Subgroup.normalizer (A : Set (SpecialLinearGroup (Fin 2) F))) :
    D.ι g ∈ Subgroup.normalizer ((A.map D.ι : Subgroup (MulAut V)) : Set (MulAut V)) :=
  Subgroup.le_normalizer_map D.ι ⟨g, hg, rfl⟩

theorem isElemAbelian2_stab {w : Fin 2 → F} (hw : w ≠ 0) : IsElemAbelian2 (D.stab w) := by
  refine ⟨?_, ?_⟩
  · intro a ha b hb
    obtain ⟨a, ha', rfl⟩ := D.mem_stab.1 ha
    obtain ⟨b, hb', rfl⟩ := D.mem_stab.1 hb
    rw [← map_mul, ← map_mul, stabVec_comm hw ha' hb']
  · intro x hx
    obtain ⟨a, ha', rfl⟩ := D.mem_stab.1 hx
    rw [← map_pow, stabVec_sq hw ha', map_one]

theorem fixV_stab_le_Vw {w : Fin 2 → F} (hw : w ≠ 0) : fixV (D.stab w) ≤ D.Vw w := by
  intro v hv
  rw [mem_Vw]
  refine (forall_smul_eq_iff hw (D.vec v)).1 fun g hg => ?_
  rw [← D.vec_ι, hv (D.ι g) (D.mem_stab.2 ⟨g, hg, rfl⟩)]

theorem Vw_le_commV_sup {w : Fin 2 → F} (hw : w ≠ 0) :
    D.Vw w ≤ commV (D.stab w) ⊔ fixV L := by
  intro v hv
  obtain ⟨c, hc⟩ := D.mem_Vw.1 hv
  obtain ⟨g, hg, hg1⟩ : ∃ g ∈ stabVec w, g ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have h1 := card_stabVec hw
    rw [(Subgroup.eq_bot_iff_forall _).2 hcon, Subgroup.card_bot, D.card_F] at h1
    have := Nat.one_lt_two_pow (n := n) (by have := D.one_le; omega)
    omega
  obtain ⟨x, hx⟩ := exists_smul_sub_eq hw hg hg1 c
  obtain ⟨v', hv'⟩ := D.exists_vec x
  have hu : D.ι g v' * v'⁻¹ ∈ commV (D.stab w) :=
    Subgroup.subset_closure ⟨D.ι g, D.mem_stab.2 ⟨g, hg, rfl⟩, v', rfl⟩
  have hvu : D.vec (D.ι g v' * v'⁻¹) = D.vec v := by
    rw [D.vec_div, D.vec_ι, hv', hx, hc]
  have hz : v * (D.ι g v' * v'⁻¹)⁻¹ ∈ fixV L :=
    (D.vec_eq_zero_iff _).1 (by rw [D.vec_div, hvu, sub_self])
  have hv2 : v = (v * (D.ι g v' * v'⁻¹)⁻¹) * (D.ι g v' * v'⁻¹) := by group
  rw [hv2]
  exact mul_mem (Subgroup.mem_sup_right hz) (Subgroup.mem_sup_left hu)

theorem stab_inf_eq_bot {w w' : Fin 2 → F} (hw : w ≠ 0) (hw' : w' ≠ 0)
    (hne : ¬ ∃ c : F, w' = c • w) : D.stab w ⊓ D.stab w' = ⊥ := by
  rw [stab, stab, ← Subgroup.map_inf _ _ D.ι D.injective_ι, stabVec_inf_eq_bot hw hw' hne,
    Subgroup.map_bot]

theorem stab_sup_eq {w w' : Fin 2 → F} (hw : w ≠ 0) (hw' : w' ≠ 0)
    (hne : ¬ ∃ c : F, w' = c • w) : D.stab w ⊔ D.stab w' = L := by
  rw [stab, stab, ← Subgroup.map_sup, stabVec_sup_eq_top hw hw' hne, Subgroup.map_top,
    D.range_ι]

theorem exists_complement_stab {w : Fin 2 → F} (hw : w ≠ 0) :
    ∃ K : Subgroup (MulAut V), K ≤ L ∧ K ⊓ D.stab w = ⊥ ∧
      K ⊔ D.stab w = Subgroup.normalizer (D.stab w : Set (MulAut V)) ⊓ L ∧
      Nat.card K = 2 ^ n - 1 ∧
      ∀ k ∈ K, k ≠ 1 → ∀ v : V, k v * v⁻¹ ∈ fixV L → v ∈ fixV L := by
  obtain ⟨h, rfl⟩ := exists_smul_e₁ hw
  obtain ⟨κ, hκ⟩ : ∃ κ : Fˣ →* MulAut V, ∀ c : Fˣ, κ c = D.ι (h * diagElt c * h⁻¹) :=
    ⟨D.ι.comp ((MulAut.conj h).toMonoidHom.comp diagHom), fun c => by
      simp [diagHom, MulAut.conj_apply]⟩
  have hκinj : Function.Injective κ := by
    intro c d hcd
    rw [hκ, hκ] at hcd
    have h1 := D.injective_ι hcd
    have h2 : diagElt c = diagElt d := by
      have h3 : h⁻¹ * (h * diagElt c * h⁻¹) * h = h⁻¹ * (h * diagElt d * h⁻¹) * h := by rw [h1]
      simpa [mul_assoc] using h3
    exact diagElt_injective h2
  have hnorm : ∀ c : Fˣ, h * diagElt c * h⁻¹ ∈ Subgroup.normalizer
      (stabVec (h • (![1, 0] : Fin 2 → F)) : Set (SpecialLinearGroup (Fin 2) F)) := by
    intro c
    rw [stabVec_smul, stabVec_e₁, ← conjSub_normalizer]
    exact mem_conjSub_of_mem (diagElt_mem_normalizer_upperUnipotent c)
  refine ⟨κ.range, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨c, rfl⟩
    rw [hκ]
    exact D.ι_mem _
  · rw [eq_bot_iff]
    rintro x ⟨⟨c, rfl⟩, hx⟩
    rw [Subgroup.mem_bot]
    have h1 : h * diagElt c * h⁻¹ ∈ stabVec (h • (![1, 0] : Fin 2 → F)) :=
      D.ι_mem_stab_iff.1 (hκ c ▸ hx)
    rw [mem_stabVec_smul, show h⁻¹ * (h * diagElt c * h⁻¹) * h = diagElt c by group,
      mem_stabVec] at h1
    have h2 := congrFun h1 0
    rw [smul_def', diagElt_mulVec] at h2
    simp at h2
    rw [h2, map_one]
  · apply le_antisymm
    · refine sup_le (le_inf ?_ ?_) (le_inf Subgroup.le_normalizer (D.stab_le _))
      · rintro _ ⟨c, rfl⟩
        rw [hκ]
        exact D.ι_mem_normalizer_map (hnorm c)
      · rintro _ ⟨c, rfl⟩
        rw [hκ]
        exact D.ι_mem _
    · rintro x ⟨hxn, hxL⟩
      obtain ⟨g, rfl⟩ := D.exists_ι_eq hxL
      have hg := D.mem_normalizer_of_ι_mem (A := stabVec (h • (![1, 0] : Fin 2 → F))) hxn
      have hg' : h⁻¹ * g * h ∈ Subgroup.normalizer
          (upperUnipotent F : Set (SpecialLinearGroup (Fin 2) F)) := by
        rw [stabVec_smul, stabVec_e₁, ← conjSub_normalizer] at hg
        exact mem_conjSub_iff.1 hg
      obtain ⟨c, t, hct⟩ := exists_eq_diagElt_mul_upperElt hg'
      have hgeq : g = (h * diagElt c * h⁻¹) * (h * upperElt F t * h⁻¹) :=
        calc g = h * (h⁻¹ * g * h) * h⁻¹ := by group
          _ = _ := by rw [hct]; group
      rw [hgeq, map_mul]
      exact Subgroup.mul_mem_sup ⟨c, hκ c⟩
        (D.mem_stab.2 ⟨_, (mem_stabVec_iff_exists h _).2 ⟨t, rfl⟩, rfl⟩)
  · rw [Nat.card_congr (MonoidHom.ofInjective hκinj).toEquiv.symm, Nat.card_units, D.card_F]
  · rintro _ ⟨c, rfl⟩ hk v hv
    have hc : c ≠ 1 := fun hc => hk (by rw [hc, map_one])
    have h1 := (D.vec_eq_zero_iff _).2 hv
    rw [D.vec_div, hκ c, D.vec_ι, sub_eq_zero, mul_smul, mul_smul] at h1
    have h2 : diagElt c • (h⁻¹ • D.vec v) = h⁻¹ • D.vec v := by
      have := congrArg (fun x => h⁻¹ • x) h1
      simpa [inv_smul_smul] using this
    rw [← D.vec_eq_zero_iff]
    exact (smul_eq_zero_iff_eq h⁻¹).1 (eq_zero_of_diagElt_smul hc h2)

end NatData

end Data

section DataFinite

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

namespace NatData

variable {L : Subgroup (MulAut V)} {n : ℕ} (D : NatData L F n)

include D

theorem card_Vw {w : Fin 2 → F} (hw : w ≠ 0) :
    Nat.card (D.Vw w) = Nat.card F * Nat.card (fixV L) := by
  rw [Vw, card_comap_of_surjective D.β D.surjective_β, card_line hw, D.ker_β, mul_comm]

theorem isSylow_stab {w : Fin 2 → F} (hw : w ≠ 0) : IsSylowOf 2 (D.stab w) L := by
  refine ⟨D.stab_le w, ?_, ?_⟩
  · rw [IsPGroup.iff_card]
    exact ⟨n, D.card_stab hw⟩
  · have h1 := Subgroup.relIndex_mul_card (D.stab w) L
    rw [inf_eq_left.2 (D.stab_le w), D.card_stab hw, D.card_L] at h1
    have h2 : (D.stab w).relIndex L = 4 ^ n - 1 := by
      apply Nat.eq_of_mul_eq_mul_right (pow_pos two_pos n)
      rw [h1, mul_comm]
    rw [h2]
    have h3 : 2 ∣ 4 ^ n := dvd_pow (by norm_num) (by have := D.one_le; omega)
    have h4 : 0 < 4 ^ n := by positivity
    omega

theorem exists_stab_of_sylow {S : Subgroup (MulAut V)} (hS : IsSylowOf 2 S L) :
    ∃ w : Fin 2 → F, w ≠ 0 ∧ S = D.stab w := by
  have he : (![1, 0] : Fin 2 → F) ≠ 0 := e₁_ne_zero
  obtain ⟨x, hx, hxS⟩ := sylow_conj_aux (D.isSylow_stab he) hS
  obtain ⟨g, rfl⟩ := D.exists_ι_eq hx
  refine ⟨g • (![1, 0] : Fin 2 → F), fun h0 => he ((smul_eq_zero_iff_eq g).1 h0), ?_⟩
  rw [hxS, stab, stab, stabVec_smul]
  exact D.conjSub_map g _

theorem card_fixV_stab (hG : SylowGood L) {w : Fin 2 → F} (hw : w ≠ 0) :
    Nat.card (fixV (D.stab w)) = 2 ^ n * Nat.card (fixV L) := by
  have h1 := (hG _ (D.isSylow_stab hw)).2
  rw [D.card_V, D.card_stab hw] at h1
  have h4 : (4 : ℕ) ^ n = 2 ^ n * 2 ^ n := by
    rw [← mul_pow]
    norm_num
  rw [h4, mul_assoc] at h1
  exact (Nat.eq_of_mul_eq_mul_left (pow_pos two_pos n) h1).symm

theorem fixV_stab (hG : SylowGood L) {w : Fin 2 → F} (hw : w ≠ 0) :
    fixV (D.stab w) = D.Vw w := by
  refine Subgroup.eq_of_le_of_card_ge (D.fixV_stab_le_Vw hw) ?_
  rw [D.card_Vw hw, D.card_fixV_stab hG hw, D.card_F]

theorem fixV_stab_eq (hG : SylowGood L) {w : Fin 2 → F} (hw : w ≠ 0) :
    fixV (D.stab w) = commV (D.stab w) ⊔ fixV L := by
  refine le_antisymm ?_ (sup_le (hG _ (D.isSylow_stab hw)).1 (fixV_anti (D.stab_le w)))
  rw [D.fixV_stab hG hw]
  exact D.Vw_le_commV_sup hw

theorem commV_zpowers_inf_fixV_stab (hG : SylowGood L) {w : Fin 2 → F} (hw : w ≠ 0)
    {s : MulAut V} (hs : s ∈ D.stab w) (hs1 : s ≠ 1) :
    commV (Subgroup.zpowers s) ⊓ fixV L = ⊥ := by
  rw [eq_bot_iff]
  intro u hu
  obtain ⟨hu1, hu2⟩ := Subgroup.mem_inf.1 hu
  rw [commV_zpowers_eq_range] at hu1
  obtain ⟨v, rfl⟩ := hu1
  obtain ⟨g, hg, rfl⟩ := D.mem_stab.1 hs
  have hg1 : g ≠ 1 := by
    rintro rfl
    exact hs1 (map_one D.ι)
  have h1 := (D.vec_eq_zero_iff _).2 hu2
  change D.vec (D.ι g v * v⁻¹) = 0 at h1
  rw [D.vec_div, D.vec_ι, sub_eq_zero] at h1
  obtain ⟨c, hc⟩ := exists_smul_of_smul_eq hw hg hg1 h1
  have hv : v ∈ fixV (D.stab w) := by
    rw [D.fixV_stab hG hw, mem_Vw]
    exact ⟨c, hc⟩
  have hsv : D.ι g v = v := hv (D.ι g) (D.mem_stab.2 ⟨g, hg, rfl⟩)
  show D.ι g v * v⁻¹ ∈ (⊥ : Subgroup V)
  rw [hsv, mul_inv_cancel]
  exact Subgroup.one_mem _

theorem fixV_stab_inf_sup (hG : SylowGood L) {w w' : Fin 2 → F} (hw : w ≠ 0) (hw' : w' ≠ 0)
    (hne : ¬ ∃ c : F, w' = c • w) :
    fixV (D.stab w) ⊓ fixV (D.stab w') = fixV L ∧ fixV (D.stab w) ⊔ fixV (D.stab w') = ⊤ := by
  have hinf : fixV (D.stab w) ⊓ fixV (D.stab w') = fixV L := by
    refine le_antisymm ?_ (le_inf (fixV_anti (D.stab_le w)) (fixV_anti (D.stab_le w')))
    intro v hv
    obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 hv
    rw [D.fixV_stab hG hw, mem_Vw] at h1
    rw [D.fixV_stab hG hw', mem_Vw] at h2
    obtain ⟨c, hc⟩ := h1
    obtain ⟨c', hc'⟩ := h2
    have hc'0 : c' = 0 := by
      by_contra h0
      refine hne ⟨c / c', ?_⟩
      have h3 : c' • w' = c • w := hc'.symm.trans hc
      rw [div_eq_inv_mul, mul_smul, ← h3, smul_smul, inv_mul_cancel₀ h0, one_smul]
    rw [← D.vec_eq_zero_iff, hc', hc'0, zero_smul]
  refine ⟨hinf, ?_⟩
  have hcard := card_sup_mul_card_inf' (X := fixV (D.stab w)) (Y := fixV (D.stab w'))
    (fun x _ y _ => mul_comm x y)
  rw [hinf, D.card_fixV_stab hG hw, D.card_fixV_stab hG hw'] at hcard
  have hpos : 0 < Nat.card (fixV L) := Nat.card_pos
  refine (Subgroup.card_eq_iff_eq_top _).1 ?_
  rw [D.card_V]
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [hcard]
  have h4 : (4 : ℕ) ^ n = 2 ^ n * 2 ^ n := by
    rw [← mul_pow]
    norm_num
  rw [h4]
  ring

theorem ncard_sylows :
    Set.ncard {S : Subgroup (MulAut V) | IsSylowOf 2 S L} = 2 ^ n + 1 := by
  let f : Projectivization F (Fin 2 → F) → Subgroup (MulAut V) := fun p => D.stab p.rep
  have hf : Function.Injective f := by
    intro p p' hpp
    obtain ⟨c, hc⟩ := (D.stab_eq_iff p.rep_nonzero p'.rep_nonzero).1 hpp.symm
    have h1 : Projectivization.mk F p'.rep p'.rep_nonzero =
        Projectivization.mk F p.rep p.rep_nonzero :=
      (Projectivization.mk_eq_mk_iff' F _ _ _ _).2 ⟨c, hc.symm⟩
    rw [Projectivization.mk_rep, Projectivization.mk_rep] at h1
    exact h1.symm
  have hrange : {S : Subgroup (MulAut V) | IsSylowOf 2 S L} = Set.range f := by
    ext S
    constructor
    · intro hS
      obtain ⟨w, hw, rfl⟩ := D.exists_stab_of_sylow hS
      refine ⟨Projectivization.mk F w hw, ?_⟩
      obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep F w hw
      exact (D.stab_eq_iff hw (Projectivization.rep_nonzero _)).2
        ⟨(a : F), ha.symm.trans (Units.smul_def a w)⟩
    · rintro ⟨p, rfl⟩
      exact D.isSylow_stab p.rep_nonzero
  rw [hrange, Set.ncard_range_of_injective hf]
  have hcard := Projectivization.card F (Fin 2 → F)
  rw [Nat.card_fun, Nat.card_fin, D.card_F] at hcard
  obtain ⟨P, hP⟩ : ∃ P, 2 ^ n = P + 2 :=
    ⟨2 ^ n - 2, by have := Nat.one_lt_two_pow (n := n) (by have := D.one_le; omega); omega⟩
  rw [hP] at hcard ⊢
  have e1 : (P + 2) ^ 2 - 1 = (P + 3) * (P + 1) := Nat.sub_eq_of_eq_add (by ring)
  have e2 : P + 2 - 1 = P + 1 := by omega
  rw [e1, e2] at hcard
  exact (Nat.eq_of_mul_eq_mul_right (by omega) hcard).symm

end NatData

end DataFinite

end NatSL2

namespace IsSLNatSection

variable {L : Subgroup (MulAut V)} {n : ℕ}

omit [Finite V] in
theorem nonempty_natData (h : IsSLNatSection L ⊤ (fixV L) n) (hn : 1 ≤ n) :
    Nonempty (NatSL2.NatData L (GaloisField 2 n) n) := by
  obtain ⟨-, θ, β, hsurj, hker, hact⟩ := h
  refine ⟨{ ι := L.subtype.comp θ.symm.toMonoidHom
            β := β.comp (Subgroup.topEquiv (G := V)).symm.toMonoidHom
            injective_ι := ?_, range_ι := ?_, surjective_β := ?_, ker_β := ?_, β_ι := ?_
            card_F := GaloisField.card 2 n (by omega)
            one_le := hn }⟩
  · intro a b hab
    exact θ.symm.injective (Subtype.ext hab)
  · ext x
    constructor
    · rintro ⟨g, rfl⟩
      exact (θ.symm g).2
    · intro hx
      exact ⟨θ ⟨x, hx⟩, by simp⟩
  · exact hsurj.comp (MulEquiv.surjective _)
  · ext v
    rw [MonoidHom.mem_ker]
    show β ⟨v, trivial⟩ = 1 ↔ _
    rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
  · intro g v
    have h1 := hact (θ.symm g) ⟨v, trivial⟩ trivial
    have h2 := congrArg Multiplicative.toAdd h1
    rw [toAdd_ofAdd, MulEquiv.apply_symm_apply] at h2
    exact h2

omit [Finite V] in
theorem card_V (h : IsSLNatSection L ⊤ (fixV L) n) (hn : 1 ≤ n) :
    Nat.card V = 4 ^ n * Nat.card (fixV L) := by
  obtain ⟨D⟩ := h.nonempty_natData hn
  exact D.card_V

omit [Finite V] in
theorem card_L (h : IsSLNatSection L ⊤ (fixV L) n) (hn : 1 ≤ n) :
    Nat.card L = 2 ^ n * (4 ^ n - 1) := by
  obtain ⟨D⟩ := h.nonempty_natData hn
  exact D.card_L

theorem sylow_card (h : IsSLNatSection L ⊤ (fixV L) n) (hn : 1 ≤ n) {S : Subgroup (MulAut V)}
    (hS : IsSylowOf 2 S L) : Nat.card S = 2 ^ n := by
  obtain ⟨D⟩ := h.nonempty_natData hn
  obtain ⟨w, hw, rfl⟩ := D.exists_stab_of_sylow hS
  exact D.card_stab hw

theorem sylow_isElemAbelian2 (h : IsSLNatSection L ⊤ (fixV L) n) (hn : 1 ≤ n)
    {S : Subgroup (MulAut V)} (hS : IsSylowOf 2 S L) : IsElemAbelian2 S := by
  obtain ⟨D⟩ := h.nonempty_natData hn
  obtain ⟨w, hw, rfl⟩ := D.exists_stab_of_sylow hS
  exact D.isElemAbelian2_stab hw

theorem sylow_conj {S S' : Subgroup (MulAut V)} (hS : IsSylowOf 2 S L) (hS' : IsSylowOf 2 S' L) :
    ∃ x ∈ L, S' = conjSub x S :=
  NatSL2.sylow_conj_aux hS hS'

theorem sylow_inf_eq_bot (h : IsSLNatSection L ⊤ (fixV L) n) (hn : 1 ≤ n)
    {S S' : Subgroup (MulAut V)} (hS : IsSylowOf 2 S L) (hS' : IsSylowOf 2 S' L) (hne : S ≠ S') :
    S ⊓ S' = ⊥ := by
  obtain ⟨D⟩ := h.nonempty_natData hn
  obtain ⟨w, hw, rfl⟩ := D.exists_stab_of_sylow hS
  obtain ⟨w', hw', rfl⟩ := D.exists_stab_of_sylow hS'
  exact D.stab_inf_eq_bot hw hw' fun hc => hne ((D.stab_eq_iff hw hw').2 hc).symm

theorem sylow_sup_eq (h : IsSLNatSection L ⊤ (fixV L) n) (hn : 1 ≤ n)
    {S S' : Subgroup (MulAut V)} (hS : IsSylowOf 2 S L) (hS' : IsSylowOf 2 S' L) (hne : S ≠ S') :
    S ⊔ S' = L := by
  obtain ⟨D⟩ := h.nonempty_natData hn
  obtain ⟨w, hw, rfl⟩ := D.exists_stab_of_sylow hS
  obtain ⟨w', hw', rfl⟩ := D.exists_stab_of_sylow hS'
  exact D.stab_sup_eq hw hw' fun hc => hne ((D.stab_eq_iff hw hw').2 hc).symm

theorem ncard_sylows (h : IsSLNatSection L ⊤ (fixV L) n) (hn : 1 ≤ n) :
    Set.ncard {S : Subgroup (MulAut V) | IsSylowOf 2 S L} = 2 ^ n + 1 := by
  obtain ⟨D⟩ := h.nonempty_natData hn
  exact D.ncard_sylows

theorem exists_complement (h : IsSLNatSection L ⊤ (fixV L) n) (hn : 1 ≤ n)
    {S : Subgroup (MulAut V)} (hS : IsSylowOf 2 S L) :
    ∃ K : Subgroup (MulAut V), K ≤ L ∧ K ⊓ S = ⊥ ∧
      K ⊔ S = Subgroup.normalizer (S : Set (MulAut V)) ⊓ L ∧ Nat.card K = 2 ^ n - 1 ∧
      ∀ k ∈ K, k ≠ 1 → ∀ v : V, k v * v⁻¹ ∈ fixV L → v ∈ fixV L := by
  obtain ⟨D⟩ := h.nonempty_natData hn
  obtain ⟨w, hw, rfl⟩ := D.exists_stab_of_sylow hS
  exact D.exists_complement_stab hw

omit [Finite V] in
theorem fixV_le_fixV_sylow {S : Subgroup (MulAut V)} (hS : IsSylowOf 2 S L) : fixV L ≤ fixV S :=
  fixV_anti hS.1

theorem sylowGood_of_exists (S₀ : Subgroup (MulAut V)) (hS₀ : IsSylowOf 2 S₀ L)
    (hq : IsQuadratic S₀) (hc : Nat.card V = Nat.card S₀ * Nat.card (fixV S₀)) : SylowGood L := by
  intro S hS
  obtain ⟨x, -, rfl⟩ := NatSL2.sylow_conj_aux hS₀ hS
  refine ⟨?_, ?_⟩
  · show commV (conjSub x S₀) ≤ fixV (conjSub x S₀)
    unfold conjSub
    rw [CFSG.Quasithin.B19.commV_map_conj, Glauberman.fixV_map_conj]
    exact Subgroup.map_mono hq
  · unfold conjSub
    rw [Glauberman.card_map_conj, Glauberman.fixV_map_conj,
      Subgroup.card_map_of_injective x.injective]
    exact hc

theorem card_fixV_sylow (h : IsSLNatSection L ⊤ (fixV L) n) (hn : 1 ≤ n) (hG : SylowGood L)
    {S : Subgroup (MulAut V)} (hS : IsSylowOf 2 S L) :
    Nat.card (fixV S) = 2 ^ n * Nat.card (fixV L) := by
  obtain ⟨D⟩ := h.nonempty_natData hn
  obtain ⟨w, hw, rfl⟩ := D.exists_stab_of_sylow hS
  exact D.card_fixV_stab hG hw

theorem fixV_sylow_eq (h : IsSLNatSection L ⊤ (fixV L) n) (hn : 1 ≤ n) (hG : SylowGood L)
    {S : Subgroup (MulAut V)} (hS : IsSylowOf 2 S L) :
    fixV S = commV S ⊔ fixV L := by
  obtain ⟨D⟩ := h.nonempty_natData hn
  obtain ⟨w, hw, rfl⟩ := D.exists_stab_of_sylow hS
  exact D.fixV_stab_eq hG hw

theorem commV_zpowers_inf_fixV (h : IsSLNatSection L ⊤ (fixV L) n) (hn : 1 ≤ n)
    (hG : SylowGood L) {S : Subgroup (MulAut V)} (hS : IsSylowOf 2 S L) {s : MulAut V}
    (hs : s ∈ S) (hs1 : s ≠ 1) : commV (Subgroup.zpowers s) ⊓ fixV L = ⊥ := by
  obtain ⟨D⟩ := h.nonempty_natData hn
  obtain ⟨w, hw, rfl⟩ := D.exists_stab_of_sylow hS
  exact D.commV_zpowers_inf_fixV_stab hG hw hs hs1

theorem fixV_inf_sup_sylow (h : IsSLNatSection L ⊤ (fixV L) n) (hn : 1 ≤ n) (hG : SylowGood L)
    {S S' : Subgroup (MulAut V)} (hS : IsSylowOf 2 S L) (hS' : IsSylowOf 2 S' L) (hne : S ≠ S') :
    fixV S ⊓ fixV S' = fixV L ∧ fixV S ⊔ fixV S' = ⊤ := by
  obtain ⟨D⟩ := h.nonempty_natData hn
  obtain ⟨w, hw, rfl⟩ := D.exists_stab_of_sylow hS
  obtain ⟨w', hw', rfl⟩ := D.exists_stab_of_sylow hS'
  exact D.fixV_stab_inf_sup hG hw hw' fun hc => hne ((D.stab_eq_iff hw hw').2 hc).symm

theorem exists_sylow_mem_fixV (h : IsSLNatSection L ⊤ (fixV L) n) (hn : 1 ≤ n) (hG : SylowGood L)
    (v : V) : ∃ S : Subgroup (MulAut V), IsSylowOf 2 S L ∧ v ∈ fixV S := by
  obtain ⟨D⟩ := h.nonempty_natData hn
  by_cases h0 : D.vec v = 0
  · exact ⟨D.stab ![1, 0], D.isSylow_stab NatSL2.e₁_ne_zero,
      fixV_anti (D.stab_le _) ((D.vec_eq_zero_iff v).1 h0)⟩
  · refine ⟨D.stab (D.vec v), D.isSylow_stab h0, ?_⟩
    rw [D.fixV_stab hG h0, NatSL2.NatData.mem_Vw]
    exact ⟨1, (one_smul _ _).symm⟩

omit [Finite V] in
theorem center_eq_bot (h : IsSLNatSection L ⊤ (fixV L) n) (hn : 1 ≤ n) {x : MulAut V}
    (hx : x ∈ L) (hc : ∀ y ∈ L, y * x = x * y) : x = 1 := by
  obtain ⟨D⟩ := h.nonempty_natData hn
  obtain ⟨g, rfl⟩ := D.exists_ι_eq hx
  have hg : g ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply D.injective_ι
    rw [map_mul, map_mul]
    exact hc _ (D.ι_mem y)
  rw [CFSG.Timmesfeld.RankOne.center_SL2_eq_bot] at hg
  rw [Subgroup.mem_bot.1 hg, map_one]

end IsSLNatSection

end CFSG.CGT.PushingUpLit.BHS
