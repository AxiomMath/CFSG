module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAL4OutC
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAL4Odd
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAProj
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L4SvCls1Frame

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup Matrix CFSG CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.CatFactsL4U4 CFSG.ComponentClassification.CatFactsL4U4.TBlocks
  CFSG.ComponentClassification.CatFactsL4U4.HBlocks
  CFSG.ComponentClassification.CatFactsL4U4.InvClassL
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open scoped MatrixGroups commutatorElement

section Blocks

variable {F : Type} [Field F]

theorem kaL4B2_mem_cent_iff {g : SL(4, F)} :
    g ∈ kaSlCent (B0 F) ↔
      (g : Matrix (Fin 4) (Fin 4) F) * X1 1 = X1 1 * (g : Matrix (Fin 4) (Fin 4) F) := by
  rw [kaSlCent, Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    have h1 := congrArg Units.val (h (B0 F) (Set.mem_singleton _))
    rw [Units.val_mul, Units.val_mul, coe_B0] at h1
    exact h1.symm
  · intro h b hb
    rw [Set.mem_singleton_iff] at hb
    subst hb
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, coe_B0]
    exact h.symm

theorem kaL4B2_blocks (h2 : (2 : F) ≠ 0) {g : SL(4, F)} (hg : g ∈ kaSlCent (B0 F)) :
    ∃ a b a' b' : Matrix (Fin 2) (Fin 2) F, (g : Matrix (Fin 4) (Fin 4) F) = bd a b ∧
      ((g⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = bd a' b' ∧ a * a' = 1 ∧ b * b' = 1 := by
  have hB : IsBD (g : Matrix (Fin 4) (Fin 4) F) :=
    isBD_of_comm_X1 h2 one_ne_zero (kaL4B2_mem_cent_iff.1 hg)
  have hB' : IsBD ((g⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) :=
    isBD_of_comm_X1 h2 one_ne_zero (kaL4B2_mem_cent_iff.1 (inv_mem hg))
  obtain ⟨a, b, hab⟩ : ∃ a b : Matrix (Fin 2) (Fin 2) F, (g : Matrix (Fin 4) (Fin 4) F) = bd a b :=
    ⟨_, _, eq_bd hB⟩
  obtain ⟨a', b', hab'⟩ : ∃ a b : Matrix (Fin 2) (Fin 2) F,
      ((g⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = bd a b := ⟨_, _, eq_bd hB'⟩
  have hgg : bd (a * a') (b * b') = bd 1 1 := by
    rw [← bd_mul, ← hab, ← hab', ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, bd_one]
  have ha := congrArg ul hgg
  have hb := congrArg lr hgg
  rw [ul_bd, ul_bd] at ha
  rw [lr_bd, lr_bd] at hb
  exact ⟨a, b, a', b', hab, hab', ha, hb⟩

theorem kaL4B2_coe_iota2 (s : SL(2, F)) :
    ((iota2 s : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = bd 1 (s : Matrix (Fin 2) (Fin 2) F) :=
  rfl

theorem kaL4B2_conj_iota1 (h2 : (2 : F) ≠ 0) {g : SL(4, F)} (hg : g ∈ kaSlCent (B0 F))
    (s : SL(2, F)) : ∃ t : SL(2, F), g * iota1 s * g⁻¹ = iota1 t := by
  obtain ⟨a, b, a', b', hg1, hg2, haa, hbb⟩ := kaL4B2_blocks h2 hg
  refine ⟨⟨a * (s : Matrix (Fin 2) (Fin 2) F) * a', ?_⟩, ?_⟩
  · rw [Matrix.det_mul, Matrix.det_mul, s.2, mul_one, ← Matrix.det_mul, haa, Matrix.det_one]
  · apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_iota1, hg1, hg2,
      bd_mul, bd_mul, mul_one, hbb]
    rfl

theorem kaL4B2_conj_iota2 (h2 : (2 : F) ≠ 0) {g : SL(4, F)} (hg : g ∈ kaSlCent (B0 F))
    (s : SL(2, F)) : ∃ t : SL(2, F), g * iota2 s * g⁻¹ = iota2 t := by
  obtain ⟨a, b, a', b', hg1, hg2, haa, hbb⟩ := kaL4B2_blocks h2 hg
  refine ⟨⟨b * (s : Matrix (Fin 2) (Fin 2) F) * b', ?_⟩, ?_⟩
  · rw [Matrix.det_mul, Matrix.det_mul, s.2, mul_one, ← Matrix.det_mul, hbb, Matrix.det_one]
  · apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, kaL4B2_coe_iota2,
      hg1, hg2, bd_mul, bd_mul, mul_one, haa]
    rfl

end Blocks

section Subgroups

variable {F : Type} [Field F]

@[expose] def kaL4B2_R0 (F : Type) [Field F] : Subgroup (projectiveSL 4 F) :=
  (kaSlCent (B0 F)).map (proj 4 F)

@[expose] def kaL4B2_L1 (F : Type) [Field F] : Subgroup (projectiveSL 4 F) :=
  ((proj 4 F).comp iota1).range

@[expose] def kaL4B2_L2 (F : Type) [Field F] : Subgroup (projectiveSL 4 F) :=
  ((proj 4 F).comp iota2).range

@[expose] def kaL4B2_L (F : Type) [Field F] : Subgroup (projectiveSL 4 F) :=
  kaL4B2_L1 F ⊔ kaL4B2_L2 F

theorem kaL4B2_L1_le_R0 : kaL4B2_L1 F ≤ kaL4B2_R0 F := by
  rintro _ ⟨s, rfl⟩
  exact ⟨iota1 s, kaL4B2_mem_cent_iff.2 (bdSL_comm (s, 1)), rfl⟩

theorem kaL4B2_L2_le_R0 : kaL4B2_L2 F ≤ kaL4B2_R0 F := by
  rintro _ ⟨s, rfl⟩
  exact ⟨iota2 s, kaL4B2_mem_cent_iff.2 (bdSL_comm (1, s)), rfl⟩

theorem kaL4B2_L_le_R0 : kaL4B2_L F ≤ kaL4B2_R0 F :=
  sup_le kaL4B2_L1_le_R0 kaL4B2_L2_le_R0

theorem kaL4B2_conj_mem_L1 (h2 : (2 : F) ≠ 0) {x l : projectiveSL 4 F} (hx : x ∈ kaL4B2_R0 F)
    (hl : l ∈ kaL4B2_L1 F) : x * l * x⁻¹ ∈ kaL4B2_L1 F := by
  obtain ⟨g, hg, rfl⟩ := hx
  obtain ⟨s, rfl⟩ := hl
  obtain ⟨t, ht⟩ := kaL4B2_conj_iota1 h2 hg s
  refine ⟨t, ?_⟩
  show proj 4 F (iota1 t) = proj 4 F g * proj 4 F (iota1 s) * (proj 4 F g)⁻¹
  rw [← ht, map_mul, map_mul, map_inv]

theorem kaL4B2_conj_mem_L2 (h2 : (2 : F) ≠ 0) {x l : projectiveSL 4 F} (hx : x ∈ kaL4B2_R0 F)
    (hl : l ∈ kaL4B2_L2 F) : x * l * x⁻¹ ∈ kaL4B2_L2 F := by
  obtain ⟨g, hg, rfl⟩ := hx
  obtain ⟨s, rfl⟩ := hl
  obtain ⟨t, ht⟩ := kaL4B2_conj_iota2 h2 hg s
  refine ⟨t, ?_⟩
  show proj 4 F (iota2 t) = proj 4 F g * proj 4 F (iota2 s) * (proj 4 F g)⁻¹
  rw [← ht, map_mul, map_mul, map_inv]

theorem kaL4B2_normalizes_L1 (h2 : (2 : F) ≠ 0) :
    ∀ x ∈ kaL4B2_R0 F, x ∈ normalizer (kaL4B2_L1 F : Set (projectiveSL 4 F)) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro l
  refine ⟨fun hl => kaL4B2_conj_mem_L1 h2 hx hl, fun hl => ?_⟩
  have := kaL4B2_conj_mem_L1 h2 (inv_mem hx) hl
  simpa [mul_assoc] using this

theorem kaL4B2_normalizes_L2 (h2 : (2 : F) ≠ 0) :
    ∀ x ∈ kaL4B2_R0 F, x ∈ normalizer (kaL4B2_L2 F : Set (projectiveSL 4 F)) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro l
  refine ⟨fun hl => kaL4B2_conj_mem_L2 h2 hx hl, fun hl => ?_⟩
  have := kaL4B2_conj_mem_L2 h2 (inv_mem hx) hl
  simpa [mul_assoc] using this

theorem kaL4B2_normalizes_L (h2 : (2 : F) ≠ 0) :
    ∀ x ∈ kaL4B2_R0 F, x ∈ normalizer (kaL4B2_L F : Set (projectiveSL 4 F)) :=
  fun x hx => Subgroup.inf_normalizer_le_normalizer_sup _ _
    ⟨kaL4B2_normalizes_L1 h2 x hx, kaL4B2_normalizes_L2 h2 x hx⟩

theorem kaL4B2_perf1 [Finite F] (h4 : 4 ≤ Nat.card F) :
    ⁅kaL4B2_L1 F, kaL4B2_L1 F⁆ = kaL4B2_L1 F := by
  have hP := (CFSG.ComponentClassification.CatFactsSp4.isQuasisimple_SL2' (K := F) h4).1
  have hJ : kaL4B2_L1 F = (⊤ : Subgroup SL(2, F)).map ((proj 4 F).comp iota1) :=
    MonoidHom.range_eq_map _
  rw [hJ, ← Subgroup.map_commutator, ← _root_.commutator_def, Group.isPerfect_def.mp hP]

theorem kaL4B2_perf2 [Finite F] (h4 : 4 ≤ Nat.card F) :
    ⁅kaL4B2_L2 F, kaL4B2_L2 F⁆ = kaL4B2_L2 F := by
  have hP := (CFSG.ComponentClassification.CatFactsSp4.isQuasisimple_SL2' (K := F) h4).1
  have hJ : kaL4B2_L2 F = (⊤ : Subgroup SL(2, F)).map ((proj 4 F).comp iota2) :=
    MonoidHom.range_eq_map _
  rw [hJ, ← Subgroup.map_commutator, ← _root_.commutator_def, Group.isPerfect_def.mp hP]

theorem kaL4B2_perf [Finite F] (h4 : 4 ≤ Nat.card F) : ⁅kaL4B2_L F, kaL4B2_L F⁆ = kaL4B2_L F := by
  refine le_antisymm (Subgroup.commutator_le.2 fun a ha b hb => ?_) (sup_le ?_ ?_)
  · rw [commutatorElement_def]
    exact (kaL4B2_L F).mul_mem ((kaL4B2_L F).mul_mem ((kaL4B2_L F).mul_mem ha hb)
      ((kaL4B2_L F).inv_mem ha)) ((kaL4B2_L F).inv_mem hb)
  · calc kaL4B2_L1 F = ⁅kaL4B2_L1 F, kaL4B2_L1 F⁆ := (kaL4B2_perf1 h4).symm
      _ ≤ ⁅kaL4B2_L F, kaL4B2_L F⁆ := Subgroup.commutator_mono le_sup_left le_sup_left
  · calc kaL4B2_L2 F = ⁅kaL4B2_L2 F, kaL4B2_L2 F⁆ := (kaL4B2_perf2 h4).symm
      _ ≤ ⁅kaL4B2_L F, kaL4B2_L F⁆ := Subgroup.commutator_mono le_sup_right le_sup_right

theorem kaL4B2_hLp [Finite F] (h4 : 4 ≤ Nat.card F) (h2 : (2 : F) ≠ 0) :
    ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ M : Subgroup (projectiveSL 4 F), M ≤ kaL4B2_L F →
      IsPGroup p ↥M → (∀ l ∈ kaL4B2_L F, l ∈ normalizer (M : Set (projectiveSL 4 F))) →
        ∀ m ∈ M, ∀ l ∈ kaL4B2_L F, m * l = l * m := by
  intro p hp _ M hML hMp hMn
  have hQ := CFSG.ComponentClassification.CatFactsSp4.isQuasisimple_SL2' (K := F) h4
  have hc1 : ∀ m ∈ M, ∀ l ∈ kaL4B2_L1 F, m * l = l * m :=
    ka_centralizes_of_perfect (p := p) (kaL4B2_L1 F) M (kaL4B2_perf1 h4)
      (fun l hl => hMn l (Subgroup.mem_sup_left hl))
      (fun x hx => kaL4B2_normalizes_L1 h2 x (kaL4B2_L_le_R0 (hML hx))) hMp
      (fun M' hM'L hM'p hM'n =>
        ka_central_of_quasisimple_image ((proj 4 F).comp iota1) hQ hp M' hM'L hM'p hM'n)
  have hc2 : ∀ m ∈ M, ∀ l ∈ kaL4B2_L2 F, m * l = l * m :=
    ka_centralizes_of_perfect (p := p) (kaL4B2_L2 F) M (kaL4B2_perf2 h4)
      (fun l hl => hMn l (Subgroup.mem_sup_right hl))
      (fun x hx => kaL4B2_normalizes_L2 h2 x (kaL4B2_L_le_R0 (hML hx))) hMp
      (fun M' hM'L hM'p hM'n =>
        ka_central_of_quasisimple_image ((proj 4 F).comp iota2) hQ hp M' hM'L hM'p hM'n)
  intro m hm l hl
  have hcent : kaL4B2_L F ≤ Subgroup.centralizer ({m} : Set (projectiveSL 4 F)) := by
    refine sup_le (fun l hl => ?_) (fun l hl => ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact hc1 m hm l hl
    · rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact hc2 m hm l hl
  have := hcent hl
  rw [Subgroup.mem_centralizer_iff] at this
  exact this m (Set.mem_singleton m)

end Subgroups

section Centralizer

variable {F : Type} [Field F]

theorem kaL4B2_scalar_eq_one (h4 : (4 : F) ≠ 0) {G H Gi : Matrix (Fin 4) (Fin 4) F} {c : F}
    (hc : H * G = c • (G * H)) (hgi : G * Gi = 1) (hig : Gi * G = 1)
    (htr : Matrix.trace H = 4) : c = 1 := by
  have htrace : Matrix.trace H = c * Matrix.trace H := by
    calc Matrix.trace H = Matrix.trace (H * G * Gi) := by rw [Matrix.mul_assoc, hgi, Matrix.mul_one]
      _ = Matrix.trace (c • (G * H) * Gi) := by rw [hc]
      _ = c * Matrix.trace (G * H * Gi) := by
          rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
      _ = c * Matrix.trace (Gi * (G * H)) := by rw [Matrix.trace_mul_comm]
      _ = c * Matrix.trace H := by rw [← Matrix.mul_assoc, hig, Matrix.one_mul]
  rw [htr] at htrace
  have h4c : (4 : F) * (1 - c) = 0 := by linear_combination htrace
  have h1c : 1 - c = 0 := (mul_eq_zero.1 h4c).resolve_left h4
  linear_combination -h1c

theorem kaL4B2_mat_comm (h4 : (4 : F) ≠ 0) {g h : SL(4, F)}
    (htr : Matrix.trace (h : Matrix (Fin 4) (Fin 4) F) = 4)
    (hc : proj 4 F g * proj 4 F h = proj 4 F h * proj 4 F g) :
    (g : Matrix (Fin 4) (Fin 4) F) * (h : Matrix (Fin 4) (Fin 4) F) =
      (h : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F) := by
  have h1 : proj 4 F (g * h) = proj 4 F (h * g) := by rw [map_mul, map_mul, hc]
  obtain ⟨c, hc'⟩ := eq_smul_of_proj_eq h1
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul] at hc'
  have hgi : (g : Matrix (Fin 4) (Fin 4) F) * ((g⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) =
      1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hig : ((g⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F) =
      1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hc1 : c = 1 := kaL4B2_scalar_eq_one h4 hc' hgi hig htr
  rw [hc1, one_smul] at hc'
  exact hc'.symm

theorem kaL4B2_smul_one_mul (a b : F) :
    (a • (1 : Matrix (Fin 2) (Fin 2) F)) * (b • 1) = (a * b) • 1 := by
  rw [Matrix.smul_mul, Matrix.one_mul, smul_smul]

theorem kaL4B2_trace_bd {a b : Matrix (Fin 2) (Fin 2) F} (ha : Matrix.trace a = 2)
    (hb : Matrix.trace b = 2) : Matrix.trace (bd a b) = 4 := by
  rw [trace_bd, ha, hb]
  norm_num

@[expose] def kaL4B2_tor (F : Type) [Field F] : Fˣ →* SL(4, F) where
  toFun u := ⟨bd ((u : F) • 1) (((u⁻¹ : Fˣ) : F) • 1), by
    rw [det_bd, Matrix.det_smul, Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one,
      mul_one, ← mul_pow, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_pow]⟩
  map_one' := Subtype.ext (by simp [bd_one])
  map_mul' u v := Subtype.ext (by
    show bd ((((u * v : Fˣ)) : F) • 1) ((((u * v)⁻¹ : Fˣ) : F) • 1) =
      bd ((u : F) • 1) (((u⁻¹ : Fˣ) : F) • 1) * bd ((v : F) • 1) (((v⁻¹ : Fˣ) : F) • 1)
    rw [bd_mul, kaL4B2_smul_one_mul, kaL4B2_smul_one_mul, mul_inv, Units.val_mul, Units.val_mul])

theorem kaL4B2_coe_T (u : Fˣ) :
    ((kaL4B2_tor F u : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) =
      bd ((u : F) • 1) (((u⁻¹ : Fˣ) : F) • 1) :=
  rfl

theorem kaL4B2_sq_mem_torus (h4 : (4 : F) ≠ 0) {g : SL(4, F)}
    (hc : ∀ l ∈ kaL4B2_L F, proj 4 F g * l = l * proj 4 F g) :
    proj 4 F g * proj 4 F g ∈ ((proj 4 F).comp (kaL4B2_tor F)).range := by
  have hL1 : ∀ s : SL(2, F), proj 4 F (iota1 s) ∈ kaL4B2_L F :=
    fun s => Subgroup.mem_sup_left ⟨s, rfl⟩
  have hL2 : ∀ s : SL(2, F), proj 4 F (iota2 s) ∈ kaL4B2_L F :=
    fun s => Subgroup.mem_sup_right ⟨s, rfl⟩
  have tr_uu : Matrix.trace (uu (1 : F)) = 2 := trace_uu 1
  have tr_ll : Matrix.trace (ll (1 : F)) = 2 := trace_ll 1
  have tr_one : Matrix.trace (1 : Matrix (Fin 2) (Fin 2) F) = 2 := by
    rw [Matrix.trace_one, Fintype.card_fin]
    norm_num
  have c1 : (g : Matrix (Fin 4) (Fin 4) F) * bd (uu 1) 1 =
      bd (uu 1) 1 * (g : Matrix (Fin 4) (Fin 4) F) :=
    kaL4B2_mat_comm h4 (h := iota1 (uuSL 1)) (kaL4B2_trace_bd tr_uu tr_one)
      (hc _ (hL1 (uuSL 1)))
  have c2 : (g : Matrix (Fin 4) (Fin 4) F) * bd (ll 1) 1 =
      bd (ll 1) 1 * (g : Matrix (Fin 4) (Fin 4) F) :=
    kaL4B2_mat_comm h4 (h := iota1 (llSL 1)) (kaL4B2_trace_bd tr_ll tr_one)
      (hc _ (hL1 (llSL 1)))
  have c3 : (g : Matrix (Fin 4) (Fin 4) F) * bd 1 (uu 1) =
      bd 1 (uu 1) * (g : Matrix (Fin 4) (Fin 4) F) :=
    kaL4B2_mat_comm h4 (h := iota2 (uuSL 1)) (kaL4B2_trace_bd tr_one tr_uu)
      (hc _ (hL2 (uuSL 1)))
  have c4 : (g : Matrix (Fin 4) (Fin 4) F) * bd 1 (ll 1) =
      bd 1 (ll 1) * (g : Matrix (Fin 4) (Fin 4) F) :=
    kaL4B2_mat_comm h4 (h := iota2 (llSL 1)) (kaL4B2_trace_bd tr_one tr_ll)
      (hc _ (hL2 (llSL 1)))
  obtain ⟨l, m, e⟩ : ∃ l m : F, (g : Matrix (Fin 4) (Fin 4) F) = bd (l • 1) (m • 1) :=
    ⟨_, _, eq_of_comm_bd c1 c2 c3 c4⟩
  have hdet : l ^ 2 * m ^ 2 = 1 := by
    have h1 := Matrix.SpecialLinearGroup.det_coe g
    rw [e, det_bd, Matrix.det_smul, Matrix.det_smul, Matrix.det_one, Fintype.card_fin] at h1
    linear_combination h1
  have hl0 : l ≠ 0 := by
    rintro rfl
    simp at hdet
  have hlm : (l * l) * (m * m) = 1 := by linear_combination hdet
  refine ⟨Units.mk0 (l * l) (mul_ne_zero hl0 hl0), ?_⟩
  have hinv : (((Units.mk0 (l * l) (mul_ne_zero hl0 hl0))⁻¹ : Fˣ) : F) = m * m := by
    rw [Units.val_inv_eq_inv_val, Units.val_mk0]
    exact inv_eq_of_mul_eq_one_right hlm
  have hgg : g * g = kaL4B2_tor F (Units.mk0 (l * l) (mul_ne_zero hl0 hl0)) := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, e, bd_mul, kaL4B2_smul_one_mul, kaL4B2_smul_one_mul,
      kaL4B2_coe_T, hinv, Units.val_mk0]
  show proj 4 F (kaL4B2_tor F (Units.mk0 (l * l) (mul_ne_zero hl0 hl0))) =
    proj 4 F g * proj 4 F g
  rw [← hgg, map_mul]

theorem kaL4B2_hcyc [Finite F] (h2 : (2 : F) ≠ 0) :
    ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ X : Subgroup (projectiveSL 4 F), IsPGroup p ↥X →
      X ≤ kaL4B2_R0 F → (∀ x ∈ X, ∀ l ∈ kaL4B2_L F, x * l = l * x) → IsCyclic ↥X := by
  intro p hp hp2 X hXp _ hXc
  have h4 : (4 : F) ≠ 0 := by
    have : (4 : F) = 2 * 2 := by norm_num
    rw [this]
    exact mul_ne_zero h2 h2
  have hX : X ≤ ((proj 4 F).comp (kaL4B2_tor F)).range := by
    intro x hx
    obtain ⟨g, rfl⟩ := proj_surjective 4 F x
    exact ka_odd_mem_of_sq_mem (kaL4B2_sq_mem_torus h4 (hXc _ hx))
      (ka_odd_of_mem_pGroup hp hp2 hXp hx)
  let φ : Fˣ →* projectiveSL 4 F := (proj 4 F).comp (kaL4B2_tor F)
  let ψ : ↥(X.comap φ) →* ↥X := (φ.comp (X.comap φ).subtype).codRestrict X (fun u => u.2)
  have hψ : Function.Surjective ψ := by
    rintro ⟨x, hx⟩
    obtain ⟨u, rfl⟩ := hX hx
    exact ⟨⟨u, hx⟩, rfl⟩
  exact isCyclic_of_surjective ψ hψ

end Centralizer

section Assembly

variable {F : Type} [Field F]

@[expose] def kaL4B2_N (F : Type) [Field F] : Matrix (Fin 4) (Fin 4) F :=
  !![0, 1, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0]

theorem kaL4B2_N_ne_zero : kaL4B2_N F ≠ 0 := by
  intro h
  have h1 := congrFun (congrFun h 0) 1
  simp [kaL4B2_N] at h1

theorem kaL4B2_N_sq : kaL4B2_N F * kaL4B2_N F = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [kaL4B2_N, Matrix.mul_apply, Fin.sum_univ_four]

theorem kaL4B2_coe_iota1_uu (c : F) :
    ((iota1 (uuSL c) : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = 1 + c • kaL4B2_N F := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_iota1, coe_uuSL, bd, kaL4B2_N]

theorem kaL4B2_B0_sq : B0 F * B0 F = GeneralLinearGroup.scalar (Fin 4) (1 : Fˣ) := by
  rw [map_one]
  apply Units.ext
  rw [Units.val_mul, coe_B0, Units.val_one]
  exact X1_one_mul_self

theorem kaL4B2_B0 [Finite F] (hodd : ringChar F ≠ 2) (h5 : 5 ≤ Nat.card F) :
    KAAll (conjAut 4 F (B0 F)) := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hodd
  have h4 : 4 ≤ Nat.card F := by omega
  refine ka_all_of_torus (ka_conj_inj_pl4 hodd) (kaL4B2_R0 F) (kaL4B2_L F) ?_ ?_ kaL4B2_L_le_R0
    (kaL4B2_normalizes_L h2) (kaL4B2_perf h4) (kaL4B2_hLp h4 h2) (kaL4B2_hcyc h2) ?_
    (ka_outCentral_pl4 hodd (B0 F) 1 kaL4B2_B0_sq)
  · rintro _ ⟨g, hg, rfl⟩
    exact proj_mem_fixSub_of_comm (kaL4B2_mem_cent_iff.1 hg)
  · intro c hc ho
    exact ka_odd_mem_map_cent_pl4 (B0 F) 1 kaL4B2_B0_sq (mem_fixSub.1 hc) ho
  · refine ka_rigid_proj (n := 4) (by norm_num) (fun A hA => ka_conjAut_inner_of_odd_pl4 hodd A hA)
      (kaL4B2_L F) (kaL4B2_N F) kaL4B2_N_ne_zero kaL4B2_N_sq fun c => ?_
    exact ⟨iota1 (uuSL c), kaL4B2_coe_iota1_uu c, Subgroup.mem_sup_left ⟨uuSL c, rfl⟩⟩

theorem kaL4B2_congr_eq_mul {Y : Type} [Group Y] (e α : MulAut Y) :
    MulAut.congr e α = e * α * e⁻¹ := by
  ext x
  simp [MulAut.congr_apply]

theorem kaL4B2_thm : KAL4B2 := by
  intro F _ _ hodd h5 B hB hr
  obtain ⟨P, hP⟩ := exists_frame_cls1 (Ring.two_ne_zero hodd) hB hr
  have h' := KAAll.of_mulEquiv (conjAut 4 F P : projectiveSL 4 F ≃* projectiveSL 4 F)
    (kaL4B2_B0 hodd h5)
  have key : MulAut.congr (conjAut 4 F P : projectiveSL 4 F ≃* projectiveSL 4 F)
      (conjAut 4 F (B0 F)) = conjAut 4 F B := by
    rw [kaL4B2_congr_eq_mul, hP, map_mul, map_mul, map_inv]
  rwa [key] at h'

end Assembly

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
