module

public import CFSG.ClassicalInvolution.Uniform.U7Vstar

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Uniform

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.G2D4Models
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.Assembly.LowTwoRank
open scoped MatrixGroups


section Standard

variable {F : Type} [Field F] [Finite F]

theorem eq_of_commutes_chartA (hodd : Odd (Nat.card F)) {a : Fin Tag.G2.rank → Fˣ}
    (ha : a = ![-1, 1]) {y : ModGL Tag.G2 F} (hy : y ∈ adjointGroup Tag.G2 F) (hy2 : y * y = 1)
    (hc : ∀ A : SL2 F, y * g2ChartA F A = g2ChartA F A * y) :
    y = 1 ∨ y = rootDiagUnit Tag.G2 a := by
  have hd : g2ChartA F (-1) = rootDiagUnit Tag.G2 a := g2ChartA_neg_one hodd ha
  have hX : y ∈ toralCentralizer Tag.G2 F a := by
    rw [mem_toralCentralizer]
    refine ⟨hy, ?_⟩
    have h := hc (-1)
    rw [hd] at h
    calc rootDiagUnit Tag.G2 a * y * (rootDiagUnit Tag.G2 a)⁻¹
        = y * rootDiagUnit Tag.G2 a * (rootDiagUnit Tag.G2 a)⁻¹ := by rw [h]
      _ = y := by group
  obtain ⟨t, ht, A, B, rfl⟩ := toralCentralizer_le_prod hodd ha hX
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  have hconj : ∀ C : SL2 F, glConjSL (diagGL (b g2i1) * Matrix.SpecialLinearGroup.toGL A) C =
      glConjSL 1 C := by
    intro C
    rw [glConjSL_one]
    apply g2ChartA_injective hodd
    rw [← prod_conj_chartA hodd b A B C, hc C, mul_assoc, mul_inv_cancel, mul_one]
  obtain ⟨c, hc0, hc1⟩ := exists_scalar_of_glConjSL_eq hconj
  refine eq_one_or_eq_of_scalar_chartA hodd ha b A B hy2 ⟨c⁻¹, ?_⟩
  calc ((diagGL (b g2i1) * Matrix.SpecialLinearGroup.toGL A : GL (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F)
      = c⁻¹ • (c • ((diagGL (b g2i1) * Matrix.SpecialLinearGroup.toGL A : GL (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F)) := by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
    _ = c⁻¹ • (1 : Matrix (Fin 2) (Fin 2) F) := by rw [← hc1, Units.val_one]

theorem eq_of_commutes_chartB (hodd : Odd (Nat.card F)) {a : Fin Tag.G2.rank → Fˣ}
    (ha : a = ![-1, 1]) {y : ModGL Tag.G2 F} (hy : y ∈ adjointGroup Tag.G2 F) (hy2 : y * y = 1)
    (hc : ∀ B : SL2 F, y * g2ChartB F B = g2ChartB F B * y) :
    y = 1 ∨ y = rootDiagUnit Tag.G2 a := by
  have hd : g2ChartB F (-1) = rootDiagUnit Tag.G2 a := g2ChartB_neg_one hodd ha
  have hX : y ∈ toralCentralizer Tag.G2 F a := by
    rw [mem_toralCentralizer]
    refine ⟨hy, ?_⟩
    have h := hc (-1)
    rw [hd] at h
    calc rootDiagUnit Tag.G2 a * y * (rootDiagUnit Tag.G2 a)⁻¹
        = y * rootDiagUnit Tag.G2 a * (rootDiagUnit Tag.G2 a)⁻¹ := by rw [h]
      _ = y := by group
  obtain ⟨t, ht, A, B, rfl⟩ := toralCentralizer_le_prod hodd ha hX
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  have hconj : ∀ C : SL2 F, glConjSL (diagGL (b g2i0 ^ 2 * b g2i1 ^ 3) *
      Matrix.SpecialLinearGroup.toGL B) C = glConjSL 1 C := by
    intro C
    rw [glConjSL_one]
    apply g2ChartB_injective hodd
    rw [← prod_conj_chartB hodd b A B C, hc C, mul_assoc, mul_inv_cancel, mul_one]
  obtain ⟨c, hc0, hc1⟩ := exists_scalar_of_glConjSL_eq hconj
  refine eq_one_or_eq_of_scalar_chartB hodd ha b A B hy2 ⟨c⁻¹, ?_⟩
  calc ((diagGL (b g2i0 ^ 2 * b g2i1 ^ 3) * Matrix.SpecialLinearGroup.toGL B : GL (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F)
      = c⁻¹ • (c • ((diagGL (b g2i0 ^ 2 * b g2i1 ^ 3) * Matrix.SpecialLinearGroup.toGL B :
        GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) := by
        rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
    _ = c⁻¹ • (1 : Matrix (Fin 2) (Fin 2) F) := by rw [← hc1, Units.val_one]

theorem eq_of_commutes_conj (hodd : Odd (Nat.card F)) {a : Fin Tag.G2.rank → Fˣ}
    (ha : a = ![-1, 1]) {Ψ : SL2 F →* ModGL Tag.G2 F} (hΨ : Ψ = g2ChartA F ∨ Ψ = g2ChartB F)
    {G x : ModGL Tag.G2 F} (hG : G ∈ adjointGroup Tag.G2 F) (hx : x ∈ adjointGroup Tag.G2 F)
    (hx2 : x * x = 1) (hc : ∀ A : SL2 F, x * (G * Ψ A * G⁻¹) = G * Ψ A * G⁻¹ * x) :
    x = 1 ∨ x = G * Ψ (-1) * G⁻¹ := by
  obtain ⟨y, hy⟩ : ∃ y, y = G⁻¹ * x * G := ⟨_, rfl⟩
  have hyA : y ∈ adjointGroup Tag.G2 F := by
    rw [hy]
    exact mul_mem (mul_mem (inv_mem hG) hx) hG
  have hy2 : y * y = 1 := by
    calc y * y = G⁻¹ * (x * x) * G := by rw [hy]; group
      _ = 1 := by rw [hx2]; group
  have hyc : ∀ A : SL2 F, y * Ψ A = Ψ A * y := by
    intro A
    have h := hc A
    calc y * Ψ A = G⁻¹ * (x * (G * Ψ A * G⁻¹)) * G := by rw [hy]; group
      _ = G⁻¹ * (G * Ψ A * G⁻¹ * x) * G := by rw [h]
      _ = Ψ A * y := by rw [hy]; group
  have hxy : x = G * y * G⁻¹ := by rw [hy]; group
  rcases hΨ with rfl | rfl
  · rcases eq_of_commutes_chartA hodd ha hyA hy2 hyc with h | h
    · left
      rw [hxy, h]
      group
    · right
      rw [hxy, h, ← g2ChartA_neg_one hodd ha]
  · rcases eq_of_commutes_chartB hodd ha hyA hy2 hyc with h | h
    · left
      rw [hxy, h]
      group
    · right
      rw [hxy, h, ← g2ChartB_neg_one hodd ha]

end Standard

section Conj

variable {F : Type} [Field F] [Finite F]

theorem rootChart_range_g2 (w : WeylGroup Tag.G2) (i : Fin Tag.G2.rank) :
    ∃ (Ψ : SL2 F →* ModGL Tag.G2 F) (h : ModGL Tag.G2 F), (Ψ = g2ChartA F ∨ Ψ = g2ChartB F) ∧
      h ∈ adjointGroup Tag.G2 F ∧
      (rootChart Tag.G2 F w i).range = Ψ.range.map (MulAut.conj h).toMonoidHom := by
  have key : ∀ (ρ : SL2 F →* ModGL Tag.G2 F) (u v : ModGL Tag.G2 F),
      ((MulAut.conj v).toMonoidHom.comp ρ).range =
        ((MulAut.conj u).toMonoidHom.comp ρ).range.map (MulAut.conj (v * u⁻¹)).toMonoidHom := by
    intro ρ u v
    rw [MonoidHom.range_comp, MonoidHom.range_comp, Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  fin_cases i
  · refine ⟨g2ChartB F, canonicalRep (coxeterSystem Tag.G2) F w *
      (canonicalRep (coxeterSystem Tag.G2) F g2WeylU)⁻¹, Or.inr rfl, ?_, ?_⟩
    · exact mul_mem (canonicalRep_mem_adjointGroup _ _ _)
        (inv_mem (canonicalRep_mem_adjointGroup _ _ _))
    · exact key (simpleRootSL2 Tag.G2 F g2i0) _ _
  · refine ⟨g2ChartA F, canonicalRep (coxeterSystem Tag.G2) F w *
      (canonicalRep (coxeterSystem Tag.G2) F 1)⁻¹, Or.inl rfl, ?_, ?_⟩
    · exact mul_mem (canonicalRep_mem_adjointGroup _ _ _)
        (inv_mem (canonicalRep_mem_adjointGroup _ _ _))
    · exact key (simpleRootSL2 Tag.G2 F g2i1) _ _

theorem exists_conj_standard {R : Subgroup ↥(adjointGroup Tag.G2 F)}
    (hR : R ∈ fundamentalSubgroups StatedLieTag.G2 (g2Datum F)) :
    ∃ (Ψ : SL2 F →* ModGL Tag.G2 F) (G : ModGL Tag.G2 F),
      (Ψ = g2ChartA F ∨ Ψ = g2ChartB F) ∧ G ∈ adjointGroup Tag.G2 F ∧
      R.map (adjointGroup Tag.G2 F).subtype = Ψ.range.map (MulAut.conj G).toMonoidHom := by
  obtain ⟨g₀, γ, hγ, rfl⟩ := hR
  have hγroot : IsRoot Tag.G2 γ := by
    rcases hγ with h | ⟨-, h⟩ | ⟨h, -⟩
    · exact mem_adjDatum_roots.1 h.1
    · exact mem_adjDatum_roots.1 h
    · exact absurd h (by decide)
  set ι : ↥(adjointGroup Tag.G2 F) →* ModGL Tag.G2 F := (adjointGroup Tag.G2 F).subtype with hι
  set Q : Subgroup ↥(adjointGroup Tag.G2 F) :=
    rootGroup (rootOperatorFamily Tag.G2) F γ ⊔ rootGroup (rootOperatorFamily Tag.G2) F (-γ)
    with hQ
  have hQmap : Q.map ι = rootPair Tag.G2 F γ := by
    rw [hQ, ← ModelFacts.subgroupOf_rootSubgroup_sup_eq (rootOperatorFamily Tag.G2) hγroot, hι,
      Subgroup.subgroupOf_map_subtype]
    have hle1 : rootSubgroup Tag.G2 F γ ≤ adjointGroup Tag.G2 F :=
      rootSubgroup_le_adjointGroup (τ := Tag.G2) (K := F) γ
    have hle2 : rootSubgroup Tag.G2 F (-γ) ≤ adjointGroup Tag.G2 F :=
      rootSubgroup_le_adjointGroup (τ := Tag.G2) (K := F) (-γ)
    exact inf_eq_left.2 (sup_le hle1 hle2)
  obtain ⟨w, i, hw⟩ := isRoot_iff_exists_smul_single.1 hγroot
  obtain ⟨Ψ, h, hΨ, hh, hrc⟩ := rootChart_range_g2 (F := F) w i
  refine ⟨Ψ, ι g₀ * h, hΨ, mul_mem g₀.2 hh, ?_⟩
  have h1 : (Generic.conjSub g₀ Q).map ι = (Q.map ι).map (MulAut.conj (ι g₀)).toMonoidHom :=
    CFSG.ClassicalInvolution.Asc77.AscQuot.map_conjSub ι g₀ Q
  rw [h1, hQmap, ← rootChart_range hw, hrc, Subgroup.map_map]
  congr 1

theorem eq_of_commutes_fundamental (hodd : Odd (Nat.card F)) {R : Subgroup ↥(adjointGroup Tag.G2 F)}
    (hR : R ∈ fundamentalSubgroups StatedLieTag.G2 (g2Datum F)) {c : ↥(adjointGroup Tag.G2 F)}
    (hc : IsUniqueInvolution R c) {x : ↥(adjointGroup Tag.G2 F)} (hx2 : x * x = 1)
    (hxR : ∀ r ∈ R, x * r = r * x) : x = 1 ∨ x = c := by
  obtain ⟨Ψ, G, hΨ, hG, hRmap⟩ := exists_conj_standard hR
  set ι : ↥(adjointGroup Tag.G2 F) →* ModGL Tag.G2 F := (adjointGroup Tag.G2 F).subtype with hι
  have hιinj : Function.Injective ι := Subtype.val_injective
  obtain ⟨a, ha⟩ : ∃ a : Fin Tag.G2.rank → Fˣ, a = ![-1, 1] := ⟨_, rfl⟩
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero (ringChar_ne_two_of_odd_nat_card hodd)
  have hΨinj : Function.Injective Ψ := by
    rcases hΨ with rfl | rfl
    exacts [g2ChartA_injective hodd, g2ChartB_injective hodd]
  have hx2' : ι x * ι x = 1 := by rw [← map_mul, hx2, map_one]
  have hcomm : ∀ A : SL2 F, ι x * (G * Ψ A * G⁻¹) = G * Ψ A * G⁻¹ * ι x := by
    intro A
    have hmem : G * Ψ A * G⁻¹ ∈ R.map ι := by
      rw [hRmap]
      exact ⟨Ψ A, ⟨A, rfl⟩, by simp [MulAut.conj_apply]⟩
    obtain ⟨r, hr, hrG⟩ := hmem
    rw [← hrG, ← map_mul, ← map_mul, hxR r hr]
  rcases eq_of_commutes_conj hodd ha hΨ hG x.2 hx2' hcomm with h | h
  · left
    exact Subtype.ext h
  · right
    have hcm : ι c ∈ R.map ι := ⟨c, hc.mem, rfl⟩
    rw [hRmap] at hcm
    obtain ⟨_, ⟨A₀, rfl⟩, hA₀⟩ := hcm
    have hcA : G * Ψ A₀ * G⁻¹ = ι c := hA₀
    have hcc : ι c * ι c = 1 := by rw [← map_mul, hc.sq, map_one]
    have hAA : A₀ * A₀ = 1 := by
      apply hΨinj
      rw [map_mul, map_one]
      have h' : G⁻¹ * (G * Ψ A₀ * G⁻¹ * (G * Ψ A₀ * G⁻¹)) * G = Ψ A₀ * Ψ A₀ := by group
      rw [hcA, hcc] at h'
      rw [← h']
      group
    rcases sl2_sq_eq_one_of_two_ne_zero h2 A₀ hAA with rfl | rfl
    · exfalso
      apply hc.ne_one
      apply hιinj
      rw [← hcA, map_one, map_one]
      group
    · apply Subtype.ext
      show (x : ModGL Tag.G2 F) = (c : ModGL Tag.G2 F)
      rw [h]
      exact hcA

end Conj

theorem g2CentralizerInvolution3_proved : G2CentralizerInvolution3 := by
  intro R hR c hc x hx2 hxR
  have hodd : Odd (Nat.card (GaloisField 3 1)) := by
    rw [GaloisField.card 3 1 (by norm_num)]
    decide
  exact eq_of_commutes_fundamental hodd hR hc hx2 hxR

end CFSG.ClassicalInvolution.Uniform
