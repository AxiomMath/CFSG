module

public import CFSG.ClassicalInvolution.AschTight.S19FChartG2
public import CFSG.ClassicalInvolution.ModelFacts.G2D4G2Class
public import CFSG.ClassicalInvolution.AschTight.S19GSL2

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19G

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.G2D4Models
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Disconnected.AschTight.S19F Matrix
open scoped MatrixGroups

variable {F : Type} [Field F]

section Simple0

theorem coe_g2Chart_g2i1 (C : SL2 F) :
    ((g2Chart F g2i1 C : adjointGroup .G2 F) : ModGL .G2 F) = g2ChartA F C :=
  (DFunLike.congr_fun (rootChart_one (τ := Tag.G2) (K := F) g2i1) C).symm

theorem coe_g2Chart_g2i0 (C : SL2 F) :
    ((g2Chart F g2i0 C : adjointGroup .G2 F) : ModGL .G2 F) =
      (canonicalRep (coxeterSystem Tag.G2) F g2WeylU)⁻¹ * g2ChartB F C *
        canonicalRep (coxeterSystem Tag.G2) F g2WeylU := by
  show simpleRootSL2 .G2 F g2i0 C = _ * rootChart Tag.G2 F g2WeylU g2i0 C * _
  rw [rootChart_apply]
  group

theorem fin_g2_cases (i : Fin Tag.G2.rank) : i = g2i0 ∨ i = g2i1 := by
  fin_cases i
  exacts [Or.inl rfl, Or.inr rfl]

end Simple0

section Charts

variable [Finite F]

theorem involution_centralizing_chartA (hodd : Odd (Nat.card F)) {a : Fin Tag.G2.rank → Fˣ}
    (ha : a = ![-1, 1]) {x : ModGL Tag.G2 F} (hx : x ∈ adjointGroup Tag.G2 F) (hx2 : x * x = 1)
    (hc : ∀ C : SL2 F, x * g2ChartA F C = g2ChartA F C * x) :
    x = 1 ∨ x = rootDiagUnit Tag.G2 a := by
  have hxX : x ∈ toralCentralizer Tag.G2 F a := by
    rw [mem_toralCentralizer]
    refine ⟨hx, ?_⟩
    rw [← g2ChartA_neg_one hodd ha, ← hc (-1)]
    group
  obtain ⟨t, ht, A, B, rfl⟩ := toralCentralizer_le_prod hodd ha hxX
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  obtain ⟨c, -, hcs⟩ := exists_scalar_of_glConjSL_eq (D := 1)
    (E := diagGL (b g2i1) * Matrix.SpecialLinearGroup.toGL A) (fun C => by
      apply g2ChartA_injective hodd
      rw [← prod_conj_chartA hodd b A B C, glConjSL_one]
      exact (mul_inv_eq_iff_eq_mul.mpr (hc C)).symm)
  exact eq_one_or_eq_of_scalar_chartA hodd ha b A B hx2 ⟨c, by rw [hcs]; simp⟩

theorem involution_centralizing_chartB (hodd : Odd (Nat.card F)) {a : Fin Tag.G2.rank → Fˣ}
    (ha : a = ![-1, 1]) {x : ModGL Tag.G2 F} (hx : x ∈ adjointGroup Tag.G2 F) (hx2 : x * x = 1)
    (hc : ∀ C : SL2 F, x * g2ChartB F C = g2ChartB F C * x) :
    x = 1 ∨ x = rootDiagUnit Tag.G2 a := by
  have hxX : x ∈ toralCentralizer Tag.G2 F a := by
    rw [mem_toralCentralizer]
    refine ⟨hx, ?_⟩
    rw [← g2ChartB_neg_one hodd ha, ← hc (-1)]
    group
  obtain ⟨t, ht, A, B, rfl⟩ := toralCentralizer_le_prod hodd ha hxX
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  obtain ⟨c, -, hcs⟩ := exists_scalar_of_glConjSL_eq (D := 1)
    (E := diagGL (b g2i0 ^ 2 * b g2i1 ^ 3) * Matrix.SpecialLinearGroup.toGL B) (fun C => by
      apply g2ChartB_injective hodd
      rw [← prod_conj_chartB hodd b A B C, glConjSL_one]
      exact (mul_inv_eq_iff_eq_mul.mpr (hc C)).symm)
  exact eq_one_or_eq_of_scalar_chartB hodd ha b A B hx2 ⟨c, by rw [hcs]; simp⟩

end Charts

section Simple

variable [Finite F]

theorem eq_one_or_eq_of_centralizing_g2Chart (hodd : Odd (Nat.card F)) (i : Fin Tag.G2.rank)
    {x : adjointGroup .G2 F} (hx2 : x * x = 1)
    (hc : ∀ C : SL2 F, x * g2Chart F i C = g2Chart F i C * x) :
    x = 1 ∨ x = g2Chart F i (-1) := by
  obtain ⟨a, ha⟩ : ∃ a : Fin Tag.G2.rank → Fˣ, a = ![-1, 1] := ⟨_, rfl⟩
  have hx2' : (x : ModGL .G2 F) * x = 1 := by
    rw [← Subgroup.coe_mul, hx2, Subgroup.coe_one]
  rcases fin_g2_cases i with rfl | rfl
  · set n := canonicalRep (coxeterSystem Tag.G2) F g2WeylU with hn
    have hnA : n ∈ adjointGroup .G2 F :=
      canonicalRep_mem_adjointGroup (coxeterSystem Tag.G2) F g2WeylU
    have hcB : ∀ C, (n * x * n⁻¹) * g2ChartB F C = g2ChartB F C * (n * x * n⁻¹) := by
      intro C
      have h := congrArg Subtype.val (hc C)
      rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_g2Chart_g2i0] at h
      calc n * x * n⁻¹ * g2ChartB F C = n * (x * (n⁻¹ * g2ChartB F C * n)) * n⁻¹ := by group
        _ = n * ((n⁻¹ * g2ChartB F C * n) * x) * n⁻¹ := by rw [h]
        _ = g2ChartB F C * (n * x * n⁻¹) := by group
    have hy2 : (n * x * n⁻¹) * (n * x * n⁻¹) = 1 := by
      calc (n * x * n⁻¹) * (n * x * n⁻¹) = n * ((x : ModGL .G2 F) * x) * n⁻¹ := by group
        _ = 1 := by rw [hx2']; group
    rcases involution_centralizing_chartB hodd ha (mul_mem (mul_mem hnA x.2) (inv_mem hnA))
      hy2 hcB with h | h
    · left
      apply Subtype.ext
      calc (x : ModGL .G2 F) = n⁻¹ * (n * x * n⁻¹) * n := by group
        _ = _ := by rw [h]; simp
    · right
      apply Subtype.ext
      rw [coe_g2Chart_g2i0, ← hn, g2ChartB_neg_one hodd ha, ← h]
      group
  · have hcA : ∀ C, (x : ModGL .G2 F) * g2ChartA F C = g2ChartA F C * x := by
      intro C
      have h := congrArg Subtype.val (hc C)
      rwa [Subgroup.coe_mul, Subgroup.coe_mul, coe_g2Chart_g2i1] at h
    rcases involution_centralizing_chartA hodd ha x.2 hx2' hcA with h | h
    · exact Or.inl (Subtype.ext h)
    · right
      apply Subtype.ext
      rw [coe_g2Chart_g2i1, g2ChartA_neg_one hodd ha, h]

end Simple

section Fund

variable [Finite F]

theorem exists_partner_g2 (hodd : Odd (Nat.card F)) (i : Fin Tag.G2.rank) :
    ∃ Φ' : SL2 F →* adjointGroup .G2 F,
      (∀ C C' : SL2 F, Φ' C * g2Chart F i C' = g2Chart F i C' * Φ' C) ∧
        Φ' (-1) = g2Chart F i (-1) := by
  obtain ⟨a, ha⟩ : ∃ a : Fin Tag.G2.rank → Fˣ, a = ![-1, 1] := ⟨_, rfl⟩
  have hcomm := g2ChartA_comm_g2ChartB (F := F) hodd
  rcases fin_g2_cases i with rfl | rfl
  · set N := canonicalRep (coxeterSystem Tag.G2) F g2WeylU with hN
    set n : adjointGroup .G2 F :=
      ⟨N, canonicalRep_mem_adjointGroup (coxeterSystem Tag.G2) F g2WeylU⟩ with hn
    refine ⟨(MulAut.conj n⁻¹).toMonoidHom.comp
      ((g2ChartA F).codRestrict (adjointGroup .G2 F) g2ChartA_mem), fun C C' => ?_, ?_⟩
    · apply Subtype.ext
      change N⁻¹ * g2ChartA F C * N⁻¹⁻¹ * _ = _ * (N⁻¹ *
        g2ChartA F C * N⁻¹⁻¹)
      rw [coe_g2Chart_g2i0, ← hN, inv_inv]
      calc N⁻¹ * g2ChartA F C * N * (N⁻¹ * g2ChartB F C' * N) =
            N⁻¹ * (g2ChartA F C * g2ChartB F C') * N := by group
        _ = N⁻¹ * (g2ChartB F C' * g2ChartA F C) * N := by rw [hcomm]
        _ = _ := by group
    · apply Subtype.ext
      change N⁻¹ * g2ChartA F (-1) * N⁻¹⁻¹ = _
      rw [coe_g2Chart_g2i0, g2ChartA_neg_one hodd ha, g2ChartB_neg_one hodd ha, inv_inv]
  · refine ⟨(g2ChartB F).codRestrict (adjointGroup .G2 F) g2ChartB_mem, fun C C' => ?_, ?_⟩
    · apply Subtype.ext
      change g2ChartB F C * _ = _ * g2ChartB F C
      rw [coe_g2Chart_g2i1]
      exact (hcomm C' C).symm
    · apply Subtype.ext
      change g2ChartB F (-1) = _
      rw [coe_g2Chart_g2i1, g2ChartA_neg_one hodd ha, g2ChartB_neg_one hodd ha]

theorem eq_one_or_mem_of_centralizing_g2 (hodd : Odd (Nat.card F))
    {R : Subgroup ↥(adjointGroup .G2 F)} (hR : R ∈ fundamentalSubgroups .G2 (g2Datum F))
    {y : adjointGroup .G2 F} (hy : y ∈ Subgroup.centralizer (R : Set (adjointGroup .G2 F)))
    (hy2 : y * y = 1) : y = 1 ∨ y ∈ R := by
  obtain ⟨i, g, rfl⟩ := exists_eq_conjSub_g2Chart hR
  have hc : ∀ C, (g⁻¹ * y * g) * g2Chart F i C = g2Chart F i C * (g⁻¹ * y * g) := by
    intro C
    have h := Subgroup.mem_centralizer_iff.mp hy (g * g2Chart F i C * g⁻¹) ⟨_, ⟨C, rfl⟩, rfl⟩
    calc g⁻¹ * y * g * g2Chart F i C = g⁻¹ * (y * (g * g2Chart F i C * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * g2Chart F i C * g⁻¹) * y) * g := by rw [h]
      _ = g2Chart F i C * (g⁻¹ * y * g) := by group
  have hx2 : (g⁻¹ * y * g) * (g⁻¹ * y * g) = 1 := by
    calc (g⁻¹ * y * g) * (g⁻¹ * y * g) = g⁻¹ * (y * y) * g := by group
      _ = 1 := by rw [hy2]; group
  rcases eq_one_or_eq_of_centralizing_g2Chart hodd i hx2 hc with h | h
  · left
    calc y = g * (g⁻¹ * y * g) * g⁻¹ := by group
      _ = 1 := by rw [h]; group
  · right
    refine ⟨g2Chart F i (-1), ⟨-1, rfl⟩, ?_⟩
    change g * g2Chart F i (-1) * g⁻¹ = y
    rw [← h]
    group

theorem exists_inv_mem_second_derived_g2 (hodd : Odd (Nat.card F))
    {R : Subgroup ↥(adjointGroup .G2 F)} (hR : R ∈ fundamentalSubgroups .G2 (g2Datum F)) :
    ∃ x ∈ R, x ≠ 1 ∧ x * x = 1 ∧
      x ∈ ⁅⁅Subgroup.centralizer (R : Set (adjointGroup .G2 F)),
        Subgroup.centralizer (R : Set (adjointGroup .G2 F))⁆,
        ⁅Subgroup.centralizer (R : Set (adjointGroup .G2 F)),
          Subgroup.centralizer (R : Set (adjointGroup .G2 F))⁆⁆ := by
  obtain ⟨i, g, rfl⟩ := exists_eq_conjSub_g2Chart hR
  obtain ⟨Φ', hcomm, hneg⟩ := exists_partner_g2 hodd i
  set Ψ : SL2 F →* adjointGroup .G2 F := (MulAut.conj g).toMonoidHom.comp Φ' with hΨ
  have hle : Ψ.range ≤ Subgroup.centralizer
      (Generic.conjSub g (g2Chart F i).range : Set (adjointGroup .G2 F)) := by
    rintro _ ⟨C, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨_, ⟨C', rfl⟩, rfl⟩
    change g * g2Chart F i C' * g⁻¹ * (g * Φ' C * g⁻¹) =
      g * Φ' C * g⁻¹ * (g * g2Chart F i C' * g⁻¹)
    calc g * g2Chart F i C' * g⁻¹ * (g * Φ' C * g⁻¹) = g * (g2Chart F i C' * Φ' C) * g⁻¹ := by
          group
      _ = g * (Φ' C * g2Chart F i C') * g⁻¹ := by rw [hcomm C C']
      _ = _ := by group
  have hU := isUniqueInvolution_range_sl2 hodd
    (g2Chart_injective (ringChar_ne_two_of_odd_nat_card hodd) i)
  refine ⟨g * g2Chart F i (-1) * g⁻¹, ⟨_, ⟨-1, rfl⟩, rfl⟩, fun h => hU.ne_one ?_, ?_, ?_⟩
  · calc g2Chart F i (-1) = g⁻¹ * (g * g2Chart F i (-1) * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  · calc g * g2Chart F i (-1) * g⁻¹ * (g * g2Chart F i (-1) * g⁻¹) =
          g * (g2Chart F i (-1) * g2Chart F i (-1)) * g⁻¹ := by group
      _ = 1 := by rw [hU.sq]; group
  · have hmem := map_neg_one_mem_second_derived (two_ne_zero_of_odd hodd) Ψ
    have hΨ1 : Ψ (-1) = g * g2Chart F i (-1) * g⁻¹ := by
      rw [hΨ, MonoidHom.comp_apply, hneg]
      rfl
    rw [hΨ1] at hmem
    exact Subgroup.commutator_mono (Subgroup.commutator_mono hle hle)
      (Subgroup.commutator_mono hle hle) hmem

end Fund

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19G
