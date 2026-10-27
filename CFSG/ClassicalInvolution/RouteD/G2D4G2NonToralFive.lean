module

public import CFSG.ClassicalInvolution.ModelFacts.G2D4G2TorusFive
public import CFSG.ClassicalInvolution.RouteD.G2D4G2NonToral7

public noncomputable section

namespace CFSG.ClassicalInvolution.G2D4Models

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank Matrix
open scoped MatrixGroups

section Generate

variable {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem nonsquare_of_nonsquare_mul {χ η r κ : F} (hneg : ∃ i : F, i * i = -1)
    (hχ : ¬ IsSquare χ) (hη : η * η = 1) (hr : r ≠ 0) (hκ : κ = r ^ 2 * (χ * η)) :
    ∀ ρ : F, κ ≠ ρ * ρ := by
  intro ρ hρ
  apply hχ
  obtain ⟨i, hi⟩ := hneg
  rcases mul_self_eq_one_iff.mp hη with h1 | h1
  · have e : r ^ 2 * (χ * 1) = ρ * ρ := by rw [← hρ, hκ, h1]
    refine ⟨ρ / r, ?_⟩
    field_simp
    linear_combination e
  · have e : r ^ 2 * (χ * -1) = ρ * ρ := by rw [← hρ, hκ, h1]
    refine ⟨i * ρ / r, ?_⟩
    field_simp
    linear_combination (-1 : F) * e - ρ ^ 2 * hi

omit [Finite F] in
theorem rootChar_g2vec_one_zero (b : Fin Tag.G2.rank → Fˣ) :
    ((rootChar b (g2vec 1 0) : Fˣ) : F) = ((b g2i0 : Fˣ) : F) := by
  rw [rootChar_g2vec]
  simp

omit [Finite F] in
theorem rootChar_g2vec_one_three (b : Fin Tag.G2.rank → Fˣ) :
    ((rootChar b (g2vec 1 3) : Fˣ) : F) = ((b g2i0 : Fˣ) : F) * ((b g2i1 : Fˣ) : F) ^ 3 := by
  rw [rootChar_g2vec]
  simp

theorem adjointGroup_le_sup_t_m0_five (hodd : Odd (Nat.card F)) (h5 : Nat.card F = 5)
    (b : Fin Tag.G2.rank → Fˣ)
    (hb : ¬ IsSquare ((b g2i0 : Fˣ) : F) ∨
      ¬ IsSquare (((b g2i0 : Fˣ) : F) * ((b g2i1 : Fˣ) : F) ^ 3)) :
    adjointGroup Tag.G2 F ≤ toralCentralizer Tag.G2 F ![-1, 1] ⊔
      (adjointGroup Tag.G2 F ⊓ Subgroup.centralizer
        ({rootDiagUnit Tag.G2 b * (g2ChartA F WSL * g2ChartB F WSL)} :
          Set (ModGL Tag.G2 F))) := by
  have hK2 : ringChar F ≠ 2 := ringChar_ne_two_of_odd_nat_card hodd
  have h4 : 4 ≤ Nat.card F := by omega
  have hneg := exists_neg_one_square_five h5
  have hneg1 : (-1 : Fˣ) ≠ 1 := fun h =>
    Ring.neg_one_ne_one_of_char_ne_two hK2 (by simpa using congrArg Units.val h)
  set M := toralCentralizer Tag.G2 F ![-1, 1] ⊔
      (adjointGroup Tag.G2 F ⊓ Subgroup.centralizer
        ({rootDiagUnit Tag.G2 b * (g2ChartA F WSL * g2ChartB F WSL)} : Set (ModGL Tag.G2 F)))
    with hM
  have hXM : toralCentralizer Tag.G2 F ![-1, 1] ≤ M := le_sup_left
  have hTP : torusGroup Tag.G2 F ≤ toralCentralizer Tag.G2 F ![-1, 1] :=
    torusGroup_le_toralCentralizer _
  obtain ⟨a₂, ha₂⟩ : ∃ a₂ : Fin Tag.G2.rank → Fˣ, a₂ = ![1, -1] := ⟨_, rfl⟩
  have ha₂0 : a₂ g2i0 = 1 := by rw [ha₂]; rfl
  have ha₂1 : a₂ g2i1 = -1 := by rw [ha₂]; rfl
  have ha₂sq : ∀ i, a₂ i = 1 ∨ a₂ i = -1 := by
    intro i; fin_cases i
    · exact Or.inl ha₂0
    · exact Or.inr ha₂1
  have ha₂ne : a₂ ≠ 1 := fun h => hneg1 (by have := congrFun h g2i1; rwa [ha₂1] at this)
  obtain ⟨a₃, ha₃⟩ : ∃ a₃ : Fin Tag.G2.rank → Fˣ, a₃ = ![-1, -1] := ⟨_, rfl⟩
  have ha₃0 : a₃ g2i0 = -1 := by rw [ha₃]; rfl
  have ha₃1 : a₃ g2i1 = -1 := by rw [ha₃]; rfl
  have ha₃sq : ∀ i, a₃ i = 1 ∨ a₃ i = -1 := by
    intro i; fin_cases i
    · exact Or.inr ha₃0
    · exact Or.inr ha₃1
  have ha₃ne : a₃ ≠ 1 := fun h => hneg1 (by have := congrFun h g2i0; rwa [ha₃0] at this)
  have hmain : ∀ A : SL2 F, rootChart Tag.G2 F 1 g2i0 A ∈ M := by
    rcases hb with hb | hb
    · intro A
      have hker : g2vec 1 0 ∈ rootCharKernel a₂ := by
        refine ⟨?_, ?_⟩
        · rw [← g2_single_0]; exact isRoot_single _ _
        · rw [rootChar_g2vec, ha₂0]; simp
      refine chart_le_sup_t_m0 hodd h4 b 1 g2i0 (x := 0) (by rw [one_smul, g2_single_0]) ha₂sq
        ha₂ne hker hTP (fun κ η' hη' ⟨r, hr, hκ⟩ => normTorusGen_of_five h5 κ ?_) A
      rw [rootChar_g2vec_one_zero] at hκ
      exact nonsquare_of_nonsquare_mul hneg hb hη' hr hκ
    · have hchart : ∀ A : SL2 F, rootChart Tag.G2 F (simple Tag.G2 g2i1) g2i0 A ∈ M := by
        intro A
        have hγ : (simple Tag.G2 g2i1) • (Pi.single g2i0 1 : Fin Tag.G2.rank → ℤ) = g2vec 1 3 := by
          rw [g2_single_0, g2_s1_smul]
          refine g2vec_ext ?_ ?_ <;> simp [g2vec_0, g2vec_1]
        have hker : g2vec 1 3 ∈ rootCharKernel a₃ := by
          refine ⟨?_, ?_⟩
          · rw [← hγ]; exact IsRoot.smul (isRoot_single _ _) _
          · rw [rootChar_g2vec, ha₃0, ha₃1]; norm_num
        refine chart_le_sup_t_m0 hodd h4 b (simple Tag.G2 g2i1) g2i0 (x := 3) hγ ha₃sq ha₃ne hker
          hTP (fun κ η' hη' ⟨r, hr, hκ⟩ => normTorusGen_of_five h5 κ ?_) A
        rw [rootChar_g2vec_one_three] at hκ
        exact nonsquare_of_nonsquare_mul hneg hb hη' hr hκ
      intro A
      have hnA : g2ChartA F WSL = canonicalRep (coxeterSystem Tag.G2) F (simple Tag.G2 g2i1) := by
        show rootChart Tag.G2 F 1 g2i1 WSL = _
        rw [rootChart_WSL_apply, canonicalRep_one, inv_one, one_mul, mul_one]
        exact (canonicalRep_simple (coxeterSystem Tag.G2) F g2i1).symm
      have hn : g2ChartA F WSL ∈ M :=
        hXM (g2ChartA_mem_toralCentralizer hodd (a := ![-1, 1]) rfl WSL)
      have e : rootChart Tag.G2 F 1 g2i0 A = (g2ChartA F WSL)⁻¹ *
          rootChart Tag.G2 F (simple Tag.G2 g2i1) g2i0 A * g2ChartA F WSL := by
        rw [rootChart_apply (simple Tag.G2 g2i1), rootChart_one, ← hnA]
        group
      rw [e]
      exact mul_mem (mul_mem (inv_mem hn) (hchart A)) hn
  rw [adjointGroup_eq_iSup_rootPair_single]
  refine iSup_le fun i => ?_
  fin_cases i
  · rw [← range_simpleRootSL2_eq_rootPair, ← rootChart_one (K := F) (τ := Tag.G2)]
    rintro _ ⟨A, rfl⟩
    exact hmain A
  · have hker : (Pi.single g2i1 1 : Fin Tag.G2.rank → ℤ) ∈
        rootCharKernel (τ := Tag.G2) (K := F) ![-1, 1] :=
      ⟨isRoot_single _ _, (rootChar_single_g2 _ _).trans rfl⟩
    exact (rootPair_le_toralCentralizer hker).trans hXM

end Generate

section Toral

variable {F : Type} [Field F] [Finite F]

theorem exists_diagonalizer_five (h5 : Nat.card F = 5) :
    ∃ (P : SL2 F) (u : Fˣ), u * u = -1 ∧ P * WSL * P⁻¹ = HSL u := by
  obtain ⟨i, hi, hd⟩ := exists_sqrt_neg_one_five h5
  have hi0 : i ≠ 0 := fun h => by
    rw [h, mul_zero] at hi
    exact zero_ne_one (neg_eq_zero.mp hi.symm |>.symm ▸ rfl : (0 : F) = 1)
  let u : Fˣ := Units.mk0 i hi0
  let Q : SL2 F := ⟨!![1, 1; i, -i], by
    rw [det_fin_two]
    simp only [of_apply, cons_val', cons_val_zero, cons_val_fin_one, cons_val_one]
    linear_combination hd⟩
  have hinv : ((u⁻¹ : Fˣ) : F) = -i := by
    rw [Units.val_inv_eq_inv_val]
    refine inv_eq_of_mul_eq_one_right ?_
    show i * -i = 1
    linear_combination -hi
  have hQc : (Q : Matrix (Fin 2) (Fin 2) F) = !![1, 1; i, -i] := rfl
  have hWc : ((WSL : SL2 F) : Matrix (Fin 2) (Fin 2) F) = !![0, 1; -1, 0] := rfl
  have hWQ : WSL * Q = Q * HSL u := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hQc, hWc, coe_HSL]
    have hu1 : ((u : Fˣ) : F) = i := rfl
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hinv, hu1]
    all_goals exact hi.symm
  refine ⟨Q⁻¹, u, Units.ext ?_, ?_⟩
  · simpa [u] using hi
  · rw [inv_inv]
    calc Q⁻¹ * WSL * Q = Q⁻¹ * (WSL * Q) := mul_assoc _ _ _
      _ = Q⁻¹ * (Q * HSL u) := by rw [hWQ]
      _ = HSL u := inv_mul_cancel_left _ _

theorem conj_m0_chart (hodd : Odd (Nat.card F)) (P : SL2 F) :
    (g2ChartA F P * g2ChartB F P) * (g2ChartA F WSL * g2ChartB F WSL) *
        (g2ChartA F P * g2ChartB F P)⁻¹ =
      g2ChartA F (P * WSL * P⁻¹) * g2ChartB F (P * WSL * P⁻¹) := by
  have hcomm := g2ChartA_comm_g2ChartB (F := F) hodd
  have h1 : ∀ X Y : SL2 F, g2ChartB F Y * g2ChartA F X = g2ChartA F X * g2ChartB F Y :=
    fun X Y => (hcomm X Y).symm
  have h2 : ∀ X Y : SL2 F, g2ChartB F Y * (g2ChartA F X)⁻¹ = (g2ChartA F X)⁻¹ * g2ChartB F Y := by
    intro X Y
    rw [← map_inv]
    exact h1 _ _
  have hB : g2ChartB F P * g2ChartB F WSL * (g2ChartB F P)⁻¹ = g2ChartB F (P * WSL * P⁻¹) := by
    rw [map_mul, map_mul, map_inv]
  have hA : g2ChartA F P * g2ChartA F WSL * (g2ChartA F P)⁻¹ = g2ChartA F (P * WSL * P⁻¹) := by
    rw [map_mul, map_mul, map_inv]
  calc (g2ChartA F P * g2ChartB F P) * (g2ChartA F WSL * g2ChartB F WSL) *
        (g2ChartA F P * g2ChartB F P)⁻¹
      = g2ChartA F P * (g2ChartB F P * g2ChartA F WSL) * g2ChartB F WSL *
          ((g2ChartB F P)⁻¹ * (g2ChartA F P)⁻¹) := by group
    _ = g2ChartA F P * (g2ChartA F WSL * g2ChartB F P) * g2ChartB F WSL *
          ((g2ChartB F P)⁻¹ * (g2ChartA F P)⁻¹) := by rw [h1]
    _ = (g2ChartA F P * g2ChartA F WSL) * (g2ChartB F P * g2ChartB F WSL * (g2ChartB F P)⁻¹) *
          (g2ChartA F P)⁻¹ := by group
    _ = (g2ChartA F P * g2ChartA F WSL) * g2ChartB F (P * WSL * P⁻¹) * (g2ChartA F P)⁻¹ := by
        rw [hB]
    _ = (g2ChartA F P * g2ChartA F WSL) * ((g2ChartA F P)⁻¹ * g2ChartB F (P * WSL * P⁻¹)) := by
        rw [mul_assoc, h2]
    _ = (g2ChartA F P * g2ChartA F WSL * (g2ChartA F P)⁻¹) * g2ChartB F (P * WSL * P⁻¹) := by
        group
    _ = _ := by rw [hA]

theorem exists_conj_t_m0_to_sign (hodd : Odd (Nat.card F)) (h5 : Nat.card F = 5)
    (b : Fin Tag.G2.rank → Fˣ) (hb0 : IsSquare ((b g2i0 : Fˣ) : F))
    (hb1 : IsSquare ((b g2i1 : Fˣ) : F)) :
    ∃ g ∈ toralCentralizer Tag.G2 F ![-1, 1],
      g * (rootDiagUnit Tag.G2 b * (g2ChartA F WSL * g2ChartB F WSL)) * g⁻¹ =
        rootDiagUnit Tag.G2 (g2tup (-1) (-1)) := by
  obtain ⟨r₀, hr₀⟩ := hb0
  obtain ⟨r₁, hr₁⟩ := hb1
  have hr₀0 : r₀ ≠ 0 := fun h => (b g2i0).ne_zero (by rw [hr₀, h, mul_zero])
  have hr₁0 : r₁ ≠ 0 := fun h => (b g2i1).ne_zero (by rw [hr₁, h, mul_zero])
  set c₀ : Fˣ := Units.mk0 r₀ hr₀0 with hc₀
  set c₁ : Fˣ := Units.mk0 r₁ hr₁0 with hc₁
  set s : ModGL Tag.G2 F := rootDiagUnit Tag.G2 (g2tup c₀ c₁) with hs
  have hsT : s ∈ torusGroup Tag.G2 F := g2_rootDiagUnit_mem_torusGroup _
  have hsb : s * s = rootDiagUnit Tag.G2 b := by
    rw [hs, rootDiagUnit_g2tup_mul]
    congr 1
    refine g2tup_ext ?_ ?_
    · exact Units.ext (by simp [hc₀, hr₀, g2tup_0])
    · exact Units.ext (by simp [hc₁, hr₁, g2tup_1])
  have hm0 := g2_m0_inverts (F := F) hsT
  have hm0' : (g2ChartA F WSL * g2ChartB F WSL) * s = s⁻¹ * (g2ChartA F WSL * g2ChartB F WSL) := by
    rw [mul_inv_eq_iff_eq_mul] at hm0
    exact hm0
  have hconj1 : s⁻¹ * (rootDiagUnit Tag.G2 b * (g2ChartA F WSL * g2ChartB F WSL)) * s =
      g2ChartA F WSL * g2ChartB F WSL := by
    calc s⁻¹ * (rootDiagUnit Tag.G2 b * (g2ChartA F WSL * g2ChartB F WSL)) * s
        = s⁻¹ * (s * s * (g2ChartA F WSL * g2ChartB F WSL)) * s := by rw [hsb]
      _ = s * ((g2ChartA F WSL * g2ChartB F WSL) * s) := by group
      _ = s * (s⁻¹ * (g2ChartA F WSL * g2ChartB F WSL)) := by rw [hm0']
      _ = g2ChartA F WSL * g2ChartB F WSL := by group
  obtain ⟨P, u, hu, hP⟩ := exists_diagonalizer_five h5
  have hg₃ : (g2ChartA F P * g2ChartB F P) * (g2ChartA F WSL * g2ChartB F WSL) *
      (g2ChartA F P * g2ChartB F P)⁻¹ = rootDiagUnit Tag.G2 (g2tup (-1) (-1)) := by
    rw [conj_m0_chart hodd P, hP, g2ChartA_HSL, g2ChartB_HSL, rootDiagUnit_g2tup_mul]
    congr 1
    have h1 : (u⁻¹) ^ 3 * u = -1 := by
      calc (u⁻¹) ^ 3 * u = ((u * u))⁻¹ := by group
        _ = -1 := by rw [hu]; simp
    have h2 : u ^ 2 * 1 = -1 := by rw [mul_one, pow_two, hu]
    exact g2tup_ext (by rw [g2tup_0, g2tup_0]; exact h1) (by rw [g2tup_1, g2tup_1]; exact h2)
  have hg₃X : g2ChartA F P * g2ChartB F P ∈ toralCentralizer Tag.G2 F ![-1, 1] :=
    mul_mem (g2ChartA_mem_toralCentralizer hodd (a := ![-1, 1]) rfl P)
      (g2ChartB_mem_toralCentralizer hodd (a := ![-1, 1]) rfl P)
  have hsX : s⁻¹ ∈ toralCentralizer Tag.G2 F ![-1, 1] :=
    torusGroup_le_toralCentralizer _ (inv_mem hsT)
  refine ⟨(g2ChartA F P * g2ChartB F P) * s⁻¹, mul_mem hg₃X hsX, ?_⟩
  calc (g2ChartA F P * g2ChartB F P) * s⁻¹ *
        (rootDiagUnit Tag.G2 b * (g2ChartA F WSL * g2ChartB F WSL)) *
        ((g2ChartA F P * g2ChartB F P) * s⁻¹)⁻¹
      = (g2ChartA F P * g2ChartB F P) *
          (s⁻¹ * (rootDiagUnit Tag.G2 b * (g2ChartA F WSL * g2ChartB F WSL)) * s) *
          (g2ChartA F P * g2ChartB F P)⁻¹ := by group
    _ = _ := by rw [hconj1, hg₃]

end Toral

section Ambient

variable {F : Type} [Field F] [Finite F]

theorem centralizer_sup_eq_top_g2_five (hodd : Odd (Nat.card F)) (h5 : Nat.card F = 5)
    {z z' : ↥(adjointGroup Tag.G2 F)} (hz : z * z = 1) (hz' : z' * z' = 1) (hz1 : z ≠ 1)
    (hz1' : z' ≠ 1) (hne : z ≠ z') (hcomm : z * z' = z' * z) (hT : ¬ ToralPair z z') :
    Subgroup.centralizer ({z} : Set ↥(adjointGroup Tag.G2 F)) ⊔
      Subgroup.centralizer ({z'} : Set ↥(adjointGroup Tag.G2 F)) = ⊤ := by
  have hK2 : ringChar F ≠ 2 := ringChar_ne_two_of_odd_nat_card hodd
  have hneg1 : (-1 : Fˣ) ≠ 1 := fun h =>
    Ring.neg_one_ne_one_of_char_ne_two hK2 (by simpa using congrArg Units.val h)
  obtain ⟨a, ha⟩ : ∃ a : Fin Tag.G2.rank → Fˣ, a = ![-1, 1] := ⟨_, rfl⟩
  obtain ⟨hasq, hane, -⟩ := g2_toral_data_a1 (F := F) hodd ha
  have hda : rootDiagUnit Tag.G2 a ∈ torusGroup Tag.G2 F := g2_rootDiagUnit_mem_torusGroup a
  have hdK : rootDiagUnit Tag.G2 a ∈ adjointGroup Tag.G2 F :=
    (mem_toralCentralizer.mp (torusGroup_le_toralCentralizer a hda)).1
  set d₁ : ↥(adjointGroup Tag.G2 F) := ⟨_, hdK⟩ with hd₁
  have hd₁2 : d₁ * d₁ = 1 := by
    apply Subtype.ext
    show rootDiagUnit Tag.G2 a * rootDiagUnit Tag.G2 a = 1
    rw [← rootDiagUnit_mul, ← rootDiagUnit_one]
    congr 1
    funext i
    rcases hasq i with h | h <;> simp [h]
  have hd₁1 : d₁ ≠ 1 := by
    intro h
    have h' : rootDiagUnit Tag.G2 a = 1 := congrArg Subtype.val h
    rw [← rootDiagUnit_one] at h'
    exact hane (rootDiagUnit_injective h')
  obtain ⟨h, hh⟩ := g2_involutions_conj hodd hz hd₁2 hz1 hd₁1
  set w : ↥(adjointGroup Tag.G2 F) := h * z' * h⁻¹ with hw
  have hw2 : w * w = 1 := by
    calc w * w = h * (z' * z') * h⁻¹ := by rw [hw]; group
      _ = 1 := by rw [hz']; group
  have hw1 : w ≠ 1 := by
    intro h0
    apply hz1'
    calc z' = h⁻¹ * (h * z' * h⁻¹) * h := by group
      _ = 1 := by rw [← hw, h0]; group
  have hwd : w ≠ d₁ := by
    intro h0
    apply hne
    rw [← hh] at h0
    have : h * z' * h⁻¹ = h * z * h⁻¹ := h0
    calc z = h⁻¹ * (h * z * h⁻¹) * h := by group
      _ = h⁻¹ * (h * z' * h⁻¹) * h := by rw [this]
      _ = z' := by group
  have hdw : d₁ * w = w * d₁ := by
    rw [← hh, hw]
    calc h * z * h⁻¹ * (h * z' * h⁻¹) = h * (z * z') * h⁻¹ := by group
      _ = h * (z' * z) * h⁻¹ := by rw [hcomm]
      _ = h * z' * h⁻¹ * (h * z * h⁻¹) := by group
  have hwX : (w : ModGL Tag.G2 F) ∈ toralCentralizer Tag.G2 F a := by
    rw [mem_toralCentralizer]
    refine ⟨w.2, ?_⟩
    rw [mul_inv_eq_iff_eq_mul]
    exact congrArg Subtype.val hdw
  obtain ⟨x, hxX, t, ht, hx⟩ := exists_conj_to_torus_mul hodd ha hwX
    (congrArg Subtype.val hw2) (fun h0 => hw1 (Subtype.ext h0))
    (fun h0 => hwd (Subtype.ext h0))
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  have htK : rootDiagUnit Tag.G2 b ∈ adjointGroup Tag.G2 F :=
    (mem_toralCentralizer.mp (torusGroup_le_toralCentralizer a ht)).1
  have hm₀K : g2ChartA F WSL * g2ChartB F WSL ∈ adjointGroup Tag.G2 F :=
    mul_mem (g2ChartA_mem WSL) (g2ChartB_mem WSL)
  set y : ↥(adjointGroup Tag.G2 F) := ⟨rootDiagUnit Tag.G2 b * (g2ChartA F WSL * g2ChartB F WSL),
    mul_mem htK hm₀K⟩ with hy
  set x' : ↥(adjointGroup Tag.G2 F) := ⟨x, (mem_toralCentralizer.mp hxX).1⟩ with hx'
  have hyx : x' * w * x'⁻¹ = y := by
    apply Subtype.ext
    exact hx
  have hxd : x' * d₁ * x'⁻¹ = d₁ := by
    apply Subtype.ext
    have h1 := (mem_toralCentralizer.mp hxX).2
    rw [mul_inv_eq_iff_eq_mul] at h1
    show x * rootDiagUnit Tag.G2 a * x⁻¹ = rootDiagUnit Tag.G2 a
    rw [mul_inv_eq_iff_eq_mul]
    exact h1.symm
  by_cases hb : ¬ IsSquare ((b g2i0 : Fˣ) : F) ∨
      ¬ IsSquare (((b g2i0 : Fˣ) : F) * ((b g2i1 : Fˣ) : F) ^ 3)
  · have hd₁val : (d₁ : ModGL Tag.G2 F) = rootDiagUnit Tag.G2 ![-1, 1] := by
      show rootDiagUnit Tag.G2 a = _
      rw [ha]
    have hgen : Subgroup.centralizer ({d₁} : Set ↥(adjointGroup Tag.G2 F)) ⊔
        Subgroup.centralizer ({y} : Set ↥(adjointGroup Tag.G2 F)) = ⊤ := by
      apply Subgroup.map_injective (adjointGroup Tag.G2 F).subtype_injective
      rw [Subgroup.map_sup, map_centralizer_g2_eq_toralCentralizer hd₁val,
        map_centralizer_g2_eq_inf, Subgroup.map_top, Subgroup.range_subtype]
      refine le_antisymm (sup_le (fun x hx => (mem_toralCentralizer.mp hx).1) inf_le_left) ?_
      exact adjointGroup_le_sup_t_m0_five hodd h5 b hb
    have hX : Subgroup.centralizer ({d₁} : Set ↥(adjointGroup Tag.G2 F)) ⊔
        Subgroup.centralizer ({w} : Set ↥(adjointGroup Tag.G2 F)) = ⊤ := by
      apply (sup_centralizer_conj_eq_top_iff x' d₁ w).mp
      rw [hxd, hyx]
      exact hgen
    apply (sup_centralizer_conj_eq_top_iff h z z').mp
    rw [hh]
    exact hX
  · exfalso
    rw [not_or, not_not, not_not] at hb
    obtain ⟨hb0, hb03⟩ := hb
    have hb1 : IsSquare ((b g2i1 : Fˣ) : F) := by
      obtain ⟨r, hr⟩ := hb0
      obtain ⟨r', hr'⟩ := hb03
      have hr0 : r ≠ 0 := fun h0 => (b g2i0).ne_zero (by rw [hr, h0, mul_zero])
      refine ⟨r' / (r * ((b g2i1 : Fˣ) : F)), ?_⟩
      have hb10 : ((b g2i1 : Fˣ) : F) ≠ 0 := (b g2i1).ne_zero
      field_simp
      rw [hr] at hr'
      linear_combination hr'
    obtain ⟨g, hgX, hg⟩ := exists_conj_t_m0_to_sign hodd h5 b hb0 hb1
    apply hT
    have hgX' : g ∈ toralCentralizer Tag.G2 F a := by rw [ha]; exact hgX
    set G : ↥(adjointGroup Tag.G2 F) := ⟨g, (mem_toralCentralizer.mp hgX').1⟩ with hG
    have hGd : G * d₁ * G⁻¹ = d₁ := by
      apply Subtype.ext
      have h1 := (mem_toralCentralizer.mp hgX').2
      rw [mul_inv_eq_iff_eq_mul] at h1
      show g * rootDiagUnit Tag.G2 a * g⁻¹ = rootDiagUnit Tag.G2 a
      rw [mul_inv_eq_iff_eq_mul]
      exact h1.symm
    refine ⟨G * x' * h, a, g2tup (-1) (-1), hasq, ?_, hane, ?_, ?_, ?_, ?_⟩
    · intro i
      fin_cases i
      · exact Or.inr rfl
      · exact Or.inr rfl
    · intro h0
      exact hneg1 (by have := congrFun h0 g2i0; exact this)
    · intro h0
      have := congrFun h0 g2i1
      rw [show a g2i1 = 1 by rw [ha]; rfl] at this
      exact hneg1 this.symm
    · have e : G * x' * h * z * (G * x' * h)⁻¹ = d₁ := by
        calc G * x' * h * z * (G * x' * h)⁻¹
            = G * (x' * (h * z * h⁻¹) * x'⁻¹) * G⁻¹ := by group
          _ = d₁ := by rw [hh, hxd, hGd]
      rw [e]
    · have e : G * x' * h * z' * (G * x' * h)⁻¹ = G * y * G⁻¹ := by
        calc G * x' * h * z' * (G * x' * h)⁻¹
            = G * (x' * (h * z' * h⁻¹) * x'⁻¹) * G⁻¹ := by group
          _ = G * y * G⁻¹ := by rw [← hw, hyx]
      rw [e]
      show g * (rootDiagUnit Tag.G2 b * (g2ChartA F WSL * g2ChartB F WSL)) * g⁻¹ = _
      exact hg

end Ambient

section Model

variable {p : ℕ} [Fact p.Prime]

theorem g2NonToralGenerateFive_proved : G2NonToralGenerateFive p := by
  intro e hadm hp2 hq5 hq7 z z' hz hz' hz1 hz1' hne hcomm hT
  have he : e ≠ 0 := by have := hadm.2.1; omega
  have hcard : Nat.card (GaloisField p e) = p ^ e := GaloisField.card p e he
  have hodd' : Odd (p ^ e) := (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  have hodd : Odd (Nat.card (GaloisField p e)) := by rw [hcard]; exact hodd'
  have h5 : Nat.card (GaloisField p e) = 5 := by
    rw [hcard]
    obtain ⟨k, hk⟩ := hodd'
    omega
  have : Finite (GaloisField p e) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact (pow_pos (Fact.out : p.Prime).pos e).ne')
  exact centralizer_sup_eq_top_g2_five (F := GaloisField p e) hodd h5 hz hz' hz1 hz1' hne hcomm hT

theorem g2NonToralGenerate_all : G2NonToralGenerate p :=
  g2NonToralGenerate_of_five g2NonToralGenerateFive_proved

end Model

end CFSG.ClassicalInvolution.G2D4Models
