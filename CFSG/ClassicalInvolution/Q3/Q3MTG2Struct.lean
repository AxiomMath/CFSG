module

public import CFSG.ClassicalInvolution.Q3.Q3MTG2Pair
public import CFSG.ClassicalInvolution.ModelFacts.G2D4G2Struct
public import CFSG.ClassicalInvolution.ModelFacts.CF3A
public import CFSG.ClassicalInvolution.SolvableCase.SL2Three

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3MT

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.G2D4Models CFSG.ClassicalInvolution.ModelFacts CFSG.Assembly.LowTwoRank
open scoped MatrixGroups


section Torus

variable {F : Type} [Field F] [Finite F]

theorem units_mul_self_eq_one_of_card_three (h3 : Nat.card F = 3) (u : Fˣ) : u * u = 1 := by
  have h2 : Nat.card Fˣ = 2 := by rw [Nat.card_units, h3]
  have := pow_card_eq_one' (G := Fˣ) (x := u)
  rw [h2] at this
  simpa [sq] using this

theorem torus_sq_eq_one (h3 : Nat.card F = 3) {t : ModGL Tag.G2 F}
    (ht : t ∈ torusGroup Tag.G2 F) : t * t = 1 := by
  obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  rw [← rootDiagUnit_mul]
  have : l * l = 1 := funext fun j => units_mul_self_eq_one_of_card_three h3 (l j)
  rw [this, rootDiagUnit_one]

end Torus

section Centralizer

variable {F : Type} [Field F] [Finite F]

@[expose] noncomputable def g2ProdRange (hodd : Odd (Nat.card F)) : Subgroup (ModGL Tag.G2 F) :=
  ((g2ChartA F).noncommCoprod (g2ChartB F)
    (fun A B => g2ChartA_comm_g2ChartB hodd A B)).range

theorem mem_g2ProdRange {hodd : Odd (Nat.card F)} {x : ModGL Tag.G2 F} :
    x ∈ g2ProdRange hodd ↔ ∃ A B : SL2 F, g2ChartA F A * g2ChartB F B = x :=
  ⟨fun ⟨⟨A, B⟩, h⟩ => ⟨A, B, h⟩, fun ⟨A, B, h⟩ => ⟨(A, B), h⟩⟩

theorem torus_conj_mem_g2ProdRange (hodd : Odd (Nat.card F)) {t : ModGL Tag.G2 F}
    (ht : t ∈ torusGroup Tag.G2 F) {s : ModGL Tag.G2 F} (hs : s ∈ g2ProdRange hodd) :
    t * s * t⁻¹ ∈ g2ProdRange hodd := by
  obtain ⟨A, B, rfl⟩ := mem_g2ProdRange.mp hs
  obtain ⟨A', hA'⟩ := torus_conj_chart ht 1 g2i1 A
  obtain ⟨B', hB'⟩ := torus_conj_chart ht g2WeylU g2i0 B
  refine mem_g2ProdRange.mpr ⟨A', B', ?_⟩
  change rootChart Tag.G2 F 1 g2i1 A' * rootChart Tag.G2 F g2WeylU g2i0 B' = _
  rw [← hA', ← hB']
  group

theorem sq_mem_g2ProdRange (hodd : Odd (Nat.card F)) (h3 : Nat.card F = 3)
    {a : Fin Tag.G2.rank → Fˣ} (ha : a = ![-1, 1]) {x : ModGL Tag.G2 F}
    (hx : x ∈ toralCentralizer Tag.G2 F a) : x * x ∈ g2ProdRange hodd := by
  obtain ⟨t, ht, A, B, rfl⟩ := toralCentralizer_le_prod hodd ha hx
  have hts := torus_sq_eq_one h3 ht
  have hs : g2ChartA F A * g2ChartB F B ∈ g2ProdRange hodd :=
    mem_g2ProdRange.mpr ⟨A, B, rfl⟩
  have hconj : t⁻¹ * (g2ChartA F A * g2ChartB F B) * t ∈ g2ProdRange hodd := by
    have := torus_conj_mem_g2ProdRange hodd (inv_mem ht) hs
    simpa using this
  have e : t * g2ChartA F A * g2ChartB F B * (t * g2ChartA F A * g2ChartB F B) =
      (t⁻¹ * (g2ChartA F A * g2ChartB F B) * t) * (g2ChartA F A * g2ChartB F B) := by
    calc _ = (t * t) * (t⁻¹ * (g2ChartA F A * g2ChartB F B) * t) *
          (g2ChartA F A * g2ChartB F B) := by group
      _ = _ := by rw [hts, one_mul]
  rw [e]
  exact mul_mem hconj hs

theorem g2Chart_neg_one (hodd : Odd (Nat.card F)) :
    g2ChartA F (-1) = rootDiagUnit Tag.G2 (![-1, 1] : Fin Tag.G2.rank → Fˣ) ∧
      g2ChartB F (-1) = rootDiagUnit Tag.G2 (![-1, 1] : Fin Tag.G2.rank → Fˣ) := by
  obtain ⟨hasq, hane, hker, -, -, -⟩ := g2_toral_data_a1 (F := F) hodd
    (a := (![-1, 1] : Fin Tag.G2.rank → Fˣ)) rfl
  exact ⟨rootChart_neg_one hodd hasq hane (γ := g2vec 0 1) (by rw [hker]; simp) (w := 1)
      (i := g2i1) (by rw [one_smul, g2_single_1]),
    rootChart_neg_one hodd hasq hane (γ := g2vec 2 3) (by rw [hker]; simp) (w := g2WeylU)
      (i := g2i0) g2WeylU_smul_single⟩

theorem chart_mem_g2ProdRange [CharP F 3] (hodd : Odd (Nat.card F)) (h3 : Nat.card F = 3)
    {a : Fin Tag.G2.rank → Fˣ} (ha : a = ![-1, 1]) {Ψ : SL2 F →* ModGL Tag.G2 F}
    (hX : ∀ A, Ψ A ∈ toralCentralizer Tag.G2 F a) (A : SL2 F) : Ψ A ∈ g2ProdRange hodd := by
  obtain ⟨S₃, -, h3s, hcl⟩ := gen3_top_sl2 (F := F)
  have hle : Subgroup.closure S₃ ≤ (g2ProdRange hodd).comap Ψ := by
    rw [Subgroup.closure_le]
    intro s hs
    have hy3 : Ψ s * Ψ s * Ψ s = 1 := by rw [← pow_three', ← map_pow, h3s s hs, map_one]
    have hsq := sq_mem_g2ProdRange hodd h3 ha (hX s)
    show Ψ s ∈ g2ProdRange hodd
    have e : Ψ s = (Ψ s * Ψ s) * (Ψ s * Ψ s) := by
      calc Ψ s = Ψ s * (Ψ s * Ψ s * Ψ s) := by rw [hy3, mul_one]
        _ = (Ψ s * Ψ s) * (Ψ s * Ψ s) := by group
    rw [e]
    exact mul_mem hsq hsq
  exact hle (hcl (Subgroup.mem_top A))

theorem symm_neg_one_of_equiv (hodd : Odd (Nat.card F)) (ε : SL(2, F) ≃* SL(2, ZMod 3)) :
    ε.symm (-1) = -1 := by
  have h2 : (2 : F) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card F hodd
  have hsq : ε.symm (-1) * ε.symm (-1) = 1 := by
    rw [← map_mul, sl23_neg_one_mul_self, map_one]
  rcases sl2_sq_eq_one h2 hsq with h | h
  · exact absurd (ε.symm.injective (h.trans (map_one ε.symm).symm)) sl23_neg_one_ne_one
  · exact h

theorem chart_neg_one_eq_of_le_toralCentralizer [CharP F 3] (hodd : Odd (Nat.card F))
    (h3 : Nat.card F = 3) {a : Fin Tag.G2.rank → Fˣ} (ha : a = ![-1, 1])
    {Ψ : SL2 F →* ModGL Tag.G2 F} (hΨ : Function.Injective Ψ)
    (hX : ∀ A, Ψ A ∈ toralCentralizer Tag.G2 F a) : Ψ (-1) = rootDiagUnit Tag.G2 a := by
  obtain ⟨ε⟩ := nonempty_mulEquiv_sl2Three_of_natCard_eq_three h3
  have h2 : (2 : F) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card F hodd
  obtain ⟨hA1, hB1⟩ := g2Chart_neg_one (F := F) hodd
  rw [← ha] at hA1 hB1
  have key := eq_central_of_le_mul3 h2 ((g2ChartA F).comp ε.symm.toMonoidHom) (g2ChartB F)
    ((g2ChartA_injective hodd).comp ε.symm.injective) (g2ChartB_injective hodd)
    (fun A B => g2ChartA_comm_g2ChartB hodd _ B)
    (by
      show g2ChartA F (ε.symm (-1)) = g2ChartB F (-1)
      rw [symm_neg_one_of_equiv hodd ε, hA1, hB1])
    (Ψ.comp ε.symm.toMonoidHom) (hΨ.comp ε.symm.injective)
    (fun A => by
      obtain ⟨A', B', h⟩ := mem_g2ProdRange.mp (chart_mem_g2ProdRange hodd h3 ha hX (ε.symm A))
      exact ⟨ε A', B', by
        show Ψ (ε.symm A) = g2ChartA F (ε.symm (ε A')) * g2ChartB F B'
        rw [MulEquiv.symm_apply_apply, h]⟩)
  have key' : Ψ (ε.symm (-1)) = g2ChartB F (-1) := key
  rw [symm_neg_one_of_equiv hodd ε, hB1] at key'
  exact key'

end Centralizer

section Involutions

variable {F : Type} [Field F] [Finite F]

theorem chart_neg_one_eq_of_commutes_g2 [CharP F 3] (hodd : Odd (Nat.card F))
    (h3 : Nat.card F = 3) {z : ↥(adjointGroup Tag.G2 F)} (hz : z * z = 1) (hz1 : z ≠ 1)
    {Ψ : SL2 F →* ↥(adjointGroup Tag.G2 F)} (hΨ : Function.Injective Ψ)
    (hc : ∀ A, Ψ A * z = z * Ψ A) : Ψ (-1) = z := by
  obtain ⟨hA1, -⟩ := g2Chart_neg_one (F := F) hodd
  set a : Fin Tag.G2.rank → Fˣ := ![-1, 1] with ha
  set ι : ↥(adjointGroup Tag.G2 F) →* ModGL Tag.G2 F := (adjointGroup Tag.G2 F).subtype with hι
  let d₀ : ↥(adjointGroup Tag.G2 F) := ⟨g2ChartA F (-1), g2ChartA_mem (-1)⟩
  have hd₀ : d₀ * d₀ = 1 := Subtype.ext (by
    show g2ChartA F (-1) * g2ChartA F (-1) = 1
    rw [← map_mul]
    have : (-1 : SL2 F) * -1 = 1 := by simp
    rw [this, map_one])
  have hd₀1 : d₀ ≠ 1 := fun h => by
    have h1 : g2ChartA F (-1) = 1 := congrArg Subtype.val h
    exact CFSG.ClassicalInvolution.sl2_neg_one_ne_one hodd
      (g2ChartA_injective hodd (h1.trans (map_one _).symm))
  obtain ⟨h, hh⟩ := g2_involutions_conj hodd hz hd₀ hz1 hd₀1
  set Ψ₂ : SL2 F →* ↥(adjointGroup Tag.G2 F) := (MulAut.conj h).toMonoidHom.comp Ψ with hΨ₂
  have hΨ₂inj : Function.Injective Ψ₂ := (MulAut.conj h).injective.comp hΨ
  have hc₂ : ∀ A, Ψ₂ A * d₀ = d₀ * Ψ₂ A := by
    intro A
    rw [← hh]
    show h * Ψ A * h⁻¹ * (h * z * h⁻¹) = h * z * h⁻¹ * (h * Ψ A * h⁻¹)
    calc h * Ψ A * h⁻¹ * (h * z * h⁻¹) = h * (Ψ A * z) * h⁻¹ := by group
      _ = h * (z * Ψ A) * h⁻¹ := by rw [hc A]
      _ = h * z * h⁻¹ * (h * Ψ A * h⁻¹) := by group
  have hX : ∀ A, (ι.comp Ψ₂) A ∈ toralCentralizer Tag.G2 F a := by
    intro A
    rw [mem_toralCentralizer]
    refine ⟨(Ψ₂ A).2, ?_⟩
    have h1 : ι (Ψ₂ A) * rootDiagUnit Tag.G2 a = rootDiagUnit Tag.G2 a * ι (Ψ₂ A) := by
      rw [← hA1]
      exact congrArg Subtype.val (hc₂ A)
    show rootDiagUnit Tag.G2 a * ι (Ψ₂ A) * (rootDiagUnit Tag.G2 a)⁻¹ = ι (Ψ₂ A)
    rw [mul_inv_eq_iff_eq_mul, ← h1]
  have hkey := chart_neg_one_eq_of_le_toralCentralizer hodd h3 ha
    (Ψ := ι.comp Ψ₂) (Subtype.val_injective.comp hΨ₂inj) hX
  have hΨ₂neg : Ψ₂ (-1) = d₀ := Subtype.ext (hkey.trans hA1.symm)
  have h1 : h * Ψ (-1) * h⁻¹ = h * z * h⁻¹ := by
    rw [hh]
    exact hΨ₂neg
  exact mul_left_cancel (mul_right_cancel h1)

end Involutions

end CFSG.ClassicalInvolution.Q3.Q3MT
