module

public import CFSG.GH74.Generic.Front.SpLA
public import CFSG.GH74.Generic.Front.DataLin
public import CFSG.GH74.Generic.Front.NoCentral
public import CFSG.GH74.Generic.ClassicalCerts
public import CFSG.ClassicalGroups.Symplectic.Model

public section

namespace CFSG.GH74.Generic

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.GH74.Filter.ClassicalOdd CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices CFSG.LinearGroups Matrix Subgroup
open scoped MatrixGroups

section SpData

variable {F : Type} [Field F]

@[expose] def sp2Diag : SL(2, F) × SL(2, F) →* Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F where
  toFun g := planeDiag ![(g.1 : Matrix (Fin 2) (Fin 2) F), (g.2 : Matrix (Fin 2) (Fin 2) F)]
  map_one' := by
    have : (![((1 : SL(2, F) × SL(2, F)).1 : Matrix (Fin 2) (Fin 2) F),
        ((1 : SL(2, F) × SL(2, F)).2 : Matrix (Fin 2) (Fin 2) F)] :
          Fin 2 → Matrix (Fin 2) (Fin 2) F) = fun _ => 1 := by
      funext i
      fin_cases i <;> simp
    rw [this]
    exact planeDiag_one
  map_mul' g h := by
    rw [planeDiag_mul]
    congr 1
    funext i
    fin_cases i <;> simp

theorem sp2Diag_apply (g : SL(2, F) × SL(2, F)) :
    sp2Diag g = planeDiag ![(g.1 : Matrix (Fin 2) (Fin 2) F), (g.2 : Matrix (Fin 2) (Fin 2) F)] :=
  rfl

theorem sp2Diag_symplectic (g : SL(2, F) × SL(2, F)) :
    (sp2Diag g)ᵀ * sp2Gram F * sp2Diag g = sp2Gram F :=
  planeDiag_symplectic _ fun i => by fin_cases i <;> simp

theorem sp2Diag_toHomUnits_val (g : SL(2, F) × SL(2, F)) :
    ((sp2Diag.toHomUnits g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
      sp2Diag g := rfl

theorem sp2Diag_mem (g : SL(2, F) × SL(2, F)) : sp2Diag.toHomUnits g ∈ StatedSp 2 F := by
  refine Subgroup.subset_closure ?_
  show ((sp2Diag.toHomUnits g : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)ᵀ * fromBlocks 0 1 (-1) 0 *
      ((sp2Diag.toHomUnits g : GL (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = fromBlocks 0 1 (-1) 0
  rw [sp2Diag_toHomUnits_val]
  exact sp2Diag_symplectic g

@[expose] noncomputable def spDiagHom : SL(2, F) × SL(2, F) →* StatedSp 2 F :=
  sp2Diag.toHomUnits.codRestrict (StatedSp 2 F) sp2Diag_mem

theorem spDiagHom_val (g : SL(2, F) × SL(2, F)) :
    (((spDiagHom g : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
      sp2Diag g := rfl

theorem statedSp_gram {n : ℕ} (x : StatedSp n F) :
    ((x : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)ᵀ *
        fromBlocks 0 1 (-1) 0 *
        ((x : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
      fromBlocks 0 1 (-1) 0 := by
  have hx : (x : GL (Fin n ⊕ Fin n) F) ∈ TauCeti.GLSymplectic (Fin n) F := by
    rw [← CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic]
    exact x.2
  exact (CFSG.ClassicalGroups.Symplectic.blueprintGram_iff_mem_symplecticGroup _).2
    (TauCeti.GLSymplectic.mem_iff_mem_symplecticGroup.1 hx)

theorem range_comp_le_range_aux {G N P : Type*} [Group G] [Group N] [Group P] (g : N →* P)
    (f : G →* N) : (g.comp f).range ≤ g.range := by
  rintro _ ⟨x, rfl⟩
  exact ⟨f x, rfl⟩

theorem planeDiag_neg_one_one :
    planeDiag ![(-1 : Matrix (Fin 2) (Fin 2) F), 1] =
      Matrix.diagonal (Sum.elim ![(-1 : F), 1] ![(-1 : F), 1]) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [planeDiag]

end SpData

section Main

variable {F : Type} [Field F] [Finite F]

theorem frontData0_statedSp2 (hF : Odd (Nat.card F)) : Nonempty (FrontData0 ↥(StatedSp 2 F)) := by
  classical
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card hF
  have hF2 : ringChar F ≠ 2 := ringChar_ne_two_of_two_ne_zero h2
  obtain ⟨a, b, h⟩ := (odd_field_two_dimensional_quaternion_matrices hF2).1
  let qh : Q8 →* SL(2, F) := quatHom h
  have hqinj : Function.Injective qh := quatHom_injective hF2 h
  have hz : ((qh (QuaternionGroup.a 2) : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = -1 :=
    quatHom_a_two h
  let φ : Q8 × Q8 →* StatedSp 2 F := spDiagHom.comp (qh.prodMap qh)
  have hφ : ∀ g k : Q8, (((φ (g, k) : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
        planeDiag ![(qh g : Matrix (Fin 2) (Fin 2) F), (qh k : Matrix (Fin 2) (Fin 2) F)] :=
    fun g k => rfl
  have hφz : (((φ (QuaternionGroup.a 2, 1) : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
        Matrix.diagonal (Sum.elim ![(-1 : F), 1] ![(-1 : F), 1]) := by
    rw [hφ, hz, map_one]
    exact planeDiag_neg_one_one
  let w : StatedSp 2 F := ⟨spSwapGL, Subgroup.subset_closure spSwapMat_symplectic⟩
  have hww : w * w = 1 := Subtype.ext (Units.ext spSwapMat_mul_self)
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hww
  have hone : ∀ t : StatedSp 2 F, t * t = 1 → t ≠ 1 → t ∉ Subgroup.center (StatedSp 2 F) →
      ∃ k : StatedSp 2 F, k * t * k⁻¹ = φ (QuaternionGroup.a 2, 1) := by
    intro t ht h1 hc
    have hM2 : ((t : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
        ((t : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = 1 := by
      have := congrArg (fun u : StatedSp 2 F =>
        ((u : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) ht
      simpa using this
    have hM1 : ((t : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) ≠ 1 :=
      fun hh => h1 (Subtype.ext (Units.ext (by simpa using hh)))
    have hMm1 : ((t : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) ≠ -1 := by
      intro hh
      apply hc
      rw [CFSG.LieType.Universal.Symplectic.center_eq, Subgroup.mem_subgroupOf, StatedScalars,
        MonoidHom.mem_range]
      refine ⟨-1, ?_⟩
      rw [NoCentralAux.scalar_neg_one]
      exact (Units.ext (by simpa using hh)).symm
    obtain ⟨g, hg⟩ := exists_symplectic_conj h2 _ hM2 (statedSp_gram t) hM1 hMm1
    refine ⟨g⁻¹, ?_⟩
    apply Subtype.ext
    apply Units.ext
    have hginv : (((g⁻¹ : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
        ((g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = 1 := by
      simp
    rw [inv_inv]
    simp only [Subgroup.coe_mul, Units.val_mul]
    rw [hφz, Matrix.mul_assoc, hg, ← Matrix.mul_assoc, hginv, Matrix.one_mul]
  have hsplit : ∀ X Y : SL(2, F), spDiagHom (X, Y) = spDiagHom (X, 1) * spDiagHom (1, Y) := by
    intro X Y
    rw [← map_mul]
    simp
  refine ⟨⟨φ, w, spDiagHom.range, ?_, hww, ?_, hone, ?_, ?_, ?_⟩⟩
  · intro x y hxy
    have h1 : sp2Diag (qh x.1, qh x.2) = sp2Diag (qh y.1, qh y.2) :=
      congrArg (fun z : StatedSp 2 F =>
        ((z : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) hxy
    have h3 := planeDiag_inj h1
    exact Prod.ext (hqinj (Subtype.ext (congrFun h3 0))) (hqinj (Subtype.ext (congrFun h3 1)))
  · intro g k
    rw [hwinv]
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul]
    exact spSwapMat_mul_planeDiag_mul _ _
  · exact range_comp_le_range_aux _ _
  · rintro _ ⟨⟨X, Y⟩, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    show spDiagHom (X, Y) * spDiagHom (qh (QuaternionGroup.a 2), qh 1) =
      spDiagHom (qh (QuaternionGroup.a 2), qh 1) * spDiagHom (X, Y)
    rw [← map_mul, ← map_mul]
    congr 1
    refine Prod.ext ?_ (by simp)
    apply Subtype.ext
    simp [hz]
  · by_cases h4 : 4 ≤ Nat.card F
    · left
      have hSL : Group.IsPerfect SL(2, F) := CFSG.ClassicalInvolution.sl2_isPerfect h4
      have hJL : ⁅(spDiagHom.comp (MonoidHom.inl SL(2, F) SL(2, F))).range,
          (spDiagHom.comp (MonoidHom.inl SL(2, F) SL(2, F))).range⁆ =
          (spDiagHom.comp (MonoidHom.inl SL(2, F) SL(2, F))).range :=
        Subgroup.isPerfect_iff.1 (Group.IsPerfect.range _)
      have hJR : ⁅(spDiagHom.comp (MonoidHom.inr SL(2, F) SL(2, F))).range,
          (spDiagHom.comp (MonoidHom.inr SL(2, F) SL(2, F))).range⁆ =
          (spDiagHom.comp (MonoidHom.inr SL(2, F) SL(2, F))).range :=
        Subgroup.isPerfect_iff.1 (Group.IsPerfect.range _)
      have hsup : spDiagHom.range =
          (spDiagHom.comp (MonoidHom.inl SL(2, F) SL(2, F))).range ⊔
            (spDiagHom.comp (MonoidHom.inr SL(2, F) SL(2, F))).range := by
        apply le_antisymm
        · rintro _ ⟨⟨X, Y⟩, rfl⟩
          rw [hsplit]
          exact Subgroup.mul_mem_sup ⟨X, rfl⟩ ⟨Y, rfl⟩
        · exact sup_le (range_comp_le_range_aux _ _) (range_comp_le_range_aux _ _)
      rw [hsup]
      exact commutator_sup_eq_of_perfect hJL hJR
    · right
      have hcard2 : 2 ≤ Nat.card F := Finite.one_lt_card
      have h3 : Nat.card F = 3 := by
        obtain ⟨m, hm⟩ := hF
        omega
      refine ⟨?_, ⟨F, inferInstance, inferInstance, h3, Or.inr ⟨MulEquiv.refl _⟩⟩⟩
      apply le_antisymm
      · exact (Subgroup.closure_le _).2 (fun g hg => hg.1)
      · set S : Set (StatedSp 2 F) := {g | g ∈ spDiagHom.range ∧ Odd (orderOf g)} with hS
        rintro _ ⟨⟨X, Y⟩, rfl⟩
        rw [hsplit]
        refine Subgroup.mul_mem _ ?_ ?_
        · exact map_mem_closure_of_elementary (spDiagHom.comp (MonoidHom.inl SL(2, F) SL(2, F))) S
            (fun e he => ⟨⟨(e, 1), rfl⟩,
              odd_orderOf_map_elementary hF (spDiagHom.comp (MonoidHom.inl SL(2, F) SL(2, F))) he⟩) X
        · exact map_mem_closure_of_elementary (spDiagHom.comp (MonoidHom.inr SL(2, F) SL(2, F))) S
            (fun e he => ⟨⟨(1, e), rfl⟩,
              odd_orderOf_map_elementary hF (spDiagHom.comp (MonoidHom.inr SL(2, F) SL(2, F))) he⟩) Y

end Main

end CFSG.GH74.Generic
