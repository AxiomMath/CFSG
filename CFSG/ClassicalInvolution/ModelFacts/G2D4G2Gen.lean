module

public import CFSG.ClassicalInvolution.ModelFacts.G2D4G2Lin

public noncomputable section

namespace CFSG.ClassicalInvolution.G2D4Models

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

section RootPairs

variable {τ : Tag} {K : Type} [Field K]

theorem range_simpleRootSL2_eq_rootPair (i : Fin τ.rank) :
    (simpleRootSL2 τ K i).range = rootPair τ K (Pi.single i 1) := by
  have h := rootChart_range (τ := τ) (K := K) (w := 1) (i := i) (γ := Pi.single i 1) (by simp)
  rw [← h]
  have : rootChart τ K 1 i = simpleRootSL2 τ K i := by
    refine MonoidHom.ext fun A => ?_
    simp [rootChart, canonicalRep_one]
  rw [this]

theorem adjointGroup_eq_iSup_rootPair_single :
    adjointGroup τ K = ⨆ i : Fin τ.rank, rootPair τ K (Pi.single i 1) := by
  apply le_antisymm
  · refine (Subgroup.closure_le _).2 ?_
    rintro g ⟨i, c, hg | hg⟩
    · have hg' : g = xUnit τ K i c := Units.ext hg
      have hmem : g ∈ rootPair τ K (Pi.single i 1) := by
        rw [← range_simpleRootSL2_eq_rootPair, hg', ← simpleRootSL2_uSL]
        exact ⟨_, rfl⟩
      exact Subgroup.mem_iSup_of_mem i hmem
    · have hg' : g = yUnit τ K i c := Units.ext hg
      have hmem : g ∈ rootPair τ K (Pi.single i 1) := by
        rw [← range_simpleRootSL2_eq_rootPair, hg', ← simpleRootSL2_vSL]
        exact ⟨_, rfl⟩
      exact Subgroup.mem_iSup_of_mem i hmem
  · exact iSup_le fun i => by
      rw [← range_simpleRootSL2_eq_rootPair]
      rintro _ ⟨A, rfl⟩
      exact simpleRootSL2_mem_adjointGroup i A

theorem rootPair_le_toralCentralizer {a : Fin τ.rank → Kˣ} {γ : Fin τ.rank → ℤ}
    (hγ : γ ∈ rootCharKernel a) : rootPair τ K γ ≤ toralCentralizer τ K a := by
  rw [toralCentralizer]
  refine le_inf ?_ ?_
  · exact sup_le (rootSubgroup_le_adjointGroup γ) (rootSubgroup_le_adjointGroup (-γ))
  · rw [rootPair_eq_rootSpan]
    refine rootSpan_le_centralizer a (S := {γ, -γ}) ?_
    rintro x (rfl | rfl)
    · exact hγ
    · exact ⟨IsRoot.neg hγ.1, by rw [rootChar_neg_inv, hγ.2, inv_one]⟩

end RootPairs

section G2

variable {K : Type} [Field K]

theorem rootChar_single_g2 (a : Fin Tag.G2.rank → Kˣ) (i : Fin Tag.G2.rank) :
    rootChar a (Pi.single i 1 : Fin Tag.G2.rank → ℤ) = a i := by
  have := rootChar_nsmul_single a i 1
  rw [one_smul, pow_one] at this
  exact this

theorem toralCentralizer_sup_eq_adjointGroup_g2 :
    toralCentralizer Tag.G2 K ![-1, 1] ⊔ toralCentralizer Tag.G2 K ![1, -1] =
      adjointGroup Tag.G2 K := by
  apply le_antisymm
  · exact sup_le inf_le_left inf_le_left
  · rw [adjointGroup_eq_iSup_rootPair_single]
    refine iSup_le fun i => ?_
    fin_cases i
    · exact le_sup_of_le_right (rootPair_le_toralCentralizer ⟨isRoot_single _ _,
        (rootChar_single_g2 _ _).trans rfl⟩)
    · exact le_sup_of_le_left (rootPair_le_toralCentralizer ⟨isRoot_single _ _,
        (rootChar_single_g2 _ _).trans rfl⟩)

end G2

section WeylMove

variable {K : Type} [Field K]

theorem weylTuple_signs (w : WeylGroup Tag.G2) {b : Fin Tag.G2.rank → Kˣ}
    (hb : ∀ i, b i = 1 ∨ b i = -1) (i : Fin Tag.G2.rank) :
    weylTuple w b i = 1 ∨ weylTuple w b i = -1 := by
  have hbsq : ∀ j, b j ^ 2 = 1 := fun j => by
    rcases hb j with h | h <;> simp [h]
  exact unit_eq_one_or_neg_one_of_sq_eq_one (weylTuple_sq_eq_one hbsq w i)

theorem vec_g2i0 {M : Type*} (x y : M) : (![x, y] : Fin Tag.G2.rank → M) g2i0 = x := rfl

theorem vec_g2i1 {M : Type*} (x y : M) : (![x, y] : Fin Tag.G2.rank → M) g2i1 = y := rfl

theorem exists_weyl_move_signPair (hneg : (-1 : Kˣ) ≠ 1) {a b : Fin Tag.G2.rank → Kˣ}
    (ha : ∀ i, a i = 1 ∨ a i = -1) (hb : ∀ i, b i = 1 ∨ b i = -1) (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (hab : a ≠ b) :
    ∃ w : WeylGroup Tag.G2, weylTuple w a = ![-1, 1] ∧ weylTuple w b = ![1, -1] := by
  have hA : ∀ i, (![-1, 1] : Fin Tag.G2.rank → Kˣ) i = 1 ∨
      (![-1, 1] : Fin Tag.G2.rank → Kˣ) i = -1 := by
    intro i
    fin_cases i <;> simp
  have hA1 : (![-1, 1] : Fin Tag.G2.rank → Kˣ) ≠ 1 := by
    intro h
    have := congrFun h g2i0
    rw [vec_g2i0] at this
    exact hneg this
  obtain ⟨w₁, hw₁⟩ := g2_signTuple_conj ha hA ha1 hA1
  set b₁ := weylTuple w₁ b with hb₁
  have hb₁s : ∀ i, b₁ i = 1 ∨ b₁ i = -1 := fun i => weylTuple_signs w₁ hb i
  have hone : ∀ w : WeylGroup Tag.G2, weylTuple w (1 : Fin Tag.G2.rank → Kˣ) = 1 := by
    intro w
    funext i
    simp [weylTuple, rootChar]
  have hb₁1 : b₁ ≠ 1 := by
    intro h
    apply hb1
    have := congrArg (weylTuple w₁⁻¹) h
    rw [hb₁, weylTuple_weylTuple, inv_mul_cancel, weylTuple_one, hone] at this
    exact this
  have hb₁a : b₁ ≠ ![-1, 1] := by
    intro h
    apply hab
    have h2 : weylTuple w₁ a = weylTuple w₁ b := hw₁.trans h.symm
    have := congrArg (weylTuple w₁⁻¹) h2
    rw [weylTuple_weylTuple, inv_mul_cancel, weylTuple_one, weylTuple_weylTuple,
      inv_mul_cancel, weylTuple_one] at this
    exact this
  have hcases : b₁ = ![1, -1] ∨ b₁ = ![-1, -1] := by
    rcases hb₁s g2i0 with h0 | h0 <;> rcases hb₁s g2i1 with h1 | h1
    · exact absurd (g2_funext h0 h1) hb₁1
    · exact Or.inl (g2_funext (h0.trans (vec_g2i0 _ _).symm) (h1.trans (vec_g2i1 _ _).symm))
    · exact absurd (g2_funext (h0.trans (vec_g2i0 _ _).symm) (h1.trans (vec_g2i1 _ _).symm)) hb₁a
    · exact Or.inr (g2_funext (h0.trans (vec_g2i0 _ _).symm) (h1.trans (vec_g2i1 _ _).symm))
  rcases hcases with h | h
  · exact ⟨w₁, hw₁, h⟩
  · refine ⟨simple Tag.G2 g2i1 * w₁, ?_, ?_⟩
    · rw [← weylTuple_weylTuple, hw₁]
      refine g2_funext ?_ ?_
      · refine (weylTuple_simple_g1_zero _).trans ?_
        rw [vec_g2i0, vec_g2i1]
        simp
      · refine (weylTuple_simple_g1_one _).trans ?_
        rw [vec_g2i1]
        simp
    · rw [← weylTuple_weylTuple, ← hb₁, h]
      refine g2_funext ?_ ?_
      · refine (weylTuple_simple_g1_zero _).trans ?_
        rw [vec_g2i0, vec_g2i1, vec_g2i0]
        simp [Odd.neg_one_pow (show Odd 3 by decide)]
      · refine (weylTuple_simple_g1_one _).trans ?_
        rw [vec_g2i1, vec_g2i1]
        simp

end WeylMove

section Model

variable {F : Type} [Field F]

theorem map_centralizer_g2_eq_toralCentralizer {a : Fin Tag.G2.rank → Fˣ}
    {c : ↥(adjointGroup Tag.G2 F)} (hc : (c : ModGL Tag.G2 F) = rootDiagUnit Tag.G2 a) :
    (Subgroup.centralizer ({c} : Set ↥(adjointGroup Tag.G2 F))).map
        (adjointGroup Tag.G2 F).subtype = toralCentralizer Tag.G2 F a := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_toralCentralizer]
    refine ⟨x.2, ?_⟩
    have h := Subgroup.mem_centralizer_singleton_iff.mp hx
    have h2 : ((x * c : ↥(adjointGroup Tag.G2 F)) : ModGL Tag.G2 F) =
        ((c * x : ↥(adjointGroup Tag.G2 F)) : ModGL Tag.G2 F) := congrArg Subtype.val h
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hc] at h2
    rw [mul_inv_eq_iff_eq_mul]
    exact h2.symm
  · intro hy
    rw [mem_toralCentralizer] at hy
    refine ⟨⟨y, hy.1⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hc]
    have h := hy.2
    rw [mul_inv_eq_iff_eq_mul] at h
    exact h.symm

theorem centralizer_sup_eq_top_of_signs {c₁ c₂ : ↥(adjointGroup Tag.G2 F)}
    (h₁ : (c₁ : ModGL Tag.G2 F) = rootDiagUnit Tag.G2 ![-1, 1])
    (h₂ : (c₂ : ModGL Tag.G2 F) = rootDiagUnit Tag.G2 ![1, -1]) :
    Subgroup.centralizer ({c₁} : Set ↥(adjointGroup Tag.G2 F)) ⊔
      Subgroup.centralizer ({c₂} : Set ↥(adjointGroup Tag.G2 F)) = ⊤ := by
  apply Subgroup.map_injective (adjointGroup Tag.G2 F).subtype_injective
  rw [Subgroup.map_sup, map_centralizer_g2_eq_toralCentralizer h₁,
    map_centralizer_g2_eq_toralCentralizer h₂, toralCentralizer_sup_eq_adjointGroup_g2,
    Subgroup.map_top, Subgroup.range_subtype]

theorem conjSub_centralizer_singleton_g2d4 {G : Type*} [Group G] (g c : G) :
    (Subgroup.centralizer ({c} : Set G)).map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer ({g * c * g⁻¹} : Set G) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    show g * x * g⁻¹ * (g * c * g⁻¹) = g * c * g⁻¹ * (g * x * g⁻¹)
    calc g * x * g⁻¹ * (g * c * g⁻¹) = g * (x * c) * g⁻¹ := by group
      _ = g * (c * x) * g⁻¹ := by rw [hx]
      _ = g * c * g⁻¹ * (g * x * g⁻¹) := by group
  · intro hy
    rw [Subgroup.mem_centralizer_singleton_iff] at hy
    refine ⟨g⁻¹ * y * g, ?_, by show g * (g⁻¹ * y * g) * g⁻¹ = y; group⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    have h2 : g⁻¹ * (y * (g * c * g⁻¹)) * g = g⁻¹ * ((g * c * g⁻¹) * y) * g := by rw [hy]
    calc g⁻¹ * y * g * c = g⁻¹ * (y * (g * c * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * c * g⁻¹) * y) * g := h2
      _ = c * (g⁻¹ * y * g) := by group

@[expose] def ToralPair (z z' : ↥(adjointGroup Tag.G2 F)) : Prop :=
  ∃ (g : ↥(adjointGroup Tag.G2 F)) (a b : Fin Tag.G2.rank → Fˣ),
    (∀ i, a i = 1 ∨ a i = -1) ∧ (∀ i, b i = 1 ∨ b i = -1) ∧ a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b ∧
      ((g * z * g⁻¹ : ↥(adjointGroup Tag.G2 F)) : ModGL Tag.G2 F) = rootDiagUnit Tag.G2 a ∧
      ((g * z' * g⁻¹ : ↥(adjointGroup Tag.G2 F)) : ModGL Tag.G2 F) = rootDiagUnit Tag.G2 b

theorem centralizer_sup_eq_top_of_toralPair (hneg : (-1 : Fˣ) ≠ 1)
    {z z' : ↥(adjointGroup Tag.G2 F)} (h : ToralPair z z') :
    Subgroup.centralizer ({z} : Set ↥(adjointGroup Tag.G2 F)) ⊔
      Subgroup.centralizer ({z'} : Set ↥(adjointGroup Tag.G2 F)) = ⊤ := by
  obtain ⟨g, a, b, ha, hb, ha1, hb1, hab, hz, hz'⟩ := h
  obtain ⟨w, hwa, hwb⟩ := exists_weyl_move_signPair hneg ha hb ha1 hb1 hab
  set N : ↥(adjointGroup Tag.G2 F) :=
    ⟨canonicalRep (coxeterSystem Tag.G2) F w, canonicalRep_mem_adjointGroup _ F w⟩ with hN
  set M := N * g with hM
  have hMz : ((M * z * M⁻¹ : ↥(adjointGroup Tag.G2 F)) : ModGL Tag.G2 F) =
      rootDiagUnit Tag.G2 ![-1, 1] := by
    have e : M * z * M⁻¹ = N * (g * z * g⁻¹) * N⁻¹ := by rw [hM]; group
    rw [e, Subgroup.coe_mul, Subgroup.coe_mul, hz, Subgroup.coe_inv]
    rw [← hwa]
    exact canonicalRep_conj_rootDiagUnit w a
  have hMz' : ((M * z' * M⁻¹ : ↥(adjointGroup Tag.G2 F)) : ModGL Tag.G2 F) =
      rootDiagUnit Tag.G2 ![1, -1] := by
    have e : M * z' * M⁻¹ = N * (g * z' * g⁻¹) * N⁻¹ := by rw [hM]; group
    rw [e, Subgroup.coe_mul, Subgroup.coe_mul, hz', Subgroup.coe_inv]
    rw [← hwb]
    exact canonicalRep_conj_rootDiagUnit w b
  have key := centralizer_sup_eq_top_of_signs hMz hMz'
  have := congrArg (Subgroup.map (MulAut.conj M⁻¹).toMonoidHom) key
  rw [Subgroup.map_sup, conjSub_centralizer_singleton_g2d4,
    conjSub_centralizer_singleton_g2d4,
    Subgroup.map_top_of_surjective _ (MulAut.conj M⁻¹).surjective] at this
  have e1 : M⁻¹ * (M * z * M⁻¹) * M⁻¹⁻¹ = z := by group
  have e2 : M⁻¹ * (M * z' * M⁻¹) * M⁻¹⁻¹ = z' := by group
  rwa [e1, e2] at this

end Model

section Wrapper

variable {p e : ℕ} [Fact p.Prime]

theorem neg_one_ne_one_of_galoisField_odd (hp2 : p ≠ 2) (he : e ≠ 0) :
    (-1 : (GaloisField p e)ˣ) ≠ 1 := by
  have hodd : Odd (Nat.card (GaloisField p e)) := by
    rw [GaloisField.card p e he]
    exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  have hK2 : ringChar (GaloisField p e) ≠ 2 :=
    CFSG.ClassicalInvolution.Balance.Bootstrap.ringChar_ne_two_of_odd_nat_card hodd
  intro h
  exact Ring.neg_one_ne_one_of_char_ne_two hK2 (by simpa using congrArg Units.val h)

theorem centralizer_sup_eq_top_of_toralPair_model (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .G2 0 p e) {z z' : (modelUniv .G2 0 p e Fact.out).K}
    (h : ToralPair (F := GaloisField p e) z z') :
    Subgroup.centralizer ({z} : Set (modelUniv .G2 0 p e Fact.out).K) ⊔
      Subgroup.centralizer ({z'} : Set (modelUniv .G2 0 p e Fact.out).K) = ⊤ :=
  centralizer_sup_eq_top_of_toralPair
    (neg_one_ne_one_of_galoisField_odd hp2 (by have := hadm.2.1; omega)) h

@[expose] def G2NonToralGenerate (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ e : ℕ, StatedLieAdmissible .G2 0 p e → p ≠ 2 → 5 ≤ p ^ e →
    ∀ z z' : (modelUniv .G2 0 p e Fact.out).K, z * z = 1 → z' * z' = 1 → z ≠ 1 → z' ≠ 1 →
      z ≠ z' → z * z' = z' * z → ¬ ToralPair (F := GaloisField p e) z z' →
        Subgroup.centralizer ({z} : Set (modelUniv .G2 0 p e Fact.out).K) ⊔
          Subgroup.centralizer ({z'} : Set (modelUniv .G2 0 p e Fact.out).K) = ⊤

theorem g2CentralizersGenerate_of_nonToral (hNT : G2NonToralGenerate p) (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ e) (hadm : StatedLieAdmissible .G2 0 p e) :
    ∀ z z' : (modelUniv .G2 0 p e Fact.out).K, z * z = 1 → z' * z' = 1 → z ≠ 1 → z' ≠ 1 →
      z ≠ z' → z * z' = z' * z →
        Subgroup.centralizer ({z} : Set (modelUniv .G2 0 p e Fact.out).K) ⊔
          Subgroup.centralizer ({z'} : Set (modelUniv .G2 0 p e Fact.out).K) = ⊤ := by
  intro z z' hz hz' hz1 hz1' hne hcomm
  by_cases hT : ToralPair (F := GaloisField p e) z z'
  · exact centralizer_sup_eq_top_of_toralPair_model hp2 hadm hT
  · exact hNT e hadm hp2 hq z z' hz hz' hz1 hz1' hne hcomm hT

end Wrapper

end CFSG.ClassicalInvolution.G2D4Models
