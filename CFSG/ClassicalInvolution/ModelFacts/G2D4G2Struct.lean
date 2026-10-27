module

public import CFSG.ClassicalInvolution.ModelFacts.G2D4G2TorusGen

public noncomputable section

namespace CFSG.ClassicalInvolution.G2D4Models

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ClassicalInvolution.Balance.Bootstrap Matrix
open scoped MatrixGroups

section Lattice

theorem sum_univ_g2 (f : Fin Tag.G2.rank → ℤ) : ∑ i, f i = f g2i0 + f g2i1 :=
  Fin.sum_univ_two f

theorem g2_cartan_00 : Tag.G2.cartan g2i0 g2i0 = 2 := by decide

theorem g2_cartan_01 : Tag.G2.cartan g2i0 g2i1 = -1 := by decide

theorem g2_cartan_10 : Tag.G2.cartan g2i1 g2i0 = -3 := by decide

theorem g2_cartan_11 : Tag.G2.cartan g2i1 g2i1 = 2 := by decide

@[expose] def g2vec (a b : ℤ) : Fin Tag.G2.rank → ℤ := ![a, b]

theorem g2vec_0 (a b : ℤ) : g2vec a b g2i0 = a := rfl

theorem g2vec_1 (a b : ℤ) : g2vec a b g2i1 = b := rfl

theorem g2vec_ext {v w : Fin Tag.G2.rank → ℤ} (h0 : v g2i0 = w g2i0) (h1 : v g2i1 = w g2i1) :
    v = w := g2_funext h0 h1

theorem g2vec_neg (a b : ℤ) : -(g2vec a b) = g2vec (-a) (-b) :=
  g2vec_ext (by simp [g2vec_0]) (by simp [g2vec_1])

theorem g2_s0_smul (v : Fin Tag.G2.rank → ℤ) :
    simple Tag.G2 g2i0 • v = g2vec (-(v g2i0) + v g2i1) (v g2i1) := by
  rw [simple_smul, reflect]
  refine g2vec_ext ?_ ?_
  · rw [g2vec_0]
    simp [sum_univ_g2, g2_cartan_00, g2_cartan_01]
    ring
  · rw [g2vec_1]
    simp [sum_univ_g2, g2_cartan_00, g2_cartan_01]

theorem g2_s1_smul (v : Fin Tag.G2.rank → ℤ) :
    simple Tag.G2 g2i1 • v = g2vec (v g2i0) (3 * v g2i0 - v g2i1) := by
  rw [simple_smul, reflect]
  refine g2vec_ext ?_ ?_
  · rw [g2vec_0]
    simp [sum_univ_g2, g2_cartan_10, g2_cartan_11]
  · rw [g2vec_1]
    simp [sum_univ_g2, g2_cartan_10, g2_cartan_11]
    ring

theorem g2_single_0 : (Pi.single g2i0 1 : Fin Tag.G2.rank → ℤ) = g2vec 1 0 :=
  g2vec_ext (by simp [g2vec_0]) (Pi.single_eq_of_ne (show g2i1 ≠ g2i0 by decide) _)

theorem g2_single_1 : (Pi.single g2i1 1 : Fin Tag.G2.rank → ℤ) = g2vec 0 1 :=
  g2vec_ext (Pi.single_eq_of_ne (show g2i0 ≠ g2i1 by decide) _) (by simp [g2vec_1])

@[expose] def g2WeylU : WeylGroup Tag.G2 := simple Tag.G2 g2i0 * simple Tag.G2 g2i1

@[expose] def g2OmegaBeta : WeylGroup Tag.G2 := g2WeylU * simple Tag.G2 g2i0 * g2WeylU⁻¹

theorem g2WeylU_smul_single : g2WeylU • (Pi.single g2i0 1 : Fin Tag.G2.rank → ℤ) = g2vec 2 3 := by
  rw [g2WeylU, mul_smul, g2_single_0, g2_s1_smul, g2_s0_smul]
  simp [g2vec_0, g2vec_1]

theorem g2WeylU_inv : g2WeylU⁻¹ = simple Tag.G2 g2i1 * simple Tag.G2 g2i0 := by
  rw [g2WeylU, _root_.mul_inv_rev, simple_inv_eq', simple_inv_eq']

theorem g2OmegaBeta_smul (v : Fin Tag.G2.rank → ℤ) :
    g2OmegaBeta • v = g2vec (-(v g2i0)) (-3 * v g2i0 + v g2i1) := by
  rw [g2OmegaBeta, g2WeylU_inv, g2WeylU]
  simp only [mul_smul, g2_s0_smul, g2_s1_smul, g2vec_0, g2vec_1]
  refine g2vec_ext ?_ ?_ <;> simp [g2vec_0, g2vec_1] <;> ring

theorem g2_weyl_ext {w w' : WeylGroup Tag.G2} (hα : w • g2vec 0 1 = w' • g2vec 0 1)
    (hβ : w • g2vec 2 3 = w' • g2vec 2 3) : w = w' := by
  refine ext_single fun i => ?_
  fin_cases i
  · show w • (Pi.single g2i0 1 : Fin Tag.G2.rank → ℤ) =
      w' • (Pi.single g2i0 1 : Fin Tag.G2.rank → ℤ)
    have hsplit : (2 : ℤ) • (Pi.single g2i0 1 : Fin Tag.G2.rank → ℤ) =
        g2vec 2 3 - (3 : ℤ) • g2vec 0 1 := by
      refine g2vec_ext ?_ ?_
      · simp [g2vec_0, g2_single_0]
      · simp [g2vec_1, g2_single_0]
    have h2 : (2 : ℤ) • (w • (Pi.single g2i0 1 : Fin Tag.G2.rank → ℤ)) =
        (2 : ℤ) • (w' • (Pi.single g2i0 1 : Fin Tag.G2.rank → ℤ)) := by
      rw [smul_comm (2 : ℤ) w, smul_comm (2 : ℤ) w', hsplit, smul_sub, smul_sub,
        smul_comm w (3 : ℤ), hα, hβ, smul_comm w' (3 : ℤ)]
    refine g2vec_ext ?_ ?_
    · have := congrFun h2 g2i0
      simp at this
      omega
    · have := congrFun h2 g2i1
      simp at this
      omega
  · exact g2_single_1 ▸ hα

end Lattice

section Stab

variable {F : Type} [Field F] [Finite F]

theorem g2_toral_data_a1 (hodd : Odd (Nat.card F)) {a : Fin Tag.G2.rank → Fˣ}
    (ha : a = ![-1, 1]) :
    (∀ i, a i = 1 ∨ a i = -1) ∧ a ≠ 1 ∧
      rootCharKernel a = {g2vec 0 1, -g2vec 0 1, g2vec 2 3, -g2vec 2 3} ∧
      rootSpan Tag.G2 F (rootCharKernel a) =
        rootPair Tag.G2 F (g2vec 0 1) ⊔ rootPair Tag.G2 F (g2vec 2 3) ∧
      ⁅rootPair Tag.G2 F (g2vec 0 1), rootPair Tag.G2 F (g2vec 2 3)⁆ = ⊥ ∧
      iform (g2vec 0 1) (g2vec 0 1) ≠ iform (g2vec 2 3) (g2vec 2 3) := by
  have hK2 : ringChar F ≠ 2 := ringChar_ne_two_of_odd_nat_card hodd
  have hne1 : (-1 : Fˣ) ≠ 1 := fun h =>
    Ring.neg_one_ne_one_of_char_ne_two hK2 (by simpa using congrArg Units.val h)
  have ha0 : a g2i0 = -1 := by rw [ha]; rfl
  have ha1 : a g2i1 = 1 := by rw [ha]; rfl
  have hasq : ∀ i, a i = 1 ∨ a i = -1 := by
    intro i; fin_cases i
    · exact Or.inr ha0
    · exact Or.inl ha1
  have hane : a ≠ 1 := by
    intro h
    have := congrFun h g2i0
    rw [ha0] at this
    exact hne1 this
  obtain ⟨α, β, hcases, hker, hspan, hcomm, -⟩ := g2_toral_data hodd hasq hane
  have hαβ : α = ![0, 1] ∧ β = ![2, 3] := by
    rcases hcases with ⟨-, h1, h2⟩ | ⟨h, -, -⟩ | ⟨h, -, -⟩
    · exact ⟨h1, h2⟩
    · exfalso
      have := congrFun (ha.symm.trans h) g2i0
      exact hne1 this
    · exfalso
      have := congrFun (ha.symm.trans h) g2i1
      exact hne1 this.symm
  obtain ⟨hαe, hβe⟩ := hαβ
  have hlen := iform_ne_g2 (K := F) hcases
  subst hαe hβe
  exact ⟨hasq, hane, hker, hspan, hcomm, hlen⟩

theorem g2_stabilizer_cases (hodd : Odd (Nat.card F))
    {a : Fin Tag.G2.rank → Fˣ} (ha : a = ![-1, 1]) {w : WeylGroup Tag.G2}
    (hw : w ∈ rootCharStabilizer (τ := Tag.G2) (K := F) a) :
    w = 1 ∨ w = simple Tag.G2 g2i1 ∨ w = g2OmegaBeta ∨
      w = simple Tag.G2 g2i1 * g2OmegaBeta := by
  obtain ⟨-, -, hker, -, -, hlen⟩ := g2_toral_data_a1 (F := F) hodd ha
  have hαk : g2vec 0 1 ∈ rootCharKernel a := by rw [hker]; simp
  have hβk : g2vec 2 3 ∈ rootCharKernel a := by rw [hker]; simp
  have hsmul : ∀ γ ∈ rootCharKernel a, w • γ ∈ rootCharKernel a := fun γ hγ =>
    ⟨IsRoot.smul hγ.1 w, by rw [hw γ]; exact hγ.2⟩
  have hmem : ∀ γ, γ ∈ rootCharKernel a → γ = g2vec 0 1 ∨ γ = -g2vec 0 1 ∨ γ = g2vec 2 3 ∨
      γ = -g2vec 2 3 := by
    intro γ hγ
    rw [hker] at hγ
    simpa using hγ
  have hcα : w • g2vec 0 1 = g2vec 0 1 ∨ w • g2vec 0 1 = -g2vec 0 1 :=
    eq_or_eq_neg_of_iform_eq hlen (Or.inl rfl) (hmem _ (hsmul _ hαk))
      (iform_smul w (g2vec 0 1) (g2vec 0 1))
  have hcβ : w • g2vec 2 3 = g2vec 2 3 ∨ w • g2vec 2 3 = -g2vec 2 3 :=
    eq_or_eq_neg_of_iform_eq hlen (Or.inr (Or.inr (Or.inl rfl))) (hmem _ (hsmul _ hβk))
      (iform_smul w (g2vec 2 3) (g2vec 2 3))
  have hs1α : simple Tag.G2 g2i1 • g2vec 0 1 = -g2vec 0 1 := by
    rw [g2_s1_smul, g2vec_neg]; simp [g2vec_0, g2vec_1]
  have hs1β : simple Tag.G2 g2i1 • g2vec 2 3 = g2vec 2 3 := by
    rw [g2_s1_smul]; simp [g2vec_0, g2vec_1]
  have hωα : g2OmegaBeta • g2vec 0 1 = g2vec 0 1 := by
    rw [g2OmegaBeta_smul]; simp [g2vec_0, g2vec_1]
  have hωβ : g2OmegaBeta • g2vec 2 3 = -g2vec 2 3 := by
    rw [g2OmegaBeta_smul, g2vec_neg]; simp [g2vec_0, g2vec_1]
  rcases hcα with h1 | h1 <;> rcases hcβ with h2 | h2
  · exact Or.inl (g2_weyl_ext (by rw [one_smul]; exact h1) (by rw [one_smul]; exact h2))
  · exact Or.inr (Or.inr (Or.inl (g2_weyl_ext (by rw [hωα]; exact h1)
      (by rw [hωβ]; exact h2))))
  · exact Or.inr (Or.inl (g2_weyl_ext (by rw [hs1α]; exact h1) (by rw [hs1β]; exact h2)))
  · refine Or.inr (Or.inr (Or.inr (g2_weyl_ext ?_ ?_)))
    · rw [mul_smul, hωα, hs1α]; exact h1
    · rw [mul_smul, hωβ, smul_neg, hs1β]; exact h2

end Stab

section Lines

variable {τ : Tag} {K : Type} [Field K]

theorem rootChart_WSL_apply (w : WeylGroup τ) (i : Fin τ.rank) :
    rootChart τ K w i WSL = canonicalRep (coxeterSystem τ) K w * weylElt τ K i 1 *
      (canonicalRep (coxeterSystem τ) K w)⁻¹ := by
  rw [rootChart_apply, simpleRootSL2_WSL]

theorem rootChart_WSL_mapsRootLines (w : WeylGroup τ) (i : Fin τ.rank) :
    MapsRootLines (rootChart τ K w i WSL) (w * simple τ i * w⁻¹) := by
  rw [rootChart_WSL_apply]
  exact ((mapsRootLines_canonicalRep w).mul (mapsRootLines_weylElt i)).mul
    (mapsRootLines_canonicalRep w).inv

theorem weylElt_mem_torusWeylCosets (i : Fin τ.rank) :
    weylElt τ K i 1 ∈ torusWeylCosets τ K :=
  ⟨simple τ i, 1, Subgroup.one_mem _, by rw [canonicalRep_simple, one_mul]⟩

theorem canonicalRep_mem_torusWeylCosets (w : WeylGroup τ) :
    canonicalRep (coxeterSystem τ) K w ∈ torusWeylCosets τ K :=
  ⟨w, 1, Subgroup.one_mem _, by rw [one_mul]⟩

theorem rootChart_WSL_mem_torusWeylCosets (w : WeylGroup τ) (i : Fin τ.rank) :
    rootChart τ K w i WSL ∈ torusWeylCosets τ K := by
  rw [rootChart_WSL_apply]
  exact mul_mem (mul_mem (canonicalRep_mem_torusWeylCosets w) (weylElt_mem_torusWeylCosets i))
    (inv_mem (canonicalRep_mem_torusWeylCosets w))

theorem exists_torus_mul_canonicalRep {g : ModGL τ K} (hg : g ∈ torusWeylCosets τ K)
    {w : WeylGroup τ} (hmaps : MapsRootLines g w) :
    ∃ k ∈ torusGroup τ K, g = k * canonicalRep (coxeterSystem τ) K w := by
  obtain ⟨w', k, hk, rfl⟩ := hg
  have h1 : MapsRootLines (k * canonicalRep (coxeterSystem τ) K w') w' := by
    simpa using (mapsRootLines_of_mem_torusGroup hk).mul (mapsRootLines_canonicalRep w')
  have h2 := h1.unique hmaps
  subst h2
  exact ⟨k, hk, rfl⟩

end Lines

section Charts

variable {τ : Tag} {K : Type} [Field K]

theorem torus_conj_chart {t : ModGL τ K} (ht : t ∈ torusGroup τ K) (w : WeylGroup τ)
    (i : Fin τ.rank) (A : SL2 K) : ∃ A' : SL2 K, t * rootChart τ K w i A * t⁻¹ =
      rootChart τ K w i A' := by
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  exact ⟨_, rootDiagUnit_conj_rootChart w i b A⟩

end Charts

section ChartsG2

abbrev g2ChartA (F : Type) [Field F] : SL2 F →* ModGL Tag.G2 F :=
  rootChart Tag.G2 F 1 g2i1

abbrev g2ChartB (F : Type) [Field F] : SL2 F →* ModGL Tag.G2 F :=
  rootChart Tag.G2 F g2WeylU g2i0

variable {F : Type} [Field F]

theorem g2ChartA_range : (g2ChartA F).range = rootPair Tag.G2 F (g2vec 0 1) :=
  rootChart_range (by rw [one_smul, g2_single_1])

theorem g2ChartB_range : (g2ChartB F).range = rootPair Tag.G2 F (g2vec 2 3) :=
  rootChart_range g2WeylU_smul_single

theorem g2ChartA_injective [Finite F] (hodd : Odd (Nat.card F)) : Function.Injective (g2ChartA F) :=
  rootChart_injective (ringChar_ne_two_of_odd_nat_card hodd) 1 g2i1

theorem g2ChartB_injective [Finite F] (hodd : Odd (Nat.card F)) : Function.Injective (g2ChartB F) :=
  rootChart_injective (ringChar_ne_two_of_odd_nat_card hodd) g2WeylU g2i0

theorem g2ChartA_comm_g2ChartB [Finite F] (hodd : Odd (Nat.card F)) (A B : SL2 F) :
    g2ChartA F A * g2ChartB F B = g2ChartB F B * g2ChartA F A := by
  obtain ⟨a, ha⟩ : ∃ a : Fin Tag.G2.rank → Fˣ, a = ![-1, 1] := ⟨_, rfl⟩
  obtain ⟨-, -, -, -, hcomm, -⟩ := g2_toral_data_a1 (F := F) hodd ha
  have hA : g2ChartA F A ∈ rootPair Tag.G2 F (g2vec 0 1) := by
    rw [← g2ChartA_range]; exact ⟨A, rfl⟩
  have hB : g2ChartB F B ∈ rootPair Tag.G2 F (g2vec 2 3) := by
    rw [← g2ChartB_range]; exact ⟨B, rfl⟩
  have h := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm hA
  exact (Subgroup.mem_centralizer_iff.mp h _ hB).symm

theorem g2ChartA_mem (A : SL2 F) : g2ChartA F A ∈ adjointGroup Tag.G2 F := by
  change rootChart Tag.G2 F 1 g2i1 A ∈ adjointGroup Tag.G2 F
  rw [rootChart_one]; exact simpleRootSL2_mem_adjointGroup g2i1 A

theorem g2ChartB_mem (A : SL2 F) : g2ChartB F A ∈ adjointGroup Tag.G2 F := by
  have h : g2ChartB F A ∈ (g2ChartB F).range := ⟨A, rfl⟩
  rw [g2ChartB_range] at h
  exact sup_le (rootSubgroup_le_adjointGroup _) (rootSubgroup_le_adjointGroup _) h

end ChartsG2


section Decomp

variable {F : Type} [Field F] [Finite F]

theorem canonicalRep_mem_sup (hodd : Odd (Nat.card F)) {a : Fin Tag.G2.rank → Fˣ}
    (ha : a = ![-1, 1]) {w : WeylGroup Tag.G2}
    (hw : w ∈ rootCharStabilizer (τ := Tag.G2) (K := F) a) :
    canonicalRep (coxeterSystem Tag.G2) F w ∈
      torusGroup Tag.G2 F ⊔ (g2ChartA F).range ⊔ (g2ChartB F).range := by
  set S := torusGroup Tag.G2 F ⊔ (g2ChartA F).range ⊔ (g2ChartB F).range with hS
  have hTS : torusGroup Tag.G2 F ≤ S := le_sup_left.trans le_sup_left
  have hAS : (g2ChartA F).range ≤ S := le_sup_right.trans le_sup_left
  have hBS : (g2ChartB F).range ≤ S := le_sup_right
  have key : ∀ g ∈ torusWeylCosets Tag.G2 F, g ∈ S → ∀ w' : WeylGroup Tag.G2,
      MapsRootLines g w' → canonicalRep (coxeterSystem Tag.G2) F w' ∈ S := by
    intro g hg hgS w' hmaps
    obtain ⟨k, hk, hgk⟩ := exists_torus_mul_canonicalRep hg hmaps
    have : canonicalRep (coxeterSystem Tag.G2) F w' = k⁻¹ * g := by rw [hgk]; group
    rw [this]
    exact S.mul_mem (S.inv_mem (hTS hk)) hgS
  have hmA : MapsRootLines (g2ChartA F WSL) (simple Tag.G2 g2i1) := by
    have := rootChart_WSL_mapsRootLines (K := F) (1 : WeylGroup Tag.G2) g2i1
    simpa using this
  have hmB : MapsRootLines (g2ChartB F WSL) g2OmegaBeta :=
    rootChart_WSL_mapsRootLines (K := F) g2WeylU g2i0
  have hcA : g2ChartA F WSL ∈ torusWeylCosets Tag.G2 F :=
    rootChart_WSL_mem_torusWeylCosets (K := F) 1 g2i1
  have hcB : g2ChartB F WSL ∈ torusWeylCosets Tag.G2 F :=
    rootChart_WSL_mem_torusWeylCosets (K := F) g2WeylU g2i0
  rcases g2_stabilizer_cases hodd ha hw with rfl | rfl | rfl | rfl
  · rw [canonicalRep_one]; exact S.one_mem
  · exact key _ hcA (hAS ⟨WSL, rfl⟩) _ hmA
  · exact key _ hcB (hBS ⟨WSL, rfl⟩) _ hmB
  · exact key _ ((torusWeylCosets Tag.G2 F).mul_mem hcA hcB)
      (S.mul_mem (hAS ⟨WSL, rfl⟩) (hBS ⟨WSL, rfl⟩)) _ (hmA.mul hmB)

theorem toralCentralizer_le_sup (hodd : Odd (Nat.card F)) {a : Fin Tag.G2.rank → Fˣ}
    (ha : a = ![-1, 1]) :
    toralCentralizer Tag.G2 F a ≤
      torusGroup Tag.G2 F ⊔ (g2ChartA F).range ⊔ (g2ChartB F).range := by
  obtain ⟨-, -, -, hspan, -⟩ := g2_toral_data_a1 (F := F) hodd ha
  rw [(Chevalley_toral_centralizer_Bruhat_factors Tag.G2 F a).2.2.2]
  refine sup_le (sup_le (le_sup_left.trans le_sup_left) ?_) ?_
  · rw [hspan, ← g2ChartA_range, ← g2ChartB_range]
    exact sup_le (le_sup_right.trans le_sup_left) le_sup_right
  · rw [Subgroup.closure_le]
    rintro _ ⟨w, hw, rfl⟩
    exact canonicalRep_mem_sup hodd ha hw

end Decomp

section Prod

variable {F : Type} [Field F] [Finite F]

theorem toralCentralizer_le_prod (hodd : Odd (Nat.card F)) {a : Fin Tag.G2.rank → Fˣ}
    (ha : a = ![-1, 1]) {x : ModGL Tag.G2 F} (hx : x ∈ toralCentralizer Tag.G2 F a) :
    ∃ t ∈ torusGroup Tag.G2 F, ∃ A B : SL2 F, x = t * g2ChartA F A * g2ChartB F B := by
  have hcomm := g2ChartA_comm_g2ChartB (F := F) hodd
  have hconjA : ∀ t ∈ torusGroup Tag.G2 F, ∀ A : SL2 F, ∃ A' : SL2 F,
      g2ChartA F A * t = t * g2ChartA F A' := by
    intro t ht A
    obtain ⟨A', hA'⟩ := torus_conj_chart (inv_mem ht) 1 g2i1 A
    refine ⟨A', ?_⟩
    rw [inv_inv] at hA'
    change _ = t * rootChart Tag.G2 F 1 g2i1 A'
    rw [← hA']
    group
  have hconjB : ∀ t ∈ torusGroup Tag.G2 F, ∀ B : SL2 F, ∃ B' : SL2 F,
      g2ChartB F B * t = t * g2ChartB F B' := by
    intro t ht B
    obtain ⟨B', hB'⟩ := torus_conj_chart (inv_mem ht) g2WeylU g2i0 B
    refine ⟨B', ?_⟩
    rw [inv_inv] at hB'
    change _ = t * rootChart Tag.G2 F g2WeylU g2i0 B'
    rw [← hB']
    group
  let S₁ : Subgroup (ModGL Tag.G2 F) :=
    { carrier := {x | ∃ t ∈ torusGroup Tag.G2 F, ∃ A B : SL2 F,
        x = t * g2ChartA F A * g2ChartB F B}
      one_mem' := ⟨1, one_mem _, 1, 1, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨t₁, ht₁, A₁, B₁, rfl⟩ ⟨t₂, ht₂, A₂, B₂, rfl⟩
        obtain ⟨A₁', hA₁⟩ := hconjA t₂ ht₂ A₁
        obtain ⟨B₁', hB₁⟩ := hconjB t₂ ht₂ B₁
        refine ⟨t₁ * t₂, mul_mem ht₁ ht₂, A₁' * A₂, B₁' * B₂, ?_⟩
        calc t₁ * g2ChartA F A₁ * g2ChartB F B₁ * (t₂ * g2ChartA F A₂ * g2ChartB F B₂)
            = t₁ * (g2ChartA F A₁ * (g2ChartB F B₁ * t₂)) * g2ChartA F A₂ * g2ChartB F B₂ := by
              group
          _ = t₁ * (g2ChartA F A₁ * (t₂ * g2ChartB F B₁')) * g2ChartA F A₂ *
                g2ChartB F B₂ := by rw [hB₁]
          _ = t₁ * ((g2ChartA F A₁ * t₂) * g2ChartB F B₁') * g2ChartA F A₂ *
                g2ChartB F B₂ := by group
          _ = t₁ * ((t₂ * g2ChartA F A₁') * g2ChartB F B₁') * g2ChartA F A₂ *
                g2ChartB F B₂ := by rw [hA₁]
          _ = t₁ * t₂ * g2ChartA F A₁' * (g2ChartB F B₁' * g2ChartA F A₂) * g2ChartB F B₂ := by
              group
          _ = t₁ * t₂ * g2ChartA F A₁' * (g2ChartA F A₂ * g2ChartB F B₁') * g2ChartB F B₂ := by
              rw [← hcomm A₂ B₁']
          _ = t₁ * t₂ * g2ChartA F (A₁' * A₂) * g2ChartB F (B₁' * B₂) := by
              rw [map_mul, map_mul]; group
      inv_mem' := by
        rintro _ ⟨t, ht, A, B, rfl⟩
        obtain ⟨A', hA'⟩ := hconjA t⁻¹ (inv_mem ht) A⁻¹
        obtain ⟨B', hB'⟩ := hconjB t⁻¹ (inv_mem ht) B⁻¹
        refine ⟨t⁻¹, inv_mem ht, A', B', ?_⟩
        calc (t * g2ChartA F A * g2ChartB F B)⁻¹
            = g2ChartB F B⁻¹ * g2ChartA F A⁻¹ * t⁻¹ := by
              simp only [map_inv]; group
          _ = g2ChartA F A⁻¹ * g2ChartB F B⁻¹ * t⁻¹ := by rw [← hcomm A⁻¹ B⁻¹]
          _ = g2ChartA F A⁻¹ * (g2ChartB F B⁻¹ * t⁻¹) := by group
          _ = g2ChartA F A⁻¹ * (t⁻¹ * g2ChartB F B') := by rw [hB']
          _ = (g2ChartA F A⁻¹ * t⁻¹) * g2ChartB F B' := by group
          _ = t⁻¹ * g2ChartA F A' * g2ChartB F B' := by rw [hA'] }
  have hT : torusGroup Tag.G2 F ≤ S₁ := fun t ht => ⟨t, ht, 1, 1, by simp⟩
  have hA : (g2ChartA F).range ≤ S₁ := by
    rintro _ ⟨A, rfl⟩
    exact ⟨1, one_mem _, A, 1, by simp⟩
  have hB : (g2ChartB F).range ≤ S₁ := by
    rintro _ ⟨B, rfl⟩
    exact ⟨1, one_mem _, 1, B, by simp⟩
  exact (sup_le (sup_le hT hA) hB) (toralCentralizer_le_sup hodd ha hx)

end Prod

end CFSG.ClassicalInvolution.G2D4Models
