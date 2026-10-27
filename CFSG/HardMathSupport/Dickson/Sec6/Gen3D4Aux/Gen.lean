module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevOuterD48Psi
public import CFSG.Quasithin.Recognition.CertD4BridgeGen

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.Gen3D4

open CFSG.Quasithin CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.Ree
open CFSG.Open (quasithinRootElt quasithinD4Root)

section Natural

variable (k : Type) [Field k]

@[expose] def g4Gens : Set (Matrix (Fin 8) (Fin 8) k) :=
  {M | ∃ (a : k) (s : Bool), M = quasithinRootElt (quasithinD4Root 0 s) a *
      quasithinRootElt (quasithinD4Root 2 s) (a ^ 4) *
      quasithinRootElt (quasithinD4Root 3 s) (a ^ 16)} ∪
  {M | ∃ (c : k) (s : Bool), c ^ 4 = c ∧ M = quasithinRootElt (quasithinD4Root 1 s) c}

@[expose] def g4Group : Subgroup (GL (Fin 8) k) :=
  Subgroup.closure {A | (A : Matrix (Fin 8) (Fin 8) k) ∈ g4Gens k}

end Natural

section Gen

variable {k : Type} [Field k] [CharP k 2]

theorem g4_mem_outer
    (i₀ i₁ i₃ : Fin Tag.D4.rank) (h₀ : i₀.val = 0) (h₁ : i₁.val = 1)
    (h₃ : i₃.val = 3) (s : Bool) (a : k) :
    d4bNat k i₀ s a * d4bNat k i₁ s (a ^ 4) * d4bNat k i₃ s (a ^ 16) ∈ g4Group k := by
  refine Subgroup.subset_closure (Or.inl ⟨a, s, ?_⟩)
  rw [Units.val_mul, Units.val_mul]
  exact d4bUm_outer i₀ i₁ i₃ h₀ h₁ h₃ s a _ _

theorem g4_mem_mid
    (i : Fin Tag.D4.rank) (hi : i.val = 2) (s : Bool) {c : k} (hc : c ^ 4 = c) :
    d4bNat k i s c ∈ g4Group k := by
  refine Subgroup.subset_closure (Or.inr ⟨c, s, hc, ?_⟩)
  exact d4bUm_mid i hi s c

end Gen

section GenΨ

variable {k : Type} [Field k] [CharP k 2] [Finite k] (hk : Nat.card k = 4 ^ 3)

variable (σ : k →+* k) (hσ : ∀ c, σ c = c ^ 4)

omit [CharP k 2] in
include hk hσ in
theorem g4_sigma3 (c : k) : σ (σ (σ c)) = c :=
  sigma_three_of_card (q := 4) hk hσ c

include hk hσ in
theorem g4_base_long
    {s : ℤ} (hs : s = 1 ∨ s = -1) {g : adjointGroup d4 k}
    (hg : g ∈ twistedRootSubgroupD4 σ (s • Pi.single (ng 0) 1)) :
    CFSG.AGLEmbedding.ChevOuterD48.d48bΨ' (k := k) g ∈ g4Group k := by
  have hα₀ : IsRoot d4 (s • Pi.single (nd 2) 1) := isRoot_smul_single hs (nd 2)
  have hp : proj (s • Pi.single (nd 2) 1) = s • Pi.single (ng 0) 1 := by
    rw [proj_smul_single hs]
    rfl
  have hfix : rho (s • Pi.single (nd 2) 1) = s • Pi.single (nd 2) 1 := by
    rw [rho_smul_single, rhoPerm_two]
  obtain ⟨c, hc, rfl⟩ :=
    (mem_twistedRootSubgroupD4_iff_of_fixed (σ := σ) (g4_sigma3 hk σ hσ) hα₀ hp hfix g).1 hg
  have h4 : c ^ 4 = c := (hσ c).symm.trans hc
  rcases hs with rfl | rfl
  · rw [one_smul, CFSG.AGLEmbedding.ChevOuterD48.d48bΨ_xPar_pos]
    exact g4_mem_mid (nd 2) rfl true h4
  · rw [neg_one_smul, CFSG.AGLEmbedding.ChevOuterD48.d48bΨ_xPar_neg]
    exact g4_mem_mid (nd 2) rfl false h4

include hk hσ in
theorem g4_base_short
    {s : ℤ} (hs : s = 1 ∨ s = -1) {g : adjointGroup d4 k}
    (hg : g ∈ twistedRootSubgroupD4 σ (s • Pi.single (ng 1) 1)) :
    CFSG.AGLEmbedding.ChevOuterD48.d48bΨ' (k := k) g ∈ g4Group k := by
  have hα₀ : IsRoot d4 (s • Pi.single (nd 0) 1) := isRoot_smul_single hs (nd 0)
  have hp : proj (s • Pi.single (nd 0) 1) = s • Pi.single (ng 1) 1 := by
    rw [proj_smul_single hs]
    rfl
  have hne : rho (s • Pi.single (nd 0) 1) ≠ s • Pi.single (nd 0) 1 :=
    rho_smul_single_ne hs (by decide)
  obtain ⟨c, rfl⟩ :=
    (mem_twistedRootSubgroupD4_iff_of_orbit (σ := σ) (g4_sigma3 hk σ hσ) hα₀ hp hne g).1 hg
  have e1 : σ c = c ^ 4 := hσ c
  have e2 : σ (σ c) = c ^ 16 := by rw [e1, hσ, ← pow_mul]
  rw [xOrbit_smul_single σ hs, e2, e1]
  rcases hs with rfl | rfl
  · simp only [xOuter, one_smul, map_mul, CFSG.AGLEmbedding.ChevOuterD48.d48bΨ_xPar_pos]
    exact g4_mem_outer (nd 0) (nd 1) (nd 3) rfl rfl rfl true c
  · simp only [xOuter, neg_one_smul, map_mul, CFSG.AGLEmbedding.ChevOuterD48.d48bΨ_xPar_neg]
    exact g4_mem_outer (nd 0) (nd 1) (nd 3) rfl rfl rfl false c

include hk hσ in
theorem g4_twistedGroup_le :
    twistedGroup σ ≤ (g4Group k).comap (CFSG.AGLEmbedding.ChevOuterD48.d48bΨ' (k := k)) := by
  set R : Subgroup (adjointGroup d4 k) := (g4Group k).comap (CFSG.AGLEmbedding.ChevOuterD48.d48bΨ' (k := k)) with hR
  have base : ∀ (j : Fin (Tag.rank .G2)) {s : ℤ}, (s = 1 ∨ s = -1) →
      twistedRootSubgroupD4 σ (s • Pi.single j 1) ≤ R := by
    intro j s hs g hg
    rw [hR, Subgroup.mem_comap]
    match j with
    | ⟨0, _⟩ => exact g4_base_long hk σ hσ hs hg
    | ⟨1, _⟩ => exact g4_base_short hk σ hσ hs hg
  have base₁ : ∀ j : Fin (Tag.rank .G2), twistedRootSubgroupD4 σ (Pi.single j 1) ≤ R := by
    intro j
    have := base j (Or.inl rfl)
    rwa [one_smul] at this
  have base₂ : ∀ j : Fin (Tag.rank .G2), twistedRootSubgroupD4 σ (-Pi.single j 1) ≤ R := by
    intro j
    have := base j (Or.inr rfl)
    rwa [neg_one_smul] at this
  have hn : ∀ i : Fin (Tag.rank .G2), ((nHat σ i : twistedGroup σ) : adjointGroup d4 k) ∈ R := by
    intro i
    have hle : CFSG.LieType.CurtisTits.rankOne (twistedRootGroup σ) i ≤
        R.subgroupOf (twistedGroup σ) := by
      refine sup_le (fun x hx => ?_) (fun x hx => ?_)
      · exact base₁ i ((mem_twistedRootGroup σ).1 hx)
      · exact base₂ i ((mem_twistedRootGroup σ).1 hx)
    exact hle (nHat_mem_rankOne σ i)
  have key : ∀ β, IsRoot .G2 β → twistedRootSubgroupD4 σ β ≤ R := by
    intro β hβ
    induction hβ with
    | basis j => exact base₁ j
    | reflect i hβ' ih =>
      intro g hg
      have hgΓ : g ∈ twistedGroup σ := twistedRootSubgroupD4_le_twistedGroup σ (hβ'.reflect i) hg
      have hx : (⟨g, hgΓ⟩ : twistedGroup σ) ∈ twistedRootGroup σ (reflect .G2 i _) :=
        (mem_twistedRootGroup σ).2 hg
      have h1 := nHat_conj_mem σ i (hβ'.reflect i) hx
      rw [reflect_reflect] at h1
      have h2 := ih ((mem_twistedRootGroup σ).1 h1)
      have h3 : (g : adjointGroup d4 k) =
          ((nHat σ i : twistedGroup σ) : adjointGroup d4 k)⁻¹ *
            (((nHat σ i : twistedGroup σ) : adjointGroup d4 k) * g *
              ((nHat σ i : twistedGroup σ) : adjointGroup d4 k)⁻¹) *
            ((nHat σ i : twistedGroup σ) : adjointGroup d4 k) := by group
      rw [h3]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (hn i)) h2) (hn i)
  exact iSup₂_le fun β hβ => key β hβ

include hk hσ in
theorem g4_G_le_map :
    g4Group k ≤ (twistedGroup σ).map (CFSG.AGLEmbedding.ChevOuterD48.d48bΨ' (k := k)) := by
  have hσ3 := g4_sigma3 hk σ hσ
  have hp : (1 : ℤ) = 1 ∨ (1 : ℤ) = -1 := Or.inl rfl
  have hn : (-1 : ℤ) = 1 ∨ (-1 : ℤ) = -1 := Or.inr rfl
  rw [g4Group, Subgroup.closure_le]
  rintro A (⟨a, s, hA⟩ | ⟨c, s, hc, hA⟩)
  · have e1 : σ a = a ^ 4 := hσ a
    have e2 : σ (σ a) = a ^ 16 := by rw [e1, hσ, ← pow_mul]
    cases s
    · refine ⟨xOuter (-1) a (σ a) (σ (σ a)), twistedRootSubgroupD4_le_twistedGroup σ
        (isRoot_smul_single_G2 hn (ng 1)) (xOuter_mem σ hn (hσ3 a)), ?_⟩
      apply Units.ext
      simp only [xOuter, neg_one_smul, map_mul, CFSG.AGLEmbedding.ChevOuterD48.d48bΨ_xPar_neg, Units.val_mul]
      rw [hA, e2, e1]
      exact d4bUm_outer (nd 0) (nd 1) (nd 3) rfl rfl rfl false a _ _
    · refine ⟨xOuter 1 a (σ a) (σ (σ a)), twistedRootSubgroupD4_le_twistedGroup σ
        (isRoot_smul_single_G2 hp (ng 1)) (xOuter_mem σ hp (hσ3 a)), ?_⟩
      apply Units.ext
      simp only [xOuter, one_smul, map_mul, CFSG.AGLEmbedding.ChevOuterD48.d48bΨ_xPar_pos, Units.val_mul]
      rw [hA, e2, e1]
      exact d4bUm_outer (nd 0) (nd 1) (nd 3) rfl rfl rfl true a _ _
  · have hσc : σ c = c := (hσ c).trans hc
    cases s
    · refine ⟨xPar (rootOperatorFamily d4) ((-1 : ℤ) • Pi.single (nd 2) 1) c,
        twistedRootSubgroupD4_le_twistedGroup σ (isRoot_smul_single_G2 hn (ng 0))
          (xPar_two_mem σ hn hσc), ?_⟩
      apply Units.ext
      rw [neg_one_smul, CFSG.AGLEmbedding.ChevOuterD48.d48bΨ_xPar_neg, hA]
      exact d4bUm_mid (nd 2) rfl false c
    · refine ⟨xPar (rootOperatorFamily d4) ((1 : ℤ) • Pi.single (nd 2) 1) c,
        twistedRootSubgroupD4_le_twistedGroup σ (isRoot_smul_single_G2 hp (ng 0))
          (xPar_two_mem σ hp hσc), ?_⟩
      apply Units.ext
      rw [one_smul, CFSG.AGLEmbedding.ChevOuterD48.d48bΨ_xPar_pos, hA]
      exact d4bUm_mid (nd 2) rfl true c

include hk hσ in
theorem g4_map_twistedGroup :
    (twistedGroup σ).map (CFSG.AGLEmbedding.ChevOuterD48.d48bΨ' (k := k)) = g4Group k :=
  le_antisymm (Subgroup.map_le_iff_le_comap.2 (g4_twistedGroup_le hk σ hσ))
    (g4_G_le_map hk σ hσ)

end GenΨ

end CFSG.HardMathSupport.Dickson.Sec6.Gen3D4
