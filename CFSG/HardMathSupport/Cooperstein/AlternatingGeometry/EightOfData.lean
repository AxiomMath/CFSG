module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.EightModel
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ExtensionPCore
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.PairModelCore
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.BarMNormalizer

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm CFSG.AGLEmbedding CFSG.QuasithinUnique

abbrev OmegaE (r s : ℕ) := (Fin r × Bool) ⊕ Fin s

abbrev AltE (r s : ℕ) := ↥(alternatingGroup (OmegaE r s))

@[expose] def pTildeEmb (r s : ℕ) : Subgroup (Perm (OmegaE r s)) :=
  (pTilde (Fin r) (Fin s)).map (Perm.sumCongrHom _ _)

theorem pTildeEmb_le_alt (r s : ℕ) : pTildeEmb r s ≤ alternatingGroup (OmegaE r s) := by
  rintro _ ⟨p, hp, rfl⟩
  rw [mem_alternatingGroup, Perm.sumCongrHom_apply, sign_sumCongr]
  exact hp.2

@[expose] def eightN (r s : ℕ) : Subgroup (AltE r s) :=
  (pTildeEmb r s).subgroupOf (alternatingGroup (OmegaE r s))

@[expose] noncomputable def eightEquiv (r s : ℕ) : ↥(eightN r s) ≃* ↥(pTilde (Fin r) (Fin s)) :=
  (Subgroup.subgroupOfEquivOfLe (pTildeEmb_le_alt r s)).trans
    (Subgroup.equivMapOfInjective (pTilde (Fin r) (Fin s)) (Perm.sumCongrHom _ _)
      Perm.sumCongrHom_injective).symm

theorem eightEquiv_spec {r s : ℕ} (x : ↥(eightN r s)) :
    Perm.sumCongr (eightEquiv r s x).1.1 (eightEquiv r s x).1.2 =
      ((x.1 : AltE r s) : Perm (OmegaE r s)) := by
  have h := congrArg Subtype.val
    ((Subgroup.equivMapOfInjective (pTilde (Fin r) (Fin s)) (Perm.sumCongrHom _ _)
      Perm.sumCongrHom_injective).apply_symm_apply
      (Subgroup.subgroupOfEquivOfLe (pTildeEmb_le_alt r s) x))
  exact h

variable {G : Type} [Group G]

@[expose] def EightBlockData (X S L : Subgroup G) (r s : ℕ) : Prop :=
  ∃ ψ : ↥(barM X L) ≃* AltE r s,
    ((barM X (Subgroup.normalizer (S : Set G) ⊓ L)).subgroupOf (barM X L)).map ψ.toMonoidHom =
      eightN r s ∧
    ∀ y ∈ barM X (Subgroup.normalizer (S : Set G) ⊓ Subgroup.normalizer (L : Set G)),
      ∃ σ₁ ∈ wStab (Fin r) Bool, ∃ σ₂ : Perm (Fin s), ∀ l l' : ↥(barM X L),
        (l' : ↥X ⧸ CFSG.pCore 2 ↥X) = y * l * y⁻¹ →
        ((ψ l' : AltE r s) : Perm (OmegaE r s)) =
          Perm.sumCongr σ₁ σ₂ * ((ψ l : AltE r s) : Perm (OmegaE r s)) *
            (Perm.sumCongr σ₁ σ₂)⁻¹

section Derivation

theorem eightAction_conj {ι Γ : Type*} [Fintype ι] [DecidableEq ι] [Fintype Γ] [DecidableEq Γ]
    {p p' : ↥(pTilde ι Γ)} {σ₁ : Perm (ι × Bool)} (hσ₁ : σ₁ ∈ wStab ι Bool) {σ₂ : Perm Γ}
    (h : p'.1 = (σ₁, σ₂) * p.1 * (σ₁, σ₂)⁻¹) :
    eightAction ι Γ p' =
      (wStabAction ι ⟨σ₁, hσ₁⟩ * (eightAction ι Γ p).1 * (wStabAction ι ⟨σ₁, hσ₁⟩)⁻¹,
        σ₂ * (eightAction ι Γ p).2 * σ₂⁻¹) := by
  have h1 : p'.1.1 = σ₁ * p.1.1 * σ₁⁻¹ := by
    have := congrArg Prod.fst h
    simpa using this
  have h2 : p'.1.2 = σ₂ * p.1.2 * σ₂⁻¹ := by
    have := congrArg Prod.snd h
    simpa using this
  refine Prod.ext ?_ ?_
  · have e : (⟨p'.1.1, p'.2.1⟩ : ↥(wStab ι Bool)) =
        ⟨σ₁, hσ₁⟩ * ⟨p.1.1, p.2.1⟩ * ⟨σ₁, hσ₁⟩⁻¹ := Subtype.ext h1
    show wStabAction ι ⟨p'.1.1, p'.2.1⟩ = _
    rw [e, map_mul, map_mul, map_inv]
    rfl
  · exact h2

theorem normalizer_of_conj {Q : Type*} [Group Q] {Kb F : Subgroup Q}
    (h : ∀ y ∈ Kb, ∀ z ∈ F, y * z * y⁻¹ ∈ F) : Kb ≤ Subgroup.normalizer (F : Set Q) := by
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro z
  refine ⟨fun hz => h y hy z hz, fun hz => ?_⟩
  have := h y⁻¹ (inv_mem hy) _ hz
  simpa [mul_assoc] using this

variable {X S L : Subgroup G}

theorem eightCore {r s : ℕ} (hr1 : 1 ≤ r) (hr : r = 1 ∨ r = 3 ∨ 5 ≤ r)
    (hs : s = 1 ∨ s = 3 ∨ 5 ≤ s) (D : EightBlockData X S L r s) :
    ∃ φ : (↥(barM X (Subgroup.normalizer (S : Set G) ⊓ L)) ⧸
        CFSG.pCore 2 ↥(barM X (Subgroup.normalizer (S : Set G) ⊓ L))) ≃*
          (Perm (Fin r) × Perm (Fin s)),
      barM X (Subgroup.normalizer (S : Set G) ⊓ Subgroup.normalizer (L : Set G)) ≤
        Subgroup.normalizer ((((MonoidHom.snd _ _).comp (φ.toMonoidHom.comp
          (QuotientGroup.mk' (CFSG.pCore 2 ↥(barM X (Subgroup.normalizer (S : Set G) ⊓ L)))))).ker.map
            (barM X (Subgroup.normalizer (S : Set G) ⊓ L)).subtype : Subgroup _) : Set _) ∧
      barM X (Subgroup.normalizer (S : Set G) ⊓ Subgroup.normalizer (L : Set G)) ≤
        Subgroup.normalizer ((((MonoidHom.fst _ _).comp (φ.toMonoidHom.comp
          (QuotientGroup.mk' (CFSG.pCore 2 ↥(barM X (Subgroup.normalizer (S : Set G) ⊓ L)))))).ker.map
            (barM X (Subgroup.normalizer (S : Set G) ⊓ L)).subtype : Subgroup _) : Set _) := by
  obtain ⟨ψ, hJ, hact⟩ := D
  set B : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X) :=
    barM X (Subgroup.normalizer (S : Set G) ⊓ L) with hB
  have hBC : B ≤ barM X L := barM_mono inf_le_right
  let Ψ : ↥B ≃* ↥(pTilde (Fin r) (Fin s)) :=
    (sectionEquiv hBC ψ (eightN r s) hJ).trans (eightEquiv r s)
  have hne : Nonempty (Fin r) := ⟨⟨0, by omega⟩⟩
  let ρ' : ↥B →* Perm (Fin r) × Perm (Fin s) := (eightAction (Fin r) (Fin s)).comp Ψ.toMonoidHom
  have hρs : Function.Surjective ρ' := eightAction_surjective.comp Ψ.surjective
  have hρk : IsPGroup 2 ρ'.ker := by
    rw [← MonoidHom.comap_ker]
    exact isPGroup_ker_eightAction.comap_of_injective _ Ψ.injective
  have hO2 : CFSG.pCore 2 (Perm (Fin r) × Perm (Fin s)) = ⊥ :=
    pCore_prod_eq_bot (pCore_perm_eq_bot (by omega)) (pCore_perm_eq_bot hs)
  let φ := quotientPCoreOfKer hO2 ρ' hρs hρk
  have hφ : ∀ b : ↥B, φ (QuotientGroup.mk b) = ρ' b := fun b => rfl
  have hspec : ∀ b : ↥B, Perm.sumCongr (Ψ b).1.1 (Ψ b).1.2 =
      ((ψ ⟨b.1, hBC b.2⟩ : AltE r s) : Perm (OmegaE r s)) := fun b =>
    eightEquiv_spec (sectionEquiv hBC ψ (eightN r s) hJ b)
  have claimA : ∀ y ∈ barM X (Subgroup.normalizer (S : Set G) ⊓ Subgroup.normalizer (L : Set G)),
      ∃ (π₁ : Perm (Fin r)) (σ₂ : Perm (Fin s)), ∀ b : ↥B, ∃ b' : ↥B,
        (b' : ↥X ⧸ CFSG.pCore 2 ↥X) = y * b * y⁻¹ ∧ (ρ' b').1 = π₁ * (ρ' b).1 * π₁⁻¹ ∧
          (ρ' b').2 = σ₂ * (ρ' b).2 * σ₂⁻¹ := by
    intro y hy
    obtain ⟨σ₁, hσ₁, σ₂, hσ⟩ := hact y hy
    refine ⟨wStabAction (Fin r) ⟨σ₁, hσ₁⟩, σ₂, fun b => ?_⟩
    obtain ⟨g, hg, hgy⟩ := (mem_barM y).1 hy
    obtain ⟨m, hm, hmb⟩ := (mem_barM b.1).1 b.2
    have hmem : y * b.1 * y⁻¹ ∈ B := by
      refine (mem_barM _).2 ⟨g * m * g⁻¹, ?_, ?_⟩
      · obtain ⟨hgS, hgL⟩ := Subgroup.mem_inf.1 hg
        obtain ⟨hmS, hmL⟩ := Subgroup.mem_inf.1 hm
        refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
        · exact mul_mem (mul_mem hgS hmS) (inv_mem hgS)
        · exact (Subgroup.mem_normalizer_iff.1 hgL m).1 hmL
      · rw [← hgy, ← hmb]; rfl
    refine ⟨⟨y * b.1 * y⁻¹, hmem⟩, rfl, ?_⟩
    have hl := hσ ⟨b.1, hBC b.2⟩ ⟨y * b.1 * y⁻¹, hBC hmem⟩ rfl
    rw [← hspec b, ← hspec ⟨y * b.1 * y⁻¹, hmem⟩] at hl
    have hl' : (Perm.sumCongrHom _ _) (Ψ ⟨y * b.1 * y⁻¹, hmem⟩).1 =
        (Perm.sumCongrHom _ _) ((σ₁, σ₂) * (Ψ b).1 * (σ₁, σ₂)⁻¹) := by
      rw [map_mul, map_mul, map_inv]
      exact hl
    have hp := Perm.sumCongrHom_injective hl'
    have := eightAction_conj (p := Ψ b) (p' := Ψ ⟨y * b.1 * y⁻¹, hmem⟩) hσ₁ (σ₂ := σ₂) hp
    refine ⟨?_, ?_⟩
    · exact congrArg Prod.fst this
    · exact congrArg Prod.snd this
  refine ⟨φ, ?_, ?_⟩
  · refine normalizer_of_conj fun y hy z hz => ?_
    obtain ⟨b, hb, rfl⟩ := hz
    obtain ⟨π₁, σ₂, hA⟩ := claimA y hy
    obtain ⟨b', hb'1, hb'2, hb'3⟩ := hA b
    have hb1 : (ρ' b).2 = 1 := by
      have := MonoidHom.mem_ker.1 hb
      simpa [hφ] using this
    refine ⟨b', MonoidHom.mem_ker.2 ?_, ?_⟩
    · show (φ (QuotientGroup.mk b')).2 = 1
      rw [hφ, hb'3, hb1]; simp
    · exact hb'1
  · refine normalizer_of_conj fun y hy z hz => ?_
    obtain ⟨b, hb, rfl⟩ := hz
    obtain ⟨π₁, σ₂, hA⟩ := claimA y hy
    obtain ⟨b', hb'1, hb'2, hb'3⟩ := hA b
    have hb1 : (ρ' b).1 = 1 := by
      have := MonoidHom.mem_ker.1 hb
      simpa [hφ] using this
    refine ⟨b', MonoidHom.mem_ker.2 ?_, ?_⟩
    · show (φ (QuotientGroup.mk b')).1 = 1
      rw [hφ, hb'2, hb1]; simp
    · exact hb'1

theorem nineThreeEight_of_eightBlockData {N r : ℕ} (hshort : IsShort2 L) (hN : Even N)
    (hr2 : 2 * r ≤ N) (hr1 : 1 ≤ r) (hr : r = 1 ∨ r = 3 ∨ 5 ≤ r) (hs : 6 ≤ N - 2 * r)
    (D : EightBlockData X S L r (N - 2 * r)) : NineThreeEight X S L := by
  obtain ⟨φ, h1, h2⟩ := eightCore hr1 hr (Or.inr (Or.inr (by omega))) D
  obtain ⟨ψ, -, -⟩ := D
  have e : OmegaE r (N - 2 * r) ≃ Fin N := Fintype.equivFinOfCardEq (by
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
    omega)
  exact ⟨hshort, N, r, hN, hr2, by omega, by omega, by omega, ⟨ψ.trans (Equiv.altCongrHom e)⟩,
    φ, h1, h2⟩

end Derivation

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
