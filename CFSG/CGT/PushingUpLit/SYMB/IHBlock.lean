module

public import CFSG.CGT.PushingUpLit.SYMB.IHInterface
public import CFSG.CGT.PushingUpLit.BHS6.SymAssembly

public section

namespace CFSG.CGT.PushingUpLit.SYMB

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
  CFSG.CGT.PushingUpLit.BHS7
open scoped commutatorElement

variable {Γ : Type} [Group Γ]

theorem seven_three_ih [Finite Γ] {G T L S : Subgroup Γ} (hG : CharTwo G) (hih : IHFor G)
    (hT : IsSylowTwoOf T G) (hL : L ∈ lSet G T) (hS : IsSylowTwoOf S L) :
    CharTwo L ∧ cStarIn L S ≠ L ∧ LocalCStarConcl L S := by
  obtain ⟨hLG, hBL, hLC⟩ := hL
  have hb0 : baum T ≠ ⊥ := by
    intro h0
    apply hLC
    rw [cStarIn_eq_of_baum_eq_bot (G := G) h0]
    exact hLG.le
  obtain ⟨S₁, hS₁, hBS₁⟩ := B6.exists_isSylowTwoOf_ge (hT.2.1.to_le inf_le_left) hBL
  have hcharL : CharTwo L := two_three_c hG hT hLG.le hS₁ hBS₁
  have hne₁ : cStarIn L S₁ ≠ L := by
    intro heq
    apply hLC
    have := two_three_d hT hb0 hLG.le hS₁ hBS₁
    rw [heq] at this
    exact this
  obtain ⟨l, hl, hlS⟩ := B6.isSylowTwoOf_exists_conj hS₁ hS
  have hne : cStarIn L S ≠ L := by
    intro heq
    apply hne₁
    have h1 : cStarIn L S = A1b.conjSub l (cStarIn L S₁) := by
      have := cStarIn_conjSub l L S₁
      rwa [conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer hl), ← b6_conjSub_eq, ← hlS]
        at this
    have h2 : A1b.conjSub l (cStarIn L S₁) = A1b.conjSub l L := by
      rw [← h1, heq, conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer hl)]
    exact (B6.conjSub l).injective h2
  exact ⟨hcharL, hne, hih L S (Nine.card_lt_of_lt hLG) hcharL (hS : IsSylowOf 2 S L) hne⟩

structure IHData (G T L S : Subgroup Γ) (𝒢 : Set (Subgroup Γ)) : Prop where
  sylow : IsSylowTwoOf S L
  baum_le : baum T ≤ S
  baum_eq : baum S = baum T
  charTwo : CharTwo L
  cStar_le : cStarIn L S ≤ cStarIn G T
  blocks : ∀ E ∈ 𝒢, IsBTBlock L S E
  invariant : ∀ E ∈ 𝒢, ∀ g ∈ L, A1b.conjSub g E ∈ 𝒢
  commute : ∀ E ∈ 𝒢, ∀ E' ∈ 𝒢, E ≠ E' → ∀ x ∈ E, ∀ y ∈ E', x * y = y * x
  gen : cStarIn L S ⊔ (⨆ E ∈ 𝒢, E) = L

theorem exists_ihData [Finite Γ] {G T L : Subgroup Γ} (hG : CharTwo G) (hih : IHFor G)
    (hT : IsSylowTwoOf T G) (hL : L ∈ lSet G T) :
    ∃ (S : Subgroup Γ) (𝒢 : Set (Subgroup Γ)), IHData G T L S 𝒢 := by
  classical
  obtain ⟨hLG, hBL, hLC⟩ := hL
  have hb0 : baum T ≠ ⊥ := by
    intro h0
    apply hLC
    rw [cStarIn_eq_of_baum_eq_bot (G := G) h0]
    exact hLG.le
  obtain ⟨S, hS, hBS⟩ := B6.exists_isSylowTwoOf_ge (hT.2.1.to_le inf_le_left) hBL
  have hbaum : baum S = baum T :=
    baum_eq_of_isPGroup_of_baum_le hT hS.2.1 (hS.1.trans hLG.le) hBS
  obtain ⟨hcharL, -, 𝒢, hbl, hinv, hcomm, hsup, -⟩ :=
    seven_three_ih hG hih hT ⟨hLG, hBL, hLC⟩ hS
  exact ⟨S, 𝒢, ⟨hS, hBS, hbaum, hcharL, two_three_d hT hb0 hLG.le hS hBS, hbl, hinv, hcomm,
    hsup⟩⟩

namespace IHData

variable {G T L S : Subgroup Γ} {𝒢 : Set (Subgroup Γ)}

theorem join_le (d : IHData G T L S 𝒢) : (⨆ E ∈ 𝒢, E) ≤ L :=
  iSup₂_le fun E hE => (d.blocks E hE).le

theorem normal_join (d : IHData G T L S 𝒢) :
    L ≤ Subgroup.normalizer ((⨆ E ∈ 𝒢, E : Subgroup Γ) : Set Γ) := by
  have key : ∀ g ∈ L, ∀ x ∈ (⨆ E ∈ 𝒢, E : Subgroup Γ),
      g * x * g⁻¹ ∈ (⨆ E ∈ 𝒢, E : Subgroup Γ) := by
    intro g hg x hx
    have hle : (⨆ E ∈ 𝒢, E : Subgroup Γ) ≤
        (⨆ E ∈ 𝒢, E : Subgroup Γ).comap (MulAut.conj g).toMonoidHom :=
      iSup₂_le fun E hE => by
        intro y hy
        have hmem : A1b.conjSub g E ∈ 𝒢 := d.invariant E hE g hg
        have h1 : g * y * g⁻¹ ∈ A1b.conjSub g E := A1b.mem_conjSub_of_mem hy
        show g * y * g⁻¹ ∈ (⨆ E ∈ 𝒢, E : Subgroup Γ)
        exact le_iSup₂ (f := fun E (_ : E ∈ 𝒢) => E) _ hmem h1
    exact hle hx
  intro g hg
  exact B6.mem_normalizer_of_forall_mem (key g hg) fun x hx => by
    simpa using key g⁻¹ (L.inv_mem hg) x hx

theorem normalizes_block (d : IHData G T L S 𝒢) {F : Subgroup Γ} (hF : F ∈ 𝒢) :
    (⨆ E ∈ 𝒢, E : Subgroup Γ) ≤ Subgroup.normalizer (F : Set Γ) := by
  refine iSup₂_le fun E hE => ?_
  intro x hx
  by_cases hEF : E = F
  · subst hEF
    exact Subgroup.le_normalizer hx
  · have hc : ∀ z ∈ F, x * z = z * x := fun z hz => d.commute E hE F hF hEF x hx z hz
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have h1 : x * y * x⁻¹ = y := by
        rw [hc y hy]
        group
      rw [h1]
      exact hy
    · intro hy
      have h1 : x⁻¹ * (x * y * x⁻¹) * x = y := by group
      have h2 : x * (x * y * x⁻¹) = (x * y * x⁻¹) * x := hc _ hy
      have h3 : x * y * x⁻¹ = y := by
        calc x * y * x⁻¹ = x⁻¹ * (x * (x * y * x⁻¹)) := by group
          _ = x⁻¹ * ((x * y * x⁻¹) * x) := by rw [h2]
          _ = y := by rw [← h1]; group
      rwa [h3] at hy

theorem residual_join (d : IHData G T L S 𝒢) :
    oResidualTwo ↥(⨆ E ∈ 𝒢, E : Subgroup Γ) = ⊤ := by
  have := oResidualTwo_sSup_eq_top (𝓔 := 𝒢) fun F hF => (d.blocks F hF).residual
  rwa [sSup_eq_iSup] at this

theorem join_not_le (d : IHData G T L S 𝒢) (hL : ¬ L ≤ cStarIn G T) :
    ¬ (⨆ E ∈ 𝒢, E : Subgroup Γ) ≤ cStarIn G T := by
  intro h
  apply hL
  rw [← d.gen]
  exact sup_le d.cStar_le h

theorem exists_block_not_le (d : IHData G T L S 𝒢) (hL : ¬ L ≤ cStarIn G T) :
    ∃ F ∈ 𝒢, ¬ F ≤ cStarIn G T := by
  by_contra hall
  push Not at hall
  exact d.join_not_le hL (iSup₂_le fun F hF => hall F hF)

theorem isBTBlock_of_mem (d : IHData G T L S 𝒢) (hLG : L ≤ G) {F : Subgroup Γ} (hF : F ∈ 𝒢)
    (hFn : ¬ F ≤ cStarIn G T) : IsBTBlock G T F :=
  isBTBlock_of_sub (d.blocks F hF) hLG d.baum_eq hFn

end IHData

end CFSG.CGT.PushingUpLit.SYMB
