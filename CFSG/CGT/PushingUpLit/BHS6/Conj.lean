module

public import CFSG.CGT.PushingUpLit.BHS6.BlockFacts
public import CFSG.CGT.PushingUpLit.BHS6.Basic

public section

namespace CFSG.CGT.PushingUpLit.BHS6

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS
open scoped commutatorElement

variable {Γ : Type} [Group Γ]

theorem b6_conjSub_eq (g : Γ) (H : Subgroup Γ) : B6.conjSub g H = conjSub g H := rfl

theorem baum_conjSub (g : Γ) (T : Subgroup Γ) : baum (conjSub g T) = conjSub g (baum T) :=
  (baum_map_mulEquiv (MulAut.conj g) T).symm

theorem omegaOneCenterOf_conjSub (g : Γ) (T : Subgroup Γ) :
    omegaOneCenterOf (conjSub g T) = conjSub g (omegaOneCenterOf T) :=
  (omegaOneCenterOf_map_mulEquiv (MulAut.conj g) T).symm

theorem pCoreOf_conjSub (g : Γ) (E : Subgroup Γ) :
    pCoreOf 2 (conjSub g E) = conjSub g (pCoreOf 2 E) := by
  rw [← oTwoIn_eq_pCoreOf, ← oTwoIn_eq_pCoreOf]
  exact oTwoIn_map_equiv (MulAut.conj g) E

theorem commutator_conjSub (g : Γ) (A B : Subgroup Γ) :
    ⁅conjSub g A, conjSub g B⁆ = conjSub g ⁅A, B⁆ := by
  unfold conjSub
  rw [Subgroup.map_commutator]

theorem conjSub_eq_bot_iff (g : Γ) (H : Subgroup Γ) : conjSub g H = ⊥ ↔ H = ⊥ :=
  Subgroup.map_eq_bot_iff_of_injective H (MulAut.conj g).injective

theorem isBTBlock_conj {G T E : Subgroup Γ} (g : Γ) (h : IsBTBlock G T E) :
    IsBTBlock (conjSub g G) (conjSub g T) (conjSub g E) where
  le := conjSub_mono g h.le
  residual := oResidualTwo_eq_top_of_mulEquiv ((MulAut.conj g).subgroupMap E) h.residual
  commutator := by
    rw [baum_conjSub, commutator_conjSub, h.commutator]
  perfect := by
    rw [pCoreOf_conjSub, commutator_conjSub, h.perfect]
  elemAbelian := by
    rw [pCoreOf_conjSub]
    refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
    · rw [mem_conjSub_iff] at hx hy
      have := h.elemAbelian.1 _ hx _ hy
      calc x * y = g * ((g⁻¹ * x * g) * (g⁻¹ * y * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * y * g) * (g⁻¹ * x * g)) * g⁻¹ := by rw [this]
        _ = y * x := by group
    · rw [mem_conjSub_iff] at hx
      have := h.elemAbelian.2 _ hx
      have e : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
      calc x ^ 2 = (g * (g⁻¹ * x * g) * g⁻¹) ^ 2 := by rw [← e]
        _ = g * (g⁻¹ * x * g) ^ 2 * g⁻¹ := conj_pow
        _ = 1 := by rw [this]; group
  nonCentral := by
    rw [omegaOneCenterOf_conjSub, commutator_conjSub, Ne, conjSub_eq_bot_iff]
    exact h.nonCentral
  type := by
    rcases h.type with ⟨n, hn, hmod⟩ | ⟨m, hm, hmod⟩
    · exact Or.inl ⟨n, hn, IsNaturalSLTwoModule.of_mulEquiv ((MulAut.conj g).subgroupMap E) hmod⟩
    · exact Or.inr ⟨m, hm, IsNaturalAltModule.of_mulEquiv ((MulAut.conj g).subgroupMap E) hmod⟩

theorem isSylowTwoOf_conjSub_of_mem {T G : Subgroup Γ} (hT : IsSylowTwoOf T G) {g : Γ}
    (hg : g ∈ G) : IsSylowTwoOf (conjSub g T) G := by
  have h := B6.isSylowTwoOf_conjSub hT g
  rwa [b6_conjSub_eq, b6_conjSub_eq, conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer hg)]
    at h

theorem mem_btBlocksG_of_isBTBlock {G T E : Subgroup Γ} (h : IsBTBlock G T E) :
    E ∈ btBlocksG G T :=
  ⟨1, G.one_mem, by rwa [conjSub_one]⟩

theorem conjSub_mem_btBlocksG {G T E : Subgroup Γ} (hE : E ∈ btBlocksG G T) {g : Γ} (hg : g ∈ G) :
    conjSub g E ∈ btBlocksG G T := by
  obtain ⟨h, hh, hEh⟩ := hE
  refine ⟨g * h, G.mul_mem hg hh, ?_⟩
  have := isBTBlock_conj g hEh
  rwa [conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer hg), ← conjSub_mul] at this

theorem isBTBlock_of_baum_eq {G T T' E : Subgroup Γ} (hE : IsBTBlock G T E) (hb : baum T' = baum T)
    (hz : ⁅E, omegaOneCenterOf T'⁆ ≠ ⊥) : IsBTBlock G T' E where
  le := hE.le
  residual := hE.residual
  commutator := by rw [hb]; exact hE.commutator
  perfect := hE.perfect
  elemAbelian := hE.elemAbelian
  nonCentral := hz
  type := hE.type

section Finite

variable [Finite Γ]

theorem exists_conj_baum_of_le_of_le {G T₁ T₂ N : Subgroup Γ} (hT₁ : IsSylowTwoOf T₁ G)
    (hT₂ : IsSylowTwoOf T₂ G) (hNG : N ≤ G) (h₁ : baum T₁ ≤ N) (h₂ : baum T₂ ≤ N) :
    ∃ n ∈ N, baum T₂ = conjSub n (baum T₁) := by
  obtain ⟨S₁, hS₁, hBS₁⟩ := B6.exists_isSylowTwoOf_ge (hT₁.2.1.to_le inf_le_left) h₁
  obtain ⟨S₂, hS₂, hBS₂⟩ := B6.exists_isSylowTwoOf_ge (hT₂.2.1.to_le inf_le_left) h₂
  have e₁ : baum S₁ = baum T₁ :=
    baum_eq_of_isPGroup_of_baum_le hT₁ hS₁.2.1 (hS₁.1.trans hNG) hBS₁
  have e₂ : baum S₂ = baum T₂ :=
    baum_eq_of_isPGroup_of_baum_le hT₂ hS₂.2.1 (hS₂.1.trans hNG) hBS₂
  obtain ⟨n, hn, hnS⟩ := B6.isSylowTwoOf_exists_conj hS₁ hS₂
  refine ⟨n, hn, ?_⟩
  rw [← e₂, hnS, ← e₁, b6_conjSub_eq]
  exact baum_conjSub n S₁

end Finite

end CFSG.CGT.PushingUpLit.BHS6
