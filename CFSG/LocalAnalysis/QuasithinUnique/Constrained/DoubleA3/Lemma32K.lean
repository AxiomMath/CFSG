module

public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesExtraComponents
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.BlockRank1
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped MatrixGroups

structure A3A3Kpre {G : Type} [Group G] [Finite G] (T M H S L : Subgroup G) (s x z₁ z₂ : G)
    (K : Subgroup G) : Prop extends A3A3x T M H S L s x z₁ z₂ where
  K_comp : IsComponentIn K (centralizerElem z₂)
  K_norm : centralizerElem z₂ ≤ Subgroup.normalizer (K : Set G)
  K_comm : ⁅K, Subgroup.zpowers (z₁ * z₂)⁆ = K
  L_le_K : L ≤ K
  L_faithful : L ⊓ Subgroup.centralizer (K : Set G) = ⊥

theorem A3A3Kpre.toA3A3K {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G} {s x z₁ z₂ : G}
    {K : Subgroup G} (h : A3A3Kpre T M H S L s x z₁ z₂ K)
    (hiso : Nonempty (↥K ≃* alternatingGroup (Fin 6)) ∨ Nonempty (↥K ≃* PSL(2, ZMod 7))) :
    A3A3K T M H S L s x z₁ z₂ K :=
  { toA3A3x := h.toA3A3x
    K_comp := h.K_comp
    K_norm := h.K_norm
    K_comm := h.K_comm
    L_le_K := h.L_le_K
    L_faithful := h.L_faithful
    K_iso := hiso }

structure K32Ctx {G : Type} [Group G] [Finite G] (T M H S L : Subgroup G) (s x z₁ z₂ : G)
    (K : Subgroup G) : Prop where
  a3 : A3A3x T M H S L s x z₁ z₂
  gamma2 : IsGamma2 M (centralizerElem z₂)
  sylow : IsSylowTwoOf (sOne S x) (centralizerElem z₂)
  oddCore : oddCoreIn (centralizerElem z₂) = ⊥
  comp : IsComponentIn K (centralizerElem z₂)
  normz : z₁ * z₂ ∈ Subgroup.normalizer (K : Set G)
  comm : ⁅K, Subgroup.zpowers (z₁ * z₂)⁆ = K
  notM : ¬ K ≤ M
  inner : (¬ CentralQuotientAlt K 6 ∧ ¬ CentralQuotientAlt K 7) → Ch1.InducesInner (z₁ * z₂) K

@[expose] def KInEight {G : Type} [Group G] (K : Subgroup G) : Prop :=
  Nonempty (↥K ≃* alternatingGroup (Fin 5)) ∨ Nonempty (↥K ≃* alternatingGroup (Fin 6)) ∨
  Nonempty (↥K ≃* alternatingGroup (Fin 7)) ∨ Nonempty (↥K ≃* alternatingGroup (Fin 8)) ∨
  Nonempty (↥K ≃* PSL(2, ZMod 7)) ∨ StatedClassicalModel ↥K .PSL 2 17 1 ∨
  StatedClassicalModel ↥K .PSL 3 3 1 ∨
  Nonempty (↥K ≃* CFSG.Blueprint.NativeSporadic.Carrier .M11)

@[expose] def K32Struct : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G) (s x z₁ z₂ : G) (K : Subgroup G),
    K32Ctx T M H S L s x z₁ z₂ K → KInEight K → A3A3Kpre T M H S L s x z₁ z₂ K

@[expose] def K32ExclA7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G) (s x z₁ z₂ : G) (K : Subgroup G),
    K32Ctx T M H S L s x z₁ z₂ K → A3A3Kpre T M H S L s x z₁ z₂ K →
      Nonempty (↥K ≃* alternatingGroup (Fin 7)) → False

@[expose] def K32ExclA8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G) (s x z₁ z₂ : G) (K : Subgroup G),
    K32Ctx T M H S L s x z₁ z₂ K → A3A3Kpre T M H S L s x z₁ z₂ K →
      Nonempty (↥K ≃* alternatingGroup (Fin 8)) → False

@[expose] def K32ExclBig : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G) (s x z₁ z₂ : G) (K : Subgroup G),
    K32Ctx T M H S L s x z₁ z₂ K → A3A3Kpre T M H S L s x z₁ z₂ K →
      (StatedClassicalModel ↥K .PSL 2 17 1 ∨ StatedClassicalModel ↥K .PSL 3 3 1 ∨
        Nonempty (↥K ≃* CFSG.Blueprint.NativeSporadic.Carrier .M11)) → False

theorem k32_exclA5 {G : Type} [Group G] [Finite G] {T M H S L K : Subgroup G} {s x z₁ z₂ : G}
    (ctx : K32Ctx T M H S L s x z₁ z₂ K) (hpre : A3A3Kpre T M H S L s x z₁ z₂ K)
    (h : Nonempty (↥K ≃* alternatingGroup (Fin 5))) : False := by
  obtain ⟨e⟩ := h
  have hcs := ctx.a3.cs
  have h3 := ctx.a3.a3
  have hA4 : IsA4Block L (blockU L) := IsA4Block.of_alt3 hcs.block.1.1 h3
  have hUK : blockU L ≤ K := hA4.le.trans hpre.L_le_K
  have hUR : blockU L ≤ baum S := blockU_le_baum hcs h3
  have hUS : blockU L ≤ sOne S x := hUR.trans le_sup_left
  have hK60 : Nat.card K = 60 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    decide
  have hS₁p : IsPGroup 2 (sOne S x) := ctx.sylow.2.1
  have hle4 : Nat.card ↥(sOne S x ⊓ K) ≤ 4 := by
    have hp : IsPGroup 2 ↥(sOne S x ⊓ K) := hS₁p.to_le inf_le_left
    obtain ⟨n, hn⟩ := hp.exists_card_eq
    have hdvd : Nat.card ↥(sOne S x ⊓ K) ∣ 4 * 15 := by
      have := Subgroup.card_dvd_of_le (inf_le_right : sOne S x ⊓ K ≤ K)
      rw [hK60] at this
      simpa using this
    rw [hn] at hdvd ⊢
    have h4 : 2 ^ n ∣ 4 := Nat.Coprime.dvd_of_dvd_mul_right
      (Nat.Coprime.pow_left n (by norm_num : Nat.Coprime 2 15)) hdvd
    exact Nat.le_of_dvd (by norm_num) h4
  have hU4 : Nat.card ↥(blockU L) = 4 := hA4.card_U
  have hUP : blockU L ≤ sOne S x ⊓ K := le_inf hUS hUK
  have hP0 : blockU L = sOne S x ⊓ K := Subgroup.eq_of_le_of_card_ge hUP (by omega)
  have hxG2 : x ∈ centralizerElem z₂ := Subgroup.mem_centralizer_singleton_iff.mpr ctx.a3.x_comm₂
  have hxK : x ∈ Subgroup.normalizer (K : Set G) := hpre.K_norm hxG2
  have hxS : x ∈ sOne S x := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have hcl' : ∀ u ∈ blockU L, x⁻¹ * u * x ∈ blockU L := by
    intro u hu
    have h1 : x⁻¹ * u * x ∈ sOne S x ⊓ K :=
      ⟨(sOne S x).mul_mem ((sOne S x).mul_mem ((sOne S x).inv_mem hxS) (hUS hu)) hxS, by
        have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (K : Set G)).inv_mem hxK) u).mp
          (hUK hu)
        simpa using this⟩
    rwa [← hP0] at h1
  apply ctx.a3.x_good
  intro y hy
  have hy1 : x * y * x⁻¹ ∈ blockU L := mem_conjR.mp hy
  have hyU : y ∈ blockU L := by
    have := hcl' _ hy1
    have e' : x⁻¹ * (x * y * x⁻¹) * x = y := by group
    rwa [e'] at this
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  exact hA4.comm_U u hu y hyU

theorem k32_A3A3K_of {G : Type} [Group G] [Finite G] {T M H S L K : Subgroup G} {s x z₁ z₂ : G}
    (ctx : K32Ctx T M H S L s x z₁ z₂ K) (hpre : A3A3Kpre T M H S L s x z₁ z₂ K) (h8 : KInEight K)
    (h2 : K32ExclA7) (h3 : K32ExclA8) (h4 : K32ExclBig) : A3A3K T M H S L s x z₁ z₂ K := by
  refine hpre.toA3A3K ?_
  rcases h8 with h | h | h | h | h | h | h | h
  · exact (k32_exclA5 ctx hpre h).elim
  · exact Or.inl h
  · exact (h2 G T M H S L s x z₁ z₂ K ctx hpre h).elim
  · exact (h3 G T M H S L s x z₁ z₂ K ctx hpre h).elim
  · exact Or.inr h
  · exact (h4 G T M H S L s x z₁ z₂ K ctx hpre (Or.inl h)).elim
  · exact (h4 G T M H S L s x z₁ z₂ K ctx hpre (Or.inr (Or.inl h))).elim
  · exact (h4 G T M H S L s x z₁ z₂ K ctx hpre (Or.inr (Or.inr h))).elim

end CFSG.QuasithinUnique.DoubleA3
