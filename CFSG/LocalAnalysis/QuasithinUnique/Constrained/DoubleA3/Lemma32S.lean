module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Lemma32K
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.L34Comp

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Id2519
open scoped MatrixGroups

@[expose] def K32LeK : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G) (s x z₁ z₂ : G) (K : Subgroup G),
    K32Ctx T M H S L s x z₁ z₂ K → KInEight K → L ≤ K

section Orbit

variable {G : Type} [Group G]

theorem card_conj_orbit_eq_relIndex (H K : Subgroup G) :
    Nat.card {L' : Subgroup G // ∃ h ∈ H, L' = CFSG.conjugate K h} =
      (H ⊓ Subgroup.normalizer (K : Set G)).relIndex H := by
  classical
  set N : Subgroup G := H ⊓ Subgroup.normalizer (K : Set G) with hN
  have hφ : ∀ a b : ↥H, CFSG.conjugate K ((a⁻¹ : ↥H) : G) = CFSG.conjugate K ((b⁻¹ : ↥H) : G) ↔
      a⁻¹ * b ∈ N.subgroupOf H := by
    intro a b
    rw [Subgroup.mem_subgroupOf]
    have hmem : ((a⁻¹ * b : ↥H) : G) ∈ H := (a⁻¹ * b).2
    have hiff : ((a⁻¹ * b : ↥H) : G) ∈ N ↔
        ((a⁻¹ * b : ↥H) : G) ∈ Subgroup.normalizer (K : Set G) := by
      rw [hN, Subgroup.mem_inf]
      exact ⟨fun h => h.2, fun h => ⟨hmem, h⟩⟩
    rw [hiff, ← BenderBranch.conjugate_eq_iff_mem_normalizer]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    constructor
    · intro h
      have h1 : CFSG.conjugate (CFSG.conjugate K ((a : G)⁻¹)) (b : G) =
          CFSG.conjugate (CFSG.conjugate K ((b : G)⁻¹)) (b : G) := by rw [h]
      rw [BenderBranch.conjugate_conjugate, BenderBranch.conjugate_conjugate, inv_mul_cancel,
        BenderBranch.conjugate_one] at h1
      exact h1
    · intro h
      have h1 : CFSG.conjugate (CFSG.conjugate K ((a : G)⁻¹ * (b : G))) ((b : G)⁻¹) =
          CFSG.conjugate K ((b : G)⁻¹) := by rw [h]
      rw [BenderBranch.conjugate_conjugate] at h1
      have e1 : (a : G)⁻¹ * (b : G) * (b : G)⁻¹ = (a : G)⁻¹ := by group
      rw [e1] at h1
      exact h1
  let φ : ↥H → {L' : Subgroup G // ∃ h ∈ H, L' = CFSG.conjugate K h} := fun a =>
    ⟨CFSG.conjugate K ((a⁻¹ : ↥H) : G), ((a⁻¹ : ↥H) : G), (a⁻¹ : ↥H).2, rfl⟩
  let f : (↥H ⧸ N.subgroupOf H) → {L' : Subgroup G // ∃ h ∈ H, L' = CFSG.conjugate K h} :=
    Quotient.lift φ (fun a b hab => by
      apply Subtype.ext
      exact (hφ a b).mpr (QuotientGroup.leftRel_apply.mp hab))
  have hf : Function.Bijective f := by
    constructor
    · intro p q hpq
      induction p using Quotient.inductionOn with
      | h a =>
        induction q using Quotient.inductionOn with
        | h b =>
          have h1 : φ a = φ b := hpq
          exact Quotient.sound (QuotientGroup.leftRel_apply.mpr ((hφ a b).mp (congrArg Subtype.val h1)))
    · rintro ⟨L', h, hh, rfl⟩
      exact ⟨⟦(⟨h, hh⟩ : ↥H)⁻¹⟧, Subtype.ext (by simp [f, φ])⟩
  rw [Subgroup.relIndex, Subgroup.index]
  exact (Nat.card_eq_of_bijective f hf).symm

theorem false_of_card_conj_eq_two [Finite G] {H K S₁ : Subgroup G} (hS : IsSylowTwoOf S₁ H)
    (hSN : S₁ ≤ Subgroup.normalizer (K : Set G))
    (hcard : Nat.card {L' : Subgroup G // ∃ h ∈ H, L' = CFSG.conjugate K h} = 2) : False := by
  have hidx : (H ⊓ Subgroup.normalizer (K : Set G)).relIndex H = 2 := by
    rw [← card_conj_orbit_eq_relIndex]; exact hcard
  have hSle : S₁ ≤ H ⊓ Subgroup.normalizer (K : Set G) := le_inf hS.1 hSN
  have h1 := Subgroup.relIndex_mul_relIndex S₁ (H ⊓ Subgroup.normalizer (K : Set G)) H hSle inf_le_left
  rw [hidx] at h1
  apply hS.2.2
  show 2 ∣ S₁.relIndex H
  rw [← h1]
  exact Dvd.intro_left _ rfl

end Orbit

section Struct

variable {G : Type} [Group G] [Finite G] {T M H S L K : Subgroup G} {s x z₁ z₂ : G}

theorem sOne_comm_z₁ (hA : A3A3x T M H S L s x z₁ z₂) {g : G} (hg : g ∈ sOne S x) :
    g * z₁ = z₁ * g := by
  have hz₁ : z₁ ∈ Subgroup.centralizer ((baum S : Subgroup G) : Set G) := hA.z₁_mem.2
  have hle : sOne S x ≤ centralizerElem z₁ := by
    refine sup_le (fun r hr => ?_) (Subgroup.zpowers_le.mpr ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hz₁ r hr)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hA.x_comm₁
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hg)

theorem k32_sOne_le_normalizer (ctx : K32Ctx T M H S L s x z₁ z₂ K) (hz₁K : z₁ ∈ K) :
    sOne S x ≤ Subgroup.normalizer (K : Set G) := by
  intro g hg
  by_contra hgN
  have hgG : g ∈ centralizerElem z₂ := ctx.sylow.1 hg
  have hgz₂ : g⁻¹ * z₂ * g = z₂ := by
    have h1 : g * z₂ = z₂ * g := Subgroup.mem_centralizer_singleton_iff.mp hgG
    calc g⁻¹ * z₂ * g = g⁻¹ * (z₂ * g) := by group
      _ = g⁻¹ * (g * z₂) := by rw [h1]
      _ = z₂ := by group
  have hK' : IsComponentIn (conjR K g) (centralizerElem z₂) := isComponentIn_conj_cent g hgz₂ ctx.comp
  have hne : conjR K g ≠ K := fun h => hgN (mem_normalizer_iff_conjR_eq.mpr h)
  rcases BenderBranch.eq_or_commute_of_isComponentIn ctx.comp hK' with h | h
  · exact hne h.symm
  · have hz₁c : z₁ ∈ conjR K g := by
      rw [mem_conjR]
      have e : g * z₁ * g⁻¹ = z₁ := by
        calc g * z₁ * g⁻¹ = (z₁ * g) * g⁻¹ := by rw [sOne_comm_z₁ ctx.a3 hg]
          _ = z₁ := by group
      rw [e]; exact hz₁K
    have hKc : K ≤ Subgroup.centralizer ((conjR K g : Subgroup G) : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
    have hKz : K ≤ centralizerElem z₂ := ctx.comp.1
    have hKzz : K ≤ Subgroup.centralizer ((Subgroup.zpowers (z₁ * z₂) : Subgroup G) : Set G) := by
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      have h1 : a * z₁ = z₁ * a := (Subgroup.mem_centralizer_iff.mp (hKc ha) z₁ hz₁c).symm
      have h2 : a * z₂ = z₂ * a := Subgroup.mem_centralizer_singleton_iff.mp (hKz ha)
      have h3 : (z₁ * z₂) * a = a * (z₁ * z₂) := by
        calc (z₁ * z₂) * a = z₁ * (z₂ * a) := by group
          _ = z₁ * (a * z₂) := by rw [h2]
          _ = (z₁ * a) * z₂ := by group
          _ = (a * z₁) * z₂ := by rw [h1]
          _ = a * (z₁ * z₂) := by group
      exact ((Commute.zpow_left (show Commute (z₁ * z₂) a from h3) n).eq)
    have hbot : ⁅K, Subgroup.zpowers (z₁ * z₂)⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hKzz
    have hKbot : K = ⊥ := by rw [← ctx.comm]; exact hbot
    have hq : CFSG.IsQuasisimple ↥K := BenderBranch.isQuasisimple_of_isComponentIn ctx.comp
    exact (Subgroup.nontrivial_iff_ne_bot K).mp (CFSG.LocalCores.isQuasisimple_nontrivial hq) hKbot

theorem k32_K_norm (hP : Prop121Three) (ctx : K32Ctx T M H S L s x z₁ z₂ K) (hz₁K : z₁ ∈ K) :
    centralizerElem z₂ ≤ Subgroup.normalizer (K : Set G) := by
  have hS := k32_sOne_le_normalizer ctx hz₁K
  have hs := ctx.a3.cs.setting
  have hpc : pCoreOf 2 (centralizerElem z₂) ≠ ⊥ :=
    pCoreOf_centralizerElem_ne_bot ctx.a3.z₂_ne ctx.a3.sq₂
  have hJc : K ∈ cComp (centralizerElem z₂) := mem_cComp_of_isComponentIn ctx.comp
  rcases hP G hs.simple hs.nonabelian hs.qtke _ hpc K hJc with hnorm | ⟨hcard, -⟩
  · exact hnorm
  · exact (false_of_card_conj_eq_two ctx.sylow hS hcard).elim

theorem k32Struct_of (hP : Prop121Three) (hLK : K32LeK) : K32Struct := by
  intro G _ _ T M H S L s x z₁ z₂ K ctx h8
  have hLK' : L ≤ K := hLK G T M H S L s x z₁ z₂ K ctx h8
  have hA4 : IsA4Block L (blockU L) := IsA4Block.of_alt3 ctx.a3.cs.block.1.1 ctx.a3.a3
  have hz₁K : z₁ ∈ K := hLK' (hA4.le ctx.a3.z₁_mem.1)
  refine ⟨ctx.a3, ctx.comp, k32_K_norm hP ctx hz₁K, ctx.comm, hLK', ?_⟩
  rw [eq_bot_iff]
  intro l hl
  have hcomm : ∀ l' ∈ L, l * l' = l' * l := fun l' hl' =>
    (Subgroup.mem_centralizer_iff.mp hl.2 l' (hLK' hl')).symm
  have := hA4.center_L l hl.1 hcomm
  simpa using this

end Struct

end CFSG.QuasithinUnique.DoubleA3
