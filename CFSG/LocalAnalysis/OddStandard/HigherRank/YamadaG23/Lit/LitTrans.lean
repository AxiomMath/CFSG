module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitAlt6
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitDefs

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup
open scoped commutatorElement

variable {X : Type*} [Group X] [Finite X] {Z A : Subgroup X} [Z.Normal]

private lemma litMap_subgroupOf_eq (h : LitCtx Z A) (g : ↥(normalizer (A : Set X))) :
    (Z.subgroupOf A).map
        ((Subgroup.normalizerMonoidHom (H := A) g : MulAut ↥A) : ↥A →* ↥A) =
      Z.subgroupOf A := by
  apply le_antisymm
  · intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨z, hz, rfl⟩
    rw [Subgroup.mem_subgroupOf] at hz ⊢
    change (g : X) * (z : X) * (g : X)⁻¹ ∈ Z
    have hc := h.central (z : X) hz (g : X)
    have he : (g : X) * (z : X) * (g : X)⁻¹ = (z : X) := by rw [← hc]; group
    rwa [he]
  · intro y hy
    rw [Subgroup.mem_map]
    refine ⟨y, hy, ?_⟩
    apply Subtype.ext
    change (g : X) * (y : X) * (g : X)⁻¹ = (y : X)
    rw [Subgroup.mem_subgroupOf] at hy
    have hc := h.central (y : X) hy (g : X)
    have he : (g : X) * (y : X) * (g : X)⁻¹ = (y : X) := by rw [← hc]; group
    rw [he]

private noncomputable def litQuotAction (h : LitCtx Z A) :
    ↥(normalizer (A : Set X)) →* MulAut (↥A ⧸ Z.subgroupOf A) :=
  MonoidHom.mk'
    (fun g => QuotientGroup.congr (Z.subgroupOf A) (Z.subgroupOf A)
      (Subgroup.normalizerMonoidHom (H := A) g) (litMap_subgroupOf_eq h g))
    (by
      intro g g'
      ext x
      induction x using QuotientGroup.induction_on with
      | H a =>
        rw [MulAut.mul_apply, QuotientGroup.congr_mk, QuotientGroup.congr_mk,
          QuotientGroup.congr_mk]
        simp [map_mul])

private lemma litQuotAction_mk (h : LitCtx Z A) (g : ↥(normalizer (A : Set X))) (a : ↥A) :
    litQuotAction h g (a : ↥A ⧸ Z.subgroupOf A) =
      ((Subgroup.normalizerMonoidHom (H := A) g a : ↥A) : ↥A ⧸ Z.subgroupOf A) := by
  change QuotientGroup.congr (Z.subgroupOf A) (Z.subgroupOf A)
    (Subgroup.normalizerMonoidHom (H := A) g) (litMap_subgroupOf_eq h g)
    (a : ↥A ⧸ Z.subgroupOf A) = _
  rw [QuotientGroup.congr_mk]

private lemma lit_val_conj_inv_mul (g : ↥(normalizer (A : Set X))) (a : ↥A) :
    (((Subgroup.normalizerMonoidHom (H := A) g) a)⁻¹ * a : ↥A).val =
      (g : X) * (a : X)⁻¹ * (g : X)⁻¹ * (a : X) := by
  simp only [Subgroup.coe_mul, Subgroup.coe_inv,
    Subgroup.normalizerMonoidHom_apply_apply_coe]
  group

private lemma litQuotAction_eq_one_iff (h : LitCtx Z A)
    (g : ↥(normalizer (A : Set X))) :
    litQuotAction h g = 1 ↔ ∀ a ∈ A, ⁅a, (g : X)⁆ ∈ Z := by
  have hcond : litQuotAction h g = 1 ↔
      ∀ a : ↥A, ((Subgroup.normalizerMonoidHom (H := A) g) a)⁻¹ * a ∈ Z.subgroupOf A := by
    constructor
    · intro h1 a
      have h2 := congrArg
        (fun f : MulAut (↥A ⧸ Z.subgroupOf A) => f (a : ↥A ⧸ Z.subgroupOf A)) h1
      simp only [MulAut.one_apply] at h2
      rw [litQuotAction_mk] at h2
      exact (QuotientGroup.eq).mp h2
    · intro h1
      ext x
      induction x using QuotientGroup.induction_on with
      | H a =>
        rw [MulAut.one_apply, litQuotAction_mk]
        exact (QuotientGroup.eq).mpr (h1 a)
  rw [hcond]
  constructor
  · intro h1 a ha
    have hw : (g : X) * (a : X)⁻¹ * (g : X)⁻¹ * (a : X) ∈ Z := by
      have h2 := h1 ⟨a, ha⟩
      rwa [Subgroup.mem_subgroupOf, lit_val_conj_inv_mul] at h2
    have hc := Normal.conj_mem (inferInstance : Z.Normal)
      ((g : X) * (a : X)⁻¹ * (g : X)⁻¹ * (a : X)) hw a
    have key : ⁅a, (g : X)⁆ =
        a * ((g : X) * (a : X)⁻¹ * (g : X)⁻¹ * (a : X)) * a⁻¹ := by
      simp only [commutatorElement_def]; group
    rwa [key]
  · intro h1 a
    have hc := h1 (a : X) a.2
    have hw : (g : X) * (a : X)⁻¹ * (g : X)⁻¹ * (a : X) ∈ Z := by
      have h2 : (a : X)⁻¹ * ⁅(a : X), (g : X)⁆ * (a : X) ∈ Z := by
        simpa using Normal.conj_mem (inferInstance : Z.Normal) ⁅(a : X), (g : X)⁆ hc (a : X)⁻¹
      have key : (g : X) * (a : X)⁻¹ * (g : X)⁻¹ * (a : X) =
          (a : X)⁻¹ * ⁅(a : X), (g : X)⁆ * (a : X) := by
        simp only [commutatorElement_def]; group
      rwa [key]
    rw [Subgroup.mem_subgroupOf, lit_val_conj_inv_mul]
    exact hw

theorem lit_transitive (h : LitCtx Z A)
    (φ : ↥(normalizer (A : Set X)) →* Equiv.Perm (Fin 6)) (hφs : Function.Surjective φ)
    (hφk : ∀ g : ↥(normalizer (A : Set X)), φ g = 1 ↔ ∀ a ∈ A, ⁅a, (g : X)⁆ ∈ Z)
    {b c : X} (hb : b ∈ A) (hc : c ∈ A) (hbZ : b ∉ Z) (hcZ : c ∉ Z) :
    ∃ n ∈ normalizer (A : Set X), ∃ z ∈ Z, n * b * n⁻¹ = c * z := by
  classical
  let N : Subgroup X := normalizer (A : Set X)
  let Z' : Subgroup ↥A := Z.subgroupOf A
  let V := ↥A ⧸ Z'
  have hZ'card : Nat.card Z' = 4 := by
    rw [show Nat.card Z' = Nat.card Z from
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.Z_le_A).toEquiv]
    exact h.card_Z
  have hAcard : Nat.card ↥A = 64 := h.card_A
  have hVcard : Nat.card V = 16 := by
    have hLag := Subgroup.card_eq_card_quotient_mul_card_subgroup Z'
    rw [hAcard, hZ'card] at hLag
    have : Nat.card V * 4 = 64 := hLag.symm
    omega
  let ρ₀ : ↥N →* MulAut V := litQuotAction h
  let P : Subgroup ↥N := (alternatingGroup (Fin 6)).comap φ
  let ρ : ↥P →* MulAut V := ρ₀.comp P.subtype
  let ψ : ↥P →* alternatingGroup (Fin 6) :=
    (φ.comp P.subtype).codRestrict (alternatingGroup (Fin 6)) (fun g => g.2)
  have hψs : Function.Surjective ψ := by
    intro σ
    obtain ⟨g, hg⟩ := hφs σ
    refine ⟨⟨g, ?_⟩, ?_⟩
    · show φ g ∈ alternatingGroup (Fin 6)
      rw [hg]; exact σ.2
    · apply Subtype.ext
      exact hg
  have hker : ∀ g : ↥P, ψ g = 1 ↔ ρ g = 1 := by
    intro g
    have h1 : ψ g = 1 ↔ φ (g.1) = 1 := by
      constructor
      · intro hh; exact congrArg Subtype.val hh
      · intro hh; exact Subtype.ext hh
    rw [h1, hφk g.1]
    have hρ : ρ g = litQuotAction h (g.1) := rfl
    rw [hρ, litQuotAction_eq_one_iff h g.1]
  let vb : ↥A := ⟨b, hb⟩
  let wc : ↥A := ⟨c, hc⟩
  have hvb : (vb : V) ≠ 1 := by
    intro h1
    apply hbZ
    have h2 := (QuotientGroup.eq_one_iff vb).mp h1
    rwa [Subgroup.mem_subgroupOf] at h2
  have hwc : (wc : V) ≠ 1 := by
    intro h1
    apply hcZ
    have h2 := (QuotientGroup.eq_one_iff wc).mp h1
    rwa [Subgroup.mem_subgroupOf] at h2
  obtain ⟨gp, hgp⟩ :=
    lit_alt6_transitive_group hVcard ρ ψ hψs hker (vb : V) (wc : V) hvb hwc
  have hgp' : litQuotAction h (gp.1) (vb : V) = (wc : V) := hgp
  change QuotientGroup.congr Z' Z' (Subgroup.normalizerMonoidHom (H := A) gp.1)
    (litMap_subgroupOf_eq h gp.1) (vb : V) = (wc : V) at hgp'
  rw [QuotientGroup.congr_mk, QuotientGroup.eq_iff_div_mem] at hgp'
  refine ⟨(gp.1 : X), gp.1.2,
    (((Subgroup.normalizerMonoidHom (H := A) gp.1) vb) / wc : ↥A).val, ?_, ?_⟩
  · rwa [Subgroup.mem_subgroupOf] at hgp'
  · have hmem := hgp'
    rw [Subgroup.mem_subgroupOf] at hmem
    have hx : ((Subgroup.normalizerMonoidHom (H := A) gp.1) vb) =
        ((((Subgroup.normalizerMonoidHom (H := A) gp.1) vb) / wc : ↥A)) * wc := by
      rw [div_eq_mul_inv]
      group
    have hval : (gp.1 : X) * b * (gp.1 : X)⁻¹ =
        ((((Subgroup.normalizerMonoidHom (H := A) gp.1) vb) / wc : ↥A).val) * c := by
      have h1 := congrArg Subtype.val hx
      change (gp.1 : X) * b * (gp.1 : X)⁻¹ =
        ((((Subgroup.normalizerMonoidHom (H := A) gp.1) vb) / wc : ↥A).val) * c at h1
      exact h1
    rw [hval]
    exact h.central _ hmem c

end CFSG.OddStandard.HigherRank.YamadaG23
