module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoPerOffenderNat
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15InnerDef

import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoPerOffenderSemi
import CFSG.RankThree.GF2n.Stroth80.FieldAut

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open Matrix

private theorem mem_innerPart_or_exists_semilinear {G : Type} [Group G] {V : Type}
    [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V} {L : Subgroup G}
    {F : Type} [Field F] [Finite F] {r : ℕ} (hr : 0 < r) (N : NatQuot ρ L F r)
    (hS : NatSchur N.Mat) (hO : NatOut N.Mat)
    (hIcomm : ∀ v ∈ N.I, v ∈ Submodule.span (ZMod 2)
      {w | ∃ l ∈ L, ∃ x ∈ N.I, w = ρ l x - x})
    {A : Subgroup G} (hA2 : ∀ a ∈ A, a * a = 1)
    (hAN : A ≤ Subgroup.normalizer (L : Set G)) (hAI : ∀ a ∈ A, ∀ v ∈ N.I, ρ a v ∈ N.I)
    {g : G} (hg : g ∈ A) :
    g ∈ innerPart L A ∨ ∃ (T : (Fin r → F) ≃+ (Fin r → F)) (σ : F ≃+* F),
      (∀ v : ↥N.I, N.π ⟨ρ g v, hAI g hg v v.2⟩ = T (N.π v)) ∧
      (∀ u, T (T u) = u) ∧
      (∀ (c : F) (u : Fin r → F), T (c • u) = σ c • T u) ∧
      σ * σ = 1 ∧ σ ≠ 1 := by
  have hgN : ∀ l ∈ L, g * l * g⁻¹ ∈ L := by
    intro l hl
    exact (Subgroup.mem_set_normalizer_iff.mp (hAN hg) l).mp hl
  have hgN' : ∀ l ∈ L, g⁻¹ * l * g ∈ L := by
    intro l hl
    have hmem : g⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
      (Subgroup.normalizer (L : Set G)).inv_mem (hAN hg)
    simpa using (Subgroup.mem_set_normalizer_iff.mp hmem l).mp hl
  have hg2 : ∀ v ∈ N.I, ρ g (ρ g v) = v := by
    intro v _
    have hmul : ρ g * ρ g = 1 := by
      rw [← map_mul, hA2 g hg, map_one]
    simpa [Module.End.mul_apply] using congrArg (fun e => e v) hmul
  obtain ⟨T, σ, hTπ, hT2, hTsmul⟩ := N.exists_semilinear_psi hS hgN hgN' (hAI g hg) hg2
  have hσ2 : σ * σ = 1 := by
    let u₀ : Fin r → F := fun _ => 1
    have hu₀ : u₀ ≠ 0 := by
      intro h
      have h1 : (1 : F) = 0 := by simpa [u₀] using congrFun h ⟨0, hr⟩
      exact one_ne_zero h1
    refine RingEquiv.ext (fun c => ?_)
    rw [RingAut.mul_apply]
    show σ (σ c) = c
    have key : σ (σ c) • u₀ = c • u₀ := by
      have h1 : T (T (c • u₀)) = T (σ c • T u₀) := by rw [hTsmul c u₀]
      have h2 : T (σ c • T u₀) = σ (σ c) • T (T u₀) := hTsmul (σ c) (T u₀)
      have h3 : T (T (c • u₀)) = c • u₀ := hT2 (c • u₀)
      have h4 : T (T u₀) = u₀ := hT2 u₀
      calc σ (σ c) • u₀ = σ (σ c) • T (T u₀) := by rw [h4]
        _ = T (σ c • T u₀) := h2.symm
        _ = T (T (c • u₀)) := h1.symm
        _ = c • u₀ := h3
    exact smul_left_injective F hu₀ key
  by_cases hlin : ∀ c, σ c = c
  · left
    have hTlin : ∀ (c : F) (u : Fin r → F), T (c • u) = c • T u := by
      intro c u
      rw [hTsmul, hlin c]
    obtain ⟨l₀, hl₀, -, hconj⟩ :=
      N.acts_as_L_of_linear hO hIcomm hgN (hAI g hg) hg2 T hTπ hTlin
    exact mem_innerPart.mpr ⟨hg, l₀, hl₀, hconj⟩
  · right
    exact ⟨T, σ, hTπ, hT2, hTsmul, hσ2, fun h1 => hlin fun c => by
      have h := congrArg (fun e : F ≃+* F => e c) h1
      rwa [RingAut.one_eq_refl, RingEquiv.refl_apply] at h⟩

private theorem exists_semilinear_of_not_mem {G : Type} [Group G] {V : Type}
    [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V} {L : Subgroup G}
    {F : Type} [Field F] [Finite F] {r : ℕ} (hr : 0 < r) (N : NatQuot ρ L F r)
    (hS : NatSchur N.Mat) (hO : NatOut N.Mat)
    (hIcomm : ∀ v ∈ N.I, v ∈ Submodule.span (ZMod 2)
      {w | ∃ l ∈ L, ∃ x ∈ N.I, w = ρ l x - x})
    {A : Subgroup G} (hA2 : ∀ a ∈ A, a * a = 1)
    (hAN : A ≤ Subgroup.normalizer (L : Set G)) (hAI : ∀ a ∈ A, ∀ v ∈ N.I, ρ a v ∈ N.I)
    {g : G} (hg : g ∈ A) (hgH : g ∉ innerPart L A) :
    ∃ (T : (Fin r → F) ≃+ (Fin r → F)) (σ : F ≃+* F),
      (∀ v : ↥N.I, N.π ⟨ρ g v, hAI g hg v v.2⟩ = T (N.π v)) ∧
      (∀ u, T (T u) = u) ∧
      (∀ (c : F) (u : Fin r → F), T (c • u) = σ c • T u) ∧
      σ * σ = 1 ∧ σ ≠ 1 := by
  rcases mem_innerPart_or_exists_semilinear hr N hS hO hIcomm hA2 hAN hAI hg with
    h | ⟨T, σ, h1, h2, h3, h4, h5⟩
  · exact absurd h hgH
  · exact ⟨T, σ, h1, h2, h3, h4, h5⟩

private theorem mul_mem_innerPart_of_not_mem {G : Type} [Group G] {V : Type}
    [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V} {L : Subgroup G}
    {F : Type} [Field F] [Finite F] {r : ℕ} (hr : 0 < r) (N : NatQuot ρ L F r)
    (hS : NatSchur N.Mat) (hO : NatOut N.Mat)
    (hIcomm : ∀ v ∈ N.I, v ∈ Submodule.span (ZMod 2)
      {w | ∃ l ∈ L, ∃ x ∈ N.I, w = ρ l x - x})
    {A : Subgroup G} (hA2 : ∀ a ∈ A, a * a = 1) (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hAN : A ≤ Subgroup.normalizer (L : Set G)) (hAI : ∀ a ∈ A, ∀ v ∈ N.I, ρ a v ∈ N.I)
    {a b : G} (ha : a ∈ A) (hb : b ∈ A)
    (haH : a ∉ innerPart L A) (hbH : b ∉ innerPart L A) :
    a * b ∈ innerPart L A := by
  obtain ⟨Ta, σa, hTaπ, hTa2, hTasmul, hσa2, hσa1⟩ :=
    exists_semilinear_of_not_mem hr N hS hO hIcomm hA2 hAN hAI ha haH
  obtain ⟨Tb, σb, hTbπ, hTb2, hTbsmul, hσb2, hσb1⟩ :=
    exists_semilinear_of_not_mem hr N hS hO hIcomm hA2 hAN hAI hb hbH
  have hσσ : σa = σb :=
    _root_.CFSG.RankThree.GF2n.Stroth80.ringEquiv_eq_of_sq_eq_one σa σb hσa2 hσb2 hσa1 hσb1
  have hpair : (a * b) * (a * b) = 1 := by
    have hcomm : a * b = b * a := hAc a ha b hb
    have ha2 : a * a = 1 := hA2 a ha
    have hb2 : b * b = 1 := hA2 b hb
    calc (a * b) * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [← hcomm]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [ha2, hb2, mul_one]
  have hgN : ∀ l ∈ L, (a * b) * l * (a * b)⁻¹ ∈ L := by
    intro l hl
    exact (Subgroup.mem_set_normalizer_iff.mp
      ((Subgroup.normalizer (L : Set G)).mul_mem (hAN ha) (hAN hb)) l).mp hl
  have hgN' : ∀ l ∈ L, (a * b)⁻¹ * l * (a * b) ∈ L := by
    intro l hl
    have hmem : (a * b)⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
      (Subgroup.normalizer (L : Set G)).inv_mem
        ((Subgroup.normalizer (L : Set G)).mul_mem (hAN ha) (hAN hb))
    simpa using (Subgroup.mem_set_normalizer_iff.mp hmem l).mp hl
  have hgI : ∀ v ∈ N.I, ρ (a * b) v ∈ N.I := by
    intro v hv
    have h1 : ρ (a * b) v = ρ a (ρ b v) := by rw [map_mul]; rfl
    rw [h1]
    exact hAI a ha (ρ b v) (hAI b hb v hv)
  have hg2 : ∀ v ∈ N.I, ρ (a * b) (ρ (a * b) v) = v := by
    intro v _
    have hmul : ρ (a * b) * ρ (a * b) = 1 := by
      rw [← map_mul, hpair, map_one]
    simpa [Module.End.mul_apply] using congrArg (fun e => e v) hmul
  have hTπ : ∀ v : ↥N.I, N.π ⟨ρ (a * b) v, hgI v v.2⟩ = (Tb.trans Ta) (N.π v) := by
    intro v
    have hv : ρ (a * b) v = ρ a (ρ b v) := by rw [map_mul]; rfl
    have hsub : (⟨ρ (a * b) v, hgI v v.2⟩ : ↥N.I) =
        ⟨ρ a ((⟨ρ b (v : V), hAI b hb (v : V) v.2⟩ : ↥N.I) : V),
          hAI a ha _ (hAI b hb (v : V) v.2)⟩ := Subtype.ext hv
    rw [hsub, hTaπ, hTbπ]
    rfl
  have hTlin : ∀ (c : F) (u : Fin r → F), (Tb.trans Ta) (c • u) = c • (Tb.trans Ta) u := by
    intro c u
    change Ta (Tb (c • u)) = c • Ta (Tb u)
    rw [hTbsmul c u, hTasmul (σb c) (Tb u)]
    have hcc : σa (σb c) = c := by
      rw [← hσσ]
      rw [← RingAut.mul_apply, hσa2]
      rfl
    rw [hcc]
  obtain ⟨l₀, hl₀, -, hconj⟩ :=
    N.acts_as_L_of_linear hO hIcomm hgN hgI hg2 (Tb.trans Ta) hTπ hTlin
  exact mem_innerPart.mpr ⟨A.mul_mem ha hb, l₀, hl₀, hconj⟩

theorem NatQuot.relIndex_innerPart_le_two {G : Type} [Group G] [Finite G] {V : Type}
    [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V} {L : Subgroup G}
    {F : Type} [Field F] [Finite F] [CharP F 2] {r : ℕ} (hr : 0 < r) (N : NatQuot ρ L F r)
    (hS : NatSchur N.Mat) (hO : NatOut N.Mat)
    (hIcomm : ∀ v ∈ N.I, v ∈ Submodule.span (ZMod 2)
      {w | ∃ l ∈ L, ∃ x ∈ N.I, w = ρ l x - x})
    {A : Subgroup G} (hA2 : ∀ a ∈ A, a * a = 1) (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hAN : A ≤ Subgroup.normalizer (L : Set G)) (hAI : ∀ a ∈ A, ∀ v ∈ N.I, ρ a v ∈ N.I) :
    (innerPart L A).relIndex A ≤ 2 := by
  have hdvd : (innerPart L A).relIndex A ∣ 2 := by
    rw [Subgroup.relIndex_dvd_two_iff]
    by_cases hle : A ≤ innerPart L A
    · exact ⟨1, A.one_mem, fun b hb => Or.inr (hle hb)⟩
    · have hne : ∃ a : G, a ∈ A ∧ a ∉ innerPart L A := by
        by_contra hcon
        apply hle
        intro x hx
        by_contra hxH
        exact hcon ⟨x, hx, hxH⟩
      obtain ⟨a, haA, haH⟩ := hne
      refine ⟨a, haA, fun b hb => ?_⟩
      by_cases hbH : b ∈ innerPart L A
      · exact Or.inr hbH
      · left
        have hab : a * b ∈ innerPart L A :=
          mul_mem_innerPart_of_not_mem hr N hS hO hIcomm hA2 hAc hAN hAI haA hb haH hbH
        rwa [hAc a haA b hb] at hab
  exact Nat.le_of_dvd (by norm_num) hdvd

end CFSG.LocalAnalysis.RankThreeUC.S15
