module

public import CFSG.LocalAnalysis.RankThreeUC.Section6.IsFrobeniusKernelComplement
import all CFSG.LocalAnalysis.RankThreeUC.Section6.IsFrobeniusKernelComplement
public import CFSG.LinearAlgebra.ProjectiveRootSpaces.SylowNormalizerIrreducible
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeUC.ProofSupport.ModelledSylowNormalizerAction

open scoped MatrixGroups

theorem isIrreducibleUnder_mono {G : Type} [Group G] [Finite G] {L L' X : Subgroup G}
    (h : CFSG.LocalAnalysis.RankThreeUC.Section6.IsIrreducibleUnder L X) (hL : L ≤ L') :
    CFSG.LocalAnalysis.RankThreeUC.Section6.IsIrreducibleUnder L' X :=
  ⟨h.1, fun W hW hN => h.2 W hW (hL.trans hN)⟩

theorem mem_normalizer_map_iff {H K : Type} [Group H] [Group K] (e : H ≃* K) (Y : Subgroup H)
    (y : K) :
    y ∈ Subgroup.normalizer ((Y.map e.toMonoidHom : Subgroup K) : Set K) ↔
      e.symm y ∈ Subgroup.normalizer (Y : Set H) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h g
    have := h (e g)
    simpa only [Subgroup.mem_map_equiv, map_mul, map_inv, MulEquiv.symm_apply_apply] using this
  · intro h k
    have := h (e.symm k)
    simpa only [Subgroup.mem_map_equiv, map_mul, map_inv] using this

theorem mem_normalizer_subgroupOf_iff {G : Type} [Group G] {H X : Subgroup G} (hXH : X ≤ H)
    (x : H) :
    x ∈ Subgroup.normalizer ((X.subgroupOf H : Subgroup H) : Set H) ↔
      (x : G) ∈ Subgroup.normalizer (X : Set G) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h g
    constructor
    · intro hg
      exact (h ⟨g, hXH hg⟩).mp hg
    · intro hg
      have hgH : g ∈ H := by
        have : (x : G)⁻¹ * ((x : G) * g * (x : G)⁻¹) * (x : G) ∈ H :=
          H.mul_mem (H.mul_mem (H.inv_mem x.2) (hXH hg)) x.2
        simpa [mul_assoc] using this
      exact (h ⟨g, hgH⟩).mpr hg
  · intro h g
    exact h g

theorem isIrreducibleUnder_inf_normalizer_of_equiv {G K : Type} [Group G] [Finite G] [Group K]
    [Finite K]
    {H X : Subgroup G} (hXH : X ≤ H) (e : H ≃* K)
    (h : CFSG.LocalAnalysis.RankThreeUC.Section6.IsIrreducibleUnder
      (Subgroup.normalizer (((X.subgroupOf H).map e.toMonoidHom : Subgroup K) : Set K))
      ((X.subgroupOf H).map e.toMonoidHom)) :
    CFSG.LocalAnalysis.RankThreeUC.Section6.IsIrreducibleUnder (H ⊓ Subgroup.normalizer (X : Set G)) X := by
  unfold CFSG.LocalAnalysis.RankThreeUC.Section6.IsIrreducibleUnder at *
  obtain ⟨hne, hirr⟩ := h
  refine ⟨?_, ?_⟩
  · intro hb
    apply hne
    rw [hb]
    ext z
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, Subgroup.mem_bot]
    constructor
    · rintro ⟨w, hw, rfl⟩
      have : (w : G) = 1 := by simpa using hw
      have : w = 1 := Subtype.ext this
      simp [this]
    · rintro rfl
      exact ⟨1, by simp, by simp⟩
  · intro W hW hN
    have hWH : W ≤ H := hW.trans hXH
    have hle : W.subgroupOf H ≤ X.subgroupOf H := fun w hw => hW hw
    have hN' : Subgroup.normalizer (((X.subgroupOf H).map e.toMonoidHom : Subgroup K) : Set K) ≤
        Subgroup.normalizer (((W.subgroupOf H).map e.toMonoidHom : Subgroup K) : Set K) := by
      intro y hy
      rw [mem_normalizer_map_iff] at hy ⊢
      rw [mem_normalizer_subgroupOf_iff hXH] at hy
      rw [mem_normalizer_subgroupOf_iff hWH]
      exact hN ⟨(e.symm y).2, hy⟩
    rcases hirr _ (Subgroup.map_mono hle) hN' with h0 | h0
    · left
      have h1 : W.subgroupOf H = ⊥ :=
        (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h0
      ext w
      simp only [Subgroup.mem_bot]
      constructor
      · intro hw
        have : (⟨w, hWH hw⟩ : H) ∈ W.subgroupOf H := hw
        rw [h1] at this
        simpa using congrArg Subtype.val (Subgroup.mem_bot.mp this)
      · rintro rfl; exact W.one_mem
    · right
      have h1 : W.subgroupOf H = X.subgroupOf H :=
        Subgroup.map_injective e.injective h0
      refine le_antisymm hW fun x hx => ?_
      have : (⟨x, hXH hx⟩ : H) ∈ X.subgroupOf H := hx
      rw [← h1] at this
      exact this

theorem isIrreducibleUnder_inf_normalizer_of_psl2 {G : Type} [Group G] [Finite G]
    {H : Subgroup G} {p n : ℕ} [Fact p.Prime] (hp : 5 ≤ p) (hn : 1 < n)
    (hH : Nonempty (H ≃* PSL(2, GaloisField p n)))
    {X : Subgroup G} (hXH : X ≤ H) (hX : CFSG.ABGLocalTools.IsSylowOf p X H) :
    CFSG.LocalAnalysis.RankThreeUC.Section6.IsIrreducibleUnder (H ⊓ Subgroup.normalizer (X : Set G)) X := by
  obtain ⟨e⟩ := hH
  obtain ⟨Q, hQ⟩ := hX
  have hQ' : (Q : Subgroup H) = X.subgroupOf H := by
    rw [← hQ]; ext g; simp [Subgroup.mem_subgroupOf, Subgroup.mem_map]
  refine isIrreducibleUnder_inf_normalizer_of_equiv hXH e ?_
  rw [← hQ']
  exact CFSG.LinearAlgebra.ProjectiveRootSpaces.SylowNormalizerIrreducible.isIrreducibleUnder_normalizer_sylow
    p n hp hn (Sylow.mapSurjective (f := e.toMonoidHom) e.surjective Q)

theorem isIrreducibleUnder_inf_normalizer_of_psl2_of_le {G : Type} [Group G] [Finite G]
    {H M : Subgroup G} {p n : ℕ} [Fact p.Prime] (hp : 5 ≤ p) (hn : 1 < n)
    (hH : Nonempty (H ≃* PSL(2, GaloisField p n)))
    {X : Subgroup G} (hXH : X ≤ H) (hX : CFSG.ABGLocalTools.IsSylowOf p X H)
    (hM : H ⊓ Subgroup.normalizer (X : Set G) ≤ M) :
    CFSG.LocalAnalysis.RankThreeUC.Section6.IsIrreducibleUnder (M ⊓ Subgroup.normalizer (X : Set G)) X :=
  isIrreducibleUnder_mono (isIrreducibleUnder_inf_normalizer_of_psl2 hp hn hH hXH hX)
    (fun x hx => ⟨hM hx, hx.2⟩)

end CFSG.LocalAnalysis.RankThreeUC.ProofSupport.ModelledSylowNormalizerAction
