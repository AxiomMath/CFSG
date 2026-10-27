module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.RankTwoPermute
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.SylowSymSix

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape

open CFSG.Open CFSG.QuasithinUnique
open scoped Pointwise

theorem perm_six_eq_alternating_of_index_two (K : Subgroup (Equiv.Perm (Fin 6)))
    (h : K.index = 2) : K = alternatingGroup (Fin 6) := by
  have hle : alternatingGroup (Fin 6) ≤ K := by
    rw [← Equiv.Perm.closure_three_cycles_eq_alternating, Subgroup.closure_le]
    intro σ hσ
    have h3 : σ ^ 3 = 1 := by
      have := Equiv.Perm.IsThreeCycle.orderOf hσ
      rw [← this]
      exact pow_orderOf_eq_one σ
    have : σ = (σ ^ 2) ^ 2 := by
      calc σ = σ * σ ^ 3 := by rw [h3, mul_one]
        _ = (σ ^ 2) ^ 2 := by group
    rw [this]
    exact Subgroup.sq_mem_of_index_two h _
  have hA : (alternatingGroup (Fin 6)).index = 2 :=
    alternatingGroup.index_eq_two
  symm
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  have h1 := Subgroup.index_mul_card K
  have h2 := Subgroup.index_mul_card (alternatingGroup (Fin 6))
  rw [h] at h1
  rw [hA] at h2
  omega

theorem set_mul_map_eq {A Γ : Type*} [Group A] [Group Γ] (ψ : A →* Γ) {T P : Subgroup A}
    (h : (T : Set A) * P = (P : Set A) * T) :
    ((T.map ψ : Subgroup Γ) : Set Γ) * (P.map ψ : Subgroup Γ) =
      (P.map ψ : Subgroup Γ) * (T.map ψ : Subgroup Γ) := by
  simp only [Subgroup.coe_map]
  rw [← Set.image_mul, ← Set.image_mul, h]

theorem sylow_permute_transport {Γ B : Type*} [Group Γ] [Group B] {Y S Z : Subgroup Γ}
    (hS : IsSylowTwoOf S Y) (f : ↥Y ≃* B)
    (h : ∀ T : Subgroup B, IsPGroup 2 T → ¬ 2 ∣ T.index →
      ∃ P0 : Subgroup B, P0 ≤ (Z.subgroupOf Y).map f.toMonoidHom ∧ Nat.card P0 = 3 ∧
        (T : Set B) * P0 = (P0 : Set B) * T) :
    ∃ P : Subgroup Γ, P ≤ Z ∧ Nat.card P = 3 ∧ (S : Set Γ) * P = (P : Set Γ) * S := by
  obtain ⟨hSY, hS2, hSi⟩ := hS
  have hS2' : IsPGroup 2 (S.subgroupOf Y) := hS2.of_equiv (Subgroup.subgroupOfEquivOfLe hSY).symm
  have hT2 : IsPGroup 2 ((S.subgroupOf Y).map f.toMonoidHom) := hS2'.map _
  have hTi : ¬ 2 ∣ ((S.subgroupOf Y).map f.toMonoidHom).index := by
    have : ((S.subgroupOf Y).map f.toMonoidHom).index = (S.subgroupOf Y).index :=
      Subgroup.index_map_equiv (S.subgroupOf Y) f
    rw [this]
    exact hSi
  obtain ⟨P0, hP0Z, hP03, hP0eq⟩ := h _ hT2 hTi
  set ψ : B →* Γ := Y.subtype.comp f.symm.toMonoidHom with hψ
  have hψinj : Function.Injective ψ := by
    intro a b hab
    have : (f.symm a : Γ) = f.symm b := hab
    exact f.symm.injective (Subtype.ext this)
  refine ⟨P0.map ψ, ?_, ?_, ?_⟩
  · rintro _ ⟨b, hb, rfl⟩
    obtain ⟨y, hy, rfl⟩ := hP0Z hb
    simpa [hψ] using Subgroup.mem_subgroupOf.mp hy
  · rw [Subgroup.card_map_of_injective hψinj]
    exact hP03
  · have hSeq : ((S.subgroupOf Y).map f.toMonoidHom).map ψ = S := by
      ext x
      constructor
      · rintro ⟨b, ⟨y, hy, rfl⟩, rfl⟩
        simpa [hψ] using Subgroup.mem_subgroupOf.mp hy
      · intro hx
        refine ⟨f ⟨x, hSY hx⟩, ⟨⟨x, hSY hx⟩, hx, rfl⟩, ?_⟩
        simp [hψ]
    rw [← hSeq]
    exact set_mul_map_eq ψ hP0eq |>.symm ▸ (set_mul_map_eq ψ hP0eq.symm).symm

theorem a6_case
    {N : Type} [Group N] [Finite N] (hs : IsSimpleGroup N) (hnc : ¬ IsMulCommutative N)
    (e : N ≃* alternatingGroup (Fin 6)) (Y : Subgroup (MulAut N)) (hY : innSub N ≤ Y)
    (h2 : (innSub N).relIndex Y ≤ 2)
    (hperm : (innSub N).relIndex Y = 2 → Nonempty (↥Y ≃* Equiv.Perm (Fin 6)))
    (S : Subgroup (MulAut N)) (hS : IsSylowTwoOf S Y) :
    ∃ P : Subgroup (MulAut N), P ≤ innSub N ∧ Nat.card P = 3 ∧
      (S : Set (MulAut N)) * P = (P : Set (MulAut N)) * S := by
  haveI : Finite (MulAut N) := inferInstance
  have hne : (innSub N).relIndex Y ≠ 0 := by
    have h := Subgroup.relIndex_mul_card (H := innSub N) (K := Y)
    intro h0
    rw [h0, zero_mul] at h
    exact (Nat.card_pos (α := ↥Y)).ne' h.symm
  have hcases : (innSub N).relIndex Y = 1 ∨ (innSub N).relIndex Y = 2 := by omega
  rcases hcases with h1 | h1
  · have hYZ : Y ≤ innSub N := Subgroup.relIndex_eq_one.mp h1
    have hinj := conj_injective_of_simple hs hnc
    have hYeq : Y = innSub N := le_antisymm hYZ hY
    let g : ↥Y ≃* N :=
      ((MulEquiv.subgroupCongr hYeq).trans (MonoidHom.ofInjective hinj).symm)
    refine sylow_permute_transport (Z := innSub N) hS (g.trans e) ?_
    intro T hT2 hTi
    obtain ⟨P0, hP03, hP0⟩ :=
      CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.SylowAltSix.exists_order_three_permuting_sylow_two_alternating_six
        T hT2 hTi
    refine ⟨P0, ?_, hP03, hP0⟩
    intro x _
    refine ⟨(g.trans e).symm x, ?_, by simp⟩
    exact Subgroup.mem_subgroupOf.mpr (hYZ ((g.trans e).symm x).2)
  · obtain ⟨f⟩ := hperm h1
    have hK : (((innSub N).subgroupOf Y).map f.toMonoidHom).index = 2 := by
      exact (Subgroup.index_map_equiv ((innSub N).subgroupOf Y) f).trans h1
    have hKeq := perm_six_eq_alternating_of_index_two _ hK
    refine sylow_permute_transport (Z := innSub N) hS f ?_
    intro T hT2 hTi
    obtain ⟨P0, hP0A, hP03, hP0⟩ := exists_order_three_permuting_sylow_two_perm_six T hT2 hTi
    exact ⟨P0, hKeq ▸ hP0A, hP03, hP0⟩

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
