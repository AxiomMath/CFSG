module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FrameDefs

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {Γ₁ Γ₂ : Type} [Group Γ₁] [Group Γ₂] {f : Γ₁ →* Γ₂}

private theorem isElemAbelian_top_of_mulEquiv {Y Y' : Type} [Group Y] [Group Y']
    (e : Y ≃* Y') (p : ℕ) (h : IsElemAbelian p (⊤ : Subgroup Y)) :
    IsElemAbelian p (⊤ : Subgroup Y') := by
  haveI : IsMulCommutative Y' :=
    e.surjective.isMulCommutative (Subgroup.topEquiv.surjective.isMulCommutative h.1)
  refine ⟨inferInstance, fun x _ => ?_⟩
  have hx : (e.symm x) ^ p = 1 := h.2 (e.symm x) trivial
  simpa using congrArg e hx

private theorem isElemAbelian_top_iff {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')
    (p : ℕ) : IsElemAbelian p (⊤ : Subgroup Y) ↔ IsElemAbelian p (⊤ : Subgroup Y') :=
  ⟨isElemAbelian_top_of_mulEquiv e p, isElemAbelian_top_of_mulEquiv e.symm p⟩

private theorem cen_map (hf : Function.Injective f) (T : Subgroup Γ₁) :
    cen (T.map f) = (cen T).map f := by
  ext y
  simp only [cen, Subgroup.mem_inf, Subgroup.mem_map, Subgroup.mem_centralizer_iff, and_assoc]
  constructor
  · rintro ⟨⟨t, ht, hty⟩, hc⟩
    refine ⟨t, ht, ?_, hty⟩
    intro s hs
    have h := hc (f s) (mem_map_of_mem f hs)
    rw [← hty] at h
    exact hf (by simpa only [map_mul] using h)
  · rintro ⟨t, ht, hc, hty⟩
    exact ⟨⟨t, ht, hty⟩, fun z hz => by
      obtain ⟨s, hs, rfl⟩ := hz
      rw [← hty, ← map_mul, ← map_mul, hc s hs]⟩

private theorem nonempty_equiv_map_aux (hf : Function.Injective f) (Y : Subgroup Γ₁)
    (M : Type) [Group M] : Nonempty (↥(Y.map f) ≃* M) ↔ Nonempty (↥Y ≃* M) :=
  ⟨fun h => h.map fun φ => (Subgroup.equivMapOfInjective Y f hf).trans φ,
    fun h => h.map fun φ => (Subgroup.equivMapOfInjective Y f hf).symm.trans φ⟩

theorem isE_map (hf : Function.Injective f) (n : ℕ) (Y : Subgroup Γ₁) :
    IsE n ↥(Y.map f) ↔ IsE n ↥Y := by
  unfold IsE
  rw [Subgroup.card_map_of_injective (K := Y) hf]
  exact and_congr (isElemAbelian_top_iff (Subgroup.equivMapOfInjective Y f hf) 2).symm Iff.rfl

theorem isExtraspecialTwo_map (hf : Function.Injective f) (n : ℕ) (X : Subgroup Γ₁) :
    IsExtraspecialTwo n (X.map f) ↔ IsExtraspecialTwo n X := by
  have hcen : cen (X.map f) = (cen X).map f := cen_map hf X
  have hcard_cen : Nat.card ↥(cen (X.map f)) = Nat.card ↥(cen X) := by
    rw [hcen]
    exact Subgroup.card_map_of_injective (K := cen X) hf
  have hcomm : ⁅X.map f, X.map f⁆ = cen (X.map f) ↔ ⁅X, X⁆ = cen X := by
    rw [← Subgroup.map_commutator (H₁ := X) (H₂ := X) f, hcen]
    exact (Subgroup.map_injective hf).eq_iff
  unfold IsExtraspecialTwo
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨?_, ?_, hcomm.mp h3, ?_⟩
    · rwa [Subgroup.card_map_of_injective (K := X) hf] at h1
    · rwa [hcard_cen] at h2
    · intro y hy
      have h := h4 (f y) (mem_map_of_mem f hy)
      rw [← map_pow, hcen, Subgroup.mem_map_iff_mem hf] at h
      exact h
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨?_, ?_, hcomm.mpr h3, ?_⟩
    · rwa [Subgroup.card_map_of_injective (K := X) hf]
    · rwa [hcard_cen]
    · intro y hy
      obtain ⟨y', hy', rfl⟩ := hy
      rw [← map_pow, hcen]
      exact mem_map_of_mem f (h4 y' hy')

theorem isInternalDirect_map (hf : Function.Injective f) (X U V : Subgroup Γ₁) :
    IsInternalDirect (X.map f) (U.map f) (V.map f) ↔ IsInternalDirect X U V := by
  have h1 : ((U.map f) ⊔ (V.map f) = X.map f) ↔ (U ⊔ V = X) := by
    rw [← Subgroup.map_sup U V f]
    exact (Subgroup.map_injective hf).eq_iff
  have h2 : ((U.map f) ⊓ (V.map f) = ⊥) ↔ (U ⊓ V = ⊥) := by
    rw [← Subgroup.map_inf_eq U V f hf]
    exact ⟨fun h => Subgroup.map_injective hf (by rw [h, Subgroup.map_bot]),
      fun h => by rw [h, Subgroup.map_bot]⟩
  have h3 : (∀ u ∈ U.map f, ∀ v ∈ V.map f, u * v = v * u) ↔
      (∀ u ∈ U, ∀ v ∈ V, u * v = v * u) := by
    constructor
    · intro h u hu v hv
      exact hf (by
        simpa only [map_mul] using h (f u) (mem_map_of_mem f hu) (f v) (mem_map_of_mem f hv))
    · rintro h u hu v hv
      obtain ⟨u', hu', rfl⟩ := hu
      obtain ⟨v', hv', rfl⟩ := hv
      rw [← map_mul, ← map_mul, h u' hu' v' hv']
  unfold IsInternalDirect
  exact and_congr h1 (and_congr h2 h3)

theorem isZ2xD8Decomp_map (hf : Function.Injective f) (X : Subgroup Γ₁) (c : Γ₁)
    (D : Subgroup Γ₁) : IsZ2xD8Decomp (X.map f) (f c) (D.map f) ↔ IsZ2xD8Decomp X c D := by
  have h1 : IsInternalDirect (X.map f) (closure {f c}) (D.map f) ↔
      IsInternalDirect X (closure {c}) D := by
    simpa only [MonoidHom.map_closure, Set.image_singleton] using
      isInternalDirect_map hf X (closure {c}) D
  have h2 : orderOf (f c) = 2 ↔ orderOf c = 2 := by
    rw [orderOf_injective f hf]
  have h3 : Nonempty (↥(D.map f) ≃* DihedralGroup 4) ↔
      Nonempty (↥D ≃* DihedralGroup 4) :=
    nonempty_equiv_map_aux hf D (DihedralGroup 4)
  have h4 : Nonempty (↥(X.map f) ≃* (Multiplicative (ZMod 2) × DihedralGroup 4)) ↔
      Nonempty (↥X ≃* (Multiplicative (ZMod 2) × DihedralGroup 4)) :=
    nonempty_equiv_map_aux hf X (Multiplicative (ZMod 2) × DihedralGroup 4)
  unfold IsZ2xD8Decomp
  exact and_congr h1 (and_congr h2 (and_congr h3 h4))

theorem nonempty_equiv_map (hf : Function.Injective f) (Y : Subgroup Γ₁) (M : Type) [Group M] :
    Nonempty (↥(Y.map f) ≃* M) ↔ Nonempty (↥Y ≃* M) :=
  nonempty_equiv_map_aux hf Y M

theorem isCyclic_map (hf : Function.Injective f) (Y : Subgroup Γ₁) :
    IsCyclic ↥(Y.map f) ↔ IsCyclic ↥Y :=
  (MulEquiv.isCyclic (Subgroup.equivMapOfInjective Y f hf)).symm

theorem isE_equiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y') (n : ℕ) :
    IsE n Y ↔ IsE n Y' := by
  unfold IsE
  rw [Nat.card_congr e.toEquiv]
  exact and_congr (isElemAbelian_top_iff e 2) Iff.rfl

private theorem isQ8StarQ8_of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : IsQ8StarQ8 Y) : IsQ8StarQ8 Y' := by
  obtain ⟨U, V, hU, hV, hcomm, hsup, hcard⟩ := h
  refine ⟨U.map e.toMonoidHom, V.map e.toMonoidHom, ?_, ?_, ?_, ?_, ?_⟩
  · exact hU.map fun φ => (MulEquiv.subgroupMap e U).symm.trans φ
  · exact hV.map fun φ => (MulEquiv.subgroupMap e V).symm.trans φ
  · intro u hu v hv
    obtain ⟨u', hu', rfl⟩ := hu
    obtain ⟨v', hv', rfl⟩ := hv
    rw [← map_mul, ← map_mul, hcomm u' hu' v' hv']
  · rw [← Subgroup.map_sup U V e.toMonoidHom, hsup,
      Subgroup.map_top_of_surjective e.toMonoidHom e.surjective]
  · rw [← Subgroup.map_inf_eq U V e.toMonoidHom e.injective,
      Subgroup.card_map_of_injective (K := U ⊓ V) e.injective]
    exact hcard

theorem isQ8StarQ8_equiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y') :
    IsQ8StarQ8 Y ↔ IsQ8StarQ8 Y' :=
  ⟨isQ8StarQ8_of_mulEquiv e, isQ8StarQ8_of_mulEquiv e.symm⟩

private theorem isFrobeniusOfOrder_of_mulEquiv {Y Y' : Type} [Group Y] [Group Y']
    (e : Y ≃* Y') (n : ℕ) (h : IsFrobeniusOfOrder n Y) : IsFrobeniusOfOrder n Y' := by
  obtain ⟨hcard, W, D, hWn, hsup, hinf, hWne, hDne, hcent⟩ := h
  refine ⟨?_, W.map e.toMonoidHom, D.map e.toMonoidHom, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Nat.card_congr e.toEquiv]
    exact hcard
  · exact hWn.map e.toMonoidHom e.surjective
  · rw [← Subgroup.map_sup W D e.toMonoidHom, hsup,
      Subgroup.map_top_of_surjective e.toMonoidHom e.surjective]
  · rw [← Subgroup.map_inf_eq W D e.toMonoidHom e.injective, hinf, Subgroup.map_bot]
  · intro hbot
    exact hWne (Subgroup.map_injective e.injective (by rw [hbot, Subgroup.map_bot]))
  · intro hbot
    exact hDne (Subgroup.map_injective e.injective (by rw [hbot, Subgroup.map_bot]))
  · intro d hd hd1 w hw hdw
    obtain ⟨d', hd', rfl⟩ := hd
    obtain ⟨w', hw', rfl⟩ := hw
    have hd1' : d' ≠ 1 := fun h1 => hd1 (by simp [h1])
    have hdw' : d' * w' = w' * d' :=
      e.injective (by rw [map_mul, map_mul]; exact hdw)
    rw [hcent d' hd' hd1' w' hw' hdw']
    exact map_one e

theorem isFrobeniusOfOrder_equiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y') (n : ℕ) :
    IsFrobeniusOfOrder n Y ↔ IsFrobeniusOfOrder n Y' :=
  ⟨isFrobeniusOfOrder_of_mulEquiv e n, isFrobeniusOfOrder_of_mulEquiv e.symm n⟩

end CFSG.OddStandard.HigherRank.YamadaG23
