module

public import CFSG.LocalAnalysis.AGLEmbedding.ConstrainedSL

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

section Lift

variable {Q : Type*} [Group Q] [Finite Q] {p : ℕ} (hp : p.Prime) (O : Subgroup Q) [O.Normal]
  (hO : p.Coprime (Nat.card O))
include hp hO

theorem conj_mem_of_mk_mem_normalizer {U S : Subgroup Q} (hU : IsPGroup p U) (hSU : S ≤ U)
    {s : Q} (hsU : s ∈ Subgroup.normalizer (U : Set Q))
    (hsS : QuotientGroup.mk' O s ∈
      Subgroup.normalizer ((S.map (QuotientGroup.mk' O) : Subgroup (Q ⧸ O)) : Set (Q ⧸ O)))
    {w : Q} (hw : w ∈ S) : s * w * s⁻¹ ∈ S := by
  have hmem : s * w * s⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp hsU w).mp (hSU hw)
  have himg : QuotientGroup.mk' O (s * w * s⁻¹) ∈ S.map (QuotientGroup.mk' O) := by
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp hsS _).mp (Subgroup.mem_map_of_mem _ hw)
  obtain ⟨w', hw', he⟩ := himg
  have := eq_of_mk_eq_of_isPGroup hp O hO hU (hSU hw') hmem he
  rw [← this]
  exact hw'

theorem mem_normalizer_of_mk_mem_normalizer {U S : Subgroup Q} (hU : IsPGroup p U)
    (hSU : S ≤ U) {s : Q} (hsU : s ∈ Subgroup.normalizer (U : Set Q))
    (hsS : QuotientGroup.mk' O s ∈
      Subgroup.normalizer ((S.map (QuotientGroup.mk' O) : Subgroup (Q ⧸ O)) : Set (Q ⧸ O))) :
    s ∈ Subgroup.normalizer (S : Set Q) := by
  rw [Subgroup.mem_normalizer_iff]
  intro w
  refine ⟨fun hw => conj_mem_of_mk_mem_normalizer hp O hO hU hSU hsU hsS hw, fun hw => ?_⟩
  have h := conj_mem_of_mk_mem_normalizer hp O hO hU hSU (Subgroup.inv_mem _ hsU)
    (by rw [map_inv]; exact Subgroup.inv_mem _ hsS) hw
  simpa [mul_assoc] using h

theorem le_of_map_mk_le {U S₁ S₂ : Subgroup Q} (hU : IsPGroup p U) (h1 : S₁ ≤ U) (h2 : S₂ ≤ U)
    (h : S₁.map (QuotientGroup.mk' O) ≤ S₂.map (QuotientGroup.mk' O)) : S₁ ≤ S₂ := by
  intro x hx
  obtain ⟨y, hy, he⟩ := h (Subgroup.mem_map_of_mem _ hx)
  rw [← eq_of_mk_eq_of_isPGroup hp O hO hU (h2 hy) (h1 hx) he]
  exact hy

theorem exists_lift_mem_normalizer {U B : Subgroup Q} (hU : IsPGroup p U) (hOB : O ≤ B)
    {b : Q} (hb : b ∈ B)
    (hbU : QuotientGroup.mk' O b ∈
      Subgroup.normalizer ((U.map (QuotientGroup.mk' O) : Subgroup (Q ⧸ O)) : Set (Q ⧸ O))) :
    ∃ t ∈ B, t ∈ Subgroup.normalizer (U : Set Q) ∧
      QuotientGroup.mk' O t = QuotientGroup.mk' O b := by
  obtain ⟨o, ho, t, ht, rfl⟩ :=
    Subgroup.mem_sup_of_normal_left.mp (comap_normalizer_map_le_sup hp O hO hU hbU)
  have ho1 : QuotientGroup.mk' O o = 1 := (QuotientGroup.eq_one_iff o).mpr ho
  refine ⟨t, by simpa using B.mul_mem (B.inv_mem (hOB ho)) hb, ht, ?_⟩
  rw [map_mul, ho1, one_mul]

theorem eq_or_eq_of_map_mk_layer {U A W : Subgroup Q} (hU : IsPGroup p U) (hAW : A ≤ W)
    (hWU : W ≤ U) {t : Q}
    (hlay : ∀ Y' : Subgroup (Q ⧸ O), A.map (QuotientGroup.mk' O) ≤ Y' →
      Y' ≤ W.map (QuotientGroup.mk' O) →
      QuotientGroup.mk' O t ∈ Subgroup.normalizer (Y' : Set (Q ⧸ O)) →
      Y' = A.map (QuotientGroup.mk' O) ∨ Y' = W.map (QuotientGroup.mk' O))
    {Y : Subgroup Q} (hAY : A ≤ Y) (hYW : Y ≤ W) (htY : t ∈ Subgroup.normalizer (Y : Set Q)) :
    Y = A ∨ Y = W := by
  rcases hlay (Y.map (QuotientGroup.mk' O)) (Subgroup.map_mono hAY) (Subgroup.map_mono hYW)
      (Subgroup.le_normalizer_map _ (Subgroup.mem_map_of_mem _ htY)) with h | h
  · exact Or.inl (le_antisymm (le_of_map_mk_le hp O hO hU (hYW.trans hWU) (hAW.trans hWU) h.le)
      hAY)
  · exact Or.inr (le_antisymm hYW (le_of_map_mk_le hp O hO hU hWU (hYW.trans hWU) h.ge))

end Lift

section Torus

theorem mem_normalizer_range_of_mult {Q : Type*} [Group Q] {F : Type*} [Field F]
    (ψ : Multiplicative F →* Q) {c : Q} {ν : F} (hν : ν ≠ 0)
    (hc : ∀ a : Multiplicative F,
      c * ψ a * c⁻¹ = ψ (Multiplicative.ofAdd (ν * Multiplicative.toAdd a))) :
    c ∈ Subgroup.normalizer (ψ.range : Set Q) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨_, (hc a).symm⟩
  · rintro ⟨b, hb⟩
    refine ⟨Multiplicative.ofAdd (ν⁻¹ * Multiplicative.toAdd b), ?_⟩
    have h1 := hc (Multiplicative.ofAdd (ν⁻¹ * Multiplicative.toAdd b))
    simp only [toAdd_ofAdd, ← mul_assoc, mul_inv_cancel₀ hν, one_mul, ofAdd_toAdd] at h1
    rw [hb] at h1
    calc ψ (Multiplicative.ofAdd (ν⁻¹ * Multiplicative.toAdd b))
        = c⁻¹ * (c * ψ (Multiplicative.ofAdd (ν⁻¹ * Multiplicative.toAdd b)) * c⁻¹) * c := by
          group
      _ = g := by rw [h1]; group

theorem exists_lift_mult {Q : Type*} [Group Q] [Finite Q] {p : ℕ} (hp : p.Prime)
    (O : Subgroup Q) [O.Normal] (hO : p.Coprime (Nat.card O)) {A B : Subgroup Q}
    (hA : IsPGroup p A) (hOB : O ≤ B) {F : Type*} [Field F]
    (ψ : Multiplicative F →* Q ⧸ O) (hψ : Function.Injective ψ)
    (hψA : ψ.range = A.map (QuotientGroup.mk' O)) (m : Fˣ → F) (hm : ∀ μ, m μ ≠ 0)
    (hc : ∀ μ : Fˣ, ∃ c ∈ B.map (QuotientGroup.mk' O), ∀ a : Multiplicative F,
      c * ψ a * c⁻¹ = ψ (Multiplicative.ofAdd (m μ * Multiplicative.toAdd a))) :
    ∃ φ : Multiplicative F ≃* A, ∀ μ : Fˣ, ∃ t ∈ B, ∀ a : Multiplicative F,
      t * (φ a : Q) * t⁻¹ = φ (Multiplicative.ofAdd (m μ * Multiplicative.toAdd a)) := by
  let g : A →* Q ⧸ O := (QuotientGroup.mk' O).comp A.subtype
  have hg : ∀ x : A, g x = QuotientGroup.mk' O (x : Q) := fun x => rfl
  have hginj : Function.Injective g := fun x y hxy =>
    Subtype.ext (eq_of_mk_eq_of_isPGroup hp O hO hA x.2 y.2 hxy)
  have hgr : ψ.range = g.range := by
    rw [hψA, MonoidHom.range_comp, Subgroup.range_subtype]
  let φ : Multiplicative F ≃* A := (MonoidHom.ofInjective hψ).trans
    ((MulEquiv.subgroupCongr hgr).trans (MonoidHom.ofInjective hginj).symm)
  have hφ : ∀ a, g (φ a) = ψ a := by
    intro a
    change g ((MonoidHom.ofInjective hginj).symm
      (MulEquiv.subgroupCongr hgr (MonoidHom.ofInjective hψ a))) = ψ a
    rw [MonoidHom.apply_ofInjective_symm, MulEquiv.subgroupCongr_apply,
      MonoidHom.ofInjective_apply]
  refine ⟨φ, fun μ => ?_⟩
  obtain ⟨_, ⟨b, hb, rfl⟩, hcψ⟩ := hc μ
  have hbA : QuotientGroup.mk' O b ∈
      Subgroup.normalizer ((A.map (QuotientGroup.mk' O) : Subgroup (Q ⧸ O)) : Set (Q ⧸ O)) :=
    hψA ▸ mem_normalizer_range_of_mult ψ (hm μ) hcψ
  obtain ⟨t, htB, ht, hot⟩ := exists_lift_mem_normalizer hp O hO hA hOB hb hbA
  refine ⟨t, htB, fun a => ?_⟩
  have hmem : t * (φ a : Q) * t⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp ht _).mp (φ a).2
  refine eq_of_mk_eq_of_isPGroup hp O hO hA hmem (φ _).2 ?_
  rw [← hg, hφ, ← hcψ, ← hφ a, hg, map_mul, map_mul, map_inv, hot]

end Torus

end CFSG.AGLEmbedding
