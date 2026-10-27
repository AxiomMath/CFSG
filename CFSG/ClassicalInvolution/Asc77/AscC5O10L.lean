module

public import CFSG.ClassicalInvolution.Asc77.AscC5O1

public section

namespace CFSG.ClassicalInvolution.Asc77.C5O

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77.ExactLayer

section Layer

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem conjSub_exactLayer_eq (hΩ : ConjInvariant Ω) {c c' g : G} (hg : g * c * g⁻¹ = c') :
    conjSub g (exactLayer Ω c) = exactLayer Ω c' := by
  rw [← hg, exactLayer_conj hΩ g c]

theorem conj_mem_exactLayer (hΩ : ConjInvariant Ω) {c c' g : G} (hg : g * c * g⁻¹ = c')
    {y : G} (hy : y ∈ exactLayer Ω c) : g * y * g⁻¹ ∈ exactLayer Ω c' := by
  rw [← conjSub_exactLayer_eq hΩ hg]
  exact conj_mem_conjSub hy

@[expose] noncomputable def conjLayer (hΩ : ConjInvariant Ω) {c c' g : G}
    (hg : g * c * g⁻¹ = c') : ↥(exactLayer Ω c) ≃* ↥(exactLayer Ω c') :=
  (Subgroup.equivMapOfInjective (exactLayer Ω c) (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective).trans (MulEquiv.subgroupCongr (conjSub_exactLayer_eq hΩ hg))

@[expose] noncomputable def layerIso (hΩ : ConjInvariant Ω) {c c' g : G}
    (hg : g * c * g⁻¹ = c') : (↥(exactLayer Ω c) ⧸ classicalInvolutionOddCore ↥(exactLayer Ω c)) ≃*
      (↥(exactLayer Ω c') ⧸ classicalInvolutionOddCore ↥(exactLayer Ω c')) :=
  QuotientGroup.congr _ _ (conjLayer hΩ hg)
    (CFSG.ComponentClassification.OddCore.equiv_invariant (conjLayer hΩ hg))

theorem layerIso_mk (hΩ : ConjInvariant Ω) {c c' g : G} (hg : g * c * g⁻¹ = c')
    (y : ↥(exactLayer Ω c)) :
    layerIso hΩ hg (QuotientGroup.mk y) =
      QuotientGroup.mk ⟨g * y * g⁻¹, conj_mem_exactLayer hΩ hg y.2⟩ :=
  rfl

theorem layerIso_symm (hΩ : ConjInvariant Ω) {c c' g : G} (hg : g * c * g⁻¹ = c')
    (hg' : g⁻¹ * c' * g⁻¹⁻¹ = c) : (layerIso hΩ hg).symm = layerIso hΩ hg' := by
  ext e
  induction e using QuotientGroup.induction_on with
  | H y =>
    rw [MulEquiv.symm_apply_eq, layerIso_mk, layerIso_mk]
    congr 1
    apply Subtype.ext
    show y.1 = g * (g⁻¹ * y.1 * g⁻¹⁻¹) * g⁻¹
    group

theorem layerIso_symm_apply (hΩ : ConjInvariant Ω) {c c' g : G} (hg : g * c * g⁻¹ = c')
    (y : ↥(exactLayer Ω c')) :
    (layerIso hΩ hg).symm (QuotientGroup.mk y) =
      QuotientGroup.mk ⟨g⁻¹ * y * g⁻¹⁻¹,
        conj_mem_exactLayer hΩ (show g⁻¹ * c' * g⁻¹⁻¹ = c by rw [← hg]; group) y.2⟩ := by
  rw [layerIso_symm hΩ hg (by rw [← hg]; group), layerIso_mk]

theorem map_exactImg_layerIso (hΩ : ConjInvariant Ω) {c c' g : G} (hg : g * c * g⁻¹ = c')
    (K : Subgroup G) :
    (T7H.exactImg Ω c K).map (layerIso hΩ hg).toMonoidHom = T7H.exactImg Ω c' (conjSub g K) := by
  have hcore : exactCore c' (conjSub g K) = conjSub g (exactCore c K) := by
    rw [← hg]
    exact exactCore_conjSub g c K
  have hg' : g⁻¹ * c' * g⁻¹⁻¹ = c := by rw [← hg]; group
  ext e
  constructor
  · rintro ⟨e₀, he₀, rfl⟩
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp he₀
    refine Subgroup.mem_map.mpr ⟨⟨g * y * g⁻¹, conj_mem_exactLayer hΩ hg y.2⟩, ?_, rfl⟩
    rw [Subgroup.mem_subgroupOf, hcore]
    exact conj_mem_conjSub (Subgroup.mem_subgroupOf.mp hy)
  · intro he
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp he
    have hy' : (y : G) ∈ conjSub g (exactCore c K) := by
      rw [← hcore]
      exact Subgroup.mem_subgroupOf.mp hy
    refine ⟨QuotientGroup.mk ⟨g⁻¹ * y * g⁻¹⁻¹, conj_mem_exactLayer hΩ hg' y.2⟩,
      Subgroup.mem_map.mpr ⟨⟨g⁻¹ * y * g⁻¹⁻¹, conj_mem_exactLayer hΩ hg' y.2⟩, ?_, rfl⟩, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      have := (mem_conjSub_iff).mp hy'
      simpa using this
    · show layerIso hΩ hg (QuotientGroup.mk _) = QuotientGroup.mk' _ y
      rw [layerIso_mk]
      congr 1
      apply Subtype.ext
      show g * (g⁻¹ * y.1 * g⁻¹⁻¹) * g⁻¹ = y.1
      group

theorem map_exactImg_layerAut (hΩ : ConjInvariant Ω) {c g : G}
    (hgc : g ∈ Subgroup.centralizer ({c} : Set G))
    (hb : conjSub g (exactLayer Ω c) = exactLayer Ω c) (K : Subgroup G) :
    (T7H.exactImg Ω c K).map (C25Y.layerAut (exactLayer Ω c) hb).toMonoidHom =
      T7H.exactImg Ω c (conjSub g K) := by
  have hg : g * c * g⁻¹ = c := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hgc]
    group
  have heq : C25Y.layerAut (exactLayer Ω c) hb = layerIso hΩ hg := by
    ext e
    induction e using QuotientGroup.induction_on with
    | H y => rfl
  rw [heq]
  exact map_exactImg_layerIso hΩ hg K

theorem layerAut_conj (hΩ : ConjInvariant Ω) {c c' g y : G} (hg : g * c * g⁻¹ = c')
    (hy : conjSub y (exactLayer Ω c) = exactLayer Ω c)
    (hy' : conjSub (g * y * g⁻¹) (exactLayer Ω c') = exactLayer Ω c')
    (e : (↥(exactLayer Ω c') ⧸ classicalInvolutionOddCore ↥(exactLayer Ω c'))) :
    C25Y.layerAut (exactLayer Ω c') hy' e =
      layerIso hΩ hg (C25Y.layerAut (exactLayer Ω c) hy ((layerIso hΩ hg).symm e)) := by
  obtain ⟨e₀, rfl⟩ := (layerIso hΩ hg).surjective e
  rw [MulEquiv.symm_apply_apply]
  induction e₀ using QuotientGroup.induction_on with
  | H w =>
    rw [layerIso_mk, C25Y.layerAut_mk, C25Y.layerAut_mk, layerIso_mk]
    congr 1
    apply Subtype.ext
    show g * y * g⁻¹ * (g * w.1 * g⁻¹) * (g * y * g⁻¹)⁻¹ = g * (y * w.1 * y⁻¹) * g⁻¹
    group

end Layer

section Ctx

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ a : G}

omit [Finite G] in
theorem le_centralizer_of_isUniqueInvolution {L : Subgroup G} {x : G}
    (hI : IsUniqueInvolution L x) : L ≤ Subgroup.centralizer ({x} : Set G) := by
  intro k hk
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hmem : k * x * k⁻¹ ∈ L := L.mul_mem (L.mul_mem hk hI.mem) (L.inv_mem hk)
  have hsq : k * x * k⁻¹ * (k * x * k⁻¹) = 1 := by
    calc k * x * k⁻¹ * (k * x * k⁻¹) = k * (x * x) * k⁻¹ := by group
      _ = 1 := by rw [hI.sq]; group
  rcases hI.unique _ hmem hsq with h | h
  · exfalso
    apply hI.ne_one
    calc x = k⁻¹ * (k * x * k⁻¹) * k := by group
      _ = 1 := by rw [h]; group
  · calc k * x = k * x * k⁻¹ * k := by group
      _ = x * k := by rw [h]

omit [Finite G] in
theorem exactCore_mul_eq {L : Subgroup G} (hL : L ≤ Subgroup.centralizer ({z} : Set G)) (a : G) :
    exactCore (a * z) L = exactCore a L := by
  rw [exactCore_def, exactCore_def]
  congr 1
  ext k
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨hk, h⟩
    refine ⟨hk, ?_⟩
    have hkz : k * z = z * k := Subgroup.mem_centralizer_singleton_iff.mp (hL hk)
    have : k * a * z = a * k * z := by
      calc k * a * z = k * (a * z) := by group
        _ = a * z * k := h
        _ = a * (z * k) := by group
        _ = a * (k * z) := by rw [hkz]
        _ = a * k * z := by group
    exact mul_right_cancel this
  · rintro ⟨hk, h⟩
    refine ⟨hk, ?_⟩
    have hkz : k * z = z * k := Subgroup.mem_centralizer_singleton_iff.mp (hL hk)
    calc k * (a * z) = k * a * z := by group
      _ = a * k * z := by rw [h]
      _ = a * (k * z) := by group
      _ = a * (z * k) := by rw [hkz]
      _ = a * z * k := by group

theorem Ctx.exactCore_az (C : Ctx p f Ω K K' W S R R' z t u₁ u₂ a) :
    exactCore (a * z) K = exactCore a K :=
  exactCore_mul_eq (le_centralizer_of_isUniqueInvolution C.hyp.std.setting.hz) a

theorem Ctx.exactCore_az' (C : Ctx p f Ω K K' W S R R' z t u₁ u₂ a) :
    exactCore (a * z) K' = exactCore a K' :=
  exactCore_mul_eq (le_centralizer_of_isUniqueInvolution
    (isUniqueInvolution_of_mem_twinSet C.hyp.std.setting.hz C.hyp.std.setting.hK')) a

end Ctx

end CFSG.ClassicalInvolution.Asc77.C5O
