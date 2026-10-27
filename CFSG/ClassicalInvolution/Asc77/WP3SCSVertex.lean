module

import CFSG.ClassicalInvolution.Asc77.AscE187Img
public import CFSG.ClassicalInvolution.Asc77.WP3SCSModel

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Disconnected
open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

section Conj

variable {G : Type} [Group G]

theorem conjSub_closure_three (g a b c : G) :
    conjSub g (Subgroup.closure ({a, b, c} : Set G)) =
      Subgroup.closure ({g * a * g⁻¹, g * b * g⁻¹, g * c * g⁻¹} : Set G) := by
  unfold conjSub
  rw [MonoidHom.map_closure]
  congr 1
  simp [Set.image_insert_eq, MulAut.conj_apply]

end Conj

section Vertex

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' J : Subgroup G} {z u t : G}

theorem TwinFrameSettingCore.exists_twinVertex (hs : TwinFrameSettingCore p f Ω K K' J z u t) :
    ∃ (g₀ : G) (V : TwinVertex p f Ω z), g₀ * z * g₀⁻¹ = t ∧ g₀ * V.a * g₀⁻¹ = z ∧
      g₀ * (V.x * V.y) * g₀⁻¹ = u ∧ V.x * V.y ≠ 1 ∧ V.x * V.y ≠ z ∧ V.x * V.y ≠ V.a ∧
      V.a * (V.x * V.y) ≠ z := by
  have hp := hs.odd
  have hq := hs.five
  have hΩ := hs.hyp
  have hd := hs.frame
  have hz := hd.hz
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hd.hK'
  have hKcl : IsClassicalMember p f K z := isClassicalMember_of_twin hΩ hd.mem hz
  have hK'cl : IsClassicalMember p f K' z := isClassicalMember_of_twin hΩ hd.hK'.1 hzK'
  obtain ⟨g₀, hg₀⟩ := hs.trans J hd.hJ.1
  have hgz : g₀ * z * g₀⁻¹ = t := by
    have h1 : IsUniqueInvolution (conjSub g₀ K) (g₀ * z * g₀⁻¹) :=
      ConnectedA2.isUniqueInvolution_of_isClassicalMember hp hq (hKcl.conj g₀)
    rw [hg₀] at h1
    exact h1.eq hd.ht
  have hzt : g₀⁻¹ * t * g₀⁻¹⁻¹ = z := by rw [← hgz]; group
  have hinj : ∀ x y : G, g₀⁻¹ * x * g₀⁻¹⁻¹ = g₀⁻¹ * y * g₀⁻¹⁻¹ → x = y := fun x y h =>
    mul_left_cancel (mul_right_cancel h)
  obtain ⟨R, R', hRsyl, hR'syl, hcomm, -, -, x, hx, y, hy, hx2, hy2, hxy⟩ :=
    hs.exists_sylow_frame_at (c := t) (Or.inl rfl)
  have hxE : x ∈ exactCore t K := hRsyl.1 hx
  have hyE : y ∈ exactCore t K' := hR'syl.1 hy
  have hconjE : ∀ (L : Subgroup G) (w : G), w ∈ exactCore t L →
      g₀⁻¹ * w * g₀⁻¹⁻¹ ∈ exactCore z (conjSub g₀⁻¹ L) := by
    intro L w hw
    have := conj_mem_conjSub (n := g₀⁻¹) hw
    rwa [← exactCore_conjSub, hzt] at this
  have hxy' : x * y = y * x := hcomm x hx y hy
  have ht_cl : t ∉ Subgroup.closure ({z, u} : Set G) := hd.t_not_mem_closure hp hq hΩ
  have hu_cl : u ∈ Subgroup.closure ({z, u} : Set G) := Subgroup.subset_closure (by simp)
  have hz_cl : z ∈ Subgroup.closure ({z, u} : Set G) := Subgroup.subset_closure (by simp)
  let V : TwinVertex p f Ω z :=
    { M := conjSub g₀⁻¹ K
      M' := conjSub g₀⁻¹ K'
      a := g₀⁻¹ * z * g₀⁻¹⁻¹
      x := g₀⁻¹ * x * g₀⁻¹⁻¹
      y := g₀⁻¹ * y * g₀⁻¹⁻¹
      hM := ⟨hΩ.conjInvariant g₀⁻¹ K hd.mem, by
        have h := trivialOnQuot_conjSub (hd.tq_t_K hp hq hΩ) g₀⁻¹
        rwa [hzt] at h⟩
      hM' := ⟨hΩ.conjInvariant g₀⁻¹ K' hd.hK'.1, by
        have h := trivialOnQuot_conjSub (hd.tq_t_K' hp hq hΩ) g₀⁻¹
        rwa [hzt] at h⟩
      hMM' := fun h => hd.hne (conjSub_injective g₀⁻¹ h).symm
      hMa := hKcl.conj g₀⁻¹
      hM'a := hK'cl.conj g₀⁻¹
      haz := fun h => hd.t_ne_z (hinj t z (by rw [hzt]; exact h.symm))
      hx := hconjE K x hxE
      hy := hconjE K' y hyE
      hxx := by
        calc g₀⁻¹ * x * g₀⁻¹⁻¹ * (g₀⁻¹ * x * g₀⁻¹⁻¹) = g₀⁻¹ * (x * x) * g₀⁻¹⁻¹ := by group
          _ = g₀⁻¹ * z * g₀⁻¹⁻¹ := by rw [hx2]
      hyy := by
        calc g₀⁻¹ * y * g₀⁻¹⁻¹ * (g₀⁻¹ * y * g₀⁻¹⁻¹) = g₀⁻¹ * (y * y) * g₀⁻¹⁻¹ := by group
          _ = g₀⁻¹ * z * g₀⁻¹⁻¹ := by rw [hy2]
      hxy := by
        calc g₀⁻¹ * x * g₀⁻¹⁻¹ * (g₀⁻¹ * y * g₀⁻¹⁻¹) = g₀⁻¹ * (x * y) * g₀⁻¹⁻¹ := by group
          _ = g₀⁻¹ * (y * x) * g₀⁻¹⁻¹ := by rw [hxy']
          _ = g₀⁻¹ * y * g₀⁻¹⁻¹ * (g₀⁻¹ * x * g₀⁻¹⁻¹) := by group }
  have hVu : V.x * V.y = g₀⁻¹ * u * g₀⁻¹⁻¹ := by
    show g₀⁻¹ * x * g₀⁻¹⁻¹ * (g₀⁻¹ * y * g₀⁻¹⁻¹) = g₀⁻¹ * u * g₀⁻¹⁻¹
    rw [← hxy]
    group
  have hVa : V.a = g₀⁻¹ * z * g₀⁻¹⁻¹ := rfl
  refine ⟨g₀, V, hgz, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hVa]
    group
  · rw [hVu]
    group
  · rw [hVu]
    intro h
    exact hd.hu1 (hinj u 1 (by rw [h]; group))
  · rw [hVu]
    intro h
    apply ht_cl
    have : u = t := hinj u t (by rw [h, hzt])
    rw [← this]
    exact hu_cl
  · rw [hVu, hVa]
    intro h
    exact hd.huz (hinj u z (by rw [h]))
  · rw [hVu, hVa]
    intro h
    apply ht_cl
    have h2 : z * u = t := hinj (z * u) t (by
      calc g₀⁻¹ * (z * u) * g₀⁻¹⁻¹ = g₀⁻¹ * z * g₀⁻¹⁻¹ * (g₀⁻¹ * u * g₀⁻¹⁻¹) := by group
        _ = z := h
        _ = g₀⁻¹ * t * g₀⁻¹⁻¹ := hzt.symm)
    rw [← h2]
    exact mul_mem hz_cl hu_cl

theorem exists_twinVertex (hs : TwinFrameSetting p f Ω K K' J z u t) :
    ∃ (g₀ : G) (V : TwinVertex p f Ω z), g₀ * z * g₀⁻¹ = t ∧ g₀ * V.a * g₀⁻¹ = z ∧
      g₀ * (V.x * V.y) * g₀⁻¹ = u ∧ V.x * V.y ≠ 1 ∧ V.x * V.y ≠ z ∧ V.x * V.y ≠ V.a ∧
      V.a * (V.x * V.y) ≠ z := by
  have hp := hs.odd
  have hq := hs.five
  have hΩ := hs.hyp
  have hd := hs.frame
  have hz := hd.hz
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hd.hK'
  have hKcl : IsClassicalMember p f K z := isClassicalMember_of_twin hΩ hd.mem hz
  have hK'cl : IsClassicalMember p f K' z := isClassicalMember_of_twin hΩ hd.hK'.1 hzK'
  obtain ⟨g₀, hg₀⟩ := hs.trans J hd.hJ.1
  have hgz : g₀ * z * g₀⁻¹ = t := by
    have h1 : IsUniqueInvolution (conjSub g₀ K) (g₀ * z * g₀⁻¹) :=
      ConnectedA2.isUniqueInvolution_of_isClassicalMember hp hq (hKcl.conj g₀)
    rw [hg₀] at h1
    exact h1.eq hd.ht
  have hzt : g₀⁻¹ * t * g₀⁻¹⁻¹ = z := by rw [← hgz]; group
  have hinj : ∀ x y : G, g₀⁻¹ * x * g₀⁻¹⁻¹ = g₀⁻¹ * y * g₀⁻¹⁻¹ → x = y := fun x y h =>
    mul_left_cancel (mul_right_cancel h)
  obtain ⟨R, R', hRsyl, hR'syl, hcomm, -, -, x, hx, y, hy, hx2, hy2, hxy⟩ :=
    hs.exists_sylow_frame_at (c := t) (Or.inl rfl)
  have hxE : x ∈ exactCore t K := hRsyl.1 hx
  have hyE : y ∈ exactCore t K' := hR'syl.1 hy
  have hconjE : ∀ (L : Subgroup G) (w : G), w ∈ exactCore t L →
      g₀⁻¹ * w * g₀⁻¹⁻¹ ∈ exactCore z (conjSub g₀⁻¹ L) := by
    intro L w hw
    have := conj_mem_conjSub (n := g₀⁻¹) hw
    rwa [← exactCore_conjSub, hzt] at this
  have hxy' : x * y = y * x := hcomm x hx y hy
  have ht_cl : t ∉ Subgroup.closure ({z, u} : Set G) := hd.t_not_mem_closure hp hq hΩ
  have hu_cl : u ∈ Subgroup.closure ({z, u} : Set G) := Subgroup.subset_closure (by simp)
  have hz_cl : z ∈ Subgroup.closure ({z, u} : Set G) := Subgroup.subset_closure (by simp)
  let V : TwinVertex p f Ω z :=
    { M := conjSub g₀⁻¹ K
      M' := conjSub g₀⁻¹ K'
      a := g₀⁻¹ * z * g₀⁻¹⁻¹
      x := g₀⁻¹ * x * g₀⁻¹⁻¹
      y := g₀⁻¹ * y * g₀⁻¹⁻¹
      hM := ⟨hΩ.conjInvariant g₀⁻¹ K hd.mem, by
        have h := trivialOnQuot_conjSub (hd.tq_t_K hp hq hΩ) g₀⁻¹
        rwa [hzt] at h⟩
      hM' := ⟨hΩ.conjInvariant g₀⁻¹ K' hd.hK'.1, by
        have h := trivialOnQuot_conjSub (hd.tq_t_K' hp hq hΩ) g₀⁻¹
        rwa [hzt] at h⟩
      hMM' := fun h => hd.hne (conjSub_injective g₀⁻¹ h).symm
      hMa := hKcl.conj g₀⁻¹
      hM'a := hK'cl.conj g₀⁻¹
      haz := fun h => hd.t_ne_z (hinj t z (by rw [hzt]; exact h.symm))
      hx := hconjE K x hxE
      hy := hconjE K' y hyE
      hxx := by
        calc g₀⁻¹ * x * g₀⁻¹⁻¹ * (g₀⁻¹ * x * g₀⁻¹⁻¹) = g₀⁻¹ * (x * x) * g₀⁻¹⁻¹ := by group
          _ = g₀⁻¹ * z * g₀⁻¹⁻¹ := by rw [hx2]
      hyy := by
        calc g₀⁻¹ * y * g₀⁻¹⁻¹ * (g₀⁻¹ * y * g₀⁻¹⁻¹) = g₀⁻¹ * (y * y) * g₀⁻¹⁻¹ := by group
          _ = g₀⁻¹ * z * g₀⁻¹⁻¹ := by rw [hy2]
      hxy := by
        calc g₀⁻¹ * x * g₀⁻¹⁻¹ * (g₀⁻¹ * y * g₀⁻¹⁻¹) = g₀⁻¹ * (x * y) * g₀⁻¹⁻¹ := by group
          _ = g₀⁻¹ * (y * x) * g₀⁻¹⁻¹ := by rw [hxy']
          _ = g₀⁻¹ * y * g₀⁻¹⁻¹ * (g₀⁻¹ * x * g₀⁻¹⁻¹) := by group }
  have hVu : V.x * V.y = g₀⁻¹ * u * g₀⁻¹⁻¹ := by
    show g₀⁻¹ * x * g₀⁻¹⁻¹ * (g₀⁻¹ * y * g₀⁻¹⁻¹) = g₀⁻¹ * u * g₀⁻¹⁻¹
    rw [← hxy]
    group
  have hVa : V.a = g₀⁻¹ * z * g₀⁻¹⁻¹ := rfl
  refine ⟨g₀, V, hgz, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hVa]
    group
  · rw [hVu]
    group
  · rw [hVu]
    intro h
    exact hd.hu1 (hinj u 1 (by rw [h]; group))
  · rw [hVu]
    intro h
    apply ht_cl
    have : u = t := hinj u t (by rw [h, hzt])
    rw [← this]
    exact hu_cl
  · rw [hVu, hVa]
    intro h
    exact hd.huz (hinj u z (by rw [h]))
  · rw [hVu, hVa]
    intro h
    apply ht_cl
    have h2 : z * u = t := hinj (z * u) t (by
      calc g₀⁻¹ * (z * u) * g₀⁻¹⁻¹ = g₀⁻¹ * z * g₀⁻¹⁻¹ * (g₀⁻¹ * u * g₀⁻¹⁻¹) := by group
        _ = z := h
        _ = g₀⁻¹ * t * g₀⁻¹⁻¹ := hzt.symm)
    rw [← h2]
    exact mul_mem hz_cl hu_cl

end Vertex

end CFSG.ClassicalInvolution.Asc77
