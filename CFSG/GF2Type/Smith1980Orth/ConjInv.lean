module

public import CFSG.GF2Type.Smith1980Orth.FourOne

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1980Orth

open Subgroup CFSG.LargeExtraspecial

variable {G : Type} [Group G] [Finite G]

theorem OE34a.conjBy {S : Setting G} (h : OE34a S) (g : G) : OE34a (S.conjBy g) := by
  intro x hx hxM hxQ hconj
  have hyM : g⁻¹ * x * g ∈ S.M := (S.mem_conjBy_M_iff g).mp hxM
  have hyQ : g⁻¹ * x * g ∉ S.QG := fun hq => hxQ ((S.mem_conjBy_QG_iff g).mpr hq)
  have hy : IsConj S.z (g⁻¹ * x * g) := by
    have h' := (MulAut.conj g⁻¹).toMonoidHom.map_isConj hx
    simpa [MulAut.conj_apply, mul_assoc] using h'
  have hconj' : IsConj S.z ((g⁻¹ * x * g) * S.z) := by
    have h' := (MulAut.conj g⁻¹).toMonoidHom.map_isConj hconj
    simpa [MulAut.conj_apply, mul_assoc] using h'
  exact h (g⁻¹ * x * g) hy hyM hyQ hconj'

theorem OOdd.conjBy {S : Setting G} (h : OOdd S) (g : G) : OOdd (S.conjBy g) := by
  intro k hxM hxQ
  set k' : G := g⁻¹ * k * g with hk'
  have hyM : k' * S.z * k'⁻¹ ∈ S.M := by
    have h' := (S.mem_conjBy_M_iff g).mp hxM
    simpa [k', mul_assoc] using h'
  have hyQ : k' * S.z * k'⁻¹ ∉ S.QG := by
    intro hq
    apply hxQ
    exact (S.mem_conjBy_QG_iff g).mpr (by simpa [k', mul_assoc] using hq)
  have hiff : ∀ c : G, (IsConj ((S.conjBy g)).z c ∧
      c ∈ ((S.conjBy g)).QG ⊓ ((S.conjBy g)).Qa k) ↔
      (IsConj S.z (g⁻¹ * c * g) ∧ g⁻¹ * c * g ∈ S.QG ⊓ S.Qa k') := by
    intro c
    rw [Subgroup.mem_inf, Subgroup.mem_inf]
    constructor
    · rintro ⟨hc, hcQ, hca⟩
      refine ⟨?_, (S.mem_conjBy_QG_iff g).mp hcQ, ?_⟩
      · exact ((S.isConj_conjBy_z_iff g).mp hc).trans (isConj_iff.mpr ⟨g⁻¹, by group⟩)
      · have hca' : c ∈ S.Qa (g * k') := by
          rw [show g * k' = k * g by rw [hk']; group]
          simpa [S.Qa_conjBy g k] using hca
        exact (S.mem_Qa_mul_iff (g := k') (h := g) (x := c)).mp hca'
    · rintro ⟨hc, hcQ, hca⟩
      have hca' : c ∈ S.Qa (g * k') :=
        (S.mem_Qa_mul_iff (g := k') (h := g) (x := c)).mpr hca
      have hca'' : c ∈ S.Qa (k * g) := by
        rwa [show g * k' = k * g by rw [hk']; group] at hca'
      refine ⟨?_, (S.mem_conjBy_QG_iff g).mpr hcQ, ?_⟩
      · exact (S.isConj_conjBy_z_iff g).mpr (hc.trans (isConj_iff.mpr ⟨g, by group⟩))
      · simpa [S.Qa_conjBy g k] using hca''
  have hset : {c : G | IsConj S.z c ∧ c ∈ S.QG ⊓ S.Qa k'} =
      (fun c => g⁻¹ * c * g) ''
        {c : G | IsConj ((S.conjBy g)).z c ∧ c ∈ ((S.conjBy g)).QG ⊓ ((S.conjBy g)).Qa k} := by
    ext c
    constructor
    · intro hc
      refine ⟨g * c * g⁻¹, ?_, by group⟩
      exact (hiff (g * c * g⁻¹)).mpr (by simpa [mul_assoc] using hc)
    · rintro ⟨c₀, hc₀, rfl⟩
      exact (hiff c₀).mp hc₀
  have hinj : Function.Injective (fun c : G => g⁻¹ * c * g) := by
    intro a b hab
    have h' := congrArg (fun x => g * x * g⁻¹) hab
    simpa [mul_assoc] using h'
  have hncard : {c : G | IsConj S.z c ∧ c ∈ S.QG ⊓ S.Qa k'}.ncard =
      {c : G | IsConj ((S.conjBy g)).z c ∧
        c ∈ ((S.conjBy g)).QG ⊓ ((S.conjBy g)).Qa k}.ncard := by
    rw [hset, Set.ncard_image_of_injective _ hinj]
  rw [← hncard]
  exact h k' hyM hyQ

theorem OF3.conjBy {S : Setting G} (h : OF3 S) (g : G) : OF3 (S.conjBy g) := by
  intro w y hw hwM hwQ hy hyQ hyne
  set k : G := w * y * w⁻¹ * y⁻¹ with hk
  set k' : G := g⁻¹ * k * g with hk'
  have hwM' : g⁻¹ * w * g ∈ S.M := (S.mem_conjBy_M_iff g).mp hwM
  have hwQ' : g⁻¹ * w * g ∉ S.QG := fun hq => hwQ ((S.mem_conjBy_QG_iff g).mpr hq)
  have hyQ' : g⁻¹ * y * g ∈ S.QG := (S.mem_conjBy_QG_iff g).mp hyQ
  have hyne' : g⁻¹ * y * g ≠ S.z := by
    intro he
    apply hyne
    have h' := congrArg (fun x => g * x * g⁻¹) he
    simpa [mul_assoc] using h'
  have hw' : IsConj S.z (g⁻¹ * w * g) := by
    have h' := (MulAut.conj g⁻¹).toMonoidHom.map_isConj hw
    simpa [MulAut.conj_apply, mul_assoc] using h'
  have hy' : IsConj S.z (g⁻¹ * y * g) := by
    have h' := (MulAut.conj g⁻¹).toMonoidHom.map_isConj hy
    simpa [MulAut.conj_apply, mul_assoc] using h'
  have hkQ : k ∈ ((S.conjBy g)).QG := by
    rw [hk]
    exact ((S.conjBy g).QG.mul_mem (((S.conjBy g)).conj_mem_QG hwM hyQ))
      (((S.conjBy g)).QG.inv_mem hyQ)
  have hkQ' : k' ∈ S.QG := by
    rw [hk']
    exact (S.mem_conjBy_QG_iff g).mp hkQ
  have hk_eq : k = g * k' * g⁻¹ := by
    calc k = w * y * w⁻¹ * y⁻¹ := hk
      _ = g * (g⁻¹ * (w * y * w⁻¹ * y⁻¹) * g) * g⁻¹ := by group
      _ = g * (g⁻¹ * k * g) * g⁻¹ := by rw [← hk]
      _ = g * k' * g⁻¹ := by rw [← hk']
  have hcomm := h (g⁻¹ * w * g) (g⁻¹ * y * g) hw' hwM' hwQ' hy' hyQ' hyne'
  rcases hcomm with hzero | ⟨c', hc', hc'Q, hc'cl⟩
  · left
    rw [((S.conjBy g)).cl_eq_zero_iff hkQ]
    have hzero' : S.cl k' = 0 := by
      simpa [k, k', hk, hk', mul_assoc] using hzero
    rcases (S.cl_eq_zero_iff hkQ').mp hzero' with h1 | h1
    · left
      calc k = g * k' * g⁻¹ := hk_eq
        _ = g * 1 * g⁻¹ := by rw [h1]
        _ = 1 := by group
    · right
      calc k = g * k' * g⁻¹ := hk_eq
        _ = g * S.z * g⁻¹ := by rw [h1]
        _ = (S.conjBy g).z := rfl
  · right
    have hcTQ : g * c' * g⁻¹ ∈ ((S.conjBy g)).QG :=
      (S.mem_conjBy_QG_iff g).mpr (by simpa [mul_assoc] using hc'Q)
    have hcT : IsConj ((S.conjBy g)).z (g * c' * g⁻¹) :=
      (S.isConj_conjBy_z_iff g).mpr (hc'.trans (isConj_iff.mpr ⟨g, rfl⟩))
    have hc'cl' : S.cl c' = S.cl k' := by
      simpa [k, k', hk, hk', mul_assoc] using hc'cl
    refine ⟨g * c' * g⁻¹, hcT, hcTQ, ?_⟩
    rw [((S.conjBy g)).cl_eq_cl_iff hcTQ hkQ]
    rcases (S.cl_eq_cl_iff hc'Q hkQ').mp hc'cl' with h1 | h1
    · left
      calc k = g * k' * g⁻¹ := hk_eq
        _ = g * c' * g⁻¹ := by rw [h1]
    · right
      calc k = g * k' * g⁻¹ := hk_eq
        _ = g * (c' * S.z) * g⁻¹ := by rw [h1]
        _ = (g * c' * g⁻¹) * (g * S.z * g⁻¹) := by group
        _ = (g * c' * g⁻¹) * (S.conjBy g).z := rfl

theorem OLocal.conjBy {S : Setting G} (h : OLocal S) (g : G) : OLocal (S.conjBy g) := by
  intro x y hx hy hxM hyM hxQ
  have hxM' : g⁻¹ * x * g ∈ S.M := (S.mem_conjBy_M_iff g).mp hxM
  have hyM' : g⁻¹ * y * g ∈ S.M := (S.mem_conjBy_M_iff g).mp hyM
  have hxQ' : g⁻¹ * x * g ∉ S.QG := fun hq => hxQ ((S.mem_conjBy_QG_iff g).mpr hq)
  have hx' : IsConj S.z (g⁻¹ * x * g) := by
    have h' := (MulAut.conj g⁻¹).toMonoidHom.map_isConj hx
    simpa [MulAut.conj_apply, mul_assoc] using h'
  have hy' : IsConj S.z (g⁻¹ * y * g) := by
    have h' := (MulAut.conj g⁻¹).toMonoidHom.map_isConj hy
    simpa [MulAut.conj_apply, mul_assoc] using h'
  obtain ⟨h1, h2⟩ := h (g⁻¹ * x * g) (g⁻¹ * y * g) hx' hy' hxM' hyM' hxQ'
  have hord : orderOf (x * y) = orderOf ((g⁻¹ * x * g) * (g⁻¹ * y * g)) := by
    rw [show (g⁻¹ * x * g) * (g⁻¹ * y * g) = g⁻¹ * (x * y) * g by group]
    simpa [MulAut.conj_apply] using (MulEquiv.orderOf_eq (MulAut.conj g⁻¹) (x * y)).symm
  refine ⟨?_, fun h4 => ?_⟩
  · rwa [hord]
  · have h4' : orderOf ((g⁻¹ * x * g) * (g⁻¹ * y * g)) = 4 := by rwa [hord] at h4
    have hsq := h2 h4'
    have he : ((g⁻¹ * x * g) * (g⁻¹ * y * g)) ^ 2 = g⁻¹ * (x * y) ^ 2 * g := by
      rw [show (g⁻¹ * x * g) * (g⁻¹ * y * g) = g⁻¹ * (x * y) * g by group, pow_two, pow_two]
      group
    rw [he] at hsq
    exact (S.isConj_conjBy_z_iff g).mpr (hsq.trans (isConj_iff.mpr ⟨g, by group⟩))

end CFSG.GF2Type.Smith1980Orth
