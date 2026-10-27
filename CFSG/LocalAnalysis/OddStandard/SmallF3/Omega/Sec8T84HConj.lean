module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Defs
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem isElemAb2_conj {G : Type} [Group G] (g : G) {B : Subgroup G} {k : ℕ}
    (hB : IsElemAb2 B k) : IsElemAb2 (B.map (MulAut.conj g).toMonoidHom) k := by
  refine ⟨CFSG.Open.IsElemAbelian.map hB.1 (MulAut.conj g).toMonoidHom, ?_⟩
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
  exact hB.2

theorem omega1_eq_of_conj {G : Type} [Group G] {P Pm : Subgroup G} (a : G)
    (h : ∀ x : G, x ∈ P ↔ a⁻¹ * x * a ∈ Pm) (hω : omega1 Pm = Pm) : omega1 P = P := by
  apply le_antisymm
  · rw [omega1]
    exact (Subgroup.closure_le P).mpr (fun x hx => hx.1)
  · have htrans : ∀ z ∈ omega1 Pm, a * z * a⁻¹ ∈ omega1 P := by
      intro z hz
      rw [omega1] at hz
      rw [omega1]
      induction hz using Subgroup.closure_induction with
      | mem x hx =>
          exact Subgroup.subset_closure
            ⟨(h (a * x * a⁻¹)).mpr (by
                rw [show a⁻¹ * (a * x * a⁻¹) * a = x by group]
                exact hx.1),
              by rw [show (a * x * a⁻¹) ^ 2 = a * x ^ 2 * a⁻¹ by
                  simp only [pow_two]; group, hx.2, mul_one, mul_inv_cancel]⟩
      | one => simpa using Subgroup.one_mem (Subgroup.closure {x : G | x ∈ P ∧ x ^ 2 = 1})
      | mul x y hx hy ihx ihy =>
          rw [show a * (x * y) * a⁻¹ = (a * x * a⁻¹) * (a * y * a⁻¹) by group]
          exact Subgroup.mul_mem _ ihx ihy
      | inv x hx ih =>
          rw [show a * x⁻¹ * a⁻¹ = (a * x * a⁻¹)⁻¹ by group]
          exact Subgroup.inv_mem _ ih
    intro y hy
    have hy' : a⁻¹ * y * a ∈ omega1 Pm := by
      rw [hω]
      exact (h y).mp hy
    have hres := htrans (a⁻¹ * y * a) hy'
    rwa [show a * (a⁻¹ * y * a) * a⁻¹ = y by group] at hres

theorem complement_of_conj {G : Type} [Group G] {P Pm : Subgroup G} (a : G)
    (h : ∀ x : G, x ∈ P ↔ a⁻¹ * x * a ∈ Pm)
    (hm : ∀ B' : Subgroup G, B' ≤ Pm → IsElemAb2 B' 4 →
      ∃ D' : Subgroup G, D' ≤ Pm ∧ B' ⊓ D' = ⊥ ∧ B' ⊔ D' = Pm) :
    ∀ B : Subgroup G, B ≤ P → IsElemAb2 B 4 →
      ∃ D : Subgroup G, D ≤ P ∧ B ⊓ D = ⊥ ∧ B ⊔ D = P := by
  intro B hBP hB
  let B' : Subgroup G := B.map (MulAut.conj a⁻¹).toMonoidHom
  have hB'Pm : B' ≤ Pm := by
    intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨b, hb, rfl⟩ := hx
    simpa [MulAut.conj_apply, inv_inv] using (h b).mp (hBP hb)
  have hB'elem : IsElemAb2 B' 4 := isElemAb2_conj a⁻¹ hB
  obtain ⟨D', hD'Pm, hinf, hsup⟩ := hm B' hB'Pm hB'elem
  have hψ_inj : Function.Injective (MulAut.conj a).toMonoidHom := (MulAut.conj a).injective
  have hB_eq : B'.map (MulAut.conj a).toMonoidHom = B := by
    have hcomp : ((MulAut.conj a).toMonoidHom).comp (MulAut.conj a⁻¹).toMonoidHom =
        MonoidHom.id G := by
      ext x
      simp only [MonoidHom.comp_apply, MonoidHom.id_apply, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply, inv_inv]
      group
    calc B'.map (MulAut.conj a).toMonoidHom
        = (B.map (MulAut.conj a⁻¹).toMonoidHom).map (MulAut.conj a).toMonoidHom := rfl
      _ = B.map (((MulAut.conj a).toMonoidHom).comp (MulAut.conj a⁻¹).toMonoidHom) :=
          Subgroup.map_map _ _ _
      _ = B.map (MonoidHom.id G) := by rw [hcomp]
      _ = B := Subgroup.map_id B
  have hPm_eq : Pm.map (MulAut.conj a).toMonoidHom = P := by
    ext x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨m, hm', rfl⟩
      have hmem : a * m * a⁻¹ ∈ P := (h (a * m * a⁻¹)).mpr (by
        rw [show a⁻¹ * (a * m * a⁻¹) * a = m by group]
        exact hm')
      simpa [MulAut.conj_apply, inv_inv] using hmem
    · intro hx
      refine ⟨a⁻¹ * x * a, (h x).mp hx, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group
  refine ⟨D'.map (MulAut.conj a).toMonoidHom, ?_, ?_, ?_⟩
  · intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨d, hd, rfl⟩ := hx
    have hmem : a * d * a⁻¹ ∈ P := (h (a * d * a⁻¹)).mpr (by
      rw [show a⁻¹ * (a * d * a⁻¹) * a = d by group]
      exact hD'Pm hd)
    simpa [MulAut.conj_apply, inv_inv] using hmem
  · have h1 : (B' ⊓ D').map (MulAut.conj a).toMonoidHom =
        B ⊓ D'.map (MulAut.conj a).toMonoidHom := by
      rw [Subgroup.map_inf_eq _ _ _ hψ_inj, hB_eq]
    rw [hinf, Subgroup.map_bot] at h1
    exact h1.symm
  · have h2 : (B' ⊔ D').map (MulAut.conj a).toMonoidHom =
        B ⊔ D'.map (MulAut.conj a).toMonoidHom := by
      rw [Subgroup.map_sup, hB_eq]
    rw [hsup, hPm_eq] at h2
    exact h2.symm

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem hasType_conj (hQ : Q.Nondegenerate) (g : ProjOrth Q) {y : ProjOrth Q} {r : ℕ} {α : ℤˣ}
    (h : HasType y r α) : HasType (g * y * g⁻¹) r α := by
  obtain ⟨hy_ne, t, htt, httype, hty⟩ := h
  obtain ⟨ĝ, hĝ⟩ := QuotientGroup.mk'_surjective (piGroup Q) g
  refine ⟨?_, ⟨ĝ * t * ĝ⁻¹, ?_, by rw [invType_conj hQ htt ĝ, httype], ?_⟩⟩
  · intro hconj
    apply hy_ne
    have h1 := congrArg (fun z => g⁻¹ * z * g) hconj
    simpa [mul_assoc] using h1
  · rw [show (ĝ * t * ĝ⁻¹) * (ĝ * t * ĝ⁻¹) = ĝ * (t * t) * ĝ⁻¹ by group, htt, mul_one,
      mul_inv_cancel]
  · simp only [map_mul, map_inv, hĝ, hty]

theorem modelI3_of_conj (hQ : Q.Nondegenerate) {P Pm : Subgroup (ProjOrth Q)} (a : ProjOrth Q)
    (h : ∀ x : ProjOrth Q, x ∈ P ↔ a⁻¹ * x * a ∈ Pm)
    (hm : ∀ x : ProjOrth Q, x ∈ normalizer (Pm : Set (ProjOrth Q)) → x * x = 1 →
      (∃ α : ℤˣ, HasType x 1 α ∨ HasType x 3 α) →
        ∃ B : Subgroup (ProjOrth Q), B ≤ Pm ∧ IsElemAb2 B 4 ∧ ∃ p ∈ Pm,
          (p * x) * (p * x) = 1 ∧ (∀ b ∈ B, (p * x) * b = b * (p * x)) ∧
            ∃ α : ℤˣ, HasType (p * x) 3 α) :
    ∀ x : ProjOrth Q, x ∈ normalizer (P : Set (ProjOrth Q)) → x * x = 1 →
      (∃ α : ℤˣ, HasType x 1 α ∨ HasType x 3 α) →
        ∃ B : Subgroup (ProjOrth Q), B ≤ P ∧ IsElemAb2 B 4 ∧ ∃ p ∈ P,
          (p * x) * (p * x) = 1 ∧ (∀ b ∈ B, (p * x) * b = b * (p * x)) ∧
            ∃ α : ℤˣ, HasType (p * x) 3 α := by
  intro x hxnorm hxsq hxtype
  have hx'norm : a⁻¹ * x * a ∈ normalizer (Pm : Set (ProjOrth Q)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hkey : (a⁻¹ * x * a) * y * (a⁻¹ * x * a)⁻¹ =
        a⁻¹ * (x * (a * y * a⁻¹) * x⁻¹) * a := by group
    rw [hkey]
    constructor
    · intro hy
      have h1 : a * y * a⁻¹ ∈ P := (h (a * y * a⁻¹)).mpr (by
        rw [show a⁻¹ * (a * y * a⁻¹) * a = y by group]
        exact hy)
      exact (h _).mp ((Subgroup.mem_normalizer_iff.mp hxnorm) _ |>.mp h1)
    · intro hy
      have h2 : x * (a * y * a⁻¹) * x⁻¹ ∈ P := (h _).mpr hy
      have h1 : a * y * a⁻¹ ∈ P :=
        (Subgroup.mem_normalizer_iff.mp hxnorm) _ |>.mpr h2
      have h3 := (h (a * y * a⁻¹)).mp h1
      rwa [show a⁻¹ * (a * y * a⁻¹) * a = y by group] at h3
  have hx'sq : (a⁻¹ * x * a) * (a⁻¹ * x * a) = 1 := by
    rw [show (a⁻¹ * x * a) * (a⁻¹ * x * a) = a⁻¹ * (x * x) * a by group, hxsq, mul_one,
      inv_mul_cancel]
  have hx'type : ∃ α : ℤˣ,
      HasType (a⁻¹ * x * a) 1 α ∨ HasType (a⁻¹ * x * a) 3 α := by
    obtain ⟨α, hα⟩ := hxtype
    rcases hα with hα | hα
    · exact ⟨α, Or.inl (by simpa only [inv_inv] using hasType_conj hQ a⁻¹ hα)⟩
    · exact ⟨α, Or.inr (by simpa only [inv_inv] using hasType_conj hQ a⁻¹ hα)⟩
  obtain ⟨B', hB'Pm, hB'elem, p', hp'Pm, hp'x'sq, hcomm', htype'⟩ :=
    hm (a⁻¹ * x * a) hx'norm hx'sq hx'type
  refine ⟨B'.map (MulAut.conj a).toMonoidHom, ?_, isElemAb2_conj a hB'elem,
    a * p' * a⁻¹, ?_, ?_, ?_, ?_⟩
  · intro z hz
    rw [Subgroup.mem_map] at hz
    obtain ⟨b', hb', rfl⟩ := hz
    have hmem : a * b' * a⁻¹ ∈ P := (h (a * b' * a⁻¹)).mpr (by
      rw [show a⁻¹ * (a * b' * a⁻¹) * a = b' by group]
      exact hB'Pm hb')
    simpa [MulAut.conj_apply, inv_inv] using hmem
  · exact (h (a * p' * a⁻¹)).mpr (by
      rw [show a⁻¹ * (a * p' * a⁻¹) * a = p' by group]
      exact hp'Pm)
  · have hpx : (a * p' * a⁻¹) * x = a * (p' * (a⁻¹ * x * a)) * a⁻¹ := by group
    rw [hpx]
    rw [show a * (p' * (a⁻¹ * x * a)) * a⁻¹ * (a * (p' * (a⁻¹ * x * a)) * a⁻¹) =
        a * ((p' * (a⁻¹ * x * a)) * (p' * (a⁻¹ * x * a))) * a⁻¹ by group, hp'x'sq,
      mul_one, mul_inv_cancel]
  · intro b hb
    rw [Subgroup.mem_map] at hb
    obtain ⟨b', hb', rfl⟩ := hb
    have hpx : (a * p' * a⁻¹) * x = a * (p' * (a⁻¹ * x * a)) * a⁻¹ := by group
    rw [hpx]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show a * (p' * (a⁻¹ * x * a)) * a⁻¹ * (a * b' * a⁻¹) =
        a * ((p' * (a⁻¹ * x * a)) * b') * a⁻¹ by group,
      show a * b' * a⁻¹ * (a * (p' * (a⁻¹ * x * a)) * a⁻¹) =
        a * (b' * (p' * (a⁻¹ * x * a))) * a⁻¹ by group,
      hcomm' b' hb']
  · obtain ⟨α', hα'⟩ := htype'
    refine ⟨α', ?_⟩
    have hpx : (a * p' * a⁻¹) * x = a * (p' * (a⁻¹ * x * a)) * a⁻¹ := by group
    rw [hpx]
    exact hasType_conj hQ a hα'

end CFSG.OddStandard.SmallF3.Omega
