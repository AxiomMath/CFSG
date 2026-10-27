module

public import CFSG.HardMathSupport.Solomon.LocalBalance.GlueTools

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator

variable {G : Type*} [Group G]

private theorem mk_eq_of_mul_inv_mem {p : ℕ} {X : Subgroup G} {a b : G} (ha : a ∈ X) (hb : b ∈ X)
    (h : a * b⁻¹ ∈ GLAPPrimeCoreOf p X) :
    QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨a, ha⟩ = QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨b, hb⟩ := by
  obtain ⟨c, hc, hcab⟩ := h
  have hc' : c = ⟨a * b⁻¹, X.mul_mem ha (X.inv_mem hb)⟩ := Subtype.ext hcab
  subst hc'
  rw [← mul_inv_eq_one, ← map_inv, ← map_mul]
  exact (QuotientGroup.eq_one_iff _).2 hc

private theorem gLBConj_self_of_mem {g : G} {X : Subgroup G} (hg : g ∈ X) : GLBConj g X = X := by
  ext y
  rw [mem_gLBConj]
  constructor
  · intro h
    have := X.mul_mem (X.mul_mem (X.inv_mem hg) h) hg
    have e : g⁻¹ * (g * y * g⁻¹) * g = y := by group
    rwa [e] at this
  · intro h
    exact X.mul_mem (X.mul_mem hg h) (X.inv_mem hg)

theorem mem_normalizer_of_ne [Finite G] {p : ℕ} (hp : p.Prime) {X J J' : Subgroup G}
    (hJ : GLAPComponent p X J) (hJ' : GLAPComponent p X J') (hne : J ≠ J') {g : G}
    (hg : g ∈ J') : g ∈ Subgroup.normalizer (J : Set G) := by
  have hgX : g ∈ X := hJ'.1 hg
  have hC : GLAPComponent p X (GLBConj g J) := by
    have := CFSG.HardMathSupport.Solomon.LocalBalance.glaPComponent_gLBConj g hJ
    rwa [gLBConj_self_of_mem hgX] at this
  have hcomm := commutator_le_gLAPPrimeCore_of_ne hp hJ hJ' hne
  have key : ∀ j (hj : j ∈ J), ∃ hy : g⁻¹ * j * g ∈ X,
      QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨g⁻¹ * j * g, hy⟩ =
        QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨j, hJ.1 hj⟩ := by
    intro j hj
    have hjX : j ∈ X := hJ.1 hj
    have hy : g⁻¹ * j * g ∈ X := X.mul_mem (X.mul_mem (X.inv_mem hgX) hjX) hgX
    refine ⟨hy, mk_eq_of_mul_inv_mem hy hjX ?_⟩
    have h1 : j * g⁻¹ * j⁻¹ * g⁻¹⁻¹ ∈ GLAPPrimeCoreOf p X :=
      hcomm (Subgroup.commutator_mem_commutator hj (J'.inv_mem hg))
    have h2 : g⁻¹ * j * g * j⁻¹ = (j * g⁻¹ * j⁻¹ * g⁻¹⁻¹)⁻¹ := by
      group
    rw [h2]
    exact (GLAPPrimeCoreOf p X).inv_mem h1
  have hbar : barX p X (GLBConj g J) = barX p X J := by
    ext x
    constructor
    · rintro ⟨⟨y, hyX⟩, hy, rfl⟩
      have hy : y ∈ GLBConj g J := hy
      rw [mem_gLBConj] at hy
      obtain ⟨hy', hmk⟩ := key _ hy
      refine ⟨⟨g * y * g⁻¹, hJ.1 hy⟩, ?_, ?_⟩
      · exact (Subgroup.mem_subgroupOf).2 hy
      · have : g⁻¹ * (g * y * g⁻¹) * g = y := by group
        simp only [this] at hmk
        exact hmk.symm
    · rintro ⟨⟨j, hjX⟩, hj, rfl⟩
      have hj : j ∈ J := hj
      obtain ⟨hy', hmk⟩ := key j hj
      refine ⟨⟨g⁻¹ * j * g, hy'⟩, ?_, hmk⟩
      show g⁻¹ * j * g ∈ GLBConj g J
      rw [mem_gLBConj]
      simpa [mul_assoc] using hj
  have := glaPComponent_uniqueAux hC hJ hbar
  exact (mem_normalizer_iff_gLBConj_eq).2 this

theorem commutator_mem_gLAPPrimeCoreOf_of_ne [Finite G] {p : ℕ} (hp : p.Prime)
    {X J J' : Subgroup G} (hJ : GLAPComponent p X J) (hJ' : GLAPComponent p X J')
    (hne : J ≠ J') {g : G} (hg : g ∈ J') {y : G} (hy : y ∈ J) :
    g * y * g⁻¹ * y⁻¹ ∈ GLAPPrimeCoreOf p J := by
  have hN := mem_normalizer_of_ne hp hJ hJ' hne hg
  have h1 : g * y * g⁻¹ * y⁻¹ ∈ GLAPPrimeCoreOf p X := by
    have := commutator_le_gLAPPrimeCore_of_ne hp hJ hJ' hne
    rw [← Subgroup.commutator_comm] at this
    exact this (Subgroup.commutator_mem_commutator hg hy)
  have h2 : g * y * g⁻¹ * y⁻¹ ∈ J :=
    J.mul_mem ((Subgroup.mem_normalizer_iff.1 hN y).1 hy) (J.inv_mem hy)
  have := gLAPPrimeCoreOf_inf_le hp X J ⟨h1, h2⟩
  rwa [inf_eq_right.2 hJ.1] at this

end CFSG.HardMathSupport.Solomon.LocalBalance
