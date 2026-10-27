module

public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import Certificates.Data.CFSGNative.PSL3Four.Certificate
public import CFSG.ClassicalInvolution.SmallCases.NobqL34CheckInputs
public import Certificates.Certificate9304
public import Certificates.Certificate2022
public meta import Certificates.Data.CFSGNative.PSL3Four.Certificate

public section

namespace CFSG.ClassicalInvolution.Nobq

open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four

theorem l34CQ_eq : l34CQ = true := by
  exact Certificates.certificate9304.1

theorem l34Key_eq : l34Key = true := by
  exact Certificates.certificate9304.2

theorem cqTabCheck_spec {C Ci : Array Tab} {r : Tab} (h : cqTabCheck C Ci r = true) :
    invsOK 42 C Ci = true ∧ ∀ a < C.size, comp 42 C[a]! C[a]! = r →
      ∃ b < C.size, comp 42 (cqTab C[a]! C[b]! Ci[b]!) (cqTab C[a]! C[b]! Ci[b]!) = idTab 42 ∧
        cqTab C[a]! C[b]! Ci[b]! ≠ idTab 42 ∧ cqTab C[a]! C[b]! Ci[b]! ≠ r := by
  simp only [cqTabCheck, Bool.and_eq_true, allBelow_eq_true] at h
  refine ⟨h.1, fun a ha hca => ?_⟩
  have h2 := h.2 a ha
  simp only [Bool.or_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq, anyBelow_eq_true,
    Bool.and_eq_true, beq_iff_eq] at h2
  rcases h2 with h2 | ⟨b, hb, ⟨h3, h4⟩, h5⟩
  · exact absurd hca h2
  · exact ⟨b, hb, h3, h4, h5⟩

theorem keyTabCheck_spec {ER C : Array Tab} {r : Tab} (h : keyTabCheck ER C r = true) :
    ∀ k < ER.size, comp 42 ER[k]! ER[k]! = r →
      ∃ j < C.size, comp 42 ER[k]! C[j]! ≠ comp 42 C[j]! ER[k]! ∧
        comp 42 ER[k]! C[j]! ≠ comp 42 (comp 42 r C[j]!) ER[k]! := by
  intro k hk hkr
  simp only [keyTabCheck, allBelow_eq_true] at h
  have h2 := h k hk
  simp only [Bool.or_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq, anyBelow_eq_true,
    Bool.and_eq_true] at h2
  rcases h2 with h2 | ⟨j, hj, h3, h4⟩
  · exact absurd hkr h2
  · exact ⟨j, hj, h3, h4⟩

theorem tab_sq_eq {x : Equiv.Perm (Fin 42)} {xT : Tab} (hx : TabRep xT x) (h : x * x = r₁) :
    comp 42 xT xT = r₁T := by
  have h1 : TabRep (comp 42 xT xT) (x * x) := hx.comp hx
  rw [h] at h1
  exact h1.tab_eq tabRep_r₁

theorem cq_C₁
    {x : Equiv.Perm (Fin 42)} (hxS : x ∈ S) (hxr : x * r₁ = r₁ * x) (hx2 : x * x = r₁) :
    ∃ g ∈ S, g * r₁ = r₁ * g ∧ (x * (g * x * g⁻¹)) * (x * (g * x * g⁻¹)) = 1 ∧
      x * (g * x * g⁻¹) ≠ 1 ∧ x * (g * x * g⁻¹) ≠ r₁ := by
  obtain ⟨hinv, hall⟩ := cqTabCheck_spec l34CQ_eq
  have hx : x ∈ C₁ := ⟨Subgroup.mem_centralizer_singleton_iff.2 hxr, hxS⟩
  obtain ⟨a, ha, hxa⟩ := enumerates_C₁.exists_pos hx
  obtain ⟨b, hb, h1, h2, h3⟩ := hall a ha (tab_sq_eq hxa hx2)
  obtain ⟨g, hg, hgb⟩ := enumerates_C₁.exists_elt hb
  have hgi := invsOK_spec hinv hb hgb
  have hy : TabRep (cqTab l34C[a]! l34C[b]! (l34C.map (invTab 42))[b]!)
      (x * (g * x * g⁻¹)) := hxa.comp ((hgb.comp hxa).comp hgi)
  refine ⟨g, hg.2, Subgroup.mem_centralizer_singleton_iff.1 hg.1, ?_, ?_, ?_⟩
  · have := hy.comp hy
    rw [h1] at this
    exact this.perm_eq TabRep.idTab
  · intro h
    rw [h] at hy
    exact h2 (hy.tab_eq TabRep.idTab)
  · intro h
    rw [h] at hy
    exact h3 (hy.tab_eq tabRep_r₁)

theorem key_R
    {r : Equiv.Perm (Fin 42)} (hr : r ∈ R) (hr2 : r * r = r₁) :
    ∃ v ∈ S, v * r₁ = r₁ * v ∧ r * v ≠ v * r ∧ r * v ≠ r₁ * v * r := by
  obtain ⟨k, hk, hrk⟩ := enumerates_R.exists_pos hr
  obtain ⟨j, hj, h1, h2⟩ := keyTabCheck_spec l34Key_eq k hk (tab_sq_eq hrk hr2)
  obtain ⟨v, hv, hvj⟩ := enumerates_C₁.exists_elt hj
  refine ⟨v, hv.2, Subgroup.mem_centralizer_singleton_iff.1 hv.1, ?_, ?_⟩
  · intro h
    have t1 := hrk.comp hvj
    have t2 := hvj.comp hrk
    rw [← h] at t2
    exact h1 (t1.tab_eq t2)
  · intro h
    have t1 := hrk.comp hvj
    have t2 := (tabRep_r₁.comp hvj).comp hrk
    rw [← h] at t2
    exact h2 (t1.tab_eq t2)

end CFSG.ClassicalInvolution.Nobq
