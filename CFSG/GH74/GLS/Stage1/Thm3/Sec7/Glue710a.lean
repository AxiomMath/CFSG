module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.Defs
public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.Basic
public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.Transport

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec7

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
  CFSG.GH74.GLS.Stage1.Thm2.Recip
open scoped commutatorElement

theorem compat7_of_psi {G : Type} [Group G] {z : G} {X S P : Subgroup G} {t w : G} {Gs : Type}
    [Group Gs] {E S' : Subgroup Gs} {t' w' z' : Gs} (hSX : S ≤ X) (hPS : P ≤ S)
    (hSO : S ⊓ Oz z = ⊥) (hzS : z ∈ S) (hz1 : z ≠ 1) (hzc : ∀ s ∈ S, s * z = z * s)
    (htS : t ∈ S) (hwS : w ∈ S) (hz'2 : z' * z' = 1)
    (hZ' : (center ↥S').map S'.subtype = zpowers z')
    (hψ : PsiData7 z X S P t w E S' t' w')
    (hfus : ∀ f : G → Gs, Tr.FHom S f → (∀ s ∈ S, f s ∈ S') → (∀ s ∈ P, f s ∈ E) → f t = t' →
      f w = w' → f z = z' →
      ∀ u ∈ S, ∀ v ∈ S, orderOf u = 2 → orderOf v = 2 → (IsConj u v ↔ IsConj (f u) (f v))) :
    Compat7 z X S E S' := by
  obtain ⟨hN, ψ, ⟨hS1, hS2⟩, ⟨hP1, -⟩, ht, hw⟩ := hψ
  refine ⟨hN, ψ, hS1, hS2, ?_⟩
  classical
  obtain ⟨φ, hφ⟩ : ∃ φ : ↥X →* Gs, ∀ u : ↥X, φ u = ((ψ (QuotientGroup.mk u) : ↥(E ⊔ S')) : Gs) :=
    ⟨(E ⊔ S').subtype.comp (ψ.toMonoidHom.comp (QuotientGroup.mk' ((Oz z).subgroupOf X))),
      fun u => rfl⟩
  obtain ⟨f, hfv⟩ : ∃ f : G → Gs, ∀ g (hg : g ∈ S), f g = φ ⟨g, hSX hg⟩ :=
    ⟨fun g => if hg : g ∈ S then φ ⟨g, hSX hg⟩ else 1, fun g hg => by simp [hg]⟩
  have hhom : Tr.FHom S f := by
    refine ⟨fun a ha b hb => ?_, fun a ha b hb hab => ?_⟩
    · rw [hfv (a * b) (S.mul_mem ha hb), hfv a ha, hfv b hb]
      exact map_mul φ ⟨a, hSX ha⟩ ⟨b, hSX hb⟩
    · rw [hfv a ha, hfv b hb, hφ, hφ] at hab
      have h1 : ψ (QuotientGroup.mk (⟨a, hSX ha⟩ : ↥X)) = ψ (QuotientGroup.mk (⟨b, hSX hb⟩ : ↥X)) :=
        Subtype.ext hab
      have h2 := QuotientGroup.eq.1 (ψ.injective h1)
      have h3 : a⁻¹ * b ∈ Oz z := Subgroup.mem_subgroupOf.1 h2
      have h4 : a⁻¹ * b ∈ S ⊓ Oz z := ⟨S.mul_mem (S.inv_mem ha) hb, h3⟩
      rw [hSO, Subgroup.mem_bot] at h4
      exact inv_mul_eq_one.1 h4
  have hfS : ∀ s ∈ S, f s ∈ S' := fun s hs => by
    rw [hfv s hs, hφ]
    exact hS1 ⟨s, hSX hs⟩ hs
  have hfP : ∀ s ∈ P, f s ∈ E := fun s hs => by
    rw [hfv s (hPS hs), hφ]
    exact hP1 ⟨s, hSX (hPS hs)⟩ hs
  have hft : f t = t' := by
    rw [hfv t htS, hφ]
    exact ht ⟨t, hSX htS⟩ rfl
  have hfw : f w = w' := by
    rw [hfv w hwS, hφ]
    exact hw ⟨w, hSX hwS⟩ rfl
  have hsurj : ∀ a ∈ S', ∃ s ∈ S, f s = a := by
    intro a ha
    obtain ⟨s, hsS, hs⟩ := hS2 (ψ.symm ⟨a, (le_sup_right : S' ≤ E ⊔ S') ha⟩) (by simpa using ha)
    refine ⟨(s : G), hsS, ?_⟩
    rw [hfv (s : G) hsS, hφ]
    show ((ψ (QuotientGroup.mk s) : ↥(E ⊔ S')) : Gs) = a
    rw [hs, MulEquiv.apply_symm_apply]
  have hfz : f z = z' := by
    have hcomm : ∀ x ∈ S', x * f z = f z * x := by
      intro x hx
      obtain ⟨s, hs, rfl⟩ := hsurj x hx
      rw [← hhom.mul s hs z hzS, ← hhom.mul z hzS s hs, hzc s hs]
    have hmem : f z ∈ (center ↥S').map S'.subtype := by
      refine ⟨⟨f z, hfS z hzS⟩, Subgroup.mem_center_iff.2 (fun g => ?_), rfl⟩
      exact Subtype.ext (hcomm g.1 g.2)
    rw [hZ'] at hmem
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hmem
    rcases B.zpow_of_sq_eq_one hz'2 k with h1 | h1
    · exact absurd (hk.symm.trans h1) (hhom.ne_one hzS hz1)
    · exact hk.symm.trans h1
  intro u v hu hv hu2 hv2
  have key := hfus f hhom hfS hfP hft hfw hfz (u : G) hu (v : G) hv hu2 hv2
  rw [hfv (u : G) hu, hfv (v : G) hv, hφ, hφ] at key
  exact key

end CFSG.GH74.GLS.Stage1.Thm3.Sec7
