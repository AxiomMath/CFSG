module

public import CFSG.GroupTheory.QuasiDihedralFusion.Transport
public import CFSG.CharacterTheory.Wreathed.CyclicWeakClosure

public section

namespace CFSG.QuasiDihedralFusion

open CFSG.BenderSuzuki.External CFSG.BenderSuzuki.PFchapter1section1

universe u

variable {H : Type u} [Group H] [Finite H]

omit [Finite H] in
theorem mem_normalizer_of_rightConjugate_eq {P : Subgroup H} {g : H}
    (hP : rightConjugate P g = P) : g⁻¹ ∈ Subgroup.normalizer (P : Set H) := by
  have hP' : P.map (MulAut.conj g⁻¹).toMonoidHom = P := hP
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← hP']
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← hP'] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_left_inj, mul_right_inj] at hyx
    rw [← hyx]
    exact hy

theorem centerOf_isolated (S : Sylow 2 H)
    (hwc : ∀ Z₀ : Subgroup H, Z₀ ≤ centerOf (S : Subgroup H) → WeaklyClosedIn (S : Subgroup H) Z₀)
    (a : H) (ha : a ∈ centerOf (S : Subgroup H)) (g : H)
    (hg : g⁻¹ * a * g ∈ (S : Subgroup H)) : g⁻¹ * a * g = a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let A := Subgroup.zpowers a
  have hAZ : A ≤ centerOf (S : Subgroup H) := Subgroup.zpowers_le.mpr ha
  have hconj : rightConjugate A g = Subgroup.zpowers (g⁻¹ * a * g) := by
    change A.map (MulAut.conj g⁻¹).toMonoidHom = _
    rw [MonoidHom.map_zpowers]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  have hle : rightConjugate A g ≤ (S : Subgroup H) := by
    rw [hconj, Subgroup.zpowers_le]
    exact hg
  have hA := (hwc A hAZ).2 g hle
  have hgN : g⁻¹ ∈ Subgroup.normalizer (A : Set H) := mem_normalizer_of_rightConjugate_eq hA
  let N := Subgroup.normalizer (A : Set H)
  have hA2 : IsPGroup 2 A := S.isPGroup'.to_le (hAZ.trans inf_le_left)
  have hAut := CFSG.TwoRankLowerBound.Helpers.cyclic_two_group_automorphisms_isPGroup A hA2
  have hSC : (S : Subgroup H) ≤ Subgroup.centralizer (A : Set H) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyC := (Subgroup.mem_inf.mp (hAZ hy)).2
    rw [Subgroup.mem_centralizer_iff] at hyC
    exact (hyC x hx).symm
  have hSN : (S : Subgroup H) ≤ N := hSC.trans (Subgroup.centralizer_le_normalizer _)
  have htriv := CFSG.GorensteinWalter.hom_to_pGroup_eq_one_of_sylow hAut A.normalizerMonoidHom
    (S.subtype hSN) (by
      intro s
      ext y
      have hs : ((s : N) : H) ∈ (S : Subgroup H) := by
        have h : (s : N) ∈ (S : Subgroup H).subgroupOf N := by
          rw [← Sylow.coe_subtype S hSN]
          exact s.property
        exact Subgroup.mem_subgroupOf.mp h
      have hyC := Subgroup.mem_centralizer_iff.mp (hSC hs) y y.property
      change ((s : N) : H) * (y : H) * ((s : N) : H)⁻¹ = (y : H)
      rw [← hyC]
      group) ⟨g⁻¹, hgN⟩
  have h := congrArg (fun φ : MulAut A => ((φ ⟨a, Subgroup.mem_zpowers a⟩ : A) : H)) htriv
  change g⁻¹ * a * g⁻¹⁻¹ = a at h
  rwa [inv_inv] at h

theorem IsQGroup.oddCore_sup_centralizer_center (hH : IsQGroup H) (S : Sylow 2 H) :
    CFSG.oddCore H ⊔ Subgroup.centralizer (centerOf (S : Subgroup H) : Set H) = ⊤ ∧
      (centerOf (S : Subgroup H)).map (QuotientGroup.mk' (CFSG.oddCore H)) ≤
        Subgroup.center (H ⧸ CFSG.oddCore H) := by
  obtain ⟨K, hK⟩ := hH.exists_data S
  have hiso := centerOf_isolated S hK.center_weaklyClosed
  have hcen : (centerOf (S : Subgroup H)).map (QuotientGroup.mk' (CFSG.oddCore H)) ≤
      Subgroup.center (H ⧸ CFSG.oddCore H) := by
    rintro _ ⟨a, ha, rfl⟩
    have hAZ : Subgroup.zpowers a ≤ centerOf (S : Subgroup H) := Subgroup.zpowers_le.mpr ha
    have h := CFSG.Wreathed.cyclic_weakClosure_image_central_mod_oddCore S (Subgroup.zpowers a)
      (hAZ.trans inf_le_left) (fun b hb => (Subgroup.mem_inf.mp (hAZ hb)).2)
      (fun b hb g hg => hiso b (hAZ hb) g hg)
    exact h ⟨a, Subgroup.mem_zpowers a, rfl⟩
  refine ⟨?_, hcen⟩
  have hfac := CFSG.Wreathed.weakClosure_normal_centralizer_factorization S
    (centerOf (S : Subgroup H)) (CFSG.oddCore H) inf_le_left hiso hcen
  rw [eq_top_iff]
  intro g _
  obtain ⟨r, hr, c, hc, rfl⟩ := hfac g
  exact Subgroup.mul_mem_sup hr hc

end CFSG.QuasiDihedralFusion
