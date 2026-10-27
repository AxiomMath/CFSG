module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutGamma.AutS7
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutGamma.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutGamma.CentS7

public section

namespace CFSG.EvenSporadicStandard.HNRecog.AutGamma

open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3

variable {G : Type} [Group G] {a z : G}

theorem eq_or_eq_conj_of_centralizes [Finite G] (hF : IsF5Type a z) (hL : F5Local G a z)
    {x y : G} (hx : x ∈ orb3A a a) (hy : y ∈ orb3A a a)
    (hc : ∀ s ∈ Gxy a x, y * s = s * y) : y = x ∨ y = a * x * a := by
  classical
  set S : Subgroup G := Gxy a x with hSdef
  have hSGa : S ≤ Gx a := by
    intro t ht
    rw [hSdef] at ht
    exact (mem_Gxy.mp ht).1
  have hS_le : S ≤ Gxy a y := by
    intro s hs
    rw [hSdef] at hs
    rw [mem_Gxy] at hs ⊢
    refine ⟨hs.1, ?_⟩
    exact mem_Gx.mpr (hc s (mem_Gxy.mpr hs))
  have hcardS : Nat.card ↥S = 5040 := by
    rw [hSdef, Gxy_eq_inf]
    exact hL.tableVII.self.card_3A x hx
  have hcardY : Nat.card ↥(Gxy a y) = 5040 := by
    rw [Gxy_eq_inf]
    exact hL.tableVII.self.card_3A y hy
  have hSy : S = Gxy a y :=
    Subgroup.eq_of_le_of_card_ge hS_le (by rw [hcardY, hcardS])
  obtain ⟨g, hgGa, hgx⟩ := hL.s7.self.orbit.transitive x hx y hy
  have hgnorm : ∀ t ∈ S, g * t * g⁻¹ ∈ S := by
    intro t ht
    rw [hSy, mem_Gxy]
    rw [hSdef] at ht
    rw [mem_Gxy] at ht
    refine ⟨?_, ?_⟩
    · exact (Gx a).mul_mem ((Gx a).mul_mem hgGa ht.1) ((Gx a).inv_mem hgGa)
    · have hxt : x * t = t * x := mem_Gx.mp ht.2
      rw [mem_Gx, ← hgx]
      calc (g * x * g⁻¹) * (g * t * g⁻¹) = g * (x * t) * g⁻¹ := by group
        _ = g * (t * x) * g⁻¹ := by rw [hxt]
        _ = (g * t * g⁻¹) * (g * x * g⁻¹) := by group
  have hSshape : IsShapeSym 7 ↥S := by
    rw [hSdef]
    exact hL.s7.self.shape x hx
  obtain ⟨s, hsS, hsconj⟩ := exists_inner_of_normalizes hSshape hgnorm
  have hsGa : s ∈ Gx a := hSGa hsS
  have hsGx : s ∈ Gx x := by
    rw [hSdef] at hsS
    exact (mem_Gxy.mp hsS).2
  let g' : G := s⁻¹ * g
  have hg'Ga : g' ∈ Gx a := (Gx a).mul_mem ((Gx a).inv_mem hsGa) hgGa
  have hg'comm : ∀ t ∈ S, g' * t = t * g' := by
    intro t ht
    have hconj : g' * t * g'⁻¹ = t := by
      have h := hsconj t ht
      calc g' * t * g'⁻¹ = s⁻¹ * (g * t * g⁻¹) * s := by
            simp only [g']; group
        _ = s⁻¹ * (s * t * s⁻¹) * s := by rw [h]
        _ = t := by group
    calc g' * t = (g' * t * g'⁻¹) * g' := by group
      _ = t * g' := by rw [hconj]
  have hg'z : g' ∈ Subgroup.zpowers a :=
    mem_zpowers_of_centralizes_sym7_of_f5Local hL hSGa hSshape hg'Ga hg'comm
  have hg'_cases : g' = 1 ∨ g' = a := by
    rw [Subgroup.mem_zpowers_iff] at hg'z
    obtain ⟨n, hn⟩ := hg'z
    have hmod : n % (orderOf a : ℤ) = 0 ∨ n % (orderOf a : ℤ) = 1 := by
      rw [hF.orderOf_a]
      simpa using Int.emod_two_eq_zero_or_one n
    rw [← hn, ← zpow_mod_orderOf a n]
    rcases hmod with h | h
    · left; rw [h]; simp
    · right; rw [h]; simp
  have hg_eq : g = s * g' := by
    simp only [g']; group
  rcases hg'_cases with h1 | ha
  · left
    have hsx : s * x = x * s := (mem_Gx.mp hsGx).symm
    rw [← hgx, hg_eq, h1]
    calc (s * 1) * x * (s * 1)⁻¹ = s * x * s⁻¹ := by group
      _ = x := by rw [hsx]; group
  · right
    have hsa : a * s = s * a := mem_Gx.mp hsGa
    have hsx : s * x = x * s := (mem_Gx.mp hsGx).symm
    have ha2 : a * a = 1 := mul_self_of_isConj hF (IsConj.refl a)
    have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
    have hcomm : s * (a * x * a) = (a * x * a) * s := by
      calc s * (a * x * a) = (s * a) * x * a := by group
        _ = (a * s) * x * a := by rw [← hsa]
        _ = a * (s * x) * a := by group
        _ = a * (x * s) * a := by rw [← hsx]
        _ = a * x * (s * a) := by group
        _ = a * x * (a * s) := by rw [← hsa]
        _ = (a * x * a) * s := by group
    rw [← hgx, hg_eq, ha]
    calc (s * a) * x * (s * a)⁻¹ = s * (a * x * a) * s⁻¹ := by
          rw [mul_inv_rev, hai]; group
      _ = (a * x * a) * s * s⁻¹ := by rw [hcomm]
      _ = a * x * a := by group

end CFSG.EvenSporadicStandard.HNRecog.AutGamma
