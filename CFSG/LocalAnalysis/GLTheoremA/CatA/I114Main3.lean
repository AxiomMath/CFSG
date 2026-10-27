module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I114Hom
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I114Ind

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I114

open CFSG.Open

variable {Y : Type} [Group Y]

theorem zpowers_elemCommute_of {g c : Y} (h : g * c = c * g) :
    ElemCommute (Subgroup.zpowers g) (Subgroup.zpowers c) := by
  intro a ha b hb
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
  exact ((Commute.zpow_left (show Commute g c from h) i).zpow_right j).eq

theorem conj_mem_iff_of_cj {P : Subgroup Y} {g z : Y} (h : cj g P = P) :
    g * z * g⁻¹ ∈ P ↔ z ∈ P := by
  have h1 : g * z * g⁻¹ ∈ cj g P ↔ z ∈ P := by
    rw [mem_cj]
    have e : g⁻¹ * (g * z * g⁻¹) * g = z := by group
    rw [e]
  rw [h] at h1
  exact h1

theorem cj_map_eq {K : Subgroup Y} {m : Y} (hm : m ∈ Subgroup.normalizer (K : Set Y))
    {U : Subgroup ↥K} (h1 : U.map (MulEquiv.toMonoidHom (actK K m hm)) = U)
    (h2 : U.map (MulEquiv.toMonoidHom (actK K m⁻¹ ((Subgroup.normalizer _).inv_mem hm))) = U) :
    cj m (U.map K.subtype) = U.map K.subtype := by
  ext z
  rw [mem_cj, Subgroup.mem_map, Subgroup.mem_map]
  constructor
  · rintro ⟨u, hu, hue⟩
    have hv : (MulEquiv.toMonoidHom (actK K m hm)) u ∈ U := by
      rw [← h1]
      exact Subgroup.mem_map_of_mem _ hu
    refine ⟨(MulEquiv.toMonoidHom (actK K m hm)) u, hv, ?_⟩
    show ((actK K m hm u : ↥K) : Y) = z
    rw [actK_apply]
    have hu' : (u : Y) = m⁻¹ * z * m := hue
    rw [hu']
    group
  · rintro ⟨v, hv, hvz⟩
    have hw : (MulEquiv.toMonoidHom (actK K m⁻¹ ((Subgroup.normalizer _).inv_mem hm))) v ∈ U := by
      rw [← h2]
      exact Subgroup.mem_map_of_mem _ hv
    refine ⟨(MulEquiv.toMonoidHom (actK K m⁻¹ ((Subgroup.normalizer _).inv_mem hm))) v, hw, ?_⟩
    show ((actK K m⁻¹ ((Subgroup.normalizer _).inv_mem hm) v : ↥K) : Y) = m⁻¹ * z * m
    rw [actK_apply]
    have hv' : (v : Y) = z := hvz
    rw [hv', inv_inv]

theorem outer_key {K : Subgroup Y} {β n m a g k : Y} (hβK : Cent K β)
    (hn : n ∈ Subgroup.normalizer (K : Set Y)) (hmK : Cent K m) (hkK : k ∈ K)
    (hgn : g = β * n) (hga : g = a * m) : n * k * n⁻¹ = a * k * a⁻¹ := by
  have hnk : n * k * n⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 hn k).1 hkK
  have hβc : β * (n * k * n⁻¹) = (n * k * n⁻¹) * β := (hβK _ hnk).symm
  have h1 : g * k * g⁻¹ = n * k * n⁻¹ := by
    rw [hgn]
    calc β * n * k * (β * n)⁻¹ = β * (n * k * n⁻¹) * β⁻¹ := by group
      _ = n * k * n⁻¹ := by rw [hβc]; group
  have hmk : m * k = k * m := (hmK k hkK).symm
  have h2 : g * k * g⁻¹ = a * k * a⁻¹ := by
    rw [hga]
    calc a * m * k * (a * m)⁻¹ = a * (m * k * m⁻¹) * a⁻¹ := by group
      _ = a * k * a⁻¹ := by rw [hmk]; group
  exact h1.symm.trans h2

end CFSG.LocalAnalysis.GLTheoremA.I114
