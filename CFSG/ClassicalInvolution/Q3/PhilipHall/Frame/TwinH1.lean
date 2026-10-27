module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinMaxOrb

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC CFSG.ClassicalInvolution.Q3.TC.Graph
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

section General

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem OrbitStd.noCentralInv (hs : OrbitStd Ω) {K : Subgroup G} {π : Set (Subgroup G)}
    (hπ : π ∈ maxOrbs (nbrAdj Ω) K) {z : G} (hz : IsUniqueInvolution K z)
    (htrans : ∀ J ∈ Ω, ∃ g : G, conjSub g K = J)
    (hgen : ∀ g : G, conjSub g K ∈ π → (⨆ M ∈ π ∪ conjSub g '' π, M) = ⊤)
    (hZ : Subgroup.center G = ⊥) : NoCentralInv π := by
  intro J hJ u hu hc
  have hJΩ : J ∈ Ω := hs.graph.mem (hs.graph.graph.symm (adj_of_mem_isMaxOrb hs.graph hπ hJ))
  obtain ⟨g, rfl⟩ := htrans J hJΩ
  have hug : u = g * z * g⁻¹ := hu.eq (hz.conj g)
  have hXz := hs.piGen_le_centralizer hπ hz
  have hle : (⨆ M ∈ π ∪ conjSub g '' π, M) ≤ Subgroup.centralizer ({u} : Set G) := by
    refine iSup₂_le fun M hM => ?_
    rcases hM with hM | ⟨M', hM', rfl⟩
    · intro x hx
      exact Subgroup.mem_centralizer_singleton_iff.mpr (hc x (le_piGen hM hx))
    · intro x hx
      rw [mem_conjSub_iff] at hx
      have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hXz (le_piGen hM' hx))
      rw [Subgroup.mem_centralizer_singleton_iff, hug]
      calc x * (g * z * g⁻¹) = g * ((g⁻¹ * x * g) * z) * g⁻¹ := by group
        _ = g * (z * (g⁻¹ * x * g)) * g⁻¹ := by rw [h1]
        _ = g * z * g⁻¹ * x := by group
  rw [hgen g hJ] at hle
  have hcen : u ∈ Subgroup.center G := Subgroup.mem_center_iff.mpr fun x =>
    Subgroup.mem_centralizer_singleton_iff.mp (hle (Subgroup.mem_top x))
  rw [hZ, Subgroup.mem_bot] at hcen
  exact hu.ne_one hcen

end General

section Twin

variable {G : Type} [Group G] [Finite G] {K₀ : Subgroup G}

theorem twin_noCentralInv (hs : TwinGraphStd K₀) (hZ : Subgroup.center G = ⊥) {K K' : Subgroup G}
    (hK : K ∈ CoreAssembly.conjClass K₀) (hK' : K' ∈ CoreAssembly.conjClass K₀) (hne : K' ≠ K)
    {z : G} (hz : IsUniqueInvolution K z) :
    ∃ π, maxOrbs (nbrAdj (CoreAssembly.conjClass K₀)) K = {π} ∧
      Lemma1710 (nbrAdj (CoreAssembly.conjClass K₀)) (CoreAssembly.conjClass K₀) K π ∧
      NoCentralInv π := by
  obtain ⟨π, h1, h2⟩ := twin_17_10 hs hK hK' hne
  have hπ : π ∈ maxOrbs (nbrAdj (CoreAssembly.conjClass K₀)) K := by rw [h1]; rfl
  refine ⟨π, h1, h2, hs.orbitStd.noCentralInv hπ hz ?_ (h2.generate (iSup_conjClass_eq_top hs.gen))
    hZ⟩
  rintro J ⟨b, rfl⟩
  obtain ⟨a, rfl⟩ := hK
  refine ⟨b * a⁻¹, ?_⟩
  ext x
  simp only [mem_conjSub_iff]
  rw [show a⁻¹ * ((b * a⁻¹)⁻¹ * x * (b * a⁻¹)) * a = b⁻¹ * x * b by group]

end Twin

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
