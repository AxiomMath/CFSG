module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWDefs
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWCore

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge

namespace TwinThmEW
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE

section Base


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G}
  {S : Sylow 2 G} {R W H : Subgroup G}

theorem MinCexQ8.exists_zW (c : MinCexQ8 Ω K S R W H) :
    ∃ z : G, IsUniqueInvolution K z ∧ z ∈ W :=
  exists_zW' c.stand.hyp c.stand.mem c.stand.hR.1 c.stand.hR.2.1 c.stand.hR.2.2 c.stand.hW.1
    c.stand.hW.2.1

theorem MinCexQ8.centralizer_le (c : MinCexQ8 Ω K S R W H) {z : G}
    (hz : IsUniqueInvolution K z) : Subgroup.centralizer ({z} : Set G) ≤ H :=
  centralizer_le_of_hyp c.stand.hyp c.stand.mem c.stand.hR.1 c.stand.hR.2.1 c.stand.hR.2.2
    c.stand.hW.1 c.stand.hW.2.1 c.hyp.cent hz

theorem MinCexQ8.exists_centralizer_le (c : MinCexQ8 Ω K S R W H) :
    ∃ z : G, IsUniqueInvolution K z ∧ Subgroup.centralizer ({z} : Set G) ≤ H := by
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution c.stand.hyp c.stand.mem
  exact ⟨z, hz, c.centralizer_le hz⟩

theorem e18_1Q8 : E18_1Q8 := by
  intro G _ _ Ω K S R W H c
  obtain ⟨z, hz, hcz⟩ := c.exists_centralizer_le
  have key : ∀ g : G, conjSub g K ∈ dstarComp Ω K → g ∈ H := by
    intro g hg
    obtain ⟨h, hhH, hh⟩ := c.hyp.trans _ hg
    have hn : conjSub (h⁻¹ * g) K = K := by
      rw [conjSub_mul, ← hh, conjSub_inv_conjSub]
    have hcent : h⁻¹ * g ∈ Subgroup.centralizer ({z} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact mul_inv_eq_iff_eq_mul.mp (hz.conj_eq hn)
    have hg' : g = h * (h⁻¹ * g) := by group
    rw [hg']
    exact H.mul_mem hhH (hcz hcent)
  refine ⟨key, ?_⟩
  by_contra hno
  push Not at hno
  apply c.proper
  rw [eq_top_iff]
  intro g _
  exact key g (hno _ (c.stand.hyp.conjInvariant g K c.stand.mem))

theorem e18_3Q8 : E18_3Q8 := by
  intro G _ _ Ω K S R W H c J hJ
  have hΩ : HypOmegaGen Ω := c.stand.hyp
  have hΩc := hΩ.conjInvariant
  have hK : K ∈ Ω := c.stand.mem
  obtain ⟨hRR, hRK, hRS⟩ := c.stand.hR
  obtain ⟨RJ, hRJmem, hRJ, -⟩ :=
    exists_mem_RSet_ge hJ (IsPGroup.of_bot : IsPGroup 2 (⊥ : Subgroup G)) bot_le
  obtain ⟨Q, hQ⟩ := IsPGroup.exists_le_sylow hRJ.2.1
  obtain ⟨y, hy⟩ := exists_conjSub_eq_of_sylow S Q
  set J' : Subgroup G := conjSub y⁻¹ J with hJ'def
  set R' : Subgroup G := conjSub y⁻¹ RJ with hR'def
  have hJ'Ω : J' ∈ Ω := hΩc y⁻¹ J hJ
  have hR'mem : R' ∈ RSet Ω := RSet.conj hΩc hRJmem y⁻¹
  have hR'J : IsSylow2In R' J' := hRJ.conj y⁻¹
  have hR'S : R' ≤ (S : Subgroup G) := by
    have h1 : RJ ≤ conjSub y (S : Subgroup G) := hy ▸ hQ
    have := conjSub_mono (n := y⁻¹) h1
    rwa [conjSub_inv_conjSub] at this
  have key : J' ∈ dstarComp Ω K := by
    by_cases hJK : J' = K
    · rw [hJK]
      exact Relation.ReflTransGen.refl
    obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution hΩ hK
    have hR2 : IsPGroup 2 R := by
      obtain ⟨J₀, -, -, h2, -⟩ := mem_RSet_iff.mp hRR
      exact h2
    have h8 := Sec6Gen.eight_le_of_mem_RSet hΩ hRR
    have h8' := Sec6Gen.eight_le_of_mem_RSet hΩ hR'mem
    have hRne : R ≠ R' := by
      intro hRR'
      exact hJK (Sec6Gen.eq_of_le_of_le hΩ hJ'Ω hK hR2 (by omega) (hRR' ▸ hR'J.1) hRK)
    have hcomm : Commutes R R' := Q3CP.l67Gen G Ω hΩ S R hRR R' hR'mem hRS hR'S hRne
    have hzR : z ∈ R := mem_of_isUniqueInvolution_of_isPGroup hz hRK hR2 (by omega)
    have hR'c : R' ≤ Subgroup.centralizer ({z} : Set G) := fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hcomm z hzR x hx).symm
    have hR'N : R' ≤ Subgroup.normalizer (K : Set G) :=
      Sec6Gen.le_normalizer_of_le_centralizer hΩ hK hJ'Ω (Ne.symm hJK) hz hR'J.1 hR'J.2.1
        (by omega) hR'c
    obtain ⟨U, hUR, hUcyc, hUcard⟩ :=
      (Sec6Gen.isQuatSub_of_mem_RSet hΩ hR'mem).exists_cyclic_index_two
    have hU : U ∈ USet Ω := mem_USet_of_natCard hJ'Ω hR'J hUR hUcyc hUcard
    exact Relation.ReflTransGen.single ⟨hJ'Ω, Or.inl ⟨hJ'Ω, hJK, U, hU, hUR.trans hR'J.1,
      hUR.trans hR'N⟩⟩
  obtain ⟨h, -, hh⟩ := c.hyp.trans J' key
  refine ⟨y * h, ?_⟩
  rw [conjSub_mul, hh]
  exact conjSub_conjSub_inv y J

theorem e18_8zQ8_of_e18_7 (h : E18_7Q8) : E18_8zQ8 := by
  intro G _ _ Ω K S R W H c a hz
  have ha1 : a ≠ 1 := hz.ne_one
  have ha2 : a * a = 1 := hz.sq
  have hcent : Subgroup.centralizer ({a} : Set G) ≤ H := c.centralizer_le hz
  have haH : a ∈ H := hcent (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  have h7 := h G Ω K S R W H c a ha1 ha2 hcent
  refine ⟨(1 : G) , ?_, ?_⟩
  · show a • ((1 : G) : G ⧸ H) = ((1 : G) : G ⧸ H)
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
    exact QuotientGroup.eq.mpr (by simpa using H.inv_mem haH)
  · intro c' hc'
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c'
    have hg : g⁻¹ * a * g ∈ H := by
      have h1 : a • ((g : G) : G ⧸ H) = (g : G ⧸ H) := hc'
      rw [MulAction.Quotient.smul_mk, smul_eq_mul] at h1
      have h2 := QuotientGroup.eq.mp h1
      have : (a * g)⁻¹ * g = g⁻¹ * a⁻¹ * g := by group
      have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
      rw [this, ha'] at h2
      exact h2
    obtain ⟨k, hk, hka⟩ := h7 g⁻¹ (by simpa using hg)
    have hgk : g * k ∈ Subgroup.centralizer ({a} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h3 : k * a * k⁻¹ = g⁻¹ * a * g := by simpa using hka
      calc (g * k) * a = (g * (k * a * k⁻¹)) * k := by group
        _ = a * (g * k) := by rw [h3]; group
    have : g ∈ H := by
      have h4 : g * k * k⁻¹ ∈ H := H.mul_mem (hcent hgk) (H.inv_mem hk)
      simpa using h4
    exact (QuotientGroup.eq.mpr (by simpa using H.inv_mem this)).symm

end Base

end TwinThmEW

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
