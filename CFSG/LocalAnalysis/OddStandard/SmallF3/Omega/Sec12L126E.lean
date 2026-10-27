module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L126Cm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L126U
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L126Nc
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L126Base
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4L46

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec126_V_normalizes {V : Subgroup G} {s : G} (hV : CFSG.Open.IsElemAbelian 2 V)
    (hs2 : s * s = 1) (hsN : s ∈ normalizer (V : Set G)) :
    V ≤ normalizer ((V ⊓ centralizer ({s} : Set G) ⊔ zpowers s : Subgroup G) : Set G) := by
  set D : Subgroup G := V ⊓ centralizer ({s} : Set G) with hD_def
  have hDV : D ≤ V := inf_le_left
  have hsCD : s ∈ centralizer (D : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hd).2
  have hsND : s ∈ normalizer (D : Set G) := Subgroup.centralizer_le_normalizer _ hsCD
  have hVF : ∀ v ∈ V, ∀ y ∈ D ⊔ zpowers s, v * y * v⁻¹ ∈ D ⊔ zpowers s := by
    intro v hv y hy
    rcases sec126_mem_sup_zpowers hsND hs2 hy with hyD | ⟨d, hd, rfl⟩
    · have hvy : v * y = y * v := hV.comm hv (hDV hyD)
      have : v * y * v⁻¹ = y := by
        calc v * y * v⁻¹ = y * v * v⁻¹ := by rw [hvy]
          _ = y := by group
      rw [this]
      exact Subgroup.mem_sup_left hyD
    · obtain ⟨d', hd', hvs⟩ := sec126_conj_mem hV hs2 hsN hv
      have hvd : v * d = d * v := hV.comm hv (hDV hd)
      have : v * (d * s) * v⁻¹ = d * d' * s := by
        calc v * (d * s) * v⁻¹ = (v * d) * s * v⁻¹ := by group
          _ = d * (v * s * v⁻¹) := by rw [hvd]; group
          _ = d * (d' * s) := by rw [hvs]
          _ = d * d' * s := by group
      rw [this]
      exact mul_mem (mul_mem (Subgroup.mem_sup_left hd) (Subgroup.mem_sup_left hd'))
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers s))
  intro v hv
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact hVF v hv y
  · intro hy
    have := hVF v⁻¹ (V.inv_mem hv) _ hy
    simpa [mul_assoc] using this

theorem sec126_exists_h2 [Finite G] {g : G} {A B V E : Subgroup G}
    (hV : CFSG.Open.IsElemAbelian 2 V)
    (hE : IsSylow2Of E (normalizer (A : Set G) ⊓ centralizer (B : Set G)))
    (hVN : V ≤ normalizer (CFSG.conjugate A g : Set G))
    (hVC : V ≤ centralizer (CFSG.conjugate B g : Set G)) :
    ∃ p ∈ normalizer (A : Set G) ⊓ centralizer (B : Set G),
      ∀ v ∈ V, (p * g) * v * (p * g)⁻¹ ∈ E := by
  have hKP : CFSG.conjugate V g⁻¹ ≤ normalizer (A : Set G) ⊓ centralizer (B : Set G) := by
    intro x hx
    rw [mem_conjugate_iff, inv_inv] at hx
    have hx' : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have := sec126_mem_normalizer_conjugate_iff.mp (hVN hx)
      rwa [← hx'] at this
    · have := sec126_mem_centralizer_conjugate_iff.mp (hVC hx)
      rwa [← hx'] at this
  have hK : IsPGroup 2 (CFSG.conjugate V g⁻¹) :=
    (sec4_isElemAbelian_conjugate hV g⁻¹).isPGroup
  obtain ⟨p, hpP, hp⟩ := sec126_exists_conj_le hE hK hKP
  refine ⟨p, hpP, fun v hv => ?_⟩
  have hvK : g * v * g⁻¹ ∈ CFSG.conjugate V g⁻¹ := by
    rw [mem_conjugate_iff, inv_inv]
    have : g⁻¹ * (g * v * g⁻¹) * g = v := by group
    rw [this]
    exact hv
  have := hp _ hvK
  have e : p * (g * v * g⁻¹) * p⁻¹ = (p * g) * v * (p * g)⁻¹ := by group
  rwa [e] at this

end CFSG.OddStandard.SmallF3.Omega
