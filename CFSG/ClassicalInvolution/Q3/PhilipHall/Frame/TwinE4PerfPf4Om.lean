module

public import CFSG.ClassicalInvolution.Q3.TL4VtxE4O8D
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinE4PerfPf2Fin

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinE4O8

open CFSG.ClassicalInvolution.Q3.TL4 CFSG.ClassicalInvolution.Q3.TL4.E4O8
open CFSG.EvenSmallLie.OmegaEight CFSG.Certificates CFSG.Certificates.Native
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Q3.TL4.E4O8Data
open CFSG.ClassicalInvolution.Q3.TL4.E4A CFSG.ClassicalInvolution.Q3.TL4.E4C
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinE4Perf

set_option linter.unusedSectionVars false

theorem acts_of_normalizing {M : Type} [Group M] {K : Subgroup M} {t : M}
    (hinv : IsUniqueInvolution K t) {x : M} (hx3 : x ^ 3 = 1) (hxK : ∀ r ∈ K, x * r * x⁻¹ ∈ K)
    {k : M} (hk : k ∈ K) (hnc : x * k ≠ k * x) :
    x * t = t * x ∧ (∀ r ∈ K, x * r * x⁻¹ ∈ K) ∧
      ∃ r ∈ K, x * r * x⁻¹ * r⁻¹ ≠ 1 ∧ x * r * x⁻¹ * r⁻¹ ≠ t := by
  have hxxx : x * x * x = 1 := by rw [← pow_three']; exact hx3
  have hxt : x * t * x⁻¹ = t := by
    have hu := hxK t hinv.mem
    have hsq : x * t * x⁻¹ * (x * t * x⁻¹) = 1 := by
      calc x * t * x⁻¹ * (x * t * x⁻¹) = x * (t * t) * x⁻¹ := by group
        _ = 1 := by rw [hinv.sq]; group
    rcases hinv.unique _ hu hsq with h | h
    · exfalso
      apply hinv.ne_one
      calc t = x⁻¹ * (x * t * x⁻¹) * x := by group
        _ = 1 := by rw [h]; group
    · exact h
  refine ⟨?_, hxK, k, hk, ?_, ?_⟩
  · calc x * t = (x * t * x⁻¹) * x := by group
      _ = t * x := by rw [hxt]
  · intro h
    apply hnc
    have h1 : x * k * x⁻¹ = k := mul_inv_eq_one.1 h
    calc x * k = (x * k * x⁻¹) * x := by group
      _ = k * x := by rw [h1]
  · intro h
    have h1 : x * k * x⁻¹ = t * k := mul_inv_eq_iff_eq_mul.1 h
    have h2 : x * (t * k) * x⁻¹ = k := by
      calc x * (t * k) * x⁻¹ = (x * t * x⁻¹) * (x * k * x⁻¹) := by group
        _ = (t * t) * k := by rw [hxt, h1]; group
        _ = k := by rw [hinv.sq]; group
    have h3 : k = t * k := by
      calc k = (x * x * x) * k * (x * x * x)⁻¹ := by rw [hxxx]; group
        _ = x * (x * (x * k * x⁻¹) * x⁻¹) * x⁻¹ := by group
        _ = t * k := by rw [h1, h2]; exact h1
    apply hinv.ne_one
    have : t * k = 1 * k := by rw [← h3, one_mul]
    exact mul_right_cancel this


theorem fin3ActsOm_of_certs : Fin3ActsOm := by
  intro Q _ _ hQ K t hq hinv htw
  obtain ⟨e⟩ := nonempty_mulEquiv_omegaT hQ
  have hinj := emb_injective e
  obtain ⟨eR⟩ := hq
  have hd : Vtx.AmbientQuatDatum omegaT (K.map (emb e)) (emb e t) := by
    rw [← range_emb e]
    refine ⟨Subgroup.map_le_range _ K, ⟨(K.equivMapOfInjective _ hinj).symm.trans eR⟩,
      Vtx.isUniqueInvolution_map _ hinj hinv, ?_⟩
    rintro _ ⟨m, rfl⟩ hms
    have hm : m ∈ Subgroup.centralizer ({t} : Set Q) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hinj (by rw [map_mul, map_mul, hms])
    rw [conjSub_map]
    rcases htw m hm with h | h
    · left
      rw [h]
    · right
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul, h x hx y hy]
  obtain ⟨g, hg, hgK⟩ := ident_omega hd
  obtain ⟨h3, hK3, hnc⟩ := three_facts
  have hthree : three ∈ omegaT := three_spec.2
  have hxmem : g⁻¹ * three * g ∈ omegaT :=
    omegaT.mul_mem (omegaT.mul_mem (omegaT.inv_mem hg) hthree) hg
  obtain ⟨m, hm⟩ : ∃ m, emb e m = g⁻¹ * three * g := by
    rw [← range_emb e] at hxmem; exact hxmem
  have hback : ∀ y ∈ K0, g⁻¹ * y * g ∈ K.map (emb e) := fun y hy => by
    have : y ∈ conjSub g (K.map (emb e)) := hgK ▸ hy
    rwa [mem_conjSub_iff] at this
  have hthreeK : ∀ y ∈ K0, three * y * three⁻¹ ∈ K0 := fun y hy => by
    have : three * y * three⁻¹ ∈ conjSub three K0 := conj_mem_conjSub hy
    rwa [hK3] at this
  have hm3 : m ^ 3 = 1 := by
    apply hinj
    rw [map_pow, hm, map_one]
    calc (g⁻¹ * three * g) ^ 3 = (g⁻¹ * three * g) * (g⁻¹ * three * g) * (g⁻¹ * three * g) :=
          pow_three' _
      _ = g⁻¹ * (three * three * three) * g := by group
      _ = 1 := by rw [← pow_three', h3]; group
  have hmK : ∀ r ∈ K, m * r * m⁻¹ ∈ K := by
    intro r hr
    have h1 : g * emb e r * g⁻¹ ∈ K0 := hgK ▸ conj_mem_conjSub (Subgroup.mem_map_of_mem _ hr)
    have h2 := hback _ (hthreeK _ h1)
    rw [show g⁻¹ * (three * (g * emb e r * g⁻¹) * three⁻¹) * g =
      (g⁻¹ * three * g) * emb e r * (g⁻¹ * three * g)⁻¹ by group, ← hm] at h2
    obtain ⟨r', hr', hr'e⟩ := h2
    have : m * r * m⁻¹ = r' := hinj (by rw [map_mul, map_mul, map_inv, hr'e])
    rw [this]
    exact hr'
  obtain ⟨r0, hr0, hr0e⟩ := hback u0 (Subgroup.subset_closure (Set.mem_insert _ _))
  have hnc' : m * r0 ≠ r0 * m := by
    intro h
    apply hnc
    have := congrArg (emb e) h
    rw [map_mul, map_mul, hm, hr0e] at this
    calc three * u0 = g * (g⁻¹ * three * g * (g⁻¹ * u0 * g)) * g⁻¹ := by group
      _ = g * (g⁻¹ * u0 * g * (g⁻¹ * three * g)) * g⁻¹ := by rw [this]
      _ = u0 * three := by group
  obtain ⟨hxt, -, r, hr, h1, h2⟩ := acts_of_normalizing hinv hm3 hmK hr0 hnc'
  exact ⟨m, hxt, hm3, hmK, r, hr, h1, h2⟩

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinE4O8
