module

public import CFSG.ClassicalInvolution.Q3.Sec13L711Sys

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

namespace Q8Omega

structure IsSys (Ω : Set (Subgroup G)) (σ : Set (Subgroup G)) : Prop where
  mem : ∀ V ∈ σ, V ∈ USet Ω
  distinct : InDistinctMembers Ω σ
  comm : ∀ a ∈ (⨆ V ∈ σ, V : Subgroup G), ∀ b ∈ (⨆ V ∈ σ, V : Subgroup G), a * b = b * a

variable (hΩ : Q8Omega Ω)
include hΩ

theorem isSys_of_eta {η : Set (Subgroup G)} (hη : η ∈ etaG Ω) : IsSys Ω η :=
  ⟨fun _ hV => hΩ.mem_USet_of_mem_eta hη hV, hη.choose_spec.1.2.1, hΩ.W_comm hη⟩

namespace IsSys

variable {σ : Set (Subgroup G)} (hσ : IsSys Ω σ)
include hσ

omit hΩ in
theorem le_span {V : Subgroup G} (hV : V ∈ σ) : V ≤ (⨆ V ∈ σ, V : Subgroup G) :=
  le_biSup (fun V => V) hV

theorem le_normalizer_member {K U : Subgroup G} (hK : K ∈ Ω) (hU : U ∈ σ) (hUK : U ≤ K)
    {V : Subgroup G} (hV : V ∈ σ) : V ≤ Subgroup.normalizer (K : Set G) := by
  by_cases hVK : V ≤ K
  · exact hVK.trans Subgroup.le_normalizer
  obtain ⟨J, hJ, hVJ⟩ := Sec6Gen.exists_member_of_mem_USet hΩ.hyp (hσ.mem V hV)
  have hJK : K ≠ J := fun h => hVK (h ▸ hVJ)
  obtain ⟨z, hz⟩ := hΩ.exists_uniqueInvolution hK
  have hzU : z ∈ U :=
    AscL62.mem_of_index_two (hΩ.isQuatSub hK) hz hUK
      (Q8Omega.natCard_eq_two_mul hΩ hK (hσ.mem U hU) hUK)
  have hVc : V ≤ Subgroup.centralizer ({z} : Set G) := fun v hv =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (hσ.comm v (le_span hσ hV hv) z (le_span hσ hU hzU))
  have hV4 := hΩ.natCard_of_mem_USet (hσ.mem V hV)
  exact Sec6Gen.le_normalizer_of_le_centralizer hΩ.hyp hK hJ hJK hz hVJ
    (hΩ.isPGroup_of_mem_USet (hσ.mem V hV)) (by omega) hVc

theorem commutator_mem_of_mem {K U : Subgroup G} (hK : K ∈ Ω) (hU : U ∈ σ) (hUK : U ≤ K)
    {V : Subgroup G} (hV : V ∈ σ) {v k : G} (hv : v ∈ V) (hk : k ∈ K) :
    v * k * v⁻¹ * k⁻¹ ∈ U := by
  have hUU := hσ.mem U hU
  have hvN : v ∈ Subgroup.normalizer (K : Set G) := hσ.le_normalizer_member hΩ hK hU hUK hV hv
  have hvkK : v * k * v⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hvN k).mp hk
  have hvc : ∀ u ∈ U, v * u = u * v := fun u hu =>
    hσ.comm v (le_span hσ hV hv) u (le_span hσ hU hu)
  by_cases hkU : k ∈ U
  · have : v * k * v⁻¹ * k⁻¹ = 1 := by rw [hvc k hkU]; group
    rw [this]; exact U.one_mem
  · have hvkU : v * k * v⁻¹ ∉ U := by
      intro h
      apply hkU
      have h1 : v⁻¹ * (v * k * v⁻¹) * v ∈ U := by
        have e : v⁻¹ * (v * k * v⁻¹) * v = v * k * v⁻¹ := by
          have h2 := hvc _ h
          calc v⁻¹ * (v * k * v⁻¹) * v = v⁻¹ * ((v * k * v⁻¹) * v) := by group
            _ = v⁻¹ * (v * (v * k * v⁻¹)) := by rw [← h2]
            _ = v * k * v⁻¹ := by group
        rw [e]; exact h
      simpa [mul_assoc] using h1
    have hc : k⁻¹ * (v * k * v⁻¹) ∈ U :=
      AscL62.inv_mul_mem_of_index_two hUK (Q8Omega.natCard_eq_two_mul hΩ hK hUU hUK) hk hvkK
        hkU hvkU
    have hkN : k ∈ Subgroup.normalizer (U : Set G) := Q8Omega.le_normalizer_of_le hΩ hK hUU hUK hk
    have h3 := (Subgroup.mem_normalizer_iff.mp hkN _).mp hc
    have e : k * (k⁻¹ * (v * k * v⁻¹)) * k⁻¹ = v * k * v⁻¹ * k⁻¹ := by group
    rw [e] at h3
    exact h3

theorem le_normalizer_span {K U : Subgroup G} (hK : K ∈ Ω) (hU : U ∈ σ) (hUK : U ≤ K) :
    K ≤ Subgroup.normalizer ((⨆ V ∈ σ, V : Subgroup G) : Set G) := by
  have hUU := hσ.mem U hU
  intro k hk
  rw [mem_normalizer_iff_conjSub_eq]
  refine Q8Omega.conjSub_eq_of_le ?_
  rw [conjSub_iSup₂]
  refine iSup₂_le fun V hV => ?_
  intro x hx
  rw [mem_conjSub_iff] at hx
  set v := k⁻¹ * x * k with hvdef
  have hxv : x = k * v * k⁻¹ := by rw [hvdef]; group
  rw [hxv]
  by_cases hVU : V = U
  · subst hVU
    have := (Subgroup.mem_normalizer_iff.mp (Q8Omega.le_normalizer_of_le hΩ hK hUU hUK hk) v).mp hx
    exact le_span hσ hU this
  ·
    have hc := hσ.commutator_mem_of_mem hΩ hK hU hUK hV hx hk
    have e : k * v * k⁻¹ = (v * k * v⁻¹ * k⁻¹)⁻¹ * v := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (le_span hσ hU hc)) (le_span hσ hV hx)

end IsSys

end Q8Omega

end CFSG.ClassicalInvolution.Q3.Sec13
