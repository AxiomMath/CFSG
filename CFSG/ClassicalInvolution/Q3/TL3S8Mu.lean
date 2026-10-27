module

public import CFSG.ClassicalInvolution.Q3.TL3S8Std
public import CFSG.ClassicalInvolution.Q3.Q3T6OpenMuTab
public import CFSG.ClassicalInvolution.AschTight.S1911Basic

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

variable {G : Type} [Group G] [Finite G] {R : Subgroup G} {S : Sylow 2 R} {t : G}

namespace TightDatum

variable (hd : TightDatum R S t)
include hd

theorem conjSub_eq_conjSub {a b : G} (h : a * t * a⁻¹ = b * t * b⁻¹) :
    conjSub a (tightCore R) = conjSub b (tightCore R) := by
  have hn : b⁻¹ * a ∈ Subgroup.normalizer (tightCore R : Set G) := by
    rw [hd.normalizer_core_eq, Subgroup.mem_centralizer_singleton_iff]
    calc b⁻¹ * a * t = b⁻¹ * (a * t * a⁻¹) * a := by group
      _ = b⁻¹ * (b * t * b⁻¹) * a := by rw [h]
      _ = t * (b⁻¹ * a) := by group
  calc conjSub a (tightCore R) = conjSub b (conjSub (b⁻¹ * a) (tightCore R)) := by
        rw [← conjSub_mul, mul_inv_cancel_left]
    _ = conjSub b (tightCore R) := by rw [conjSub_eq_of_mem_normalizer hn]

theorem mem_normalizer_of_commute {K₁ : Subgroup G}
    (hK₁ : K₁ ∈ CoreAssembly.conjClass (tightCore R)) {z₁ : G} (hz₁ : IsUniqueInvolution K₁ z₁)
    {v : G} (hv : v * z₁ = z₁ * v) : v ∈ Subgroup.normalizer (K₁ : Set G) := by
  obtain ⟨a, rfl⟩ := CoreAssembly.single_class (tightCore R) K₁ hK₁
  obtain rfl : z₁ = a * t * a⁻¹ := hz₁.eq (hd.isUniqueInvolution_core.conj a)
  have hconj : conjSub v (conjSub a (tightCore R)) = conjSub a (tightCore R) := by
    rw [← conjSub_mul]
    apply hd.conjSub_eq_conjSub
    calc v * a * t * (v * a)⁻¹ = v * (a * t * a⁻¹) * v⁻¹ := by group
      _ = a * t * a⁻¹ * v * v⁻¹ := by rw [hv]
      _ = a * t * a⁻¹ := by group
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have hx : v * x * v⁻¹ ∈ conjSub v (conjSub a (tightCore R)) ↔ x ∈ conjSub a (tightCore R) := by
    rw [mem_conjSub_iff]
    simp [mul_assoc]
  rw [hconj] at hx
  exact hx.symm

theorem exists_isUniqueInvolution_member {J : Subgroup G}
    (hJ : J ∈ CoreAssembly.conjClass (tightCore R)) : ∃ u : G, IsUniqueInvolution J u := by
  obtain ⟨g, rfl⟩ := CoreAssembly.single_class (tightCore R) J hJ
  exact ⟨_, hd.isUniqueInvolution_core.conj g⟩

theorem eq_of_isUniqueInvolution_member {J₁ J₂ : Subgroup G}
    (h₁ : J₁ ∈ CoreAssembly.conjClass (tightCore R))
    (h₂ : J₂ ∈ CoreAssembly.conjClass (tightCore R)) {u : G} (hu₁ : IsUniqueInvolution J₁ u)
    (hu₂ : IsUniqueInvolution J₂ u) : J₁ = J₂ := by
  obtain ⟨a, rfl⟩ := CoreAssembly.single_class (tightCore R) J₁ h₁
  obtain ⟨b, rfl⟩ := CoreAssembly.single_class (tightCore R) J₂ h₂
  have ha := (hd.isUniqueInvolution_core.conj a).eq hu₁
  have hb := (hd.isUniqueInvolution_core.conj b).eq hu₂
  exact hd.conjSub_eq_conjSub (ha.trans hb.symm)

theorem normalizer_eq_centralizer_member {J : Subgroup G}
    (hJ : J ∈ CoreAssembly.conjClass (tightCore R)) {u : G} (hu : IsUniqueInvolution J u) :
    Subgroup.normalizer (J : Set G) = Subgroup.centralizer ({u} : Set G) :=
  le_antisymm (S1911.normalizer_le_centralizer_member hu) fun _ hv =>
    hd.mem_normalizer_of_commute hJ hu (Subgroup.mem_centralizer_singleton_iff.mp hv)

end TightDatum

namespace TightSylowStd

variable {T : Sylow 2 G} (h : TightSylowStd R S t T)
include h

theorem exists_w69 :
    ∃ W ∈ WSet (CoreAssembly.conjClass (tightCore R)), W ≤ (T : Subgroup G) := by
  obtain ⟨η, hη, hinv⟩ := Sec6Gen.exists_invariant_mem_etaSet h.hypOmegaGen T
  exact ⟨⨆ U ∈ η, U, ⟨η, ⟨T, hη, hinv⟩, rfl⟩, iSup₂_le fun U hU => (hη.1 hU).2⟩

theorem muZ2OrS3 {W : Subgroup G} (hW : W ∈ WSet (CoreAssembly.conjClass (tightCore R))) :
    MuIsoZ2 (CoreAssembly.conjClass (tightCore R)) W ∨
      MuIsoS3 (CoreAssembly.conjClass (tightCore R)) W := by
  by_cases hex : ∃ J ∈ CoreAssembly.conjClass (tightCore R),
      (omegaStarNbr (CoreAssembly.conjClass (tightCore R)) J).Nonempty
  · exact Or.inr (Q3T6.Mu.muIsoS3_of_shape h.partIHypG hW h.edgeless hex)
  · refine Or.inl (Q3T6.Mu.muIsoZ2_of_shape h.partIHypG hW
      ⟨tightCore R, CoreAssembly.mem_conjClass_self _⟩ fun J hJ => ?_)
    exact Set.not_nonempty_iff_eq_empty.mp fun hne => hex ⟨J, hJ, hne⟩

omit [Finite G] h in
theorem not_muIsoZ2_of_muIsoS3 {Ω : Set (Subgroup G)} {W : Subgroup G}
    (h3 : MuIsoS3 Ω W) : ¬ MuIsoZ2 Ω W := by
  rintro ⟨e2⟩
  obtain ⟨e3⟩ := h3
  have h := (Nat.card_congr e2.toEquiv).symm.trans (Nat.card_congr e3.toEquiv)
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod, Nat.card_perm, Nat.card_fin] at h
  norm_num [Nat.factorial] at h

theorem not_allTypeTwo_of_muIsoS3 {W : Subgroup G}
    (hW : W ∈ WSet (CoreAssembly.conjClass (tightCore R)))
    (hS3 : MuIsoS3 (CoreAssembly.conjClass (tightCore R)) W) : ¬ AllTypeTwo (tightCore R) t := by
  intro hA
  refine not_muIsoZ2_of_muIsoS3 hS3 (Q3T6.Mu.muIsoZ2_of_shape h.partIHypG hW
    ⟨tightCore R, CoreAssembly.mem_conjClass_self _⟩ fun J hJ => ?_)
  refine Set.eq_empty_of_forall_notMem ?_
  rintro J' ⟨hJ', hne, U, hU, hUJ', hUN⟩
  obtain ⟨w, hw⟩ := h.datum.exists_isUniqueInvolution_member hJ
  obtain ⟨u, hu⟩ := h.datum.exists_isUniqueInvolution_member hJ'
  obtain ⟨x, rfl⟩ := CoreAssembly.single_class (tightCore R) J hJ
  have hwx : x * t * x⁻¹ = w := (h.isUniqueInvolution.conj x).eq hw
  have hUw : U ≤ Subgroup.centralizer ({w} : Set G) :=
    (h.datum.normalizer_eq_centralizer_member hJ hw) ▸ hUN
  obtain ⟨R', hR', hUR', -, hidx⟩ := hU
  have h8 := Sec6Gen.eight_le_of_mem_RSet h.hypOmegaGen hR'
  have hcard : Nat.card R' = 2 * Nat.card U := by
    have h1 := Subgroup.relIndex_mul_card (H := U) (K := R')
    rw [inf_eq_left.mpr hUR', hidx] at h1
    exact h1.symm
  have hU2 : IsPGroup 2 U := (isPGroup_of_mem_rSet hR').to_le hUR'
  have huU : u ∈ U := S1911.mem_of_le_member hu hUJ' hU2 (by omega)
  have hwu : w ≠ u := by
    rintro rfl
    exact hne (h.datum.eq_of_isUniqueInvolution_member hJ' hJ hu hw)
  have hcomm : w * u = u * w := (Subgroup.mem_centralizer_singleton_iff.mp (hUw huU)).symm
  have h2 := hA J' hJ' u w hu ⟨x, hwx⟩ hwu hcomm U hU2 hUJ' hUw
  omega

end TightSylowStd

end CFSG.ClassicalInvolution.Q3
