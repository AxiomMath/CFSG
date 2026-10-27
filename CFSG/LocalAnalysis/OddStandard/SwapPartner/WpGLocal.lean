module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.WpGTypes

import CFSG.LocalAnalysis.OddStandard.SwapPartner.InputLPerm

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup Equiv Equiv.Perm CFSG.OddStandard.AltStdSec.SwapPattern

variable {G : Type} [Group G] {z : G} {ι : Perm (Fin 10) →* G}

private lemma wp_mem_fixFin_iff {σ ρ : Perm (Fin 10)} (hcomm : ρ * σ = σ * ρ) (i : Fin 10) :
    i ∈ fixFin σ ↔ ρ i ∈ fixFin σ := by
  rw [mem_fixFin, mem_fixFin]
  have h : ρ (σ i) = σ (ρ i) := by
    simpa only [Perm.mul_apply] using congrArg (fun f : Perm (Fin 10) => f i) hcomm
  constructor
  · intro hi; rw [hi] at h; exact h.symm
  · intro hi; rw [hi] at h; exact ρ.injective h

private lemma wp_conj_mem_altSub {σ ρ a : Perm (Fin 10)} (hcomm : ρ * σ = σ * ρ)
    (ha : a ∈ altSub (fixFin σ)) : ρ * a * ρ⁻¹ ∈ altSub (fixFin σ) :=
  (mem_normalizer_iff.mp
    (mem_normalizer_altSub (T := fixFin σ) (wp_mem_fixFin_iff hcomm)) a).1 ha

private lemma wp_altSub_comm {σ ρ : Perm (Fin 10)} (hσ : σ * σ = 1)
    (hρ : ρ ∈ altSub (fixFin σ)) : ρ * σ = σ * ρ := by
  have hfix : ∀ i, i ∉ fixFin σ → ρ i = i := (mem_altSub.1 hρ).2
  ext i
  simp only [Perm.mul_apply]
  by_cases hi : i ∈ fixFin σ
  · have hσi : σ i = i := mem_fixFin.1 hi
    have hρiF : ρ i ∈ fixFin σ := by
      by_contra hcon
      have h1 : ρ (ρ i) = ρ i := hfix (ρ i) hcon
      have h2 : ρ i = i := ρ.injective h1
      exact hcon (by rw [h2]; exact hi)
    rw [hσi, mem_fixFin.1 hρiF]
  · have hσi : σ i ≠ i := fun h => hi (mem_fixFin.2 h)
    have hρi : ρ i = i := hfix i hi
    have hσiF : σ i ∉ fixFin σ := by
      intro hmem
      have h1 : σ (σ i) = σ i := mem_fixFin.1 hmem
      rw [← Perm.mul_apply, hσ, Perm.one_apply] at h1
      exact hσi h1.symm
    rw [hρi, hfix (σ i) hσiF]

private lemma wp_z_comm_z_mul (hC : CentData z ι) (σ : Perm (Fin 10)) :
    z * (z * ι σ) = (z * ι σ) * z := by
  rw [mul_assoc, hC.comm σ]

private lemma wp_z_mul_comm_iff {x w : G} (hz : z * w = w * z) :
    (z * x) * w = w * (z * x) ↔ x * w = w * x := by
  constructor
  · intro h
    have h2 : z * (x * w) = z * (w * x) := by
      calc z * (x * w) = (z * x) * w := by group
        _ = w * (z * x) := h
        _ = (w * z) * x := by group
        _ = (z * w) * x := by rw [← hz]
        _ = z * (w * x) := by group
    exact mul_left_cancel h2
  · intro h
    calc (z * x) * w = z * (x * w) := by group
      _ = z * (w * x) := by rw [h]
      _ = (z * w) * x := by group
      _ = (w * z) * x := by rw [hz]
      _ = w * (z * x) := by group

private lemma wp_mul_z_comm_iff {x w : G} (hx : x * z = z * x) :
    x * (z * w) = (z * w) * x ↔ x * w = w * x := by
  constructor
  · intro h
    have h2 : z * (x * w) = z * (w * x) := by
      calc z * (x * w) = (z * x) * w := by group
        _ = (x * z) * w := by rw [← hx]
        _ = x * (z * w) := by group
        _ = (z * w) * x := h
        _ = z * (w * x) := by group
    exact mul_left_cancel h2
  · intro h
    calc x * (z * w) = (x * z) * w := by group
      _ = (z * x) * w := by rw [hx]
      _ = z * (x * w) := by group
      _ = z * (w * x) := by rw [h]
      _ = (z * w) * x := by group

private lemma wp_conj_iota (hC : CentData z ι) {ρ a : Perm (Fin 10)} :
    (ι ρ) * ι a * (ι ρ)⁻¹ = ι (ρ * a * ρ⁻¹) := by
  rw [map_mul, map_mul, map_inv]

private lemma wp_conj_z_iota (hC : CentData z ι) {ρ a : Perm (Fin 10)} :
    (z * ι ρ) * ι a * (z * ι ρ)⁻¹ = ι (ρ * a * ρ⁻¹) := by
  have hz_inv : z⁻¹ = z := (eq_inv_of_mul_eq_one_right hC.mul_self).symm
  calc (z * ι ρ) * ι a * (z * ι ρ)⁻¹
      = z * (ι ρ * ι a * (ι ρ)⁻¹) * z := by rw [mul_inv_rev, hz_inv]; group
    _ = z * ι (ρ * a * ρ⁻¹) * z := by rw [wp_conj_iota hC]
    _ = ι (ρ * a * ρ⁻¹) := by
        rw [hC.comm (ρ * a * ρ⁻¹), mul_assoc, hC.mul_self, mul_one]

theorem exists_simpleNormalIn (hC : CentData z ι) {g x : G} {σ : Perm (Fin 10)}
    (hσ : σ * σ = 1) (hσ1 : σ ≠ 1) (hk : Multiset.card σ.cycleType ≤ 2)
    (hx : g⁻¹ * x * g = ι σ ∨ g⁻¹ * x * g = z * ι σ) :
    ∃ D : Subgroup G, SimpleNormalIn (g * z * g⁻¹) x D ∧
      Nat.card D = (10 - 2 * Multiset.card σ.cycleType).factorial / 2 := by
  classical
  let F : Finset (Fin 10) := fixFin σ
  have hFcard : F.card = 10 - 2 * Multiset.card σ.cycleType := by
    have hcard := card_fixed_add_two_mul_card_cycleType (m := 10) hσ
    have hsub : Fintype.card {i : Fin 10 // σ i = i} = F.card :=
      Fintype.card_subtype (fun i : Fin 10 => σ i = i)
    rw [hsub] at hcard
    omega
  have hFge : 5 ≤ F.card := by omega
  let D₀ : Subgroup G := (altSub F).map ι
  let D : Subgroup G := D₀.map (MulAut.conj g).toMonoidHom
  let e1 : altSub F ≃* D₀ := Subgroup.equivMapOfInjective (altSub F) ι hC.inj
  let e2 : D₀ ≃* D :=
    Subgroup.equivMapOfInjective D₀ (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  let eD : D ≃* alternatingGroup (Fin F.card) := (e1.trans e2).symm.trans (altSubEquiv F)
  have hmem : ∀ d : G, d ∈ D ↔ ∃ a ∈ altSub F, g * ι a * g⁻¹ = d := by
    intro d
    constructor
    · intro hd
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hd
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hy
      exact ⟨a, ha, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact Subgroup.mem_map.mpr ⟨ι a, Subgroup.mem_map.mpr ⟨a, ha, rfl⟩, rfl⟩
  have hle : D ≤ centralizer ({g * z * g⁻¹} : Set G) ⊓ centralizer ({x} : Set G) := by
    intro d hd
    obtain ⟨a, ha, rfl⟩ := (hmem d).mp hd
    rw [Subgroup.mem_inf]
    constructor
    · rw [mem_centralizer_singleton_iff]
      calc (g * ι a * g⁻¹) * (g * z * g⁻¹) = g * (ι a * z) * g⁻¹ := by group
        _ = g * (z * ι a) * g⁻¹ := by rw [hC.comm a]
        _ = (g * z * g⁻¹) * (g * ι a * g⁻¹) := by group
    · rw [mem_centralizer_singleton_iff]
      have hxw : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
      have hcommw : ι a * (g⁻¹ * x * g) = (g⁻¹ * x * g) * ι a := by
        have hp : a * σ = σ * a := wp_altSub_comm hσ ha
        rcases hx with hx | hx
        · rw [hx, ← map_mul, ← map_mul, hp]
        · rw [hx]
          have his : ι a * ι σ = ι σ * ι a := by rw [← map_mul, ← map_mul, hp]
          calc ι a * (z * ι σ) = (ι a * z) * ι σ := by group
            _ = (z * ι a) * ι σ := by rw [← hC.comm a]
            _ = z * (ι a * ι σ) := by group
            _ = z * (ι σ * ι a) := by rw [his]
            _ = (z * ι σ) * ι a := by group
      calc (g * ι a * g⁻¹) * x = g * (ι a * (g⁻¹ * x * g)) * g⁻¹ := by rw [hxw]; group
        _ = g * ((g⁻¹ * x * g) * ι a) * g⁻¹ := by rw [hcommw]
        _ = x * (g * ι a * g⁻¹) := by rw [hxw]; group
  have hnormal : ∀ f ∈ centralizer ({g * z * g⁻¹} : Set G) ⊓ centralizer ({x} : Set G),
      ∀ d ∈ D, f * d * f⁻¹ ∈ D := by
    intro f hf d hd
    obtain ⟨a, ha, rfl⟩ := (hmem d).mp hd
    set f' : G := g⁻¹ * f * g with hf'_def
    set w : G := g⁻¹ * x * g with hw_def
    have hwc : w = ι σ ∨ w = z * ι σ := by
      rcases hx with hx | hx
      · exact Or.inl (hw_def.trans hx)
      · exact Or.inr (hw_def.trans hx)
    have hf'z : f' ∈ centralizer ({z} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      have hfz : f * (g * z * g⁻¹) = (g * z * g⁻¹) * f :=
        mem_centralizer_singleton_iff.mp hf.1
      rw [hf'_def]
      calc (g⁻¹ * f * g) * z = g⁻¹ * (f * (g * z * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * z * g⁻¹) * f) * g := by rw [hfz]
        _ = z * (g⁻¹ * f * g) := by group
    have hf'w : f' ∈ centralizer ({w} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      have hfx : f * x = x * f := mem_centralizer_singleton_iff.mp hf.2
      rw [hf'_def, hw_def]
      calc (g⁻¹ * f * g) * (g⁻¹ * x * g) = g⁻¹ * (f * x) * g := by group
        _ = g⁻¹ * (x * f) * g := by rw [hfx]
        _ = (g⁻¹ * x * g) * (g⁻¹ * f * g) := by group
    obtain ⟨ρ, hρ⟩ := hC.cases f' hf'z
    have hzw : z * w = w * z := by
      rcases hwc with hwc | hwc
      · rw [hwc]; exact hC.comm σ
      · rw [hwc]; exact wp_z_comm_z_mul hC σ
    have hιρw : ι ρ * w = w * ι ρ := by
      have hcomm := mem_centralizer_singleton_iff.mp hf'w
      rcases hρ with hρ | hρ
      · rw [hρ] at hcomm; exact hcomm
      · rw [hρ] at hcomm
        exact (wp_z_mul_comm_iff hzw).mp hcomm
    have hρσ : ρ * σ = σ * ρ := by
      rcases hwc with hwc | hwc
      · rw [hwc] at hιρw
        exact hC.inj (by simpa only [map_mul] using hιρw)
      · rw [hwc] at hιρw
        have h2 : ι ρ * ι σ = ι σ * ι ρ :=
          (wp_mul_z_comm_iff (hC.comm ρ).symm).mp hιρw
        exact hC.inj (by simpa only [map_mul] using h2)
    have hρa : ρ * a * ρ⁻¹ ∈ altSub F := wp_conj_mem_altSub hρσ ha
    have hconj : f * (g * ι a * g⁻¹) * f⁻¹ = g * ι (ρ * a * ρ⁻¹) * g⁻¹ := by
      have h1 : f * (g * ι a * g⁻¹) * f⁻¹ = g * (f' * ι a * f'⁻¹) * g⁻¹ := by
        rw [hf'_def]; group
      rw [h1]
      have h2 : f' * ι a * f'⁻¹ = ι (ρ * a * ρ⁻¹) := by
        rcases hρ with hρ | hρ
        · rw [hρ]; exact wp_conj_iota hC
        · rw [hρ]; exact wp_conj_z_iota hC
      rw [h2]
    rw [hconj]
    exact (hmem _).mpr ⟨ρ * a * ρ⁻¹, hρa, rfl⟩
  have hsimple : IsSimpleGroup D := by
    haveI : Nontrivial (Fin F.card) := Fin.nontrivial_iff_two_le.mpr (by omega)
    haveI : IsSimpleGroup (alternatingGroup (Fin F.card)) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; exact hFge)
    exact MulEquiv.isSimpleGroup eD
  have hnonab : ∃ a ∈ D, ∃ b ∈ D, a * b ≠ b * a := by
    by_contra h
    push Not at h
    have hcommD : ∀ a b : D, a * b = b * a := fun a b => Subtype.ext (h a a.2 b b.2)
    have hcommAlt : IsMulCommutative (alternatingGroup (Fin F.card)) :=
      IsMulCommutative.of_comm (fun a b => by
        have h1 := hcommD (eD.symm a) (eD.symm b)
        calc a * b = eD (eD.symm a * eD.symm b) := by simp
          _ = eD (eD.symm b * eD.symm a) := by rw [h1]
          _ = b * a := by simp)
    have h3 : Nat.card (Fin F.card) ≤ 3 :=
      alternatingGroup.isMulCommutative_iff_card_le_three.mp hcommAlt
    rw [Nat.card_fin] at h3
    omega
  have hcard : Nat.card D = (10 - 2 * Multiset.card σ.cycleType).factorial / 2 := by
    haveI : Nontrivial (Fin F.card) := Fin.nontrivial_iff_two_le.mpr (by omega)
    calc Nat.card D = Nat.card (alternatingGroup (Fin F.card)) := Nat.card_congr eD.toEquiv
      _ = (Nat.card (Fin F.card)).factorial / 2 := nat_card_alternatingGroup
      _ = F.card.factorial / 2 := by rw [Nat.card_fin]
      _ = (10 - 2 * Multiset.card σ.cycleType).factorial / 2 := by rw [hFcard]
  exact ⟨D, ⟨hle, hnormal, hsimple, hnonab⟩, hcard⟩

end CFSG.OddStandard.AltStdSec.SwapPartner
