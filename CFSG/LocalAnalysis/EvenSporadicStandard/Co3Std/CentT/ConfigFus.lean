module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.CentT.ConjZ
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Config

public section

namespace CFSG.EvenSporadicStandard.Co3Std.CentT

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic

private lemma map_conj_centralizer_singleton {G : Type*} [Group G] (g x : G) :
    (Subgroup.centralizer ({x} : Set G)).map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer ({g * x * g⁻¹} : Set G) := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨z, hz, rfl⟩
    show (g * z * g⁻¹) * (g * x * g⁻¹) = (g * x * g⁻¹) * (g * z * g⁻¹)
    calc (g * z * g⁻¹) * (g * x * g⁻¹) = g * (z * x) * g⁻¹ := by group
      _ = g * (x * z) * g⁻¹ := by rw [hz]
      _ = (g * x * g⁻¹) * (g * z * g⁻¹) := by group
  · intro hy
    refine ⟨g⁻¹ * y * g, ?_, ?_⟩
    · calc (g⁻¹ * y * g) * x = g⁻¹ * (y * (g * x * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * x * g⁻¹) * y) * g := by rw [hy]
        _ = x * (g⁻¹ * y * g) := by group
    · show g * (g⁻¹ * y * g) * g⁻¹ = y
      group

theorem card_centralizer_eq_of_isConj {G : Type} [Group G] [Finite G] {a b : G}
    (h : IsConj a b) :
    Nat.card ↥(centralizer ({a} : Set G)) = Nat.card ↥(centralizer ({b} : Set G)) := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  have hmap : (centralizer ({a} : Set G)).map (MulAut.conj c).toMonoidHom =
      centralizer ({b} : Set G) := by
    rw [map_conj_centralizer_singleton, hc]
  rw [← hmap]
  rw [Subgroup.card_map_of_injective (f := (MulAut.conj c).toMonoidHom)
    (MulAut.conj c).injective]

theorem not_isConj_z_t {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G}
    {T₀ : Subgroup G} (hcfg : Fin76b.InnerConfig G L z t T₀) (hT₀ : Nat.card T₀ = 2 ^ 10)
    (hdvd : 2 ^ 12 ∣ Nat.card ↥(centralizer ({t} : Set G))) : ¬ IsConj z t := by
  intro hconj
  obtain ⟨m, hm_odd, hmL⟩ := hcfg.T₀_odd
  have hcard := card_centralizer_eq_of_isConj hconj
  have hLcard : Nat.card (L ⊔ zpowers z : Subgroup G) = Nat.card L * 2 := by
    rw [Nat.card_congr (mulEquivProdSup (zpowers_le.2 hcfg.z_cent) hcfg.disjoint).toEquiv.symm,
      Nat.card_prod, Nat.card_zpowers, hcfg.z_order]
  have hzcard : Nat.card ↥(centralizer ({z} : Set G)) = 2 ^ 10 * m * 2 := by
    rw [hcfg.cent_eq, hLcard, hmL, hT₀]
  rw [← hcard, hzcard] at hdvd
  have hm2 : 2 ∣ m := by
    have h1 : (2 : ℕ) ^ 12 = 2 ^ 11 * 2 := by norm_num
    have h2 : (2 : ℕ) ^ 10 * m * 2 = 2 ^ 11 * m := by ring
    rw [h1, h2] at hdvd
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : (0 : ℕ) < 2 ^ 11) hdvd
  obtain ⟨k, hk⟩ := hm_odd
  obtain ⟨j, hj⟩ := hm2
  omega

section Certified


theorem centFacts_of_isConj {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hL : IsSporadic ↥L .Co3) {z t : G} {T₀ : Subgroup G}
    (hcfg : Fin76b.InnerConfig G L z t T₀) (hzt : ¬ IsConj z t) {w : G} (hw : IsConj z w)
    (hwt : w * t = t * w) :
    w * w = 1 ∧ w ≠ 1 ∧
      CentFacts ↥(centralizer ({w} : Set G) ⊓ centralizer ({t} : Set G)) := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hw
  have hw2 : w * w = 1 := by
    rw [← hg]
    calc (g * z * g⁻¹) * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [hcfg.z_sq]; group
  have hw1 : w ≠ 1 := by
    intro h
    refine hcfg.z_ne ?_
    calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
      _ = 1 := by rw [hg, h]; group
  have htne : t ≠ w := by
    intro h
    exact hzt (by rw [h]; exact hw)
  set φ : G →* G := (MulAut.conj g).toMonoidHom with hφ
  set Λ : Subgroup G := L.map φ with hΛdef
  have hφz : φ z = w := by
    rw [hφ]
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hg
  have hΛ : IsSporadic ↥Λ .Co3 := by
    obtain ⟨e⟩ := hL
    rw [hΛdef]
    exact ⟨(Subgroup.equivMapOfInjective L φ (MulAut.conj g).injective).symm.trans e⟩
  have hcent_map : (centralizer ({z} : Set G)).map φ = centralizer ({w} : Set G) := by
    rw [hφ, map_conj_centralizer_singleton, hg]
  have hcent : centralizer ({w} : Set G) = Λ ⊔ zpowers w := by
    rw [← hcent_map, hcfg.cent_eq, hΛdef, Subgroup.map_sup, MonoidHom.map_zpowers, hφz]
  have hdisj : Disjoint Λ (zpowers w) := by
    have hmap := Subgroup.disjoint_map (f := φ) (MulAut.conj g).injective hcfg.disjoint
    rw [← hΛdef, MonoidHom.map_zpowers, hφz] at hmap
    exact hmap
  exact ⟨hw2, hw1,
    centFacts_of_centralizer_pair hΛ hw2 hw1 hcent hdisj hcfg.t_sq hcfg.t_ne hwt.symm htne⟩

end Certified

end CFSG.EvenSporadicStandard.Co3Std.CentT
