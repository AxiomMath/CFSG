module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.Rho
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.NMASetting
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.ZStabFacts

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.EvenSporadicStandard.HNRecog.HaradaLA

variable {G : Type} [Group G] [Finite G] {t z z₁ : G} {ι : Elem2 6 →* G} {zv : V6}
  {R0 F : Subgroup G}

private lemma coordElt_injective (hι : Function.Injective ι) :
    Function.Injective (coordElt ι) := by
  intro u v huv
  have h : Multiplicative.ofAdd u = Multiplicative.ofAdd v := hι huv
  simpa using congrArg Multiplicative.toAdd h

private lemma isAddPerm_zero {g : Equiv.Perm V6} (hg : IsAddPerm g) : g 0 = 0 := by
  have h := hg 0 0
  rw [add_zero] at h
  have h2 : g 0 + g 0 = 0 := by
    funext i
    exact CharTwo.add_self_eq_zero (g 0 i)
  rw [← h] at h2
  exact h2

theorem Setting25.card_N (h : Setting25 G t z z₁ ι zv R0 F) :
    Nat.card (normalizer (ι.range : Set G)) = 64 * 25920 := by
  rw [← card_inducedGroup_mul h.injective_ι h.centralizer_le, h.omega, h.card_omega]

theorem Setting25.range_le_K (h : Setting25 G t z z₁ ι zv R0 F) : ι.range ≤ Kgrp ι z := by
  intro x hx
  refine ⟨Subgroup.le_normalizer hx, ?_⟩
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp hx
  have hz : z ∈ ι.range := by
    rw [← h.coord_z]
    exact MonoidHom.mem_range.mpr ⟨Multiplicative.ofAdd zv, rfl⟩
  obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp hz
  calc x * z = ι a * ι b := by rw [← ha, ← hb]
    _ = ι (a * b) := (map_mul ι a b).symm
    _ = ι (b * a) := by rw [mul_comm]
    _ = ι b * ι a := map_mul ι b a
    _ = z * x := by rw [hb, ha]

theorem Setting25.mem_K_iff (h : Setting25 G t z z₁ ι zv R0 F) {x : G} :
    x ∈ Kgrp ι z ↔ ∃ g : Equiv.Perm V6, Acts ι x g ∧ g zv = zv := by
  constructor
  · intro hx
    rw [Kgrp, Subgroup.mem_inf] at hx
    obtain ⟨hnorm, hcent⟩ := hx
    obtain ⟨g, hg⟩ := exists_acts h.injective_ι hnorm
    refine ⟨g, hg, ?_⟩
    have hcomm : x * z = z * x := Subgroup.mem_centralizer_singleton_iff.mp hcent
    have h1 : x * z * x⁻¹ = z := mul_inv_eq_iff_eq_mul.mpr hcomm
    have h2 : coordElt ι (g zv) = coordElt ι zv := by
      rw [← hg zv, h.coord_z, h1]
    exact coordElt_injective h.injective_ι h2
  · rintro ⟨g, hg, hgz⟩
    refine ⟨Acts.mem_normalizer hg, ?_⟩
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    have h2 : x * z * x⁻¹ = z := by
      calc x * z * x⁻¹ = x * coordElt ι zv * x⁻¹ := by rw [h.coord_z]
        _ = coordElt ι (g zv) := hg zv
        _ = coordElt ι zv := by rw [hgz]
        _ = z := h.coord_z
    exact mul_inv_eq_iff_eq_mul.mp h2

theorem Setting25.mem_actImage_K_iff (h : Setting25 G t z z₁ ι zv R0 F) {g : Equiv.Perm V6} :
    g ∈ actImage ι (Kgrp ι z) ↔ g ∈ OmegaMinus ∧ g zv = zv := by
  have hKle : Kgrp ι z ≤ normalizer (ι.range : Set G) := inf_le_left
  constructor
  · rintro ⟨k, hk, hg⟩
    have hgInd : g ∈ inducedGroup ι := by
      have h2 : g ∈ actImage ι (normalizer (ι.range : Set G)) :=
        actImage_mono hKle ⟨k, hk, hg⟩
      rwa [actImage_normalizer] at h2
    refine ⟨?_, ?_⟩
    · rwa [h.omega] at hgInd
    · obtain ⟨g', hg', hgz⟩ := (h.mem_K_iff).mp hk
      have : g = g' := Acts.unique h.injective_ι hg hg'
      rwa [this]
  · rintro ⟨hgOm, hgz⟩
    have hgInd : g ∈ inducedGroup ι := by rwa [← h.omega] at hgOm
    have h2 : g ∈ actImage ι (normalizer (ι.range : Set G)) := by
      rwa [actImage_normalizer]
    obtain ⟨n, hn, hng⟩ := h2
    exact ⟨n, (h.mem_K_iff).mpr ⟨g, hng, hgz⟩, hng⟩

theorem Setting25.exists_mem_N_acts (h : Setting25 G t z z₁ ι zv R0 F) {g : Equiv.Perm V6}
    (hg : g ∈ OmegaMinus) : ∃ n ∈ normalizer (ι.range : Set G), Acts ι n g := by
  have hg' : g ∈ actImage ι (normalizer (ι.range : Set G)) := by
    rw [actImage_normalizer, h.omega]
    exact hg
  exact hg'

theorem Setting25.exists_mem_K_acts (h : Setting25 G t z z₁ ι zv R0 F) {g : Equiv.Perm V6}
    (hg : g ∈ OmegaMinus) (hgz : g zv = zv) : ∃ k ∈ Kgrp ι z, Acts ι k g := by
  have hmem : g ∈ actImage ι (Kgrp ι z) := (h.mem_actImage_K_iff).mpr ⟨hg, hgz⟩
  exact hmem

theorem Setting25.exists_acts_of_mem_K (h : Setting25 G t z z₁ ι zv R0 F) {k : G}
    (hk : k ∈ Kgrp ι z) : ∃ g ∈ OmegaMinus, g zv = zv ∧ Acts ι k g := by
  obtain ⟨g, hg, hgz⟩ := (h.mem_K_iff).mp hk
  have hmem : g ∈ actImage ι (Kgrp ι z) := ⟨k, hk, hg⟩
  obtain ⟨hgOm, -⟩ := (h.mem_actImage_K_iff).mp hmem
  exact ⟨g, hgOm, hgz, hg⟩

theorem Setting25.card_K (h : Setting25 G t z z₁ ι zv R0 F) : Nat.card (Kgrp ι z) = 61440 := by
  let N : Subgroup G := normalizer (ι.range : Set G)
  letI : MulAction ↥N G :=
    MulAction.compHom G (ConjAct.toConjAct.toMonoidHom.comp N.subtype)
  have smul_eq : ∀ (n : ↥N) (x : G), n • x = n.1 * x * n.1⁻¹ := by
    intro n x
    change (ConjAct.toConjAct n.1) • x = n.1 * x * n.1⁻¹
    rw [ConjAct.toConjAct_smul]
  have hstab : Nat.card (MulAction.stabilizer ↥N z) = Nat.card (Kgrp ι z) := by
    have e : MulAction.stabilizer ↥N z ≃ ↥(N ⊓ centralizer ({z} : Set G)) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro s
        refine ⟨s.1.1, s.1.2, ?_⟩
        have hs : s.1.1 * z * s.1.1⁻¹ = z := by
          have h : s.1 • z = z := s.2
          rwa [smul_eq] at h
        exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hs)
      · intro m
        refine ⟨⟨m.1, m.2.1⟩, ?_⟩
        show (⟨m.1, m.2.1⟩ : ↥N) • z = z
        rw [smul_eq]
        exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp m.2.2)
      · intro s; apply Subtype.ext; rfl
      · intro m; apply Subtype.ext; rfl
    rw [Nat.card_congr e]
    rfl
  let X : Type := {v : V6 // qm v = 0 ∧ v ≠ 0}
  have hcardX : Nat.card X = 27 := by
    dsimp only [X]
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact card_singular
  have horbit : Nat.card (MulAction.orbit ↥N z) = Nat.card X := by
    let f : X → MulAction.orbit ↥N z := fun v =>
      ⟨coordElt ι v, MulAction.mem_orbit_iff.mpr (by
        obtain ⟨g, hgOm, hgv⟩ :=
          exists_omegaMinus_singular_map h.hD2.qm_zv h.zv_ne_zero v.2.1 v.2.2
        obtain ⟨n, hn, hng⟩ := h.exists_mem_N_acts hgOm
        exact ⟨⟨n, hn⟩, by rw [smul_eq, ← h.coord_z, hng zv, hgv]⟩)⟩
    refine (Nat.card_congr (Equiv.ofBijective f ?_)).symm
    constructor
    · intro v w hvw
      apply Subtype.ext
      have hv : coordElt ι v = coordElt ι w := congrArg Subtype.val hvw
      exact coordElt_injective h.injective_ι hv
    · intro x
      obtain ⟨n, hn⟩ := MulAction.mem_orbit_iff.mp x.2
      have hnt : n.1 * z * n.1⁻¹ = (x : G) := by rw [← smul_eq]; exact hn
      obtain ⟨g, hg⟩ := exists_acts h.injective_ι n.2
      have hgOm : g ∈ OmegaMinus := by
        have : g ∈ inducedGroup ι := ⟨n.1, n.2, hg⟩
        rwa [h.omega] at this
      refine ⟨⟨g zv, ?_, ?_⟩, ?_⟩
      · rw [qm_apply_of_mem_omegaMinus hgOm, h.hD2.qm_zv]
      · intro h0
        apply h.zv_ne_zero
        apply g.injective
        rw [h0, isAddPerm_zero (Acts.isAddPerm h.injective_ι hg)]
      · apply Subtype.ext
        change coordElt ι (g zv) = (x : G)
        rw [← hnt, ← h.coord_z, hg zv]
  have hOS : Nat.card ↥N = Nat.card (Kgrp ι z) * Nat.card X := by
    rw [← Subgroup.card_mul_index (MulAction.stabilizer ↥N z), MulAction.index_stabilizer,
      ← Nat.card_coe_set_eq, hstab, horbit]
  have hNK : Nat.card (Kgrp ι z) * 27 = 64 * 25920 := by
    rw [← hcardX, ← hOS]
    dsimp only [N]
    exact h.card_N
  omega

theorem Setting25.exists_n_z₁ (h : Setting25 G t z z₁ ι zv R0 F) :
    ∃ n ∈ normalizer (ι.range : Set G), n * z₁ * n⁻¹ = z := by
  obtain ⟨v, hv, hlam, hqm⟩ := h.coords_z₁
  have hv0 : v ≠ 0 := by
    intro h0
    rw [h0] at hlam
    simp [lam] at hlam
  obtain ⟨g, hgOm, hgv⟩ := exists_omegaMinus_singular_map hqm hv0 h.hD2.qm_zv h.zv_ne_zero
  obtain ⟨n, hn, hng⟩ := h.exists_mem_N_acts hgOm
  exact ⟨n, hn, by rw [← hv, hng v, hgv, h.coord_z]⟩

end CFSG.EvenSporadicStandard.HNRecog.Harada
