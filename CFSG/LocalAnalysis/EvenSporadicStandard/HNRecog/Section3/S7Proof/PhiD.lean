module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.S7Proof.ThreeTransp
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.S7Proof.Model7

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G]

private theorem s7_phi_D_forward {a z x : G} (H : S7Hyps a z) (hx : x ∈ orb3A a a)
    (φ : ↥(Gxy a x) ≃* Sym 7) (t : ↥(Gxy a x))
    (ht : (t : G) ∈ orb2A a a ∩ orb2A a x) : (φ t).cycleType = {2} := by
  let D' : Set (Sym 7) :=
    {σ | ∃ d : ↥(Gxy a x), (d : G) ∈ orb2A a a ∩ orb2A a x ∧ φ d = σ}
  have hne : D'.Nonempty := by
    obtain ⟨d₀, hd₀⟩ := hx.2.2
    obtain ⟨hdG, -⟩ := s7_D_subset H hx.1 hd₀
    exact ⟨φ ⟨d₀, hdG⟩, ⟨⟨d₀, hdG⟩, hd₀, rfl⟩⟩
  have hinv : ∀ d ∈ D', d ^ 2 = 1 ∧ d ≠ 1 := by
    rintro d ⟨u, huD, rfl⟩
    have hu_sq_G : (u : G) ^ 2 = 1 := s7_sq_of_isConj_a H huD.1.1
    have hu_sq : u ^ 2 = 1 := by
      apply Subtype.ext
      simpa only [Subgroup.coe_pow, Subgroup.coe_one] using hu_sq_G
    constructor
    · calc (φ u) ^ 2 = φ (u ^ 2) := (map_pow φ u 2).symm
        _ = 1 := by rw [hu_sq, map_one]
    · intro h
      have hu_one : u = 1 := (MulEquiv.map_eq_one_iff φ).mp h
      have hd_one : (u : G) = 1 := by
        simpa only [Subgroup.coe_one] using
          congrArg (fun y : ↥(Gxy a x) => (y : G)) hu_one
      exact s7_ne_one_of_isConj_a H huD.1.1 hd_one
  have hnorm : ∀ d ∈ D', ∀ g : Sym 7, g * d * g⁻¹ ∈ D' := by
    rintro d ⟨u, huD, rfl⟩ g
    refine ⟨φ.symm g * u * (φ.symm g)⁻¹, ?_, ?_⟩
    · have hk : ((φ.symm g : ↥(Gxy a x)) : G) ∈ Gxy a x := (φ.symm g).2
      have hmem := s7_conj_D (a := a) (x := x) (t := (u : G))
        (k := ((φ.symm g : ↥(Gxy a x)) : G)) hk huD
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hmem
    · simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
  have hthree : ∀ d ∈ D', ∀ e ∈ D', (d * e) ^ 3 = 1 ∨ (d * e) ^ 2 = 1 := by
    rintro d ⟨u, huD, rfl⟩ e ⟨v, hvD, rfl⟩
    have hthree_G := s7_three H hx huD hvD
    have hthree_sub : (u * v) ^ 3 = 1 ∨ (u * v) ^ 2 = 1 := by
      rcases hthree_G with h | h
      · left
        apply Subtype.ext
        simpa only [Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_one] using h
      · right
        apply Subtype.ext
        simpa only [Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_one] using h
    rcases hthree_sub with h | h
    · left
      rw [← map_mul, ← map_pow, h, map_one]
    · right
      rw [← map_mul, ← map_pow, h, map_one]
  exact s7_sym7_swap_of_threeTransp hne hinv hnorm hthree (φ t) ⟨t, ht, rfl⟩

theorem s7_phi_D {a z x : G} (H : S7Hyps a z) (hx : x ∈ orb3A a a) (φ : ↥(Gxy a x) ≃* Sym 7)
    (t : ↥(Gxy a x)) : (t : G) ∈ orb2A a a ∩ orb2A a x ↔ (φ t).cycleType = {2} := by
  constructor
  · intro ht
    exact s7_phi_D_forward H hx φ t ht
  · intro hct
    obtain ⟨d₀, hd₀⟩ := hx.2.2
    obtain ⟨hdG, -⟩ := s7_D_subset H hx.1 hd₀
    let u₀ : ↥(Gxy a x) := ⟨d₀, hdG⟩
    have hu₀D : (u₀ : G) ∈ orb2A a a ∩ orb2A a x := hd₀
    have hu₀cycle : (φ u₀).cycleType = {2} := s7_phi_D_forward H hx φ u₀ hu₀D
    have hconj : IsConj (φ u₀) (φ t) := by
      rw [Equiv.Perm.isConj_iff_cycleType_eq, hu₀cycle, hct]
    obtain ⟨g, hg⟩ := isConj_iff.mp hconj
    have ht_eq : t = φ.symm g * u₀ * (φ.symm g)⁻¹ := by
      have h := congrArg φ.symm hg
      simpa only [map_mul, map_inv, MulEquiv.apply_symm_apply, MulEquiv.symm_apply_apply]
        using h.symm
    rw [ht_eq]
    have hmem := s7_conj_D (a := a) (x := x) (t := (u₀ : G))
      (k := ((φ.symm g : ↥(Gxy a x)) : G)) (φ.symm g).2 hu₀D
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hmem

end CFSG.EvenSporadicStandard.HNRecog.Section3
