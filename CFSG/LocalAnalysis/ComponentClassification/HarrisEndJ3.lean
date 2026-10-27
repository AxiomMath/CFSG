module

public import CFSG.Sporadic.SmallOddCore.J3Aut
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndPermModel

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.HarrisEnd

open CFSG Subgroup CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier

theorem j3_outer_facts {Y : Type} [Group Y] (hY : Nonempty (Y ≃* Blueprint.NativeSporadic.J3))
    {τ : MulAut Y} (hτ2 : orderOf τ = 2) (hout : τ ∉ innAut Y) :
    (∀ φ : MulAut Y, φ ∈ innAut Y ∨ φ * τ ∈ innAut Y) ∧ Nat.card ↥(fixedPoints τ) = 2448 := by
  obtain ⟨e₁⟩ := hY
  obtain ⟨e, he, -, -, -⟩ := ctuc_j3_full_automorphism_permutation_model
  obtain ⟨hu2, -, -, hmap, -, hR, -⟩ := ctuc_j3_normalizing_involution_permutation_model
  have hPR : j3P ≤ j3R := fun x hx => (hR x).mpr (Or.inl hx)
  obtain ⟨M⟩ := nonempty_permAutModel (e₁.trans j3PermEquiv) hPR e he
  have huu : j3u⁻¹ = j3u := inv_eq_of_mul_eq_one_right (by rw [← sq, hu2])
  have hun : ∀ p ∈ j3P, j3u * p * j3u⁻¹ ∈ j3P := fun p hp => by
    rw [← hmap]
    exact ⟨p, hp, rfl⟩
  have hprod : ∀ x y : Equiv.Perm (Fin 6156), x ∈ j3R → y ∈ j3R → x ∉ j3P → y ∉ j3P →
      x * y ∈ j3P := by
    intro x y hx hy hxP hyP
    have hxu : x * j3u ∈ j3P := ((hR x).mp hx).resolve_left hxP
    have hyu : y * j3u ∈ j3P := ((hR y).mp hy).resolve_left hyP
    have h1 : j3u * (y * j3u) * j3u⁻¹ ∈ j3P := hun _ hyu
    rw [show j3u * (y * j3u) * j3u⁻¹ = j3u * y by rw [huu, mul_assoc, mul_assoc, ← sq, hu2,
      mul_one]] at h1
    rw [show x * y = (x * j3u) * (j3u * y) by rw [mul_assoc, ← mul_assoc j3u, ← sq, hu2, one_mul]]
    exact mul_mem hxu h1
  have hτP : ((M.Φ τ : j3R) : Equiv.Perm (Fin 6156)) ∉ j3P := fun h =>
    hout ((M.mem_innAut_iff τ).mpr h)
  refine ⟨fun φ => ?_, ?_⟩
  · by_cases hφ : φ ∈ innAut Y
    · exact Or.inl hφ
    · right
      rw [M.mem_innAut_iff, map_mul, Subgroup.coe_mul]
      exact hprod _ _ (M.Φ φ).2 (M.Φ τ).2 (fun h => hφ ((M.mem_innAut_iff φ).mpr h)) hτP
  ·
    obtain ⟨-, -, -, hrows, hcover, -, hlist, -⟩ :=
      ctuc_j3_all_involution_fixed_subgroups_odd_core_trivial
    have hτo : orderOf ((M.Φ τ : j3R) : Equiv.Perm (Fin 6156)) = 2 := by
      rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hτ2]
    obtain ⟨r, hr, g, hg, hgr⟩ := hcover _ (M.Φ τ).2 hτo
    obtain ⟨-, -, hout', -, hcard, -⟩ := hrows r hr
    have hrepP : tp 6156 r.rep ∉ j3P := by
      intro h
      apply hτP
      rw [hgr]
      exact mul_mem (mul_mem hg h) (inv_mem hg)
    have hrout : r.outer = true := hout'.mpr hrepP
    have hmem : (r.outer, r.classSize, r.centOrder) ∈
        [(false, 26163, 1920), (true, 20520, 2448)] := by
      rw [← hlist]
      exact List.mem_map_of_mem hr
    have h2448 : r.centOrder = 2448 := by
      rw [hrout] at hmem
      simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hmem
      rcases hmem with ⟨h, -⟩ | ⟨-, -, h⟩
      · exact absurd h (by decide)
      · exact h
    obtain ⟨φ₁⟩ := M.nonempty_fixedPoints_equiv τ
    have hgN : g ∈ normalizer (j3P : Set (Equiv.Perm (Fin 6156))) :=
      mem_normalizer_iff.mpr fun x => ⟨fun hx => mul_mem (mul_mem hg hx) (inv_mem hg),
        fun hx => by
          have := mul_mem (mul_mem (inv_mem hg) hx) hg
          rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group] at this⟩
    obtain ⟨φ₂⟩ := nonempty_centralizer_conj_equiv' hgN hgr
    rw [Nat.card_congr (φ₁.trans φ₂).toEquiv, inf_comm, hcard, h2448]

end CFSG.ComponentClassification.HarrisLit.HarrisEnd
