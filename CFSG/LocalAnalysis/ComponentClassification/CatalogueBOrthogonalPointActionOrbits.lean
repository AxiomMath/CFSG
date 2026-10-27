module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionProjective
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasTwo

public section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalPointAction

open QuadraticMap CFSG.ClassicalGroups.Orthogonal
open scoped Classical

universe u v

variable {K : Type u} [Field K]
variable {V : Type v} [AddCommGroup V] [Module K V]
variable (Q : QuadraticForm K V)

theorem pointPerp_self (L : Points Q) : PointPerp L L := by
  obtain ⟨x, hx, hQx, rfl⟩ := exists_eq_pointMk L
  rw [pointPerp_pointMk]
  exact polar_self_eq_zero hQx

@[expose] def perpendicularPoints (L : Points Q) : Set (Points Q) :=
  {M | M ≠ L ∧ PointPerp L M}

@[expose] def nonperpendicularPoints (L : Points Q) : Set (Points Q) :=
  {M | ¬ PointPerp L M}

theorem pointMk_ne_of_pairings {x y z : V} (hx : x ≠ 0) (hy : y ≠ 0)
    (hQx : Q x = 0) (hQy : Q y = 0) (hxz : polar Q x z ≠ 0)
    (hyz : polar Q y z = 0) : pointMk x hx hQx ≠ pointMk y hy hQy := by
  intro h
  obtain ⟨a, ha⟩ := (pointMk_eq_iff hx hy hQx hQy).mp h
  apply hxz
  rw [← ha, polar_smul_left_eq, hyz, mul_zero]

theorem projective_stabilizer_orbit_eq (L M : Points Q) :
    MulAction.orbit (projectiveStabilizer Q L) M =
      MulAction.orbit (elementaryStabilizer Q L) M := by
  ext N
  rw [MulAction.mem_orbit_iff, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨g, hg⟩
    obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective (scalarKernel Q) g.val
    have hfix : a • L = L := by
      have h : g.val • L = L := g.property
      rw [← ha, quotient_smul] at h
      exact h
    refine ⟨⟨a, hfix⟩, ?_⟩
    have h : g.val • M = N := hg
    rw [← ha, quotient_smul] at h
    exact h
  · rintro ⟨g, hg⟩
    refine ⟨⟨QuotientGroup.mk' (scalarKernel Q) g.val, ?_⟩, ?_⟩
    · change (QuotientGroup.mk' (scalarKernel Q) g.val) • L = L
      rw [quotient_smul]
      exact g.property
    · change (QuotientGroup.mk' (scalarKernel Q) g.val) • M = N
      rw [quotient_smul]
      exact hg

variable [FiniteDimensional K V]

theorem elementary_stabilizer_orbit_iff (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (L M N : Points Q) :
    N ∈ MulAction.orbit (elementaryStabilizer Q L) M ↔
      (M = L ↔ N = L) ∧ (PointPerp L M ↔ PointPerp L N) := by
  rw [MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨g, hg⟩
    have hfix : g.val • L = L := g.property
    have hmove : g.val • M = N := hg
    have heq : M = L ↔ N = L := by
      constructor
      · rintro rfl
        rw [← hmove, hfix]
      · intro hNL
        apply (MulAction.toPerm g.val).injective
        change g.val • M = g.val • L
        rw [hmove, hfix, hNL]
    refine ⟨heq, ?_⟩
    have h := pointPerp_smul_iff g.val L M
    rw [hfix, hmove] at h
    exact h.symm
  · rintro ⟨heq, hperp⟩
    by_cases hML : M = L
    · have hNL := heq.mp hML
      subst M
      subst N
      exact ⟨1, one_smul _ _⟩
    have hNL : N ≠ L := fun h => hML (heq.mpr h)
    obtain ⟨e, he0, he, rfl⟩ := exists_eq_pointMk L
    obtain ⟨P₁, P₂, P₃, rfl, h₁₂, h₁₃, h₂₃⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.quadratic_three_hyperbolic_pairs hQ hT he he0
    obtain ⟨x, hx0, hx, rfl⟩ := exists_eq_pointMk M
    obtain ⟨y, hy0, hy, rfl⟩ := exists_eq_pointMk N
    by_cases hex : polar Q P₁.e x = 0
    · have hey : polar Q P₁.e y = 0 := by
        rw [← pointPerp_pointMk P₁.e_ne_zero hy0 P₁.Q_e hy]
        exact hperp.mp ((pointPerp_pointMk P₁.e_ne_zero hx0 P₁.Q_e hx).mpr hex)
      have hxe : ∀ a : K, x ≠ a • P₁.e := by
        intro a ha
        exact hML ((pointMk_eq_iff hx0 P₁.e_ne_zero hx P₁.Q_e).mpr ⟨a, ha.symm⟩)
      have hye : ∀ a : K, y ≠ a • P₁.e := by
        intro a ha
        exact hNL ((pointMk_eq_iff hy0 P₁.e_ne_zero hy P₁.Q_e).mpr ⟨a, ha.symm⟩)
      obtain ⟨g, hg, hge, hgx⟩ :=
        exists_fix_apply_eq_of_polar_eq_zero h₁₂ h₁₃ h₂₃ hQ hx hex hxe
      obtain ⟨k, hk, hke, hky⟩ :=
        exists_fix_apply_eq_of_polar_eq_zero h₁₂ h₁₃ h₂₃ hQ hy hey hye
      let g₀ : elementaryGroup Q := ⟨g, hg⟩
      let k₀ : elementaryGroup Q := ⟨k, hk⟩
      have hgL : g₀ • pointMk P₁.e P₁.e_ne_zero P₁.Q_e =
          pointMk P₁.e P₁.e_ne_zero P₁.Q_e :=
        smul_pointMk_of_apply_eq_smul _ _ _ _ (a := 1) (by simpa using hge)
      have hkL : k₀ • pointMk P₁.e P₁.e_ne_zero P₁.Q_e =
          pointMk P₁.e P₁.e_ne_zero P₁.Q_e :=
        smul_pointMk_of_apply_eq_smul _ _ _ _ (a := 1) (by simpa using hke)
      have hgM : g₀ • pointMk x hx0 hx = pointMk P₂.e P₂.e_ne_zero P₂.Q_e :=
        smul_pointMk_of_apply_eq_smul _ _ _ _ (a := 1) (by simpa using hgx)
      have hkN : k₀ • pointMk y hy0 hy = pointMk P₂.e P₂.e_ne_zero P₂.Q_e :=
        smul_pointMk_of_apply_eq_smul _ _ _ _ (a := 1) (by simpa using hky)
      refine ⟨⟨k₀⁻¹ * g₀, ?_⟩, ?_⟩
      · change (k₀⁻¹ * g₀) • pointMk P₁.e P₁.e_ne_zero P₁.Q_e = _
        rw [mul_smul, hgL]
        exact inv_smul_eq_iff.mpr hkL.symm
      · change (k₀⁻¹ * g₀) • pointMk x hx0 hx = pointMk y hy0 hy
        rw [mul_smul, hgM, ← hkN, inv_smul_smul]
    · have hey : polar Q P₁.e y ≠ 0 := by
        intro h
        apply hex
        rw [← pointPerp_pointMk P₁.e_ne_zero hx0 P₁.Q_e hx]
        exact hperp.mpr ((pointPerp_pointMk P₁.e_ne_zero hy0 P₁.Q_e hy).mpr h)
      obtain ⟨g, hg, hge, a, hgy⟩ :=
        exists_fix_apply_eq_smul_of_polar_ne_zero P₁.Q_e hx hy hex hey
      let g₀ : elementaryGroup Q := ⟨g, hg⟩
      refine ⟨⟨g₀, ?_⟩, ?_⟩
      · change g₀ • pointMk P₁.e P₁.e_ne_zero P₁.Q_e = _
        exact smul_pointMk_of_apply_eq_smul _ _ _ _ (a := 1) (by simpa using hge)
      · exact smul_pointMk_of_apply_eq_smul _ _ _ _ hgy

theorem elementary_stabilizer_orbit (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (L M : Points Q) :
    MulAction.orbit (elementaryStabilizer Q L) M =
      if M = L then {L} else if PointPerp L M then perpendicularPoints Q L
      else nonperpendicularPoints Q L := by
  classical
  ext N
  rw [elementary_stabilizer_orbit_iff Q hQ hT]
  split_ifs with hML hLM
  · constructor
    · rintro ⟨heq, -⟩
      exact heq.mp hML
    · intro h
      have hNL : N = L := h
      rw [hML, hNL]
      exact ⟨Iff.rfl, Iff.rfl⟩
  · simp [perpendicularPoints, hML, hLM]
  · constructor
    · rintro ⟨-, h⟩
      exact fun hLN => hLM (h.mpr hLN)
    · intro hLN
      have hNL : N ≠ L := by
        intro h
        apply hLN
        rw [h]
        exact pointPerp_self Q L
      exact ⟨iff_of_false hML hNL, iff_of_false hLM hLN⟩

theorem projective_stabilizer_orbit_iff (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (L M N : Points Q) :
    N ∈ MulAction.orbit (projectiveStabilizer Q L) M ↔
      (M = L ↔ N = L) ∧ (PointPerp L M ↔ PointPerp L N) := by
  rw [projective_stabilizer_orbit_eq]
  exact elementary_stabilizer_orbit_iff Q hQ hT L M N

theorem projective_stabilizer_orbit (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (L M : Points Q) :
    MulAction.orbit (projectiveStabilizer Q L) M =
      if M = L then {L} else if PointPerp L M then perpendicularPoints Q L
      else nonperpendicularPoints Q L := by
  rw [projective_stabilizer_orbit_eq]
  exact elementary_stabilizer_orbit Q hQ hT L M

theorem off_diagonal_points (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (L : Points Q) :
    (∃ M N : Points Q, M ≠ N ∧ M ∈ perpendicularPoints Q L ∧
      N ∈ perpendicularPoints Q L) ∧
    (∃ M N : Points Q, M ≠ N ∧ M ∈ nonperpendicularPoints Q L ∧
      N ∈ nonperpendicularPoints Q L) := by
  obtain ⟨e, he0, he, rfl⟩ := exists_eq_pointMk L
  obtain ⟨P₁, P₂, P₃, rfl, h₁₂, h₁₃, h₂₃⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.quadratic_three_hyperbolic_pairs hQ hT he he0
  have he₂ : pointMk P₂.e P₂.e_ne_zero P₂.Q_e ≠
      pointMk P₁.e P₁.e_ne_zero P₁.Q_e :=
    pointMk_ne_of_pairings Q _ _ _ _ (by rw [P₂.polar_ef]; exact one_ne_zero) h₁₂.ef
  have he₃ : pointMk P₃.e P₃.e_ne_zero P₃.Q_e ≠
      pointMk P₁.e P₁.e_ne_zero P₁.Q_e :=
    pointMk_ne_of_pairings Q _ _ _ _ (by rw [P₃.polar_ef]; exact one_ne_zero) h₁₃.ef
  have he₂₃ : pointMk P₂.e P₂.e_ne_zero P₂.Q_e ≠
      pointMk P₃.e P₃.e_ne_zero P₃.Q_e :=
    pointMk_ne_of_pairings Q _ _ _ _ (by rw [P₂.polar_ef]; exact one_ne_zero)
      (by rw [polar_comm]; exact h₂₃.fe)
  have hQs : Q (P₁.f + P₂.e) = 0 := by
    rw [QuadraticMap.map_add Q, P₁.Q_f, P₂.Q_e, h₁₂.fe, add_zero, add_zero]
  have hpols : polar Q P₁.e (P₁.f + P₂.e) = 1 := by
    rw [polar_add_right, P₁.polar_ef, h₁₂.ee, add_zero]
  have hs0 : P₁.f + P₂.e ≠ 0 := by
    intro h
    rw [h, polar_zero_right] at hpols
    exact zero_ne_one hpols
  have hfs : pointMk P₁.f P₁.f_ne_zero P₁.Q_f ≠ pointMk (P₁.f + P₂.e) hs0 hQs := by
    apply Ne.symm
    apply pointMk_ne_of_pairings Q _ _ _ _ (z := P₂.f)
    · rw [polar_add_left, h₁₂.ff, P₂.polar_ef, zero_add]
      exact one_ne_zero
    · exact h₁₂.ff
  constructor
  · refine ⟨pointMk P₂.e P₂.e_ne_zero P₂.Q_e, pointMk P₃.e P₃.e_ne_zero P₃.Q_e,
      he₂₃, ⟨he₂, ?_⟩, ⟨he₃, ?_⟩⟩
    · exact (pointPerp_pointMk _ _ _ _).mpr h₁₂.ee
    · exact (pointPerp_pointMk _ _ _ _).mpr h₁₃.ee
  · refine ⟨pointMk P₁.f P₁.f_ne_zero P₁.Q_f, pointMk (P₁.f + P₂.e) hs0 hQs,
      hfs, ?_, ?_⟩
    · change ¬ PointPerp _ _
      rw [pointPerp_pointMk, P₁.polar_ef]
      exact one_ne_zero
    · change ¬ PointPerp _ _
      rw [pointPerp_pointMk, hpols]
      exact one_ne_zero

theorem exists_stabilizer_move (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (L M : Points Q) (hML : M ≠ L) :
    ∃ g : projectiveStabilizer Q L, g • M ≠ M := by
  have htwo := off_diagonal_points Q hQ hT L
  have hchoose : ∀ S : Set (Points Q),
      (∃ U W : Points Q, U ≠ W ∧ U ∈ S ∧ W ∈ S) →
      ∃ N : Points Q, N ≠ M ∧ N ∈ S := by
    rintro S ⟨U, W, hUW, hU, hW⟩
    by_cases hUM : U = M
    · exact ⟨W, by rw [← hUM]; exact hUW.symm, hW⟩
    · exact ⟨U, hUM, hU⟩
  by_cases hLM : PointPerp L M
  · obtain ⟨N, hNM, hNL, hLN⟩ := hchoose _ htwo.1
    have horbit : N ∈ MulAction.orbit (projectiveStabilizer Q L) M := by
      rw [projective_stabilizer_orbit_iff Q hQ hT]
      exact ⟨iff_of_false hML hNL, iff_of_true hLM hLN⟩
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp horbit
    exact ⟨g, by rw [hg]; exact hNM⟩
  · obtain ⟨N, hNM, hLN⟩ := hchoose _ htwo.2
    have hNL : N ≠ L := by
      intro h
      subst N
      exact hLN (pointPerp_self Q L)
    have horbit : N ∈ MulAction.orbit (projectiveStabilizer Q L) M := by
      rw [projective_stabilizer_orbit_iff Q hQ hT]
      exact ⟨iff_of_false hML hNL, iff_of_false hLM hLN⟩
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp horbit
    exact ⟨g, by rw [hg]; exact hNM⟩

theorem projectiveStabilizer_injective (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) :
    Function.Injective (projectiveStabilizer Q) := by
  intro L M hstab
  by_contra hLM
  obtain ⟨g, hg⟩ := exists_stabilizer_move Q hQ hT L M (fun h => hLM h.symm)
  have hmem : g.val ∈ projectiveStabilizer Q M := hstab ▸ g.property
  exact hg hmem

end CFSG.ComponentClassification.CatalogueBOrthogonalPointAction
