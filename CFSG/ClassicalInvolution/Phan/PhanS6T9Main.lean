module

public import CFSG.ClassicalInvolution.Phan.PhanS6T7Frame
public import CFSG.ClassicalInvolution.Phan.PhanS6T8Hyp

public section

namespace CFSG.ClassicalInvolution.PhanB3.S.Std.T

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanB3.S

variable {K : Type} [Field K] {M : Model K}

theorem geom_smul_mid {μ : K} (hμ : μ ≠ 0) {x y z : Vec K} (h : Geom M x (μ • y) z) :
    Geom M x y z := by
  have := (geom_smul M (c := 1) (d := μ⁻¹) (e := 1) one_ne_zero (inv_ne_zero hμ)
    one_ne_zero).2 h
  simpa [smul_smul, inv_mul_cancel₀ hμ] using this

theorem octahedron_exists [Finite K] (hq : 7 ≤ M.q) {a b c : Vec K} (T : TriData M a b c) :
    ∃ p₁ p₂ p₃ : Vec K, IsFF M p₁ ∧ IsFF M p₂ ∧ IsFF M p₃ ∧ Geom M b p₃ p₁ ∧
      Geom M p₃ p₂ p₁ ∧ Geom M p₂ c p₁ ∧ Geom M b c p₁ ∧ Geom M b p₃ a ∧
        Geom M p₃ p₂ a ∧ Geom M p₂ c a := by
  obtain ⟨α, β, μ, r, hμ, hc, hrW, hrr, hτr, hr0⟩ := exists_rational_r (M := M) (by omega) T
  have hD : gram M a b ≠ 0 := T.hab.2
  obtain ⟨F, haF, hbF, hrF, hζ⟩ :=
    exists_frame (by omega) T.ha T.hb T.hab.1 hD hrW hrr hτr hr0
  subst haF hbF hrF
  have hΦc : F.Φ (vc α β) = μ • c := by rw [Frame.Φ_vc, hc]
  have hna : F.gd.na ≠ 0 := T.ha.2
  have hnb : F.gd.nb ≠ 0 := T.hb.2
  have hDg : F.gd.D ≠ 0 := by
    have := F.gram_Φ va vb
    rw [Frame.Φ_va, Frame.Φ_vb, Gd.gramc_ab] at this
    rw [← this]
    exact hD
  have hcol1 : Col M F.b (μ • c) := by
    have := (col_smul M (c := 1) (d := μ) one_ne_zero hμ (x := F.b) (y := c)).2 T.hbc
    simpa using this
  have hcol2 : Col M (μ • c) F.a := by
    have := (col_smul M (c := μ) (d := 1) hμ one_ne_zero (x := c) (y := F.a)).2 T.hca
    simpa using this
  have hα : α ≠ 0 := by
    intro h0
    have := hcol1.2
    rw [← hΦc, ← Frame.Φ_vb (F := F), Frame.gram_Φ, Gd.gramc_bc, h0] at this
    simp [nrm] at this
  have hβ : β ≠ 0 := by
    intro h0
    have := hcol2.2
    rw [← hΦc, ← Frame.Φ_va (F := F), Frame.gram_Φ, Gd.gramc_comm, Gd.gramc_ac, h0] at this
    simp [nrm] at this
  have hnc : F.gd.nc α β ≠ 0 := by
    have h1 : her M (F.Φ (vc α β)) (F.Φ (vc α β)) = F.gd.nc α β := by
      rw [Frame.her_Φ]
      exact Gd.herc_cc F.gd α β
    rw [← h1, hΦc, her_smul_left, her_smul_right, ← mul_assoc]
    exact mul_ne_zero (mul_ne_zero hμ (tau_ne_zero M hμ)) T.hc.2 |> fun h => by
      simpa [mul_assoc] using h
  obtain ⟨w, u, H⟩ := exists_hyp (M := M) hq F.gd hna hnb hDg hα hβ hnc hζ
  have O := Gd.octa_co H
  refine ⟨F.Φ (F.gd.vp1 α w u), F.Φ (F.gd.vp2 β w u), F.Φ (F.gd.vp3 w), F.isFF_Φ O.ff1,
    F.isFF_Φ O.ff2, F.isFF_Φ O.ff3, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [Frame.Φ_vb] using F.geom_Φ O.t1
  · exact F.geom_Φ O.t2
  · have := F.geom_Φ O.t3
    rw [hΦc] at this
    exact geom_smul_mid hμ this
  · have := F.geom_Φ O.t4
    rw [hΦc, Frame.Φ_vb] at this
    exact geom_smul_mid hμ this
  · have := F.geom_Φ O.t5
    rwa [Frame.Φ_vb, Frame.Φ_va] at this
  · have := F.geom_Φ O.t6
    rwa [Frame.Φ_va] at this
  · have := F.geom_Φ O.t7
    rw [hΦc, Frame.Φ_va] at this
    exact geom_smul_mid hμ this

section Points

variable (M)

theorem geomPt_of {X Y Z : FFPt M} {x y z : Vec K} (hX : ∃ s : K, s ≠ 0 ∧ X.1.rep = s • x)
    (hY : ∃ s : K, s ≠ 0 ∧ Y.1.rep = s • y) (hZ : ∃ s : K, s ≠ 0 ∧ Z.1.rep = s • z)
    (h : Geom M x y z) : GeomPt M X Y Z := by
  obtain ⟨s, hs, hXs⟩ := hX
  obtain ⟨t, ht, hYt⟩ := hY
  obtain ⟨v, hv, hZv⟩ := hZ
  unfold GeomPt
  rw [hXs, hYt, hZv]
  exact (geom_smul M hs ht hv).2 h

theorem tri_of_geomPt {X Y Z : FFPt M} (h : GeomPt M X Y Z) : Tri (geomWalks M) X Y Z :=
  ⟨h.1, h.2.1, h.2.2.1, cycleHomotopic_of_mem _ ⟨Y, Z, h.1, h.2.1, h.2.2.1, rfl, h⟩⟩

end Points

theorem triNull_of_model [Finite K] (M : Model K) (hq : 7 ≤ M.q) : TriNull M := by
  intro a b c hab hbc hca
  by_cases hg : GeomPt M a b c
  · exact cycleHomotopic_of_mem _ ⟨b, c, hab, hbc, hca, rfl, hg⟩
  · have hdet : det3 M a.1.rep b.1.rep c.1.rep = 0 := by
      by_contra h
      exact hg ⟨hab, hbc, hca, Or.inl h⟩
    have hnd : ¬ ∃ s t : K, c.1.rep = s • a.1.rep + t • b.1.rep :=
      fun h => hg ⟨hab, hbc, hca, Or.inr h⟩
    obtain ⟨p₁, p₂, p₃, h₁, h₂, h₃, g₁, g₂, g₃, g₄, g₅, g₆, g₇⟩ :=
      octahedron_exists hq (a := a.1.rep) (b := b.1.rep) (c := c.1.rep)
        ⟨a.2, b.2, c.2, hab, hbc, hca, hdet, hnd⟩
    obtain ⟨s₁, hs₁, hr₁⟩ := FFPt.mk_rep M h₁
    obtain ⟨s₂, hs₂, hr₂⟩ := FFPt.mk_rep M h₂
    obtain ⟨s₃, hs₃, hr₃⟩ := FFPt.mk_rep M h₃
    have e₁ : ∃ s : K, s ≠ 0 ∧ (FFPt.mk M h₁).1.rep = s • p₁ := ⟨s₁, hs₁, hr₁⟩
    have e₂ : ∃ s : K, s ≠ 0 ∧ (FFPt.mk M h₂).1.rep = s • p₂ := ⟨s₂, hs₂, hr₂⟩
    have e₃ : ∃ s : K, s ≠ 0 ∧ (FFPt.mk M h₃).1.rep = s • p₃ := ⟨s₃, hs₃, hr₃⟩
    have ea : ∃ s : K, s ≠ 0 ∧ a.1.rep = s • a.1.rep := ⟨1, one_ne_zero, (one_smul K _).symm⟩
    have eb : ∃ s : K, s ≠ 0 ∧ b.1.rep = s • b.1.rep := ⟨1, one_ne_zero, (one_smul K _).symm⟩
    have ec : ∃ s : K, s ≠ 0 ∧ c.1.rep = s • c.1.rep := ⟨1, one_ne_zero, (one_smul K _).symm⟩
    exact cycleHomotopic_triangle_of_octahedron (p₁ := FFPt.mk M h₁) (p₂ := FFPt.mk M h₂)
      (p₃ := FFPt.mk M h₃) hab hbc hca
      (tri_of_geomPt M (geomPt_of M eb e₃ e₁ g₁)) (tri_of_geomPt M (geomPt_of M e₃ e₂ e₁ g₂))
      (tri_of_geomPt M (geomPt_of M e₂ ec e₁ g₃)) (tri_of_geomPt M (geomPt_of M eb ec e₁ g₄))
      (tri_of_geomPt M (geomPt_of M eb e₃ ea g₅)) (tri_of_geomPt M (geomPt_of M e₃ e₂ ea g₆))
      (tri_of_geomPt M (geomPt_of M e₂ ec ea g₇))

end CFSG.ClassicalInvolution.PhanB3.S.Std.T
