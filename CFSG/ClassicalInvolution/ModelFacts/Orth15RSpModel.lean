module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15RSpKlein
public import CFSG.ClassicalInvolution.ModelFacts.Orth15TwinRows

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerSp

open QuadraticAlgebra CFSG.ClassicalInvolution.Models.SymplecticPairs
  CFSG.LieType.Universal.Symplectic.SpExtras CFSG.Assembly.LowTwoRank CFSG.LieType.Steinberg.Sp
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.FrameVertex
open CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerL4 (QE r0 coe_r0 exists_conj_r0 sl2_sq_cases
  mem_sup_of_comm isQuasisimple_sl2 sup_le_normalizer_of_comm exists_sq_add_sq)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterSp4 (twin_std_sp)
open scoped Matrix MatrixGroups

variable {F : Type} [Field F]

theorem alphaOf_twin_psp_core [Finite F] [Group.IsPerfect (StatedSp 2 F)] (h2 : (2 : F) ≠ 0)
    (h4 : 4 ≤ Nat.card F) {H : Type} [Group H] [Finite H] (ψ : StatedSp 2 F →* H)
    (hker : ψ.ker ≤ Subgroup.center (StatedSp 2 F)) {R R' : Subgroup (StatedSp 2 F)}
    {g : StatedSp 2 F} (hRg : R = (R0 F).map (MulAut.conj g).toMonoidHom)
    (hR'g : R' = (R0' F).map (MulAut.conj g).toMonoidHom) {x x' : StatedSp 2 F} (hxR : x ∈ R)
    (hx2 : x * x = 1) (hx1 : x ≠ 1) (hx'R' : x' ∈ R') (hx'2 : x' * x' = 1) (hx'1 : x' ≠ 1)
    (hsame : ψ x = ψ x') {u : H} (hun : u ∈ Subgroup.normalizer (ψ.range : Set H))
    (hu : u ∈ R.map ψ ⊔ R'.map ψ) (hu2 : u * u = 1) (hu1 : u ≠ 1) (huz : u ≠ ψ x) :
    alphaOf (Subgroup.closure ({toInducedAutOn ψ.range ⟨u, hun⟩,
      toInducedAutOn ψ.range ⟨ψ x, FrameVertex.mem_normalizer_range ψ x⟩} :
        Set ↥(inducedAutOn ψ.range))) = ⊥ := by
  have hLR : IsLongRootSp2 R (g * x0 F * g⁻¹) := ⟨0, g, hRg, rfl⟩
  have hLR' : IsLongRootSp2 R' (g * longInv F 2 1 * g⁻¹) := ⟨1, g, hR'g, rfl⟩
  have hxg : x = g * x0 F * g⁻¹ :=
    hLR.eq_of_orderOf_eq_two h2 hxR (orderOf_eq_prime (by rwa [pow_two]) hx1)
  have hx'g : x' = zneg F * x := by
    have := hLR'.eq_of_orderOf_eq_two h2 hx'R' (orderOf_eq_prime (by rwa [pow_two]) hx'1)
    rw [this, ← zneg_mul_x0_eq_longInv, hxg]
    calc g * (zneg F * x0 F) * g⁻¹ = (g * zneg F * g⁻¹) * (g * x0 F * g⁻¹) := by group
      _ = zneg F * (g * x0 F * g⁻¹) := by rw [zneg_conj]
  have hzneg : ψ (zneg F) = 1 := by
    have h1 : ψ x' = ψ (zneg F) * ψ x := by rw [hx'g, map_mul]
    rw [← hsame] at h1
    exact mul_eq_right.mp h1.symm
  have hu' : u ∈ (R ⊔ R').map ψ := by
    rw [Subgroup.map_sup]
    exact hu
  obtain ⟨s, hs, hsu⟩ := hu'
  have hs' : s ∈ (R0 F ⊔ R0' F).map (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.map_sup, ← hRg, ← hR'g]
    exact hs
  obtain ⟨w, hw, rfl⟩ := hs'
  have hsu' : ψ (g * w * g⁻¹) = u := hsu
  have hww : w * w ∈ Subgroup.center (StatedSp 2 F) := by
    have h1 : (g * w * g⁻¹) * (g * w * g⁻¹) ∈ Subgroup.center (StatedSp 2 F) :=
      hker (by rw [MonoidHom.mem_ker, map_mul, hsu', hu2])
    have e : (g * w * g⁻¹) * (g * w * g⁻¹) = g * (w * w) * g⁻¹ := by group
    rw [e] at h1
    exact InnerL4.mem_center_of_conj_mem_center h1
  rcases classify_w h2 hw hww with rfl | rfl | rfl | rfl | ⟨h, hh, rfl⟩
  · exact absurd (by simpa using hsu'.symm) hu1
  · exact absurd (by rw [hxg]; exact hsu'.symm) huz
  · refine absurd ?_ huz
    have e : g * (zneg F * x0 F) * g⁻¹ = zneg F * x := by
      calc g * (zneg F * x0 F) * g⁻¹ = (g * zneg F * g⁻¹) * (g * x0 F * g⁻¹) := by group
        _ = zneg F * x := by rw [zneg_conj, hxg]
    rw [e, map_mul, hzneg, one_mul] at hsu'
    exact hsu'.symm
  · refine absurd ?_ hu1
    rw [zneg_conj, hzneg] at hsu'
    exact hsu'.symm
  · have hxh : h * x0 F = x0 F * h := by
      have := (slayer_x0 h2 h4).comm h hh
      exact this
    have key := alphaOf_klein_psp h2 h4 ψ hker hzneg (g * h)
    have e1 : toInducedAutOn ψ.range ⟨u, hun⟩ = innerHom ψ (g * h * u0 F * (g * h)⁻¹) := by
      rw [innerHom_apply]
      congr 1
      apply Subtype.ext
      show u = ψ (g * h * u0 F * (g * h)⁻¹)
      rw [← hsu']
      congr 1
      group
    have e2 : toInducedAutOn ψ.range ⟨ψ x, FrameVertex.mem_normalizer_range ψ x⟩ =
        innerHom ψ (g * h * x0 F * (g * h)⁻¹) := by
      rw [innerHom_apply]
      congr 1
      apply Subtype.ext
      show ψ x = ψ (g * h * x0 F * (g * h)⁻¹)
      congr 1
      rw [hxg]
      calc g * x0 F * g⁻¹ = g * (h * x0 F * h⁻¹) * g⁻¹ := by rw [hxh]; group
        _ = g * h * x0 F * (g * h)⁻¹ := by group
    rw [e1, e2]
    exact key


theorem alphaOf_twin_psp [Finite F] [Group.IsPerfect (StatedSp 2 F)] (h2 : (2 : F) ≠ 0)
    (h4 : 4 ≤ Nat.card F) {H : Type} [Group H] [Finite H] (ψ : StatedSp 2 F →* H)
    (hker : ψ.ker ≤ Subgroup.center (StatedSp 2 F)) {R R' : Subgroup (StatedSp 2 F)}
    (hR : ∃ i, IsLongRootSp2 R i) (hR' : ∃ i, IsLongRootSp2 R' i) (hne : R ≠ R')
    {x x' : StatedSp 2 F} (hxR : x ∈ R) (hx2 : x * x = 1) (hx1 : x ≠ 1) (hx'R' : x' ∈ R')
    (hx'2 : x' * x' = 1) (hx'1 : x' ≠ 1) (hsame : ψ x = ψ x') {u : H}
    (hun : u ∈ Subgroup.normalizer (ψ.range : Set H)) (hu : u ∈ R.map ψ ⊔ R'.map ψ)
    (hu2 : u * u = 1) (hu1 : u ≠ 1) (huz : u ≠ ψ x) :
    alphaOf (Subgroup.closure ({toInducedAutOn ψ.range ⟨u, hun⟩,
      toInducedAutOn ψ.range ⟨ψ x, FrameVertex.mem_normalizer_range ψ x⟩} :
        Set ↥(inducedAutOn ψ.range))) = ⊥ := by
  have hc : x' * x⁻¹ ∈ Subgroup.center (StatedSp 2 F) :=
    hker (by rw [MonoidHom.mem_ker, map_mul, map_inv, ← hsame, mul_inv_cancel])
  obtain ⟨g, k, hRg, hR'g⟩ := twin_std_sp h2 hR hR' hne hxR hx2 hx1 hx'R' hx'2 hx'1 hc
  have hk : k = 0 ∨ k = 1 := by omega
  rcases hk with rfl | rfl
  · exact alphaOf_twin_psp_core h2 h4 ψ hker hRg hR'g hxR hx2 hx1 hx'R' hx'2 hx'1 hsame hun hu hu2
      hu1 huz
  · have hrev : Fin.rev (1 : Fin 2) = 0 := rfl
    rw [hrev] at hR'g
    have key := alphaOf_twin_psp_core h2 h4 ψ hker hR'g hRg hx'R' hx'2 hx'1 hxR hx2 hx1 hsame.symm
      hun (by rwa [sup_comm]) hu2 hu1 (by rwa [← hsame])
    have e : toInducedAutOn ψ.range ⟨ψ x', FrameVertex.mem_normalizer_range ψ x'⟩ =
        toInducedAutOn ψ.range ⟨ψ x, FrameVertex.mem_normalizer_range ψ x⟩ := by
      congr 2
      exact hsame.symm
    rwa [e] at key


theorem twinInnerAlpha_psp2 {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {e : ℕ} (hq : 5 ≤ p ^ e)
    (hadm : StatedLieAdmissible .PSp 2 p e) : TwinInnerAlpha p e .PSp 2 := by
  have hf : 1 ≤ e := hadm.2.1
  have h2 : (2 : GaloisField p e) ≠ 0 := two_ne_zero_galoisField e hp2
  have h4 : 4 ≤ Nat.card (GaloisField p e) := by
    rw [GaloisField.card p e (by omega)]
    omega
  have : Group.IsPerfect (StatedSp 2 (GaloisField p e)) :=
    Group.isPerfect_def.2 (modelClauseZero .PSp 2 p e Fact.out trivial hadm).1.1
  intro H _ _ ψ R R' x x' hpair u hun hu hu2 hu1 huz
  exact alphaOf_twin_psp h2 h4 ψ hpair.ker
    ((exists_isLongRootSp2_iff h2 R).mpr ((mem_fundamentalSubgroups_PSp_iff hadm R).mp hpair.mem))
    ((exists_isLongRootSp2_iff h2 R').mpr
      ((mem_fundamentalSubgroups_PSp_iff hadm R').mp hpair.mem'))
    hpair.ne hpair.hx hpair.hx2 hpair.hx1 hpair.hx' hpair.hx'2 hpair.hx'1 hpair.same hun hu hu2
    hu1 huz


end CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerSp

namespace CFSG.ClassicalInvolution.Asc77


theorem twinSmallInnerSp (p : ℕ) [Fact p.Prime] : TwinSmallInnerSp p := fun hp2 _ hq hadm =>
  ModelFacts.Orth15.InnerSp.twinInnerAlpha_psp2 hp2 hq hadm

end CFSG.ClassicalInvolution.Asc77
