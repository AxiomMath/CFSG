module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263SDLinSel

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263.SD.Lin

open Polynomial Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ComponentClassification CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.CALinearPrimary
  CFSG.LocalAnalysis.GLTheoremA.T263.SD

variable {K : Type} [Field K] [Finite K] {n : ℕ}

theorem glA_mem_centralizer_of_comm {A B : GL (Fin n) K} (h : B * A = A * B) :
    glA B ∈ gl_centralizer (glA A) := by
  rw [mem_gl_centralizer]
  have h3 : (glA B) * (glA A) = (glA A) * (glA B) := by
    show Matrix.GeneralLinearGroup.toLin B * Matrix.GeneralLinearGroup.toLin A =
      Matrix.GeneralLinearGroup.toLin A * Matrix.GeneralLinearGroup.toLin B
    rw [← map_mul, ← map_mul, h]
  have h4 := congrArg (fun z : LinearMap.GeneralLinearGroup K (Fin n → K) =>
    (z : Module.End K (Fin n → K))) h3
  simp only [Units.val_mul] at h4
  exact h4

theorem famSel_linear (h2 : (2 : K) = 0) (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : p = 3 → 4 ≤ Nat.card K) :
    FamSel p (projectiveSL n K) (fun φ => ∃ A : GL (Fin n) K, φ = conjAut n K A) := by
  classical
  intro u hinn hup hu1 𝔹 h𝔹 Y hYfix hY2 hYinv hcomm
  obtain ⟨A, rfl⟩ := hinn
  have hn0 : 0 < n := by omega
  haveI : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
  have hpk : (p : K) ≠ 0 := by
    intro h0
    have := (CharP.cast_eq_zero_iff K 2 p).1 h0
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 this).symm
  obtain ⟨c, hAp⟩ := pow_scalar_of_conjAut_pow hn hup
  have hsq := squarefree_minpoly_glA hpk hAp
  have hY2' : ∀ w ∈ Y, ∃ k : ℕ, w ^ (2 ^ k) = 1 := fun w hw => by
    obtain ⟨k, hk⟩ := hY2 ⟨w, hw⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  have lift2 : ∀ w ∈ Y, ∃ g : Matrix.SpecialLinearGroup (Fin n) K, proj n K g = w ∧
      (∃ k : ℕ, g ^ (2 ^ k) = 1) ∧ slGL n K g ∈ gl_centralizer (glA A) := by
    intro w hw
    obtain ⟨k, hk⟩ := hY2' w hw
    obtain ⟨g, hg, hgk⟩ := exists_lift_two_pow h2 hn0 hk
    exact ⟨g, hg, ⟨k, hgk⟩, lift_commutes h2 hn0 (hYfix hw) hg hgk⟩
  have hcommY : ∀ b ∈ 𝔹, ∀ y ∈ Y, b y * y⁻¹ ∈ Y := by
    intro b hb y hy
    have h1 : b.toMonoidHom y ∈ Y.map b.toMonoidHom := Subgroup.mem_map_of_mem _ hy
    rw [hYinv b hb] at h1
    exact Y.mul_mem h1 (Y.inv_mem hy)
  obtain ⟨b, hb, y, hy, hz⟩ : ∃ b ∈ 𝔹, ∃ y ∈ Y, b y * y⁻¹ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply hcomm
    rw [autComm, eq_bot_iff, Subgroup.closure_le]
    rintro z ⟨b, hb, y, hy, rfl⟩
    exact Subgroup.mem_bot.2 (hcon b hb y hy)
  obtain ⟨⟨B, rfl⟩, hbp, hbu⟩ := h𝔹 b hb
  have hzY : conjAut n K B y * y⁻¹ ∈ Y := hcommY _ hb y hy
  obtain ⟨g, hgy, ⟨k₁, hg2⟩, hgc⟩ := lift2 y hy
  obtain ⟨zt, hzt, ⟨k₂, hzt2⟩, hztc⟩ := lift2 _ hzY
  have hzt1 : zt ≠ 1 := by
    intro h1
    apply hz
    rw [← hzt, h1, map_one]
  have hrel : proj n K (CatalogueBHigherLinearAction.slConjugation n K B g * g⁻¹) =
      proj n K zt := by
    rw [map_mul, map_inv, ← conjAut_proj, hgy, hzt]
  have hs : (CatalogueBHigherLinearAction.slConjugation n K B g * g⁻¹)⁻¹ * zt ∈ scalars n K :=
    proj_eq_proj_iff.1 hrel
  have hzt_eq : zt = CatalogueBHigherLinearAction.slConjugation n K B g * g⁻¹ *
      ((CatalogueBHigherLinearAction.slConjugation n K B g * g⁻¹)⁻¹ * zt) :=
    (mul_inv_cancel_left _ _).symm
  have hzt_gl : slGL n K zt ≠ 1 := fun h1 => hzt1 (slGL_injective (by rw [h1, map_one]))
  have hzt_pow : (slGL n K zt) ^ (2 ^ k₂) = 1 := by rw [← map_pow, hzt2, map_one]
  obtain ⟨h, hh, hgood, v, hv, hne⟩ := exists_good_block h2 hsq hztc hzt_pow hzt_gl
    (fun h hh hm2 hq => bad_block_trivial h2 hn hp hp2 hK hsq hbu hbp hgc hs hh hm2 hq)
  have hgood' := hgood
  unfold IsGoodFactor at hgood'
  refine ⟨(specialFactor A h).map (proj n K), isComponentOf_map_specialFactor hsq hh hgood, ?_, ?_, ?_⟩
  ·
    refine dvd_card_centerQuot_map_of_dvd hsq hh hgood hp ?_
    haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
    haveI : Finite (AdjoinRoot h) := Module.finite_of_finite K
    have hm : 2 ≤ primaryMultiplicity (glA A : Module.End K (Fin n → K)) h := by omega
    by_cases hpq : p ∣ Nat.card (AdjoinRoot h) - 1
    · exact dvd_card_specialFactor_of_dvd_units hsq hh hm hp hpq
    · obtain ⟨ζ, hζ⟩ := comm_scalar_of_conjAut_comm hn hbu
      have hζp : ζ ^ p = 1 := commutator_scalar_pow_eq_one hn0 hAp hζ
      have hζ1 : ζ = 1 := units_pow_eq_one_of_not_dvd (E := AdjoinRoot h) hp hpq hζp
      rw [hζ1, map_one] at hζ
      have hBA : B * A = A * B := mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 hζ)
      have hBc : glA B ∈ gl_centralizer (glA A) := glA_mem_centralizer_of_comm hBA
      obtain ⟨c₁, hBp⟩ := pow_scalar_of_conjAut_pow hn hbp
      exact dvd_card_specialFactor_of_noncentral hsq hh hp hpq hBc hBp
        (not_scalar_on_block h2 hsq hh hgc hBc hzt_eq hs hzt2 hv hne)
  ·
    intro hbot
    obtain ⟨g', hg'F, hg'2, hnc⟩ := exists_noncommuting_in_block h2 hsq hztc hzt_pow hh hv hne
    obtain ⟨f, hf⟩ := mem_range_slGL (det_eq_one_of_mem_linearSpecialBlock hsq hh hg'F)
    have hfF : f ∈ specialFactor A h := by
      show slGL n K f ∈ linearSpecialBlock (glA A) h
      rw [hf]
      exact hg'F
    have hf2 : f ^ 2 = 1 := slGL_injective (by rw [map_pow, hf, map_one]; exact hg'2)
    have hzmem : conjAut n K B y * y⁻¹ ∈ autComm 𝔹 Y :=
      Subgroup.subset_closure ⟨_, hb, y, hy, rfl⟩
    have hjmem : proj n K f ∈ (specialFactor A h).map (proj n K) :=
      Subgroup.mem_map_of_mem _ hfF
    have hcc := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hbot hzmem
    have hc1 := Subgroup.mem_centralizer_iff.1 hcc (proj n K f) hjmem
    have h5 : proj n K (zt * f * zt⁻¹) = proj n K f := by
      rw [map_mul, map_mul, map_inv, hzt]
      exact mul_inv_eq_iff_eq_mul.2 hc1.symm
    have h6 := conj_eq_of_proj_eq_of_scalars
      (fun z hz hz2 => scalars_eq_one_of_sq h2 hn0 hz hz2) hf2 h5
    apply hnc
    have h7 : zt * f = f * zt := mul_inv_eq_iff_eq_mul.1 h6
    have h8 := congrArg (slGL n K) h7
    rw [map_mul, map_mul, hf] at h8
    exact h8
  ·
    rw [autComm, Subgroup.closure_le]
    rintro _ ⟨b', hb', y', hy', rfl⟩
    obtain ⟨zt', hzt', ⟨k, hk⟩, hztc'⟩ := lift2 _ (hcommY b' hb' y' hy')
    obtain ⟨w₁, hw₁, w₂, hw₂c, hw₂comm, hdec⟩ := exists_decomp_sl h2 hsq hztc' hk hh
    rw [SetLike.mem_coe, ← hzt', hdec, map_mul]
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_inf.2 ⟨?_, ?_⟩))
      (Subgroup.mem_sup_left (Subgroup.mem_map_of_mem _ hw₁))
    · exact proj_mem_fix (mem_fixSubgroup_slConjugation_iff.2 hw₂c)
    · refine Subgroup.mem_centralizer_iff.2 ?_
      rintro _ ⟨f, hf, rfl⟩
      rw [← map_mul, ← map_mul, hw₂comm f hf]

end CFSG.LocalAnalysis.GLTheoremA.T263.SD.Lin

end
