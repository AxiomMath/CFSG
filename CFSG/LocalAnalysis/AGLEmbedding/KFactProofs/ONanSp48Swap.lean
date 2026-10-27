module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSp48Theta
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSp48Setup
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSp48Aut

public section

namespace CFSG.AGLEmbedding.KFactProofs.Sp48

open scoped MatrixGroups Matrix
open CFSG.Quasithin CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.QuasithinUnique.Lin2.Five (tauAut tauAut_proj)
open CFSG.RankThree.PartTwo.KFacts (conjAut_mem_inner_of_charTwo)

theorem spFPF_fieldSp (σ : GF8 ≃+* GF8) {g : Sp8} (hg : SpFPF g) :
    SpFPF (fieldSp 2 GF8 σ g) := by
  intro v hv
  have hmat : mat 2 GF8 (fieldSp 2 GF8 σ g) = (mat 2 GF8 g).map σ := rfl
  rw [hmat] at hv
  have hw : mat 2 GF8 g *ᵥ (fun i => σ.symm (v i)) = fun i => σ.symm (v i) := by
    funext i
    apply σ.injective
    have h1 := σ.toRingHom.map_mulVec (mat 2 GF8 g) (fun i => σ.symm (v i)) i
    have h2 : (σ.toRingHom ∘ fun i => σ.symm (v i)) = v := by
      funext j
      simp
    rw [h2] at h1
    have h3 := congrFun hv i
    simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe] at h1 ⊢
    rw [h1, h3]
    simp
  have := hg _ hw
  funext i
  have h4 := congrFun this i
  simpa using h4

theorem spFPF_conjSp (A : gsp 2 GF8) {g : Sp8} (hg : SpFPF g) : SpFPF (conjSp 2 GF8 A g) := by
  intro v hv
  have hmat : mat 2 GF8 (conjSp 2 GF8 A g) =
      ((A : GL (Fin 2 ⊕ Fin 2) GF8) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) GF8) * mat 2 GF8 g *
        (((A : GL (Fin 2 ⊕ Fin 2) GF8)⁻¹ : GL (Fin 2 ⊕ Fin 2) GF8) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) GF8) := rfl
  rw [hmat] at hv
  set Am : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) GF8 :=
    ((A : GL (Fin 2 ⊕ Fin 2) GF8) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) GF8) with hAm
  set Ai : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) GF8 :=
    (((A : GL (Fin 2 ⊕ Fin 2) GF8)⁻¹ : GL (Fin 2 ⊕ Fin 2) GF8) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) GF8) with hAi
  have hAA : Am * Ai = 1 := by
    rw [hAm, hAi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hAA' : Ai * Am = 1 := by
    rw [hAm, hAi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h1 : mat 2 GF8 g *ᵥ (Ai *ᵥ v) = Ai *ᵥ v := by
    have h2 : (Ai * (Am * mat 2 GF8 g * Ai)) *ᵥ v = Ai *ᵥ v := by
      rw [← Matrix.mulVec_mulVec, hv]
    have h3 : Ai * (Am * mat 2 GF8 g * Ai) = mat 2 GF8 g * Ai := by
      calc Ai * (Am * mat 2 GF8 g * Ai) = (Ai * Am) * mat 2 GF8 g * Ai := by
            simp only [mul_assoc]
        _ = mat 2 GF8 g * Ai := by rw [hAA', one_mul]
    rw [h3, ← Matrix.mulVec_mulVec] at h2
    exact h2
  have h3 := hg _ h1
  have : v = Am *ᵥ (Ai *ᵥ v) := by rw [Matrix.mulVec_mulVec, hAA, Matrix.one_mulVec]
  rw [this, h3]
  simp

theorem exists_conj_fieldSp_of_fix {α : MulAut Sp8} (h : α spZ1 = spZ1) :
    ∃ (g : Sp8) (σ : GF8 ≃+* GF8), α = MulAut.conj g * fieldSp 2 GF8 σ := by
  set ρ : MulAut Sp8 ≃* MulAut (StatedProj (StatedSp 2 GF8)) := MulAut.congr piP with hρ
  obtain ⟨A, σ, ε, hε, hαρ⟩ :=
    CFSG.RankThree.PartTwo.KFacts.exists_eq_conjAut_mul_fieldAut_mul_tauAut_pow (ρ α)
  interval_cases ε
  · simp only [pow_zero, mul_one] at hαρ
    obtain ⟨l, hl⟩ := conjAut_mem_inner_of_charTwo A
    have hconj : conjAut 2 GF8 A = MulAut.conj l := hl.symm
    refine ⟨piP.symm l, σ, ?_⟩
    apply ρ.injective
    rw [hαρ, map_mul, hconj, hρ, CFSG.ComponentClassification.OuterAutomorphisms.congr_conj,
      congr_piP_fieldSp, MulEquiv.apply_symm_apply]
  · exfalso
    simp only [pow_one] at hαρ
    have key : α spZ1 = conjSp 2 GF8 A (fieldSp 2 GF8 σ (tauG spZ1)) := by
      apply piP.injective
      have h1 : piP (α spZ1) = (ρ α) (piP spZ1) := by
        show piP (α spZ1) = piP (α (piP.symm (piP spZ1)))
        rw [MulEquiv.symm_apply_apply]
      rw [h1, hαρ]
      show ((conjAut 2 GF8 A * fieldAut 2 GF8 σ * tauAut :
        MulAut (StatedProj (StatedSp 2 GF8))) (proj 2 GF8 spZ1)) = proj 2 GF8 _
      simp only [MulAut.mul_apply]
      rw [show (tauAut : MulAut (StatedProj (StatedSp 2 GF8))) (proj 2 GF8 spZ1) =
          proj 2 GF8 (tauG spZ1) from tauAut_proj spZ1, fieldAut_proj, conjAut_proj]
    rw [h] at key
    exact not_SpFPF_spZ1 (key ▸ spFPF_conjSp A (spFPF_fieldSp σ fpf_tau_spZ1))

theorem blk0_slZ_mem_spE : blk0 slZ ∈ spE :=
  (mem_spE_iff _).2 ⟨slZ, Subgroup.mem_zpowers _, 1, Subgroup.one_mem _, by simp⟩

theorem blk1_slZ_mem_spE : blk1 slZ ∈ spE :=
  (mem_spE_iff _).2 ⟨1, Subgroup.one_mem _, slZ, Subgroup.mem_zpowers _, by simp⟩

theorem centralizer_spE_le {h : Sp8} (hc : ∀ z ∈ spE, h * z = z * h) : h ∈ spT0 := by
  obtain ⟨x, y, hx, hh⟩ := block_of_comm (hc _ blk0_slZ_mem_spE)
  have hb1 : h * blk1 slZ = blk1 slZ * h := hc _ blk1_slZ_mem_spE
  have h2 : (swp * h * swp⁻¹) * blk0 slZ = blk0 slZ * (swp * h * swp⁻¹) := by
    rw [← swp_conj_blk1 slZ]
    calc swp * h * swp⁻¹ * (swp * blk1 slZ * swp⁻¹) = swp * (h * blk1 slZ) * swp⁻¹ := by group
      _ = swp * (blk1 slZ * h) * swp⁻¹ := by rw [hb1]
      _ = swp * blk1 slZ * swp⁻¹ * (swp * h * swp⁻¹) := by group
  obtain ⟨x', y', hx', hh'⟩ := block_of_comm h2
  rw [hh, conj_swp_blk] at hh'
  obtain ⟨hyx, -⟩ := blk_inj hh'
  exact (mem_spT0_iff _).2 ⟨x, hx, y, hyx ▸ hx', hh⟩

theorem spZ1_mem_spE : spZ1 ∈ spE := blk0_slZ_mem_spE

section YLevel

variable {Y : Type} [Group Y] {K : Subgroup Y} [K.Normal] {e : K ≃* Sp8} {T : Subgroup Y}
  {y : Y}

theorem emb_adHom (g : Y) (k : Sp8) : emb e (adHom K e g k) = g * emb e k * g⁻¹ :=
  coe_symm_adHom K e g k

theorem adHom_emb (h : Sp8) : adHom K e (emb e h) = MulAut.conj h := by
  have := adHom_coe (eK := e) (e.symm h)
  simpa [emb_apply] using this

theorem Sp48Setup.adHom_y (S : Sp48Setup e T y) : adHom K e y = fr := by
  refine MulEquiv.ext fun k => ?_
  apply emb_injective e
  rw [emb_adHom, S.act]

theorem Sp48Setup.eq_emb_mul_y_pow (S : Sp48Setup e T y)
    (hC : Subgroup.centralizer (K : Set Y) = ⊥) {g : Y} {h : Sp8} {σ : GF8 ≃+* GF8}
    (hα : adHom K e g = MulAut.conj h * fieldSp 2 GF8 σ) : ∃ j : ℕ, g = emb e h * y ^ j := by
  rcases ringAut_gf8 σ with rfl | rfl | rfl
  · refine ⟨0, adHom_injective (eK := e) hC ?_⟩
    rw [hα, map_one, mul_one, pow_zero, mul_one, adHom_emb]
  · refine ⟨1, adHom_injective (eK := e) hC ?_⟩
    rw [hα, map_mul, adHom_emb, pow_one, S.adHom_y]
    rfl
  · refine ⟨2, adHom_injective (eK := e) hC ?_⟩
    rw [hα, map_mul, adHom_emb]
    simp only [map_pow, S.adHom_y]
    rfl

theorem Sp48Setup.cent_E_le (S : Sp48Setup e T y) (hC : Subgroup.centralizer (K : Set Y) = ⊥)
    {g : Y} (hg : ∀ z ∈ spE.map (emb e), g * z = z * g) : g ∈ T := by
  have hfix : adHom K e g spZ1 = spZ1 := by
    apply emb_injective e
    rw [emb_adHom]
    have := hg (emb e spZ1) ⟨spZ1, spZ1_mem_spE, rfl⟩
    rw [this]
    group
  obtain ⟨h, σ, hα⟩ := exists_conj_fieldSp_of_fix hfix
  obtain ⟨j, hj⟩ := S.eq_emb_mul_y_pow hC hα
  have hyE : ∀ z ∈ spE, Commute (y ^ j) (emb e z) := by
    intro z hz
    have := S.y_pow_act j z
    rw [fr_pow_spE hz] at this
    show y ^ j * emb e z = emb e z * y ^ j
    calc y ^ j * emb e z = (y ^ j * emb e z * (y ^ j)⁻¹) * y ^ j := by group
      _ = emb e z * y ^ j := by rw [this]
  have hh : h ∈ spT0 := by
    apply centralizer_spE_le
    intro z hz
    apply emb_injective e
    rw [map_mul, map_mul]
    have h1 : Commute g (emb e z) := hg (emb e z) ⟨z, hz, rfl⟩
    have h2 : emb e h = g * (y ^ j)⁻¹ := by rw [hj]; group
    rw [h2]
    exact Commute.mul_left h1 (hyE z hz).inv_left
  exact (S.mem_iff g).2 ⟨h, hh, j, hj⟩

end YLevel

end CFSG.AGLEmbedding.KFactProofs.Sp48
