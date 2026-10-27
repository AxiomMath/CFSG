module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172AExistBase
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172XInner
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineL2Line
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172ALayerGL
import CFSG.Goldschmidt.Steps.G3b35Basic
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ADefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.T173

private theorem card_ker_eq_three_of {Ω : Type} [Group Ω] [Finite Ω] {B : Subgroup Ω} {x : Ω}
    {G : Type} [Group G] (φ : ↥B →* G)
    (hker : ∀ b : ↥B, φ b = 1 ↔ (b : Ω) ∈ Subgroup.zpowers x)
    (hBel : IsElemAbelian 3 B) (hxB : x ∈ B) (hx1 : x ≠ 1) : Nat.card φ.ker = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hordx : orderOf x = 3 := orderOf_eq_prime (hBel.2 x hxB) hx1
  have : φ.ker = (Subgroup.zpowers x).subgroupOf B := by
    ext b
    rw [MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
  rw [this, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.2 hxB)).toEquiv,
    Nat.card_zpowers, hordx]

theorem lin_two_B_le_sup {p : ℕ} {Ω : Type} [Group Ω] {S B : Subgroup Ω} (hSn : S.Normal)
    (hSq : CFSG.Open.IsQuasisimple ↥S) {d : ℕ} {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2)
    {θ : ↥S ⧸ Subgroup.center ↥S ≃* LargeEvenProj (LargeEvenSLGroup (Fin d) F)}
    (hM : LinMarking p S B 1 d F θ) :
    ∀ b ∈ B, b ∈ S ⊔ Subgroup.centralizer (S : Set Ω) := by
  haveI := hSn
  intro b hb
  obtain ⟨-, -, -, -, -, -, hconj⟩ := hM
  obtain ⟨φ, hφmem, hφind⟩ := hconj b hb
  obtain ⟨x₀, hx₀⟩ :=
    CFSG.StandardType.LineL2.matConjImage_subset_conj (d := d) hF hφmem
  obtain ⟨l, hl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥S) (θ.symm x₀)
  have hl' : θ (QuotientGroup.mk l) = x₀ := by
    have h := congrArg θ hl
    simpa using h
  have hconjq : CFSG.Goldschmidt.G3b.conjQuot S b⁻¹ =
      MulAut.conj (l : ↥S ⧸ Subgroup.center ↥S) := by
    ext y
    induction y using QuotientGroup.induction_on with
    | H y =>
      rw [CFSG.Goldschmidt.G3b.conjQuot_mk, MulAut.conj_apply]
      simp only [inv_inv]
      apply θ.injective
      rw [map_mul, map_mul, map_inv, hl']
      have hmem : b⁻¹ * (y : Ω) * b ∈ S := by
        simpa using hSn.conj_mem y y.2 b⁻¹
      have h := hφind y ⟨b⁻¹ * (y : Ω) * b, hmem⟩ rfl
      rw [← hx₀, MulAut.conj_apply] at h
      exact h.symm
  have hmem := CFSG.Goldschmidt.G3b.mem_sup_centralizer_of_conjQuot_eq_conj S hSq.1 l hconjq
  simpa using (Subgroup.inv_mem (S ⊔ Subgroup.centralizer (S : Set Ω)) hmem)

theorem lin_two_equiv_vecAut {d : ℕ} {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2) :
    Nonempty (LargeEvenProj (LargeEvenSLGroup (Fin d) F) ≃*
      CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Transfer.VecAut d) := by
  obtain ⟨σ⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Transfer.exists_ringEquiv_zmod2 F hF
  exact ⟨(CFSG.StandardType.LineL2.recipeEquivTwo hF).trans
    ((CFSG.StandardType.LineL2.projEquivTwo hF).trans
      (CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Transfer.projEquiv d σ))⟩

theorem lin_two_center_bot
    {Ω : Type} [Group Ω] [Finite Ω] {S : Subgroup Ω}
    (hSq : CFSG.Open.IsQuasisimple ↥S) {d : ℕ} {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2) (hd : 5 ≤ d)
    (θ : ↥S ⧸ Subgroup.center ↥S ≃* LargeEvenProj (LargeEvenSLGroup (Fin d) F)) :
    Subgroup.center ↥S = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKcard : Nat.card (GaloisField 2 1) = 2 := by
    rw [GaloisField.card 2 1 (by norm_num)]
    norm_num
  obtain ⟨σ'⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Transfer.exists_ringEquiv_zmod2
      (GaloisField 2 1) hKcard
  obtain ⟨e₂⟩ := lin_two_equiv_vecAut (d := d) (F := F) hF
  let e : ↥S ⧸ Subgroup.center ↥S ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin d) (GaloisField 2 1) :=
    θ.trans (e₂.trans
      ((CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Transfer.projEquiv d σ').symm.trans
        (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
          d (GaloisField 2 1)).symm))
  exact S172A.center_eq_bot_of_psl_two hSq (n := d) (p := 2) (f := 1) hd (by norm_num)
    (by norm_num) e

theorem lin_two_six_le {Ω : Type} [Group Ω] [Finite Ω] {S B N D K : Subgroup Ω} {x : Ω}
    (hcfg : Cfg173 3 S B N D K x) {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (M : S172X.S172Model S B (V ≃ₗ[ZMod 2] V)) :
    6 ≤ Module.finrank (ZMod 2) V := by
  have hker : Nat.card M.β.ker = 3 :=
    card_ker_eq_three_of M.β (fun b => M.β_eq_one_iff_mem_zpowers hcfg.cent b)
      hcfg.elem hcfg.mem hcfg.ne_one
  have hmul := Subgroup.card_ker_mul_card_range M.β
  rw [hker] at hmul
  have hB : 3 ^ 3 ≤ Nat.card M.β.range := by
    have h4 : 81 ≤ Nat.card ↥B := by
      have := hcfg.four
      norm_num at this
      exact this
    have : 27 ≤ Nat.card M.β.range := by omega
    simpa using this
  have hE : IsElemAbelian 3 M.β.range :=
    S172A.GL.isElemAbelian_range_hom M.β hcfg.elem
  have hle : Nat.card M.β.range ≤ 3 ^ (Module.finrank (ZMod 2) V / 2) :=
    S172A.GL.card_le_three_pow M.β.range hE
  have hpow : 3 ^ 3 ≤ 3 ^ (Module.finrank (ZMod 2) V / 2) := le_trans hB hle
  have h3 : 3 ≤ Module.finrank (ZMod 2) V / 2 :=
    (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).1 hpow
  have h32 : 3 * 2 ≤ Module.finrank (ZMod 2) V :=
    (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).1 h3
  omega

end CFSG.LocalAnalysis.GLTheoremA.T173A

end
