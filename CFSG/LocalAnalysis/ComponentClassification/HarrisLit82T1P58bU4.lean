module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58bCov
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBClPSU
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBCoverU
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBSU4Lift
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEndOddLieL2
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEndOddLieL4

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup Assembly.LowTwoRank Blueprint CFSG.LocalAnalysis.ComponentInitial Matrix
open CFSG.ClassicalGroups.UnitaryFlag CFSG.ComponentClassification.Burgoyne.U
  CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.PSL (signMat)
open scoped MatrixGroups

namespace P58b

variable {p f : ℕ} {K : Type} [Field K] (hu : UnitaryFieldData p f K)

theorem noL2At_uConjAut_split [Finite K] (hp2 : p ≠ 2) {n : ℕ} (hn : 3 ≤ n) {A : uU hu n}
    (hAA : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1)
    (hns : ∀ c : Kˣ, (A : GL (Fin n) K) ≠ GeneralLinearGroup.scalar (Fin n) c) :
    Burgoyne.Cl.NoL2At (uConjAut hu (by omega) A) := by
  have h2 := CatLeafProof.EndOddLin.two_ne_zero_of_unitary hu hp2
  have hn1 : 1 ≤ n := by omega
  set Am := ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hAm
  have hU : (Am.map hu.bar)ᵀ * Am = 1 := (mem_uU hu).1 A.2
  obtain ⟨Hm, J, hHU, hHA⟩ := exists_split_unitary_normal_form hu h2 hU hAA
  have hconj : (Hm.map hu.bar)ᵀ * Am * Hm = signMat K J := by
    rw [Matrix.mul_assoc, hHA, ← Matrix.mul_assoc, hHU, Matrix.one_mul]
  have hHH : Hm * (Hm.map hu.bar)ᵀ = 1 := mul_eq_one_comm.1 hHU
  have hJ : ∃ a ∈ J, ∃ b, b ∉ J := by
    by_contra hcon
    push Not at hcon
    obtain ⟨s, hs, hsJ⟩ : ∃ s : K, s ≠ 0 ∧ signMat K J = s • 1 := by
      by_cases hne : J.Nonempty
      · obtain ⟨a, ha⟩ := hne
        refine ⟨-1, neg_ne_zero.2 one_ne_zero, ?_⟩
        ext i j
        simp [signMat, diagonal_apply, one_apply, hcon a ha i]
      · rw [Finset.not_nonempty_iff_eq_empty] at hne
        refine ⟨1, one_ne_zero, ?_⟩
        ext i j
        simp [signMat, diagonal_apply, one_apply, hne]
    have e : Am = s • 1 := by
      calc Am = Hm * ((Hm.map hu.bar)ᵀ * Am * Hm) * (Hm.map hu.bar)ᵀ := by
            simp only [← Matrix.mul_assoc, hHH, Matrix.one_mul]
            rw [Matrix.mul_assoc, hHH, Matrix.mul_one]
        _ = s • 1 := by
            rw [hconj, hsJ, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hHH]
    apply hns (Units.mk0 s hs)
    apply Units.ext
    rw [GeneralLinearGroup.coe_scalar]
    change Am = _
    rw [e, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
    rfl
  obtain ⟨a, ha, b, hb⟩ := hJ
  set H : uU hu n := ⟨uGL hu Hm hHU, uGL_mem hu _ _⟩ with hH
  refine Burgoyne.Cl.NoL2At.of_conj (uConjAut hu hn1 H)⁻¹ ?_
  have e : (uConjAut hu hn1 H)⁻¹ * uConjAut hu hn1 A * (uConjAut hu hn1 H)⁻¹⁻¹ =
      uConjAut hu hn1 (uSign hu J) := by
    rw [inv_inv, ← map_inv, ← map_mul, ← map_mul]
    refine uConjAut_eq_of_eq_smul hu hn one_ne_zero ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Units.val_mul,
      one_smul, coe_uSign]
    exact hconj
  rw [e]
  exact Burgoyne.Cl.noL2At_uSign hu hp2 hn1 ha hb

end P58b

open P58b

theorem noConfig_PSU_four : Harris82Lemma58bNoConfig .PSU 4 := by
  intro X _ _ hX hO p f hp hp2 hm k c t Q hcfg
  have hII := propBHypII_of_config hp hp2 hcfg
  have hc2 : orderOf c = 2 := hcfg.1
  have htZ : t ∉ center X := hcfg.2.2.2.1
  have ht2 : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rwa [hcfg.2.2.1, pow_two] at h
  have hc1 : c ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hc2
    exact absurd hc2 (by norm_num)
  rcases hm with ⟨-, hcl⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩
  rotate_left
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)
  obtain ⟨⟨hp', hf, -, -⟩, K₀, _, _, hKc, ⟨θ⟩⟩ := hcl
  have hu : UnitaryFieldData p f K₀ := ⟨hp', hf, by rw [hKc, ← pow_mul, mul_comm]⟩
  have : Fact p.Prime := ⟨hp'⟩
  have := hu.charP
  have hneg : (-1 : GL (Fin 4) K₀) ∈ StatedSU 4 (p ^ f) K₀ := by
    rw [mem_unitarySU_iff hu]
    refine ⟨?_, ?_⟩
    · rw [Units.val_neg, Units.val_one, det_neg, det_one, Fintype.card_fin]
      norm_num
    · simp [Matrix.map_neg, Matrix.map_one]
  set g₀ : StatedSU 4 (p ^ f) K₀ := ⟨-1, hneg⟩ with hg₀
  have hg₀m : ((g₀ : GL (Fin 4) K₀) : Matrix (Fin 4) (Fin 4) K₀) = -1 := by
    show ((-1 : GL (Fin 4) K₀) : Matrix (Fin 4) (Fin 4) K₀) = -1
    rw [Units.val_neg, Units.val_one]
  set β : StatedSU 4 (p ^ f) K₀ →* X ⧸ center X :=
    θ.symm.toMonoidHom.comp (projH (StatedSU 4 (p ^ f) K₀)) with hβ
  refine false_of_cover hX hO hp hp2 hcfg (G := StatedSU 4 (p ^ f) K₀)
    (Burgoyne.B.statedSU_central_two_splitting hu.card_eq_sq hp2 (by norm_num)) β
    (θ.symm.surjective.comp projH_surjective) ?_
  intro α hαs hαβ hker g hg
  have hc : c = α g₀ := Burgoyne.B.burgoynePropBSU4CoverInput p f K₀ hu hp2 X α hαs c hII g₀ hg₀m
  have hβ1 : ∀ z, β z = 1 → ∃ ζ : K₀ˣ,
      ((z : GL (Fin 4) K₀) : Matrix (Fin 4) (Fin 4) K₀) = scalar (Fin 4) (ζ : K₀) := by
    intro z hz
    rw [hβ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff] at hz
    obtain ⟨ζ, hζ⟩ := mem_subgroupOf.mp ((QuotientGroup.eq_one_iff z).mp hz)
    refine ⟨ζ, ?_⟩
    rw [← hζ, GeneralLinearGroup.coe_scalar]
  have hext : ∀ {x y : StatedSU 4 (p ^ f) K₀},
      ((x : GL (Fin 4) K₀) : Matrix (Fin 4) (Fin 4) K₀) =
        ((y : GL (Fin 4) K₀) : Matrix (Fin 4) (Fin 4) K₀) → x = y :=
    fun h => Subtype.ext (Units.ext h)
  have hinj : ∀ z, α z = 1 → z = 1 := by
    intro z hz
    obtain ⟨ζ, hzζ⟩ := hβ1 z (by rw [← hαβ, hz, map_one])
    have hdet := CFSG.LieType.Universal.Unitary.det_eq_one_of_mem_statedSU z.2
    rw [hzζ, scalar_apply, det_diagonal, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin] at hdet
    have h4 : ((ζ : K₀) * ζ) * ((ζ : K₀) * ζ) = 1 := by linear_combination hdet
    rcases mul_self_eq_one_iff.mp h4 with h2 | h2
    · rcases mul_self_eq_one_iff.mp h2 with h1 | h1
      · apply hext
        rw [hzζ, h1, map_one, Subgroup.coe_one, Units.val_one]
      · exfalso
        have hz₀ : z = g₀ := by
          apply hext
          rw [hzζ, h1, map_neg, map_one, hg₀m]
        exact hc1 (by rw [hc, ← hz₀]; exact hz)
    · exfalso
      have hzz : z * z = g₀ := by
        apply hext
        rw [Subgroup.coe_mul, Units.val_mul, hzζ, ← map_mul, h2, map_neg, map_one, hg₀m]
      have h1 : α g₀ = 1 := by rw [← hzz, map_mul, hz, one_mul]
      exact hc1 (hc.trans h1)
  have hgg : g * g = 1 := hinj _ (by rw [map_mul, hg, ht2])
  have hns : ∀ c' : K₀ˣ,
      ((⟨(g : GL (Fin 4) K₀), statedSU_le_uU hu g.2⟩ : uU hu 4) : GL (Fin 4) K₀) ≠
        GeneralLinearGroup.scalar (Fin 4) c' := by
    intro c' hc'
    apply htZ
    rw [hker]
    refine ⟨g, MonoidHom.mem_ker.mpr ?_, hg⟩
    rw [hβ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]
    exact (QuotientGroup.eq_one_iff g).mpr (mem_subgroupOf.mpr ⟨c', hc'.symm⟩)
  have hAA : ((g : GL (Fin 4) K₀) : Matrix (Fin 4) (Fin 4) K₀) *
      ((g : GL (Fin 4) K₀) : Matrix (Fin 4) (Fin 4) K₀) = 1 := by
    have h := congrArg
      (fun x : StatedSU 4 (p ^ f) K₀ => ((x : GL (Fin 4) K₀) : Matrix (Fin 4) (Fin 4) K₀)) hgg
    simpa only [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_one, Units.val_one] using h
  have hNo := noL2At_uConjAut_split hu hp2 (by norm_num : 3 ≤ 4)
    (A := ⟨(g : GL (Fin 4) K₀), statedSU_le_uU hu g.2⟩) hAA hns
  rw [uConjAut_of_mem_SU hu] at hNo
  refine Burgoyne.Cl.NoL2At.of_congr θ ?_
  have e : MulAut.congr θ (MulAut.conj (β g)) =
      MulAut.conj (projH (StatedSU 4 (p ^ f) K₀) g) :=
    mulAut_congr_conj θ (projH (StatedSU 4 (p ^ f) K₀) g)
  rw [e]
  exact hNo

end CFSG.ComponentClassification.HarrisLit.T1
