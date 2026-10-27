module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OmegaProj
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5LACent
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFAutSurj
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFClassModelAux1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFSimAct

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private theorem sec5la_ffSimOmegaAct_h2_irrel (hQ : Q.Nondegenerate)
    {h2a h2b : 2 ≤ Module.finrank (ZMod 3) V} :
    ffSimOmegaAct hQ h2a = ffSimOmegaAct hQ h2b := by
  apply MonoidHom.ext
  intro x
  apply MulEquiv.ext
  intro w
  exact Subtype.ext rfl

private theorem sec5la_ffSimOmegaAct_injective' (hQ : Q.Nondegenerate)
    (h5 : 5 ≤ Module.finrank (ZMod 3) V) (h2 : 2 ≤ Module.finrank (ZMod 3) V) :
    Function.Injective (ffSimOmegaAct hQ h2) := by
  have h := ffSimOmegaAct_injective hQ h5
  rwa [← sec5la_ffSimOmegaAct_h2_irrel (hQ := hQ) (h2a := h2)] at h

private theorem sec5la_ffSimOmegaAct_surjective' (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hs : quadSign Q = -1)
    (h2 : 2 ≤ Module.finrank (ZMod 3) V) :
    Function.Surjective (ffSimOmegaAct hQ h2) := by
  have h := (ffSimOmegaAct_bijective_six_minus hQ hdim hs).2
  rwa [← sec5la_ffSimOmegaAct_h2_irrel (hQ := hQ) (h2a := h2)] at h

theorem sec5la_mulAut_omegaProj_eq_one (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hs : quadSign Q = -1)
    {u : omegaGroup hQ} (huu : (u : OGroup Q) * u = 1) (hty : invType (u : OGroup Q) = (4, 1))
    {n : ℕ} (hn : Nat.Coprime n 6) {α : MulAut (omegaProj hQ)} (hαn : α ^ n = 1)
    (hfix : α (omegaToProj hQ u) = omegaToProj hQ u) : α = 1 := by
  have H2 : 2 ≤ Module.finrank (ZMod 3) V := by omega
  obtain ⟨x, hx⟩ := sec5la_ffSimOmegaAct_surjective' hQ hdim hs H2 α
  obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective x
  have hpow : QuotientGroup.mk γ ^ n = 1 :=
    sec5la_ffSimOmegaAct_injective' hQ (by omega) H2 (by rw [map_pow, hx, hαn, map_one])
  have hmem : γ ^ n ∈ piSim Q :=
    (QuotientGroup.eq_one_iff (N := piSim Q) (γ ^ n)).mp (by
      rw [QuotientGroup.mk_pow]
      exact hpow)
  have hp2 : (γ ^ n) * (γ ^ n) = 1 := by
    rcases mem_piSim_iff.mp hmem with h1 | h1
    · rw [h1, one_mul]
    · rw [h1, ← map_mul, piOrth_mul_self, map_one]
  have hg2n : γ ^ (2 * n) = 1 := by
    rw [mul_comm 2 n, pow_mul, pow_two]
    exact hp2
  have hgg : (γ * γ) ^ n = 1 := by
    rw [show γ * γ = γ ^ 2 from (pow_two γ).symm, ← pow_mul]
    exact hg2n
  have hproj : toProj Q (simAct Q γ (u : OGroup Q)) = toProj Q (u : OGroup Q) := by
    have hmain : (ffSimOmegaAct hQ H2 (QuotientGroup.mk γ)) (omegaToProj hQ u) =
        omegaToProj hQ u := by
      rw [hx]
      exact hfix
    have h := congrArg (fun z : omegaProj hQ => (z : ProjOrth Q)) hmain
    simpa only [coe_ffSimOmegaAct, coe_omegaToProj, projSimAct_mk, projActAux_toProj] using h
  have hproj_or : simAct Q γ (u : OGroup Q) = (u : OGroup Q) ∨
      simAct Q γ (u : OGroup Q) = piOrth Q * (u : OGroup Q) :=
    toProj_eq_or_eq_piOrth hproj
  have hfix2 : simAct Q (γ * γ) (u : OGroup Q) = (u : OGroup Q) := by
    rcases hproj_or with h1 | h1
    · calc simAct Q (γ * γ) (u : OGroup Q)
          = simAct Q γ (simAct Q γ (u : OGroup Q)) := by rw [map_mul, MulAut.mul_apply]
        _ = simAct Q γ (u : OGroup Q) := congrArg (simAct Q γ) h1
        _ = (u : OGroup Q) := h1
    · calc simAct Q (γ * γ) (u : OGroup Q)
          = simAct Q γ (simAct Q γ (u : OGroup Q)) := by rw [map_mul, MulAut.mul_apply]
        _ = simAct Q γ (piOrth Q * (u : OGroup Q)) := by rw [h1]
        _ = simAct Q γ (piOrth Q) * simAct Q γ (u : OGroup Q) := by rw [map_mul]
        _ = piOrth Q * simAct Q γ (u : OGroup Q) := by rw [simAct_piOrth]
        _ = piOrth Q * (piOrth Q * (u : OGroup Q)) := by rw [h1]
        _ = (piOrth Q * piOrth Q) * (u : OGroup Q) := by rw [mul_assoc]
        _ = (u : OGroup Q) := by rw [piOrth_mul_self, one_mul]
  obtain ⟨c, hc⟩ := γ.2
  have hcc : c * c = 1 := by
    rcases aux_unit_eq_one_or_neg_one c with h1 | h1 <;> rw [h1] <;> decide
  have hsim : IsSimilitude Q ((γ * γ : simGroup Q) : V ≃ₗ[ZMod 3] V) 1 := by
    rw [Subgroup.coe_mul, ← hcc]
    exact aux_isSimilitude_mul hc hc
  let o : OGroup Q := ⟨((γ * γ : simGroup Q) : V ≃ₗ[ZMod 3] V), isSimilitude_one_iff.mp hsim⟩
  have hortho : orthToSim Q o = γ * γ := Subtype.ext rfl
  have hcomm : o * (u : OGroup Q) * o⁻¹ = (u : OGroup Q) := by
    rw [← simAct_orthToSim o (u : OGroup Q), hortho]
    exact hfix2
  have hcomm' : o * (u : OGroup Q) = (u : OGroup Q) * o := by
    have h := congrArg (fun z : OGroup Q => z * o) hcomm
    simpa [mul_assoc] using h
  have hon : o ^ n = 1 :=
    orthToSim_injective (by rw [map_pow, hortho, map_one]; exact hgg)
  have hbox : o = 1 := sec5la_eq_one_of_commute_pow_eq_one hQ hdim hs huu hty hn hcomm' hon
  have hgg1 : γ * γ = 1 := by
    rw [← hortho, hbox, map_one]
  have hαα : α * α = 1 := by
    have hxx : (QuotientGroup.mk γ : ProjSim Q) * QuotientGroup.mk γ = 1 := by
      rw [← QuotientGroup.mk_mul (N := piSim Q) γ γ, hgg1, QuotientGroup.mk_one]
    rw [← hx, ← map_mul, hxx, map_one]
  have hα2 : α ^ 2 = 1 := by rw [pow_two]; exact hαα
  have hn2 : Nat.Coprime n 2 := hn.coprime_dvd_right (by norm_num : 2 ∣ 6)
  exact (pow_eq_one_iff_of_coprime (a := α) (m := 2) (n := n) hn2.symm).mp ⟨hα2, hαn⟩

end CFSG.OddStandard.SmallF3.Omega
