module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
import CFSG.HardMathSupport.Timmesfeld.LinearRank.ProjRank
import CFSG.RankThree.PartTwo.Sec13.KF135Chev2Core
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOutCycLinear
import CFSG.HardMathSupport.Solomon.Coordinator.InndiagPSLn
import CFSG.LocalAnalysis.GLTheoremA.CatA.T123CTrans
import CFSG.Permutation.UnitaryThreeRecognition.ModelFinite

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267Z.Lin

open Matrix CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {K : Type} [Field K] [Finite K]

private theorem conjAut_eq_one_iff (A : GL (Fin 3) K) :
    conjAut 3 K A = 1 ↔ A ∈ Subgroup.center (GL (Fin 3) K) := by
  rw [CFSG.HardMathSupport.Timmesfeld.LinearRank.mem_center_iff]
  constructor
  · intro h
    obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (le_refl 3) A 1
      (by rw [map_one, mul_one, h])
    exact ⟨c, hc.symm⟩
  · rintro ⟨c, rfl⟩
    exact conjAut_scalar c

private theorem card_center_GL : Nat.card (Subgroup.center (GL (Fin 3) K)) = Nat.card K - 1 := by
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar, ← Nat.card_units]
  have hinj : Function.Injective (Matrix.GeneralLinearGroup.scalar (Fin 3) : Kˣ →* GL (Fin 3) K) := by
    intro u v h
    have h1 := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 0 0) h
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq]
      at h1
    exact Units.ext h1
  exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm

theorem card_le_of_le_linearAutGroup_of_not_dvd {p : ℕ} (hp : p.Prime) (hpK : (p : K) ≠ 0)
    (hq : ¬ p ∣ Nat.card K - 1) {E : Subgroup (MulAut (projectiveSL 3 K))}
    (hED : E ≤ linearAutGroup 3 K) (hE : IsElemAbelian p E) : Nat.card E ≤ p := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let ψ : Matrix.ProjGenLinGroup (Fin 3) K →* MulAut (projectiveSL 3 K) :=
    QuotientGroup.lift (Subgroup.center (GL (Fin 3) K)) (conjAut 3 K)
      (fun A hA => (conjAut_eq_one_iff A).2 hA)
  have hψ : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨A, rfl⟩ := QuotientGroup.mk_surjective x
    have h1 : conjAut 3 K A = 1 := hx
    exact (QuotientGroup.eq_one_iff A).2 ((conjAut_eq_one_iff A).1 h1)
  have hEψ : E ≤ ψ.range := by
    intro α hα
    obtain ⟨A, hA⟩ := mem_linearAutGroup_iff.1 (hED hα)
    exact ⟨QuotientGroup.mk A, hA⟩
  set P := CFSG.PGLModel.projImage (⊤ : Subgroup (GL (Fin 3) K)) with hP
  have hPtop : P = ⊤ := Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)
  have hN : ¬ p ∣ Nat.card ((Subgroup.center (GL (Fin 3) K)).subgroupOf ⊤) := by
    rw [← Subgroup.card_map_of_injective (f := (⊤ : Subgroup (GL (Fin 3) K)).subtype)
      (⊤ : Subgroup (GL (Fin 3) K)).subtype_injective, Subgroup.subgroupOf_map_subtype, inf_top_eq,
      card_center_GL]
    exact hq
  have h1 : ((Nat.card K : ℕ) : ZMod p) ≠ 1 := by
    intro h
    apply hq
    have hK1 : 1 ≤ Nat.card K := Nat.card_pos
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hK1, h, Nat.cast_one, sub_self]
  have hn : Fintype.card (Fin 3) < 2 * CFSG.StandardType.OrdPNS.ordQ K p := by
    have := CFSG.RankThree.PartTwo.Sec13.KF135Chev2.two_le_ordQ hp hpK h1
    simp only [Fintype.card_fin]
    omega
  have hR := CFSG.RankThree.PartTwo.Sec13.KF135Chev2.rankLE1_projImage_of_lt hp hpK ⊤ hN hn
  let F : Subgroup ↥P := (E.comap ψ).subgroupOf P
  have hmap : (E.comap ψ).map ψ = E := Subgroup.map_comap_eq_self hEψ
  have hcomapEl : IsElemAbelian p (E.comap ψ) := by
    rw [← CFSG.LocalAnalysis.GLTheoremA.T123C.isElemAbelian_map_iff hψ, hmap]
    exact hE
  have hF : IsElemAbelian p F := hcomapEl.subgroupOf P
  have hcardF : Nat.card F = Nat.card E := by
    have h2 : Nat.card F = Nat.card (E.comap ψ) := by
      rw [← Subgroup.card_map_of_injective (f := P.subtype) P.subtype_injective,
        Subgroup.subgroupOf_map_subtype, hPtop, inf_top_eq]
    rw [h2]
    calc Nat.card (E.comap ψ) = Nat.card ((E.comap ψ).map ψ) :=
          (Subgroup.card_map_of_injective hψ).symm
      _ = Nat.card E := by rw [hmap]
  rw [← hcardF]
  exact hR F hF

theorem card_le_sq_of_le_linearAutGroup {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpK : (p : K) ≠ 0)
    {E : Subgroup (MulAut (projectiveSL 3 K))} (hED : E ≤ linearAutGroup 3 K)
    (hE : IsElemAbelian p E) : Nat.card E ≤ p ^ 2 := by
  by_cases hq : p ∣ Nat.card K - 1
  · let ρ : ↥(⊤ : Subgroup (GL (Fin 3) K)) →* MulAut (projectiveSL 3 K) :=
      (conjAut 3 K).comp (⊤ : Subgroup (GL (Fin 3) K)).subtype
    have hker : ∀ A : ↥(⊤ : Subgroup (GL (Fin 3) K)),
        ρ A = 1 ↔ (A : GL (Fin 3) K) ∈ Subgroup.center (GL (Fin 3) K) :=
      fun A => conjAut_eq_one_iff (A : GL (Fin 3) K)
    have hEρ : E ≤ ρ.range := by
      intro α hα
      obtain ⟨A, hA⟩ := mem_linearAutGroup_iff.1 (hED hα)
      exact ⟨⟨A, Subgroup.mem_top A⟩, hA⟩
    have h := CFSG.HardMathSupport.Timmesfeld.LinearRank.card_le_of_scalar_kernel hp hp2
      (by rw [Nat.card_units]; exact hq) (by norm_num : 0 < 3) ⊤ ρ hker E hEρ hE
    simpa using h
  · exact (card_le_of_le_linearAutGroup_of_not_dvd hp hpK hq hED hE).trans
      (Nat.le_self_pow (by norm_num) p)

theorem card_le_mul_card_inf_linearAutGroup {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {E : Subgroup (MulAut (projectiveSL 3 K))} (hE : IsElemAbelian p E) :
    Nat.card E ≤ p * Nat.card ↥(E ⊓ linearAutGroup 3 K) := by
  have : Finite (MulAut (projectiveSL 3 K)) := MulEquiv.finite_left
  have h1 := CFSG.LocalAnalysis.GLTheoremA.KD264Lie.outCycAt_projectiveSL (K := K) (le_refl 3) hp
    hp2 E hE
  have h2 : Nat.card ↥(E ⊓ CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived
      (projectiveSL 3 K)) ≤ Nat.card ↥(E ⊓ linearAutGroup 3 K) :=
    Subgroup.card_le_of_le (inf_le_inf_left _
      (CFSG.HardMathSupport.Solomon.Coordinator.innAutDerived_le_linearAutGroup (le_refl 3)))
  exact h1.trans (Nat.mul_le_mul_left p h2)

theorem card_le_cube {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpK : (p : K) ≠ 0)
    {E : Subgroup (MulAut (projectiveSL 3 K))} (hE : IsElemAbelian p E) : Nat.card E ≤ p ^ 3 := by
  have h1 := card_le_mul_card_inf_linearAutGroup hp hp2 hE
  have h2 := card_le_sq_of_le_linearAutGroup hp hp2 hpK (inf_le_right : E ⊓ linearAutGroup 3 K ≤ _)
    (hE.mono inf_le_left)
  calc Nat.card E ≤ p * Nat.card ↥(E ⊓ linearAutGroup 3 K) := h1
    _ ≤ p * p ^ 2 := Nat.mul_le_mul_left p h2
    _ = p ^ 3 := by ring

theorem cube_facts {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpK : (p : K) ≠ 0)
    {E : Subgroup (MulAut (projectiveSL 3 K))} (hE : IsElemAbelian p E) (hc : Nat.card E = p ^ 3) :
    Nat.card ↥(E ⊓ linearAutGroup 3 K) = p ^ 2 ∧ p ∣ Nat.card K - 1 ∧
      ∃ α ∈ E, α ∉ linearAutGroup 3 K := by
  have h1 := card_le_mul_card_inf_linearAutGroup hp hp2 hE
  have hEl : IsElemAbelian p (E ⊓ linearAutGroup 3 K) := hE.mono inf_le_left
  have h2 := card_le_sq_of_le_linearAutGroup hp hp2 hpK inf_le_right hEl
  have hp1 := hp.one_lt
  have hge : p ^ 2 ≤ Nat.card ↥(E ⊓ linearAutGroup 3 K) := by
    rw [hc, show p ^ 3 = p * p ^ 2 by ring] at h1
    exact Nat.le_of_mul_le_mul_left h1 hp.pos
  have heq : Nat.card ↥(E ⊓ linearAutGroup 3 K) = p ^ 2 := le_antisymm h2 hge
  refine ⟨heq, ?_, ?_⟩
  · by_contra hq
    have h3 := card_le_of_le_linearAutGroup_of_not_dvd hp hpK hq inf_le_right hEl
    rw [heq] at h3
    have : p < p ^ 2 := by
      calc p = p ^ 1 := (pow_one p).symm
        _ < p ^ 2 := Nat.pow_lt_pow_right hp1 (by norm_num)
    omega
  · by_contra hall
    push Not at hall
    have hle : E ≤ E ⊓ linearAutGroup 3 K := fun α hα => ⟨hα, hall α hα⟩
    have h4 := Subgroup.card_le_of_le hle
    rw [hc, heq] at h4
    have : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hp1 (by norm_num)
    omega

end CFSG.LocalAnalysis.GLTheoremA.S267Z.Lin

end
