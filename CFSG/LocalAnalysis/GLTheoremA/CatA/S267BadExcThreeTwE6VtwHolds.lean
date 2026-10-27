module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcThreeTwE6VtwLayer
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcThreeTwE6VtwJ
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcThreeTwE6VtwField
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcThreeTwE6Input

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.TwE6Vtw

open Matrix CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.TwE6Conc
open CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.TwE6Outer


variable {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
  (hK : Nat.card K = (ℓ ^ f) ^ 2) (hf : 1 ≤ f)
  {ζ : K} (hζ : ζ ≠ 0) (hσζ : unitaryInvolution K ℓ f ζ = -ζ)
  (P : GL (Fin 6) K) (hP : conjTr (unitaryInvolution K ℓ f) (P : Matrix (Fin 6) (Fin 6) K) *
    (P : Matrix (Fin 6) (Fin 6) K) = antidiag 6)
  {c : Kˣ} (hc : orderOf c = 3) (h3 : 3 ∣ ℓ ^ f + 1)
  (hct : unitaryInvolution K ℓ f ((c : K) + ((c⁻¹ : Kˣ) : K)) = (c : K) + ((c⁻¹ : Kˣ) : K))

theorem vtwPhi_cons_diagGen4 :
    twistedE6InndiagConj K (unitaryInvolution K ℓ f) (vtwPhi hK hf hζ hσζ P hP hc h3 hct
        (Fin.cons 1 (Fin.cons 1 diagGen4))) =
      MulAut.conj (leviSU hK hf hζ hσζ P hP (diagThreeHom c hc h3 diagGen4)) := by
  have e : vtwPhi hK hf hζ hσζ P hP hc h3 hct (Fin.cons 1 (Fin.cons 1 diagGen4)) =
      Subgroup.inclusion (twistedE6RootGroup_le_twistedE6InndiagGL (unitaryInvolution K ℓ f))
        (leviSU hK hf hζ hσζ P hP (diagThreeHom c hc h3 diagGen4)) := by
    apply Subtype.ext
    rw [vtwPhi_apply]
    change (vtwX hK hf hζ hσζ P hP hc h3 : ModGL TwistTag.E6.tag K) ^
        (Multiplicative.toAdd (1 : Multiplicative (ZMod 3))).val *
      ((twE6R0 c hct : ModGL TwistTag.E6.tag K) ^
          (Multiplicative.toAdd (1 : Multiplicative (ZMod 3))).val *
        (leviSU hK hf hζ hσζ P hP (diagThreeHom c hc h3 diagGen4) : ModGL TwistTag.E6.tag K)) = _
    rw [toAdd_one, ZMod.val_zero, pow_zero, pow_zero, one_mul, one_mul]
    rfl
  rw [e, twistedE6InndiagConj_inclusion]

theorem exists_vtwV_layer (hℓ2 : ℓ ≠ 2) :
    ∃ v₁ ∈ vtwV hK hf hζ hσζ P hP hc h3 hct,
      v₁ ∉ Subgroup.zpowers (MulAut.conj (twE6R0 c hct)) ∧
      GLAPLayer 3 ((leviJ K ℓ f).subgroupOf (twistedE6RootGroup K (unitaryInvolution K ℓ f)) ⊓
        fixSubgroup v₁) ≠ ⊥ := by
  set y : Fin 6 → Multiplicative (ZMod 3) := Fin.cons 1 (Fin.cons 1 diagGen4) with hy
  set Φ := (twistedE6InndiagConj K (unitaryInvolution K ℓ f)).comp
    (vtwPhi hK hf hζ hσζ P hP hc h3 hct) with hΦ
  have hΦy : Φ y = MulAut.conj (leviSU hK hf hζ hσζ P hP (diagThreeHom c hc h3 diagGen4)) :=
    vtwPhi_cons_diagGen4 hK hf hζ hσζ P hP hc h3 hct
  have hΦe : Φ (Pi.mulSingle 1 (Multiplicative.ofAdd 1)) = MulAut.conj (twE6R0 c hct) := by
    rw [hΦ, MonoidHom.comp_apply, vtwPhi_mulSingle_one, twistedE6InndiagConj_inclusion]
  have hinj : Function.Injective Φ := vtwPhi_conj_injective hK hf hζ hσζ P hP hc h3 hct
  refine ⟨Φ y, ⟨y, rfl⟩, fun hmem => ?_, ?_⟩
  · obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hmem
    rw [← hΦe, ← map_zpow] at hn
    have h2 := congrFun (hinj hn) 2
    have hl : ((Pi.mulSingle 1 (Multiplicative.ofAdd 1) : Fin 6 → Multiplicative (ZMod 3)) ^ n)
        2 = 1 := by
      rw [Pi.pow_apply, Pi.mulSingle_eq_of_ne (by decide), _root_.one_zpow]
    have hr : y 2 = Multiplicative.ofAdd 1 := by
      rw [hy]
      rfl
    rw [hl, hr] at h2
    exact absurd (congrArg Multiplicative.toAdd h2) (by decide)
  · rw [hΦy]
    exact glaPLayer_inf_fixSubgroup_ne_bot hK hf hζ hσζ P hP hℓ2 h3 hc

theorem twE6VtwInput_holds : TwE6VtwInput := by
  intro K _ _ ℓ f _ _ hK hf hℓ2 h3 ζ hζ hσζ P hP c hc hct
  obtain ⟨hVe, hVc⟩ := isElemAbelian_vtwV hK hf hζ hσζ P hP hc h3 hct
  exact ⟨vtwV hK hf hζ hσζ P hP hc h3 hct, vtwV_le hK hf hζ hσζ P hP hc h3 hct, hVe, hVc,
    conj_twE6R0_mem_vtwV hK hf hζ hσζ P hP hc h3 hct,
    vtwV_apply_twE6T hK hf hζ hσζ P hP hc h3 hct,
    vtwV_map_leviJ hK hf hζ hσζ P hP hc h3 hct,
    vtwV_mem_zpowers_of_trivial hK hf hζ hσζ P hP hc h3 hct,
    exists_vtwV_layer hK hf hζ hσζ P hP hc h3 hct hℓ2,
    fun δ hδζ hδc hδP _ hv =>
      fieldActor_mul_eq_of_mem_vtwV hK hf hζ hσζ P hP hc h3 hct δ hδζ hδc hδP hv,
    vtwV_apply_leviSU_of_isDiag hK hf hζ hσζ P hP hc h3 hct⟩

end CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.TwE6Vtw

end
