module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcThreeTwE6Vtw
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcTwE6ConcOuter

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.TwE6Vtw

open Matrix CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.E6A5Cube CFSG.LieType.SeitzGeneration.ExcWideThree
  CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply)
open CFSG.RankThree.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.ClassicalInvolution.Balance.StrongBalance (GUid mem_GUid conjSUid coe_conjSUid)
open CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.TwE6Conc
open CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.TwE6Outer

section Field


variable {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
  (hK : Nat.card K = (ℓ ^ f) ^ 2) (hf : 1 ≤ f)
  {ζ : K} (hζ : ζ ≠ 0) (hσζ : unitaryInvolution K ℓ f ζ = -ζ)
  (P : GL (Fin 6) K) (hP : conjTr (unitaryInvolution K ℓ f) (P : Matrix (Fin 6) (Fin 6) K) *
    (P : Matrix (Fin 6) (Fin 6) K) = antidiag 6)
  {c : Kˣ} (hc : orderOf c = 3) (h3 : 3 ∣ ℓ ^ f + 1)
  (hct : unitaryInvolution K ℓ f ((c : K) + ((c⁻¹ : Kˣ) : K)) = (c : K) + ((c⁻¹ : Kˣ) : K))

omit
  [Finite K] [Fact ℓ.Prime] [CharP K ℓ] in
private theorem units_map_eq_of_mem_zpowers {δ : K ≃+* K} (hδc : δ c = c) {u : Kˣ}
    (hu : u ∈ Subgroup.zpowers c) : Units.map δ.toRingHom.toMonoidHom u = u := by
  have hc' : Units.map δ.toRingHom.toMonoidHom c = c := Units.ext hδc
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  rw [map_zpow, hc']

omit
  [Fact ℓ.Prime] [CharP K ℓ] in
private theorem glMap_diagGL {δ : K ≃+* K} {d : Fin 6 → Kˣ}
    (hd : ∀ i, Units.map δ.toRingHom.toMonoidHom (d i) = d i) :
    Matrix.GeneralLinearGroup.map δ.toRingHom (diagGL K 6 d) = diagGL K 6 d := by
  apply Units.ext
  change ((diagGL K 6 d : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).map δ =
    ((diagGL K 6 d : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)
  rw [coe_diagGL, diagonal_map (map_zero δ)]
  congr 1
  funext i
  exact congrArg Units.val (hd i)

theorem fieldActor_mul_eq_of_mem_vtwV (δ : K ≃+* K) (hδζ : δ ζ = ζ) (hδc : δ c = c)
    (hδP : ∀ i j, δ ((P : Matrix (Fin 6) (Fin 6) K) i j) = (P : Matrix (Fin 6) (Fin 6) K) i j)
    {v : MulAut ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f))}
    (hv : v ∈ vtwV hK hf hζ hσζ P hP hc h3 hct) :
    fieldActor (unitaryInvolution K ℓ f) δ * v = v * fieldActor (unitaryInvolution K ℓ f) δ := by
  have hzp : ∀ u ∈ Subgroup.zpowers c, Units.map δ.toRingHom.toMonoidHom u = u :=
    fun u hu => units_map_eq_of_mem_zpowers hδc hu
  have hc' : Units.map δ.toRingHom.toMonoidHom c = c := hzp c (Subgroup.mem_zpowers c)
  have hcinv : Units.map δ.toRingHom.toMonoidHom c⁻¹ = c⁻¹ := by rw [map_inv, hc']
  have hone : Units.map δ.toRingHom.toMonoidHom (1 : Kˣ) = 1 := map_one _
  have hlevi : ∀ s : Su K ℓ f 6,
      ((s : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).map δ =
        ((s : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) →
      Units.map (entrywiseHom δ.toRingHom)
          (leviSU hK hf hζ hσζ P hP s : ModGL TwistTag.E6.tag K) =
        (leviSU hK hf hζ hσζ P hP s : ModGL TwistTag.E6.tag K) := by
    intro s hs
    have h := congrArg Subtype.val (entrywise_leviSU hK hf hζ hσζ P hP hδζ hδP s)
    rw [coe_fieldActor] at h
    refine h.trans (congrArg (fun z => (leviSU hK hf hζ hσζ P hP z : ModGL TwistTag.E6.tag K))
      (Subtype.ext (Units.ext ?_)))
    rw [coe_suidMap]
    exact hs
  have hR : Units.map (entrywiseHom δ.toRingHom) (twE6R0 c hct : ModGL TwistTag.E6.tag K) =
      (twE6R0 c hct : ModGL TwistTag.E6.tag K) := by
    have hδc2 : δ ((c : K) + ((c⁻¹ : Kˣ) : K)) = (c : K) + ((c⁻¹ : Kˣ) : K) := by
      rw [map_add, hδc, Units.val_inv_eq_inv_val, map_inv₀, hδc]
    have h := congrArg Subtype.val (fieldActor_twE6R0 (ℓ := ℓ) (f := f) (δ := δ) c hct hδc2)
    rw [coe_fieldActor] at h
    exact h
  have hD : Units.map (entrywiseHom δ.toRingHom) (vtwD c : ModGL TwistTag.E6.tag K) = vtwD c := by
    rw [vtwD, CFSG.LieType.Chevalley.units_map_entrywiseHom_rootDiagUnit]
    congr 1
    funext i
    change Fin 6 at i
    fin_cases i
    · exact hc'
    · exact hone
    · exact hone
    · exact hone
    · exact hone
    · exact hcinv
  have hW : Units.map (entrywiseHom δ.toRingHom)
      (leviSU hK hf hζ hσζ P hP (vtwW P hP hc h3) : ModGL TwistTag.E6.tag K) =
        (leviSU hK hf hζ hσζ P hP (vtwW P hP hc h3) : ModGL TwistTag.E6.tag K) := by
    refine hlevi _ ?_
    have hPm : Matrix.GeneralLinearGroup.map δ.toRingHom P = P := by
      apply Units.ext
      change (P : Matrix (Fin 6) (Fin 6) K).map δ = (P : Matrix (Fin 6) (Fin 6) K)
      ext i j
      exact hδP i j
    have hd0 : Matrix.GeneralLinearGroup.map δ.toRingHom (diagGL K 6 (vtwD0 c)) =
        diagGL K 6 (vtwD0 c) := by
      refine glMap_diagGL fun i => ?_
      fin_cases i
      · exact hone
      · exact hone
      · exact hone
      · exact hone
      · exact hcinv
      · exact hone
    have he : Matrix.GeneralLinearGroup.map δ.toRingHom (diagGL K 6 (vtwE c)) =
        diagGL K 6 (vtwE c) := by
      refine glMap_diagGL fun i => ?_
      fin_cases i
      · exact hone
      · exact hcinv
      · exact hcinv
      · exact hcinv
      · exact hcinv
      · exact hone
    have hWm : Matrix.GeneralLinearGroup.map δ.toRingHom
        ((vtwW P hP hc h3 : Su K ℓ f 6) : GL (Fin 6) K) =
          ((vtwW P hP hc h3 : Su K ℓ f 6) : GL (Fin 6) K) := by
      rw [coe_vtwW, coe_vtwD0GU, coe_vtwC, map_mul, map_inv, map_mul, map_mul, map_inv, hPm,
        hd0, he]
    exact congrArg Units.val hWm
  have hS : ∀ s : Fin 4 → Multiplicative (ZMod 3),
      Units.map (entrywiseHom δ.toRingHom)
          (leviSU hK hf hζ hσζ P hP (diagThreeHom c hc h3 s) : ModGL TwistTag.E6.tag K) =
        (leviSU hK hf hζ hσζ P hP (diagThreeHom c hc h3 s) : ModGL TwistTag.E6.tag K) := by
    intro s
    refine hlevi _ ?_
    rw [coe_diagThreeHom, diagonal_map (map_zero δ)]
    congr 1
    funext i
    refine congrArg Units.val (hzp _ ?_)
    simp only [diagTuple]
    split_ifs
    · exact Subgroup.pow_mem _ (Subgroup.mem_zpowers c) _
    · exact Subgroup.inv_mem _ (Subgroup.prod_mem _ fun j _ =>
        Subgroup.pow_mem _ (Subgroup.mem_zpowers c) _)
  have hX : Units.map (entrywiseHom δ.toRingHom)
      (vtwX hK hf hζ hσζ P hP hc h3 : ModGL TwistTag.E6.tag K) =
        (vtwX hK hf hζ hσζ P hP hc h3 : ModGL TwistTag.E6.tag K) := by
    rw [coe_vtwX, map_mul, hW, hD]
  obtain ⟨y, rfl⟩ := hv
  have hΦ : Units.map (entrywiseHom δ.toRingHom)
      (vtwPhi hK hf hζ hσζ P hP hc h3 hct y : ModGL TwistTag.E6.tag K) =
        (vtwPhi hK hf hζ hσζ P hP hc h3 hct y : ModGL TwistTag.E6.tag K) := by
    rw [vtwPhi_apply, map_mul, map_mul, map_pow, map_pow, hX, hR, hS]
  refine MulEquiv.ext fun g => Subtype.ext ?_
  change Units.map (entrywiseHom δ.toRingHom)
      ((vtwPhi hK hf hζ hσζ P hP hc h3 hct y : ModGL TwistTag.E6.tag K) *
        (g : ModGL TwistTag.E6.tag K) *
          (vtwPhi hK hf hζ hσζ P hP hc h3 hct y : ModGL TwistTag.E6.tag K)⁻¹) =
    (vtwPhi hK hf hζ hσζ P hP hc h3 hct y : ModGL TwistTag.E6.tag K) *
      Units.map (entrywiseHom δ.toRingHom) (g : ModGL TwistTag.E6.tag K) *
        (vtwPhi hK hf hζ hσζ P hP hc h3 hct y : ModGL TwistTag.E6.tag K)⁻¹
  rw [map_mul, map_mul, map_inv, hΦ]

end Field

end CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.TwE6Vtw

end
