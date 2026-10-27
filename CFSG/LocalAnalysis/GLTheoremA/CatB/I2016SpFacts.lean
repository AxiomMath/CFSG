module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I2016SpMain
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTSp8F
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U4InnSp8d
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1431YCase2
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1210

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2016Sp

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.CatB
  CFSG.LocalAnalysis.GLTheoremA.CatB.U4Sp8 CFSG.LocalAnalysis.GLTheoremA.I2016
  CFSG.LocalAnalysis.GLTheoremA.HSubT

theorem i2016FactSp_of_gaps (hS : SchurSp8) (hGap : FpfIrrGap) : I2016.I2016FactSp := by
  intro Q _ _ σ A I T hQ _ hcat hσ3 hA hA6 hI hIt hT1 hT2 hTσ hAT
  have hcat9 : catalogIs (Q ⧸ Subgroup.center Q) S9.isSp8two := hcat
  have hZ0 : Subgroup.center Q = ⊥ := hS Q hQ hcat9
  have eQ : Q ≃* (Q ⧸ Subgroup.center Q) :=
    ((QuotientGroup.quotientMulEquivOfEq hZ0).trans QuotientGroup.quotientBot).symm
  obtain ⟨eS⟩ := sp8_model hcat9
  let e : Q ≃* StatedSp 4 (ZMod 2) := eQ.trans eS
  haveI : Finite (StatedSp 4 (ZMod 2)) := Finite.of_equiv Q e.toEquiv
  haveI : IsSimpleGroup (Q ⧸ Subgroup.center Q) := hQ.2
  haveI : IsSimpleGroup (StatedSp 4 (ZMod 2)) := eS.symm.isSimpleGroup
  have hcatS : catalogIs (StatedSp 4 (ZMod 2)) S9.isSp8two := by
    obtain ⟨i, hi, ⟨ej⟩⟩ := hcat
    exact ⟨i, hi, ⟨eS.symm.trans ej⟩⟩
  have hσS3 : (MulAut.congr e σ) ^ 3 = 1 := by
    rw [← map_pow, hσ3, map_one]
  obtain ⟨g, hg⟩ := mem_innerAut_of_index_le_two hσS3 (u4Out_index_sp8two hcatS)
  have hconj : ∀ y : Q, g * e y * g⁻¹ = e (σ y) := by
    intro y
    have h := congrArg (fun φ : MulAut (StatedSp 4 (ZMod 2)) => φ (e y)) hg
    rw [MulAut.conj_apply] at h
    rw [h]
    show e (σ (e.symm (e y))) = e (σ y)
    rw [MulEquiv.symm_apply_apply]
  have hg3 : g ^ 3 = 1 := by
    have hc : MulAut.conj (g ^ 3) = 1 := by
      rw [map_pow, hg, hσS3]
    have h1 : ∀ x : StatedSp 4 (ZMod 2), g ^ 3 * x * (g ^ 3)⁻¹ = x := fun x => by
      have h0 := DFunLike.congr_fun hc x
      rw [MulAut.one_apply, MulAut.conj_apply] at h0
      exact h0
    have hcen : e.symm (g ^ 3) ∈ Subgroup.center Q := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply e.injective
      have h2 : e y * g ^ 3 = g ^ 3 * e y := by
        have := h1 (e y)
        rw [mul_inv_eq_iff_eq_mul] at this
        exact this.symm
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact h2
    rw [hZ0, Subgroup.mem_bot] at hcen
    have h3 : g ^ 3 = e (e.symm (g ^ 3)) := (e.apply_symm_apply _).symm
    rw [h3, hcen, map_one]
  have hfix : (fixSub σ).map e.toMonoidHom = Subgroup.centralizer ({g} : Set (StatedSp 4 (ZMod 2))) := by
    ext x
    rw [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : σ y = y := hy
      have h := hconj y
      rw [hy'] at h
      have h' : g * e y = e y * g := mul_inv_eq_iff_eq_mul.1 h
      exact h'.symm
    · intro hx
      refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
      show σ (e.symm x) = e.symm x
      apply e.injective
      have h := hconj (e.symm x)
      rw [e.apply_symm_apply] at h
      have h2 : g * x * g⁻¹ = x := by rw [← hx, mul_inv_cancel_right]
      rw [h2] at h
      rw [e.apply_symm_apply]
      exact h.symm
  have hI' : CFSG.Open.IsSubnormal (I.map e.toMonoidHom)
      (Subgroup.centralizer ({g} : Set (StatedSp 4 (ZMod 2)))) := by
    rw [← hfix]
    exact CFSG.Open.IsSubnormal.map e.toMonoidHom hI
  have hA' : A.map e.toMonoidHom ≤ Subgroup.centralizer ({g} : Set (StatedSp 4 (ZMod 2))) := by
    rw [← hfix]
    exact Subgroup.map_mono hA
  have hA6' : HasA6Quot (A.map e.toMonoidHom) := by
    obtain ⟨A₀, S₆, hS₆, f, hA₀A, hcatA6, hfsurj⟩ := hA6
    let φ : ↥(A₀.map e.toMonoidHom) ≃* ↥A₀ :=
      (Subgroup.equivMapOfInjective A₀ e.toMonoidHom e.injective).symm
    exact ⟨A₀.map e.toMonoidHom, S₆, hS₆, f.comp φ.toMonoidHom, Subgroup.map_mono hA₀A, hcatA6,
      hfsurj.comp φ.surjective⟩
  have hq' : QuotU4 (I.map e.toMonoidHom) := by
    have hIt' : catalogIs (PSimple 3 I) S8.isPSp43 := hIt.1
    obtain ⟨i, hi, ⟨eP⟩⟩ := hIt'
    have hU : catalogIs (PSimple 3 I) S9.isU4two :=
      ⟨i, CFSG.LocalAnalysis.GLTheoremA.I1431Y.isU4two_of_isPSp43 hi, ⟨eP⟩⟩
    have hcard : Nat.card (PSimple 3 I) = 25920 := card_of_catalogIs_u4two hU
    let φI : ↥(I.map e.toMonoidHom) ≃* ↥I :=
      (Subgroup.equivMapOfInjective I e.toMonoidHom e.injective).symm
    let Ψ : ↥I →* PSimple 3 I :=
      (QuotientGroup.mk' (Subgroup.center (PQuot 3 I))).comp (QuotientGroup.mk' (GLAPPrimeCore 3 ↥I))
    have hΨ : Function.Surjective Ψ :=
      (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
    exact ⟨PSimple 3 I, inferInstance, Ψ.comp φI.toMonoidHom, hΨ.comp φI.surjective, hcard⟩
  have hT1' : T.map e.toMonoidHom ≠ ⊥ := by
    intro h
    exact hT1 ((Subgroup.map_eq_bot_iff_of_injective T e.injective).1 h)
  have hT2' : IsPGroup 2 (T.map e.toMonoidHom) := by
    intro x
    obtain ⟨t, ht, hxt⟩ := Subgroup.mem_map.1 x.2
    obtain ⟨k, hk⟩ := hT2 ⟨t, ht⟩
    refine ⟨k, Subtype.ext ?_⟩
    have h2 : t ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hx : (x : StatedSp 4 (ZMod 2)) = e t := hxt.symm
    rw [Subgroup.coe_pow, Subgroup.coe_one, hx, ← map_pow, h2, map_one]
  have hTg' : ∀ x ∈ T.map e.toMonoidHom, g⁻¹ * x * g ∈ T.map e.toMonoidHom := by
    intro x hx
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hx
    obtain ⟨u, hu, hus⟩ : ∃ u ∈ T, σ u = s := by
      have hsT : s ∈ T.map σ.toMonoidHom := by
        rw [hTσ]
        exact hs
      obtain ⟨u, hu, hus⟩ := Subgroup.mem_map.1 hsT
      exact ⟨u, hu, hus⟩
    refine Subgroup.mem_map.2 ⟨u, hu, ?_⟩
    have h := hconj u
    rw [hus] at h
    show e u = g⁻¹ * e s * g
    rw [← h]
    group
  have hAT' : A.map e.toMonoidHom ≤
      Subgroup.normalizer ((T.map e.toMonoidHom : Subgroup (StatedSp 4 (ZMod 2))) :
        Set (StatedSp 4 (ZMod 2))) := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← Subgroup.map_normalizer_eq_of_bijective T e.bijective]
    exact Subgroup.mem_map.2 ⟨a, hAT ha, rfl⟩
  exact noT_sp8 hGap hg3 hI' hq' hA' hA6' hT1' hT2' hTg' hAT'

end CFSG.LocalAnalysis.GLTheoremA.I2016Sp

end
