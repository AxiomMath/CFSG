module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcTwE6ThreeModel

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.TwE6Vtw

open Matrix CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.TwE6Conc
open CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.TwE6Outer
open CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary
  (coordBlockSU mem_coordBlockSU_iff isQuasisimple_coordBlockSU)


variable {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
  (hK : Nat.card K = (ℓ ^ f) ^ 2) (hf : 1 ≤ f)
  {ζ : K} (hζ : ζ ≠ 0) (hσζ : unitaryInvolution K ℓ f ζ = -ζ)
  (P : GL (Fin 6) K) (hP : conjTr (unitaryInvolution K ℓ f) (P : Matrix (Fin 6) (Fin 6) K) *
    (P : Matrix (Fin 6) (Fin 6) K) = antidiag 6)

theorem glaPLayer_inf_fixSubgroup_ne_bot (hℓ2 : ℓ ≠ 2) (h3 : 3 ∣ ℓ ^ f + 1) {c : Kˣ}
    (hc : orderOf c = 3) :
    GLAPLayer 3 ((leviJ K ℓ f).subgroupOf (twistedE6RootGroup K (unitaryInvolution K ℓ f)) ⊓
      fixSubgroup (MulAut.conj (leviSU hK hf hζ hσζ P hP (diagThreeHom c hc h3 diagGen4)))) ≠ ⊥ := by
  classical
  set C₀ := twistedE6RootGroup K (unitaryInvolution K ℓ f) with hC₀
  set ι := leviSU hK hf hζ hσζ P hP with hιdef
  set h := diagThreeHom c hc h3 diagGen4 with hhdef
  have hQ1 : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ (Fact.out : ℓ.Prime).pos
  have hpQ2 := three_dvd_sq_sub_one_of_dvd_add_one hQ1 h3
  have h3K : ((3 : ℕ) : K) ≠ 0 := natCast_ne_zero_of_dvd_sq hf Nat.prime_three hpQ2
  have htr : (c : K) + ((c⁻¹ : Kˣ) : K) + 4 ≠ 0 := by
    rw [add_inv_eq_neg_one_of_orderOf_three hc]
    intro h'
    apply h3K
    push_cast
    linear_combination h'
  have hhmem : h ∈ coordBlockSU K ℓ f blk01 := diagThreeHom_diagGen4_mem c hc h3
  have hhp : h ^ 3 = 1 := by rw [hhdef, ← map_pow, pow_eq_one_of_fin, map_one]
  have hh1 : h ≠ 1 := fun h1 =>
    diagGen4_ne_one (diagThreeHom_injective c hc h3 (h1.trans (map_one _).symm))
  set N0 := coordBlockSU K ℓ f blk01ᶜ with hN0
  set N := N0.map ι with hN
  have hN0inj : Function.Injective (ι.comp N0.subtype) := by
    rw [injective_iff_map_eq_one]
    intro y hy
    obtain ⟨l, hl⟩ := exists_smul_of_leviSU_eq_one hK hf hζ hσζ P hP hy
    simp only [Subgroup.coe_subtype] at hl
    have h00 := (mem_coordBlockSU_iff.1 y.2) 0 0 (Or.inl (by decide))
    rw [hl] at h00
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, if_pos] at h00
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    rw [hl, h00, one_smul]
    rfl
  have hrange : (ι.comp N0.subtype).range = N := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have heN : ↥N0 ≃* ↥N :=
    (MonoidHom.ofInjective hN0inj).trans (MulEquiv.subgroupCongr hrange)
  have hNq : CFSG.Open.IsQuasisimple ↥N :=
    CFSG.LocalAnalysis.GLTheoremA.KD264Gen.Co15.isQuasisimple_of_equiv heN
      (isQuasisimple_coordBlockSU hK (five_le_of_three_dvd_add_one hℓ2 h3) (by decide))
  have hpN : 3 ∣ Nat.card ↥N := by
    rw [← Nat.card_congr heN.toEquiv]
    exact dvd_card_coordBlockSU_compl (dvd_card_su_two hK hpQ2)
  have hNJ : N ≤ (leviJ K ℓ f).subgroupOf C₀ := by
    rintro _ ⟨y, -, rfl⟩
    exact leviSU_mem_leviJ hK hf hζ hσζ P hP y
  have hNC : N ≤ fixSubgroup (MulAut.conj (ι h)) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [mem_fixSubgroup, MulAut.conj_apply]
    have hy1 : y * h = h * y :=
      Subgroup.mem_centralizer_singleton_iff.1 (coordBlockSU_compl_le_centralizer hhmem hy)
    rw [← map_inv, ← map_mul, ← map_mul, ← hy1, mul_inv_cancel_right]
  have hNn : (N.subgroupOf ((leviJ K ℓ f).subgroupOf C₀ ⊓
      fixSubgroup (MulAut.conj (ι h)))).Normal := by
    refine CFSG.HardMathSupport.Dickson.I271.normal_subgroupOf_of_conj fun g hg l hl => ?_
    obtain ⟨hgJ, hgC⟩ := Subgroup.mem_inf.1 hg
    obtain ⟨y', rfl⟩ := exists_leviSU_eq hK hf hζ hσζ P hP hgJ
    have hgC' := mem_fixSubgroup.1 hgC
    rw [MulAut.conj_apply] at hgC'
    have hcomm1 : ι y' * ι h = ι h * ι y' := by
      calc ι y' * ι h = ι h * ι y' * (ι h)⁻¹ * ι h := by rw [hgC']
        _ = ι h * ι y' := by group
    have hy'c : y' * h = h * y' := commute_of_leviSU_commute_diagThree c hc h3 htr y' hcomm1
    obtain ⟨y, hy, rfl⟩ := hl
    refine ⟨y' * y * y'⁻¹, conj_mem_coordBlockSU_of_commute h3K hhmem hhp hh1 hy'c hy, ?_⟩
    rw [map_mul, map_mul, map_inv]
  have hNc := CFSG.HardMathSupport.Dickson.I271.glaPComponent_of_normal Nat.prime_three hNq hpN
    (le_inf hNJ hNC) hNn
  intro hbot
  have hle : N ≤ GLAPLayer 3 ((leviJ K ℓ f).subgroupOf C₀ ⊓ fixSubgroup (MulAut.conj (ι h))) :=
    le_sSup hNc
  rw [hbot, le_bot_iff] at hle
  exact CFSG.LocalAnalysis.GLTheoremA.glaPComponent_ne_bot' hNc hle

end CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.TwE6Vtw

end
