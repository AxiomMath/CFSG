module

public import Mathlib.GroupTheory.Transfer
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.ML1.FibreProduct

public section

namespace CFSG.EvenSporadicStandard.HNRecog.ML1

theorem exists_hom_C2_of_odd_index {G : Type} [Group G] [Finite G] (N : Subgroup G) [N.Normal]
    (z : G) (hz : z ∈ Subgroup.center G) (hzN : z ∉ N) (T : Subgroup G) (hNT : N ≤ T) (hzT : z ∈ T)
    (hT : Odd T.index) (hsq : ∀ t ∈ T, t ^ 2 ∈ N) :
    ∃ lam : G →* C2, lam z ≠ 1 ∧ ∀ n ∈ N, lam n = 1 := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  let W := T ⧸ N.subgroupOf T
  have hWsq : ∀ w : W, w * w = 1 := by
    intro w
    obtain ⟨t, ht⟩ := QuotientGroup.mk'_surjective (N.subgroupOf T) w
    have hsq' : QuotientGroup.mk' (N.subgroupOf T) t * QuotientGroup.mk' (N.subgroupOf T) t = 1 := by
      have h2t : QuotientGroup.mk' (N.subgroupOf T) t * QuotientGroup.mk' (N.subgroupOf T) t
          = (t ^ 2 : T ⧸ N.subgroupOf T) := by
        rw [← map_mul, ← pow_two]
        rfl
      rw [h2t]
      exact (QuotientGroup.eq_one_iff (t ^ 2)).mpr (by
        simpa only [Subgroup.mem_subgroupOf, Subgroup.coe_pow] using hsq t t.2)
    rw [← ht]
    exact hsq'
  have hcomm : ∀ a b : W, a * b = b * a := by
    intro a b
    have hab : a * b * (a * b) = 1 := hWsq (a * b)
    have ha : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hWsq a)
    have hb : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hWsq b)
    calc a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right hab).symm
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = b * a := by rw [ha, hb]
  have hWcomm : IsMulCommutative W := IsMulCommutative.of_comm hcomm
  let cW : CommGroup W := @IsMulCommutative.instCommGroup W _ hWcomm
  letI : AddCommGroup (Additive W) := @Additive.addCommGroup W cW
  letI hmod := AddCommGroup.zmodModule (G := Additive W) (n := 2) fun x => by
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero, pow_two]
    exact hWsq x.toMul
  let w0 : W := QuotientGroup.mk' (N.subgroupOf T) ⟨z, hzT⟩
  have hw0 : w0 ≠ 1 := by
    intro h
    have hmem : (⟨z, hzT⟩ : T) ∈ N.subgroupOf T :=
      (QuotientGroup.eq_one_iff (⟨z, hzT⟩ : T)).mp
        (by simpa only [w0, QuotientGroup.mk'_apply] using h)
    exact hzN (by simpa only [Subgroup.mem_subgroupOf] using hmem)
  obtain ⟨f, hf⟩ : ∃ f : Module.Dual (ZMod 2) (Additive W), f (Additive.ofMul w0) ≠ 0 := by
    by_contra h
    rw [not_exists] at h
    simp only [not_not] at h
    refine hw0 ?_
    have hv := (Module.forall_dual_apply_eq_zero_iff (ZMod 2) (Additive.ofMul w0)).mp h
    exact (ofMul_eq_zero).mp (by simpa using hv)
  let g : W →* C2 := AddMonoidHom.toMultiplicative f.toAddMonoidHom
  let lamT : T →* C2 := g.comp (QuotientGroup.mk' (N.subgroupOf T))
  have hker : ∀ x : T, (x : G) ∈ N → lamT x = 1 := by
    intro x hx
    have hxNt : x ∈ N.subgroupOf T := by
      simpa only [Subgroup.mem_subgroupOf] using hx
    have hxq : QuotientGroup.mk' (N.subgroupOf T) x = 1 := by
      change (x : T ⧸ N.subgroupOf T) = 1
      exact (QuotientGroup.eq_one_iff x).mpr hxNt
    change g (QuotientGroup.mk' (N.subgroupOf T) x) = 1
    rw [hxq, map_one]
  let lam : G →* C2 := MonoidHom.transfer (H := T) lamT
  have hkeyz : ∀ (k : ℕ) (g₀ : G), g₀⁻¹ * z ^ k * g₀ ∈ T → g₀⁻¹ * z ^ k * g₀ = z ^ k := by
    intro k g₀ _
    have hzc : z ^ k ∈ Subgroup.center G := Subgroup.pow_mem _ hz k
    have hcz : z ^ k * g₀ = g₀ * z ^ k := ((Subgroup.mem_center_iff.mp hzc) g₀).symm
    calc g₀⁻¹ * z ^ k * g₀ = g₀⁻¹ * (z ^ k * g₀) := by rw [mul_assoc]
      _ = g₀⁻¹ * (g₀ * z ^ k) := by rw [hcz]
      _ = z ^ k := by rw [inv_mul_cancel_left]
  obtain ⟨m, hm⟩ := hT
  have hzidx : z ^ T.index = z * (z ^ 2) ^ m := by
    rw [hm, pow_succ]
    rw [show (z ^ 2) ^ m = z ^ (2 * m) from (pow_mul z 2 m).symm]
    exact pow_mul_comm' z (2 * m)
  have hzidx_eq : (⟨z ^ T.index, MonoidHom.transfer_eq_pow_aux z hkeyz⟩ : T) =
      ⟨z, hzT⟩ * ⟨(z ^ 2) ^ m, T.pow_mem (T.pow_mem hzT 2) m⟩ := by
    ext
    rw [Subgroup.coe_mul]
    exact hzidx
  have hval : lamT ⟨z ^ T.index, MonoidHom.transfer_eq_pow_aux z hkeyz⟩ = lamT ⟨z, hzT⟩ := by
    rw [hzidx_eq, map_mul]
    rw [hker ⟨(z ^ 2) ^ m, T.pow_mem (T.pow_mem hzT 2) m⟩ (N.pow_mem (hsq z hzT) m), mul_one]
  have hlamz_apply : lamT ⟨z, hzT⟩ = Multiplicative.ofAdd (f (Additive.ofMul w0)) := by
    change AddMonoidHom.toMultiplicative f.toAddMonoidHom w0 =
      Multiplicative.ofAdd (f (Additive.ofMul w0))
    rw [AddMonoidHom.coe_toMultiplicative]
    rfl
  have hlamz_ne : lamT ⟨z, hzT⟩ ≠ 1 := by
    rw [hlamz_apply]
    intro h
    exact hf ((ofAdd_eq_one).mp h)
  refine ⟨lam, ?_, ?_⟩
  · have hlamz : lam z = lamT ⟨z ^ T.index, MonoidHom.transfer_eq_pow_aux z hkeyz⟩ :=
      MonoidHom.transfer_eq_pow (H := T) (ϕ := lamT) z hkeyz
    rw [hlamz, hval]
    exact hlamz_ne
  · intro n hn
    have hlamn : lam n = MonoidHom.transfer (H := T) lamT n := rfl
    haveI : Fintype (Quotient (MulAction.orbitRel (Subgroup.zpowers n) (G ⧸ T))) := Fintype.ofFinite _
    rw [hlamn, MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot (H := T) (ϕ := lamT) n]
    refine Finset.prod_eq_one fun q _ => ?_
    apply hker
    simpa using (inferInstance : N.Normal).conj_mem
      (n ^ Function.minimalPeriod (n • ·) q.out) (N.pow_mem hn _) (q.out.out)⁻¹

end CFSG.EvenSporadicStandard.HNRecog.ML1
