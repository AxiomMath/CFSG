module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherLinearAutNormal
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneCoprimeCentral
public import CFSG.HardMathSupport.Timmesfeld.LinearRank.ProjRank
public import CFSG.LocalAnalysis.SectionRank.SubgroupRank
public import CFSG.GH74.GLS.Balance.Bender.Aux1

public section

namespace CFSG.LocalAnalysis.ComponentInitial.LinearFlag

open Subgroup

variable {K : Type} [Field K]

theorem pRank_linearAutGroup_le [Finite K] {n : ℕ} (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpK : p ∣ Nat.card Kˣ) :
    CFSG.Open.pRank p (linearAutGroup n K) ≤ n - 1 := by
  have hker : (conjAut n K).ker = Subgroup.center (GL (Fin n) K) := by
    ext A
    rw [MonoidHom.mem_ker,
      CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.conjAut_eq_one_iff hn,
      CFSG.HardMathSupport.Timmesfeld.LinearRank.mem_center_iff]
  let e : CFSG.HardMathSupport.Timmesfeld.LinearRank.PGL n K ≃* linearAutGroup n K :=
    (QuotientGroup.quotientMulEquivOfEq hker).symm.trans
      ((QuotientGroup.quotientKerEquivRange (conjAut n K)).trans
        (MulEquiv.subgroupCongr linearAutGroup_eq_range.symm))
  calc CFSG.Open.pRank p (linearAutGroup n K)
      = CFSG.Open.pRank p (⊤ : Subgroup (linearAutGroup n K)) :=
        (CFSG.SectionRank.pRank_eq_pRank_top_subgroup _)
    _ = CFSG.Open.pRank p (⊤ : Subgroup (CFSG.HardMathSupport.Timmesfeld.LinearRank.PGL n K)) :=
        CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e.symm
    _ ≤ n - 1 := CFSG.HardMathSupport.Timmesfeld.LinearRank.pRank_pgl_le hp hp2 hpK (by omega)

theorem coprime_orderOf_of_oResidual_eq_top {A : Type*} [Group A] [Finite A]
    (hcomm : ∀ a b : A, a * b = b * a) {p : ℕ} (hres : CFSG.GH74.GLS.oResidual p A = ⊤)
    (a : A) : Nat.Coprime (orderOf a) p := by
  have h : ∀ a ∈ CFSG.GH74.GLS.oResidual p A, Nat.Coprime (orderOf a) p := by
    intro a ha
    rw [CFSG.GH74.GLS.oResidual] at ha
    refine Subgroup.closure_induction (p := fun x _ => Nat.Coprime (orderOf x) p) ?_ ?_ ?_ ?_ ha
    · intro x hx
      exact hx
    · simp
    · intro x y hx hy hpx hpy
      exact Nat.Coprime.coprime_dvd_left (Commute.orderOf_mul_dvd_mul_orderOf (hcomm x y))
        (Nat.Coprime.mul_left hpx hpy)
    · intro x hx hpx
      rwa [orderOf_inv]
  rw [hres] at h
  exact h a (Subgroup.mem_top a)

theorem mem_of_commutator_mem_of_oResidual_eq_top {G : Type*} [Group G] {N : Subgroup G}
    [N.Normal] {p : ℕ} (hp : p.Prime) (hN : ∀ a b : G, a * b * a⁻¹ * b⁻¹ ∈ N)
    {H : Subgroup G} [Finite ↥H] (hres : CFSG.GH74.GLS.oResidual p ↥H = ⊤)
    {x : G} (hx : x ∈ H) {k : ℕ} (hxk : x ^ (p ^ k) = 1) : x ∈ N := by
  let π : G →* G ⧸ N := QuotientGroup.mk' N
  have hcomm : ∀ a b : G ⧸ N, a * b = b * a := by
    intro a b
    induction a using QuotientGroup.induction_on with | H a => ?_
    induction b using QuotientGroup.induction_on with | H b => ?_
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have h := hN b⁻¹ a⁻¹
    convert h using 1
    group
  haveI : Finite ↥(H.map π) := Finite.of_surjective _ (π.subgroupMap_surjective H)
  have hcommA : ∀ a b : ↥(H.map π), a * b = b * a := fun a b =>
    Subtype.ext (hcomm (a : G ⧸ N) (b : G ⧸ N))
  have hresA : CFSG.GH74.GLS.oResidual p ↥(H.map π) = ⊤ := by
    have hmap := CFSG.GH74.GLS.Balance.BenderExt.map_oResidual (A := ↥H)
      (B := ↥(H.map π)) hp (π.subgroupMap H) (π.subgroupMap_surjective H)
    rw [hres, Subgroup.map_top_of_surjective _ (π.subgroupMap_surjective H)] at hmap
    exact hmap.symm
  have hx' : π x ∈ H.map π := Subgroup.mem_map_of_mem π hx
  have hcop := coprime_orderOf_of_oResidual_eq_top hcommA hresA ⟨π x, hx'⟩
  have hpow : (⟨π x, hx'⟩ : ↥(H.map π)) ^ (p ^ k) = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← map_pow, hxk, map_one]
  have hdvd : orderOf (⟨π x, hx'⟩ : ↥(H.map π)) ∣ p ^ k := orderOf_dvd_of_pow_eq_one hpow
  have hcop' : Nat.Coprime (orderOf (⟨π x, hx'⟩ : ↥(H.map π))) (p ^ k) := hcop.pow_right k
  have hone : orderOf (⟨π x, hx'⟩ : ↥(H.map π)) = 1 :=
    Nat.dvd_one.mp (hcop'.dvd_mul_left.mp (by simpa using hdvd))
  have h1 : (⟨π x, hx'⟩ : ↥(H.map π)) = 1 := orderOf_eq_one_iff.mp hone
  exact (QuotientGroup.eq_one_iff x).mp (congrArg Subtype.val h1)

theorem mem_linearAutGroup_of_pow_eq_one [Finite K] {n : ℕ} (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime)
    {H : Subgroup (MulAut (projectiveSL n K))} (hres : CFSG.GH74.GLS.oResidual p ↥H = ⊤)
    {x : MulAut (projectiveSL n K)} (hx : x ∈ H) {k : ℕ} (hxk : x ^ (p ^ k) = 1) :
    x ∈ linearAutGroup n K := by
  haveI : Finite (MulAut (projectiveSL n K)) :=
    CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.finite_mulAut_projectiveSL n
  haveI : (linearAutGroup n K).Normal := linearAutGroup_normal_of_three_le hn
  refine mem_of_commutator_mem_of_oResidual_eq_top (N := linearAutGroup n K) hp ?_ hres hx hxk
  intro a b
  exact CFSG.LocalAnalysis.ComponentInitial.OuterDerived.commutator_mem_linearAutGroup hn a b

theorem pRank_le_of_oResidual_eq_top [Finite K] {n : ℕ} (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpK : p ∣ Nat.card Kˣ)
    {H : Subgroup (MulAut (projectiveSL n K))} (hres : CFSG.GH74.GLS.oResidual p ↥H = ⊤) :
    CFSG.Open.pRank p H ≤ n - 1 := by
  obtain ⟨E, hEH, hEel, hcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt H
  have hEN : E ≤ linearAutGroup n K := fun x hx =>
    mem_linearAutGroup_of_pow_eq_one hn hp hres (hEH hx) (k := 1) (by simpa using hEel.2 x hx)
  calc CFSG.Open.pRank p H ≤ CFSG.Open.pRank p (linearAutGroup n K) :=
        CFSG.SectionRank.le_pRank hp.one_lt hEN hEel hcard
    _ ≤ n - 1 := pRank_linearAutGroup_le hn hp hp2 hpK

end CFSG.LocalAnalysis.ComponentInitial.LinearFlag
