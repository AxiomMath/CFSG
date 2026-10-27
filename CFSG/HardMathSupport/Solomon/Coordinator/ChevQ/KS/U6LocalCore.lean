module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUModel
public import CFSG.HardMathSupport.Dickson.Bal207.LocalBalClassicalUniOuter
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThree
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Open
import Mathlib.GroupTheory.SchurZassenhaus
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAUGen
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.F4LocalOne
import CFSG.HardMathSupport.Timmesfeld.CrossChar.UnitaryBalNonsplit
import CFSG.HardMathSupport.Timmesfeld.CrossChar.UnitaryBalSplit
import CFSG.HardMathSupport.Timmesfeld.CrossChar.UnitaryOuter
import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossOrthBase
import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossUniOuter
import CFSG.LocalAnalysis.ComponentInitial.UnitaryDiagonalOuterOrder
import CFSG.RankThree.PartOne.KC.UnitaryOrthonormalEigenbasis
import CFSG.RankThree.PartOne.KC.UnitaryPrimaryPairing
import CFSG.RankThree.PartOne.KC.UnitaryRigidityLines
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneProjSlice
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL4
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL4Cases
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL4Kill
import CFSG.HardMathSupport.Timmesfeld.CrossChar.UnitaryDiag
import CFSG.HardMathSupport.Timmesfeld.CrossChar.UnitaryFamily
import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUGraphCore
import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUGraphDescent
import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUInnerPaired
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedGraphSymm

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSFourU

open Polynomial Module Matrix CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.Balance
  CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.ComponentClassification.Burgoyne.U
  CFSG.ComponentClassification.Burgoyne.Proj CFSG.GH74.GLS.Stage2.Signalizer.Odd87
  CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.KCUnitaryFrame CFSG.RankThree.PartOne.KCUnitaryPlane
  CFSG.RankThree.PartOne.KCUnitaryScalar CFSG.RankThree.PartOne.KCUnitary
  CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
  CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.PSUTwo CFSG.HardMathSupport.Dickson.Bal207

namespace U6LocalAux

section CentralQuotient

variable {G P : Type*} [Group G] [Group P]

theorem noNormalPPrime_centralizer_map {p : ℕ} (π : G →* P) (hπ : Function.Surjective π)
    (hZ : π.ker ≤ Subgroup.center G) (hZp : ∃ k : ℕ, Nat.card π.ker = p ^ k) {x : G}
    (hx : NoNormalPPrime p (Subgroup.centralizer ({x} : Set G))) :
    NoNormalPPrime p (Subgroup.centralizer ({π x} : Set P)) := by
  classical
  intro N hNC hNn hNc
  set Nt : Subgroup G := N.comap π with hNt
  set Z : Subgroup G := π.ker with hZdef
  have hZNt : Z ≤ Nt := fun z hz => by
    rw [hNt, Subgroup.mem_comap, MonoidHom.mem_ker.1 hz]
    exact N.one_mem
  haveI hZnormal : Z.Normal := π.normal_ker
  set Z' : Subgroup Nt := Z.subgroupOf Nt with hZ'
  haveI : Z'.Normal := Subgroup.Normal.subgroupOf hZnormal Nt
  set m := Nat.card N with hm
  have hidx : Z'.index = m := by
    have h1 : Z.relIndex Nt = Nat.card (Nt.map π) := Subgroup.relIndex_ker π (K := Nt)
    rw [hNt, Subgroup.map_comap_eq_self_of_surjective hπ] at h1
    exact h1
  have hcardZ : Nat.card Z' = Nat.card Z :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZNt).toEquiv
  have hcopZ : Nat.Coprime (Nat.card Z) m := by
    obtain ⟨k, hk⟩ := hZp
    rw [hZdef, hk]
    exact Nat.Coprime.pow_left k hNc
  have hcop : Nat.Coprime (Nat.card Z') Z'.index := by rw [hcardZ, hidx]; exact hcopZ
  obtain ⟨H', hH'⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  set H : Subgroup G := H'.map Nt.subtype with hH
  have hH'card : Nat.card H' = m := hH'.symm.index_eq_card.symm.trans hidx
  have hHcard : Nat.card H = m := by
    rw [hH, Subgroup.card_map_of_injective Nt.subtype_injective, hH'card]
  have hHle : H ≤ Nt := fun y hy => by
    obtain ⟨w, -, rfl⟩ := hy
    exact w.2
  have hHpow : ∀ y ∈ H, y ^ m = 1 := by
    intro y hy
    obtain ⟨w, hw, rfl⟩ := hy
    have h1 : (⟨w, hw⟩ : H') ^ m = 1 := by
      rw [← hH'card]
      exact pow_card_eq_one'
    have h2 := congrArg (fun a : H' => ((a : Nt) : G)) h1
    simpa using h2
  have hmemH : ∀ y ∈ Nt, y ^ m = 1 → y ∈ H := by
    intro y hy hym
    obtain ⟨⟨z, w⟩, hzw⟩ := hH'.2 ⟨y, hy⟩
    have hzZ : (z : Nt).1 ∈ Z := Subgroup.mem_subgroupOf.1 z.2
    have hyzw : y = (z : Nt).1 * (w : Nt).1 := by
      have := congrArg (fun a : Nt => (a : G)) hzw
      simpa using this.symm
    have hwH : (w : Nt).1 ∈ H := ⟨(w : Nt), w.2, rfl⟩
    have hwm : (w : Nt).1 ^ m = 1 := hHpow _ hwH
    have hcomm : Commute (z : Nt).1 (w : Nt).1 :=
      (Subgroup.mem_center_iff.1 (hZ hzZ) _).symm
    have hzm : (z : Nt).1 ^ m = 1 := by
      have := hym
      rw [hyzw, hcomm.mul_pow, hwm, mul_one] at this
      exact this
    have hz1 : (z : Nt).1 = 1 := by
      have h1 : orderOf (z : Nt).1 ∣ Nat.card Z := Subgroup.orderOf_dvd_natCard Z hzZ
      have h2 : orderOf (z : Nt).1 ∣ m := orderOf_dvd_of_pow_eq_one hzm
      exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcopZ h1 h2)
    rw [hyzw, hz1, one_mul]
    exact hwH
  have hHcent : ∀ y ∈ H, y * x = x * y := by
    intro y hy
    have hπy : π y ∈ N := hHle hy
    have hcomm' : π y * π x = π x * π y := Subgroup.mem_centralizer_singleton_iff.1 (hNC hπy)
    set c : G := y * x * y⁻¹ * x⁻¹ with hc
    have hcZ : c ∈ Z := by
      rw [hZdef, MonoidHom.mem_ker]
      simp only [hc, map_mul, map_inv]
      rw [hcomm']
      group
    have hcc : ∀ g : G, c * g = g * c := fun g => (Subgroup.mem_center_iff.1 (hZ hcZ) g).symm
    have hyx : y * x = c * x * y := by
      rw [hc]
      group
    have hpow : ∀ k : ℕ, y ^ k * x = c ^ k * x * y ^ k := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        calc y ^ (k + 1) * x = y ^ k * (y * x) := by rw [pow_succ, mul_assoc]
          _ = y ^ k * (c * x * y) := by rw [hyx]
          _ = c * (y ^ k * x) * y := by
              calc y ^ k * (c * x * y) = (y ^ k * c) * x * y := by group
                _ = (c * y ^ k) * x * y := by rw [← hcc (y ^ k)]
                _ = c * (y ^ k * x) * y := by group
          _ = c * (c ^ k * x * y ^ k) * y := by rw [ih]
          _ = c ^ (k + 1) * x * y ^ (k + 1) := by rw [pow_succ, pow_succ]; group
    have hcm : c ^ m = 1 := by
      have h1 := hpow m
      rw [hHpow y hy, mul_one, one_mul] at h1
      have h2 : c ^ m * x = 1 * x := by rw [one_mul]; exact h1.symm
      exact mul_right_cancel h2
    have hc1 : c = 1 := by
      have h1 : orderOf c ∣ Nat.card Z := Subgroup.orderOf_dvd_natCard Z hcZ
      have h2 : orderOf c ∣ m := orderOf_dvd_of_pow_eq_one hcm
      exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcopZ h1 h2)
    rw [hc1] at hyx
    simpa using hyx
  have hHN : ∀ g ∈ Subgroup.centralizer ({x} : Set G), ∀ y ∈ H, g * y * g⁻¹ ∈ H := by
    intro g hg y hy
    have hgx : g * x = x * g := Subgroup.mem_centralizer_singleton_iff.1 hg
    have hπg : π g ∈ Subgroup.centralizer ({π x} : Set P) := by
      rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hgx]
    have hπy : π y ∈ N := hHle hy
    refine hmemH _ ?_ ?_
    · have := hNn (π g) hπg (π y) hπy
      simpa [hNt, Subgroup.mem_comap] using this
    · rw [conj_pow, hHpow y hy]
      simp
  have hHbot : H = ⊥ :=
    hx H (fun y hy => Subgroup.mem_centralizer_singleton_iff.2 (hHcent y hy)) hHN
      (by rw [hHcard]; exact hNc)
  have hm1 : m = 1 := by
    rw [← hHcard, hHbot]
    exact Subgroup.card_bot
  exact Subgroup.card_eq_one.1 hm1

theorem noNormalPPrime_centralizer_of_equiv (e : G ≃* P) {p : ℕ} (x : G)
    (hx : NoNormalPPrime p (Subgroup.centralizer ({e x} : Set P))) :
    NoNormalPPrime p (Subgroup.centralizer ({x} : Set G)) := by
  have hmap : (Subgroup.centralizer ({x} : Set G)).map e.toMonoidHom =
      Subgroup.centralizer ({e x} : Set P) := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hz' : z * x = x * z := Subgroup.mem_centralizer_singleton_iff.1 hz
      rw [Subgroup.mem_centralizer_singleton_iff]
      show e z * e x = e x * e z
      rw [← map_mul, ← map_mul, hz']
    · intro hy
      refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
      have hy' : y * e x = e x * y := Subgroup.mem_centralizer_singleton_iff.1 hy
      show e.symm y ∈ Subgroup.centralizer ({x} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply e.injective
      rw [map_mul, map_mul, e.apply_symm_apply]
      exact hy'
  rw [← W2.noNormalPPrime_map_iff e.toMonoidHom e.injective, hmap]
  exact hx

end CentralQuotient

section Pow

variable {ℓ f n : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K}

theorem squarefree_minpoly_of_pow_eq_one {m : ℕ} (hm : (m : K) ≠ 0)
    {x : primeFormUnitary h (idGram K n)} (hx : (x : GL (Fin n) K) ^ m = 1) :
    Squarefree (minpoly K ((toLinU h n x : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K))) := by
  have hx' : (x : GL (Fin n) K) ^ m = GeneralLinearGroup.scalar (Fin n) (1 : Kˣ) := by
    rw [hx, map_one]
  have hsep : (X ^ m - C ((1 : Kˣ) : K)).Separable :=
    Polynomial.separable_X_pow_sub_C ((1 : Kˣ) : K) hm (1 : Kˣ).ne_zero
  exact squarefree_minpoly_of_aeval_eq_zero (p := X ^ m - C ((1 : Kˣ) : K)) hsep.squarefree
    (aeval_X_pow_sub_C_eq_zero hx')

theorem exists_eigen_frame_pow {m : ℕ} (hm : (m : K) ≠ 0) (hpq : m ∣ ℓ ^ f + 1)
    {x : gramSU h (idGram K n)} (hx : x ^ m = 1) {ν : K} {v₀ : Fin n → K} (hv₀ : v₀ ≠ 0)
    (hv₀e : ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v₀ = ν • v₀) :
    h.bar ν * ν = 1 ∧ ∃ (m' : ℕ) (u : Fin m' → Fin n → K), 1 ≤ m' ∧ IsOrthonormalFamily h u ∧
      (∀ i, ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ u i = ν • u i) ∧
      (∀ w, ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w = ν • w →
        w ∈ Submodule.span K (Set.range u)) := by
  classical
  have hxu : toUnitary h n x ^ m = 1 := by rw [← map_pow, hx, map_one]
  have hxgl : ((toUnitary h n x : primeFormUnitary h (idGram K n)) : GL (Fin n) K) ^ m = 1 := by
    have := congrArg (fun y : primeFormUnitary h (idGram K n) => (y : GL (Fin n) K)) hxu
    simpa using this
  have H0 : UnitaryPrimaryData h.bar (idForm h n) (toLinU h n (toUnitary h n x)) :=
    ⟨h.bar_bar, idForm_isSymm h n, idForm_separatingLeft h n, toLinU_mem _,
      squarefree_minpoly_of_pow_eq_one hm hxgl⟩
  set xm : Matrix (Fin n) (Fin n) K := ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hxm
  set T : Module.End K (Fin n → K) := ((toLinU h n (toUnitary h n x) :
      LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) with hT
  have hTe : ∀ v, T v = xm *ᵥ v := fun v => rfl
  have hνp : ν ^ m = 1 := eigenvalue_pow_eq_one hxu hv₀ (by rw [hTe]; exact hv₀e)
  have hνb : h.bar ν * ν = 1 := bar_eq_inv_of_pow_eq_one h hpq hνp
  have hHasEig : T.HasEigenvalue ν :=
    Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr (by rw [hTe]; exact hv₀e), hv₀⟩
  have hmem := X_sub_C_mem_primaryFactors hHasEig
  have hWmem : ∀ v, v ∈ primaryComponent T (X - C ν) ↔ xm *ᵥ v = ν • v := fun v => by
    rw [mem_primaryComponent_X_sub_C, hTe]
  have hd1 : 1 ≤ Module.finrank K (primaryComponent T (X - C ν)) :=
    Submodule.one_le_finrank_iff.2 (fun hbot => hv₀ (by
      have : v₀ ∈ primaryComponent T (X - C ν) := (hWmem v₀).2 hv₀e
      rw [hbot] at this
      exact (Submodule.mem_bot K).1 this))
  have hsep := separatingLeft_primaryComponent_selfDual H0 hmem (dualPoly_X_sub_C_self hνb)
  obtain ⟨u, huW, hu⟩ := KCUnitaryLines.exists_orthonormal_family hsep
    (m := Module.finrank K (primaryComponent T (X - C ν))) le_rfl
  refine ⟨hνb, _, u, hd1, hu, fun i => (hWmem (u i)).1 (huW i), fun w hw => ?_⟩
  rw [span_eq_of_orthonormal hu huW rfl]
  exact (hWmem w).2 hw

theorem pow_eq_one_of_eigen_scalar_pow {m : ℕ} (hm0 : m ≠ 0) (hm : (m : K) ≠ 0) {ω : K}
    (hω : IsPrimitiveRoot ω m) {Z : primeFormUnitary h (idGram K n)} (hZ : Z ^ m = 1)
    {M : GL (Fin n) K} {k : ℕ}
    (hM : ∀ ν : K, ∃ c : K, c ^ k = 1 ∧ ∀ v : Fin n → K,
      ((Z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v = ν • v →
        (M : Matrix (Fin n) (Fin n) K) *ᵥ v = c • v) : M ^ k = 1 := by
  classical
  have := h.finite
  have hZgl : (Z : GL (Fin n) K) ^ m = 1 := by
    have := congrArg (fun y : primeFormUnitary h (idGram K n) => (y : GL (Fin n) K)) hZ
    simpa using this
  have H0 : UnitaryPrimaryData h.bar (idForm h n) (toLinU h n Z) :=
    ⟨h.bar_bar, idForm_isSymm h n, idForm_separatingLeft h n, toLinU_mem _,
      squarefree_minpoly_of_pow_eq_one hm hZgl⟩
  set A : Matrix (Fin n) (Fin n) K := (M : Matrix (Fin n) (Fin n) K) with hA
  have hext : Matrix.toLin' (A ^ k) = LinearMap.id := by
    refine ext_primaryComponent H0.squarefree fun a ha v hv => ?_
    obtain ⟨ν, rfl⟩ := exists_eq_X_sub_C_of_mem_primaryFactors hm0 hω hZgl ha
    have hZv : ((Z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v = ν • v :=
      mem_primaryComponent_X_sub_C.1 hv
    obtain ⟨c, hck, hc⟩ := hM ν
    have hMv : A *ᵥ v = c • v := hc v hZv
    have hpow : ∀ j : ℕ, (A ^ j) *ᵥ v = c ^ j • v := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        rw [pow_succ, ← Matrix.mulVec_mulVec, hMv, Matrix.mulVec_smul, ih, smul_smul, pow_succ']
    rw [Matrix.toLin'_apply, LinearMap.id_apply, hpow k, hck, one_smul]
  have hAk : A ^ k = 1 := by
    apply Matrix.toLin'.injective
    rw [hext, Matrix.toLin'_one]
  exact Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hAk)

theorem exists_primitiveRoot_two_pow_add_one (h : UnitaryFieldData 2 f K) :
    ∃ ω : K, IsPrimitiveRoot ω (2 ^ f + 1) := by
  haveI := h.finite
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  have hcard : Nat.card Kˣ = (2 ^ f + 1) * (2 ^ f - 1) := by
    rw [Nat.card_units, h.card, two_mul, pow_add]
    have := Nat.mul_self_sub_mul_self_eq (2 ^ f) 1
    simpa using this
  have hdvd : 2 ^ f + 1 ∣ orderOf g := by
    rw [hg, hcard]
    exact Dvd.intro _ rfl
  refine ⟨((g ^ (orderOf g / (2 ^ f + 1)) : Kˣ) : K), ?_⟩
  rw [IsPrimitiveRoot.coe_units_iff]
  have := IsPrimitiveRoot.orderOf (g ^ (orderOf g / (2 ^ f + 1)))
  rwa [orderOf_pow_orderOf_div (orderOf_pos g).ne' hdvd] at this

theorem noNormalPPrime_three_centralizer_gramSU_pow (hE : UnitaryFieldData 2 f K)
    (hf : 2 ^ f = 2 ∨ 2 ^ f = 8) {ω : K} (hω : IsPrimitiveRoot ω (2 ^ f + 1))
    {x : gramSU hE (idGram K n)} (hx : x ^ (2 ^ f + 1) = 1) :
    NoNormalPPrime 3 (Subgroup.centralizer {x}) := by
  classical
  intro N hNC hNn hNc
  rw [eq_bot_iff]
  intro y hy
  rw [Subgroup.mem_bot]
  have hq : 2 ≤ 2 ^ f := by rcases hf with hf | hf <;> omega
  have hm : ((2 ^ f + 1 : ℕ) : K) ≠ 0 := by
    have := hE.charP
    rw [Ne, CharP.cast_eq_zero_iff K 2]
    have h2 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by have := hE.one_le; omega)
    omega
  have hNx : ∀ z ∈ N, z * x = x * z := fun z hz =>
    Subgroup.mem_centralizer_singleton_iff.1 (hNC hz)
  have hNn' : ∀ c : gramSU hE (idGram K n), c * x = x * c → ∀ z ∈ N, c * z * c⁻¹ ∈ N :=
    fun c hc z hz => hNn c (Subgroup.mem_centralizer_singleton_iff.2 hc) z hz
  have hxu : toUnitary hE n x ^ (2 ^ f + 1) = 1 := by rw [← map_pow, hx, map_one]
  have hy1 : (y : GL (Fin n) K) ^ (2 ^ f + 1) = 1 := by
    refine pow_eq_one_of_eigen_scalar_pow (Nat.succ_ne_zero _) hm hω
      (Z := toUnitary hE n x) hxu fun ν => ?_
    by_cases hev : ∃ v : Fin n → K, v ≠ 0 ∧
        ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v = ν • v
    · obtain ⟨v₀, hv₀, hv₀e⟩ := hev
      obtain ⟨hνb, m, u, hm', hu, hxu', hspan⟩ :=
        exists_eigen_frame_pow hm dvd_rfl hx hv₀ hv₀e
      obtain ⟨c, hcb, hc⟩ := eigen_scalar_of_normal hq hm'
        (noNormalPPrime_three_gramSU_two_eight hE hf m) hNc hNx hNn' hνb hu hxu' hspan hy
      refine ⟨c, ?_, hc⟩
      rw [UnitaryFieldData.bar_apply, ← pow_succ] at hcb
      exact hcb
    · refine ⟨1, one_pow _, fun v hv => ?_⟩
      have hv0 : v = 0 := by
        by_contra hv0
        exact hev ⟨v, hv0, hv⟩
      simp [hv0]
  have hyk : y ^ (2 ^ f + 1) = 1 := Subtype.ext (by simpa using hy1)
  have hord1 : orderOf y ∣ 2 ^ f + 1 := orderOf_dvd_of_pow_eq_one hyk
  have hord2 : orderOf y ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hy
  have hcop : Nat.Coprime (2 ^ f + 1) (Nat.card N) := by
    rcases hf with hf | hf <;> rw [hf]
    · simpa using hNc
    · simpa using Nat.Coprime.pow_left 2 hNc
  exact orderOf_eq_one_iff.1 ((hcop.coprime_dvd_left hord1).eq_one_of_dvd hord2)

theorem exists_orthonormal_eigenbasis_pow {m : ℕ} [NeZero m] {ζ : K} (hζ : IsPrimitiveRoot ζ m)
    (hpq : m ∣ ℓ ^ f + 1) {X : primeFormUnitary h (idGram K n)} (hX : X ^ m = 1) :
    ∃ b : Fin n → Fin n → K, IsOrthonormalFamily h b ∧ ∀ i, ∃ μ : K,
      ((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ b i = μ • b i := by
  classical
  have := h.finite
  set T : Module.End K (Fin n → K) := ((toLinU h n X :
      LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) with hT
  have hpow : T ^ m = 1 := by
    have h1 : (toLinU h n X) ^ m = 1 := by rw [← map_pow, hX, map_one]
    have h2 := congrArg (fun g : LinearMap.GeneralLinearGroup K (Fin n → K) =>
      (g : Module.End K (Fin n → K))) h1
    simpa [Units.val_pow_eq_pow_val] using h2
  have hiso : ∀ v w, idForm h n (T v) (T w) = idForm h n v w := fun v w => toLinU_mem X v w
  obtain ⟨b, μ, hbμ, hbo⟩ := KCUnitaryPlane.exists_orthonormal_common_eigenbasis h hζ hpq
    (idForm_isSymm h n) (idForm_separatingLeft h n) (ι := Unit) (fun _ => T)
    (fun _ _ => Commute.refl _) (fun _ => hpow) (fun _ v w => hiso v w)
  refine ⟨b.reindex (finCongr (Module.finrank_fin_fun K)), fun i j => ?_, fun i => ?_⟩
  · rw [Module.Basis.reindex_apply, Module.Basis.reindex_apply, hbo]
    simp
  · rw [Module.Basis.reindex_apply]
    exact ⟨μ () _, hbμ () _⟩

theorem trace_torusMat {b₁ b₂ : Fin n → K} (hb : IsONPair h b₁ b₂) (c : K) :
    Matrix.trace (torusMat h b₁ b₂ c) = (n : K) + (c - 1) + (c⁻¹ - 1) := by
  have hP : ∀ b : Fin n → K, idForm h n b b = 1 → Matrix.trace (projMat h b) = 1 := by
    intro b hb1
    rw [projMat, Matrix.trace_vecMulVec, dotProduct_comm, ← idForm_eq_dotProduct h]
    exact hb1
  unfold torusMat
  rw [Matrix.trace_add, Matrix.trace_add, Matrix.trace_one, Matrix.trace_smul, Matrix.trace_smul,
    hP _ hb.self₁, hP _ hb.self₂, Fintype.card_fin]
  simp

end Pow

section Torus

variable {K : Type} [Field K]

theorem eq_one_of_trace_twist [CharP K 2] {c lam : K} (hc9 : c ^ 9 = 1) (hc1 : c ≠ 1)
    (φ : K ≃+* K) (hlam6 : lam ^ 6 = 1) (htr : c + c⁻¹ = lam * φ (c + c⁻¹)) : lam = 1 := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc9
  have hu8 : (c + c⁻¹) ^ 8 = c + c⁻¹ := by
    have h1 : (c + c⁻¹) ^ 2 ^ 3 = c ^ 2 ^ 3 + c⁻¹ ^ 2 ^ 3 := add_pow_char_pow c c⁻¹ 2 3
    have h2 : c ^ 8 = c⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      calc c ^ 8 * c = c ^ 9 := by ring
        _ = 1 := hc9
    have h3 : c⁻¹ ^ 8 = c := by rw [inv_pow, h2, inv_inv]
    calc (c + c⁻¹) ^ 8 = (c + c⁻¹) ^ 2 ^ 3 := by norm_num
      _ = c ^ 2 ^ 3 + c⁻¹ ^ 2 ^ 3 := h1
      _ = c ^ 8 + c⁻¹ ^ 8 := by norm_num
      _ = c⁻¹ + c := by rw [h2, h3]
      _ = c + c⁻¹ := add_comm _ _
  have hu0 : c + c⁻¹ ≠ 0 := by
    intro h0
    apply hc1
    have h1 : (c + 1) ^ 2 = 0 := by
      have : c * (c + c⁻¹) = (c + 1) ^ 2 := by
        field_simp
        have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
        linear_combination (-c) * h2
      rw [← this, h0, mul_zero]
    have h2 : c + 1 = 0 := pow_eq_zero_iff (two_ne_zero) |>.1 h1
    have h3 : (1 : K) = -1 := by
      have : (2 : K) = 0 := CharP.cast_eq_zero K 2
      linear_combination this
    calc c = -1 := eq_neg_of_add_eq_zero_left h2
      _ = 1 := h3.symm
  set u := c + c⁻¹ with hu
  have hφu0 : φ u ≠ 0 := fun h0 => hu0 (φ.injective (by rw [h0, map_zero]))
  have hφu8 : φ u ^ 8 = φ u := by rw [← map_pow, hu8]
  have hlam0 : lam ≠ 0 := by
    rintro rfl
    simp at hlam6
  have h1 : lam ^ 8 * φ u = lam * φ u := by
    calc lam ^ 8 * φ u = lam ^ 8 * φ u ^ 8 := by rw [hφu8]
      _ = (lam * φ u) ^ 8 := by rw [mul_pow]
      _ = u ^ 8 := by rw [← htr]
      _ = u := hu8
      _ = lam * φ u := htr
  have h2 : lam ^ 8 = lam := mul_right_cancel₀ hφu0 h1
  have h3 : lam ^ 7 = 1 := by
    have : lam * lam ^ 7 = lam * 1 := by
      calc lam * lam ^ 7 = lam ^ 8 := by ring
        _ = lam := h2
        _ = lam * 1 := (mul_one _).symm
    exact mul_left_cancel₀ hlam0 this
  have h4 : lam ^ 7 = lam := by
    calc lam ^ 7 = lam * lam ^ 6 := by ring
      _ = lam := by rw [hlam6, mul_one]
  exact h4.symm.trans h3

end Torus

section U6Aux

variable {K0 : Type} [Field K0]

theorem pow_nine_of_proj_pow_three (h : UnitaryFieldData 2 3 K0) {g : StatedSU 6 (2 ^ 3) K0}
    (hg : (projH (StatedSU 6 (2 ^ 3) K0) g) ^ 3 = 1) : g ^ 9 = 1 := by
  classical
  haveI := h.finite
  have hker : (projH (StatedSU 6 (2 ^ 3) K0)).ker = unitaryScalars h 6 :=
    (QuotientGroup.ker_mk' _).trans (unitaryScalars_eq h (n := 6) (by norm_num)).symm
  have hcard : Nat.card (unitaryScalars h 6) = 3 := by
    rw [card_unitaryScalars h (by norm_num)]
    norm_num
  have h1 : projH (StatedSU 6 (2 ^ 3) K0) (g ^ 3) = 1 := by rw [map_pow]; exact hg
  have h2 : g ^ 3 ∈ unitaryScalars h 6 := by rw [← hker]; exact h1
  have h3 : (⟨g ^ 3, h2⟩ : unitaryScalars h 6) ^ 3 = 1 := by
    have := pow_card_eq_one' (G := unitaryScalars h 6) (x := ⟨g ^ 3, h2⟩)
    rwa [hcard] at this
  have h4 := congrArg (fun a : unitaryScalars h 6 => (a : StatedSU 6 (2 ^ 3) K0)) h3
  simpa [← pow_mul] using h4

theorem torus_commute_of_fixed (h : UnitaryFieldData 2 3 K0) {b₁ b₂ : Fin 6 → K0}
    (hb : IsONPair h b₁ b₂) (A : uU h 6) (φ : K0 ≃+* K0) {c : K0ˣ} (hc : h.norm (c : K0) = 1)
    {T : StatedSU 6 (2 ^ 3) K0}
    (hT : ((T : GL (Fin 6) K0) : Matrix (Fin 6) (Fin 6) K0) = torusMat h b₁ b₂ c)
    (hfix : (uConjAut h (by norm_num : 1 ≤ 6) A * uFieldAut h (by norm_num : 1 ≤ 6) φ)
      (projH _ T) = projH _ T) :
    ((A : GL (Fin 6) K0) : Matrix (Fin 6) (Fin 6) K0) * (torusMat h b₁ b₂ c).map φ =
      torusMat h b₁ b₂ c * ((A : GL (Fin 6) K0) : Matrix (Fin 6) (Fin 6) K0) := by
  haveI := h.finite
  haveI := h.charP
  by_cases hc1 : (c : K0) = 1
  · have h1 : torusMat h b₁ b₂ c = 1 := by rw [hc1]; exact torusMat_one h b₁ b₂
    rw [h1]
    simp
  · rw [uLift_proj] at hfix
    have h2 : (uLift h A φ T)⁻¹ * T ∈ unitaryScalars h 6 := by
      rw [unitaryScalars_eq h (n := 6) (by norm_num)]
      exact QuotientGroup.eq.1 hfix
    obtain ⟨lam, -, hlam6, hlam⟩ := h2
    set Tm : Matrix (Fin 6) (Fin 6) K0 := torusMat h b₁ b₂ c with hTm
    set Am : Matrix (Fin 6) (Fin 6) K0 := ((A : GL (Fin 6) K0) : Matrix (Fin 6) (Fin 6) K0)
      with hAm
    set Ai : Matrix (Fin 6) (Fin 6) K0 :=
      (((A : GL (Fin 6) K0)⁻¹ : GL (Fin 6) K0) : Matrix (Fin 6) (Fin 6) K0) with hAi
    have hAiA : Ai * Am = 1 := by
      rw [hAi, hAm, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hMeq : (((uLift h A φ T : StatedSU 6 (2 ^ 3) K0) : GL (Fin 6) K0) :
        Matrix (Fin 6) (Fin 6) K0) = Am * Tm.map φ * Ai := by
      rw [coe_uLift, hT]
    have hscal : ((GeneralLinearGroup.scalar (Fin 6) lam : GL (Fin 6) K0) :
        Matrix (Fin 6) (Fin 6) K0) = (lam : K0) • (1 : Matrix (Fin 6) (Fin 6) K0) := by
      rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
    have hTU : Tm = (lam : K0) • (Am * Tm.map φ * Ai) := by
      have h1 : (T : GL (Fin 6) K0) =
          ((uLift h A φ T : StatedSU 6 (2 ^ 3) K0) : GL (Fin 6) K0) *
            GeneralLinearGroup.scalar (Fin 6) lam := by
        have h3 := hlam
        simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h3
        calc (T : GL (Fin 6) K0)
            = ((uLift h A φ T : StatedSU 6 (2 ^ 3) K0) : GL (Fin 6) K0) *
              (((uLift h A φ T : StatedSU 6 (2 ^ 3) K0) : GL (Fin 6) K0)⁻¹ *
                (T : GL (Fin 6) K0)) := by group
          _ = _ := by rw [h3]
      have h2 := congrArg (fun g : GL (Fin 6) K0 => (g : Matrix (Fin 6) (Fin 6) K0)) h1
      simp only [Units.val_mul] at h2
      rw [hT, hMeq, hscal, Matrix.mul_smul, Matrix.mul_one] at h2
      exact h2
    have hc9 : (c : K0) ^ 9 = 1 := by
      have := hc
      rw [h.norm_eq_pow] at this
      simpa using this
    have htrM : Matrix.trace (Am * Tm.map φ * Ai) = φ (Matrix.trace Tm) := by
      rw [hAm, hAi, Matrix.trace_units_conj (A : GL (Fin 6) K0) (Tm.map φ),
        AddMonoidHom.map_trace φ Tm]
    have hu : Matrix.trace Tm = (c : K0) + (c : K0)⁻¹ := by
      rw [hTm, trace_torusMat hb]
      have h6 : ((6 : ℕ) : K0) = 0 := by
        rw [CharP.cast_eq_zero_iff K0 2]
        norm_num
      have h2 : (2 : K0) = 0 := CharP.cast_eq_zero K0 2
      rw [h6]
      linear_combination (-1 : K0) * h2
    have htr : (c : K0) + (c : K0)⁻¹ = (lam : K0) * φ ((c : K0) + (c : K0)⁻¹) := by
      have h1 := congrArg Matrix.trace hTU
      rw [Matrix.trace_smul, htrM, hu, smul_eq_mul] at h1
      exact h1
    have hlam6' : (lam : K0) ^ 6 = 1 := by
      have := congrArg (fun u : K0ˣ => (u : K0)) hlam6
      simpa using this
    have hlam1 : (lam : K0) = 1 := eq_one_of_trace_twist hc9 hc1 φ hlam6' htr
    rw [hlam1, one_smul] at hTU
    calc Am * Tm.map φ = (Am * Tm.map φ * Ai) * Am := by
          rw [Matrix.mul_assoc _ Ai Am, hAiA, Matrix.mul_one]
      _ = Tm * Am := by rw [← hTU]

theorem uConjAut_mem_innSub_of_sq (h : UnitaryFieldData 2 3 K0) (A : uU h 6)
    (hA : uConjAut h (by norm_num : 1 ≤ 6) A ^ 2 = 1) :
    uConjAut h (by norm_num : 1 ≤ 6) A ∈ innSub (StatedProj (StatedSU 6 (2 ^ 3) K0)) := by
  classical
  haveI := h.finite
  set e := uTransport h (by norm_num : 1 ≤ 6) with he
  set x : MulAut (primeFormP h ((1 : GL (Fin 6) K0) : Matrix (Fin 6) (Fin 6) K0)) :=
    primeFormConjHom h ((1 : GL (Fin 6) K0) : Matrix (Fin 6) (Fin 6) K0) A with hx
  have hxe : MulAut.congr e (uConjAut h (by norm_num : 1 ≤ 6) A) = x :=
    (MulAut.congr e).apply_symm_apply x
  have hx2 : x ^ 2 = 1 := by
    rw [← hxe, ← map_pow, hA, map_one]
  have hxD : x ∈ primeFormD h ((1 : GL (Fin 6) K0) : Matrix (Fin 6) (Fin 6) K0) := ⟨A, rfl⟩
  have hxinn := mem_inner_of_pow_eq_one_unitary h (1 : GL (Fin 6) K0) Nat.prime_two
    (by norm_num) hxD hx2
  have hxinn' : x ∈ (CFSG.ComponentClassification.OuterAutomorphisms.inner
      (StatedProj (StatedSU 6 (2 ^ 3) K0))).map (MulAut.congr e).toMonoidHom := by
    rw [CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr e]
    exact hxinn
  obtain ⟨y, hy, hyx⟩ := hxinn'
  have hyA : y = uConjAut h (by norm_num : 1 ≤ 6) A :=
    (MulAut.congr e).injective (hyx.trans hxe.symm)
  rw [← hyA]
  exact hy

end U6Aux

end U6LocalAux

section U6

variable {K0 : Type} [Field K0]

open U6LocalAux

theorem u6_outer_sq_eq_one (h : UnitaryFieldData 2 3 K0)
    (y : CFSG.ComponentClassification.OuterAutomorphisms.Outer
      (StatedProj (StatedSU 6 (2 ^ 3) K0))) (hy : Nat.Coprime 3 (orderOf y)) : y ^ 2 = 1 := by
  have hcard := (unitary_full_diagonal_outer_order h (n := 6) (by norm_num) (by norm_num)).2.2.2.1
  have e := CFSG.ComponentClassification.OuterAutomorphisms.equivalence
    (uTransport h (n := 6) (by norm_num))
  have hcard' : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
      (StatedProj (StatedSU 6 (2 ^ 3) K0))) = 18 := by
    rw [Nat.card_congr e.toEquiv, hcard]
    norm_num
  have hdvd : orderOf y ∣ 2 * 9 := by
    have := orderOf_dvd_natCard y
    rw [hcard'] at this
    simpa using this
  have h2 : orderOf y ∣ 2 :=
    Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.pow_right 2 hy.symm) (by simpa using hdvd)
  exact orderOf_dvd_iff_pow_eq_one.1 h2

theorem u6_core_centralizer_eq_bot (h : UnitaryFieldData 2 3 K0)
    {s : StatedProj (StatedSU 6 (2 ^ 3) K0)} (hs3 : s ^ 3 = 1) (hs1 : s ≠ 1) :
    GLAPPrimeCoreOf 3 (Subgroup.centralizer ({s} : Set (StatedProj (StatedSU 6 (2 ^ 3) K0)))) =
      ⊥ := by
  classical
  haveI := h.finite
  clear hs1
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective s
  set π : StatedSU 6 (2 ^ 3) K0 →* StatedProj (StatedSU 6 (2 ^ 3) K0) := projH _ with hπ
  have hker : π.ker = unitaryScalars h 6 :=
    (QuotientGroup.ker_mk' _).trans (unitaryScalars_eq h (n := 6) (by norm_num)).symm
  have hcard : Nat.card (unitaryScalars h 6) = 3 := by
    rw [card_unitaryScalars h (by norm_num)]
    norm_num
  have hg9 : g ^ 9 = 1 := pow_nine_of_proj_pow_three h hs3
  obtain ⟨ω, hω⟩ := exists_primitiveRoot_two_pow_add_one h
  let e : StatedSU 6 (2 ^ 3) K0 ≃* gramSU h (idGram K0 6) :=
    MulEquiv.subgroupCongr (statedSU_eq_gramSU h (n := 6))
  have hxe : (e g) ^ (2 ^ 3 + 1) = 1 := by
    rw [← map_pow]
    have : g ^ (2 ^ 3 + 1) = 1 := hg9
    rw [this, map_one]
  have hN : NoNormalPPrime 3 (Subgroup.centralizer ({g} : Set (StatedSU 6 (2 ^ 3) K0))) :=
    noNormalPPrime_centralizer_of_equiv e g
      (noNormalPPrime_three_centralizer_gramSU_pow h (by right; norm_num) hω hxe)
  have hN' := noNormalPPrime_centralizer_map π (QuotientGroup.mk'_surjective _)
    (by rw [hker]; exact unitaryScalars_le_center h 6) ⟨1, by rw [hker, hcard]; norm_num⟩ hN
  exact W2.core_eq_bot_of_noNormalPPrime Nat.prime_three hN'

theorem u6_exists_moved_of_outer (h : UnitaryFieldData 2 3 K0)
    {s : StatedProj (StatedSU 6 (2 ^ 3) K0)} (hs3 : s ^ 3 = 1) (hs1 : s ≠ 1)
    {τ : MulAut (StatedProj (StatedSU 6 (2 ^ 3) K0))} (hτ : τ ^ 2 = 1)
    (hτi : τ ∉ innSub (StatedProj (StatedSU 6 (2 ^ 3) K0))) :
    ∃ t : StatedProj (StatedSU 6 (2 ^ 3) K0), s * t = t * s ∧ τ t ≠ t := by
  classical
  haveI := h.finite
  clear hs1
  by_contra hno
  push Not at hno
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective s
  have hg9 : g ^ (2 ^ 3 + 1) = 1 := pow_nine_of_proj_pow_three h hs3
  obtain ⟨ω, hω⟩ := exists_primitiveRoot_two_pow_add_one h
  haveI : NeZero (2 ^ 3 + 1) := ⟨by norm_num⟩
  let X : primeFormUnitary h (idGram K0 6) := ⟨(g : GL (Fin 6) K0), statedSU_le_uU h g.2⟩
  have hX : X ^ (2 ^ 3 + 1) = 1 := by
    apply Subtype.ext
    have := congrArg (fun a : StatedSU 6 (2 ^ 3) K0 => (a : GL (Fin 6) K0)) hg9
    simpa using this
  obtain ⟨b, hb, hbe⟩ := exists_orthonormal_eigenbasis_pow hω (dvd_refl _) hX
  obtain ⟨A, φ, hτ'⟩ := exists_uConjAut_mul_uFieldAut h (by norm_num : 3 ≤ 6) (by norm_num) τ
  have key : ∀ i j : Fin 6, i ≠ j → ∀ c : K0ˣ, h.norm (c : K0) = 1 →
      ((A : GL (Fin 6) K0) : Matrix (Fin 6) (Fin 6) K0) * (torusMat h (b i) (b j) c).map φ =
        torusMat h (b i) (b j) c * ((A : GL (Fin 6) K0) : Matrix (Fin 6) (Fin 6) K0) := by
    intro i j hij c hc
    have hp := hb.pair hij
    obtain ⟨μi, hμi⟩ := hbe i
    obtain ⟨μj, hμj⟩ := hbe j
    let Tsu : StatedSU 6 (2 ^ 3) K0 := ⟨(torusUnitary h hp c hc : GL (Fin 6) K0), by
      rw [statedSU_eq_gramSU h (n := 6)]
      exact (mem_gramSU_iff_unitary h).2 ⟨(torusUnitary h hp c hc).2, det_torusUnitary h hp c hc⟩⟩
    have hTX : g * Tsu = Tsu * g :=
      Subtype.ext (Units.ext (torusMat_comm_of_eigen (X := X) hp hμi hμj c))
    have hcomm : projH (StatedSU 6 (2 ^ 3) K0) g * projH (StatedSU 6 (2 ^ 3) K0) Tsu =
        projH (StatedSU 6 (2 ^ 3) K0) Tsu * projH (StatedSU 6 (2 ^ 3) K0) g := by
      rw [← map_mul, ← map_mul, hTX]
    have hfix := hno _ hcomm
    rw [hτ'] at hfix
    exact torus_commute_of_fixed h hp A φ hc (T := Tsu) rfl hfix
  have h01 : (⟨0, by norm_num⟩ : Fin 6) ≠ ⟨1, by norm_num⟩ := by simp [Fin.ext_iff]
  have h02 : (⟨0, by norm_num⟩ : Fin 6) ≠ ⟨2, by norm_num⟩ := by simp [Fin.ext_iff]
  have h12 : (⟨1, by norm_num⟩ : Fin 6) ≠ ⟨2, by norm_num⟩ := by simp [Fin.ext_iff]
  have hφ : φ = RingEquiv.refl K0 :=
    tau_eq_one_of_torus h (Units.isUnit (A : GL (Fin 6) K0)) (hb.pair h01) (hb.pair h02)
      (hb.linearIndependent_triple h01 h02 h12) (key _ _ h01) (key _ _ h02)
  have hτA : τ = uConjAut h (by norm_num : 1 ≤ 6) A := by
    rw [hτ']
    have : φ = 1 := hφ
    rw [this, map_one, mul_one]
  rw [hτA] at hτ hτi
  exact hτi (uConjAut_mem_innSub_of_sq h A hτ)

theorem u6_fieldCoreAt (h : UnitaryFieldData 2 3 K0) {σ : K0 ≃+* K0} (hσ : orderOf σ = 3)
    {φ : MulAut (StatedProj (StatedSU 6 (2 ^ 3) K0))}
    (hφ : ∃ M : uU h 6, (uConjAut h (by norm_num) M)⁻¹ * φ * uConjAut h (by norm_num) M =
      uFieldAut h (by norm_num) σ) : FieldCoreAt 3 φ := by
  obtain ⟨M, hM⟩ := hφ
  have hfin := h.finite
  have hfc : FieldCoreAt 3 (primeFormFieldHom h (isPrimeFormGram_one (n := 6)) σ) :=
    fieldCoreAt_fieldHom_of_subfield h Nat.prime_three (by norm_num) hσ (by norm_num)
      (by norm_num) (fun ⟨h1, _⟩ => by omega)
      (dvd_card_range_of_dvd_q h Nat.prime_three (by norm_num) hσ (by norm_num) (by norm_num))
  have hfc' : FieldCoreAt 3 (uFieldAut h (by norm_num : 1 ≤ 6) σ) :=
    FieldCoreAt.congr hfc (uTransport h (by norm_num : 1 ≤ 6)).symm
  exact fieldCoreAt_of_conj hfc' (uConjAut h (by norm_num : 1 ≤ 6) M)⁻¹ (by rw [inv_inv]; exact hM)

theorem u6_innerOneBalanceThree (h : UnitaryFieldData 2 3 K0) :
    InnerOneBalanceThree (StatedProj (StatedSU 6 (2 ^ 3) K0)) := by
  classical
  haveI := h.finite
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcen : Subgroup.center (StatedProj (StatedSU 6 (2 ^ 3) K0)) = ⊥ :=
    ka_center_bot_pu (p := 2) (f := 3) (by rw [h.card]; norm_num) (by norm_num) (by norm_num)
  have hinj : Function.Injective (MulAut.conj : StatedProj (StatedSU 6 (2 ^ 3) K0) →*
      MulAut (StatedProj (StatedSU 6 (2 ^ 3) K0))) := ka_conj_inj_of_center_bot hcen
  intro d hd hd3 hd1 H hH
  obtain ⟨s, rfl⟩ := hd
  have hs3 : s ^ 3 = 1 := by
    apply hinj
    rw [map_pow, map_one]
    exact hd3
  have hs1 : s ≠ 1 := by
    rintro rfl
    exact hd1 (map_one _)
  refine F4LocalOneAux.oneBalanced_at_of_good Nat.prime_three hcen
    (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner
      (StatedProj (StatedSU 6 (2 ^ 3) K0)))) (fun α => QuotientGroup.eq_one_iff α)
    (fun y hy => u6_outer_sq_eq_one h y hy) (u6_core_centralizer_eq_bot h hs3 hs1)
    (fun τ hτ hτi => u6_exists_moved_of_outer h hs3 hs1 hτ hτi) H hH

end U6

end KSFourU

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

end
