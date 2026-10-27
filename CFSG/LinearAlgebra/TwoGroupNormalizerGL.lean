module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.GroupTheory.PGroup
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFourteenSixNRank

public section

namespace CFSG.LinearAlgebra.TwoGroupNormalizerGL

open Subgroup Module
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

theorem commute_of_mem_normalizer_GL_of_sq_lt {K : Type} [Field K] [Finite K]
    (h2 : (2 : K) ≠ 0) {d r : ℕ} (hd : 2 ≤ d) (hr : r.Prime) (hdr : d * d < r)
    {P : Subgroup (GL (Fin d) K)} (hP : IsPGroup 2 P) {y : GL (Fin d) K}
    (hy : y ∈ normalizer (P : Set (GL (Fin d) K))) {k : ℕ} (hyk : y ^ r ^ k = 1) :
    ∀ x ∈ P, y * x = x * y := by
  classical
  let K' := AlgebraicClosure K
  let V := Fin d → K'
  have halg : Function.Injective (algebraMap K K') := RingHom.injective (algebraMap K K')
  have h2' : (2 : K') ≠ 0 := by
    intro h0
    apply h2
    apply halg
    rw [map_ofNat, map_zero]
    exact h0
  have hV : finrank K' V ≤ d := by
    change finrank K' (Fin d → K') ≤ d
    rw [Module.finrank_fin_fun K']
  let φ : GL (Fin d) K →* GL (Fin d) K' := Matrix.GeneralLinearGroup.map (algebraMap K K')
  let e : GL (Fin d) K' ≃* (V →ₗ[K'] V)ˣ := Matrix.GeneralLinearGroup.toLin
  let ρ : Representation K' (GL (Fin d) K) V :=
    (Units.coeHom (V →ₗ[K'] V)).comp (e.toMonoidHom.comp φ)
  have hmap : Function.Injective (RingHom.mapMatrix (m := Fin d) (algebraMap K K')) := by
    intro A B h
    ext i j
    refine halg ?_
    have h1 := congrArg (fun M : Matrix (Fin d) (Fin d) K' => M i j) h
    simpa using h1
  have hinjφ : Function.Injective φ := by
    intro A B h
    have h1 : (RingHom.mapMatrix (m := Fin d) (algebraMap K K'))
        (A : Matrix (Fin d) (Fin d) K) =
        (RingHom.mapMatrix (m := Fin d) (algebraMap K K'))
          (B : Matrix (Fin d) (Fin d) K) := congrArg Units.val h
    exact Units.ext (hmap h1)
  have hinjρ : Function.Injective ρ := by
    intro a b hab
    have h1 : (Matrix.GeneralLinearGroup.toLin (n := Fin d) (R := K')) (φ a) =
        (Matrix.GeneralLinearGroup.toLin (n := Fin d) (R := K')) (φ b) :=
      Units.ext hab
    exact hinjφ ((Matrix.GeneralLinearGroup.toLin (n := Fin d) (R := K')).injective h1)
  have hcomm := KFourteenSixN.commute_of_mem_normalizer_of_sq_lt h2' hd hV ρ hP hinjρ.injOn hr
    hdr hy hyk
  intro x hx
  exact hinjρ (congrArg ρ (hcomm x hx))

theorem mem_centralizer_of_isPGroup_two_of_lift {X Γ K : Type} [Group X] [Group Γ] [Field K]
    [Finite K] (h2 : (2 : K) ≠ 0) {d r : ℕ} (hd : 2 ≤ d) (hr : r.Prime) (hdr : d * d < r)
    (ι : Γ →* GL (Fin d) K) (hι : Function.Injective ι) (π : Γ →* X)
    (hπ : Function.Surjective π) (hker : IsPGroup 2 π.ker) {a : X} (ha : a ^ r = 1)
    {Q : Subgroup X} (hQ : IsPGroup 2 Q) (haQ : a ∈ normalizer (Q : Set X)) :
    a ∈ centralizer (Q : Set X) := by
  have hr2 : r ≠ 2 := by
    have h4 : 2 * 2 ≤ d * d := Nat.mul_le_mul hd hd
    omega
  obtain ⟨b, rfl⟩ := hπ a
  obtain ⟨m, hm⟩ := hker ⟨b ^ r, by rw [MonoidHom.mem_ker, map_pow, ha]⟩
  have hbm : (b ^ r) ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  have hyr : ι (b ^ 2 ^ m) ^ r ^ 1 = 1 := by
    rw [pow_one, ← map_pow, ← pow_mul, mul_comm, pow_mul, hbm, map_one]
  have hQt : IsPGroup 2 (Q.comap π) := hQ.comap_of_ker_isPGroup π hker
  have hyQt : b ^ 2 ^ m ∈ normalizer ((Q.comap π : Subgroup Γ) : Set Γ) :=
    le_normalizer_comap π (mem_comap.2 (by rw [map_pow]; exact pow_mem haQ _))
  have hιy : ι (b ^ 2 ^ m) ∈ normalizer (((Q.comap π).map ι : Subgroup _) : Set _) :=
    le_normalizer_map ι (mem_map_of_mem ι hyQt)
  have hcomm := commute_of_mem_normalizer_GL_of_sq_lt h2 hd hr hdr (hQt.map ι) hιy hyr
  have hcent : π b ^ 2 ^ m ∈ centralizer (Q : Set X) := by
    rw [← map_pow, mem_centralizer_iff]
    intro q hq
    obtain ⟨x, rfl⟩ := hπ q
    have h1 := hcomm (ι x) (mem_map_of_mem ι (mem_comap.2 hq))
    have h3 : b ^ 2 ^ m * x = x * b ^ 2 ^ m := hι (by rw [map_mul, map_mul]; exact h1)
    rw [← map_mul, ← map_mul, h3]
  have hcop : (2 ^ m).Coprime (orderOf (π b)) :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one ha)
      (Nat.Coprime.pow_left m ((Nat.coprime_primes Nat.prime_two hr).2 (Ne.symm hr2)))
  obtain ⟨u, hu⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hu]
  exact pow_mem hcent u

end CFSG.LinearAlgebra.TwoGroupNormalizerGL
