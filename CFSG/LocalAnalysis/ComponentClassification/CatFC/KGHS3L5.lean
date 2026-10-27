module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.KGHS3EigBase
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.KGHS3BaseChange
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic

public section

namespace CFSG.ComponentClassification.CatFC.KGHS3

open Module

theorem five_ne_zero_of_ringChar_ne {E : Type*} [Field E] (hE : ringChar E ≠ 5) :
    ((5 : ℕ) : E) ≠ 0 := by
  intro h
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp ((ringChar.spec (R := E) 5).mp h) with
    h1 | h1
  · have h0 : ((1 : ℕ) : E) = 0 := (ringChar.spec (R := E) 1).mpr (by simp [h1])
    exact one_ne_zero (by exact_mod_cast h0)
  · exact hE h1

def mulThreeFin5 (k : Fin 5) : Fin 5 := ⟨(k : ℕ) * 3 % 5, Nat.mod_lt _ (by norm_num)⟩

theorem pow_eq_pow_mod_five {E : Type*} [Field E] {ζ : E} (hζ : IsPrimitiveRoot ζ 5) (n : ℕ) :
    ζ ^ n = ζ ^ (n % 5) := by
  conv_lhs => rw [← Nat.mod_add_div n 5, pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]

theorem five_dvd_finrank_eigenspace {E V : Type*} [Field E] [AddCommGroup V] [Module E V]
    [FiniteDimensional E V] {x y z w : Module.End E V} {ζ : E} (hζ : IsPrimitiveRoot ζ 5)
    (hx : IsUnit x) (hy : IsUnit y) (hxz : x * z = z * x) (hyz : y * z = z * y)
    (hwz : w * z = z * w) (hw2 : w ^ 2 = 1) (hc : x * y = z * w * (y * x)) :
    5 ∣ finrank E (z.eigenspace ζ) := by
  have hxW : ∀ v ∈ z.eigenspace ζ, x v ∈ z.eigenspace ζ := fun v hv =>
    map_mem_eigenspace_of_mul_eq hxz hv
  have hyW : ∀ v ∈ z.eigenspace ζ, y v ∈ z.eigenspace ζ := fun v hv =>
    map_mem_eigenspace_of_mul_eq hyz hv
  have hwW : ∀ v ∈ z.eigenspace ζ, w v ∈ z.eigenspace ζ := fun v hv =>
    map_mem_eigenspace_of_mul_eq hwz hv
  have hxI : Function.Injective x :=
    LinearMap.ker_eq_bot.mp ((LinearMap.isUnit_iff_ker_eq_bot x).mp hx)
  have hyI : Function.Injective y :=
    LinearMap.ker_eq_bot.mp ((LinearMap.isUnit_iff_ker_eq_bot y).mp hy)
  have hxs : IsUnit (LinearMap.restrict x hxW) :=
    (LinearMap.isUnit_iff_ker_eq_bot _).mpr
      (LinearMap.ker_eq_bot.mpr fun a b hab => Subtype.ext (hxI (congrArg Subtype.val hab)))
  have hys : IsUnit (LinearMap.restrict y hyW) :=
    (LinearMap.isUnit_iff_ker_eq_bot _).mpr
      (LinearMap.ker_eq_bot.mpr fun a b hab => Subtype.ext (hyI (congrArg Subtype.val hab)))
  have hww : ∀ u : V, w (w u) = u := fun u => by
    have h : (w ^ 2) u = u := by rw [hw2, Module.End.one_apply]
    rwa [sq, Module.End.mul_apply] at h
  have hws : LinearMap.restrict w hwW * LinearMap.restrict w hwW = 1 := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    simp [Module.End.mul_apply, hww]
  have hcomm : LinearMap.restrict x hxW * LinearMap.restrict y hyW =
      (ζ • LinearMap.restrict w hwW) * (LinearMap.restrict y hyW * LinearMap.restrict x hxW) := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    have hm : w (y (x v)) ∈ z.eigenspace ζ := hwW _ (hyW _ (hxW _ v.2))
    have hz' : z (w (y (x v))) = ζ • w (y (x v)) := Module.End.mem_eigenspace_iff.mp hm
    have hc' : x (y v) = z (w (y (x v))) := by
      have h := congrArg (fun f : Module.End E V => f (v : V)) hc
      simpa only [Module.End.mul_apply] using h
    simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.coe_restrict_apply,
      Submodule.coe_smul]
    exact hc'.trans hz'
  have hpow := pow_finrank_eq_one_of_commutator hxs hys hws hcomm
  have h5 : 5 ∣ 2 * finrank E (z.eigenspace ζ) := (hζ.pow_eq_one_iff_dvd _).mp hpow
  omega

theorem twenty_le_finrank_of_heis5 {E V : Type*} [Field E] [IsAlgClosed E] [AddCommGroup V]
    [Module E V] [FiniteDimensional E V] (hE : ringChar E ≠ 5) (x y z g w : Module.End E V)
    (hz : z ^ 5 = 1) (hz1 : z ≠ 1) (hx : IsUnit x) (hy : IsUnit y) (hg : IsUnit g)
    (hxz : x * z = z * x) (hyz : y * z = z * y) (hgz : g * z = z ^ 2 * g)
    (hwx : w * x = x * w) (hwy : w * y = y * w) (hwz : w * z = z * w) (hw2 : w ^ 2 = 1)
    (hc : x * y = z * w * (y * x)) : 20 ≤ finrank E V := by
  have h5 : ((5 : ℕ) : E) ≠ 0 := five_ne_zero_of_ringChar_ne hE
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_of_isAlgClosed h5
  have hgI : Function.Injective g :=
    LinearMap.ker_eq_bot.mp ((LinearMap.isUnit_iff_ker_eq_bot g).mp hg)
  have hmap : ∀ i : Fin 5, ∀ v ∈ z.eigenspace (ζ ^ (i : ℕ)),
      g v ∈ z.eigenspace (ζ ^ ((mulThreeFin5 i : Fin 5) : ℕ)) := by
    intro i v hv
    have hz3 : (z ^ 2) ^ 3 = z := by
      rw [← pow_mul, show 2 * 3 = 1 + 5 by norm_num, pow_add, hz, pow_one, mul_one]
    have h1 : g v ∈ (z ^ 2).eigenspace (ζ ^ (i : ℕ)) := map_mem_eigenspace_of_mul_eq hgz hv
    have h3 : g v ∈ z.eigenspace ((ζ ^ (i : ℕ)) ^ 3) := mem_eigenspace_of_pow_eq hz3 h1
    have hpm : (ζ ^ (i : ℕ)) ^ 3 = ζ ^ ((mulThreeFin5 i : Fin 5) : ℕ) :=
      calc (ζ ^ (i : ℕ)) ^ 3 = ζ ^ ((i : ℕ) * 3) := (pow_mul ζ (i : ℕ) 3).symm
        _ = ζ ^ ((i : ℕ) * 3 % 5) := pow_eq_pow_mod_five hζ _
        _ = ζ ^ ((mulThreeFin5 i : Fin 5) : ℕ) := rfl
    rw [hpm] at h3
    exact h3
  have hcyc : mulThreeFin5^[4] 1 = 1 := by decide
  have hn : ∀ n : ℕ, finrank E (z.eigenspace (ζ ^ ((mulThreeFin5^[n] 1 : Fin 5) : ℕ))) =
      finrank E (z.eigenspace (ζ ^ ((1 : Fin 5) : ℕ))) := fun n =>
    finrank_iterate_eq_of_cycle (fun k : Fin 5 => z.eigenspace (ζ ^ (k : ℕ))) mulThreeFin5 hgI
      hmap 1 (by norm_num) hcyc n
  have e3 : finrank E (z.eigenspace (ζ ^ 3)) = finrank E (z.eigenspace (ζ ^ 1)) := hn 1
  have e4 : finrank E (z.eigenspace (ζ ^ 4)) = finrank E (z.eigenspace (ζ ^ 1)) := hn 2
  have e2 : finrank E (z.eigenspace (ζ ^ 2)) = finrank E (z.eigenspace (ζ ^ 1)) := hn 3
  have hall : ∀ k : Fin 5, (k : ℕ) ≠ 0 →
      finrank E (z.eigenspace (ζ ^ (k : ℕ))) = finrank E (z.eigenspace (ζ ^ 1)) := by
    intro k hk
    fin_cases k
    · exact (hk rfl).elim
    · rfl
    · exact e2
    · exact e3
    · exact e4
  have hA : 5 ∣ finrank E (z.eigenspace (ζ ^ 1)) := by
    rw [pow_one]
    exact five_dvd_finrank_eigenspace hζ hx hy hxz hyz hwz hw2 hc
  obtain ⟨k, hk0, hkne⟩ := exists_eigenspace_ne_bot_of_ne_one hζ h5 hz hz1
  have hpos : 1 ≤ finrank E (z.eigenspace (ζ ^ (k : ℕ))) :=
    Submodule.one_le_finrank_iff.mpr hkne
  rw [hall k hk0] at hpos
  have hD5 : 5 ≤ finrank E (z.eigenspace (ζ ^ 1)) := Nat.le_of_dvd (by omega) hA
  have hsplit : ∑ k : Fin 5, finrank E (z.eigenspace (ζ ^ (k : ℕ))) =
      finrank E (z.eigenspace (ζ ^ 0)) + finrank E (z.eigenspace (ζ ^ 1)) +
        finrank E (z.eigenspace (ζ ^ 2)) + finrank E (z.eigenspace (ζ ^ 3)) +
        finrank E (z.eigenspace (ζ ^ 4)) :=
    Fin.sum_univ_five _
  have hsum := sum_finrank_eigenspace_pow hζ h5 hz
  omega

theorem twenty_le_card_of_heis5 {F : Type} [Field F] (hF : ringChar F ≠ 5) {ι : Type}
    [Fintype ι] [DecidableEq ι] (x y z g w : Matrix ι ι F) (hz : z ^ 5 = 1) (hz1 : z ≠ 1)
    (hx : IsUnit x) (hy : IsUnit y) (hg : IsUnit g) (hxz : x * z = z * x) (hyz : y * z = z * y)
    (hgz : g * z = z ^ 2 * g) (hwx : w * x = x * w) (hwy : w * y = y * w) (hwz : w * z = z * w)
    (hw2 : w ^ 2 = 1) (hc : x * y = z * w * (y * x)) : 20 ≤ Fintype.card ι := by
  obtain ⟨E, _, _, φ, hinj, hchar⟩ := exists_algClosed_ringHom F ι
  have hE : ringChar E ≠ 5 := by rw [hchar]; exact hF
  have key := twenty_le_finrank_of_heis5 hE (φ x) (φ y) (φ z) (φ g) (φ w)
    (by rw [← map_pow, hz, map_one])
    (fun h => hz1 (hinj (by rw [h, map_one])))
    (RingHom.isUnit_map φ hx) (RingHom.isUnit_map φ hy) (RingHom.isUnit_map φ hg)
    (by simpa only [map_mul] using congrArg φ hxz)
    (by simpa only [map_mul] using congrArg φ hyz)
    (by simpa only [map_mul, map_pow] using congrArg φ hgz)
    (by simpa only [map_mul] using congrArg φ hwx)
    (by simpa only [map_mul] using congrArg φ hwy)
    (by simpa only [map_mul] using congrArg φ hwz)
    (by simpa only [map_pow, map_one] using congrArg φ hw2)
    (by simpa only [map_mul] using congrArg φ hc)
  rwa [Module.finrank_fintype_fun_eq_card] at key

end CFSG.ComponentClassification.CatFC.KGHS3
