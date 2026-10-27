module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrAbs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrStruct
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrQuot
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrPow

public section

namespace CFSG.AGLEmbedding.ParabAutIrr

open CFSG.AGLEmbedding CFSG.AGLEmbedding.ParabPrime
open scoped commutatorElement

section Decomp

variable {G : Type*} [Group G]

theorem exists_torus_mul {J S T : Subgroup G} (hS2 : IsPGroup 2 S) (hSJ : S ≤ J) (hTJ : T ≤ J)
    (hTc : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) (hTodd : ∀ t ∈ T, ∃ m : ℕ, Odd m ∧ t ^ m = 1)
    (hTS : T ≤ Subgroup.normalizer (S : Set G)) (hgen : J ≤ T ⊔ S ⊔ perfectJoin J) :
    ∀ x ∈ J, ∃ t ∈ T, ∃ n ∈ twoCore J, x = t * n := by
  obtain ⟨hEq, -⟩ := borelLike_facts hS2 hSJ hTJ hTc hTodd hTS hgen
  set P := perfectJoin J with hP
  have hJP : J ≤ Subgroup.normalizer (P : Set G) := le_normalizer_perfectJoin J
  have hT' : T ≤ Subgroup.normalizer ((P ⊔ S : Subgroup G) : Set G) := fun t ht =>
    mem_normalizer_sup (hJP (hTJ ht)) (hTS ht)
  intro x hx
  have hEq' : T ⊔ S ⊔ P = T ⊔ (P ⊔ S) := by rw [sup_assoc, sup_comm S P]
  have h1 : x ∈ T ⊔ (P ⊔ S) := by
    rw [← hEq']
    exact hgen hx
  have h2 := Subgroup.coe_mul_of_left_le_normalizer_right T (P ⊔ S) hT'
  rw [← SetLike.mem_coe, h2, Set.mem_mul] at h1
  obtain ⟨t, ht, n, hn, rfl⟩ := h1
  exact ⟨t, ht, n, hEq ▸ hn, rfl⟩

end Decomp

variable {Y : Type} [Group Y] [Finite Y]

theorem noIrr_aut {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hinj : Function.Injective (MulAut.conj : Y →* MulAut Y))
    (hS : ParabStruct Y) (R1 : OutPTwoGen Y p) (R2 : AutScalarTorus Y)
    (S₀ : Sylow 2 Y) {J : Subgroup Y} (hJ : Subgroup.normalizer (S₀ : Set Y) ≤ J)
    (hcyc : PerfectCyclicSylow p J)
    {U Z : Subgroup (MulAut Y)} {y : MulAut Y}
    (hU : IsPGroup p U) (hZ : Z = ⁅U, U⁆) (hirr : IrrAct y U Z) (hrank : NeedsThree U Z)
    (hyU : y ∈ Subgroup.normalizer (U : Set (MulAut Y)))
    (hUJ : U ≤ Subgroup.normalizer
      ((J.map (MulAut.conj : Y →* MulAut Y) : Subgroup (MulAut Y)) : Set (MulAut Y)))
    (hyJ : y ∈ Subgroup.normalizer
      ((J.map (MulAut.conj : Y →* MulAut Y) : Subgroup (MulAut Y)) : Set (MulAut Y)))
    (hyo : ∃ e : ℕ, 0 < e ∧ Nat.Coprime e 6 ∧ y ^ e ∈ inn Y) : False := by
  classical
  set cj : Y →* MulAut Y := MulAut.conj with hcj
  set J' : Subgroup (MulAut Y) := J.map cj with hJ'
  have hSJ : (S₀ : Subgroup Y) ≤ J := fun x hx => hJ (Subgroup.le_normalizer hx)
  obtain ⟨T, hTJ, hTc, hTodd, hTS, hgen⟩ := hS S₀ J hJ
  obtain ⟨hS2', hSJ', hTJ', hTc', hTodd', hTS', hgen'⟩ :=
    borelLike_map cj S₀.isPGroup' hSJ hTJ hTc hTodd hTS hgen
  have hself : ∀ g ∈ inn Y, g ∈ Subgroup.normalizer (J' : Set (MulAut Y)) → g ∈ J' := by
    rintro _ ⟨x, rfl⟩ hx
    have hxJ := iff_of_mem_normalizer_map_conj hinj hx
    have hxn : x ∈ Subgroup.normalizer (J : Set Y) := by
      rw [Subgroup.mem_normalizer_iff]
      exact hxJ
    exact ⟨x, mem_of_mem_normalizer S₀ hSJ hJ hxn, rfl⟩
  have hcyc' : ∀ A : Subgroup (MulAut Y), A ≤ perfectJoin J' → IsPGroup p A → IsCyclic A :=
    fun A hA hAp => isCyclic_of_le_perfectJoin_map cj hinj hcyc hA hAp
  obtain ⟨hEq, hab⟩ := borelLike_facts S₀.isPGroup' hSJ hTJ hTc hTodd hTS hgen
  have hdec := exists_torus_mul S₀.isPGroup' hSJ hTJ hTc hTodd hTS hgen
  have R2' : U ≤ inn Y → U ≤ J' → y ∉ inn Y →
      ∀ u ∈ U, ∃ k : ℕ, y * u * y⁻¹ * (u ^ k)⁻¹ ∈ twoCore J' := by
    intro _ hUJ'' _ u hu
    have hyiff := iff_of_mem_normalizer_map_conj hinj hyJ
    have hyJ_Y : J.map y.toMonoidHom = J := map_aut_eq_of_iff hyiff
    obtain ⟨j, hjJ, hjS⟩ := exists_conj_mul_normalizes S₀ hSJ y hyJ_Y
    set y₀ : MulAut Y := MulAut.conj j * y with hy₀
    have hy₀app : ∀ z, y₀ z = j * y z * j⁻¹ := fun z => rfl
    have hy₀iff : ∀ z, z ∈ J ↔ y₀ z ∈ J := by
      intro z
      rw [hy₀app, hyiff z]
      constructor
      · intro h
        exact J.mul_mem (J.mul_mem hjJ h) (J.inv_mem hjJ)
      · intro h
        have := J.mul_mem (J.mul_mem (J.inv_mem hjJ) h) hjJ
        simpa [mul_assoc] using this
    have hy₀J : J.map y₀.toMonoidHom = J := map_aut_eq_of_iff hy₀iff
    have hy₀e : ∃ e : ℕ, 0 < e ∧ Nat.Coprime e 6 ∧ y₀ ^ e ∈ inn Y := by
      obtain ⟨e, he, he6, hye⟩ := hyo
      exact ⟨e, he, he6, pow_mem_inn_of_mul ⟨j, rfl⟩ hye⟩
    obtain ⟨k, hk⟩ := R2 S₀ y₀ hjS hy₀e
    have hfN : (twoCore J).map y₀.toMonoidHom ≤ twoCore J := map_twoCore_le y₀.toMonoidHom hy₀J.le
    have hkT : ∀ t ∈ T, y₀ t * (t ^ k)⁻¹ ∈ twoCore J := fun t ht => by
      have := hk t (hTS ht)
      rw [hEq]
      exact Subgroup.mem_sup_right this
    have hpowJ := powerMap_of_torus (J := J) (N := twoCore J) (T := T)
      (fun x hx => mem_normalizer_twoCore (Subgroup.le_normalizer hx)) hdec hTJ hy₀J.le hfN hkT
    obtain ⟨x, hxJ, rfl⟩ := hUJ'' hu
    refine ⟨k, ?_⟩
    have hz : y x * (x ^ k)⁻¹ ∈ twoCore J := by
      have h1 := hab j⁻¹ (J.inv_mem hjJ) (y₀ x) ((hy₀iff x).1 hxJ)
      have h2 := hpowJ x hxJ
      have e : y x * (x ^ k)⁻¹ = ⁅j⁻¹, y₀ x⁆ * (y₀ x * (x ^ k)⁻¹) := by
        rw [commutatorElement_def, hy₀app]
        group
      rw [e]
      exact mul_mem h1 h2
    have e1 : y * MulAut.conj x * y⁻¹ * (MulAut.conj x ^ k)⁻¹ =
        MulAut.conj (y x * (x ^ k)⁻¹) := by
      rw [aut_mul_conj_mul_inv, map_mul, map_inv, map_pow]
    rw [show cj x = MulAut.conj x from rfl, e1]
    exact map_twoCore_le cj (le_refl _) ⟨_, hz, rfl⟩
  exact noIrrAction hp2 hU hZ hirr hrank hyU hself hUJ hyJ hS2' hSJ' hTJ' hTc' hTodd' hTS' hgen'
    hcyc' (R1 U hU) R2'

end CFSG.AGLEmbedding.ParabAutIrr
