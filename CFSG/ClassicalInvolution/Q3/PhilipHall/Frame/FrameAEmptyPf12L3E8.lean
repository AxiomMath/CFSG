module

public import CFSG.ClassicalInvolution.Balance.Basic
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.Open CFSG.ClassicalInvolution.Balance Matrix
open scoped MatrixGroups

abbrev L3Two : Type := Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)

theorem l3Two_centralizer_exp :
    ∀ x y : L3Two, x * x = 1 → x ≠ 1 → x * y = y * x → y ^ 4 = 1 := by
  decide +kernel

theorem isSimpleGroup_l3Two : IsSimpleGroup L3Two := by
  have hP : IsSimpleGroup (ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) :=
    (CFSG.LinearGroups.linear_projective_simple (K := ZMod 2) (by norm_num)
      (Or.inl le_rfl)).2.1
  let e₂ : PSL(3, ZMod 2) ≃* L3Two :=
    (QuotientGroup.quotientMulEquivOfEq
      CFSG.LocalAnalysis.ComponentInitial.center_SL_three_zmod_two_eq_bot).trans
      QuotientGroup.quotientBot
  exact e₂.symm.isSimpleGroup

@[expose] def IsL3E8 (X : Type) [Group X] : Prop :=
  ∃ (E : Subgroup X) (_ : E.Normal), IsElemAbelian 2 E ∧ Nat.card E = 8 ∧
    Nonempty ((X ⧸ E) ≃* L3Two)

section Aux

theorem eq_one_of_odd_of_dvd_two_pow {m k : ℕ} (hm : Odd m) (h : m ∣ 2 ^ k) : m = 1 := by
  obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h
  rcases i with _ | i
  · rfl
  · exfalso
    have : Even (2 ^ (i + 1)) := (Nat.even_pow.mpr ⟨even_two, by omega⟩)
    exact (Nat.not_even_iff_odd.mpr hm) this

variable {X : Type} [Group X] [Finite X]

theorem eq_one_of_odd_of_mem_pGroup {E : Subgroup X} (hE : IsPGroup 2 E) {n : X} (hn : n ∈ E)
    (hodd : Odd (orderOf n)) : n = 1 := by
  obtain ⟨k, hk⟩ := hE ⟨n, hn⟩
  have h1 : orderOf n ∣ 2 ^ k := by
    apply orderOf_dvd_of_pow_eq_one
    simpa using congrArg Subtype.val hk
  exact orderOf_eq_one_iff.mp (eq_one_of_odd_of_dvd_two_pow hodd h1)

end Aux

variable {X : Type} [Group X] [Finite X]

theorem oddCoreIn_centralizer_eq_bot_of_l3e8 (hO : classicalInvolutionOddCore X = ⊥)
    {E : Subgroup X} [hEn : E.Normal] (hE : IsElemAbelian 2 E)
    (e : (X ⧸ E) ≃* L3Two) {c : X} (hc : c * c = 1) :
    oddCoreIn (Subgroup.centralizer ({c} : Set X)) = ⊥ := by
  have hE2 : IsPGroup 2 E := fun g => ⟨1, by simpa using Subtype.ext (hE.2 g g.2)⟩
  set C : Subgroup X := Subgroup.centralizer ({c} : Set X) with hC
  set N : Subgroup X := oddCoreIn C with hN
  have hNodd : Odd (Nat.card N) := odd_card_oddCoreIn C
  have hNC : N ≤ C := oddCoreIn_le C
  have hnodd : ∀ n ∈ N, Odd (orderOf n) := fun n hn => by
    have h1 := Subgroup.orderOf_dvd_natCard N hn
    exact Odd.of_dvd_nat hNodd h1
  have hNE : ∀ n ∈ N, n ∈ E → n = 1 := fun n hn hnE =>
    eq_one_of_odd_of_mem_pGroup hE2 hnE (hnodd n hn)
  let f : X →* L3Two := e.toMonoidHom.comp (QuotientGroup.mk' E)
  have hfker : ∀ x : X, f x = 1 ↔ x ∈ E := fun x => by
    show e (QuotientGroup.mk' E x) = 1 ↔ _
    rw [map_eq_one_iff e e.injective]
    exact QuotientGroup.eq_one_iff x
  rw [eq_bot_iff]
  intro n hn
  rw [Subgroup.mem_bot]
  by_cases hcE : c ∈ E
  ·
    have hcomm : ∀ y ∈ E, y * c = c * y := fun y hy => by
      have := hE.1.1.comm ⟨y, hy⟩ ⟨c, hcE⟩
      simpa using congrArg Subtype.val this
    have hnK : ∀ y ∈ E, y * n = n * y := by
      intro y hy
      have hyC : y ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr (hcomm y hy)
      have h1 : y * n * y⁻¹ ∈ N := conj_mem_oddCoreIn hyC hn
      have h2 : (y * n * y⁻¹) * n⁻¹ ∈ N := N.mul_mem h1 (N.inv_mem hn)
      have h3 : (y * n * y⁻¹) * n⁻¹ ∈ E := by
        have : (y * n * y⁻¹) * n⁻¹ = y * (n * y⁻¹ * n⁻¹) := by group
        rw [this]
        exact E.mul_mem hy (hEn.conj_mem _ (E.inv_mem hy) n)
      have h4 := hNE _ h2 h3
      calc y * n = (y * n * y⁻¹) * y := by group
        _ = n * y := by
          have : y * n * y⁻¹ = n := by
            have := mul_inv_eq_one.mp h4
            exact this
          rw [this]
    set K : Subgroup X := Subgroup.centralizer (E : Set X) with hK
    have hKn : n ∈ K := Subgroup.mem_centralizer_iff.mpr fun y hy => hnK y hy
    have hKnormal : K.Normal := ⟨fun k hk g y hy => by
      have hk' := Subgroup.mem_centralizer_iff.mp hk
      have hy' : g⁻¹ * y * g ∈ E := by
        simpa using hEn.conj_mem y hy g⁻¹
      have := hk' _ hy'
      calc y * (g * k * g⁻¹) = g * ((g⁻¹ * y * g) * k) * g⁻¹ := by group
        _ = g * (k * (g⁻¹ * y * g)) * g⁻¹ := by rw [this]
        _ = (g * k * g⁻¹) * y := by group⟩
    have hEK : E ≤ K := fun y hy => Subgroup.mem_centralizer_iff.mpr fun z hz => by
      have := hE.1.1.comm ⟨z, hz⟩ ⟨y, hy⟩
      simpa using congrArg Subtype.val this
    haveI : IsSimpleGroup L3Two := isSimpleGroup_l3Two
    have hfs : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective E)
    have hKm : (K.map f).Normal := hKnormal.map f hfs
    haveI := hKm
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (K.map f) with h | h
    ·
      have hnE : n ∈ E := by
        have : f n ∈ K.map f := ⟨n, hKn, rfl⟩
        rw [h, Subgroup.mem_bot] at this
        exact (hfker n).mp this
      exact hNE n hn hnE
    ·
      have hKtop : K = ⊤ := by
        rw [eq_top_iff]
        intro x _
        have : f x ∈ K.map f := by rw [h]; exact Subgroup.mem_top _
        obtain ⟨k, hk, hkx⟩ := this
        have : x * k⁻¹ ∈ E := (hfker _).mp (by rw [map_mul, map_inv, hkx, mul_inv_cancel])
        have := K.mul_mem (hEK this) hk
        simpa using this
      have hcz : ∀ x : X, x * c = c * x := fun x => by
        have := Subgroup.mem_centralizer_iff.mp (hKtop ▸ Subgroup.mem_top x) c hcE
        exact this.symm
      have hCtop : ∀ x : X, x ∈ C := fun x =>
        Subgroup.mem_centralizer_singleton_iff.mpr (hcz x)
      haveI hNnormal : N.Normal := ⟨fun m hm g => conj_mem_oddCoreIn (hCtop g) hm⟩
      have hle : N ≤ classicalInvolutionOddCore X :=
        le_sSup ⟨hNnormal, hNodd⟩
      rw [hO] at hle
      exact Subgroup.mem_bot.mp (hle hn)
  ·
    have hfc1 : f c ≠ 1 := fun h => hcE ((hfker c).mp h)
    have hfc2 : f c * f c = 1 := by rw [← map_mul, hc, map_one]
    have hcn : f c * f n = f n * f c := by
      have := Subgroup.mem_centralizer_singleton_iff.mp (hNC hn)
      rw [← map_mul, ← map_mul, this]
    have h4 : (f n) ^ 4 = 1 := l3Two_centralizer_exp _ _ hfc2 hfc1 hcn
    have hdvd1 : orderOf (f n) ∣ 4 := orderOf_dvd_of_pow_eq_one h4
    have hdvd2 : orderOf (f n) ∣ orderOf n := orderOf_map_dvd f n
    have hodd : Odd (orderOf (f n)) := Odd.of_dvd_nat (hnodd n hn) hdvd2
    have h1 : f n = 1 :=
      orderOf_eq_one_iff.mp (eq_one_of_odd_of_dvd_two_pow (k := 2) hodd (by simpa using hdvd1))
    exact hNE n hn ((hfker n).mp h1)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
