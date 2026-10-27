module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpSmBase

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small.Q3L

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.LieType.HighestRoot
open scoped commutatorElement MatrixGroups

set_option linter.unusedSectionVars false

theorem sl23_q8 : ∀ x y : SL23, x ^ 4 = 1 → x ^ 2 ≠ 1 → y ^ 4 = 1 → y ^ 2 ≠ 1 →
    (x * y * x⁻¹ * y⁻¹) ^ 2 = 1 ∧ (x * y = y * x → y = x ∨ y = x⁻¹) := by
  decide +kernel

theorem pow_four_of_orderOf {G : Type*} [Monoid G] {x : G} (hx : orderOf x = 4) :
    x ^ 4 = 1 ∧ x ^ 2 ≠ 1 := by
  refine ⟨by rw [← hx]; exact pow_orderOf_eq_one x, fun h => ?_⟩
  have := orderOf_dvd_of_pow_eq_one h
  rw [hx] at this
  norm_num at this

theorem sl3_q8 {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3) {J : Type*} [Group J]
    (e : J ≃* SL(2, K)) : ∀ x y : J, orderOf x = 4 → orderOf y = 4 →
      (x * y * x⁻¹ * y⁻¹) ^ 2 = 1 ∧ (x * y = y * x → y = x ∨ y = x⁻¹) := by
  intro x y hx hy
  set φ := e.trans (slEquivSL23 hK)
  have hx' : orderOf (φ x) = 4 := by rw [MulEquiv.orderOf_eq]; exact hx
  have hy' : orderOf (φ y) = 4 := by rw [MulEquiv.orderOf_eq]; exact hy
  obtain ⟨hx4, hx2⟩ := pow_four_of_orderOf hx'
  obtain ⟨hy4, hy2⟩ := pow_four_of_orderOf hy'
  obtain ⟨h1, h2⟩ := sl23_q8 (φ x) (φ y) hx4 hx2 hy4 hy2
  refine ⟨?_, fun hxy => ?_⟩
  · apply φ.injective
    rw [map_one, map_pow, map_mul, map_mul, map_mul, map_inv, map_inv]
    exact h1
  · rcases h2 (by rw [← map_mul, ← map_mul, hxy]) with h | h
    · exact Or.inl (φ.injective h)
    · exact Or.inr (φ.injective (by rw [h, map_inv]))

set_option maxRecDepth 100000 in
theorem mat23_q8 : ∀ M A : Matrix (Fin 2) (Fin 2) (ZMod 3), M * M * (M * M) = 1 → M * M ≠ 1 →
    A * A * (A * A) = 1 → A * A ≠ 1 →
      (M * A * (M * M * M) * (A * A * A)) * (M * A * (M * M * M) * (A * A * A)) = 1 ∧
        (M * A = A * M → A = M ∨ A = M * M * M) := by
  decide

theorem gl23_q8 : ∀ x y : GL (Fin 2) (ZMod 3), orderOf x = 4 → orderOf y = 4 →
    (x * y * x⁻¹ * y⁻¹) ^ 2 = 1 ∧ (x * y = y * x → y = x ∨ y = x⁻¹) := by
  intro x y hx hy
  obtain ⟨hx4, -⟩ := pow_four_of_orderOf hx
  obtain ⟨hy4, -⟩ := pow_four_of_orderOf hy
  have hxi : x⁻¹ = x * x * x := inv_eq_of_mul_eq_one_right
    ((by simp only [pow_succ, pow_zero, one_mul, mul_assoc] : x * (x * x * x) = x ^ 4).trans hx4)
  have hyi : y⁻¹ = y * y * y := inv_eq_of_mul_eq_one_right
    ((by simp only [pow_succ, pow_zero, one_mul, mul_assoc] : y * (y * y * y) = y ^ 4).trans hy4)
  have hval : ∀ z : GL (Fin 2) (ZMod 3), orderOf z = 4 →
      (z : Matrix (Fin 2) (Fin 2) (ZMod 3)) * z * (z * z) = 1 ∧
        (z : Matrix (Fin 2) (Fin 2) (ZMod 3)) * z ≠ 1 := fun z hz => by
    obtain ⟨h4, h2⟩ := pow_four_of_orderOf hz
    refine ⟨?_, fun h => h2 (Units.ext ?_)⟩
    · have := congrArg Units.val h4
      rw [Units.val_pow_eq_pow_val, Units.val_one] at this
      rw [← this, ← mul_assoc, pow_succ, pow_succ, pow_succ, pow_one]
    · rw [Units.val_pow_eq_pow_val, Units.val_one, sq]
      exact h
  obtain ⟨hM4, hM2⟩ := hval x hx
  obtain ⟨hA4, hA2⟩ := hval y hy
  obtain ⟨h1, h2⟩ := mat23_q8 _ _ hM4 hM2 hA4 hA2
  refine ⟨?_, fun hxy => ?_⟩
  · rw [hxi, hyi, sq]
    apply Units.ext
    simpa only [Units.val_mul, Units.val_one] using h1
  · have hxy' : (x : Matrix (Fin 2) (Fin 2) (ZMod 3)) * y = y * x := by
      rw [← Units.val_mul, ← Units.val_mul, hxy]
    rcases h2 hxy' with h | h
    · exact Or.inl (Units.ext h)
    · right
      rw [hxi]
      apply Units.ext
      simpa only [Units.val_mul] using h

theorem q8_conj_aux : ∀ x w : QuaternionGroup 2, x ^ 4 = 1 → x ^ 2 ≠ 1 →
    w * x * w⁻¹ = x ∨ w * x * w⁻¹ = x⁻¹ := by
  decide

theorem q8_conj {Q : Type*} [Group Q] (e : Q ≃* QuaternionGroup 2) {x : Q} (hx : orderOf x = 4)
    (w : Q) : w * x * w⁻¹ = x ∨ w * x * w⁻¹ = x⁻¹ := by
  have hx' : orderOf (e x) = 4 := by rw [MulEquiv.orderOf_eq]; exact hx
  obtain ⟨h4, h2⟩ := pow_four_of_orderOf hx'
  rcases q8_conj_aux (e x) (e w) h4 h2 with h | h
  · exact Or.inl (e.injective (by rw [map_mul, map_mul, map_inv, h]))
  · exact Or.inr (e.injective (by rw [map_mul, map_mul, map_inv, h, map_inv]))

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem eq_one_of_mul_self_odd {G : Type*} [Group G] {M : Subgroup G} (hMo : Odd (Nat.card M))
    {m : G} (hm : m ∈ M) (hmm : m * m = 1) : m = 1 := by
  have h2 : orderOf m ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq, hmm])
  have hodd : Odd (orderOf m) := hMo.of_dvd_nat (Subgroup.orderOf_dvd_natCard M hm)
  rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
  · exact orderOf_eq_one_iff.mp h
  · rw [h] at hodd
    exact absurd hodd (by decide)

theorem uniqueInv_conj (h : PerpHypS n Y R S t) {g : Y}
    (hgc : g ∈ Subgroup.centralizer ({t} : Set Y)) :
    IsUniqueInvolution (conjSub g (tightCore R)) t := by
  have hct : g * t * g⁻¹ = t := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hgc
    rw [hgc]; group
  have := (uniqueInv_core h).conj g
  rwa [hct] at this

theorem false_of_twin_hom (h : PerpHypS n Y R S t) {H : Type*} [Group H] {θ : H →* Y}
    (hθ : Function.Injective θ)
    (hH : ∀ x y : H, orderOf x = 4 → orderOf y = 4 →
      (x * y * x⁻¹ * y⁻¹) ^ 2 = 1 ∧ (x * y = y * x → y = x ∨ y = x⁻¹))
    {g : Y} (hgc : g ∈ Subgroup.centralizer ({t} : Set Y))
    (hne : conjSub g (tightCore R) ≠ tightCore R) {s : Y} (hsK : s ∈ tightCore R)
    (hs4 : orderOf s = 4) (hs : s ∈ θ.range) (hs' : g * s * g⁻¹ ∈ θ.range) : False := by
  set K := tightCore R with hKdef
  set K' := conjSub g K with hK'def
  have hΩ := h.core.hyp
  have hz := uniqueInv_core h
  have hz' : IsUniqueInvolution K' t := uniqueInv_conj h hgc
  have hKΩ : K ∈ CoreAssembly.conjClass K := CoreAssembly.mem_conjClass_self _
  have hK'Ω : K' ∈ CoreAssembly.conjClass K := ⟨g, rfl⟩
  obtain ⟨x, rfl⟩ := hs
  obtain ⟨y, hy⟩ := hs'
  have hx4 : orderOf x = 4 := by rwa [orderOf_injective θ hθ] at hs4
  have hs'4 : orderOf (g * θ x * g⁻¹) = 4 := by
    have := MulEquiv.orderOf_eq (MulAut.conj g) (θ x)
    rw [MulAut.conj_apply] at this
    rw [this, hs4]
  have hy4 : orderOf y = 4 := by rw [← orderOf_injective θ hθ, hy, hs'4]
  obtain ⟨h2, hc⟩ := hH x y hx4 hy4
  have hs'K' : g * θ x * g⁻¹ ∈ K' := conj_mem_conjSub hsK
  have hcomm := comm_le_oddCore_of_twin hΩ hKΩ hK'Ω hne.symm hz hz'
  have hmem : ⁅θ x, θ y⁆ ∈ ⁅K, K'⁆ :=
    Subgroup.commutator_mem_commutator hsK (hy ▸ hs'K')
  have hodd : ⁅θ x, θ y⁆ ∈ oddCoreOf K := (Subgroup.mem_inf.mp (hcomm hmem)).1
  have hsq : ⁅θ x, θ y⁆ * ⁅θ x, θ y⁆ = 1 := by
    rw [commutatorElement_def, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, ← map_mul,
      ← pow_two, h2, map_one]
  have h1 : ⁅θ x, θ y⁆ = 1 := eq_one_of_mul_self_odd (oddCoreOf_odd_natCard K) hodd hsq
  have hxy : x * y = y * x := by
    apply hθ
    rw [map_mul, map_mul]
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  have hyK : θ y ∈ K := by
    rcases hc hxy with rfl | rfl
    · exact hsK
    · rw [map_inv]; exact K.inv_mem hsK
  have hcmem : θ y ∈ K ⊓ K' := Subgroup.mem_inf.mpr ⟨hyK, hy ▸ hs'K'⟩
  have hdvd : 2 ^ 2 ∣ Nat.card ↥(K ⊓ K') := by
    have := Subgroup.orderOf_dvd_natCard (K ⊓ K') hcmem
    rw [orderOf_injective θ hθ, hy4] at this
    simpa using this
  have h4 := (hΩ.omega4 K hKΩ K' hK'Ω hne.symm).1
  have h3 := (padicValNat_dvd_iff_le (p := 2) Nat.card_pos.ne').mp hdvd
  omega

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small.Q3L
