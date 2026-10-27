module

public import CFSG.LocalAnalysis.OddStandard.Solomon75AhatDataSylow
public import Certificates.Certificate6122
public import CFSG.LocalAnalysis.OddStandard.GH71.AhatPerm

public section

namespace CFSG.OddStandard.GH71.AhatB

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS CFSG.OddStandard.Solomon75.AhatData
open scoped commutatorElement

variable {K : Type} [Group K]

theorem card_P0 : Nat.card (P0 11) = 128 :=
  Certificates.certificate6122.1

theorem index_odd [Finite K] (hK : IsDoubleCoverOfAlt K 11) {T : Subgroup K}
    (hT : Nat.card T = 2 ^ 8) : ¬ 2 ∣ T.index := by
  have h1 := Subgroup.card_mul_index T
  rw [card_K_eq (by norm_num) hK, hT] at h1
  have h2 : T.index = 155925 := by
    norm_num [Nat.factorial] at h1
    omega
  rw [h2]
  decide

theorem exists_frame [Finite K] (hK : IsDoubleCoverOfAlt K 11) {S : Subgroup K}
    (hS : IsPGroup 2 S) (hc : Nat.card S = 2 ^ 8) :
    ∃ C : CoverSetup 11 K, S = (P0 11).comap C.ρ := by
  let C₀ := CoverSetup.ofCover hK
  have hS₀card : Nat.card ((P0 11).comap C₀.ρ) = 2 ^ 8 := by
    rw [C₀.card_comap (P0_le_alternatingGroup (by norm_num) (by norm_num)), card_P0]
    norm_num
  obtain ⟨k, hk⟩ := exists_conj_of_sylow S ((P0 11).comap C₀.ρ) hS (IsPGroup.of_card hS₀card)
    (index_odd hK hc) (index_odd hK hS₀card)
  have key : ∀ y : K, k⁻¹ * y * k ∈ center K ↔ y ∈ center K := by
    intro y
    constructor
    · intro h
      have := (inferInstance : (center K).Normal).conj_mem _ h k
      simpa [mul_assoc] using this
    · intro h
      exact (inferInstance : (center K).Normal).conj_mem' _ h k
  refine ⟨⟨C₀.π.comp (MulAut.conj k⁻¹).toMonoidHom,
    C₀.surj.comp (MulAut.conj k⁻¹).surjective, ?_, hK⟩, ?_⟩
  · ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, C₀.ker,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, key]
  · ext x
    rw [hk x]
    simp [CoverSetup.ρ]

namespace Cov

theorem center_eq (C : CoverSetup 11 K) {c c' : K} (hc : c ∈ center K) (hc' : c' ∈ center K)
    (h1 : c ≠ 1) (h1' : c' ≠ 1) : c = c' := by
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : center K)).1 C.center_card
  have e1 := hy ⟨c, hc⟩ (fun h => h1 (congrArg Subtype.val h))
  have e2 := hy ⟨c', hc'⟩ (fun h => h1' (congrArg Subtype.val h))
  exact congrArg Subtype.val (e1.trans e2.symm)

theorem comm_of_center {x c : K} (hc : c ∈ center K) : Commute x c :=
  mem_center_iff.1 hc x

theorem commutator_mem_center (C : CoverSetup 11 K) {a b : K}
    (hc : C.ρ a * C.ρ b = C.ρ b * C.ρ a) : a * b * a⁻¹ * b⁻¹ ∈ center K := by
  rw [← C.ρ_eq_one_iff]
  simp only [map_mul, map_inv]
  rw [hc]
  group

theorem comm_of_isoI (C : CoverSetup 11 K) {a b : K} (ha : IsoI (C.ρ a))
    (hb : IsoI (C.ρ b)) (hab : IsoI (C.ρ a * C.ρ b)) (hc : C.ρ a * C.ρ b = C.ρ b * C.ρ a) :
    a * b = b * a := by
  have hI : ∀ x : K, IsoI (C.ρ x) → x * x = 1 := fun x hx =>
    C.isoI_sq_eq_one (by norm_num) (by norm_num) e8_witness hx
  have hsq := CoverSetup.sq_mul_of_comm_central (commutator_mem_center C hc)
  rw [hI (a * b) (by rw [map_mul]; exact hab), hI a ha, hI b hb] at hsq
  simp only [mul_one] at hsq
  have h1 : a * b * a⁻¹ * b⁻¹ = 1 := inv_eq_one.1 hsq.symm
  calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
    _ = b * a := by rw [h1, one_mul]

theorem commutator_of_dblI (C : CoverSetup 11 K) {a b : K} (ha : DblI (C.ρ a))
    (hb : DblI (C.ρ b)) (hab : DblI (C.ρ a * C.ρ b)) (hc : C.ρ a * C.ρ b = C.ρ b * C.ρ a) :
    ⁅a, b⁆ ∈ center K ∧ ⁅a, b⁆ ≠ 1 := by
  have hcen := commutator_mem_center C hc
  have hsq := CoverSetup.sq_mul_of_comm_central hcen
  have hab' : DblI (C.ρ (a * b)) := by rw [map_mul]; exact hab
  have hza := C.sq_mem_center ha.1
  have hzb := C.sq_mem_center hb.1
  have hzab := C.sq_mem_center hab'.1
  have e1 := center_eq C hzb hza (C.dblI_sq_ne_one (by norm_num) hb)
    (C.dblI_sq_ne_one (by norm_num) ha)
  have e2 := center_eq C hzab hza (C.dblI_sq_ne_one (by norm_num) hab')
    (C.dblI_sq_ne_one (by norm_num) ha)
  rw [e1, e2, C.sq_of_mem_center hza, mul_one] at hsq
  refine ⟨by rw [commutatorElement_def]; exact hcen, ?_⟩
  rw [commutatorElement_def]
  intro h1
  rw [h1, inv_one] at hsq
  exact C.dblI_sq_ne_one (by norm_num) ha hsq

theorem exists_lift_prime (C : CoverSetup 11 K) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {y : K}
    (h : C.ρ y ^ p = 1) (h1 : C.ρ y ≠ 1) : ∃ c ∈ center K, orderOf (y * c) = p := by
  have : Fact p.Prime := ⟨hp⟩
  have hyc : y ^ p ∈ center K := by
    rw [← C.ρ_eq_one_iff, map_pow, h]
  have hodd : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨m, hm⟩ := hodd
  have hne : ∀ c ∈ center K, y * c ≠ 1 := fun c hc h' => h1 (by
    rw [show y = c⁻¹ by rw [eq_inv_iff_mul_eq_one, h'], map_inv,
      (C.ρ_eq_one_iff).2 hc, inv_one])
  by_cases h0 : y ^ p = 1
  · exact ⟨1, one_mem _, orderOf_eq_prime (by rw [mul_one, h0]) (hne 1 (one_mem _))⟩
  · refine ⟨y ^ p, hyc, orderOf_eq_prime ?_ (hne _ hyc)⟩
    have hc2 : y ^ p * y ^ p = 1 := C.sq_of_mem_center hyc
    rw [(comm_of_center (x := y) hyc).mul_pow, ← pow_succ',
      show p + 1 = 2 * (m + 1) by omega, pow_mul, sq, hc2, one_pow]

end Cov

end CFSG.OddStandard.GH71.AhatB
