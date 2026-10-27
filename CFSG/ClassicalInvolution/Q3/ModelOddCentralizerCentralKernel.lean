module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ClassicalInvolution.Balance.Basic

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution.Balance CFSG.ComponentClassification

section Complement

variable {G : Type} [Group G] [Finite G]

theorem exists_normal_complement_odd {C : Subgroup G} (hC : C ≤ Subgroup.center G)
    (hC2 : IsPGroup 2 C) (hidx : ¬ 2 ∣ C.index) :
    ∃ H : Subgroup G, H.Normal ∧ ¬ 2 ∣ Nat.card H ∧ Subgroup.IsComplement' H C ∧
      ∀ x : G, x ∈ H ↔ Odd (orderOf x) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Sylow 2 G := hC2.toSylow hidx
  have hPC : (P : Subgroup G) = C := rfl
  have hP : Subgroup.normalizer (P : Subgroup G) ≤ Subgroup.centralizer (P : Set G) := by
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_center_iff.mp (hC hy) x).symm
  have hcomp := MonoidHom.ker_transferSylow_isComplement' P hP
  refine ⟨(MonoidHom.transferSylow P hP).ker, inferInstance,
    MonoidHom.not_dvd_card_ker_transferSylow P hP, hcomp, fun x => ?_⟩
  constructor
  · intro hx
    refine Odd.of_dvd_nat ?_ (Subgroup.orderOf_dvd_natCard _ hx)
    exact Nat.odd_iff.mpr (by
      have := MonoidHom.not_dvd_card_ker_transferSylow P hP
      omega)
  · intro hodd
    obtain ⟨⟨⟨h, hh⟩, ⟨p, hp⟩⟩, hxhp⟩ := hcomp.2 x
    simp only at hxhp
    have hpc : ∀ y : G, y * p = p * y := fun y => Subgroup.mem_center_iff.mp (hC hp) y
    set t := orderOf x with ht
    have hxt : x ^ t = 1 := pow_orderOf_eq_one x
    have hht : h ^ t * p ^ t = 1 := by
      rw [← (show Commute h p from hpc h).mul_pow, hxhp, hxt]
    have hdisj : h ^ t = 1 := by
      have h1 : h ^ t ∈ (MonoidHom.transferSylow P hP).ker := pow_mem hh t
      have h2 : h ^ t ∈ C := by
        have : h ^ t = (p ^ t)⁻¹ := eq_inv_of_mul_eq_one_left hht
        rw [this]
        exact inv_mem (pow_mem hp t)
      exact Subgroup.disjoint_def.mp hcomp.disjoint h1 h2
    have hpt : p ^ t = 1 := by
      rw [hdisj, one_mul] at hht
      exact hht
    obtain ⟨k, hk⟩ := hC2 ⟨p, hp⟩
    have hpk : p ^ (2 ^ k) = 1 := congrArg Subtype.val hk
    have h1 : orderOf p ∣ t := orderOf_dvd_of_pow_eq_one hpt
    have h2 : orderOf p ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hpk
    have h3 : Nat.Coprime t (2 ^ k) := (Nat.coprime_two_right.mpr hodd).pow_right k
    have hp1 : p = 1 := orderOf_eq_one_iff.mp
      (Nat.Coprime.eq_one_of_dvd (h3.coprime_dvd_left h1) h2)
    rw [hp1, mul_one] at hxhp
    rw [← hxhp]
    exact hh

end Complement

section Kernel

variable {J S : Type} [Group J] [Finite J] [Group S]

theorem oddCoreIn_range_eq_bot_of_central_kernel (π : J →* S)
    (hJ : componentClassificationOddCore J = ⊥) (hker : π.ker ≤ Subgroup.center J)
    (hC : IsPGroup 2 π.ker) : oddCoreIn π.range = ⊥ := by
  set π' : J →* π.range := π.rangeRestrict with hπ'
  have hsurj : Function.Surjective π' := π.rangeRestrict_surjective
  have hker' : π'.ker = π.ker := MonoidHom.ker_rangeRestrict π
  have : Finite π.range := Finite.of_surjective _ hsurj
  suffices hO : componentClassificationOddCore π.range = ⊥ by
    unfold oddCoreIn
    rw [hO, Subgroup.map_bot]
  set O := componentClassificationOddCore π.range with hOdef
  have hOodd : Odd (Nat.card O) := OddCore.odd_card π.range
  set N : Subgroup J := O.comap π' with hN
  have hNn : N.Normal := Subgroup.Normal.comap inferInstance π'
  let ρ : N →* O := (π'.comp N.subtype).codRestrict O fun x => x.2
  have hρ : Function.Surjective ρ := fun o => by
    obtain ⟨j, hj⟩ := hsurj o.1
    exact ⟨⟨j, by rw [hN, Subgroup.mem_comap, hj]; exact o.2⟩, Subtype.ext hj⟩
  have hker_mem : ∀ x : N, x ∈ ρ.ker ↔ x.1 ∈ π.ker := fun x => by
    rw [← hker', MonoidHom.mem_ker, MonoidHom.mem_ker, Subtype.ext_iff]
    rfl
  have hC0c : ρ.ker ≤ Subgroup.center N := fun x hx =>
    Subgroup.mem_center_iff.mpr fun y => Subtype.ext
      (Subgroup.mem_center_iff.mp (hker ((hker_mem x).mp hx)) y.1)
  have hC0p : IsPGroup 2 ρ.ker := fun x => by
    obtain ⟨k, hk⟩ := hC ⟨x.1.1, (hker_mem x.1).mp x.2⟩
    exact ⟨k, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hk))⟩
  have hidx : ¬ 2 ∣ ρ.ker.index := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hρ, Subgroup.card_top]
    have := Nat.odd_iff.mp hOodd
    omega
  obtain ⟨H, hHn, hH2, hcomp, hHchar⟩ := exists_normal_complement_odd hC0c hC0p hidx
  have hHodd : Odd (Nat.card H) := Nat.odd_iff.mpr (by omega)
  set Hj : Subgroup J := H.map N.subtype with hHj
  have hHjn : Hj.Normal := ⟨fun n hn g => by
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hn
    have hgy : g * (y : J) * g⁻¹ ∈ N := hNn.conj_mem _ y.2 g
    refine Subgroup.mem_map.mpr ⟨⟨_, hgy⟩, ?_, rfl⟩
    rw [hHchar]
    have h1 : orderOf (⟨g * (y : J) * g⁻¹, hgy⟩ : N) = orderOf y := by
      rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe y]
      exact orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective (y : J)
    rw [h1, ← hHchar]
    exact hy⟩
  have hHjodd : Odd (Nat.card Hj) := by
    rw [hHj, Subgroup.card_map_of_injective N.subtype_injective]
    exact hHodd
  have hHj1 : Hj ≤ componentClassificationOddCore J := le_sSup ⟨hHjn, hHjodd⟩
  rw [hJ, le_bot_iff] at hHj1
  have hH1 : H = ⊥ := (Subgroup.map_eq_bot_iff_of_injective _ N.subtype_injective).mp hHj1
  have hcard := hcomp.card_mul_card
  have hcard2 : Nat.card N = Nat.card O * Nat.card ρ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker]
    congr 1
    exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ρ hρ).toEquiv
  rw [hH1, Subgroup.card_bot, one_mul, hcard2] at hcard
  have h1 : Nat.card O = 1 :=
    Nat.eq_of_mul_eq_mul_right Nat.card_pos (hcard.symm.trans (one_mul _).symm)
  exact Subgroup.card_eq_one.mp h1

end Kernel

end CFSG.ClassicalInvolution.Q3
