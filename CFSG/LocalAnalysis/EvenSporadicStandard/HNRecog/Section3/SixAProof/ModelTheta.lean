module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.SixAProof.ModelDefs

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open Equiv Equiv.Perm

theorem sixAExt_injective : Function.Injective sixAExt :=
  Equiv.Perm.extendDomainHom_injective sixAEmb

theorem sixATheta_injective : Function.Injective sixATheta := by
  rw [injective_iff_map_eq_one]
  rintro ⟨ε, ρ⟩ h
  rw [sixATheta_apply] at h
  have hε : ε = 1 := by
    rcases sixA_Z2_cases ε with rfl | rfl
    · rfl
    · exfalso
      rw [sixAFlip_eps] at h
      have h0 := congrArg (fun p : Sym 7 => p 0) h
      simp only [Equiv.Perm.mul_apply, Equiv.Perm.coe_one, id_eq] at h0
      rw [sixAExt_apply_of_lt ρ 0 (by decide)] at h0
      revert h0
      decide
  subst hε
  rw [sixAFlip_one, one_mul] at h
  have hρ : ρ = 1 := sixAExt_injective (by rw [h, map_one])
  simp [hρ]

theorem sixATheta_mem (x : Z 2 × Sym 5) :
    sixATheta x ∈ Subgroup.centralizer ({sixASigma} : Set (Sym 7)) := by
  obtain ⟨ε, ρ⟩ := x
  rw [sixATheta_apply, Subgroup.mem_centralizer_singleton_iff]
  have h1 : Commute sixASigma (sixAFlip ε) := by
    rcases sixA_Z2_cases ε with rfl | rfl
    · rw [sixAFlip_one]; exact Commute.one_right _
    · rw [sixAFlip_eps]
  have h2 : Commute sixASigma (sixAExt ρ) := (sixAExt_disjoint ρ).commute
  exact (h1.mul_right h2).eq.symm

theorem sixA_cycleType_sigma : sixASigma.cycleType = {2} :=
  Equiv.Perm.isSwap_iff_cycleType.1 ⟨0, 1, by decide, rfl⟩

theorem sixA_sigma_mul_self : sixASigma * sixASigma = 1 := Equiv.swap_mul_self _ _

theorem sixATheta_surj {g : Sym 7} (hg : g ∈ Subgroup.centralizer ({sixASigma} : Set (Sym 7))) :
    ∃ x, sixATheta x = g := by
  have hcard : Nat.card (Subgroup.centralizer ({sixASigma} : Set (Sym 7))) = 240 := by
    rw [Equiv.Perm.nat_card_centralizer, sixA_cycleType_sigma]
    simp [Nat.factorial]
  let φ : Z 2 × Sym 5 →* Subgroup.centralizer ({sixASigma} : Set (Sym 7)) :=
    sixATheta.codRestrict _ sixATheta_mem
  have hinj : Function.Injective φ := fun x y h => sixATheta_injective (congrArg Subtype.val h)
  have hcard2 : Nat.card (Z 2 × Sym 5) = 240 := by
    rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Z 2), Nat.card_eq_fintype_card (α := Sym 5)]
    simp [Fintype.card_perm, Nat.factorial]
  have hbij : Function.Bijective φ := hinj.bijective_of_nat_card_le (by rw [hcard, hcard2])
  obtain ⟨x, hx⟩ := hbij.2 ⟨g, hg⟩
  exact ⟨x, congrArg Subtype.val hx⟩

theorem sixA_cycleType_ext (ρ : Sym 5) : (sixAExt ρ).cycleType = ρ.cycleType := by
  simp [sixAExt, Equiv.Perm.extendDomainHom_apply]

theorem sixA_cycleType_sigma_mul_ext (ρ : Sym 5) :
    (sixASigma * sixAExt ρ).cycleType = {2} + ρ.cycleType := by
  rw [(sixAExt_disjoint ρ).cycleType_mul, sixA_cycleType_sigma, sixA_cycleType_ext]

theorem sixA_coord {s : Sym 7} (hs : s ∈ Subgroup.centralizer ({sixASigma} : Set (Sym 7))) :
    ∃ ρ : Sym 5, s = sixAExt ρ ∨ s = sixASigma * sixAExt ρ := by
  obtain ⟨⟨ε, ρ⟩, hx⟩ := sixATheta_surj hs
  rw [sixATheta_apply] at hx
  refine ⟨ρ, ?_⟩
  rcases sixA_Z2_cases ε with rfl | rfl
  · left; rw [← hx, sixAFlip_one, one_mul]
  · right; rw [← hx, sixAFlip_eps]

theorem sixA_sym5_inv {ρ : Sym 5} (h2 : ρ ^ 2 = 1) (h1 : ρ ≠ 1) :
    ρ.cycleType = {2} ∨ ρ.cycleType = {2, 2} := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hrep := Equiv.Perm.cycleType_of_pow_prime_eq_one (p := 2) h2
  have hle := Equiv.Perm.sum_cycleType_le ρ
  obtain ⟨c, hc⟩ : ∃ c, ρ.cycleType.card = c := ⟨_, rfl⟩
  rw [hc] at hrep
  rw [hrep] at hle
  simp only [Multiset.sum_replicate, smul_eq_mul, Fintype.card_fin] at hle
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply h1
    exact Equiv.Perm.cycleType_eq_zero.1 (by simpa using hrep)
  have hc2 : c ≤ 2 := by omega
  interval_cases c
  · exact absurd rfl hc0
  · left; simpa using hrep
  · right; simpa using hrep

end CFSG.EvenSporadicStandard.HNRecog.Section3
