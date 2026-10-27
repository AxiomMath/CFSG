module

public import CFSG.ClassicalInvolution.AschTight.Sec6Gen64U

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K J R T : Subgroup G}
  {z j u v : G}

namespace Cfg64D

variable {N₀K N₀J : Subgroup G} {r t : G} (d : Cfg64D Ω K J z j u v R T N₀K N₀J r t)
include d

theorem not_mem_omegaNbr_twin {L : Subgroup G} (hLz : IsUniqueInvolution L z) :
    J ∉ omegaNbr Ω L := by
  rintro ⟨-, -, T', hT', hT'J, hT'N⟩
  obtain ⟨M, -, hT'M⟩ := exists_isSylow2In_of_mem_RSet hT'
  have hT'c := le_centralizer_of_le_normalizer' hLz hT'N
  have h8 := eight_le_of_mem_RSet d.c.hΩ hT'
  exact d.c.notJ ⟨d.c.hJ, d.c.hKJ.symm, T', hT', hT'J,
    le_normalizer_of_le_centralizer d.c.hΩ d.c.hK d.c.hJ d.c.hKJ d.c.hz hT'J hT'M.2.1
      (by omega) hT'c⟩

theorem twin_eq (hA : ∀ y ∈ pairNormalizers K J z j, conjSub y K ≠ J) {L : Subgroup G}
    (hL : L ∈ Ω) (hLz : IsUniqueInvolution L z) : L = K ∨ L = conjSub (r * t)⁻¹ J := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hLK, hLKs⟩ := hcon
  have hΩ := d.c.hΩ
  have hne := d.Kstar_ne hA
  have hJL : J ≠ L := fun h => d.c.z_ne_j (hLz.eq (h ▸ d.c.hj))
  have hLnot : L ∉ omegaNbr Ω J :=
    not_mem_omegaNbr_symm hΩ hL d.c.hJ hLz d.c.hj d.c.z_ne_j (d.not_mem_omegaNbr_twin hLz)
  have hKL := le_normalizer_of_twin hΩ d.c.hK hL (Ne.symm hLK) d.c.hz hLz
  have hKsL := le_normalizer_of_twin hΩ d.Kstar_mem hL (Ne.symm hLKs) d.isUniqueInvolution_J' hLz
  have hcK := comm_le_oddCore_of_twin hΩ d.c.hK hL (Ne.symm hLK) d.c.hz hLz
  have hcKs := comm_le_oddCore_of_twin hΩ d.Kstar_mem hL (Ne.symm hLKs) d.isUniqueInvolution_J' hLz
  have hcommUU : Commutes (Subgroup.zpowers u) (conjSub (r * t)⁻¹ (Subgroup.zpowers v)) :=
    fun a ha b hb => d.c.UV_comm a (Subgroup.mem_sup_left ha) b (d.Ustar_le_UV hb)
  obtain ⟨u₁, hu₁, u₂, hu₂, hj12⟩ := exists_mul_of_mem_sup_of_commutes hcommUU (d.j_mem hne)
  have hu₁K : u₁ ∈ K := d.c.hUK hu₁
  have hu₂K : u₂ ∈ conjSub (r * t)⁻¹ J := conjSub_mono d.c.hVJ hu₂
  have hjN : j ∈ Subgroup.normalizer (L : Set G) := by
    rw [hj12]
    exact Subgroup.mul_mem _ (hKL hu₁K) (hKsL hu₂K)
  have hjc : ∀ l ∈ L, j * l * j⁻¹ * l⁻¹ ∈ oddCoreOf L := by
    intro l hl
    have hl' : u₂ * l * u₂⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hKsL hu₂K) l).mp hl
    have h1 : ⁅u₁, u₂ * l * u₂⁻¹⁆ ∈ oddCoreOf L :=
      (hcK (Subgroup.commutator_mem_commutator hu₁K hl')).2
    have h2 : ⁅u₂, l⁆ ∈ oddCoreOf L := (hcKs (Subgroup.commutator_mem_commutator hu₂K hl)).2
    have e : j * l * j⁻¹ * l⁻¹ = ⁅u₁, u₂ * l * u₂⁻¹⁆ * ⁅u₂, l⁆ := by
      rw [hj12]
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Subgroup.mul_mem _ h1 h2
  have hj2 : IsPGroup 2 ↥(Subgroup.zpowers j) :=
    isPGroup_zpowers_of_mul_self_eq_one d.c.hj.sq d.c.hj.ne_one
  obtain ⟨RL, hRL, hRLinv⟩ := AscL62.exists_sylow_normalized hj2 (Subgroup.zpowers_le.mpr hjN)
  have hRLc : RL ≤ Subgroup.centralizer ({j} : Set G) := by
    intro x hx
    have h1 : j * x * j⁻¹ ∈ RL := by
      have := conj_mem_conjSub (n := j) hx
      rwa [hRLinv j (Subgroup.mem_zpowers j)] at this
    have h2 : j * x * j⁻¹ * x⁻¹ ∈ RL := Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hx)
    have h3 := eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard L) (hjc x (hRL.1 hx))
      (hRL.2.1.to_le (Subgroup.zpowers_le.mpr h2))
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc x * j = (j * x * j⁻¹ * x⁻¹)⁻¹ * (j * x) := by group
      _ = j * x := by rw [h3, inv_one, one_mul]
  have hRLΩ := mem_RSet_of_isSylow2In hL hRL
  have h8 := eight_le_of_mem_RSet hΩ hRLΩ
  exact hLnot ⟨hL, Ne.symm hJL, RL, hRLΩ, hRL.1,
    le_normalizer_of_le_centralizer hΩ d.c.hJ hL hJL d.c.hj hRL.1 hRL.2.1 (by omega) hRLc⟩

theorem twinSet_eq (hA : ∀ y ∈ pairNormalizers K J z j, conjSub y K ≠ J) :
    twinSet Ω K = {K, conjSub (r * t)⁻¹ J} := by
  ext L
  constructor
  · rintro ⟨hL, z', hz', hLz'⟩
    have hLz : IsUniqueInvolution L z := (hz'.eq d.c.hz) ▸ hLz'
    rcases d.twin_eq hA hL hLz with h | h
    · exact Or.inl h
    · exact Or.inr h
  · rintro (rfl | rfl)
    · exact ⟨d.c.hK, z, d.c.hz, d.c.hz⟩
    · exact ⟨d.Kstar_mem, z, d.c.hz, d.isUniqueInvolution_J'⟩

end Cfg64D

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen
