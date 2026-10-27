module

public import CFSG.ClassicalInvolution.Uniform.U5Comp
public import CFSG.ClassicalInvolution.Uniform.U5Three
public import CFSG.ClassicalInvolution.Q3.OddCentralizerModels
public import CFSG.ClassicalInvolution.Q3.M11Kernel
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerGaussUnitary
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.Uniform

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77
open scoped MatrixGroups commutatorElement

section Local

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem exists_sylow_of_omegaNbr (hΩ : HypOmegaModU (.sl2 3 1) Ω) (hex : ExactMembers Ω)
    {K J : Subgroup G} (hJ : J ∈ omegaNbr Ω K) :
    ∃ Q : Subgroup G, Q ≤ J ∧ Nat.card Q = 8 ∧ Q ≤ Subgroup.normalizer (K : Set G) := by
  obtain ⟨hJΩ, hne, R, hR, hRJ, hRN⟩ := hJ
  have h24 : ∀ L ∈ Ω, Nat.card L = 24 := fun L hL =>
    (natCard_memberU hΩ hex hL).trans natCard_sl2_galoisField_three
  obtain ⟨J', hJ'Ω, P, rfl⟩ := hR
  refine ⟨_, hRJ, ?_, hRN⟩
  rw [Subgroup.card_map_of_injective J'.subtype_injective, Sylow.card_eq_multiplicity,
    h24 J' hJ'Ω, two_pow_factorization_24]

theorem commutes_of_twins (hΩ : HypOmegaModU (.sl2 3 1) Ω) (hex : ExactMembers Ω)
    {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hne : K ≠ J) {z : G}
    (hzK : IsUniqueInvolution K z) (hzJ : IsUniqueInvolution J z) : Commutes K J := by
  obtain ⟨hv, -⟩ := hΩ.omega4 K hK J hJ hne
  refine (hΩ.omega4_commutes hex hK hJ hne).2 ?_
  have hord : orderOf (⟨z, hzK.mem, hzJ.mem⟩ : ↥(K ⊓ J)) = 2 :=
    orderOf_eq_prime (by ext; simpa [pow_two] using hzK.sq)
      (fun h => hzK.ne_one (by simpa using congrArg Subtype.val h))
  have h2 : 2 ∣ Nat.card ↥(K ⊓ J) := hord ▸ orderOf_dvd_natCard _
  have h2' : 1 ≤ padicValNat 2 (Nat.card ↥(K ⊓ J)) :=
    (padicValNat_dvd_iff_le (Nat.card_pos (α := ↥(K ⊓ J))).ne').mp
      (by simpa using h2 : 2 ^ 1 ∣ Nat.card ↥(K ⊓ J))
  omega

theorem card_sup_of_sylow_normalizes {K J Q : Subgroup G} (hK24 : Nat.card K = 24)
    (hQ8 : Nat.card Q = 8) (hQJ : Q ≤ J) (hQN : Q ≤ Subgroup.normalizer (K : Set G))
    (hv : padicValNat 2 (Nat.card ↥(K ⊓ J)) ≤ 1) :
    (Nat.card ↥(Q ⊔ K) = 192 ∧ Nat.card ↥(K ⊓ Q) = 1) ∨
      (Nat.card ↥(Q ⊔ K) = 96 ∧ Nat.card ↥(K ⊓ Q) = 2) := by
  have hcdvd8 : Nat.card ↥(K ⊓ Q) ∣ 2 ^ 3 := by
    have := Subgroup.card_dvd_of_le (inf_le_right : K ⊓ Q ≤ Q)
    rwa [hQ8] at this
  have hcdvdKJ : Nat.card ↥(K ⊓ Q) ∣ Nat.card ↥(K ⊓ J) :=
    Subgroup.card_dvd_of_le (inf_le_inf_left K hQJ)
  have hnot4 : ¬ 4 ∣ Nat.card ↥(K ⊓ Q) := by
    intro h4
    have h4' : 2 ^ 2 ∣ Nat.card ↥(K ⊓ J) := by
      have := h4.trans hcdvdKJ
      simpa using this
    have := (padicValNat_dvd_iff_le Nat.card_pos.ne').mp h4'
    omega
  have hc12 : Nat.card ↥(K ⊓ Q) = 1 ∨ Nat.card ↥(K ⊓ Q) = 2 := by
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hcdvd8
    interval_cases k
    · exact Or.inl (by simpa using hk')
    · exact Or.inr (by simpa using hk')
    · exact absurd (by rw [hk']; norm_num) hnot4
    · exact absurd (by rw [hk']; norm_num) hnot4
  have hprod := CFSG.ClassicalInvolution.Asc77.ChainFrame.card_sup_mul_card_inf' hQN
  rw [hK24, hQ8] at hprod
  rcases hc12 with h | h
  · left
    rw [h] at hprod
    exact ⟨by omega, h⟩
  · right
    rw [h] at hprod
    exact ⟨by omega, h⟩

end Local

section Components

theorem compGen3_sl23 : CompGen3 Q3.CompData.sl23 := by
  intro X _ _ ψ _ R₁ hR₁ R₂ hR₂ _ _ hne
  exact absurd (by rw [Set.mem_singleton_iff.mp hR₁, Set.mem_singleton_iff.mp hR₂]) hne

theorem compGen3_m11 : CompGen3 Q3.CompData.m11 := by
  intro X _ _ ψ hker R₁ hR₁ R₂ hR₂ h24₁ h24₂ hne hQ hv htw
  exfalso
  obtain ⟨Q, hQJ, hQ8, hQN⟩ := hQ
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans (Q3.center_m11_eq_bot Q3.m11Facts).le
  have hrange : Nat.card ψ.range = 7920 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    exact Q3.card_m11_kernel
  have hKr : R₁.map ψ ≤ ψ.range := Subgroup.map_le_range ψ R₁
  have hJr : R₂.map ψ ≤ ψ.range := Subgroup.map_le_range ψ R₂
  have hle : Q ⊔ R₁.map ψ ≤ ψ.range := sup_le (hQJ.trans hJr) hKr
  have hdvd : Nat.card ↥(Q ⊔ R₁.map ψ) ∣ 7920 := hrange ▸ Subgroup.card_dvd_of_le hle
  rcases card_sup_of_sylow_normalizes h24₁ hQ8 hQJ hQN hv with ⟨h, -⟩ | ⟨h, -⟩ <;>
    rw [h] at hdvd <;> norm_num at hdvd

end Components

end CFSG.ClassicalInvolution.Uniform
