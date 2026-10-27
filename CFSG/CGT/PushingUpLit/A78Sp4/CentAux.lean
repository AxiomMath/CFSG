module

public import CFSG.CGT.PushingUpLit.A78Sp4.AuxLemmas
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.CGT.PushingUpLit.A78Sp4

open CFSG.Assembly CFSG.ABGLocalTools

variable {G : Type} [Group G]

theorem exists_fully_centralized [Finite G] {S : Subgroup G} (hS : IsSylowOf 2 S ⊤) {f : G}
    (hfS : f ∈ S) : ∃ g : G, g⁻¹ * f * g ∈ S ∧
      IsSylowOf 2 (S ⊓ Subgroup.centralizer ({g⁻¹ * f * g} : Set G))
        (Subgroup.centralizer ({g⁻¹ * f * g} : Set G)) := by
  classical
  let α := {g : G // g⁻¹ * f * g ∈ S}
  have : Nonempty α := ⟨⟨1, by simpa using hfS⟩⟩
  obtain ⟨g₀, hg₀⟩ := Finite.exists_max
    (fun g : α => Nat.card ↥(S ⊓ Subgroup.centralizer ({g.1⁻¹ * f * g.1} : Set G)))
  set f' : G := g₀.1⁻¹ * f * g₀.1 with hf'
  have hf'S : f' ∈ S := g₀.2
  have hU : IsPGroup 2 ↥(S ⊓ Subgroup.centralizer ({f'} : Set G)) :=
    hS.isPGroup.to_le inf_le_left
  obtain ⟨R, hR, hUR⟩ := exists_isSylowOf_ge hU inf_le_right
  obtain ⟨k, -, hk⟩ := exists_conj_le_of_isSylowOf hS (le_top : R ≤ ⊤) hR.isPGroup
  have hf'R : f' ∈ R := hUR ⟨hf'S, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩
  have hkf : k * f' * k⁻¹ ∈ S := hk (mul_mem_cj k hf'R)
  have hkg : (g₀.1 * k⁻¹)⁻¹ * f * (g₀.1 * k⁻¹) = k * f' * k⁻¹ := by
    rw [hf']
    group
  have hle : cj k R ≤ S ⊓ Subgroup.centralizer ({k * f' * k⁻¹} : Set G) := by
    refine le_inf hk ?_
    rw [← cj_centralizer_singleton]
    exact cj_mono k hR.le
  have hmax := hg₀ ⟨g₀.1 * k⁻¹, by rw [hkg]; exact hkf⟩
  simp only [hkg] at hmax
  have hcard : Nat.card R ≤ Nat.card ↥(S ⊓ Subgroup.centralizer ({f'} : Set G)) := by
    calc Nat.card R = Nat.card (cj k R) := (card_cj k R).symm
      _ ≤ Nat.card ↥(S ⊓ Subgroup.centralizer ({k * f' * k⁻¹} : Set G)) :=
          Subgroup.card_le_of_le hle
      _ ≤ _ := hmax
  have hEq : S ⊓ Subgroup.centralizer ({f'} : Set G) = R :=
    Subgroup.eq_of_le_of_card_ge hUR hcard
  exact ⟨g₀.1, g₀.2, hEq ▸ hR⟩

theorem isPGroup_zpowers_of_mul_self {f : G} (hf : f * f = 1) :
    IsPGroup 2 (Subgroup.zpowers f) := by
  intro x
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 x.2
  refine ⟨1, Subtype.ext ?_⟩
  show (x : G) ^ 2 ^ 1 = 1
  rw [← hn, pow_one, pow_two, ← (Commute.refl f).mul_zpow n, hf, one_zpow]

theorem isTwoLocal_centralizer {f : G} (hf : f * f = 1) (hf1 : f ≠ 1) :
    IsTwoLocal (Subgroup.centralizer ({f} : Set G)) := by
  refine ⟨Subgroup.zpowers f, ?_, isPGroup_zpowers_of_mul_self hf, ?_⟩
  · intro hbot
    exact hf1 (Subgroup.mem_bot.1 (hbot ▸ Subgroup.mem_zpowers f))
  · ext g
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_normalizer_iff]
    constructor
    · intro hg y
      have h1 : g * f * g⁻¹ = f := by rw [hg]; group
      have hc : ∀ m : ℤ, g * f ^ m * g⁻¹ = f ^ m := fun m => by rw [← conj_zpow, h1]
      constructor
      · rintro ⟨n, rfl⟩
        exact ⟨n, (hc n).symm⟩
      · rintro ⟨n, hn⟩
        refine ⟨n, ?_⟩
        have hn' : f ^ n = g * y * g⁻¹ := hn
        have h3 : g * f ^ n * g⁻¹ = g * y * g⁻¹ := by rw [hc n, hn']
        exact mul_left_cancel (mul_right_cancel h3)
    · intro h
      have h1 : g * f * g⁻¹ ∈ Subgroup.zpowers f := (h f).1 (Subgroup.mem_zpowers f)
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 h1
      have h2 : f ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hf
      have hfn : f ^ n = 1 ∨ f ^ n = f := by
        rcases Int.even_or_odd' n with ⟨k, rfl | rfl⟩
        · left
          rw [zpow_mul, h2, one_zpow]
        · right
          rw [zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]
      rcases hfn with h3 | h3
      · exfalso
        apply hf1
        have : g * f * g⁻¹ = 1 := by rw [← hn, h3]
        have h4 : f = g⁻¹ * (g * f * g⁻¹) * g := by group
        rw [h4, this]
        group
      · have : g * f * g⁻¹ = f := by rw [← hn, h3]
        calc g * f = g * f * g⁻¹ * g := by group
          _ = f * g := by rw [this]

theorem pCoreOf_le_of_isSylowOf [Finite G] {R C : Subgroup G} (hR : IsSylowOf 2 R C) :
    CFSG.Open.pCoreOf 2 C ≤ R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := hR.exists_sylow_eq_subgroupOf
  have : (CFSG.Open.pCore 2 C).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have h1 : CFSG.Open.pCore 2 C ≤ (Q : Subgroup C) :=
    IsPGroup.le_sylow_of_normal (CFSG.LieType.BorelTits.pCore_isPGroup 2) Q
  have h2 := Subgroup.map_mono (f := C.subtype) h1
  rw [hQ, Subgroup.map_subgroupOf_eq_of_le hR.le] at h2
  exact h2

theorem cent_le_pCoreOf (hc : IsCharTwoType G) {f : G} (hf : f * f = 1) (hf1 : f ≠ 1) :
    Subgroup.centralizer ({f} : Set G) ⊓
      Subgroup.centralizer
        (CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({f} : Set G)) : Set G) ≤
    CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({f} : Set G)) :=
  hc _ (isTwoLocal_centralizer hf hf1)

end CFSG.CGT.PushingUpLit.A78Sp4
