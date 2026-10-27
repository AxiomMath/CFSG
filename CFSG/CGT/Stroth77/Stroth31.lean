module

public import CFSG.CGT.Stroth77.StrothAmbient

public section

namespace CFSG.CGT.Stroth77

variable {G : Type*} [Group G] [Finite G]

noncomputable def strothR (X : StrothAmbient G) (D : Subgroup G) : Subgroup G :=
  ((X.S : Subgroup G) ⊓ Subgroup.normalizer D) ⊓
    Subgroup.centralizer (omegaIn 1 D : Set G)

theorem mem_strothR {X : StrothAmbient G} {D : Subgroup G} {x : G} :
    x ∈ strothR X D ↔
      x ∈ (X.S : Subgroup G) ∧ x ∈ Subgroup.normalizer D ∧
        x ∈ Subgroup.centralizer (omegaIn 1 D : Set G) := by
  simp [strothR, and_assoc]

theorem strothR_le_sylow (X : StrothAmbient G) (D : Subgroup G) :
    strothR X D ≤ (X.S : Subgroup G) := by
  intro x hx
  rw [mem_strothR] at hx
  exact hx.1

theorem strothR_le_normalizer (X : StrothAmbient G) (D : Subgroup G) :
    strothR X D ≤ Subgroup.normalizer D := by
  intro x hx
  rw [mem_strothR] at hx
  exact hx.2.1

theorem strothR_le_centralizer (X : StrothAmbient G) (D : Subgroup G) :
    strothR X D ≤ Subgroup.centralizer (omegaIn 1 D : Set G) := by
  intro x hx
  rw [mem_strothR] at hx
  exact hx.2.2

abbrev IsMinimalLModuleMod {D : Subgroup G} {τ : StrothTypeIndex}
    (dD : StrothWeakTypeData D τ) (C : Subgroup G) : Prop :=
  dD.IsMinimalLModule C

theorem IsMinimalLModuleMod.d_lt {D : Subgroup G} {τ : StrothTypeIndex}
    {dD : StrothWeakTypeData D τ} {C : Subgroup G} (h : IsMinimalLModuleMod dD C) :
    D < C :=
  h.1

theorem IsMinimalLModuleMod.le_normalizer {D : Subgroup G} {τ : StrothTypeIndex}
    {dD : StrothWeakTypeData D τ} {C : Subgroup G} (h : IsMinimalLModuleMod dD C) :
    dD.L ≤ Subgroup.normalizer C :=
  h.2.1

theorem le_sylow_of_le_strothR {X : StrothAmbient G} {Z : StrothDatum X} {C : Subgroup G}
    (hCR : C ≤ strothR X Z.D) : C ≤ (X.S : Subgroup G) :=
  hCR.trans (strothR_le_sylow X Z.D)

theorem isPGroup_of_le_strothR {X : StrothAmbient G} {Z : StrothDatum X} {C : Subgroup G}
    (hCR : C ≤ strothR X Z.D) : IsPGroup 2 C :=
  X.S.isPGroup'.to_le (le_sylow_of_le_strothR hCR)

theorem exists_card_eq_pow_two {X : StrothAmbient G} {Z : StrothDatum X} {C : Subgroup G}
    (hCR : C ≤ strothR X Z.D) : ∃ k : ℕ, Nat.card C = 2 ^ k :=
  IsPGroup.exists_card_eq (p := 2) (isPGroup_of_le_strothR hCR)

theorem index_eq_pow_two {X : StrothAmbient G} {Z : StrothDatum X} {C : Subgroup G}
    (hCR : C ≤ strothR X Z.D) :
    ∃ k : ℕ, (Z.D.subgroupOf C).index = 2 ^ k := by
  obtain ⟨n, hn⟩ := exists_card_eq_pow_two (X := X) (Z := Z) (C := C) hCR
  have hmul := Subgroup.card_mul_index (Z.D.subgroupOf C)
  have hdvd : (Z.D.subgroupOf C).index ∣ Nat.card C :=
    ⟨Nat.card (Z.D.subgroupOf C), by rw [mul_comm, hmul]⟩
  rw [hn] at hdvd
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  exact ⟨k, hk⟩

theorem one_lt_index_of_d_lt {X : StrothAmbient G} {Z : StrothDatum X} {C : Subgroup G}
    (hmin : IsMinimalLModuleMod Z.dataD C) : 1 < (Z.D.subgroupOf C).index := by
  have hne : Z.D.subgroupOf C ≠ ⊤ := by
    intro htop
    exact not_le_of_gt hmin.d_lt (Subgroup.subgroupOf_eq_top.mp htop)
  exact Subgroup.one_lt_index_of_ne_top hne

theorem card_D_of_tau_t100 {X : StrothAmbient G} {Z : StrothDatum X} {m : ℕ}
    (hτ : Z.τ = StrothTypeIndex.t100 m) : Nat.card Z.D = 2 ^ (3 * m + 2) := by
  have h := Z.dataD.card
  rw [hτ] at h
  have hnum : (StrothTypeIndex.t100 m).k 0 + (StrothTypeIndex.t100 m).k 1 +
      (StrothTypeIndex.t100 m).k 2 = 3 * m + 2 := by
    simp [StrothTypeIndex.k, Type100.k]
    ring
  rwa [hnum] at h

theorem stroth_3_1 (X : StrothAmbient G) {m : ℕ} (Z : StrothDatum X)
    (hτ : Z.τ = StrothTypeIndex.t100 m) (C : Subgroup G) (hDC : Z.D ≤ C)
    (hCR : C ≤ strothR X Z.D) (hmin : IsMinimalLModuleMod Z.dataD C)
    (hle : (Z.D.subgroupOf C).index ≤ 4)
    (hne : (Z.D.subgroupOf C).index ≠ 4) :
    Nat.card C = 2 * Nat.card Z.D := by
  obtain ⟨k, hk⟩ := index_eq_pow_two (X := X) (Z := Z) (C := C) hCR
  have hgt : 1 < 2 ^ k := by
    rw [← hk]
    exact one_lt_index_of_d_lt hmin
  have hk1 : k = 1 := by
    have hkpos : 0 < k := by
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · rw [hk0] at hgt
        exact absurd hgt (by norm_num)
      · exact hkpos
    have hkle : k ≤ 2 := by
      by_contra hk2
      have h2k : 2 ^ k ≤ 4 := by omega
      have h8 : 8 ≤ 2 ^ k := by
        calc 8 = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hkne : k ≠ 2 := by
      intro hk2
      apply hne
      rw [hk, hk2]
      norm_num
    omega
  have hidx : (Z.D.subgroupOf C).index = 2 := by
    rw [hk, hk1]
    norm_num
  have hcard : Nat.card (Z.D.subgroupOf C) = Nat.card Z.D :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDC).toEquiv
  calc
    Nat.card C = Nat.card (Z.D.subgroupOf C) * (Z.D.subgroupOf C).index :=
      (Subgroup.card_mul_index (Z.D.subgroupOf C)).symm
    _ = Nat.card Z.D * 2 := by rw [hcard, hidx]
    _ = 2 * Nat.card Z.D := Nat.mul_comm _ _

end CFSG.CGT.Stroth77
