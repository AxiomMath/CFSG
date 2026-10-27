module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7L771K

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec7l771_AC [Finite G] {K A : Subgroup G} {s : G}
    (hcyc : ∀ P : Subgroup G, IsSylow2Of P (centralizer (K : Set G)) → IsCyclic P)
    (hAc : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a) (hA2 : ∀ a ∈ A, a * a = 1)
    (hsA : s ∈ A) (hs : s ∈ centralizer (K : Set G)) (hs2 : orderOf s = 2) :
    Nat.card ↥(A ⊓ centralizer (K : Set G)) = 2 := by
  have hset : (A ⊓ centralizer (K : Set G) : Subgroup G) = Subgroup.zpowers s := by
    apply le_antisymm
    · intro x hx
      rw [Subgroup.mem_inf] at hx
      obtain ⟨hxA, hxC⟩ := hx
      rw [Subgroup.mem_zpowers_iff]
      rcases eq_one_or_eq_of_commute hcyc hxC hs (hA2 x hxA) hs2 (hAc x hxA s hsA) with h1 | h1
      · exact ⟨0, by rw [h1]; simp⟩
      · exact ⟨1, by rw [h1]; simp⟩
    · exact Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨hsA, hs⟩)
  rw [hset, Nat.card_zpowers, hs2]

theorem sec7l771_D_le_A_b [Finite G] {K A E : Subgroup G} {s : G}
    (hZ : K ⊓ centralizer (K : Set G) = ⊥)
    (hcyc : ∀ P : Subgroup G, IsSylow2Of P (centralizer (K : Set G)) → IsCyclic P)
    (hAc : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a) (hA2 : ∀ a ∈ A, a * a = 1)
    (hsA : s ∈ A) (hs : s ∈ centralizer (K : Set G)) (hs2 : orderOf s = 2)
    (hAK : ∀ a ∈ A, a ∈ normalizer (K : Set G)) (hAE : ∀ a ∈ A, ∀ e ∈ E, a * e = e * a)
    (hX : (centralizer (K : Set G)).relIndex
      (normalizer (K : Set G) ⊓ centralizer (E : Set G)) ≤ 32)
    (hA : 64 ≤ Nat.card A) : K ⊓ centralizer (E : Set G) ≤ A := by
  have hAC2 : Nat.card ↥(A ⊓ centralizer (K : Set G)) = 2 :=
    sec7l771_AC hcyc hAc hA2 hsA hs hs2
  have hAX : A ≤ normalizer (K : Set G) ⊓ centralizer (E : Set G) := by
    intro a ha
    exact Subgroup.mem_inf.mpr
      ⟨hAK a ha, Subgroup.mem_centralizer_iff.mpr fun e he => (hAE a ha e he).symm⟩
  have hcount := sec7l771_count (C := centralizer (K : Set G))
    (X := normalizer (K : Set G) ⊓ centralizer (E : Set G)) (A := A) hAX hX hA hAC2
  intro d hd
  rw [Subgroup.mem_inf] at hd
  obtain ⟨hdK, hdE⟩ := hd
  have hdX : d ∈ normalizer (K : Set G) ⊓ centralizer (E : Set G) :=
    Subgroup.mem_inf.mpr ⟨Subgroup.le_normalizer hdK, hdE⟩
  obtain ⟨a, ha, c, hc, hdac⟩ := hcount d hdX
  exact sec7l771_mem_A hZ hcyc hAc hA2 hsA hs hs2 ha hdK
    ((centralizer (K : Set G)).inv_mem hc) (by rw [hdac]; group)

private theorem sec7l771_N_eq {K A D : Subgroup G}
    (hAK : ∀ a ∈ A, a ∈ normalizer (K : Set G))
    (hAD : ∀ a ∈ A, ∀ d ∈ D, a * d = d * a)
    (hDA : D ≤ A) (hDK : D ≤ K) (hinf : ∀ a ∈ A, a ∈ K → a ∈ D)
    (hKD : ∀ x ∈ K, (∀ d ∈ D, x * d = d * x) → x ∈ D) :
    K ⊓ normalizer (A : Set G) = K ⊓ normalizer (D : Set G) := by
  have H : ∀ x ∈ K, x ∈ normalizer (D : Set G) → ∀ a ∈ A, x * a * x⁻¹ ∈ A := by
    intro x hxK hxD a ha
    have hcK : (x * a * x⁻¹) * a⁻¹ ∈ K := by
      rw [show (x * a * x⁻¹) * a⁻¹ = x * (a * x⁻¹ * a⁻¹) by group]
      exact K.mul_mem hxK
        ((Subgroup.mem_normalizer_iff.mp (hAK a ha) x⁻¹).mp (K.inv_mem hxK))
    have hcComm : ∀ d ∈ D,
        ((x * a * x⁻¹) * a⁻¹) * d = d * ((x * a * x⁻¹) * a⁻¹) := by
      intro d hd
      have hd' : x⁻¹ * d * x ∈ D := (Subgroup.mem_normalizer_iff''.mp hxD d).mp hd
      have hcomm_ad : Commute a d := hAD a ha d hd
      have h1 : Commute (x * a * x⁻¹) d := by
        show (x * a * x⁻¹) * d = d * (x * a * x⁻¹)
        calc (x * a * x⁻¹) * d = x * (a * (x⁻¹ * d * x)) * x⁻¹ := by group
          _ = x * ((x⁻¹ * d * x) * a) * x⁻¹ := by
                rw [hAD a ha (x⁻¹ * d * x) hd']
          _ = d * (x * a * x⁻¹) := by group
      exact h1.mul_left hcomm_ad.inv_left
    have hcD : (x * a * x⁻¹) * a⁻¹ ∈ D := hKD _ hcK hcComm
    have hcA : (x * a * x⁻¹) * a⁻¹ ∈ A := hDA hcD
    have hmem : ((x * a * x⁻¹) * a⁻¹) * a ∈ A := A.mul_mem hcA ha
    rwa [show ((x * a * x⁻¹) * a⁻¹) * a = x * a * x⁻¹ by group] at hmem
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_inf] at hx ⊢
    obtain ⟨hxK, hxA⟩ := hx
    refine ⟨hxK, ?_⟩
    rw [Subgroup.mem_normalizer_iff]
    intro d
    constructor
    · intro hd
      exact hinf (x * d * x⁻¹)
        ((Subgroup.mem_normalizer_iff.mp hxA d).mp (hDA hd))
        (K.mul_mem (K.mul_mem hxK (hDK hd)) (K.inv_mem hxK))
    · intro hd
      exact hinf d ((Subgroup.mem_normalizer_iff.mp hxA d).mpr (hDA hd)) (by
        rw [show d = x⁻¹ * (x * d * x⁻¹) * x by group]
        exact K.mul_mem (K.mul_mem (K.inv_mem hxK) (hDK hd)) hxK)
  · intro x hx
    rw [Subgroup.mem_inf] at hx ⊢
    obtain ⟨hxK, hxD⟩ := hx
    refine ⟨hxK, ?_⟩
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · exact H x hxK hxD a
    · intro ha
      have h := H x⁻¹ (K.inv_mem hxK) ((normalizer (D : Set G)).inv_mem hxD)
        (x * a * x⁻¹) ha
      rw [inv_inv] at h
      rwa [show x⁻¹ * (x * a * x⁻¹) * x = a by group] at h

theorem sec7l771_conclude {K A D : Subgroup G}
    (hAK : ∀ a ∈ A, a ∈ normalizer (K : Set G))
    (hAD : ∀ a ∈ A, ∀ d ∈ D, a * d = d * a)
    (hDA : D ≤ A) (hDK : D ≤ K) (hinf : ∀ a ∈ A, a ∈ K → a ∈ D)
    (hKD : ∀ x ∈ K, (∀ d ∈ D, x * d = d * x) → x ∈ D)
    (hD : IsElemAb2 D 4)
    (hS5 : QuotEquivTo (K ⊓ normalizer (D : Set G)) D (Equiv.Perm (Fin 5))) :
    IsElemAb2 (A ⊓ K) 4 ∧
      QuotEquivTo (K ⊓ normalizer (A : Set G)) (K ⊓ A) (Equiv.Perm (Fin 5)) := by
  have hAD' : A ⊓ K = D := by
    apply le_antisymm
    · intro a ha
      exact hinf a (Subgroup.mem_inf.mp ha).1 (Subgroup.mem_inf.mp ha).2
    · exact le_inf hDA hDK
  constructor
  · rw [hAD']; exact hD
  · rw [sec7l771_N_eq (K := K) (A := A) (D := D) hAK hAD hDA hDK hinf hKD,
      inf_comm K A, hAD']
    exact hS5

end CFSG.OddStandard.SmallF3.Omega
