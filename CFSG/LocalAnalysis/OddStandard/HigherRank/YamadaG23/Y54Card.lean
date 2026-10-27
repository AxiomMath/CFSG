module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y54Aut

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private theorem isCoatom_subgroupOf_of_isMaximalIn {Γ : Type} [Group Γ] {V M : Subgroup Γ}
    (h : IsMaximalIn V M) : IsCoatom (M.subgroupOf V) := by
  rw [isCoatom_iff_ge_of_le]
  refine ⟨?_, ?_⟩
  · intro htop
    apply h.1.2
    intro x hx
    have hmem : (⟨x, hx⟩ : ↥V) ∈ M.subgroupOf V := by rw [htop]; trivial
    exact Subgroup.mem_subgroupOf.mp hmem
  · intro K hKne hMK
    by_contra hKM
    obtain ⟨k, hkK, hkM⟩ := SetLike.not_le_iff_exists.mp hKM
    let N : Subgroup Γ := K.map V.subtype
    have hNV : N ≤ V := by
      rintro x ⟨y, -, rfl⟩
      exact y.2
    have hMN : M ≤ N := by
      intro m hm
      exact Subgroup.mem_map.mpr ⟨⟨m, h.1.1 hm⟩, hMK (Subgroup.mem_subgroupOf.mpr hm), rfl⟩
    have hkN : ((k : ↥V) : Γ) ∈ N := Subgroup.mem_map.mpr ⟨k, hkK, rfl⟩
    have hkM' : ((k : ↥V) : Γ) ∉ M := fun hm => hkM (Subgroup.mem_subgroupOf.mpr hm)
    have hlt : M < N := lt_of_le_of_ne hMN fun heq => hkM' (heq ▸ hkN)
    have hNVeq : N = V := h.2 N hlt hNV
    have hKN : N.subgroupOf V = K := by
      rw [← Subgroup.comap_subtype]
      exact K.comap_map_eq_self_of_injective Subtype.coe_injective
    exact hKne (by rw [← hKN, hNVeq, Subgroup.subgroupOf_self])

theorem y54_S_le_N {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    s.fr.S ≤ normIn L s.fr.F := by
  intro x hx
  refine Subgroup.mem_inf.mpr ⟨s3_S_le_L s hx, ?_⟩
  obtain ⟨hFn, -⟩ := hH.hLF.fact14.2.2.2.2.1.1
  have hFn' : (s.fr.F.subgroupOf s.fr.S).Normal := hFn
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer
    ((s3_F_le_A s).trans (s3_A_le_S s))).mp hFn' hx

theorem y54_card_S {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    Nat.card ↥s.fr.S = 64 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSN : s.fr.S ≤ normIn L s.fr.F := y54_S_le_N hH
  have hNL : normIn L s.fr.F ≤ L := inf_le_left
  have hodd : ¬ 2 ∣ s.fr.S.relIndex (normIn L s.fr.F) := by
    intro h2
    have hrel := Subgroup.relIndex_mul_relIndex (H := s.fr.S) (K := normIn L s.fr.F)
      (L := L) hSN hNL
    exact s.sylow_S.2.2 (hrel ▸ dvd_mul_of_dvd_left h2 (Subgroup.relIndex (normIn L s.fr.F) L))
  have hcardN : s.fr.S.relIndex (normIn L s.fr.F) * Nat.card ↥s.fr.S = 1344 := by
    have h := Subgroup.relIndex_mul_card (H := s.fr.S) (K := normIn L s.fr.F)
    rw [inf_of_le_left hSN, y54_card_N hH] at h
    exact h
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp (s3_isPGroup_S s)
  have hdvd64 : Nat.card ↥s.fr.S ∣ 64 := by
    have hdiv : Nat.card ↥s.fr.S ∣ 1344 :=
      ⟨_, by rw [mul_comm]; exact hcardN.symm⟩
    rw [hn] at hdiv ⊢
    have hcop : Nat.Coprime (2 ^ n) 21 := (show Nat.Coprime 2 21 by norm_num).pow_left n
    have h6 : 2 ^ n ∣ 2 ^ 6 := hcop.dvd_of_dvd_mul_right (by
      rwa [show (1344 : ℕ) = 2 ^ 6 * 21 by norm_num] at hdiv)
    rwa [show (64 : ℕ) = 2 ^ 6 by norm_num]
  have hdvdS : 64 ∣ Nat.card ↥s.fr.S := by
    have hcop : Nat.Coprime 64 (s.fr.S.relIndex (normIn L s.fr.F)) := by
      rw [show (64 : ℕ) = 2 ^ 6 by norm_num]
      exact (Nat.prime_two.coprime_iff_not_dvd.mpr hodd).pow_left 6
    have h64 : 64 ∣ s.fr.S.relIndex (normIn L s.fr.F) * Nat.card ↥s.fr.S := by
      rw [hcardN, show (1344 : ℕ) = 64 * 21 by norm_num]
      exact dvd_mul_right 64 21
    exact hcop.dvd_of_dvd_mul_left h64
  exact Nat.dvd_antisymm hdvd64 hdvdS

theorem y54_card_NS {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    Nat.card ↥(normIn L s.fr.F) = 21 * Nat.card ↥s.fr.S := by
  rw [y54_card_N hH, y54_card_S hH]

theorem y54_card_B {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    Nat.card ↥s.fr.B = 32 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmax : IsMaximalIn s.fr.S s.fr.B := hH.hLF.fact14.2.2.1.2.2.1
  have hBS : s.fr.B ≤ s.fr.S := s3_B_le_S s
  have hcoatom : IsCoatom (s.fr.B.subgroupOf s.fr.S) :=
    isCoatom_subgroupOf_of_isMaximalIn hmax
  haveI : Group.IsNilpotent ↥(s.fr.S) := (s3_isPGroup_S s).isNilpotent
  have hidx : s.fr.B.relIndex s.fr.S = 2 :=
    (IsPGroup.isCoatom_iff_index_eq_prime (p := 2) (s3_isPGroup_S s)).mp hcoatom
  have hcard := Subgroup.relIndex_mul_card (H := s.fr.B) (K := s.fr.S)
  rw [inf_of_le_left hBS, hidx, y54_card_S hH] at hcard
  omega

end CFSG.OddStandard.HigherRank.YamadaG23
