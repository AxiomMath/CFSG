module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Shapes

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

private lemma s7_card_alt_inf_centralizer (α : Type*) [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (hodd : Equiv.Perm.sign σ = -1) :
    Nat.card ↥(alternatingGroup α ⊓
        Subgroup.centralizer ({σ} : Set (Equiv.Perm α))) * 2 =
      Nat.card ↥(Subgroup.centralizer ({σ} : Set (Equiv.Perm α))) := by
  classical
  let A : Subgroup (Equiv.Perm α) := alternatingGroup α
  let C : Subgroup (Equiv.Perm α) := Subgroup.centralizer ({σ} : Set (Equiv.Perm α))
  change Nat.card ↥(A ⊓ C) * 2 = Nat.card ↥C
  have hσC : σ ∈ C := by
    change σ ∈ Subgroup.centralizer ({σ} : Set (Equiv.Perm α))
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
  let f : C →* ℤˣ := Equiv.Perm.sign.comp C.subtype
  have hker : f.ker = A.subgroupOf C := by
    ext x
    simp [f, A, MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Equiv.Perm.mem_alternatingGroup]
  have hrange : f.range = ⊤ := by
    rw [MonoidHom.range_eq_top]
    intro u
    rcases Int.units_eq_one_or u with h | h
    · exact ⟨1, by simp [f, h]⟩
    · exact ⟨⟨σ, hσC⟩, by simp [f, h, hodd]⟩
  have hidx : f.ker.index = 2 := by
    rw [Subgroup.index_ker, hrange, Subgroup.card_top, Nat.card_eq_fintype_card,
      Fintype.card_units_int]
  have hcardC : Nat.card ↥f.ker * 2 = Nat.card ↥C := by
    have h := Subgroup.card_mul_index (H := f.ker)
    rw [hidx] at h
    exact h
  have hsub : (A ⊓ C).subgroupOf C = A.subgroupOf C := by
    ext x
    simp [A, C, Subgroup.mem_subgroupOf]
  have hcardA : Nat.card ↥(A.subgroupOf C) = Nat.card ↥(A ⊓ C) := by
    rw [← hsub]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : A ⊓ C ≤ C)).toEquiv
  rw [← hcardA, ← hker]
  exact hcardC

theorem s7_sym8_cycleType_of_card {σ : Sym 8} (hσ : σ ^ 2 = 1) (hodd : Equiv.Perm.sign σ = -1)
    (hcard : Nat.card ↥(alternatingGroup (Fin 8) ⊓
      Subgroup.centralizer ({σ} : Set (Sym 8))) = 720) : σ.cycleType = {2} := by
  classical
  have hct : σ.cycleType = Multiset.replicate σ.cycleType.card 2 :=
    Equiv.Perm.cycleType_of_pow_prime_eq_one hσ
  have hsum : σ.cycleType.sum = 2 * σ.cycleType.card := by
    conv_lhs => rw [hct]
    rw [Multiset.sum_replicate]
    ring
  have hle : 2 * σ.cycleType.card ≤ 8 := by
    have h := σ.sum_cycleType_le
    rw [hsum, Fintype.card_fin] at h
    exact h
  have hne : σ ≠ 1 := by
    intro h1
    rw [h1, Equiv.Perm.sign_one] at hodd
    exact (by decide : (1 : ℤˣ) ≠ -1) hodd
  have hpos : 0 < σ.cycleType.card := Equiv.Perm.card_cycleType_pos.mpr hne
  have hoddk : Odd σ.cycleType.card := by
    have hsign : (-1 : ℤˣ) ^ (σ.cycleType.sum + σ.cycleType.card) = -1 := by
      rw [← Equiv.Perm.sign_of_cycleType σ, hodd]
    have h3 : σ.cycleType.sum + σ.cycleType.card = 3 * σ.cycleType.card := by
      rw [hsum]; ring
    rw [h3] at hsign
    exact Nat.Odd.of_mul_right ((neg_one_pow_eq_neg_one_iff_odd (by decide)).mp hsign)
  have hk : σ.cycleType.card = 1 ∨ σ.cycleType.card = 3 := by
    obtain ⟨m, hm⟩ := hoddk
    omega
  rcases hk with hk | hk
  · rw [hct, hk]
    decide
  · exfalso
    have hct3 : σ.cycleType = {2, 2, 2} := by
      rw [hct, hk]
      decide
    have hcent : Nat.card ↥(Subgroup.centralizer ({σ} : Set (Sym 8))) = 96 := by
      rw [Equiv.Perm.nat_card_centralizer σ, hct3]
      decide
    have h2 := s7_card_alt_inf_centralizer (Fin 8) σ hodd
    rw [hcard, hcent] at h2
    norm_num at h2

end CFSG.EvenSporadicStandard.HNRecog.Section3
