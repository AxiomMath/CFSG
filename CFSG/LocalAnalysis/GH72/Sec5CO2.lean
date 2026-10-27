module

public import CFSG.LocalAnalysis.GH72.Sec5CTools

public section

namespace CFSG.GH72

open Subgroup CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

theorem mem_of_odd_orderOf_of_sup_eq_top {Γ : Type*} [Group Γ] [Finite Γ] {S H : Subgroup Γ}
    (hS : IsPGroup 2 S) (hSH : S ⊓ H = ⊥) (htop : S ⊔ H = ⊤)
    (hHS : H ≤ centralizer (S : Set Γ)) {g : Γ} (hg : Odd (orderOf g)) : g ∈ H := by
  have hSN : S ≤ normalizer (H : Set Γ) :=
    (le_centralizer_iff.mp hHS).trans (centralizer_le_normalizer _)
  have hg' : g ∈ ((S ⊔ H : Subgroup Γ) : Set Γ) := by rw [htop]; trivial
  rw [coe_mul_of_left_le_normalizer_right S H hSN] at hg'
  obtain ⟨s, hs, h, hh, rfl⟩ := Set.mem_mul.mp hg'
  have hc : Commute s h := (mem_centralizer_iff.mp (hHS hh) s hs)
  set m := orderOf (s * h) with hm
  have h1 : s ^ m * h ^ m = 1 := by
    rw [← hc.mul_pow]
    exact pow_orderOf_eq_one _
  have h2 : s ^ m ∈ S ⊓ H := by
    refine ⟨S.pow_mem hs m, ?_⟩
    rw [eq_inv_of_mul_eq_one_left h1]
    exact H.inv_mem (H.pow_mem hh m)
  rw [hSH, mem_bot] at h2
  obtain ⟨k, hk⟩ := hS ⟨s, hs⟩
  have hs2 : s ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hs1 : s = 1 :=
    (pow_eq_one_iff_of_coprime ((Nat.coprime_two_left.mpr hg).pow_left k)).mp ⟨hs2, h2⟩
  rw [hs1, one_mul]
  exact hh

theorem exists_mul_mem_normalizer_of_map_conj_le {T O : Subgroup G} (hT : IsPGroup 2 T)
    (hO : Odd (Nat.card O)) (hTO : T ≤ normalizer (O : Set G)) {n : G}
    (hn : T.map (MulAut.conj n).toMonoidHom ≤ O ⊔ T) :
    ∃ o ∈ O, o * n ∈ normalizer (T : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsyl : IsSylowOf 2 T (O ⊔ T) := by
    rw [isSylowOf_iff]
    refine ⟨le_sup_right, hT, ?_⟩
    rw [CFSG.ABGTheoremB.relIndex_sup_eq_relIndex_of_le_normalizer hTO]
    intro h2
    exact (Nat.not_even_iff_odd.mpr hO) (even_iff_two_dvd.mpr (h2.trans (index_dvd_card _)))
  obtain ⟨c, hc, hcT⟩ := exists_mem_map_conj_le_of_isSylowOf hsyl hn (hT.map _)
  have hcn : c * n ∈ normalizer (T : Set G) := by
    apply mem_normalizer_of_map_conj_le
    have e : (MulAut.conj (c * n)).toMonoidHom =
        (MulAut.conj c).toMonoidHom.comp (MulAut.conj n).toMonoidHom := by
      ext y
      simp [mul_assoc]
    rw [e, ← map_map]
    exact hcT
  have hc' : c ∈ ((T ⊔ O : Subgroup G) : Set G) := by rw [sup_comm]; exact hc
  rw [coe_mul_of_left_le_normalizer_right T O hTO] at hc'
  obtain ⟨t, ht, o, ho, rfl⟩ := Set.mem_mul.mp hc'
  refine ⟨o, ho, ?_⟩
  have e : o * n = t⁻¹ * (t * o * n) := by group
  rw [e]
  exact mul_mem (inv_mem (le_normalizer ht)) hcn

end CFSG.GH72
