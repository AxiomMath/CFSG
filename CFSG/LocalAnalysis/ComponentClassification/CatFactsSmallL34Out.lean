module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog5L34
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourAutomorphisms
public import CFSG.GH74.KGroups.Cover

public section

namespace CFSG.ComponentClassification.CatFactsSmall

open CFSG.GH74.KGroups CFSG.ComponentClassification.GSThmB Subgroup
open scoped commutatorElement

theorem nonempty_equiv_psl34_of_lieModel {X : Type} [Group X]
    (h : Blueprint.LieModel X .PSL 3 2 2) : Nonempty (X ≃* PSL3Four.S) := by
  have hst : Assembly.LowTwoRank.StatedClassicalModel X .PSL 3 2 2 := by
    rcases h with ⟨-, h⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact h
    all_goals omega
  exact PSL3Four.exact_model.2.2.2.1 X hst

theorem comm_of_isPGroup_two_of_card_twelve {Q : Type*} [Group Q] (hQ : Nat.card Q = 12)
    (H : Subgroup Q) (hH : IsPGroup 2 H) : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite Q := Nat.finite_of_card_ne_zero (by rw [hQ]; norm_num)
  obtain ⟨k, hk⟩ := hH.exists_card_eq
  have hdvd : 2 ^ k ∣ 12 := hk ▸ hQ ▸ card_subgroup_dvd_card H
  have hk2 : k ≤ 2 := by
    by_contra hlt
    have h8 : 2 ^ 3 ∣ 12 := (pow_dvd_pow 2 (by omega)).trans hdvd
    norm_num at h8
  intro a ha b hb
  have key : (⟨a, ha⟩ : H) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨a, ha⟩ := by
    rcases (show k = 2 ∨ k ≤ 1 by omega) with rfl | hk1
    · exact (IsPGroup.isMulCommutative_of_card_eq_prime_sq hk).is_comm.comm _ _
    · have hc : IsCyclic H := isCyclic_of_card_dvd_prime (p := 2)
        (hk ▸ pow_dvd_pow 2 hk1 |>.trans (by norm_num))
      exact (IsCyclic.isMulCommutative (α := H)).is_comm.comm _ _
  exact congrArg Subtype.val key

variable {Y : Type} [Group Y]

theorem mem_range_conj_of_inducedHom (hY : Group.IsPerfect Y) (φ : MulAut Y)
    (h : inducedHom φ ∈ (MulAut.conj : Y ⧸ center Y →* MulAut (Y ⧸ center Y)).range) :
    φ ∈ (MulAut.conj : Y →* MulAut Y).range := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective c
  refine ⟨y, inducedHom_injective hY ?_⟩
  rw [← hc]
  ext x
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  rfl

theorem cfL34CoverOut : CFL34CoverOut := by
  intro Y _ _ hperf _ hL R' hR' u hu v hv
  obtain ⟨ψ⟩ := nonempty_equiv_psl34_of_lieModel hL
  obtain ⟨eR, -, hinn⟩ := PSL3Four.full_automorphism_action
  let f : MulAut Y →* PSL3Four.R :=
    eR.symm.toMonoidHom.comp ((MulAut.congr ψ).toMonoidHom.comp inducedHom)
  let N : Subgroup PSL3Four.R := PSL3Four.S.subgroupOf PSL3Four.R
  have : N.Normal := PSL3Four.S_normal
  have hN : Nat.card N = 20160 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe PSL3Four.S_le_R).toEquiv, PSL3Four.card_S]
  have hQ : Nat.card (PSL3Four.R ⧸ N) = 12 := by
    have h := card_eq_card_quotient_mul_card_subgroup N
    rw [PSL3Four.card_R, hN] at h
    omega
  let q : PSL3Four.R →* PSL3Four.R ⧸ N := QuotientGroup.mk' N
  have hcomm := comm_of_isPGroup_two_of_card_twelve hQ (R'.map (q.comp f))
    (hR'.map (q.comp f)) _ (mem_map_of_mem _ hu) _ (mem_map_of_mem _ hv)
  have hq : q.comp f ⁅u, v⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm
  have hmemN : f ⁅u, v⁆ ∈ N := (QuotientGroup.eq_one_iff _).1 hq
  have hinner : eR (f ⁅u, v⁆) ∈ (MulAut.conj : PSL3Four.S →* MulAut PSL3Four.S).range := by
    rw [← hinn]
    exact mem_map_of_mem _ hmemN
  have hf : eR (f ⁅u, v⁆) = MulAut.congr ψ (inducedHom ⁅u, v⁆) := by
    simp [f]
  rw [hf] at hinner
  obtain ⟨s, hs⟩ := hinner
  refine mem_range_conj_of_inducedHom hperf _ ⟨ψ.symm s, ?_⟩
  apply (MulAut.congr ψ).injective
  rw [← hs]
  ext x
  simp [MulAut.congr_apply]

end CFSG.ComponentClassification.CatFactsSmall
