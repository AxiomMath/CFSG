module

public import CFSG.GroupTheory.PermSylowTwo.Preserve
public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG.GroupTheory.PermSylowTwo

open Equiv Equiv.Perm CFSG.QuasithinUnique

variable {β γ : Type} [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]

theorem not_three_dvd_card_of_isPGroup_two {G : Type*} [Group G] [Finite G] {K : Subgroup G}
    (hK : IsPGroup 2 K) : ¬ 3 ∣ Nat.card K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hK.exists_card_eq
  rw [hk]
  intro h3
  have h32 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
  omega

theorem le_of_isSylowTwoOf_of_isPGroup {G : Type*} [Group G] [Finite G] {S H M : Subgroup G}
    (hS : IsSylowTwoOf S M) (hSH : S ≤ H) (hHM : H ≤ M) (hH : IsPGroup 2 H) : H ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSsub : IsPGroup 2 (S.subgroupOf M) :=
    hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
  have hHsub : IsPGroup 2 (H.subgroupOf M) :=
    hH.of_equiv (Subgroup.subgroupOfEquivOfLe hHM).symm
  let S' : Sylow 2 ↥M := hSsub.toSylow hS.2.2
  have hS'coe : (S' : Subgroup ↥M) = S.subgroupOf M := IsPGroup.toSylow_coe hSsub hS.2.2
  have hEq : H.subgroupOf M = S.subgroupOf M := by
    have hmax := S'.is_maximal' hHsub (by rw [hS'coe]; exact Subgroup.subgroupOf_mono M hSH)
    rwa [hmax, hS'coe]
  intro x hx
  have hx' : (⟨x, hHM hx⟩ : ↥M) ∈ H.subgroupOf M := Subgroup.mem_subgroupOf.mpr hx
  rw [hEq] at hx'
  exact Subgroup.mem_subgroupOf.mp hx'

theorem isPGroup_two_pairSwaps_sup {R : Subgroup (Perm β)} (hR : IsPGroup 2 R) :
    IsPGroup 2 ↥(pairSwaps β γ ⊔ R.map ((pairCent β γ).subtype.comp (pairLift β γ))) := by
  let f : Perm β →* Perm ((β × Bool) ⊕ γ) := (pairCent β γ).subtype.comp (pairLift β γ)
  have hR' : IsPGroup 2 (R.map f) := hR.map f
  have hle : R.map f ≤ Subgroup.normalizer (pairSwaps β γ) := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨r, -, rfl⟩
    exact pairLift_mem_normalizer_pairSwaps r
  have hsup := IsPGroup.to_sup_of_normal_left'
    (isPGroup_two_pairSwaps : IsPGroup 2 ↥(pairSwaps β γ)) hR' hle
  simpa [f] using hsup

theorem isSylowTwoOf_map_pairHom {P : Subgroup (Perm ((β × Bool) ⊕ γ))} (hP : IsPGroup 2 P)
    {R : Subgroup (Perm β)} (hR : IsSylowTwoOf R ⊤)
    (hRP : R.map ((pairCent β γ).subtype.comp (pairLift β γ)) ≤ P) :
    IsSylowTwoOf ((P.subgroupOf (pairCent β γ)).map (pairHom β γ)) ⊤ := by
  have hP₀ : ∀ r ∈ R, pairLift β γ r ∈ P.subgroupOf (pairCent β γ) := by
    intro r hr
    refine Subgroup.mem_subgroupOf.mpr ?_
    simpa using hRP (Subgroup.mem_map_of_mem
      ((pairCent β γ).subtype.comp (pairLift β γ)) hr)
  have hRle : R ≤ (P.subgroupOf (pairCent β γ)).map (pairHom β γ) := by
    intro r hr
    have hmem := Subgroup.mem_map_of_mem (pairHom β γ) (hP₀ r hr)
    simpa [pairHom_pairLift] using hmem
  have hPC : IsPGroup 2 (P ⊓ pairCent β γ : Subgroup (Perm ((β × Bool) ⊕ γ))) :=
    IsPGroup.to_le (K := P) hP
      (show (P ⊓ pairCent β γ : Subgroup (Perm ((β × Bool) ⊕ γ))) ≤ P from
        fun x hx => (Subgroup.mem_inf.mp hx).1)
  have hP₀' : IsPGroup 2 ((P ⊓ pairCent β γ).subgroupOf (pairCent β γ)) :=
    hPC.of_equiv (Subgroup.subgroupOfEquivOfLe
      (show (P ⊓ pairCent β γ : Subgroup (Perm ((β × Bool) ⊕ γ))) ≤ pairCent β γ from
        fun x hx => (Subgroup.mem_inf.mp hx).2)).symm
  have hP₁ : IsPGroup 2 ((P.subgroupOf (pairCent β γ)).map (pairHom β γ)) := by
    have h := hP₀'.map (pairHom β γ)
    rwa [Subgroup.inf_subgroupOf_right] at h
  have hEq : (P.subgroupOf (pairCent β γ)).map (pairHom β γ) = R :=
    le_antisymm (le_of_isSylowTwoOf_of_isPGroup hR hRle le_top hP₁) hRle
  refine ⟨le_top, hP₁, ?_⟩
  rw [hEq]
  exact hR.2.2

theorem map_pairHom_cond {P H : Subgroup (Perm ((β × Bool) ⊕ γ))} (hHC : H ≤ pairCent β γ)
    (h3 : ¬ 3 ∣ Nat.card H ∨ H ≤ Subgroup.normalizer (P : Set (Perm ((β × Bool) ⊕ γ)))) :
    ¬ 3 ∣ Nat.card ((H.subgroupOf (pairCent β γ)).map (pairHom β γ)) ∨
      (H.subgroupOf (pairCent β γ)).map (pairHom β γ) ≤
        Subgroup.normalizer (((P.subgroupOf (pairCent β γ)).map (pairHom β γ) :
          Subgroup (Perm β)) : Set (Perm β)) := by
  rcases h3 with h3 | hN
  · left
    intro hdiv
    have hdvd : 3 ∣ Nat.card (H.subgroupOf (pairCent β γ)) :=
      hdiv.trans (Subgroup.card_map_dvd (H.subgroupOf (pairCent β γ)) (pairHom β γ))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHC).toEquiv] at hdvd
    exact h3 hdvd
  · right
    refine Subgroup.le_normalizer_iff.mpr ?_
    intro x hx p hp
    rcases Subgroup.mem_map.mp hx with ⟨h, hh, rfl⟩
    rcases Subgroup.mem_map.mp hp with ⟨p₀, hp₀, rfl⟩
    have hconj : (h : Perm ((β × Bool) ⊕ γ)) * (p₀ : Perm ((β × Bool) ⊕ γ)) *
        (h : Perm ((β × Bool) ⊕ γ))⁻¹ ∈ P :=
      (Subgroup.le_normalizer_iff.mp hN) (h : Perm ((β × Bool) ⊕ γ))
        (Subgroup.mem_subgroupOf.mp hh) (p₀ : Perm ((β × Bool) ⊕ γ))
        (Subgroup.mem_subgroupOf.mp hp₀)
    rw [← map_mul, ← map_inv, ← map_mul]
    refine Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr ?_)
    simpa using hconj

theorem isPGroup_two_of_le_pairCent [Subsingleton γ] {H : Subgroup (Perm ((β × Bool) ⊕ γ))}
    (hHC : H ≤ pairCent β γ)
    (h1 : IsPGroup 2 ((H.subgroupOf (pairCent β γ)).map (pairHom β γ))) : IsPGroup 2 H := by
  intro x
  let x' : ↥(pairCent β γ) := ⟨x, hHC x.2⟩
  have hx' : x' ∈ H.subgroupOf (pairCent β γ) := Subgroup.mem_subgroupOf.mpr x.2
  obtain ⟨a, ha⟩ :=
    h1 ⟨pairHom β γ x', Subgroup.mem_map_of_mem (pairHom β γ) hx'⟩
  refine ⟨a + 1, ?_⟩
  have ha' : (pairHom β γ x') ^ 2 ^ a = 1 := by
    have := congrArg (fun z : ↥((H.subgroupOf (pairCent β γ)).map (pairHom β γ)) =>
      (z : Perm β)) ha
    simpa using this
  have hmap : pairHom β γ (x' ^ 2 ^ a) = 1 := by rw [map_pow, ha']
  have hsq : (x' ^ 2 ^ a) ^ 2 = 1 := sq_eq_one_of_pairHom_eq_one hmap
  have hval : (((x : Perm ((β × Bool) ⊕ γ)) ^ 2 ^ a) ^ 2) = 1 := by
    have := congrArg (fun z : ↥(pairCent β γ) => (z : Perm ((β × Bool) ⊕ γ))) hsq
    simpa using this
  have hx : x ^ 2 ^ (a + 1) = (x ^ 2 ^ a) ^ 2 := by rw [pow_succ, pow_mul]
  rw [hx]
  apply Subtype.ext
  simpa using hval

theorem isPGroup_two_of_pairing [Subsingleton γ]
    (ih : ∀ P' H' : Subgroup (Perm β), IsSylowTwoOf P' ⊤ → P' ≤ H' →
      (¬ 3 ∣ Nat.card H' ∨ H' ≤ Subgroup.normalizer (P' : Set (Perm β))) → IsPGroup 2 H')
    {P H : Subgroup (Perm ((β × Bool) ⊕ γ))} (hP : IsSylowTwoOf P ⊤) (hsw : pairSwaps β γ ≤ P)
    {R : Subgroup (Perm β)} (hR : IsSylowTwoOf R ⊤)
    (hRP : R.map ((pairCent β γ).subtype.comp (pairLift β γ)) ≤ P) (hPH : P ≤ H)
    (h3 : ¬ 3 ∣ Nat.card H ∨ H ≤ Subgroup.normalizer (P : Set (Perm ((β × Bool) ⊕ γ)))) :
    IsPGroup 2 H := by
  have hHC : H ≤ pairCent β γ := by
    intro h hh
    rcases h3 with h3' | hN
    · exact mem_pairCent_of_swaps h3'
        (fun b => hPH (hsw (pairSwap_mem_pairSwaps b)))
        (fun b => H.mul_mem (H.mul_mem hh (hPH (hsw (pairSwap_mem_pairSwaps b))))
          (H.inv_mem hh))
    · refine mem_pairCent_of_swaps (not_three_dvd_card_of_isPGroup_two hP.2.1)
        (fun b => hsw (pairSwap_mem_pairSwaps b)) (fun b => ?_)
      exact (Subgroup.mem_normalizer_iff.mp (hN hh) (pairSwap β γ b)).mp
        (hsw (pairSwap_mem_pairSwaps b))
  have hH₁ : IsPGroup 2 ((H.subgroupOf (pairCent β γ)).map (pairHom β γ)) :=
    ih ((P.subgroupOf (pairCent β γ)).map (pairHom β γ))
      ((H.subgroupOf (pairCent β γ)).map (pairHom β γ))
      (isSylowTwoOf_map_pairHom hP.2.1 hR hRP)
      (Subgroup.map_mono (Subgroup.subgroupOf_mono (pairCent β γ) hPH))
      (map_pairHom_cond hHC h3)
  exact isPGroup_two_of_le_pairCent hHC hH₁

end CFSG.GroupTheory.PermSylowTwo
