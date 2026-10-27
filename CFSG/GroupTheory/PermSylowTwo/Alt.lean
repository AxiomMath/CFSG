module

public import CFSG.GroupTheory.PermSylowTwo.AltCore

public section

namespace CFSG.GroupTheory.PermSylowTwo

open Equiv Equiv.Perm CFSG.QuasithinUnique

theorem map_alternatingGroup_permCongrHom {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (e : α ≃ β) :
    (alternatingGroup α).map e.permCongrHom.toMonoidHom = alternatingGroup β := by
  refine le_antisymm ?_ ?_
  · rintro σ ⟨τ, hτ, hτσ⟩
    rw [← hτσ]
    have hτ' : Equiv.Perm.sign τ = 1 := hτ
    show Equiv.Perm.sign (e.permCongr τ) = 1
    simpa using hτ'
  · intro σ hσ
    refine ⟨e.symm.permCongr σ, ?_, ?_⟩
    · have hσ' : Equiv.Perm.sign σ = 1 := hσ
      show Equiv.Perm.sign (e.symm.permCongr σ) = 1
      simpa using hσ'
    · ext x
      simp [Equiv.permCongr_apply]

theorem isSylowTwoOf_subgroupOf_top {G : Type*} [Group G] {S M : Subgroup G}
    (hS : IsSylowTwoOf S M) : IsSylowTwoOf (S.subgroupOf M) ⊤ := by
  refine ⟨le_top, IsPGroup.of_equiv hS.2.1 (Subgroup.subgroupOfEquivOfLe hS.1).symm, ?_⟩
  have h : ((S.subgroupOf M).subgroupOf (⊤ : Subgroup ↥M)).index = (S.subgroupOf M).index := by
    rw [← Subgroup.relIndex_top_right ((S.subgroupOf M).subgroupOf ⊤),
      ← Subgroup.relIndex_top_right (S.subgroupOf M)]
    have h2 := Subgroup.relIndex_subgroupOf (G := ↥M) (H := S.subgroupOf M) (K := ⊤) (L := ⊤)
      le_top
    rwa [Subgroup.subgroupOf_self] at h2
  rw [h]
  exact hS.2.2

variable {β γ : Type} [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]

theorem sign_pairSwap (b : β) : Equiv.Perm.sign (pairSwap β γ b) = -1 := by
  rw [show pairSwap β γ b = Equiv.swap (Sum.inl (b, false)) (Sum.inl (b, true)) from rfl,
    Equiv.Perm.sign_swap (x := Sum.inl (b, false)) (y := Sum.inl (b, true)) (by simp)]

theorem isPGroup_two_of_sylow_le_pairing [Subsingleton γ] (hβ : 3 ≤ Fintype.card β)
    {S H : Subgroup (Perm ((β × Bool) ⊕ γ))}
    (hS : IsSylowTwoOf S (alternatingGroup ((β × Bool) ⊕ γ)))
    (hSH : S ≤ H) (hHA : H ≤ alternatingGroup ((β × Bool) ⊕ γ))
    (h3 : ¬ 3 ∣ Nat.card H ∨ H ≤ Subgroup.normalizer (S : Set (Perm ((β × Bool) ⊕ γ)))) :
    IsPGroup 2 H := by
  classical
  obtain ⟨R, hR⟩ := exists_isSylowTwoOf_top (Perm β)
  let F : Subgroup (Perm ((β × Bool) ⊕ γ)) :=
    Subgroup.closure {x | ∃ b b', x = pairSwap β γ b * pairSwap β γ b'} ⊔
      R.map ((pairCent β γ).subtype.comp (pairLift β γ))
  have hFle : F ≤ pairSwaps β γ ⊔ R.map ((pairCent β γ).subtype.comp (pairLift β γ)) := by
    refine sup_le ?_ le_sup_right
    refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨b, b', rfl⟩
    exact Subgroup.mem_sup_left (mul_mem (pairSwap_mem_pairSwaps b) (pairSwap_mem_pairSwaps b'))
  have hF2 : IsPGroup 2 F := (isPGroup_two_pairSwaps_sup hR.2.1).to_le hFle
  have hFA : F ≤ alternatingGroup ((β × Bool) ⊕ γ) := by
    refine sup_le ?_ ?_
    · refine (Subgroup.closure_le _).2 ?_
      rintro x ⟨b, b', rfl⟩
      show Equiv.Perm.sign (pairSwap β γ b * pairSwap β γ b') = 1
      rw [Equiv.Perm.sign_mul, sign_pairSwap, sign_pairSwap, Int.units_mul_self]
    · rw [Subgroup.map_le_iff_le_comap]
      intro x _
      exact pairLift_mem_alternatingGroup (β := β) (γ := γ) x
  obtain ⟨g, hg, hFg⟩ := exists_mem_conj_ge hS hFA hF2
  have hconjA : (alternatingGroup ((β × Bool) ⊕ γ)).map (MulAut.conj g).toMonoidHom
      = alternatingGroup ((β × Bool) ⊕ γ) := Subgroup.conj_smul_eq_self_of_mem hg
  have hS' : IsSylowTwoOf (S.map (MulAut.conj g).toMonoidHom)
      (alternatingGroup ((β × Bool) ⊕ γ)) := by
    have h := isSylowTwoOf_map_mulEquiv (MulAut.conj g) hS
    rwa [hconjA] at h
  have hSH' : S.map (MulAut.conj g).toMonoidHom ≤ H.map (MulAut.conj g).toMonoidHom :=
    Subgroup.map_mono hSH
  have hHA' : H.map (MulAut.conj g).toMonoidHom ≤ alternatingGroup ((β × Bool) ⊕ γ) := by
    rw [← hconjA]
    exact Subgroup.map_mono hHA
  have h3' := map_cond_of_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective h3
  have hH' : IsPGroup 2 (H.map (MulAut.conj g).toMonoidHom) :=
    isPGroup_two_of_pairing_alt (β := β) (γ := γ) hβ hS'
      (fun b b' => hFg (Subgroup.mem_sup_left (Subgroup.subset_closure ⟨b, b', rfl⟩)))
      hR (le_sup_right.trans hFg) hSH' hHA' h3'
  exact isPGroup_two_of_map_mulEquiv (MulAut.conj g) hH'

theorem isPGroup_two_of_sylow_le_alt (α : Type) [Fintype α] [DecidableEq α]
    (hα : 6 ≤ Fintype.card α) {S H : Subgroup (Perm α)}
    (hS : IsSylowTwoOf S (alternatingGroup α)) (hSH : S ≤ H) (hHA : H ≤ alternatingGroup α)
    (h3 : ¬ 3 ∣ Nat.card H ∨ H ≤ Subgroup.normalizer (S : Set (Perm α))) : IsPGroup 2 H := by
  classical
  set m := Fintype.card α with hm
  have hβ : 3 ≤ m / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
    omega
  have hγ : m % 2 ≤ 1 := by
    rcases Nat.mod_two_eq_zero_or_one m with h | h <;> omega
  haveI : Subsingleton (Fin (m % 2)) := Fin.subsingleton_iff_le_one.2 hγ
  have hcard : Fintype.card α = Fintype.card ((Fin (m / 2) × Bool) ⊕ Fin (m % 2)) := by
    have hdm := Nat.div_add_mod m 2
    rw [← hm]
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]
    omega
  let e : α ≃ ((Fin (m / 2) × Bool) ⊕ Fin (m % 2)) := Fintype.equivOfCardEq hcard
  let ψ : Perm α ≃* Perm ((Fin (m / 2) × Bool) ⊕ Fin (m % 2)) := e.permCongrHom
  have hA : (alternatingGroup α).map ψ.toMonoidHom
      = alternatingGroup ((Fin (m / 2) × Bool) ⊕ Fin (m % 2)) :=
    map_alternatingGroup_permCongrHom e
  have hS' : IsSylowTwoOf (S.map ψ.toMonoidHom)
      (alternatingGroup ((Fin (m / 2) × Bool) ⊕ Fin (m % 2))) := by
    have h := isSylowTwoOf_map_mulEquiv ψ hS
    rwa [hA] at h
  have hSH' : S.map ψ.toMonoidHom ≤ H.map ψ.toMonoidHom := Subgroup.map_mono hSH
  have hHA' : H.map ψ.toMonoidHom
      ≤ alternatingGroup ((Fin (m / 2) × Bool) ⊕ Fin (m % 2)) := by
    rw [← hA]
    exact Subgroup.map_mono hHA
  have h3' := map_cond_of_injective (f := ψ.toMonoidHom) ψ.injective h3
  exact isPGroup_two_of_map_mulEquiv ψ
    (isPGroup_two_of_sylow_le_pairing (β := Fin (m / 2)) (γ := Fin (m % 2))
      (by simpa using hβ) hS' hSH' hHA' h3')

theorem isPGroup_two_of_isSylowTwoOf_of_mulEquiv_alt {G : Type*} [Group G] [Finite G]
    {M S H : Subgroup G} {n : ℕ} (hn : 6 ≤ n) (e : ↥M ≃* alternatingGroup (Fin n))
    (hS : IsSylowTwoOf S M) (hSH : S ≤ H) (hHM : H ≤ M)
    (h3 : ¬ 3 ∣ Nat.card H ∨ H ≤ Subgroup.normalizer (S : Set G)) : IsPGroup 2 H := by
  classical
  let f : ↥M →* Perm (Fin n) := (alternatingGroup (Fin n)).subtype.comp e.toMonoidHom
  have hf : Function.Injective f := fun x y hxy =>
    e.injective ((alternatingGroup (Fin n)).subtype_injective hxy)
  have htop : Subgroup.map f ⊤ = alternatingGroup (Fin n) := by
    have h1 : Subgroup.map e.toMonoidHom (⊤ : Subgroup ↥M) = ⊤ :=
      Subgroup.map_top_of_surjective e.toMonoidHom e.surjective
    have h2 : Subgroup.map (alternatingGroup (Fin n)).subtype
        (⊤ : Subgroup ↥(alternatingGroup (Fin n))) = alternatingGroup (Fin n) := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [show f = (alternatingGroup (Fin n)).subtype.comp e.toMonoidHom from rfl,
      ← Subgroup.map_map, h1, h2]
  have hS₁ : IsSylowTwoOf (Subgroup.map f (S.subgroupOf M)) (alternatingGroup (Fin n)) := by
    have h := isSylowTwoOf_map_of_injective hf (isSylowTwoOf_subgroupOf_top hS)
    rwa [htop] at h
  have hSH₁ : Subgroup.map f (S.subgroupOf M) ≤ Subgroup.map f (H.subgroupOf M) :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono M hSH)
  have hHA₁ : Subgroup.map f (H.subgroupOf M) ≤ alternatingGroup (Fin n) := by
    rintro x ⟨y, -, rfl⟩
    exact (e y).2
  have hcond : ¬ 3 ∣ Nat.card (Subgroup.map f (H.subgroupOf M)) ∨
      Subgroup.map f (H.subgroupOf M) ≤ Subgroup.normalizer
        ((Subgroup.map f (S.subgroupOf M) : Subgroup (Perm (Fin n))) : Set (Perm (Fin n))) := by
    rcases h3 with h3 | h3
    · refine Or.inl ?_
      rw [Subgroup.card_map_of_injective hf,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHM).toEquiv]
      exact h3
    · refine map_cond_of_injective (f := f) hf (Or.inr ?_)
      intro h hh
      rw [Subgroup.mem_normalizer_iff]
      intro x
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
        Subgroup.mem_normalizer_iff.mp (h3 hh)]
      simp
  have hH₁ : IsPGroup 2 (Subgroup.map f (H.subgroupOf M)) :=
    isPGroup_two_of_sylow_le_alt (Fin n) (by simpa using hn) hS₁ hSH₁ hHA₁ hcond
  exact IsPGroup.of_equiv
    (IsPGroup.of_equiv hH₁ (Subgroup.equivMapOfInjective (H.subgroupOf M) f hf).symm)
    (Subgroup.subgroupOfEquivOfLe hHM)

theorem le_of_isSylowTwoOf_of_mulEquiv_alt {G : Type*} [Group G] [Finite G] {M S H : Subgroup G}
    {n : ℕ} (hn : 6 ≤ n) (e : ↥M ≃* alternatingGroup (Fin n)) (hS : IsSylowTwoOf S M)
    (hSH : S ≤ H) (hHM : H ≤ M) (h3 : ¬ 3 ∣ Nat.card H) : H ≤ S :=
  le_of_isSylowTwoOf_of_isPGroup hS hSH hHM
    (isPGroup_two_of_isSylowTwoOf_of_mulEquiv_alt hn e hS hSH hHM (Or.inl h3))

theorem inf_normalizer_le_of_mulEquiv_alt {G : Type*} [Group G] [Finite G] {M S : Subgroup G}
    {n : ℕ} (hn : 6 ≤ n) (e : ↥M ≃* alternatingGroup (Fin n)) (hS : IsSylowTwoOf S M) :
    M ⊓ Subgroup.normalizer (S : Set G) ≤ S :=
  le_of_isSylowTwoOf_of_isPGroup hS (le_inf hS.1 Subgroup.le_normalizer) inf_le_left
    (isPGroup_two_of_isSylowTwoOf_of_mulEquiv_alt hn e hS (le_inf hS.1 Subgroup.le_normalizer)
      inf_le_left (Or.inr inf_le_right))

end CFSG.GroupTheory.PermSylowTwo
