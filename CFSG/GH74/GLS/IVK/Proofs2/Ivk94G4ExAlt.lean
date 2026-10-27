module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk94G4Assembly

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk94

open scoped MatrixGroups

theorem perfect_hom_perm_eq_one {G X : Type*} [Group G] [Group.IsPerfect G] [Finite X]
    (hX : Nat.card X ≤ 4) (φ : G →* Equiv.Perm X) (g : G) : φ g = 1 := by
  have : Group.IsPerfect φ.range := Group.IsPerfect.range φ
  have : Group.IsSolvable (Equiv.Perm X) := Equiv.Perm.isSolvable hX
  by_contra hne
  have : Nontrivial φ.range := ⟨⟨⟨φ g, g, rfl⟩, 1, fun h => hne (congrArg Subtype.val h)⟩⟩
  exact Group.IsPerfect.not_isSolvable φ.range inferInstance

theorem card_cycleFactorsFinset_le_four {n : ℕ} (hn : n ≤ 11) {σ : Equiv.Perm (Fin n)}
    (hσ : σ ∈ alternatingGroup (Fin n)) (hσ2 : σ ^ 2 = 1) : σ.cycleFactorsFinset.card ≤ 4 := by
  have hct : σ.cycleType = Multiset.replicate σ.cycleType.card 2 :=
    Equiv.Perm.cycleType_of_pow_prime_eq_one hσ2
  have hcard : σ.cycleFactorsFinset.card = σ.cycleType.card := by
    rw [Equiv.Perm.cycleType_def, Multiset.card_map]
    rfl
  have hsum : σ.cycleType.sum = σ.cycleType.card * 2 := by
    rw [hct]
    simp
  have hle : σ.cycleType.sum ≤ n := by
    simpa using Equiv.Perm.sum_cycleType_le σ
  have hsign : Equiv.Perm.sign σ = 1 := Equiv.Perm.mem_alternatingGroup.1 hσ
  rw [Equiv.Perm.sign_of_cycleType, neg_one_pow_eq_one_iff_even (by decide), hsum] at hsign
  obtain ⟨r, hr⟩ := hsign
  omega

theorem alt_core (n : ℕ) (hn : n ≤ 11) (σ : Equiv.Perm (Fin n)) (hσ : σ ∈ alternatingGroup (Fin n))
    (hσ2 : σ * σ = 1) (hσ1 : σ ≠ 1) (P : Subgroup (Equiv.Perm (Fin n))) (hP : Group.IsPerfect P)
    (hσP : σ ∈ P) (hPc : ∀ x ∈ P, x * σ = σ * x) : False := by
  have hσ2' : σ ^ 2 = 1 := by rw [sq]; exact hσ2
  have hle : P ≤ Subgroup.centralizer {σ} := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.2 (hPc x hx)
  have hfix : ∀ x ∈ P, ∀ c ∈ σ.cycleFactorsFinset, Commute x c := by
    intro x hx c hc
    let Φ : P →* Equiv.Perm σ.cycleFactorsFinset :=
      (Equiv.Perm.OnCycleFactors.toPermHom σ).comp (Subgroup.inclusion hle)
    have hΦ : Φ ⟨x, hx⟩ = 1 := perfect_hom_perm_eq_one (by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]
      exact card_cycleFactorsFinset_le_four hn hσ hσ2') Φ ⟨x, hx⟩
    have hker : (⟨x, hle hx⟩ : Subgroup.centralizer {σ}) ∈
        (Equiv.Perm.OnCycleFactors.toPermHom σ).ker := hΦ
    exact (Equiv.Perm.OnCycleFactors.mem_ker_toPermHom_iff σ _).1 hker c hc
  obtain ⟨a, ha⟩ : ∃ a, σ a ≠ a := by
    by_contra h
    push Not at h
    exact hσ1 (Equiv.ext h)
  have hc : σ.cycleOf a ∈ σ.cycleFactorsFinset :=
    Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.2 (Equiv.Perm.mem_support.2 ha)
  have hmem : a ∈ (σ.cycleOf a).support := by
    rw [Equiv.Perm.mem_support, Equiv.Perm.cycleOf_apply_self]
    exact ha
  have hV : ∀ x ∈ P, ∀ u, u ∈ (σ.cycleOf a).support ↔ x u ∈ (σ.cycleOf a).support := by
    intro x hx u
    have h := congrArg (fun f : Equiv.Perm (Fin n) => f u) (hfix x hx _ hc).eq
    simp only [Equiv.Perm.mul_apply] at h
    rw [Equiv.Perm.mem_support, Equiv.Perm.mem_support, ← h, Ne, Ne, Equiv.apply_eq_iff_eq]
  have hcard2 : (σ.cycleOf a).support.card = 2 := by
    have hct : σ.cycleType = Multiset.replicate σ.cycleType.card 2 :=
      Equiv.Perm.cycleType_of_pow_prime_eq_one hσ2'
    have hmem' : (σ.cycleOf a).support.card ∈ σ.cycleType := by
      rw [Equiv.Perm.cycleType_def]
      exact Multiset.mem_map_of_mem _ hc
    rw [hct] at hmem'
    exact Multiset.eq_of_mem_replicate hmem'
  let ρ : P →* Equiv.Perm {u // u ∈ (σ.cycleOf a).support} :=
    MonoidHom.mk' (fun x => (x : Equiv.Perm (Fin n)).subtypePerm fun u => (hV x x.2 u).symm)
      (fun x y => Equiv.ext fun u => Subtype.ext rfl)
  have hρ : ρ ⟨σ, hσP⟩ = 1 := perfect_hom_perm_eq_one (by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe, hcard2]
      norm_num) ρ ⟨σ, hσP⟩
  have hfin : σ a = a := congrArg (fun f : Equiv.Perm {u // u ∈ (σ.cycleOf a).support} =>
    (f ⟨a, hmem⟩).1) hρ
  exact ha hfin

theorem k94_alt : K94Excl fun K _ =>
    ∃ n : ℕ, 8 ≤ n ∧ n ≤ 11 ∧ Nonempty (K ≃* alternatingGroup (Fin n)) := by
  intro K _ _ _ _ _ _ hK z I₁ I₂ F₁ F₂ _ _ _ _ cfg
  obtain ⟨n, -, hn, ⟨e⟩⟩ := hK
  obtain ⟨e₁⟩ := cfg.e₁
  have h4 : 4 ≤ Nat.card F₁ := by
    obtain ⟨p, f, -, -, h5, hc⟩ := cfg.cards
    rcases hc with ⟨c1, -⟩ | ⟨c1, -⟩
    · rw [c1]; omega
    · rw [c1]; exact le_trans (by omega) (Nat.le_self_pow (by norm_num) _)
  have hperf : Group.IsPerfect SL(2, F₁) :=
    (CFSG.GH74.GLS.IVK.Lifted.isQuasisimple_sl2' h4).1
  have hI₁ : Group.IsPerfect I₁ :=
    Group.IsPerfect.ofSurjective (f := e₁.symm.toMonoidHom) e₁.symm.surjective
  let φ : K →* Equiv.Perm (Fin n) := (alternatingGroup (Fin n)).subtype.comp e.toMonoidHom
  have hφ : Function.Injective φ := Subtype.val_injective.comp e.injective
  have hz : z ∈ I₁ ⊓ I₂ := by
    rw [cfg.inter]
    exact Subgroup.mem_zpowers z
  have hz2 : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [cfg.z_ord, sq] at this
  have hz1 : z ≠ 1 := by
    intro h
    have := cfg.z_ord
    rw [h, orderOf_one] at this
    omega
  have hP : Group.IsPerfect (I₁.map φ) := Group.IsPerfect.map φ
  refine alt_core n hn (φ z) (e z).2 (by rw [← map_mul, hz2, map_one])
    (fun h => hz1 (hφ (h.trans (map_one φ).symm))) (I₁.map φ) hP
    (Subgroup.mem_map_of_mem φ (Subgroup.mem_inf.1 hz).1) ?_
  rintro x hx
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hx
  rw [← map_mul, ← map_mul, cfg.comm a ha z (Subgroup.mem_inf.1 hz).2]

end CFSG.GH74.GLS.IVK.Proofs2.Ivk94
