module

public import CFSG.FeitThompson.Definitions.RawFittingSubgroupConstruction
public import CFSG.FeitThompson.Foundations.FiniteDirectProductNilpotent
import CFSG.FeitThompson.Foundations.PrimeCoreLargestNormalPSubgroup
import CFSG.FeitThompson.Foundations.DistinctPrimeCoresCommute
import CFSG.FeitThompson.Foundations.PGroupNilpotent

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {G : Type*} [Group G] [Finite G] {p : ℕ}

theorem pCore_eq_bot_of_notMem_primeFactors (hp : p.Prime)
    (h : p ∉ (Nat.card G).primeFactors) : pCore p G = ⊥ := by
  obtain ⟨n, hn⟩ := exists_card_pCore_eq_pow hp G
  rcases Nat.eq_zero_or_pos n with rfl | hn'
  · exact Subgroup.card_eq_one.1 (by simpa using hn)
  · refine absurd (Nat.mem_primeFactors.2 ⟨hp, ?_, Nat.card_pos.ne'⟩) h
    exact dvd_trans (hn ▸ dvd_pow_self p hn'.ne') (Subgroup.card_subgroup_dvd_card _)

theorem fittingRaw_eq_biSup_pCore_primeFactors (G : Type*) [Group G] [Finite G] :
    fittingRaw G = ⨆ p ∈ (Nat.card G).primeFactors, pCore p G := by
  rw [fittingRaw_eq_iSup_pCore]
  refine le_antisymm (iSup₂_le fun p hp => ?_) (iSup₂_le fun p hp => ?_)
  · by_cases h : p ∈ (Nat.card G).primeFactors
    · exact le_iSup₂ (f := fun p (_ : p ∈ (Nat.card G).primeFactors) => pCore p G) p h
    · rw [pCore_eq_bot_of_notMem_primeFactors hp h]; exact bot_le
  · exact le_iSup₂ (f := fun p (_ : p ∈ {p : ℕ | p.Prime}) => pCore p G) p
      (Nat.prime_of_mem_primeFactors hp)

theorem iSup_pCore_primeFactors (G : Type*) [Group G] [Finite G] :
    (⨆ p : (Nat.card G).primeFactors, pCore (p : ℕ) G) = fittingRaw G := by
  rw [fittingRaw_eq_biSup_pCore_primeFactors, iSup_subtype']

theorem primeFactors_natCard_eq_empty_of_subsingleton (G : Type*) [Group G] [Finite G]
    [Subsingleton G] : (Nat.card G).primeFactors = ∅ := by
  rw [Nat.card_eq_one_iff_unique.2 ⟨inferInstance, inferInstance⟩]
  simp

theorem pCore_pairwise_commute (G : Type*) [Group G] [Finite G] :
    Pairwise fun i j : (Nat.card G).primeFactors =>
      ∀ x y : G, x ∈ pCore (i : ℕ) G → y ∈ pCore (j : ℕ) G → Commute x y :=
  fun i j hij _ _ hx hy =>
    mul_comm_of_mem_pCore (Nat.prime_of_mem_primeFactors i.2)
      (Nat.prime_of_mem_primeFactors j.2) (fun h => hij (Subtype.ext h)) hx hy

noncomputable def pCorePiHom (G : Type*) [Group G] [Finite G] :
    (∀ p : (Nat.card G).primeFactors, pCore (p : ℕ) G) →* G :=
  Subgroup.noncommPiCoprod (pCore_pairwise_commute G)

theorem pCorePiHom_apply (u : ∀ p : (Nat.card G).primeFactors, pCore (p : ℕ) G) :
    pCorePiHom G u = Finset.univ.noncommProd (fun p => (u p : G))
      (fun i _ j _ hij => pCore_pairwise_commute G hij _ _ (u i).2 (u j).2) :=
  Subgroup.noncommPiCoprod_apply _ u

theorem pCorePiHom_eq_list_prod {n : ℕ} (e : Fin n ≃ (Nat.card G).primeFactors)
    (u : ∀ p : (Nat.card G).primeFactors, pCore (p : ℕ) G) :
    pCorePiHom G u = (List.ofFn fun i => ((u (e i) : G))).prod := by
  classical
  set f : (Nat.card G).primeFactors → G := fun p => (u p : G) with hf
  have comm : ((Finset.univ : Finset (Nat.card G).primeFactors) : Set _).Pairwise
      (Function.onFun Commute f) :=
    fun i _ j _ hij => pCore_pairwise_commute G hij _ _ (u i).2 (u j).2
  have hl : (List.ofFn fun i => e i).Nodup := List.nodup_ofFn.2 e.injective
  have hu : (List.ofFn fun i => e i).toFinset = Finset.univ := by
    ext a; simpa using ⟨e.symm a, by simp⟩
  have key := Finset.noncommProd_toFinset (List.ofFn fun i => e i) f (hu ▸ comm) hl
  rw [pCorePiHom_apply, Finset.noncommProd_congr hu.symm (fun _ _ => rfl) comm, key,
    List.map_ofFn]
  rfl

theorem pCorePiHom_injective (G : Type*) [Group G] [Finite G] :
    Function.Injective (pCorePiHom G) := by
  have _ : ∀ p : (Nat.card G).primeFactors, Fintype (pCore (p : ℕ) G) := fun _ =>
    Fintype.ofFinite _
  refine Subgroup.injective_noncommPiCoprod_of_iSupIndep
    (Subgroup.independent_of_coprime_order (pCore_pairwise_commute G) fun i j hij => ?_)
  have h := coprime_natCard_pCore (Nat.prime_of_mem_primeFactors i.2)
    (Nat.prime_of_mem_primeFactors j.2) (fun h => hij (Subtype.ext h)) G
  simpa [Nat.card_eq_fintype_card] using h

theorem pCorePiHom_range (G : Type*) [Group G] [Finite G] :
    (pCorePiHom G).range = fittingRaw G := by
  rw [pCorePiHom, Subgroup.noncommPiCoprod_range, iSup_pCore_primeFactors]

noncomputable def pCorePiEquivFittingRaw (G : Type*) [Group G] [Finite G] :
    (∀ p : (Nat.card G).primeFactors, pCore (p : ℕ) G) ≃* fittingRaw G :=
  (MonoidHom.ofInjective (pCorePiHom_injective G)).trans
    (MulEquiv.subgroupCongr (pCorePiHom_range G))

@[simp]
theorem pCorePiEquivFittingRaw_apply_coe (u : ∀ p : (Nat.card G).primeFactors, pCore (p : ℕ) G) :
    ((pCorePiEquivFittingRaw G u : fittingRaw G) : G) = pCorePiHom G u := (rfl)

instance fittingRaw_characteristic (G : Type*) [Group G] [Finite G] :
    (fittingRaw G).Characteristic := by
  rw [fittingRaw_eq_iSup_pCore]
  exact Subgroup.characteristic_biSup fun p _ => pCore_characteristic p G

theorem map_fittingRaw (G : Type*) [Group G] [Finite G] (φ : G ≃* G) :
    (fittingRaw G).map φ.toMonoidHom = fittingRaw G :=
  Subgroup.characteristic_iff_map_eq.1 (fittingRaw_characteristic G) φ

theorem fittingRaw_normal (G : Type*) [Group G] [Finite G] : (fittingRaw G).Normal :=
  Subgroup.normal_of_characteristic _

theorem isNilpotent_pCore (hp : p.Prime) (G : Type*) [Group G] [Finite G] :
    Group.IsNilpotent (pCore p G) :=
  (exists_card_pCore_eq_pow hp G).elim fun _ hn => isNilpotent_of_natCard_eq_prime_pow hp hn

instance fittingRaw_isNilpotent (G : Type*) [Group G] [Finite G] :
    Group.IsNilpotent (fittingRaw G) :=
  have : ∀ p : (Nat.card G).primeFactors, Group.IsNilpotent (pCore (p : ℕ) G) := fun p =>
    isNilpotent_pCore (Nat.prime_of_mem_primeFactors p.2) G
  Group.nilpotent_of_mulEquiv (pCorePiEquivFittingRaw G)

theorem exists_normal_central_series_fittingRaw (G : Type*) [Group G] [Finite G] :
    ∃ (r : ℕ) (S : ℕ → Subgroup (fittingRaw G)), S 0 = ⊥ ∧ S r = ⊤ ∧
      (∀ i, S i ≤ S (i + 1)) ∧ (∀ i, (S i).Normal) ∧
      ∀ i, ⁅(⊤ : Subgroup (fittingRaw G)), S (i + 1)⁆ ≤ S i :=
  (isNilpotent_iff_exists_normal_central_series _).1 (fittingRaw_isNilpotent G)

end

end CFSG.FeitThompson
