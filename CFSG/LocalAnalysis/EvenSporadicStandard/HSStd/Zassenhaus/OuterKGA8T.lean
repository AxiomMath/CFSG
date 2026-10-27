module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterKGA8TAlt
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpTType
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterSwapCaseCatalog
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.HSInvolutions
import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.HSStd
open scoped commutatorElement

theorem card_alt8_kga8t : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Fintype.card_fin, Nat.factorial]

theorem exists_noncomm_alt8_kga8t :
    ∃ a b : alternatingGroup (Fin 8), a * b ≠ b * a := by
  refine ⟨⟨Equiv.swap 0 1 * Equiv.swap 1 2, ?_⟩, ⟨Equiv.swap 0 1 * Equiv.swap 1 3, ?_⟩, ?_⟩
  · rw [Equiv.Perm.mem_alternatingGroup]
    simp [Equiv.Perm.sign_mul]
  · rw [Equiv.Perm.mem_alternatingGroup]
    simp [Equiv.Perm.sign_mul]
  · intro h
    have := congrArg Subtype.val h
    revert this
    decide

theorem quasisimple_of_alt8_kga8t {N : Type*} [Group N] (e : N ≃* alternatingGroup (Fin 8)) :
    CFSG.IsQuasisimple N ∧ center N = ⊥ := by
  have hsimple : IsSimpleGroup N :=
    have : IsSimpleGroup (alternatingGroup (Fin 8)) :=
      alternatingGroup.isSimpleGroup (by simp)
    e.isSimpleGroup
  have hnab : ∃ a b : N, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := exists_noncomm_alt8_kga8t
    exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩
  have hZ : center N = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center N) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      exact hab ((Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b)) a)
  have hperf : Group.IsPerfect N := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator N) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      have : ⁅a, b⁆ = 1 := by
        rw [← Subgroup.mem_bot, ← h]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      exact hab (commutatorElement_eq_one_iff_mul_comm.mp this)
    · exact ⟨h⟩
  let q : N ⧸ center N ≃* N :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  refine ⟨⟨hperf, q.isSimpleGroup, ?_⟩, hZ⟩
  obtain ⟨a, b, hab⟩ := hnab
  exact ⟨q.symm a, q.symm b, fun h => hab (by simpa using congrArg q h)⟩

theorem dvd_card_of_alt8_kga8t {G : Type*} [Group G] [Finite G] (D : Subgroup G)
    (e : ↥D ≃* alternatingGroup (Fin 8)) : 20160 ∣ Nat.card G := by
  have h := Subgroup.card_subgroup_dvd_card D
  rwa [Nat.card_congr e.toEquiv, card_alt8_kga8t] at h

theorem clause_one_of_T (hT : KGPumpTableT) (K : Type) [Group K] [Finite K] (hcat : Catalog K)
    (hs : IsSimpleGroup K) (τ : MulAut K) (h2 : τ * τ = 1) (h1 : τ ≠ 1)
    (D : Subgroup ↥(autCentralizer τ)) (hD : D.Normal) (e : ↥D ≃* alternatingGroup (Fin 8)) :
    (∃ m : ℕ, 5 ≤ m ∧ Nonempty (K ≃* alternatingGroup (Fin (2 * m)))) ∨ IsSporadic K .HS ∨
      LieModel K .PSL 4 2 2 := by
  let N : Subgroup K := D.map (autCentralizer τ).subtype
  have hNle : N ≤ autCentralizer τ := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  let eN : ↥N ≃* ↥D :=
    (D.equivMapOfInjective _ (autCentralizer τ).subtype_injective).symm
  obtain ⟨hq, hZ⟩ := quasisimple_of_alt8_kga8t (eN.trans e)
  have hsub : (N.subgroupOf (autCentralizer τ)).IsSubnormal := by
    have : N.subgroupOf (autCentralizer τ) = D :=
      Subgroup.comap_map_eq_self_of_injective (autCentralizer τ).subtype_injective D
    rw [this]
    exact hD.isSubnormal
  have hpg : IsPGroup 2 (center ↥N) := IsPGroup.of_card (n := 0) (by simp [hZ])
  have hquot : Nonempty (↥N ⧸ center ↥N ≃* alternatingGroup (Fin 8)) :=
    ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans
      (eN.trans e)⟩
  rcases (hT K hcat hs τ h2 h1 N hNle hq hsub hpg).1 hquot with h | h | h | ⟨-, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · simp [hZ] at h

theorem card_eq_of_lieModel_l44 {K : Type} [Group K] (h : LieModel K .PSL 4 2 2) :
    Nat.card K = 987033600 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_four_four (h.statedClassicalModel (by decide))

section HS

theorem not_inner_of_hs_kga8t {K : Type} [Group K] [Finite K] (hs : IsSimpleGroup K)
    (hHS : IsSporadic K .HS) (τ : MulAut K) (h2 : τ * τ = 1) (h1 : τ ≠ 1)
    (hdvd : 20160 ∣ Nat.card (autCentralizer τ)) :
    τ ∉ (MulAut.conj : K →* MulAut K).range := by
  rintro ⟨g, rfl⟩
  have hcard := CFSG.EvenSporadicStandard.HSStd.Zassenhaus.card_eq_of_isSporadic_hs hHS
  have hZ : center K = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center K) with h | h
    · exact h
    · exfalso
      let : CommGroup K := Group.commGroupOfCenterEqTop h
      have hp := IsSimpleGroup.prime_card (α := K)
      rw [hcard] at hp
      norm_num at hp
  have hg2 : g * g = 1 := by
    have h3 : MulAut.conj (g * g) = 1 := by rw [map_mul]; exact h2
    have h4 : g * g ∈ center K := by
      rw [Subgroup.mem_center_iff]
      intro x
      have := congrArg (fun f : MulAut K => f x) h3
      simp only [MulAut.conj_apply, MulAut.one_apply, mul_inv_rev] at this
      have h5 : g * g * x * (g⁻¹ * g⁻¹) * (g * g) = x * (g * g) := by rw [this]
      calc x * (g * g) = g * g * x * (g⁻¹ * g⁻¹) * (g * g) := h5.symm
        _ = g * g * x := by group
    rw [hZ, Subgroup.mem_bot] at h4
    exact h4
  have hg1 : g ≠ 1 := by
    rintro rfl
    exact h1 (map_one _)
  have hord : orderOf g = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact hg2) hg1
  have hC : autCentralizer (MulAut.conj g) = centralizer ({g} : Set K) := by
    ext x
    rw [Subgroup.mem_centralizer_singleton_iff]
    change MulAut.conj g x = x ↔ _
    rw [MulAut.conj_apply, mul_inv_eq_iff_eq_mul]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  rw [hC] at hdvd
  rcases CFSG.EvenSporadicStandard.HSStd.Zassenhaus.card_centralizer_of_involution_hs hHS g hord
    with h | h <;> rw [h] at hdvd <;> omega

end HS

theorem kgA8Q8_of_T
    (hT : KGPumpTableT) : KGA8Q8 := by
  intro K _ _ hcat hs τ h2 h1 hcard ⟨D, hD, ⟨e⟩, _⟩
  have hdvd : 20160 ∣ Nat.card (autCentralizer τ) := dvd_card_of_alt8_kga8t D e
  have hinner : IsSporadic K .HS → τ ∉ (MulAut.conj : K →* MulAut K).range :=
    fun hHS => not_inner_of_hs_kga8t hs hHS τ h2 h1 hdvd
  rcases clause_one_of_T hT K hcat hs τ h2 h1 D hD e with ⟨m, hm, ⟨eK⟩⟩ | h | h
  · obtain ⟨a, ha1, ha2, hc⟩ :=
      card_autCentralizer_alt (2 * m) (by omega) (by omega) eK τ h2 h1
    rcases (alt_numeric ha1 ha2 hc hdvd hcard).1 with rfl | rfl
    · exact ⟨Or.inl ⟨5, by norm_num, ⟨eK⟩⟩, Or.inl ⟨eK⟩, hinner⟩
    · exact ⟨Or.inl ⟨6, by norm_num, ⟨eK⟩⟩, Or.inr (Or.inl ⟨eK⟩), hinner⟩
  · exact ⟨Or.inr (Or.inl h), Or.inr (Or.inr (Or.inl h)), hinner⟩
  · exact ⟨Or.inr (Or.inr (Or.inr (Or.inr ⟨1, le_rfl, by simpa using h⟩))),
      Or.inr (Or.inr (Or.inr (card_eq_of_lieModel_l44 h))), hinner⟩

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer
