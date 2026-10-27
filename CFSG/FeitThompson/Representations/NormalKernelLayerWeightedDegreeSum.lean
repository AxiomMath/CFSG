module

public import CFSG.FeitThompson.Representations.InducedIrreducibleNormOrbitFormula
public import CFSG.FeitThompson.Representations.QuotientIrreducibleCharsDegreeSum
import CFSG.FeitThompson.Representations.NonprincipalInducedOrthPrincipalInduced
import CFSG.FeitThompson.Representations.CommonClassLinearCharacterCongruence
import CFSG.FeitThompson.Representations.NormalInducedCharactersOrthogonal
import CFSG.FeitThompson.Foundations.OrbitStabilizerIndex

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace NormalInducedFamily

open NormalInduction (conjClassFun conjClassFun_apply coe_conjNormal_inv)

variable {L : Type*} [Group L] {A K : Subgroup L}

theorem eq_one_of_mem_Irr_of_forall_apply_eq {G : Type*} [Group G] [Finite G] {χ : G → ℂ}
    (hχ : χ ∈ Irr G) (h : ∀ g : G, χ g = χ 1) : χ = 1 := by
  have : Fintype G := Fintype.ofFinite G
  obtain ⟨d, -, hχ1⟩ := exists_apply_one_eq_of_mem_Irr hχ
  have hone : cfInner χ χ = 1 := cfInner_self_of_mem_Irr hχ
  rw [cfInner_def] at hone
  simp only [h, hχ1, Complex.conj_natCast, Finset.sum_const, Finset.card_univ,
    ← Nat.card_eq_fintype_card, nsmul_eq_mul] at hone
  rw [inv_mul_cancel_left₀ (Nat.cast_ne_zero.2 Nat.card_pos.ne' : (Nat.card G : ℂ) ≠ 0)] at hone
  have hd1 : d = 1 := Nat.eq_one_of_mul_eq_one_right (by exact_mod_cast hone)
  funext g
  rw [h g, hχ1, hd1]
  simp

@[simp] theorem conjClassFun_apply_one [K.Normal] (t : L) (θ : ↥K → ℂ) :
    conjClassFun K t θ 1 = θ 1 := by
  rw [conjClassFun_apply, map_one]

def kerLayerIrr (A K : Subgroup L) : Set (↥K → ℂ) := irrTrivialOn (A.subgroupOf K) \ {1}

theorem mem_kerLayerIrr {θ : ↥K → ℂ} :
    θ ∈ kerLayerIrr A K ↔ θ ∈ Irr ↥K ∧ (∀ n : ↥K, (n : L) ∈ A → θ n = θ 1) ∧ θ ≠ 1 := by
  simp [kerLayerIrr, mem_irrTrivialOn, Subgroup.mem_subgroupOf, and_assoc]

theorem kerLayerIrr_subset_Irr : kerLayerIrr A K ⊆ Irr ↥K := fun _ h => (mem_kerLayerIrr.1 h).1

theorem finite_kerLayerIrr [Finite L] : (kerLayerIrr A K).Finite :=
  finite_irrTrivialOn.sdiff

noncomputable def kerLayerIrrFinset (A K : Subgroup L) [Finite L] : Finset (↥K → ℂ) :=
  (finite_kerLayerIrr (A := A) (K := K)).toFinset

@[simp] theorem mem_kerLayerIrrFinset [Finite L] {θ : ↥K → ℂ} :
    θ ∈ kerLayerIrrFinset A K ↔ θ ∈ kerLayerIrr A K := Set.Finite.mem_toFinset _

theorem kerLayerIrr_eq_empty_self [Finite L] : kerLayerIrr K K = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun θ hθ => ?_
  obtain ⟨hirr, hker, hne⟩ := mem_kerLayerIrr.1 hθ
  exact hne (eq_one_of_mem_Irr_of_forall_apply_eq hirr fun n => hker n n.2)

theorem one_mem_irrTrivialOn_subgroupOf :
    (1 : ↥K → ℂ) ∈ irrTrivialOn (A.subgroupOf K) :=
  mem_irrTrivialOn.2 ⟨one_mem_Irr, fun _ _ => rfl⟩

theorem sum_sq_degree_kerLayerIrrFinset [Finite L] [A.Normal] :
    ∑ θ ∈ kerLayerIrrFinset A K, θ 1 ^ 2 = (A.relIndex K : ℂ) - 1 := by
  classical
  have hnorm : (A.subgroupOf K).Normal := ‹A.Normal›.subgroupOf K
  have h1 : (1 : ↥K → ℂ) ∈ irrTrivialOnFinset (A.subgroupOf K) :=
    mem_irrTrivialOnFinset.2 one_mem_irrTrivialOn_subgroupOf
  have hset : kerLayerIrrFinset A K = (irrTrivialOnFinset (A.subgroupOf K)).erase 1 := by
    ext θ
    simp [kerLayerIrr, Finset.mem_erase, and_comm]
  have key := Finset.sum_erase_add (irrTrivialOnFinset (A.subgroupOf K))
    (fun θ : ↥K → ℂ => θ 1 ^ 2) h1
  rw [sum_sq_degree_irrTrivialOn_eq_index] at key
  rw [hset, eq_sub_iff_add_eq]
  simpa [Subgroup.relIndex] using key

theorem conjClassFun_mem_kerLayerIrr [A.Normal] [K.Normal] (t : L) {θ : ↥K → ℂ}
    (hθ : θ ∈ kerLayerIrr A K) : conjClassFun K t θ ∈ kerLayerIrr A K := by
  obtain ⟨hirr, hker, hne⟩ := mem_kerLayerIrr.1 hθ
  refine mem_kerLayerIrr.2 ⟨conjClassFun_mem_Irr K t hirr, ?_, ?_⟩
  · intro n hn
    rw [conjClassFun_apply_one, conjClassFun_apply]
    exact hker _ (by rw [coe_conjNormal_inv]; simpa [mul_assoc] using ‹A.Normal›.conj_mem _ hn t⁻¹)
  · intro h
    apply hne
    have h' := congrArg (conjClassFun K t⁻¹) h
    rwa [← conjClassFun_mul, inv_mul_cancel, conjClassFun_one, conjClassFun_one_right] at h'

@[instance_reducible]
private def conjAction (K : Subgroup L) [K.Normal] : MulAction L (↥K → ℂ) where
  smul t f := conjClassFun K t f
  one_smul := conjClassFun_one K
  mul_smul := conjClassFun_mul K

attribute [local instance] conjAction

def charOrbit (K : Subgroup L) [K.Normal] (θ : ↥K → ℂ) : Set (↥K → ℂ) :=
  {θ' | ∃ t : L, conjClassFun K t θ = θ'}

theorem mem_charOrbit [K.Normal] {θ θ' : ↥K → ℂ} :
    θ' ∈ charOrbit K θ ↔ ∃ t : L, conjClassFun K t θ = θ' := Iff.rfl

theorem self_mem_charOrbit [K.Normal] (θ : ↥K → ℂ) : θ ∈ charOrbit K θ :=
  ⟨1, conjClassFun_one K θ⟩

private theorem charOrbit_eq_orbit [K.Normal] (θ : ↥K → ℂ) :
    charOrbit K θ = MulAction.orbit L θ := rfl

theorem natCard_charOrbit [K.Normal] (θ : ↥K → ℂ) :
    Nat.card (charOrbit K θ) = (inertiaGroup K θ).index := by
  rw [charOrbit_eq_orbit, natCard_orbit_eq_index_stabilizer]
  congr 1
  ext t
  rw [MulAction.mem_stabilizer_iff, mem_inertiaGroup]
  exact Iff.rfl

theorem sq_degree_div_norm_indClassFun [Fintype L] [K.Normal] {θ : ↥K → ℂ} (hθ : θ ∈ Irr ↥K) :
    indClassFun K θ 1 ^ 2 / cfInner (indClassFun K θ) (indClassFun K θ)
      = (K.index : ℂ) * ((inertiaGroup K θ).index : ℂ) * θ 1 ^ 2 := by
  have hKI : K ≤ inertiaGroup K θ := le_inertiaGroup K (Irr_subset_classFun hθ)
  have hmul : K.relIndex (inertiaGroup K θ) * (inertiaGroup K θ).index = K.index :=
    Subgroup.relIndex_mul_index hKI
  have hr : (K.relIndex (inertiaGroup K θ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 (relIndex_inertiaGroup_ne_zero K θ)
  rw [cfInner_self_indClassFun K hθ, indClassFun_one_eq_index_mul, div_eq_iff hr]
  have h : ((K.relIndex (inertiaGroup K θ) : ℂ)) * ((inertiaGroup K θ).index : ℂ)
      = (K.index : ℂ) := by exact_mod_cast congrArg (Nat.cast : ℕ → ℂ) hmul
  calc ((K.index : ℂ) * θ 1) ^ 2 = (K.index : ℂ) * ((K.index : ℂ)) * θ 1 ^ 2 := by ring
  _ = (K.index : ℂ) * (((K.relIndex (inertiaGroup K θ) : ℂ)) * ((inertiaGroup K θ).index : ℂ))
        * θ 1 ^ 2 := by rw [h]
  _ = _ := by ring

noncomputable def kerLayerIndFam (A K : Subgroup L) [Fintype L] : Set (L → ℂ) :=
  indFam K (kerLayerIrr A K)

theorem mem_kerLayerIndFam [Fintype L] {f : L → ℂ} :
    f ∈ kerLayerIndFam A K ↔ ∃ θ ∈ kerLayerIrr A K, indClassFun K θ = f := mem_indFam K

theorem indClassFun_mem_kerLayerIndFam [Fintype L] {θ : ↥K → ℂ} (hθ : θ ∈ kerLayerIrr A K) :
    indClassFun K θ ∈ kerLayerIndFam A K := indClassFun_mem_indFam K hθ

theorem kerLayerIndFam_subset_indFam [Fintype L] : kerLayerIndFam A K ⊆ indFam K (Irr ↥K) :=
  indFam_mono K kerLayerIrr_subset_Irr

theorem finite_kerLayerIndFam [Fintype L] : (kerLayerIndFam A K).Finite :=
  indFam_finite K finite_kerLayerIrr

theorem kerLayerIndFam_eq_empty_self [Fintype L] : kerLayerIndFam K K = ∅ := by
  rw [kerLayerIndFam, kerLayerIrr_eq_empty_self, indFam_empty]

noncomputable def kerLayerIndFinset (A K : Subgroup L) [Fintype L] : Finset (L → ℂ) :=
  (finite_kerLayerIndFam (A := A) (K := K)).toFinset

@[simp] theorem mem_kerLayerIndFinset [Fintype L] {f : L → ℂ} :
    f ∈ kerLayerIndFinset A K ↔ f ∈ kerLayerIndFam A K := Set.Finite.mem_toFinset _

theorem kerLayerIndFinset_eq_image [Fintype L] [DecidableEq (L → ℂ)] :
    kerLayerIndFinset A K = (kerLayerIrrFinset A K).image (indClassFun K) := by
  ext f
  simp [mem_kerLayerIndFinset, mem_kerLayerIndFam, eq_comm]

theorem filter_kerLayerIrrFinset_eq [Fintype L] [A.Normal] [K.Normal] {θ : ↥K → ℂ}
    (hθ : θ ∈ kerLayerIrr A K) (θ' : ↥K → ℂ) :
    (θ' ∈ kerLayerIrrFinset A K ∧ indClassFun K θ' = indClassFun K θ) ↔ θ' ∈ charOrbit K θ := by
  constructor
  · rintro ⟨hmem, heq⟩
    obtain ⟨t, ht⟩ := (indClassFun_eq_iff_exists_conjClassFun K
      (kerLayerIrr_subset_Irr (mem_kerLayerIrrFinset.1 hmem)) (kerLayerIrr_subset_Irr hθ)).1 heq
    exact mem_charOrbit.2 ⟨t, ht⟩
  · rintro ⟨t, rfl⟩
    exact ⟨mem_kerLayerIrrFinset.2 (conjClassFun_mem_kerLayerIrr t hθ),
      indClassFun_conjClassFun K t θ⟩

theorem sum_sq_degree_div_norm_kerLayerIndFinset [Fintype L] [A.Normal] [K.Normal] :
    ∑ χ ∈ kerLayerIndFinset A K, χ 1 ^ 2 / cfInner χ χ
      = (K.index : ℂ) * ((A.relIndex K : ℂ) - 1) := by
  classical
  rw [kerLayerIndFinset_eq_image,
    Finset.sum_image' (h := fun θ : ↥K → ℂ => (K.index : ℂ) * θ 1 ^ 2) ?_]
  · rw [← Finset.mul_sum, sum_sq_degree_kerLayerIrrFinset]
  · intro θ hθmem
    have hθ : θ ∈ kerLayerIrr A K := mem_kerLayerIrrFinset.1 hθmem
    have hfilter : ((kerLayerIrrFinset A K).filter
        (fun θ' => indClassFun K θ' = indClassFun K θ) : Set (↥K → ℂ)) = charOrbit K θ := by
      ext θ'
      simp only [Finset.coe_filter, Set.mem_ofPred_eq]
      exact filter_kerLayerIrrFinset_eq hθ θ'
    have hcard : ((kerLayerIrrFinset A K).filter
        (fun θ' => indClassFun K θ' = indClassFun K θ)).card = (inertiaGroup K θ).index := by
      rw [← natCard_charOrbit θ, ← hfilter, Nat.card_coe_set_eq, Set.ncard_coe_finset]
    rw [sq_degree_div_norm_indClassFun (kerLayerIrr_subset_Irr hθ),
      Finset.sum_congr rfl (g := fun _ => (K.index : ℂ) * θ 1 ^ 2) ?_]
    · rw [Finset.sum_const, hcard, nsmul_eq_mul]
      ring
    · intro θ' hθ'
      obtain ⟨t, rfl⟩ := (filter_kerLayerIrrFinset_eq hθ θ').1 (by
        simpa [Finset.mem_filter] using hθ')
      rw [conjClassFun_apply_one]

theorem exists_apply_one_eq_of_mem_kerLayerIndFam [Fintype L] {f : L → ℂ}
    (hf : f ∈ kerLayerIndFam A K) : ∃ d : ℕ, 0 < d ∧ K.index ∣ d ∧ f 1 = (d : ℂ) :=
  exists_apply_one_eq_of_mem_indFam K (kerLayerIndFam_subset_indFam hf)

theorem cfInner_eq_zero_of_mem_kerLayerIndFam [Fintype L] [K.Normal] {f g : L → ℂ}
    (hf : f ∈ kerLayerIndFam A K) (hg : g ∈ kerLayerIndFam A K) (hne : f ≠ g) :
    cfInner f g = 0 :=
  cfInner_eq_zero_of_mem_indFam K (kerLayerIndFam_subset_indFam hf)
    (kerLayerIndFam_subset_indFam hg) hne

end NormalInducedFamily

end CFSG.FeitThompson
