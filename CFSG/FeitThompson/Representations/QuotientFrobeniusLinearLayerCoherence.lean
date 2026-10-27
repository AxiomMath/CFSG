module

public import CFSG.FeitThompson.Representations.NormalKernelLayerWeightedDegreeSum
public import CFSG.FeitThompson.Representations.CoprimePowerInducedLinearFamily
public import CFSG.FeitThompson.Representations.EqualDegreeFamilyCoherence
public import Mathlib.GroupTheory.FixedPointFree
public import Mathlib.GroupTheory.Nilpotent
import CFSG.FeitThompson.Representations.LinearIrreduciblesKillDerived
import CFSG.FeitThompson.Representations.SolvableGroupNonprincipalLinearCharacter
import CFSG.FeitThompson.Representations.SolvableFrobeniusKernelInducedIndexDegree
import CFSG.FeitThompson.Representations.NormalInducedCharactersOrthogonal
import CFSG.FeitThompson.Representations.ProductCharactersFullBasis
import CFSG.FeitThompson.Representations.TensorAndDualCharacters
import CFSG.FeitThompson.Representations.FixedPointFreeActsFreelyOnLinearChars
public import CFSG.FeitThompson.Definitions.KernelFilteredIrreducibleCharacters

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace FrobeniusQuotientLayer

open Module
open scoped Pointwise
open NormalInduction (conjClassFun_apply coe_conjNormal_inv)
open NormalLinearInduced (nonprincipalLinearIrr mem_nonprincipalLinearIrr coe_mem_commutator_iff
  indFamLinear mem_indFamLinear apply_one_of_mem_indFamLinear conj_mem_indFamLinear)
open NormalInducedFamily (kerLayerIrr mem_kerLayerIrr kerLayerIrrFinset mem_kerLayerIrrFinset
  kerLayerIndFam mem_kerLayerIndFam kerLayerIndFinset kerLayerIndFinset_eq_image
  natCard_charOrbit filter_kerLayerIrrFinset_eq sum_sq_degree_kerLayerIrrFinset
  finite_kerLayerIndFam)

variable {L : Type*} [Group L] {K E : Subgroup L}

theorem exists_monoidHom_units_coe_eq {X : Type*} [Group X] {θ : X → ℂ} (hθ : θ ∈ Irr X)
    (h1 : θ 1 = 1) : ∃ ψ : X →* ℂˣ, (fun x => (ψ x : ℂ)) = θ := by
  obtain ⟨W, hW, rfl⟩ := mem_Irr.1 hθ
  have hfr : finrank ℂ W.V = 1 := by
    have h := W.char_one
    rw [h1] at h
    exact_mod_cast h.symm
  obtain ⟨χ, hχ⟩ := Representation.exists_monoidHom_units_of_finrank_eq_one W.ρ hfr
  refine ⟨χ, ?_⟩
  funext g
  have hg : W.ρ g = (χ g : ℂ) • LinearMap.id := by ext v; simpa using hχ g v
  rw [FDRep.character, hg]
  simp [hfr]

theorem abelianization_of_eq_iff {X : Type*} [Group X] {a b : X} :
    Abelianization.of a = Abelianization.of b ↔ a⁻¹ * b ∈ commutator X := by
  rw [← Abelianization.ker_of (G := X), MonoidHom.mem_ker, map_mul, map_inv,
    inv_mul_eq_one, eq_comm]

theorem abelianization_of_eq_one_iff {X : Type*} [Group X] {a : X} :
    Abelianization.of a = 1 ↔ a ∈ commutator X := by
  rw [← Abelianization.ker_of (G := X), MonoidHom.mem_ker]

noncomputable def conjAbelianizationAut (K : Subgroup L) [K.Normal] (u : L) :
    MulAut (Abelianization ↥K) :=
  MulEquiv.abelianizationCongr (MulAut.conjNormal u⁻¹ : MulAut ↥K)

@[simp] theorem conjAbelianizationAut_of [K.Normal] (u : L) (k : ↥K) :
    conjAbelianizationAut K u (Abelianization.of k)
      = Abelianization.of (MulAut.conjNormal u⁻¹ k) := by
  simp [conjAbelianizationAut, MulEquiv.abelianizationCongr]

def FixesOnlyCommutatorCoset (K E : Subgroup L) : Prop :=
  ∀ u ∈ E, u ≠ 1 → ∀ k ∈ K, k⁻¹ * (u⁻¹ * k * u) ∈ (⁅K, K⁆ : Subgroup L) → k ∈ ⁅K, K⁆

theorem conjAbelianizationAut_of_eq_self_iff [K.Normal] (u : L) {k : L} (hk : k ∈ K) :
    conjAbelianizationAut K u (Abelianization.of ⟨k, hk⟩) = Abelianization.of ⟨k, hk⟩
      ↔ k⁻¹ * (u⁻¹ * k * u) ∈ (⁅K, K⁆ : Subgroup L) := by
  rw [conjAbelianizationAut_of, abelianization_of_eq_iff]
  constructor
  · intro h
    have h' := (⁅K, K⁆ : Subgroup L).inv_mem ((coe_mem_commutator_iff K).2 h)
    rw [Subgroup.coe_mul, Subgroup.coe_inv, coe_conjNormal_inv] at h'
    simpa [mul_inv_rev, mul_assoc] using h'
  · intro h
    refine (coe_mem_commutator_iff K).1 ?_
    rw [Subgroup.coe_mul, Subgroup.coe_inv, coe_conjNormal_inv]
    simpa [mul_inv_rev, mul_assoc] using (⁅K, K⁆ : Subgroup L).inv_mem h

theorem fixesOnlyCommutatorCoset_iff_forall_fixedPointFree [K.Normal] :
    FixesOnlyCommutatorCoset K E
      ↔ ∀ u ∈ E, u ≠ 1 → MonoidHom.FixedPointFree (conjAbelianizationAut K u) := by
  constructor
  · intro hfree u hu hu1 x hx
    obtain ⟨k, rfl⟩ := abelianization_of_surjective ↥K x
    rw [abelianization_of_eq_one_iff, ← coe_mem_commutator_iff K]
    exact hfree u hu hu1 (k : L) k.2
      ((conjAbelianizationAut_of_eq_self_iff u k.2).1 (by simpa using hx))
  · intro h u hu hu1 k hk hmem
    have hone := h u hu hu1 _ ((conjAbelianizationAut_of_eq_self_iff u hk).2 hmem)
    rw [abelianization_of_eq_one_iff] at hone
    simpa using (coe_mem_commutator_iff K).2 hone

theorem fixedPointFree_conjAbelianizationAut [K.Normal] (hfree : FixesOnlyCommutatorCoset K E)
    {u : L} (hu : u ∈ E) (hu1 : u ≠ 1) :
    MonoidHom.FixedPointFree (conjAbelianizationAut K u) :=
  fixesOnlyCommutatorCoset_iff_forall_fixedPointFree.1 hfree u hu hu1

theorem kerLayerIrr_commutator_eq_nonprincipalLinearIrr [Finite L] :
    kerLayerIrr ⁅K, K⁆ K = nonprincipalLinearIrr ↥K := by
  have : Finite ↥K := Subtype.finite
  ext θ
  rw [mem_kerLayerIrr, mem_nonprincipalLinearIrr]
  refine and_congr_right fun hθ => and_congr_left fun _ => ?_
  rw [Irr.apply_one_eq_one_iff hθ]
  exact ⟨fun h x hx => mem_charValueKernel.2 (h x ((coe_mem_commutator_iff K).2 hx)),
    fun h n hn => mem_charValueKernel.1 (h ((coe_mem_commutator_iff K).1 hn))⟩

theorem kerLayerIndFam_commutator_eq_indFamLinear [Fintype L] :
    kerLayerIndFam ⁅K, K⁆ K = indFamLinear K := by
  ext f
  rw [mem_kerLayerIndFam, mem_indFamLinear, kerLayerIrr_commutator_eq_nonprincipalLinearIrr]

theorem inertiaGroup_le_of_mem_nonprincipalLinearIrr [Finite L] [K.Normal]
    (hmul : (K : Set L) * (E : Set L) = Set.univ) (hfree : FixesOnlyCommutatorCoset K E)
    {θ : ↥K → ℂ} (hθ : θ ∈ nonprincipalLinearIrr ↥K) : inertiaGroup K θ ≤ K := by
  have : Finite ↥K := Subtype.finite
  obtain ⟨hθIrr, hθ1, hθne⟩ := mem_nonprincipalLinearIrr.1 hθ
  intro t ht
  obtain ⟨k₀, hk₀, u, hu, rfl⟩ : ∃ k ∈ (K : Set L), ∃ u ∈ (E : Set L), k * u = t := by
    have h : t ∈ (K : Set L) * (E : Set L) := by rw [hmul]; trivial
    exact h
  have hKle : K ≤ inertiaGroup K θ := le_inertiaGroup K (Irr_subset_classFun hθIrr)
  have hu' : u ∈ inertiaGroup K θ := by
    have h1 : k₀ ∈ inertiaGroup K θ := hKle hk₀
    have h2 := (inertiaGroup K θ).mul_mem ((inertiaGroup K θ).inv_mem h1) ht
    simpa [← mul_assoc] using h2
  by_cases hu1 : u = 1
  · subst hu1
    simpa using hk₀
  · exfalso
    obtain ⟨ψ, hψ⟩ := exists_monoidHom_units_coe_eq hθIrr hθ1
    have : Finite (Abelianization ↥K) := finite_abelianization ↥K
    have hlamIrr : (fun x => ((Abelianization.lift ψ) x : ℂ)) ∈ Irr (Abelianization ↥K) :=
      mem_Irr_of_monoidHom (Abelianization.lift ψ)
    have hlamof : ∀ k : ↥K, ((Abelianization.lift ψ) (Abelianization.of k) : ℂ) = θ k := by
      intro k
      rw [show ((Abelianization.lift ψ) (Abelianization.of k) : ℂ) = (ψ k : ℂ) by simp]
      exact congrFun hψ k
    have hinv : ∀ x, ((Abelianization.lift ψ) (conjAbelianizationAut K u x) : ℂ)
        = ((Abelianization.lift ψ) x : ℂ) := by
      intro x
      obtain ⟨k, rfl⟩ := abelianization_of_surjective ↥K x
      rw [conjAbelianizationAut_of, hlamof, hlamof]
      have h := congrFun (mem_inertiaGroup.1 hu') k
      rwa [conjClassFun_apply] at h
    have hlam1 : (fun x => ((Abelianization.lift ψ) x : ℂ)) = 1 :=
      eq_one_of_forall_apply_aut_eq
        (fixedPointFree_conjAbelianizationAut hfree hu hu1) hlamIrr hinv
    refine hθne ?_
    funext k
    rw [← hlamof k]
    exact congrFun hlam1 (Abelianization.of k)

theorem inertiaGroup_eq_of_mem_nonprincipalLinearIrr [Finite L] [K.Normal]
    (hmul : (K : Set L) * (E : Set L) = Set.univ) (hfree : FixesOnlyCommutatorCoset K E)
    {θ : ↥K → ℂ} (hθ : θ ∈ nonprincipalLinearIrr ↥K) : inertiaGroup K θ = K :=
  le_antisymm (inertiaGroup_le_of_mem_nonprincipalLinearIrr hmul hfree hθ)
    (le_inertiaGroup K (Irr_subset_classFun (mem_nonprincipalLinearIrr.1 hθ).1))

theorem kerLayerIndFam_commutator_nonempty [Fintype L] (hK : K ≠ ⊥)
    [Group.IsSolvable ↥K] : (kerLayerIndFam ⁅K, K⁆ K).Nonempty := by
  have _ : Nontrivial ↥K := K.nontrivial_iff_ne_bot.2 hK
  have _ : Finite ↥K := Subtype.finite
  obtain ⟨θ, hθ, hθ1, hθne⟩ := exists_mem_Irr_apply_one_eq_one_and_ne_one ↥K
  refine ⟨indClassFun K θ, mem_kerLayerIndFam.2 ⟨θ, ?_, rfl⟩⟩
  rw [kerLayerIrr_commutator_eq_nonprincipalLinearIrr]
  exact mem_nonprincipalLinearIrr.2 ⟨hθ, hθ1, hθne⟩

theorem conj_mem_kerLayerIndFam_commutator [Fintype L] {f : L → ℂ}
    (hf : f ∈ kerLayerIndFam ⁅K, K⁆ K) :
    (fun y => (starRingEnd ℂ) (f y)) ∈ kerLayerIndFam ⁅K, K⁆ K := by
  rw [kerLayerIndFam_commutator_eq_indFamLinear] at hf ⊢
  exact conj_mem_indFamLinear K hf

theorem kerLayerIndFam_commutator_subset_Irr [Fintype L] [K.Normal]
    (hmul : (K : Set L) * (E : Set L) = Set.univ) (hfree : FixesOnlyCommutatorCoset K E) :
    kerLayerIndFam ⁅K, K⁆ K ⊆ Irr L := by
  intro f hf
  obtain ⟨θ, hθ, rfl⟩ := mem_kerLayerIndFam.1 hf
  rw [kerLayerIrr_commutator_eq_nonprincipalLinearIrr] at hθ
  have hθIrr : θ ∈ Irr ↥K := (mem_nonprincipalLinearIrr.1 hθ).1
  obtain ⟨W, hW⟩ := NormalInducedFamily.exists_fdRep_character_eq_of_mem_indFam K
    (indClassFun_mem_indFam K hθIrr)
  refine mem_Irr.2 ⟨W, ?_, hW⟩
  rw [isIrreducible_iff_cfInner_self_eq_one W.ρ,
    show Representation.character W.ρ = indClassFun K θ from hW,
    cfInner_self_indClassFun K hθIrr,
    Subgroup.relIndex_eq_one.2 (inertiaGroup_le_of_mem_nonprincipalLinearIrr hmul hfree hθ),
    Nat.cast_one]

theorem apply_one_of_mem_kerLayerIndFam_commutator [Fintype L] {f : L → ℂ}
    (hf : f ∈ kerLayerIndFam ⁅K, K⁆ K) : f 1 = (K.index : ℂ) := by
  rw [kerLayerIndFam_commutator_eq_indFamLinear] at hf
  exact apply_one_of_mem_indFamLinear K hf

theorem apply_one_eq_card_of_mem_kerLayerIndFam_commutator [Fintype L]
    (hmul : (K : Set L) * (E : Set L) = Set.univ) (hinf : K ⊓ E = ⊥) {f : L → ℂ}
    (hf : f ∈ kerLayerIndFam ⁅K, K⁆ K) : f 1 = (Nat.card E : ℂ) := by
  rw [apply_one_of_mem_kerLayerIndFam_commutator hf,
    index_eq_card_of_isComplement' (isComplement'_of_mul_eq_univ_of_inf_eq_bot hmul hinf)]

theorem card_kerLayerIrrFinset_commutator [Finite L] [K.Normal] :
    (kerLayerIrrFinset ⁅K, K⁆ K).card + 1 = (⁅K, K⁆ : Subgroup L).relIndex K := by
  have hsum := sum_sq_degree_kerLayerIrrFinset (A := (⁅K, K⁆ : Subgroup L)) (K := K)
  have hdeg : ∀ θ ∈ kerLayerIrrFinset (⁅K, K⁆ : Subgroup L) K, θ 1 ^ 2 = (1 : ℂ) := by
    intro θ hθ
    have h : θ ∈ nonprincipalLinearIrr ↥K := by
      rw [← kerLayerIrr_commutator_eq_nonprincipalLinearIrr]
      exact mem_kerLayerIrrFinset.1 hθ
    rw [(mem_nonprincipalLinearIrr.1 h).2.1, one_pow]
  rw [Finset.sum_congr rfl hdeg, Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
  have h : ((kerLayerIrrFinset (⁅K, K⁆ : Subgroup L) K).card + 1 : ℂ)
      = ((⁅K, K⁆ : Subgroup L).relIndex K : ℂ) := by rw [hsum]; ring
  exact_mod_cast h

theorem card_kerLayerIndFinset_commutator_mul_index [Fintype L] [K.Normal]
    (hmul : (K : Set L) * (E : Set L) = Set.univ) (hfree : FixesOnlyCommutatorCoset K E) :
    (kerLayerIndFinset ⁅K, K⁆ K).card * K.index + 1 = (⁅K, K⁆ : Subgroup L).relIndex K := by
  classical
  rw [← card_kerLayerIrrFinset_commutator (K := K)]
  congr 1
  rw [kerLayerIndFinset_eq_image,
    Finset.card_eq_sum_card_image (indClassFun K) (kerLayerIrrFinset ⁅K, K⁆ K),
    Finset.sum_congr rfl (g := fun _ => K.index) ?_, Finset.sum_const, smul_eq_mul]
  intro f hf
  obtain ⟨θ, hθmem, rfl⟩ := Finset.mem_image.1 hf
  have hθ : θ ∈ kerLayerIrr (⁅K, K⁆ : Subgroup L) K := mem_kerLayerIrrFinset.1 hθmem
  have hfilter : (((kerLayerIrrFinset (⁅K, K⁆ : Subgroup L) K).filter
      (fun θ' => indClassFun K θ' = indClassFun K θ)) : Set (↥K → ℂ))
      = NormalInducedFamily.charOrbit K θ := by
    ext θ'
    simp only [Finset.coe_filter, Set.mem_ofPred_eq]
    exact filter_kerLayerIrrFinset_eq hθ θ'
  have hcard : ((kerLayerIrrFinset (⁅K, K⁆ : Subgroup L) K).filter
      (fun θ' => indClassFun K θ' = indClassFun K θ)).card = (inertiaGroup K θ).index := by
    rw [← natCard_charOrbit θ, ← hfilter, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  have hθlin : θ ∈ nonprincipalLinearIrr ↥K := by
    rwa [← kerLayerIrr_commutator_eq_nonprincipalLinearIrr]
  rw [hcard, inertiaGroup_eq_of_mem_nonprincipalLinearIrr hmul hfree hθlin]

theorem card_kerLayerIndFinset_commutator [Fintype L] [K.Normal]
    (hmul : (K : Set L) * (E : Set L) = Set.univ) (hfree : FixesOnlyCommutatorCoset K E) :
    (kerLayerIndFinset ⁅K, K⁆ K).card = ((⁅K, K⁆ : Subgroup L).relIndex K - 1) / K.index := by
  have h := card_kerLayerIndFinset_commutator_mul_index (E := E) hmul hfree
  have h' : (kerLayerIndFinset ⁅K, K⁆ K).card * K.index
      = (⁅K, K⁆ : Subgroup L).relIndex K - 1 := by omega
  have hpos : 0 < K.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  rw [← h', Nat.mul_div_cancel _ hpos]

theorem isCoherent_kerLayerIndFam_commutator {G : Type*} [Group G] [Fintype G] [Fintype L]
    [K.Normal] (hmul : (K : Set L) * (E : Set L) = Set.univ)
    (hfree : FixesOnlyCommutatorCoset K E)
    (τ : charSpanZero (kerLayerIndFam ⁅K, K⁆ K) →+ virtualChars G)
    (hτiso : ∀ f g : charSpanZero (kerLayerIndFam ⁅K, K⁆ K),
      cfInner (τ f : G → ℂ) (τ g : G → ℂ) = cfInner (f : L → ℂ) (g : L → ℂ))
    (hτ1 : ∀ f : charSpanZero (kerLayerIndFam ⁅K, K⁆ K), (τ f : G → ℂ) 1 = 0) :
    IsCoherent (kerLayerIndFam ⁅K, K⁆ K) τ :=
  isCoherent_of_forall_apply_one_eq finite_kerLayerIndFam
    (kerLayerIndFam_commutator_subset_Irr hmul hfree)
    (fun _ hf => apply_one_of_mem_kerLayerIndFam_commutator hf) τ hτiso hτ1

theorem kerLayerIrr_mono {A A' : Subgroup L} (h : A' ≤ A) :
    kerLayerIrr A K ⊆ kerLayerIrr A' K := by
  intro θ hθ
  obtain ⟨hirr, hker, hne⟩ := mem_kerLayerIrr.1 hθ
  exact mem_kerLayerIrr.2 ⟨hirr, fun n hn => hker n (h hn), hne⟩

theorem kerLayerIndFam_commutator_subset_kerLayerIndFam [Fintype L] {A : Subgroup L}
    (hA : A ≤ (⁅K, K⁆ : Subgroup L)) : kerLayerIndFam ⁅K, K⁆ K ⊆ kerLayerIndFam A K := by
  intro f hf
  obtain ⟨θ, hθ, rfl⟩ := mem_kerLayerIndFam.1 hf
  exact mem_kerLayerIndFam.2 ⟨θ, kerLayerIrr_mono hA hθ, rfl⟩

theorem kerLayerIndFam_commutator_conclusion {G : Type*} [Group G] [Fintype G] [Fintype L]
    [K.Normal] [Group.IsNilpotent ↥K] (hK : K ≠ ⊥)
    (hmul : (K : Set L) * (E : Set L) = Set.univ) (hinf : K ⊓ E = ⊥)
    (hfree : FixesOnlyCommutatorCoset K E) :
    (kerLayerIndFam ⁅K, K⁆ K).Nonempty
      ∧ (∀ f ∈ kerLayerIndFam ⁅K, K⁆ K,
          (fun y => (starRingEnd ℂ) (f y)) ∈ kerLayerIndFam ⁅K, K⁆ K)
      ∧ kerLayerIndFam ⁅K, K⁆ K ⊆ Irr L
      ∧ (∀ f ∈ kerLayerIndFam ⁅K, K⁆ K, f 1 = (Nat.card E : ℂ))
      ∧ (kerLayerIndFinset ⁅K, K⁆ K).card * K.index + 1 = (⁅K, K⁆ : Subgroup L).relIndex K
      ∧ (∀ τ : charSpanZero (kerLayerIndFam ⁅K, K⁆ K) →+ virtualChars G,
          (∀ f g : charSpanZero (kerLayerIndFam ⁅K, K⁆ K),
            cfInner (τ f : G → ℂ) (τ g : G → ℂ) = cfInner (f : L → ℂ) (g : L → ℂ)) →
          (∀ f : charSpanZero (kerLayerIndFam ⁅K, K⁆ K), (τ f : G → ℂ) 1 = 0) →
          IsCoherent (kerLayerIndFam ⁅K, K⁆ K) τ)
      ∧ ∀ A : Subgroup L, A ≤ (⁅K, K⁆ : Subgroup L) →
          kerLayerIndFam ⁅K, K⁆ K ⊆ kerLayerIndFam A K :=
  ⟨kerLayerIndFam_commutator_nonempty hK, fun _ hf => conj_mem_kerLayerIndFam_commutator hf,
    kerLayerIndFam_commutator_subset_Irr hmul hfree,
    fun _ hf => apply_one_eq_card_of_mem_kerLayerIndFam_commutator hmul hinf hf,
    card_kerLayerIndFinset_commutator_mul_index hmul hfree,
    fun τ hτiso hτ1 => isCoherent_kerLayerIndFam_commutator hmul hfree τ hτiso hτ1,
    fun _ hA => kerLayerIndFam_commutator_subset_kerLayerIndFam hA⟩

end FrobeniusQuotientLayer

end CFSG.FeitThompson
