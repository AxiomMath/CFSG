module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotPositionBNormalForm
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotPositionBRank
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotPositionBLevi
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPositionRouteB
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotRootSL2Aut

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.EvenSmallLie CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin (perfectCore perfectCore_le le_perfectCore_of_perfect perfectCore_perfect
  map_perfectCore)

theorem InvPlacement.elt_eq_one_of_eq_zero {n k : ℕ} {K : Type*} [Field K] (P : InvPlacement n k)
    (hk : k = 0) : P.elt K = 1 := by
  subst hk
  have h0 : P.nil K = 0 := nilOf_eq_zero_of_eq_zero (u := P.u) (w := P.w) rfl
  have h : P.mat K = 1 := by
    apply Subtype.ext
    rw [InvPlacement.coe_mat, h0, add_zero, Matrix.SpecialLinearGroup.coe_one]
  rw [InvPlacement.elt, h, map_one]

theorem map_le_centralizer_map {A G : Type*} [Group A] [Group G] (f : A →* G) {H Z : Subgroup A}
    (h : H ≤ centralizer (Z : Set A)) :
    H.map f ≤ centralizer ((Z.map f : Subgroup G) : Set G) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨z, hz, rfl⟩
  rw [← map_mul, ← map_mul, mem_centralizer_iff.1 (h hx) z hz]

theorem disjoint_map_of_injective {A G : Type*} [Group A] [Group G] {f : A →* G}
    (hf : Function.Injective f) {H K : Subgroup A} (h : Disjoint H K) :
    Disjoint (H.map f) (K.map f) := by
  rw [disjoint_iff, ← map_inf_eq _ _ _ hf, disjoint_iff.1 h, Subgroup.map_bot]

theorem card_blockSL_eq {n : ℕ} {K : Type*} [Field K] {I : Finset (Fin n)} (hI : I.card < n) :
    Nat.card (blockSL (K := K) I) = Nat.card (Matrix.SpecialLinearGroup (Fin I.card) K) := by
  obtain ⟨e⟩ := blockSL_mulEquiv (K := K) hI
  exact Nat.card_congr e.toEquiv

theorem blockSL_mulEquiv_blockSL {n : ℕ} {K : Type*} [Field K] {I I' : Finset (Fin n)}
    (hI : I.card < n) (hII' : I.card = I'.card) :
    Nonempty (blockSL (K := K) I ≃* blockSL (K := K) I') := by
  obtain ⟨e⟩ := blockSL_mulEquiv (K := K) hI
  obtain ⟨e'⟩ := blockSL_mulEquiv (K := K) (I := I') (hII' ▸ hI)
  exact ⟨e.trans ((reindexSpecialLinear (finCongr hII')).trans e'.symm)⟩

section Coordinates

variable {G : Type*} [Group G] [Finite G] {n : ℕ} {K : Type*} [Field K] [Finite K] [CharP K 2]
  {φ φ' : LinearFlag.projectiveSL n K →* G} {k k' : ℕ}

omit [Finite G] in
theorem two_le_card_free_of_map_perfectCore_eq (hq : 4 ≤ Nat.card K) (hn : 4 ≤ n)
    (hφ : Function.Injective φ) (hφ' : Function.Injective φ') (P : InvPlacement n k)
    (P' : InvPlacement n k') (hk : 0 < k) (hJ2 : 2 ≤ P.free.card)
    (hΛ : (perfectCore (centralizer {P.elt K})).map φ =
      (perfectCore (centralizer {P'.elt K})).map φ') :
    2 ≤ P'.free.card := by
  have hJn : 2 ≤ n - 2 * k := P.card_free ▸ hJ2
  obtain ⟨hQp, hΛeq, -, hMN, hSeq⟩ := P.centralizer_inv_perfectCore hq hJn
  have hQΛ : P.radicalP K ≤ perfectCore (centralizer {P.elt K}) := by
    rw [hΛeq]
    exact le_sup_left
  have hSΛ : blockSL (K := K) P.free ≤ perfectCore (centralizer {P.elt K}) := by
    rw [hΛeq]
    exact le_sup_right.trans le_sup_right
  have hΛN : perfectCore (centralizer {P.elt K}) ≤
      normalizer (P.radicalP K : Set (LinearFlag.projectiveSL n K)) := by
    rw [hΛeq]
    exact sup_le le_normalizer hMN
  have hmax : ∀ T : Subgroup (LinearFlag.projectiveSL n K), IsPGroup 2 T →
      T ≤ perfectCore (centralizer {P.elt K}) →
      perfectCore (centralizer {P.elt K}) ≤ normalizer (T : Set (LinearFlag.projectiveSL n K)) →
      T ≤ P.radicalP K :=
    fun T hT h1 h2 => P.le_radicalP_of_isPGroup_perfectCore hq hJ2 hT h1 h2
  have hQQ : ⁅P.radicalP K, P.radicalP K⁆ ≠ ⊥ := by
    obtain ⟨j, hj⟩ : P.free.Nonempty := Finset.card_pos.1 (by omega)
    exact P.commutator_radicalP_ne_bot hk ⟨j, hj⟩
  have hSp : ⁅blockSL (K := K) P.free, blockSL (K := K) P.free⁆ = blockSL (K := K) P.free := by
    rw [hSeq]
    exact perfectCore_perfect _
  have hS1 : blockSL (K := K) P.free ≠ ⊥ := by
    obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.1 (by omega : 1 < P.free.card)
    intro h
    have hmem := proj_transvection_mem_blockSL (K := K) hij hi hj 1
    rw [h, mem_bot] at hmem
    exact proj_transvection_ne_one hij one_ne_zero hmem
  have hSC : blockSL (K := K) P.free ≤ centralizer
      ((⁅P.radicalP K, P.radicalP K⁆ : Subgroup (LinearFlag.projectiveSL n K)) :
        Set (LinearFlag.projectiveSL n K)) := by
    rw [hSeq]
    exact (perfectCore_le _).trans inf_le_right
  have hQQmap := map_commutator_comap_map hΛ hQΛ
  refine two_le_card_free_of_radical_data hq hn P' (Q := ((P.radicalP K).map φ).comap φ')
    (S := ((blockSL (K := K) P.free).map φ).comap φ')
    (comap_map_le hφ' hΛ hQΛ) (isPGroup_comap_map hφ' hQp) (le_normalizer_comap_map hΛ hΛN)
    (fun T hT h1 h2 => le_comap_map_of_forall hφ hΛ hmax hT h1 h2) ?_
    (comap_map_le hφ' hΛ hSΛ) (commutator_comap_map_eq hφ' hΛ hSΛ hSp)
    (comap_map_ne_bot hφ hΛ hSΛ hS1) ?_
  · intro h
    apply hQQ
    rw [h, Subgroup.map_bot] at hQQmap
    exact (map_eq_bot_iff_of_injective _ hφ).1 hQQmap.symm
  · rw [← comap_map_eq_self_of_injective hφ' ⁅_, _⁆, hQQmap]
    exact comap_map_le_centralizer hφ' hSC

omit [Finite G] in
theorem map_radicalP_eq (hq : 4 ≤ Nat.card K) (hφ : Function.Injective φ)
    (hφ' : Function.Injective φ') (P : InvPlacement n k) (P' : InvPlacement n k')
    (hJ2 : 2 ≤ P.free.card) (hJ'2 : 2 ≤ P'.free.card)
    (hΛ : (perfectCore (centralizer {P.elt K})).map φ =
      (perfectCore (centralizer {P'.elt K})).map φ') :
    (P'.radicalP K).map φ' = (P.radicalP K).map φ := by
  obtain ⟨hQp, hΛeq, -, hMN, -⟩ := P.centralizer_inv_perfectCore hq (P.card_free ▸ hJ2)
  obtain ⟨hQp', hΛeq', -, hMN', -⟩ := P'.centralizer_inv_perfectCore hq (P'.card_free ▸ hJ'2)
  have hQΛ : P.radicalP K ≤ perfectCore (centralizer {P.elt K}) := by
    rw [hΛeq]
    exact le_sup_left
  have hΛN : perfectCore (centralizer {P.elt K}) ≤
      normalizer (P.radicalP K : Set (LinearFlag.projectiveSL n K)) := by
    rw [hΛeq]
    exact sup_le le_normalizer hMN
  have hQ'Λ : P'.radicalP K ≤ perfectCore (centralizer {P'.elt K}) := by
    rw [hΛeq']
    exact le_sup_left
  have hΛN' : perfectCore (centralizer {P'.elt K}) ≤
      normalizer (P'.radicalP K : Set (LinearFlag.projectiveSL n K)) := by
    rw [hΛeq']
    exact sup_le le_normalizer hMN'
  have heq : P'.radicalP K = ((P.radicalP K).map φ).comap φ' := by
    apply le_antisymm
    · exact le_comap_map_of_forall hφ hΛ
        (fun T hT h1 h2 => P.le_radicalP_of_isPGroup_perfectCore hq hJ2 hT h1 h2) hQp' hQ'Λ hΛN'
    · exact P'.le_radicalP_of_isPGroup_perfectCore hq hJ'2 (isPGroup_comap_map hφ' hQp)
        (comap_map_le hφ' hΛ hQΛ) (le_normalizer_comap_map hΛ hΛN)
  rw [heq, map_comap_map_eq hΛ hQΛ]

theorem sup_map_blockSL_eq (hq : 4 ≤ Nat.card K) (hφ : Function.Injective φ)
    (hφ' : Function.Injective φ') (P : InvPlacement n k) (P' : InvPlacement n k')
    (hJ2 : 2 ≤ P.free.card) (hJ'2 : 2 ≤ P'.free.card)
    (hΛ : (perfectCore (centralizer {P.elt K})).map φ =
      (perfectCore (centralizer {P'.elt K})).map φ') :
    (P.radicalP K).map φ ⊔ (blockSL (K := K) P.free).map φ =
      (P.radicalP K).map φ ⊔ (blockSL (K := K) P'.free).map φ' := by
  have hQeq := map_radicalP_eq hq hφ hφ' P P' hJ2 hJ'2 hΛ
  obtain ⟨-, hΛeq, hdisj, hMN, hSeq⟩ := P.centralizer_inv_perfectCore hq (P.card_free ▸ hJ2)
  obtain ⟨-, hΛeq', hdisj', -, hSeq'⟩ :=
    P'.centralizer_inv_perfectCore hq (P'.card_free ▸ hJ'2)
  have hMN' : ((P.leviOneP K ⊔ blockSL (K := K) P.free).map φ) ≤
      normalizer (((P.radicalP K).map φ : Subgroup G) : Set G) :=
    (map_mono hMN).trans (le_normalizer_map φ)
  have hQM : Disjoint ((P.radicalP K).map φ) ((P.leviOneP K ⊔ blockSL (K := K) P.free).map φ) :=
    disjoint_map_of_injective hφ hdisj
  have hQM' : Disjoint ((P.radicalP K).map φ)
      ((P'.leviOneP K ⊔ blockSL (K := K) P'.free).map φ') := by
    rw [← hQeq]
    exact disjoint_map_of_injective hφ' hdisj'
  have hMM' : (P.radicalP K).map φ ⊔ (P.leviOneP K ⊔ blockSL (K := K) P.free).map φ =
      (P.radicalP K).map φ ⊔ (P'.leviOneP K ⊔ blockSL (K := K) P'.free).map φ' := by
    rw [← Subgroup.map_sup, ← hΛeq, hΛ, hΛeq', Subgroup.map_sup, hQeq]
  have hQZ : (P.radicalP K).map φ ≤ centralizer
      ((⁅(P.radicalP K).map φ, (P.radicalP K).map φ⁆ : Subgroup G) : Set G) := by
    rw [← Subgroup.map_commutator]
    exact map_le_centralizer_map φ P.radicalP_le_centralizer_commutator
  have hS : (blockSL (K := K) P.free).map φ =
      perfectCore ((P.leviOneP K ⊔ blockSL (K := K) P.free).map φ ⊓
        centralizer ((⁅(P.radicalP K).map φ, (P.radicalP K).map φ⁆ : Subgroup G) : Set G)) := by
    rw [← Subgroup.map_commutator, ← map_inf_centralizer_of_injective hφ, ← map_perfectCore,
      ← hSeq]
  have hS' : (blockSL (K := K) P'.free).map φ' =
      perfectCore ((P'.leviOneP K ⊔ blockSL (K := K) P'.free).map φ' ⊓
        centralizer ((⁅(P.radicalP K).map φ, (P.radicalP K).map φ⁆ : Subgroup G) : Set G)) := by
    rw [← hQeq, ← Subgroup.map_commutator, ← map_inf_centralizer_of_injective hφ',
      ← map_perfectCore, ← hSeq']
  rw [hS, hS']
  exact sup_eq_sup_of_perfectCore_inf_centralizer hMN' hQM hQM' hMM' hQZ

theorem complements_map_blockSL (hq : 4 ≤ Nat.card K) (hφ : Function.Injective φ)
    (hφ' : Function.Injective φ') (P : InvPlacement n k) (P' : InvPlacement n k')
    (hJ2 : 2 ≤ P.free.card) (hJ'2 : 2 ≤ P'.free.card)
    (hΛ : (perfectCore (centralizer {P.elt K})).map φ =
      (perfectCore (centralizer {P'.elt K})).map φ') :
    IsPGroup 2 ((P.radicalP K).map φ) ∧
      (blockSL (K := K) P.free).map φ ≤ normalizer (((P.radicalP K).map φ : Subgroup G) : Set G) ∧
      Disjoint ((P.radicalP K).map φ) ((blockSL (K := K) P.free).map φ) ∧
      Disjoint ((P.radicalP K).map φ) ((blockSL (K := K) P'.free).map φ') ∧
      (P.radicalP K).map φ ⊔ (blockSL (K := K) P.free).map φ =
        (P.radicalP K).map φ ⊔ (blockSL (K := K) P'.free).map φ' := by
  have hQeq := map_radicalP_eq hq hφ hφ' P P' hJ2 hJ'2 hΛ
  obtain ⟨hQp, -, hdisj, hMN, -⟩ := P.centralizer_inv_perfectCore hq (P.card_free ▸ hJ2)
  obtain ⟨-, -, hdisj', -, -⟩ := P'.centralizer_inv_perfectCore hq (P'.card_free ▸ hJ'2)
  refine ⟨hQp.map φ, (map_mono (le_sup_right.trans hMN)).trans (le_normalizer_map φ),
    disjoint_map_of_injective hφ (hdisj.mono_right le_sup_right), ?_,
    sup_map_blockSL_eq hq hφ hφ' P P' hJ2 hJ'2 hΛ⟩
  rw [← hQeq]
  exact disjoint_map_of_injective hφ' (hdisj'.mono_right le_sup_right)

theorem card_free_eq_of_map_perfectCore_eq (hq : 4 ≤ Nat.card K) (hφ : Function.Injective φ)
    (hφ' : Function.Injective φ') (P : InvPlacement n k) (P' : InvPlacement n k')
    (hk : 0 < k) (hk' : 0 < k') (hJ2 : 2 ≤ P.free.card) (hJ'2 : 2 ≤ P'.free.card)
    (hΛ : (perfectCore (centralizer {P.elt K})).map φ =
      (perfectCore (centralizer {P'.elt K})).map φ') :
    P.free.card = P'.free.card := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨-, hSN, hQS, hQS', hSS'⟩ := complements_map_blockSL hq hφ hφ' P P' hJ2 hJ'2 hΛ
  have h1 : Nat.card (blockSL (K := K) P.free) = Nat.card (blockSL (K := K) P'.free) := by
    rw [← card_map_of_injective hφ, ← card_map_of_injective hφ']
    exact Nat.card_congr (EPilot.mulEquivOfComplements hSN hQS hQS' hSS').toEquiv
  have hJlt : P.free.card < n := by have := P.card_free; omega
  have hJ'lt : P'.free.card < n := by have := P'.card_free; omega
  rw [card_blockSL_eq hJlt, card_blockSL_eq hJ'lt] at h1
  exact eq_of_card_specialLinearGroup_eq (by omega) (by omega) h1

theorem exists_conj_le_map_rootSL2 (hq : 4 ≤ Nat.card K) (hn : 4 ≤ n)
    (hφ : Function.Injective φ) (hφ' : Function.Injective φ') (P : InvPlacement n k)
    (P' : InvPlacement n k') (hk : 0 < k) (hk' : 0 < k') {a b : Fin n} (ha : a ∈ P.free)
    (hb : b ∈ P.free) (hab : a ≠ b)
    (hΛ : (perfectCore (centralizer {P.elt K})).map φ =
      (perfectCore (centralizer {P'.elt K})).map φ')
    {X : Subgroup G} (hXodd : Odd (Nat.card X)) (hXJ : X ≤ (rootSL2 (K := K) a b).map φ) :
    ∃ c d : Fin n, c ≠ d ∧ ∃ h ∈ φ'.range,
      X ≤ ((rootSL2 (K := K) c d).map φ').map (MulAut.conj h).toMonoidHom := by
  have hJ2 : 2 ≤ P.free.card := by
    calc 2 = ({a, b} : Finset (Fin n)).card := (Finset.card_pair hab).symm
      _ ≤ P.free.card := Finset.card_le_card (Finset.insert_subset ha
          (Finset.singleton_subset_iff.2 hb))
  have hJ'2 := two_le_card_free_of_map_perfectCore_eq hq hn hφ hφ' P P' hk hJ2 hΛ
  have hcardJ := card_free_eq_of_map_perfectCore_eq hq hφ hφ' P P' hk hk' hJ2 hJ'2 hΛ
  have hJ'lt : P'.free.card < n := by have := P'.card_free; omega
  have hQeq := map_radicalP_eq hq hφ hφ' P P' hJ2 hJ'2 hΛ
  obtain ⟨hQp, hSN, hQS, hQS', hSS'⟩ := complements_map_blockSL hq hφ hφ' P P' hJ2 hJ'2 hΛ
  have hJS : (rootSL2 (K := K) a b).map φ ≤ (blockSL (K := K) P.free).map φ :=
    map_mono (rootSL2_le_blockSL ha hb)
  obtain ⟨q₀, hq₀, hXq⟩ :=
    EPilot.exists_conj_le_inf_sup_of_complements_of_odd hQp hSN hQS hQS' hSS' hJS hXJ hXodd
  set ιS := EPilot.mulEquivOfComplements hSN hQS hQS' hSS' with hιS
  set e₀ := (blockSL (K := K) P.free).equivMapOfInjective φ hφ with he₀
  set e₁ := (blockSL (K := K) P'.free).equivMapOfInjective φ' hφ' with he₁
  set ψ : blockSL (K := K) P.free ≃* blockSL (K := K) P'.free := e₀.trans (ιS.trans e₁.symm)
    with hψdef
  obtain ⟨c, -, d, -, hcd, g₀, -, hψ⟩ :=
    exists_map_rootSL2_of_mulEquiv_blockSL hq hJ2 hcardJ hJ'lt ψ ha hb hab
  have hhom : φ'.comp ((blockSL (K := K) P'.free).subtype.comp ψ.toMonoidHom) =
      (((blockSL (K := K) P'.free).map φ').subtype.comp ιS.toMonoidHom).comp e₀.toMonoidHom := by
    ext j
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, coe_subtype, hψdef,
      MulEquiv.trans_apply]
    have h := coe_equivMapOfInjective_apply (blockSL (K := K) P'.free) φ' hφ'
      (e₁.symm (ιS (e₀ j)))
    rw [← he₁, MulEquiv.apply_symm_apply] at h
    exact h.symm
  have hJsub : ((rootSL2 (K := K) a b).subgroupOf (blockSL (K := K) P.free)).map
      e₀.toMonoidHom = ((rootSL2 (K := K) a b).map φ).subgroupOf
        ((blockSL (K := K) P.free).map φ) := by
    ext s
    constructor
    · rintro ⟨j, hj, rfl⟩
      rw [SetLike.mem_coe, mem_subgroupOf] at hj
      rw [mem_subgroupOf, MulEquiv.coe_toMonoidHom, he₀, coe_equivMapOfInjective_apply]
      exact mem_map_of_mem φ hj
    · intro hs
      rw [mem_subgroupOf] at hs
      obtain ⟨r, hr, hrs⟩ := hs
      obtain ⟨j, hjS, hjs⟩ := s.2
      have hrj : r = j := hφ (hrs.trans hjs.symm)
      subst hrj
      refine ⟨⟨r, hjS⟩, mem_subgroupOf.2 hr, Subtype.ext ?_⟩
      rw [MulEquiv.coe_toMonoidHom, he₀, coe_equivMapOfInjective_apply]
      exact hrs
  have hιJ : ((rootSL2 (K := K) a b).map φ ⊔ (P.radicalP K).map φ) ⊓
      (blockSL (K := K) P'.free).map φ' =
      ((rootSL2 (K := K) c d).map (MulAut.conj g₀).toMonoidHom).map φ' := by
    rw [← hψ, Subgroup.map_map (f := (blockSL (K := K) P'.free).subtype.comp ψ.toMonoidHom)
      (g := φ'), hhom, ← Subgroup.map_map, ← Subgroup.map_map, hJsub]
    exact (EPilot.map_mulEquivOfComplements hSN hQS hQS' hSS' hJS).symm
  have hconj : ∀ H : Subgroup (LinearFlag.projectiveSL n K),
      ((H.map (MulAut.conj g₀).toMonoidHom).map φ').map (MulAut.conj q₀).toMonoidHom =
        (H.map φ').map (MulAut.conj (q₀ * φ' g₀)).toMonoidHom := by
    intro H
    rw [Subgroup.map_map, Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [map_mul, map_mul, map_inv]
    group
  refine ⟨c, d, hcd, q₀ * φ' g₀, mul_mem ?_ ⟨g₀, rfl⟩, ?_⟩
  · rw [← hQeq] at hq₀
    obtain ⟨x, -, rfl⟩ := hq₀
    exact ⟨x, rfl⟩
  · rw [← hconj, ← hιJ]
    exact hXq

theorem exists_le_range_inf_centralizer_mulEquiv_blockSL (hq : 4 ≤ Nat.card K) (hn : 4 ≤ n)
    (hφ : Function.Injective φ) (hφ' : Function.Injective φ') (P : InvPlacement n k)
    (P' : InvPlacement n k') (hk : 0 < k) (hk' : 0 < k') {a b : Fin n} (ha : a ∈ P.free)
    (hb : b ∈ P.free) (hab : a ≠ b)
    (hΛ : (perfectCore (centralizer {P.elt K})).map φ =
      (perfectCore (centralizer {P'.elt K})).map φ')
    {X : Subgroup G} (hXodd : Odd (Nat.card X)) (hXJ : X ≤ (rootSL2 (K := K) a b).map φ) :
    ∃ P₀ : Subgroup G, P₀ ≤ φ'.range ⊓ centralizer (X : Set G) ∧
      Nonempty (P₀ ≃* blockSL (K := K) ({a, b}ᶜ : Finset (Fin n))) := by
  obtain ⟨c, d, hcd, h, hh, hXh⟩ :=
    exists_conj_le_map_rootSL2 hq hn hφ hφ' P P' hk hk' ha hb hab hΛ hXodd hXJ
  refine ⟨((blockSL (K := K) ({c, d}ᶜ : Finset (Fin n))).map φ').map
    (MulAut.conj h).toMonoidHom, le_inf ?_ ?_, ?_⟩
  · rintro _ ⟨_, ⟨s, -, rfl⟩, rfl⟩
    obtain ⟨y, rfl⟩ := hh
    exact ⟨y * s * y⁻¹, by simp [MulAut.conj_apply]⟩
  · rintro _ ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    rw [mem_centralizer_iff]
    intro x hx
    obtain ⟨_, ⟨r, hr, rfl⟩, rfl⟩ := hXh hx
    have hsr : Commute s r :=
      commute_blockSL_of_disjoint disjoint_compl_left s hs r hr
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc h * φ' r * h⁻¹ * (h * φ' s * h⁻¹) = h * (φ' (r * s)) * h⁻¹ := by
          rw [map_mul]; group
      _ = h * (φ' (s * r)) * h⁻¹ := by rw [hsr.eq]
      _ = h * φ' s * h⁻¹ * (h * φ' r * h⁻¹) := by rw [map_mul]; group
  · have hcd' : ({c, d}ᶜ : Finset (Fin n)).card = ({a, b}ᶜ : Finset (Fin n)).card := by
      rw [Finset.card_compl, Finset.card_compl, Finset.card_pair hcd, Finset.card_pair hab]
    have hcdn : ({c, d}ᶜ : Finset (Fin n)).card < n := by
      rw [Finset.card_compl, Finset.card_pair hcd, Fintype.card_fin]
      omega
    obtain ⟨eB⟩ := blockSL_mulEquiv_blockSL (K := K) hcdn hcd'
    exact ⟨((((blockSL (K := K) ({c, d}ᶜ : Finset (Fin n))).map φ').equivMapOfInjective _
      (MulAut.conj h).injective).symm.trans
      (((blockSL (K := K) ({c, d}ᶜ : Finset (Fin n)))).equivMapOfInjective _ hφ').symm).trans eB⟩

end Coordinates

section Setting

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_le_centralizer_mulEquiv_of_conj_eq_mul (hset : StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) {n : ℕ} {K : Type*} [Field K] [Finite K] [CharP K 2]
    (hq : 4 ≤ Nat.card K) (hn : 4 ≤ n) (e : L ≃* LinearFlag.projectiveSL n K) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {a b : Fin n} (hab : a ≠ b) {X : Subgroup G} (hXodd : Odd (Nat.card X))
    (hXJ : X ≤ ((rootSL2 (K := K) a b).map e.symm.toMonoidHom).map L.subtype) {g y : G}
    (hyD : y ∈ ((blockSL (K := K) ({a, b}ᶜ : Finset (Fin n))).map e.symm.toMonoidHom).map
      L.subtype)
    (hy : orderOf y = 2) (hg : g⁻¹ * t * g = t * y) :
    ∃ g₁ y₁ : G,
      y₁ ∈ ((blockSL (K := K) ({a, b}ᶜ : Finset (Fin n))).map e.symm.toMonoidHom).map
        L.subtype ∧
      orderOf y₁ = 2 ∧ g₁⁻¹ * t * g₁ = t * y₁ ∧
      ∃ P : Subgroup G, P ≤ centralizer (X : Set G) ⊓ centralizer ({t * y₁} : Set G) ∧
        Nonempty (P ≃* ((blockSL (K := K) ({a, b}ᶜ : Finset (Fin n))).map
          e.symm.toMonoidHom).map L.subtype) := by
  classical
  have htK : t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := hKt ▸ mem_zpowers t
  have htC : t ∈ centralizer (L : Set G) := htK.1
  set φ : LinearFlag.projectiveSL n K →* G := L.subtype.comp e.symm.toMonoidHom with hφdef
  have hφ : Function.Injective φ := L.subtype_injective.comp e.symm.injective
  have hφr : φ.range = L := EPilot.range_subtype_comp_mulEquiv_symm e
  have hφL : ∀ x, φ x ∈ L := fun x => hφr ▸ ⟨x, rfl⟩
  have hmap : ∀ H : Subgroup (LinearFlag.projectiveSL n K),
      (H.map e.symm.toMonoidHom).map L.subtype = H.map φ := fun H => by
    rw [Subgroup.map_map]
  rw [hmap] at hyD hXJ ⊢
  obtain ⟨y₀, hy₀D, rfl⟩ := hyD
  have hy₀2 : y₀ * y₀ = 1 := by
    apply hφ
    rw [map_mul, map_one, ← sq, ← hy, pow_orderOf_eq_one]
  have hy₀1 : y₀ ≠ 1 := by
    rintro rfl
    rw [map_one, orderOf_one] at hy
    exact absurd hy (by norm_num)
  have hIcard : ({a, b}ᶜ : Finset (Fin n)).card < n := by
    rw [Finset.card_compl, Finset.card_pair hab, Fintype.card_fin]
    omega
  obtain ⟨k, P, c, hPout, hc⟩ := exists_conj_eq_elt_of_mem_blockSL hIcard hy₀D hy₀2
  obtain ⟨haJ, hbJ, hJ2⟩ := P.free_card_two_le_of_outer_subset_compl_pair hab hPout
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h
    · exfalso
      apply hy₀1
      rw [P.elt_eq_one_of_eq_zero h0] at hc
      calc y₀ = c⁻¹ * (c * y₀ * c⁻¹) * c := by group
        _ = 1 := by rw [hc]; group
    · exact h
  set y₁ := φ (P.elt K) with hy₁def
  set g₁ := g * (φ c)⁻¹ with hg₁def
  have htc : φ c * t = t * φ c := mem_centralizer_iff.1 htC _ (hφL c)
  have hy₁c : y₁ = φ c * φ y₀ * (φ c)⁻¹ := by
    rw [hy₁def, ← hc, map_mul, map_mul, map_inv]
  have hg₁ : g₁⁻¹ * t * g₁ = t * y₁ := by
    have e1 : g₁⁻¹ * t * g₁ = φ c * (g⁻¹ * t * g) * (φ c)⁻¹ := by rw [hg₁def]; group
    rw [e1, hg, hy₁c]
    calc φ c * (t * φ y₀) * (φ c)⁻¹ = (φ c * t) * φ y₀ * (φ c)⁻¹ := by group
      _ = t * (φ c * φ y₀ * (φ c)⁻¹) := by rw [htc]; group
  have hy₁D : y₁ ∈ (blockSL (K := K) ({a, b}ᶜ : Finset (Fin n))).map φ :=
    ⟨P.elt K, P.elt_mem_blockSL hPout, rfl⟩
  have hy₁sq : y₁ * y₁ = 1 := by
    rw [hy₁def, ← map_mul, InvPlacement.elt, ← map_mul, P.mat_mul_self, map_one, map_one]
  have hy₁1 : y₁ ≠ 1 := by
    rw [hy₁c]
    intro h
    apply hy₀1
    apply hφ
    rw [map_one]
    calc φ y₀ = (φ c)⁻¹ * (φ c * φ y₀ * (φ c)⁻¹) * φ c := by group
      _ = 1 := by rw [h]; group
  have hy₁2 : orderOf y₁ = 2 := orderOf_eq_prime (by rw [sq]; exact hy₁sq) hy₁1
  refine ⟨g₁, y₁, hy₁D, hy₁2, hg₁, ?_⟩
  have ht'C : g₁⁻¹ * t * g₁ ∈ centralizer (CFSG.conjugate L g₁ : Set G) := by
    rw [mem_centralizer_iff]
    intro l hl
    exact mem_centralizer_singleton_iff.1 (EPilot.conjugate_le_centralizer_conj htC g₁ hl)
  have hy₁inv : y₁⁻¹ = y₁ := inv_eq_of_mul_eq_one_right hy₁sq
  have hty₁ : y₁ * t = t * y₁ := mem_centralizer_iff.1 htC _ (hφL _)
  have hw' : y₁⁻¹ * t ∈ centralizer (CFSG.conjugate L g₁ : Set G) := by
    rw [hy₁inv, hty₁, ← hg₁]
    exact ht'C
  have hΛeq := EPilot.perfectCore_inf_centralizer_eq_of_inv_mul_mem hset hOut htC ht
    (Or.inr hg₁) hw'
  have hΛ0 : (perfectCore (centralizer {P.elt K})).map φ =
      perfectCore (L ⊓ centralizer ({y₁} : Set G)) := by
    rw [map_perfectCore_centralizer_singleton hφ, hφr]
  have hy₁Λ : y₁ ∈ perfectCore (L ⊓ centralizer ({y₁} : Set G)) := by
    rw [← hΛ0]
    obtain ⟨-, hΛP, -, -, -⟩ := P.centralizer_inv_perfectCore hq (P.card_free ▸ hJ2)
    refine mem_map_of_mem φ ?_
    rw [hΛP]
    exact mem_sup_left P.elt_mem_radicalP
  have hy₁L' : y₁ ∈ CFSG.conjugate L g₁ := by
    rw [hΛeq] at hy₁Λ
    exact ((perfectCore_le _).trans inf_le_left) hy₁Λ
  set φ'₀ : LinearFlag.projectiveSL n K →* G := (MulAut.conj g₁⁻¹).toMonoidHom.comp φ
    with hφ'₀def
  have hφ'₀ : Function.Injective φ'₀ := (MulAut.conj g₁⁻¹).injective.comp hφ
  have hφ'₀r : φ'₀.range = CFSG.conjugate L g₁ := by
    rw [hφ'₀def, MonoidHom.range_comp, hφr]
    rfl
  obtain ⟨z₀, hz₀⟩ : y₁ ∈ φ'₀.range := hφ'₀r ▸ hy₁L'
  have hz₀2 : z₀ * z₀ = 1 := hφ'₀ (by rw [map_mul, hz₀, hy₁sq, map_one])
  obtain ⟨k', P', c', hc'⟩ := exists_conj_eq_elt hz₀2
  set φ' : LinearFlag.projectiveSL n K →* G := φ'₀.comp (MulAut.conj c'⁻¹).toMonoidHom
    with hφ'def
  have hφ' : Function.Injective φ' := hφ'₀.comp (MulAut.conj c'⁻¹).injective
  have hφ'r : φ'.range = CFSG.conjugate L g₁ := by
    rw [hφ'def, MonoidHom.range_comp, MonoidHom.range_eq_top.2 (MulAut.conj c'⁻¹).surjective,
      ← MonoidHom.range_eq_map, hφ'₀r]
  have hφ'P' : φ' (P'.elt K) = y₁ := by
    rw [hφ'def, MonoidHom.comp_apply, ← hc', ← hz₀]
    congr 1
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    group
  have hk' : 0 < k' := by
    rcases Nat.eq_zero_or_pos k' with h0 | h
    · exfalso
      apply hy₁1
      rw [← hφ'P', P'.elt_eq_one_of_eq_zero h0, map_one]
    · exact h
  have hΛ1 : (perfectCore (centralizer {P'.elt K})).map φ' =
      perfectCore (CFSG.conjugate L g₁ ⊓ centralizer ({y₁} : Set G)) := by
    rw [map_perfectCore_centralizer_singleton hφ', hφ'r, hφ'P']
  have hΛ : (perfectCore (centralizer {P.elt K})).map φ =
      (perfectCore (centralizer {P'.elt K})).map φ' := by
    rw [hΛ0, hΛ1, hΛeq]
  obtain ⟨P₀, hP₀, ⟨eP₀⟩⟩ := exists_le_range_inf_centralizer_mulEquiv_blockSL hq hn hφ hφ' P P'
    hk hk' haJ hbJ hab hΛ hXodd hXJ
  refine ⟨P₀, le_inf (hP₀.trans inf_le_right) ?_,
    ⟨eP₀.trans ((blockSL (K := K) ({a, b}ᶜ : Finset (Fin n))).equivMapOfInjective φ hφ)⟩⟩
  have hP₀L : P₀ ≤ CFSG.conjugate L g₁ := hφ'r ▸ hP₀.trans inf_le_left
  rw [← hg₁]
  exact hP₀L.trans (EPilot.conjugate_le_centralizer_conj htC g₁)

end Setting

end CFSG.SeitzReduction.LinearPilot
