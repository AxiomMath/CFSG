module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2Centralizer
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2RootSL2
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotPositionB
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotPositionPerfectOdd

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.EvenSmallLie CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin (perfectCore perfectCore_le le_perfectCore_of_perfect perfectCore_perfect
  map_perfectCore)

theorem exists_map_rootSL2_of_mulEquiv_blockSL_of_three_le' {n : ℕ} {K : Type*} [Field K]
    [Finite K] [CharP K 2] {I I' : Finset (Fin n)} (hI : 3 ≤ I.card) (hII' : I.card = I'.card)
    (hI'n : I'.card < n)
    (ψ : blockSL (K := K) I ≃* blockSL (K := K) I') {a b : Fin n} (ha : a ∈ I) (hb : b ∈ I)
    (hab : a ≠ b) :
    ∃ c ∈ I', ∃ d ∈ I', c ≠ d ∧ ∃ g ∈ blockSL (K := K) I',
      ((rootSL2 (K := K) a b).subgroupOf (blockSL (K := K) I)).map
          ((blockSL (K := K) I').subtype.comp ψ.toMonoidHom) =
        (rootSL2 (K := K) c d).map (MulAut.conj g).toMonoidHom := by
  by_cases h2 : Nat.card K = 2
  · exact exists_map_rootSL2_of_mulEquiv_blockSL_two h2 hI hII' hI'n ψ ha hb hab
  · exact exists_map_rootSL2_of_mulEquiv_blockSL (four_le_card_of_card_ne_two h2) (by omega) hII'
      hI'n ψ ha hb hab

section Coordinates

variable {G : Type*} [Group G] {n : ℕ} {K : Type*} [Field K] [Finite K] [CharP K 2]
  {φ φ' : LinearFlag.projectiveSL n K →* G}

theorem map_radicalP_eq_of_rank_one (hn : 5 ≤ n) (hφ : Function.Injective φ)
    (hφ' : Function.Injective φ') (P P' : InvPlacement n 1)
    (hΛ : (perfectCore (centralizer {P.elt K})).map φ =
      (perfectCore (centralizer {P'.elt K})).map φ') :
    (P'.radicalP K).map φ' = (P.radicalP K).map φ := by
  obtain ⟨hQp, hΛeq, -, hMN, -⟩ := P.centralizer_inv_perfectCore_of_rank_one (K := K) hn
  obtain ⟨hQp', hΛeq', -, hMN', -⟩ := P'.centralizer_inv_perfectCore_of_rank_one (K := K) hn
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
        (fun T hT h1 h2 => P.le_radicalP_of_isPGroup_perfectCore_of_rank_one hn hT h1 h2) hQp'
        hQ'Λ hΛN'
    · exact P'.le_radicalP_of_isPGroup_perfectCore_of_rank_one hn (isPGroup_comap_map hφ' hQp)
        (comap_map_le hφ' hΛ hQΛ) (le_normalizer_comap_map hΛ hΛN)
  rw [heq, map_comap_map_eq hΛ hQΛ]

variable [Finite G]

theorem sup_map_blockSL_eq_of_rank_one (hn : 5 ≤ n) (hφ : Function.Injective φ)
    (hφ' : Function.Injective φ') (P P' : InvPlacement n 1)
    (hΛ : (perfectCore (centralizer {P.elt K})).map φ =
      (perfectCore (centralizer {P'.elt K})).map φ') :
    (P.radicalP K).map φ ⊔ (blockSL (K := K) P.free).map φ =
      (P.radicalP K).map φ ⊔ (blockSL (K := K) P'.free).map φ' := by
  have hQeq := map_radicalP_eq_of_rank_one hn hφ hφ' P P' hΛ
  obtain ⟨-, hΛeq, hdisj, hMN, hSeq⟩ := P.centralizer_inv_perfectCore_of_rank_one (K := K) hn
  obtain ⟨-, hΛeq', hdisj', -, hSeq'⟩ := P'.centralizer_inv_perfectCore_of_rank_one (K := K) hn
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

theorem complements_map_blockSL_of_rank_one (hn : 5 ≤ n) (hφ : Function.Injective φ)
    (hφ' : Function.Injective φ') (P P' : InvPlacement n 1)
    (hΛ : (perfectCore (centralizer {P.elt K})).map φ =
      (perfectCore (centralizer {P'.elt K})).map φ') :
    IsPGroup 2 ((P.radicalP K).map φ) ∧
      (blockSL (K := K) P.free).map φ ≤ normalizer (((P.radicalP K).map φ : Subgroup G) : Set G) ∧
      Disjoint ((P.radicalP K).map φ) ((blockSL (K := K) P.free).map φ) ∧
      Disjoint ((P.radicalP K).map φ) ((blockSL (K := K) P'.free).map φ') ∧
      (P.radicalP K).map φ ⊔ (blockSL (K := K) P.free).map φ =
        (P.radicalP K).map φ ⊔ (blockSL (K := K) P'.free).map φ' := by
  have hQeq := map_radicalP_eq_of_rank_one hn hφ hφ' P P' hΛ
  obtain ⟨hQp, -, hdisj, hMN, -⟩ := P.centralizer_inv_perfectCore_of_rank_one (K := K) hn
  obtain ⟨-, -, hdisj', -, -⟩ := P'.centralizer_inv_perfectCore_of_rank_one (K := K) hn
  refine ⟨hQp.map φ, (map_mono (le_sup_right.trans hMN)).trans (le_normalizer_map φ),
    disjoint_map_of_injective hφ (hdisj.mono_right le_sup_right), ?_,
    sup_map_blockSL_eq_of_rank_one hn hφ hφ' P P' hΛ⟩
  rw [← hQeq]
  exact disjoint_map_of_injective hφ' (hdisj'.mono_right le_sup_right)

theorem exists_conj_le_map_rootSL2_of_rank_one (hn : 5 ≤ n)
    (hφ : Function.Injective φ) (hφ' : Function.Injective φ') (P P' : InvPlacement n 1)
    {a b : Fin n} (ha : a ∈ P.free) (hb : b ∈ P.free) (hab : a ≠ b)
    (hΛ : (perfectCore (centralizer {P.elt K})).map φ =
      (perfectCore (centralizer {P'.elt K})).map φ')
    {X : Subgroup G} (hXodd : Odd (Nat.card X)) (hXJ : X ≤ (rootSL2 (K := K) a b).map φ) :
    ∃ c d : Fin n, c ≠ d ∧ ∃ h ∈ φ'.range,
      X ≤ ((rootSL2 (K := K) c d).map φ').map (MulAut.conj h).toMonoidHom := by
  have hJ3 : 3 ≤ P.free.card := by rw [P.card_free]; omega
  have hcardJ : P.free.card = P'.free.card := by rw [P.card_free, P'.card_free]
  have hJ'lt : P'.free.card < n := by rw [P'.card_free]; omega
  have hQeq := map_radicalP_eq_of_rank_one hn hφ hφ' P P' hΛ
  obtain ⟨hQp, hSN, hQS, hQS', hSS'⟩ := complements_map_blockSL_of_rank_one hn hφ hφ' P P' hΛ
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
    exists_map_rootSL2_of_mulEquiv_blockSL_of_three_le' hJ3 hcardJ hJ'lt ψ ha hb hab
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

theorem exists_le_range_inf_centralizer_mulEquiv_blockSL_of_rank_one (hn : 5 ≤ n)
    (hφ : Function.Injective φ) (hφ' : Function.Injective φ') (P P' : InvPlacement n 1)
    {a b : Fin n} (ha : a ∈ P.free) (hb : b ∈ P.free) (hab : a ≠ b)
    (hΛ : (perfectCore (centralizer {P.elt K})).map φ =
      (perfectCore (centralizer {P'.elt K})).map φ')
    {X : Subgroup G} (hXodd : Odd (Nat.card X)) (hXJ : X ≤ (rootSL2 (K := K) a b).map φ) :
    ∃ P₀ : Subgroup G, P₀ ≤ φ'.range ⊓ centralizer (X : Set G) ∧
      Nonempty (P₀ ≃* blockSL (K := K) ({a, b}ᶜ : Finset (Fin n))) := by
  obtain ⟨c, d, hcd, h, hh, hXh⟩ :=
    exists_conj_le_map_rootSL2_of_rank_one hn hφ hφ' P P' ha hb hab hΛ hXodd hXJ
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

theorem exists_le_centralizer_mulEquiv_of_conj_eq_mul_of_transvection (hset : StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) {n : ℕ} {K : Type*} [Field K] [Finite K] [CharP K 2]
    (hn : 5 ≤ n) (e : L ≃* LinearFlag.projectiveSL n K) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {a b : Fin n} (hab : a ≠ b) {X : Subgroup G} (hXodd : Odd (Nat.card X))
    (hXJ : X ≤ ((rootSL2 (K := K) a b).map e.symm.toMonoidHom).map L.subtype) {g : G} {y : L}
    (hyD : e y ∈ blockSL (K := K) ({a, b}ᶜ : Finset (Fin n)))
    (hy : IsInvolutionClass 1 (e y)) (hg : g⁻¹ * t * g = t * y) (hgy : g * y * g⁻¹ ∈ L)
    (hy' : IsInvolutionClass 1 (e ⟨g * y * g⁻¹, hgy⟩)) :
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
  rw [hmap] at hXJ ⊢
  set y₀ := e y with hy₀def
  have hφy₀ : φ y₀ = y := by
    show (L.subtype.comp e.symm.toMonoidHom) (e y) = y
    simp
  have hy₀2 : y₀ * y₀ = 1 := by
    rw [← sq, ← hy.orderOf_eq_two one_ne_zero, pow_orderOf_eq_one]
  have hIcard : ({a, b}ᶜ : Finset (Fin n)).card < n := by
    rw [Finset.card_compl, Finset.card_pair hab, Fintype.card_fin]
    omega
  obtain ⟨k, P, c, hPout, hc⟩ := exists_conj_eq_elt_of_mem_blockSL hIcard hyD hy₀2
  have hPcl : IsInvolutionClass 1 (P.elt K) := hc ▸ hy.conj c
  have hk : k = 1 := P.eq_of_isInvolutionClass hPcl
  subst hk
  obtain ⟨haJ, hbJ, -⟩ := P.free_card_two_le_of_outer_subset_compl_pair hab hPout
  set y₁ := φ (P.elt K) with hy₁def
  set g₁ := g * (φ c)⁻¹ with hg₁def
  have htc : φ c * t = t * φ c := mem_centralizer_iff.1 htC _ (hφL c)
  have hy₁c : y₁ = φ c * y * (φ c)⁻¹ := by
    rw [hy₁def, ← hc, map_mul, map_mul, map_inv, hφy₀]
  have hg₁ : g₁⁻¹ * t * g₁ = t * y₁ := by
    have e1 : g₁⁻¹ * t * g₁ = φ c * (g⁻¹ * t * g) * (φ c)⁻¹ := by rw [hg₁def]; group
    rw [e1, hg, hy₁c]
    calc φ c * (t * y) * (φ c)⁻¹ = (φ c * t) * y * (φ c)⁻¹ := by group
      _ = t * (φ c * y * (φ c)⁻¹) := by rw [htc]; group
  have hy₁D : y₁ ∈ (blockSL (K := K) ({a, b}ᶜ : Finset (Fin n))).map φ :=
    ⟨P.elt K, P.elt_mem_blockSL hPout, rfl⟩
  have hy₁sq : y₁ * y₁ = 1 := by
    rw [hy₁def, ← map_mul, InvPlacement.elt, ← map_mul, P.mat_mul_self, map_one, map_one]
  have hy₁1 : y₁ ≠ 1 := fun h => hPcl.ne_one one_ne_zero (hφ (by rw [map_one]; exact h))
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
  set φ'₀ : LinearFlag.projectiveSL n K →* G := (MulAut.conj g₁⁻¹).toMonoidHom.comp φ
    with hφ'₀def
  have hφ'₀ : Function.Injective φ'₀ := (MulAut.conj g₁⁻¹).injective.comp hφ
  have hφ'₀r : φ'₀.range = CFSG.conjugate L g₁ := by
    rw [hφ'₀def, MonoidHom.range_comp, hφr]
    rfl
  set z₀ := e ⟨g * y * g⁻¹, hgy⟩ with hz₀def
  have hφz₀ : φ z₀ = g * y * g⁻¹ := by
    show (L.subtype.comp e.symm.toMonoidHom) (e ⟨g * y * g⁻¹, hgy⟩) = _
    simp
  have hz₀ : φ'₀ z₀ = y₁ := by
    rw [hφ'₀def, MonoidHom.comp_apply, hφz₀, hy₁c, hg₁def]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    group
  obtain ⟨P', c', hc'⟩ := exists_conj_eq_elt_of_isInvolutionClass_one hy'
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
  have hΛ1 : (perfectCore (centralizer {P'.elt K})).map φ' =
      perfectCore (CFSG.conjugate L g₁ ⊓ centralizer ({y₁} : Set G)) := by
    rw [map_perfectCore_centralizer_singleton hφ', hφ'r, hφ'P']
  have hΛ : (perfectCore (centralizer {P.elt K})).map φ =
      (perfectCore (centralizer {P'.elt K})).map φ' := by
    rw [hΛ0, hΛ1, hΛeq]
  obtain ⟨P₀, hP₀, ⟨eP₀⟩⟩ := exists_le_range_inf_centralizer_mulEquiv_blockSL_of_rank_one hn hφ
    hφ' P P' haJ hbJ hab hΛ hXodd hXJ
  refine ⟨P₀, le_inf (hP₀.trans inf_le_right) ?_,
    ⟨eP₀.trans ((blockSL (K := K) ({a, b}ᶜ : Finset (Fin n))).equivMapOfInjective φ hφ)⟩⟩
  have hP₀L : P₀ ≤ CFSG.conjugate L g₁ := hφ'r ▸ hP₀.trans inf_le_left
  rw [← hg₁]
  exact hP₀L.trans (EPilot.conjugate_le_centralizer_conj htC g₁)

theorem not_normal_map_oddCore_of_conj_eq_mul_of_transvection (hset : StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) {n : ℕ} {K : Type*} [Field K] [Finite K] [CharP K 2]
    (hn : 5 ≤ n) (e : L ≃* LinearFlag.projectiveSL n K) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {a b : Fin n} (hab : a ≠ b) {X : Subgroup G} (hXodd : Odd (Nat.card X))
    (hXJ : X ≤ ((rootSL2 (K := K) a b).map e.symm.toMonoidHom).map L.subtype) {g : G} {y : L}
    (hyD : e y ∈ blockSL (K := K) ({a, b}ᶜ : Finset (Fin n)))
    (hy : IsInvolutionClass 1 (e y)) (hg : g⁻¹ * t * g = t * y) (hgy : g * y * g⁻¹ ∈ L)
    (hy' : IsInvolutionClass 1 (e ⟨g * y * g⁻¹, hgy⟩)) (htX : t ∈ centralizer (X : Set G))
    (hDX : ((blockSL (K := K) ({a, b}ᶜ : Finset (Fin n))).map e.symm.toMonoidHom).map L.subtype ≤
      centralizer (X : Set G))
    (hDq : CFSG.Open.IsQuasisimple
      (((blockSL (K := K) ({a, b}ᶜ : Finset (Fin n))).map e.symm.toMonoidHom).map L.subtype))
    (hZD : Odd (Nat.card (center
      (((blockSL (K := K) ({a, b}ᶜ : Finset (Fin n))).map e.symm.toMonoidHom).map L.subtype))))
    (hOutD : Group.IsSolvable (Outer
      ((((blockSL (K := K) ({a, b}ᶜ : Finset (Fin n))).map e.symm.toMonoidHom).map L.subtype) ⧸
        center (((blockSL (K := K) ({a, b}ᶜ : Finset (Fin n))).map e.symm.toMonoidHom).map
          L.subtype))))
    (hsyl : ∀ U : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
      IsPGroup 2 U →
      U ≤ centralizer (((((blockSL (K := K) ({a, b}ᶜ : Finset (Fin n))).map
          e.symm.toMonoidHom).map L.subtype).subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) :
        Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
      Nat.card U ≤ 2) :
    ¬ (((((blockSL (K := K) ({a, b}ᶜ : Finset (Fin n))).map e.symm.toMonoidHom).map
        L.subtype).subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal := by
  have htK : t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := hKt ▸ mem_zpowers t
  have hDt : ((blockSL (K := K) ({a, b}ᶜ : Finset (Fin n))).map e.symm.toMonoidHom).map
      L.subtype ≤ centralizer ({t} : Set G) :=
    (map_subtype_le _).trans (le_centralizer_of_mem_centralizer htK.1)
  obtain ⟨-, y₁, hy₁D, hy₁, -, P, hP, hPD⟩ :=
    exists_le_centralizer_mulEquiv_of_conj_eq_mul_of_transvection hset hOut hn e ht hKt hab hXodd
      hXJ hyD hy hg hgy hy'
  exact not_normal_map_oddCore_centralizer_of_mulEquiv_of_odd_center htX ht hDX hDq hZD hOutD hDt
    hsyl hy₁D hy₁ (Or.inr rfl) hP hPD

end Setting

end CFSG.SeitzReduction.LinearPilot
