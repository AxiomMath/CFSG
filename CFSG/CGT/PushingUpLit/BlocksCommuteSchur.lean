module

public import CFSG.Quasithin.Background.A3Structure37Schur
public import CFSG.CGT.PushingUpLit.BlocksCommuteQuasi1

public section

namespace CFSG.CGT.PushingUpLit

open CFSG CFSG.RankThree.PartOne
open scoped commutatorElement

theorem schur_trivial_of_perfect {P : Type*} [CommGroup P] [Finite P] (Zq : Subgroup P)
    {SG TG : Type*} [Group SG] [Group TG] (σ : SG →* MulAut P) (τ : TG →* MulAut P)
    (hσ : ∀ s x, x ∈ Zq ↔ σ s x ∈ Zq) (hτ : ∀ t x, x ∈ Zq ↔ τ t x ∈ Zq)
    (hne : Zq ≠ ⊤)
    (hirr : ∀ J : Subgroup P, Zq ≤ J → (∀ s : SG, ∀ x ∈ J, σ s x ∈ J) → J = Zq ∨ J = ⊤)
    (hcomm : ∀ s t x, σ s (τ t x) * (τ t (σ s x))⁻¹ ∈ Zq)
    (hperf : commutator TG = ⊤) :
    ∀ t x, τ t x * x⁻¹ ∈ Zq := by
  classical
  have hmap : ∀ φ : MulAut P, (∀ x, x ∈ Zq ↔ φ x ∈ Zq) →
      Zq.map (φ : P ≃* P).toMonoidHom = Zq := by
    intro φ hφ
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hφ x).1 hx
    · intro hy
      refine ⟨φ.symm y, ?_, by simp⟩
      exact (hφ _).2 (by simpa using hy)
  let σ' : SG →* MulAut (P ⧸ Zq) :=
    { toFun := fun s => QuotientGroup.congr Zq Zq (σ s) (hmap (σ s) (hσ s))
      map_one' := by
        refine MulEquiv.ext fun q => ?_
        induction q using QuotientGroup.induction_on with
        | H x =>
          show (↑((σ 1) x) : P ⧸ Zq) = ↑x
          rw [map_one]; rfl
      map_mul' := fun s s' => by
        refine MulEquiv.ext fun q => ?_
        induction q using QuotientGroup.induction_on with
        | H x =>
          show (↑((σ (s * s')) x) : P ⧸ Zq) = ↑((σ s) ((σ s') x))
          rw [map_mul]; rfl }
  let τ' : TG →* MulAut (P ⧸ Zq) :=
    { toFun := fun t => QuotientGroup.congr Zq Zq (τ t) (hmap (τ t) (hτ t))
      map_one' := by
        refine MulEquiv.ext fun q => ?_
        induction q using QuotientGroup.induction_on with
        | H x =>
          show (↑((τ 1) x) : P ⧸ Zq) = ↑x
          rw [map_one]; rfl
      map_mul' := fun t t' => by
        refine MulEquiv.ext fun q => ?_
        induction q using QuotientGroup.induction_on with
        | H x =>
          show (↑((τ (t * t')) x) : P ⧸ Zq) = ↑((τ t) ((τ t') x))
          rw [map_mul]; rfl }
  have hnt : Nontrivial (P ⧸ Zq) := by
    obtain ⟨x, hx⟩ : ∃ x : P, x ∉ Zq := by
      by_contra h
      push Not at h
      exact hne (eq_top_iff.2 fun x _ => h x)
    exact ⟨⟨QuotientGroup.mk x, 1, fun h => hx ((QuotientGroup.eq_one_iff x).1 h)⟩⟩
  have hirr' : CFSG.Quasithin.XMod.IsIrrSec ↥(σ'.range) (⊥ : Subgroup (P ⧸ Zq)) ⊤ := by
    refine ⟨bot_lt_top, fun J hJ _ _ => ?_⟩
    have hZJ : Zq ≤ J.comap (QuotientGroup.mk' Zq) := fun x hx => by
      rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).2 hx]
      exact J.one_mem
    have hJσ : ∀ s : SG, ∀ x ∈ J.comap (QuotientGroup.mk' Zq),
        σ s x ∈ J.comap (QuotientGroup.mk' Zq) := by
      intro s x hx
      exact hJ ⟨σ' s, ⟨s, rfl⟩⟩ (QuotientGroup.mk x) hx
    rcases hirr _ hZJ hJσ with h | h
    · left
      refine (Subgroup.eq_bot_iff_forall J).2 fun q hq => ?_
      induction q using QuotientGroup.induction_on with
      | H x =>
        have : x ∈ J.comap (QuotientGroup.mk' Zq) := hq
        rw [h] at this
        exact (QuotientGroup.eq_one_iff x).2 this
    · right
      refine eq_top_iff.2 fun q _ => ?_
      induction q using QuotientGroup.induction_on with
      | H x =>
        have : x ∈ J.comap (QuotientGroup.mk' Zq) := by rw [h]; trivial
        exact this
  have hcomm' : ∀ s ∈ σ'.range, ∀ t ∈ τ'.range, s * t = t * s := by
    rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩
    refine MulEquiv.ext fun q => ?_
    induction q using QuotientGroup.induction_on with
    | H x =>
      show (↑((σ s) ((τ t) x)) : P ⧸ Zq) = ↑((τ t) ((σ s) x))
      exact (QuotientGroup.eq_iff_div_mem).2 (by simpa [div_eq_mul_inv] using hcomm s t x)
  have hab := CFSG.Quasithin.A37.commute_of_irreducible (σ'.range) (τ'.range) hirr' hcomm'
  have hker : τ'.ker = ⊤ := by
    refine eq_top_iff.mpr ?_
    rw [← hperf, _root_.commutator_def]
    refine Subgroup.commutator_le.mpr fun x _ y _ => ?_
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (hab _ ⟨x, rfl⟩ _ ⟨y, rfl⟩)
  intro t x
  have h1 : τ' t = 1 := by
    have : t ∈ τ'.ker := by rw [hker]; trivial
    exact this
  have h2 : τ' t (QuotientGroup.mk x) = QuotientGroup.mk x := by rw [h1]; rfl
  have h3 : (QuotientGroup.mk (τ t x) : P ⧸ Zq) = QuotientGroup.mk x := h2
  simpa [div_eq_mul_inv] using (QuotientGroup.eq_iff_div_mem).1 h3

variable {G : Type} [Group G] [Finite G]

theorem perfect_acts_trivially {X Y : Subgroup G} (hY : IsBlockOf Y)
    (hXN : X ≤ Subgroup.normalizer (Y : Set G)) (hperf : ⁅X, X⁆ = X)
    (hcomm : ∀ x ∈ X, ∀ l ∈ Y, ⁅x, l⁆ ∈ oTwoIn Y) :
    ∀ x ∈ X, ∀ u ∈ blockU Y, ⁅x, u⁆ ∈ blockZ Y := by
  classical
  have hUc : ∀ u v : ↥(blockU Y), u * v = v * u := fun u v =>
    Subtype.ext (blockU_commute hY.2 u.2 v.2)
  let _ : CommGroup ↥(blockU Y) := { (inferInstance : Group ↥(blockU Y)) with mul_comm := hUc }
  have hYU : ∀ g ∈ Subgroup.normalizer (Y : Set G), g ∈ Subgroup.normalizer (blockU Y : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro u
    refine ⟨fun hu => conj_mem_blockU hg hu, fun hu => ?_⟩
    have := conj_mem_blockU (inv_mem hg) hu
    simpa [mul_assoc] using this
  let σ : ↥Y →* MulAut ↥(blockU Y) := (Subgroup.normalizerMonoidHom (blockU Y)).comp
    (Subgroup.inclusion (fun g hg => hYU g (Subgroup.le_normalizer hg)))
  let τ : ↥X →* MulAut ↥(blockU Y) := (Subgroup.normalizerMonoidHom (blockU Y)).comp
    (Subgroup.inclusion (fun g hg => hYU g (hXN hg)))
  have hσval : ∀ (s : ↥Y) (x : ↥(blockU Y)), ((σ s x : ↥(blockU Y)) : G) = s * x * (s : G)⁻¹ :=
    fun s x => Subgroup.normalizerMonoidHom_apply_apply_coe (blockU Y) _ x
  have hτval : ∀ (t : ↥X) (x : ↥(blockU Y)), ((τ t x : ↥(blockU Y)) : G) = t * x * (t : G)⁻¹ :=
    fun t x => Subgroup.normalizerMonoidHom_apply_apply_coe (blockU Y) _ x
  let Zq : Subgroup ↥(blockU Y) := (blockZ Y).subgroupOf (blockU Y)
  have hmemZq : ∀ x : ↥(blockU Y), x ∈ Zq ↔ (x : G) ∈ blockZ Y := fun x => Iff.rfl
  have hσ : ∀ (s : ↥Y) (x : ↥(blockU Y)), x ∈ Zq ↔ σ s x ∈ Zq := by
    intro s x
    rw [hmemZq, hmemZq, hσval]
    refine ⟨fun hx => conj_mem_blockZ (Subgroup.le_normalizer s.2) hx, fun hx => ?_⟩
    have := conj_mem_blockZ (inv_mem (Subgroup.le_normalizer s.2)) hx
    simpa [mul_assoc] using this
  have hτ : ∀ (t : ↥X) (x : ↥(blockU Y)), x ∈ Zq ↔ τ t x ∈ Zq := by
    intro t x
    rw [hmemZq, hmemZq, hτval]
    refine ⟨fun hx => conj_mem_blockZ (hXN t.2) hx, fun hx => ?_⟩
    have := conj_mem_blockZ (inv_mem (hXN t.2)) hx
    simpa [mul_assoc] using this
  have hne : Zq ≠ ⊤ := by
    intro htop
    have : blockU Y ≤ blockZ Y := fun u hu => by
      have : (⟨u, hu⟩ : ↥(blockU Y)) ∈ Zq := by rw [htop]; trivial
      exact this
    exact absurd this (not_le_of_gt (blockZ_lt_of_short hY.2))
  have hirr : ∀ J : Subgroup ↥(blockU Y), Zq ≤ J → (∀ s : ↥Y, ∀ x ∈ J, σ s x ∈ J) →
      J = Zq ∨ J = ⊤ := by
    intro J hZJ hJσ
    have hZ' : blockZ Y ≤ J.map (blockU Y).subtype := by
      intro z hz
      exact ⟨⟨z, blockZ_le_blockU Y hz⟩, hZJ ((hmemZq _).2 hz), rfl⟩
    have hU' : J.map (blockU Y).subtype ≤ blockU Y := by
      rintro _ ⟨v, -, rfl⟩
      exact v.2
    have hN : ∀ g ∈ Y, ∀ n ∈ J.map (blockU Y).subtype, g * n * g⁻¹ ∈ J.map (blockU Y).subtype := by
      rintro g hg _ ⟨v, hv, rfl⟩
      refine ⟨σ ⟨g, hg⟩ v, hJσ ⟨g, hg⟩ v hv, ?_⟩
      rw [Subgroup.coe_subtype, hσval]
    rcases blockU_irred_of_short hY.2 _ hZ' hU' hN with h | h
    · left
      have h2 : (blockZ Y).subgroupOf (blockU Y) = Zq := rfl
      apply Subgroup.map_injective (blockU Y).subtype_injective
      rw [h, ← h2, Subgroup.map_subgroupOf_eq_of_le (blockZ_le_blockU Y)]
    · right
      apply Subgroup.map_injective (blockU Y).subtype_injective
      rw [h, Subgroup.map_top, Subgroup.range_subtype]
  have hcomm' : ∀ (s : ↥Y) (t : ↥X) (x : ↥(blockU Y)),
      σ s (τ t x) * (τ t (σ s x))⁻¹ ∈ Zq := by
    intro s t x
    have hc : ⁅(s : G), (t : G)⁆ ∈ oTwoIn Y := by
      have := inv_mem (hcomm t t.2 s s.2)
      simpa [commutatorElement_def, mul_assoc] using this
    have hv : (t : G) * ((s : G) * x * (s : G)⁻¹) * (t : G)⁻¹ ∈ blockU Y :=
      conj_mem_blockU (hXN t.2) (conj_mem_blockU (Subgroup.le_normalizer s.2) x.2)
    have hcv := blockU_comm_of_short hY.2 _ hv _ hc
    have heq : σ s (τ t x) = τ t (σ s x) := by
      refine Subtype.ext ?_
      rw [hσval, hτval, hτval, hσval]
      have e : (s : G) * ((t : G) * x * (t : G)⁻¹) * (s : G)⁻¹ =
          ⁅(s : G), (t : G)⁆ * ((t : G) * ((s : G) * x * (s : G)⁻¹) * (t : G)⁻¹) *
            ⁅(s : G), (t : G)⁆⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e, ← hcv]
      group
    rw [heq, mul_inv_cancel]
    exact Zq.one_mem
  have hperf' : commutator ↥X = ⊤ := (Subgroup.isPerfect_iff.2 hperf).commutator_eq_top
  have key := schur_trivial_of_perfect Zq σ τ hσ hτ hne hirr hcomm' hperf'
  intro a ha u hu
  have := key ⟨a, ha⟩ ⟨u, hu⟩
  rw [hmemZq] at this
  simpa [commutatorElement_def, hτval] using this

end CFSG.CGT.PushingUpLit
