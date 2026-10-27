module

public import CFSG.CGT.PushingUpLit.ThmOne.Basic
public import CFSG.CGT.PushingUpLit.ThmOne.SchurAut

public section

namespace CFSG.CGT.PushingUpLit.ThmOne

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit
open CFSG.Quasithin.XMod (IsIrrSec)
open scoped commutatorElement

section Ambient

variable {G : Type} [Group G] [Finite G]

theorem exists_tildeU_action {X : Subgroup G} (hX : IsShortGroup ↥X) :
    ∃ (W : Type) (_ : CommGroup W) (_ : Finite W) (π : ↥(blockU X) →* W)
      (ρ : ↥(Subgroup.normalizer (X : Set G)) →* MulAut W) (S : Subgroup (MulAut W)),
      Function.Surjective π ∧ (∀ u : ↥(blockU X), π u = 1 ↔ (u : G) ∈ blockZ X) ∧
      (∀ (g : ↥(Subgroup.normalizer (X : Set G))) (u v : ↥(blockU X)),
        (v : G) = g * u * (g : G)⁻¹ → ρ g (π u) = π v) ∧
      (∀ w : W, w ^ 2 = 1) ∧ IsIrrSec ↥S (⊥ : Subgroup W) ⊤ ∧
      (∀ s ∈ S, ∃ l : ↥(Subgroup.normalizer (X : Set G)), (l : G) ∈ X ∧ s = ρ l) ∧
      IsField ↥(CFSG.Quasithin.XMod.eqvEnd ↥S W) ∧ CharP ↥(CFSG.Quasithin.XMod.eqvEnd ↥S W) 2 ∧
      (∀ g : ↥(Subgroup.normalizer (X : Set G)),
        (∀ l ∈ X, ∀ u ∈ blockU X, ⁅⁅(g : G), l⁆, u⁆ ∈ blockZ X) → ∀ s ∈ S, s * ρ g = ρ g * s) ∧
      ∀ g : ↥(Subgroup.normalizer (X : Set G)),
        ρ g = 1 ↔ ∀ u ∈ blockU X, ⁅(g : G), u⁆ ∈ blockZ X := by
  classical
  let _ : CommGroup ↥(blockU X) :=
    { (inferInstance : Group ↥(blockU X)) with
      mul_comm := fun u v => Subtype.ext (blockU_mul_comm hX u.2 v.2) }
  have hNU : Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (blockU X : Set G) :=
    fun g hg => Subgroup.mem_normalizer_iff.mpr fun u => ⟨fun hu => conj_mem_blockU hg hu,
      fun hu => by simpa [mul_assoc] using conj_mem_blockU (inv_mem hg) hu⟩
  let τ : ↥(Subgroup.normalizer (X : Set G)) →* MulAut ↥(blockU X) :=
    (Subgroup.normalizerMonoidHom (blockU X)).comp (Subgroup.inclusion hNU)
  have hτval : ∀ (g : ↥(Subgroup.normalizer (X : Set G))) (x : ↥(blockU X)),
      ((τ g x : ↥(blockU X)) : G) = g * x * (g : G)⁻¹ :=
    fun g x => Subgroup.normalizerMonoidHom_apply_apply_coe (blockU X) _ x
  let ι : ↥X →* ↥(Subgroup.normalizer (X : Set G)) := Subgroup.inclusion Subgroup.le_normalizer
  let σ : ↥X →* MulAut ↥(blockU X) := τ.comp ι
  have hσval : ∀ (s : ↥X) (x : ↥(blockU X)), ((σ s x : ↥(blockU X)) : G) = s * x * (s : G)⁻¹ :=
    fun s x => hτval (ι s) x
  let Zq : Subgroup ↥(blockU X) := (blockZ X).subgroupOf (blockU X)
  have hτZ : ∀ (g : ↥(Subgroup.normalizer (X : Set G))) (x : ↥(blockU X)),
      x ∈ Zq ↔ τ g x ∈ Zq := by
    intro g x
    show (x : G) ∈ blockZ X ↔ ((τ g x : ↥(blockU X)) : G) ∈ blockZ X
    rw [hτval]
    refine ⟨fun hx => conj_mem_blockZ g.2 hx, fun hx => ?_⟩
    simpa [mul_assoc] using conj_mem_blockZ (inv_mem g.2) hx
  have hne : Zq ≠ ⊤ := by
    intro htop
    have : blockU X ≤ blockZ X := fun u hu => by
      have : (⟨u, hu⟩ : ↥(blockU X)) ∈ Zq := by rw [htop]; trivial
      exact this
    exact absurd this (not_le_of_gt (blockZ_lt_of_short hX))
  have hirr : ∀ J : Subgroup ↥(blockU X), Zq ≤ J → (∀ s : ↥X, ∀ x ∈ J, σ s x ∈ J) →
      J = Zq ∨ J = ⊤ := by
    intro J hZJ hJσ
    have hZ' : blockZ X ≤ J.map (blockU X).subtype := fun z hz =>
      ⟨⟨z, blockZ_le_blockU X hz⟩, hZJ (show (⟨z, _⟩ : ↥(blockU X)) ∈ Zq from hz), rfl⟩
    have hU' : J.map (blockU X).subtype ≤ blockU X := by
      rintro _ ⟨v, -, rfl⟩
      exact v.2
    have hN : ∀ g ∈ X, ∀ n ∈ J.map (blockU X).subtype,
        g * n * g⁻¹ ∈ J.map (blockU X).subtype := by
      rintro g hg _ ⟨v, hv, rfl⟩
      exact ⟨σ ⟨g, hg⟩ v, hJσ ⟨g, hg⟩ v hv, by rw [Subgroup.coe_subtype, hσval]⟩
    rcases blockU_irred_of_short hX _ hZ' hU' hN with h | h
    · left
      apply Subgroup.map_injective (blockU X).subtype_injective
      rw [h, Subgroup.map_subgroupOf_eq_of_le (blockZ_le_blockU X)]
    · right
      apply Subgroup.map_injective (blockU X).subtype_injective
      rw [h, Subgroup.map_top, Subgroup.range_subtype]
  obtain ⟨σ', τ', hσ', hτ', hirr'⟩ := exists_quotAction Zq σ τ (fun s x => hτZ (ι s) x) hτZ hne hirr
  have h2 : ∀ w : ↥(blockU X) ⧸ Zq, w ^ 2 = 1 := by
    intro w
    induction w using QuotientGroup.induction_on with
    | H x =>
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact sq_mem_blockZ_of_isShortGroup hX x.2
  have hστ : ∀ s : ↥X, σ' s = τ' (ι s) := fun s => MulEquiv.ext fun q => by
    induction q using QuotientGroup.induction_on with
    | H x => rw [hσ', hτ']; rfl
  obtain ⟨hfin, hfield, hchar⟩ := CFSG.Quasithin.XMod.eqvEnd_isField_charTwo h2 hirr'
  refine ⟨↥(blockU X) ⧸ Zq, inferInstance, inferInstance, QuotientGroup.mk' Zq, τ', σ'.range,
    QuotientGroup.mk'_surjective Zq, fun u => QuotientGroup.eq_one_iff u, ?_, h2, hirr', ?_,
    hfield, hchar, ?_, ?_⟩
  · intro g u v huv
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, hτ']
    congr 1
    exact Subtype.ext ((hτval g u).trans huv.symm)
  · rintro _ ⟨s, rfl⟩
    exact ⟨ι s, s.2, hστ s⟩
  · rintro g hg _ ⟨s, rfl⟩
    refine MulEquiv.ext fun q => ?_
    induction q using QuotientGroup.induction_on with
    | H x =>
      show σ' s (τ' g x) = τ' g (σ' s x)
      rw [hτ', hσ', hσ', hτ', QuotientGroup.eq]
      have hw : (s : G) * (g * x * (g : G)⁻¹) * (s : G)⁻¹ ∈ blockU X :=
        conj_mem_blockU (Subgroup.le_normalizer s.2) (conj_mem_blockU g.2 x.2)
      have hz := inv_mem (hg s s.2 _ (inv_mem hw))
      show (((σ s (τ g x))⁻¹ * τ g (σ s x) : ↥(blockU X)) : G) ∈ blockZ X
      convert hz using 1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hσval, hτval, commutatorElement_def]
      group
  · intro g
    constructor
    · intro h1 u hu
      have h3 : τ' g ((⟨u⁻¹, inv_mem hu⟩ : ↥(blockU X)) : ↥(blockU X) ⧸ Zq) =
          ((⟨u⁻¹, inv_mem hu⟩ : ↥(blockU X)) : ↥(blockU X) ⧸ Zq) := by rw [h1]; rfl
      rw [hτ', QuotientGroup.eq] at h3
      have h4 : (((τ g ⟨u⁻¹, inv_mem hu⟩)⁻¹ * ⟨u⁻¹, inv_mem hu⟩ : ↥(blockU X)) : G) ∈ blockZ X :=
        h3
      convert h4 using 1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hτval, commutatorElement_def]
      group
    · intro h1
      refine MulEquiv.ext fun q => ?_
      induction q using QuotientGroup.induction_on with
      | H x =>
        show τ' g x = x
        rw [hτ', QuotientGroup.eq]
        have h4 := h1 _ (inv_mem x.2)
        show (((τ g x)⁻¹ * x : ↥(blockU X)) : G) ∈ blockZ X
        convert h4 using 1
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, hτval, commutatorElement_def]
        group

theorem commutator_mem_blockZ_of_pow_two_pow {X : Subgroup G} (hX : IsShortGroup ↥X) {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) {k : ℕ} (hk : g ^ 2 ^ k = 1)
    (hc : ∀ l ∈ X, ∀ u ∈ blockU X, ⁅⁅g, l⁆, u⁆ ∈ blockZ X) :
    ∀ u ∈ blockU X, ⁅g, u⁆ ∈ blockZ X := by
  obtain ⟨W, _, _, -, ρ, S, -, -, -, hW, hirr, -, -, -, hcomm, htriv⟩ := exists_tildeU_action hX
  have hW2 : IsPGroup 2 W := fun w => ⟨1, by rw [pow_one]; exact hW w⟩
  refine (htriv ⟨g, hg⟩).mp (eq_one_of_commute_irreducible_of_pow_two_pow hW2 hirr
    (hcomm ⟨g, hg⟩ hc) (k := k) ?_)
  rw [← map_pow, show (⟨g, hg⟩ : ↥(Subgroup.normalizer (X : Set G))) ^ 2 ^ k = 1 from
    Subtype.ext (by simpa using hk), map_one]

theorem commutator_commutator_mem_blockZ {X : Subgroup G} (hX : IsShortGroup ↥X) {g h : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) (hh : h ∈ Subgroup.normalizer (X : Set G))
    (hcg : ∀ l ∈ X, ∀ u ∈ blockU X, ⁅⁅g, l⁆, u⁆ ∈ blockZ X)
    (hch : ∀ l ∈ X, ∀ u ∈ blockU X, ⁅⁅h, l⁆, u⁆ ∈ blockZ X) :
    ∀ u ∈ blockU X, ⁅⁅g, h⁆, u⁆ ∈ blockZ X := by
  obtain ⟨W, _, _, -, ρ, S, -, -, -, -, hirr, -, -, -, hcomm, htriv⟩ := exists_tildeU_action hX
  have hab := CFSG.Quasithin.A37.commute_of_irreducible S
    (Subgroup.centralizer (S : Set (MulAut W))) hirr
    (fun s hs t ht => Subgroup.mem_centralizer_iff.mp ht s hs) (ρ ⟨g, hg⟩)
    (Subgroup.mem_centralizer_iff.mpr (hcomm ⟨g, hg⟩ hcg)) (ρ ⟨h, hh⟩)
    (Subgroup.mem_centralizer_iff.mpr (hcomm ⟨h, hh⟩ hch))
  have h1 : ρ ⁅(⟨g, hg⟩ : ↥(Subgroup.normalizer (X : Set G))), ⟨h, hh⟩⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hab
  exact (htriv _).mp h1

theorem commutator_eq_one_of_commutator_mem_blockZ {X : Subgroup G} (hX : IsShortGroup ↥X)
    {g : G} (hg : g ∈ Subgroup.normalizer (X : Set G))
    (hc : ∀ l ∈ X, ⁅g, l⁆ ∈ Subgroup.centralizer (blockU X : Set G))
    (htriv : ∀ u ∈ blockU X, ⁅g, u⁆ ∈ blockZ X) :
    g ∈ Subgroup.centralizer (blockU X : Set G) := by
  have key2 : ∀ a ∈ blockU X, ∀ b ∈ blockU X, ⁅g, a * b⁆ = ⁅g, a⁆ * ⁅g, b⁆ := by
    intro a ha b hb
    have hab : a * ⁅g, b⁆ = ⁅g, b⁆ * a := blockU_mul_comm hX ha (htriv b hb).1
    calc ⁅g, a * b⁆ = ⁅g, a⁆ * (a * ⁅g, b⁆ * a⁻¹) := by
          simp only [commutatorElement_def]; group
      _ = ⁅g, a⁆ * ⁅g, b⁆ := by rw [hab, mul_inv_cancel_right]
  have key3 : ∀ l ∈ X, ∀ v ∈ blockU X, ⁅g, l * v * l⁻¹⁆ = ⁅g, v⁆ := by
    intro l hl v hv
    have hw : l * (g * v * g⁻¹) * l⁻¹ ∈ blockU X :=
      conj_mem_blockU (Subgroup.le_normalizer hl) (conj_mem_blockU hg hv)
    have hcw : ⁅g, l⁆ * (l * (g * v * g⁻¹) * l⁻¹) = (l * (g * v * g⁻¹) * l⁻¹) * ⁅g, l⁆ :=
      (Subgroup.mem_centralizer_iff.mp (hc l hl) _ hw).symm
    have hzl : l * ⁅g, v⁆ * l⁻¹ = ⁅g, v⁆ := by
      rw [Subgroup.mem_centralizer_iff.mp (htriv v hv).2 l hl, mul_inv_cancel_right]
    calc ⁅g, l * v * l⁻¹⁆ =
          (⁅g, l⁆ * (l * (g * v * g⁻¹) * l⁻¹) * ⁅g, l⁆⁻¹) * (l * v * l⁻¹)⁻¹ := by
          simp only [commutatorElement_def]; group
      _ = (l * (g * v * g⁻¹) * l⁻¹) * (l * v * l⁻¹)⁻¹ := by rw [hcw, mul_inv_cancel_right]
      _ = l * ⁅g, v⁆ * l⁻¹ := by simp only [commutatorElement_def]; group
      _ = ⁅g, v⁆ := hzl
  have hle : ⁅blockU X, X⁆ ≤ Subgroup.centralizer ({g} : Set G) := by
    refine Subgroup.commutator_le.2 fun u hu l hl => ?_
    have hu' : l * u⁻¹ * l⁻¹ ∈ blockU X :=
      conj_mem_blockU (Subgroup.le_normalizer hl) (inv_mem hu)
    have h1 : ⁅g, ⁅u, l⁆⁆ = 1 := by
      rw [show ⁅u, l⁆ = u * (l * u⁻¹ * l⁻¹) by simp [commutatorElement_def, mul_assoc],
        key2 u hu _ hu', key3 l hl _ (inv_mem hu), ← key2 u hu _ (inv_mem hu), mul_inv_cancel,
        commutatorElement_one_right]
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
  rw [blockU_commutator_eq_self hX.residual_eq] at hle
  exact Subgroup.mem_centralizer_iff.mpr fun u hu =>
    Subgroup.mem_centralizer_singleton_iff.mp (hle hu)

omit [Finite G] in
theorem commutator_mem_blockZ_of_mem_centralizer {X : Subgroup G} {c : G}
    (hc : c ∈ Subgroup.centralizer (blockU X : Set G)) {u : G} (hu : u ∈ blockU X) :
    ⁅c, u⁆ ∈ blockZ X := by
  rw [commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_centralizer_iff.mp hc u hu).symm]
  exact one_mem _

theorem le_centralizer_blockU_of_isPGroup {X P : Subgroup G} (hX : IsShortGroup ↥X)
    (hP : IsPGroup 2 P) (hPN : P ≤ Subgroup.normalizer (X : Set G))
    (hc : ∀ g ∈ P, ∀ l ∈ X, ⁅g, l⁆ ∈ Subgroup.centralizer (blockU X : Set G)) :
    P ≤ Subgroup.centralizer (blockU X : Set G) := by
  intro g hg
  obtain ⟨k, hk⟩ := hP ⟨g, hg⟩
  have hk' : g ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  exact commutator_eq_one_of_commutator_mem_blockZ hX (hPN hg) (hc g hg)
    (commutator_mem_blockZ_of_pow_two_pow hX (hPN hg) hk' fun l hl _ hu =>
      commutator_mem_blockZ_of_mem_centralizer (hc g hg l hl) hu)

theorem le_centralizer_blockU_of_le_centralizerModCore {X P : Subgroup G} (hX : IsShortGroup ↥X)
    (hP : IsPGroup 2 P) (hPC : P ≤ centralizerModCore X) :
    P ≤ Subgroup.centralizer (blockU X : Set G) :=
  le_centralizer_blockU_of_isPGroup hX hP (fun _ hg => (hPC hg).1) fun _ hg l hl =>
    Subgroup.mem_centralizer_iff.mpr fun u hu => blockU_comm_of_short hX u hu _ ((hPC hg).2 l hl)

theorem blockU_le_inf_centralizer_of_isSylowOf {X M R : Subgroup G} (hX : IsShortGroup ↥X)
    (hXM : X ≤ M) (hR : IsSylowOf 2 R (centralizerModCore X ⊓ M)) :
    blockU X ≤ R ⊓ Subgroup.centralizer (R : Set G) :=
  le_inf ((blockU_le_oTwoIn X).trans (oTwoIn_self_le_of_isSylowOf_centralizerModCore_inf hXM hR))
    (Subgroup.le_centralizer_iff.mp
      (le_centralizer_blockU_of_le_centralizerModCore hX hR.2.1 (hR.1.trans inf_le_left)))

end Ambient

end CFSG.CGT.PushingUpLit.ThmOne
