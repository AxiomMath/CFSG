module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotClassUF5
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotClassVF3
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InBlk2
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotClassURankClassLift

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Quasithin (perfectCore perfectCore_le)
open scoped commutatorElement

variable {K : Type} [Field K]


section Main

variable [Finite K] [CharP K 2]

@[expose] noncomputable def uAutImage
    (β : (uCoreRadical K ⊔ uLevi K : Subgroup (adjointGroup .E7 K)) ≃*
      (uCoreRadical K ⊔ uLevi K : Subgroup (adjointGroup .E7 K)))
    (S : Subgroup (adjointGroup .E7 K)) : Subgroup (adjointGroup .E7 K) :=
  ((S.subgroupOf (uCoreRadical K ⊔ uLevi K)).map β.toMonoidHom).map
    (uCoreRadical K ⊔ uLevi K).subtype

theorem card_uAutImage
    (β : (uCoreRadical K ⊔ uLevi K : Subgroup (adjointGroup .E7 K)) ≃*
      (uCoreRadical K ⊔ uLevi K : Subgroup (adjointGroup .E7 K)))
    {S : Subgroup (adjointGroup .E7 K)} (hS : S ≤ uCoreRadical K ⊔ uLevi K) :
    Nat.card (uAutImage β S) = Nat.card S := by
  rw [uAutImage, card_map_of_injective (Subgroup.subtype_injective _),
    card_map_of_injective β.injective]
  exact Nat.card_congr (subgroupOfEquivOfLe hS).toEquiv

theorem leviAutOfAut_sq_eq_one
    (β : (uCoreRadical K ⊔ uLevi K : Subgroup (adjointGroup .E7 K)) ≃*
      (uCoreRadical K ⊔ uLevi K : Subgroup (adjointGroup .E7 K)))
    (hβ : ((uCoreRadical K).subgroupOf (uCoreRadical K ⊔ uLevi K)).map β.toMonoidHom =
      (uCoreRadical K).subgroupOf (uCoreRadical K ⊔ uLevi K))
    {m : uLevi K} (hm : (m : adjointGroup .E7 K) ^ 2 = 1) :
    ((EPilot.leviAutOfAut (uCoreRadical K) (uLevi K) disjoint_uCoreRadical_uLevi
      uLevi_le_normalizer_uCoreRadical β hβ m : uLevi K) : adjointGroup .E7 K) ^ 2 = 1 := by
  have hm' : m ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, hm]; rfl)
  rw [← Subgroup.coe_pow, ← map_pow, hm', map_one]
  rfl

theorem commutator_zpowers_leviAutOfAut_eq
    (β : (uCoreRadical K ⊔ uLevi K : Subgroup (adjointGroup .E7 K)) ≃*
      (uCoreRadical K ⊔ uLevi K : Subgroup (adjointGroup .E7 K)))
    (hβ : ((uCoreRadical K).subgroupOf (uCoreRadical K ⊔ uLevi K)).map β.toMonoidHom =
      (uCoreRadical K).subgroupOf (uCoreRadical K ⊔ uLevi K))
    {m : uLevi K} (hm : (m : adjointGroup .E7 K) ^ 2 = 1) :
    ⁅uCoreRadical K, zpowers ((EPilot.leviAutOfAut (uCoreRadical K) (uLevi K)
      disjoint_uCoreRadical_uLevi uLevi_le_normalizer_uCoreRadical β hβ m : uLevi K) :
        adjointGroup .E7 K)⁆ =
      uAutImage β ⁅uCoreRadical K, zpowers (m : adjointGroup .E7 K)⁆ := by
  set ι := EPilot.leviAutOfAut (uCoreRadical K) (uLevi K) disjoint_uCoreRadical_uLevi
    uLevi_le_normalizer_uCoreRadical β hβ with hι
  have hQ : ∀ a ∈ uCoreRadical K, ∀ b ∈ uCoreRadical K, a * b = b * a :=
    fun a ha b hb => uCoreRadical_comm ha hb
  have hm2 := leviAutOfAut_sq_eq_one β hβ hm
  ext x
  rw [mem_commutator_zpowers_iff hQ (uLevi_le_normalizer_uCoreRadical (ι m).2) hm2]
  constructor
  · rintro ⟨q, hq, rfl⟩
    set y := β.symm ⟨q, mem_sup_left hq⟩ with hy
    have hβy : β y = ⟨q, mem_sup_left hq⟩ := β.apply_symm_apply _
    have hyQ : (y : adjointGroup .E7 K) ∈ uCoreRadical K :=
      (EPilot.coe_mem_iff_of_map_eq hβ y).1 (by rw [hβy]; exact hq)
    have h := EPilot.leviAutOfAut_commutatorElement_eq disjoint_uCoreRadical_uLevi
      uLevi_le_normalizer_uCoreRadical hβ hQ m y hyQ
    rw [hβy] at h
    refine ⟨_, ⟨⁅y, inclusion le_sup_right m⁆, mem_subgroupOf.2 ?_, rfl⟩, h.symm⟩
    exact commutator_mem_commutator hyQ (mem_zpowers _)
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    obtain ⟨q, hq, hqz⟩ := (mem_commutator_zpowers_iff hQ (uLevi_le_normalizer_uCoreRadical m.2)
      hm).1 (mem_subgroupOf.1 hz)
    have hz' : z = ⁅(⟨q, mem_sup_left hq⟩ : (uCoreRadical K ⊔ uLevi K : Subgroup _)),
        inclusion le_sup_right m⁆ := Subtype.ext hqz.symm
    have h := EPilot.leviAutOfAut_commutatorElement_eq disjoint_uCoreRadical_uLevi
      uLevi_le_normalizer_uCoreRadical hβ hQ m ⟨q, mem_sup_left hq⟩ hq
    refine ⟨_, (EPilot.coe_mem_iff_of_map_eq hβ ⟨q, mem_sup_left hq⟩).2 hq, ?_⟩
    rw [h, hz']
    rfl

theorem rootSubgroup_smul_highRoot_le_uLevi (ε : ℤ) (hε : ε = 1 ∨ ε = -1) :
    (rootSubgroup .E7 K (ε • highRoot .E7)).subgroupOf (adjointGroup .E7 K) ≤ uLevi K := by
  refine le_trans ?_ highRootSL2_le_uLevi
  intro x hx
  rw [mem_subgroupOf] at hx ⊢
  rcases hε with rfl | rfl
  · rw [one_smul] at hx
    exact mem_sup_left hx
  · rw [neg_one_smul] at hx
    exact mem_sup_right hx

theorem exists_map_leviAutOfAut_le (hq : 4 ≤ Nat.card K)
    (β : (uCoreRadical K ⊔ uLevi K : Subgroup (adjointGroup .E7 K)) ≃*
      (uCoreRadical K ⊔ uLevi K : Subgroup (adjointGroup .E7 K)))
    (hβ : ((uCoreRadical K).subgroupOf (uCoreRadical K ⊔ uLevi K)).map β.toMonoidHom =
      (uCoreRadical K).subgroupOf (uCoreRadical K ⊔ uLevi K))
    (ε : ℤ) (hε : ε = 1 ∨ ε = -1) :
    ∃ X ∈ leviURootSubgroups K,
      ((((rootSubgroup .E7 K (ε • highRoot .E7)).subgroupOf (adjointGroup .E7 K)).subgroupOf
          (uLevi K)).map (EPilot.leviAutOfAut (uCoreRadical K) (uLevi K)
            disjoint_uCoreRadical_uLevi uLevi_le_normalizer_uCoreRadical β hβ).toMonoidHom).map
        (uLevi K).subtype ≤ X := by
  set ι := EPilot.leviAutOfAut (uCoreRadical K) (uLevi K) disjoint_uCoreRadical_uLevi
    uLevi_le_normalizer_uCoreRadical β hβ with hι
  set Xε := (rootSubgroup .E7 K (ε • highRoot .E7)).subgroupOf (adjointGroup .E7 K) with hXε
  have hXεN : Xε ∈ leviURootSubgroups K := rootSubgroup_smul_highRoot_mem_leviURootSubgroups ε hε
  have hXεM : Xε ≤ uLevi K := rootSubgroup_smul_highRoot_le_uLevi ε hε
  have hR : ∀ x ∈ radicalU K, ∀ y ∈ radicalU K, x * y = y * x := fun x hx y hy =>
    radicalU_comm hx hy
  set W := ⁅radicalU K, Xε⁆ with hW
  have hQa : ∀ a ∈ Xε, a ≠ 1 → ⁅uCoreRadical K, zpowers a⁆ = W := fun a ha ha1 => by
    rw [← commutator_radicalU_zpowers_eq_uCoreRadical hq ε hε ha,
      commutator_radicalU_zpowers_eq hXεN ha ha1]
  have hsq : ∀ a ∈ Xε, a ^ 2 = 1 := fun a ha => by
    obtain ⟨t, ht⟩ := mem_rootSubgroup.1 (mem_subgroupOf.1 ha)
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← ht, pow_two, ← pinnedX_add, CharTwo.add_self_eq_zero, pinnedX_zero]
    rfl
  set a₀ : adjointGroup .E7 K := ⟨pinnedX .E7 K (ε • highRoot .E7) 1, pinnedX_mem_adjointGroup _ _⟩
  have ha₀ : a₀ ∈ Xε := mem_subgroupOf.2 (mem_rootSubgroup.2 ⟨1, rfl⟩)
  have ha₀1 : a₀ ≠ 1 := fun h => one_ne_zero (pinnedX_injective .E7 K _
    ((congrArg Subtype.val h).trans (pinnedX_zero .E7 K _).symm))
  have hWΛ : W ≤ uCoreRadical K ⊔ uLevi K := by
    rw [← hQa a₀ ha₀ ha₀1]
    exact (commutator_mono le_sup_left ((zpowers_le).2 (mem_sup_right (hXεM ha₀)))).trans
      (commutator_le_self _)
  have hcardW : Nat.card W = Nat.card (uTopGroup K) :=
    card_commutator_radicalU_leviURootSubgroup hXεN
  have key : ∀ a (ha : a ∈ Xε), a ≠ 1 → ∃ X ∈ leviURootSubgroups K,
      ((ι ⟨a, hXεM ha⟩ : uLevi K) : adjointGroup .E7 K) ∈ X ∧
        ⁅radicalU K, X⁆ = uAutImage β W := by
    intro a ha ha1
    set m : uLevi K := ⟨a, hXεM ha⟩
    have hm2 : (m : adjointGroup .E7 K) ^ 2 = 1 := hsq a ha
    have ha'2 := leviAutOfAut_sq_eq_one β hβ hm2
    have ha'1 : ((ι m : uLevi K) : adjointGroup .E7 K) ≠ 1 := by
      intro h
      apply ha1
      have h' : ι m = ι 1 := by rw [map_one]; exact Subtype.ext h
      exact congrArg Subtype.val (ι.injective h')
    have ha'N : ((ι m : uLevi K) : adjointGroup .E7 K) ∈ leviU K := uLevi_le_leviU (ι m).2
    have hQa' : ⁅uCoreRadical K, zpowers ((ι m : uLevi K) : adjointGroup .E7 K)⁆ =
        uAutImage β W := by
      rw [commutator_zpowers_leviAutOfAut_eq β hβ hm2, hQa a ha ha1]
    have hcardQ' : Nat.card (⁅uCoreRadical K, zpowers ((ι m : uLevi K) :
        adjointGroup .E7 K)⁆ : Subgroup (adjointGroup .E7 K)) = Nat.card (uTopGroup K) := by
      rw [hQa', card_uAutImage β hWΛ, hcardW]
    have hlt : Nat.card (⁅radicalU K, zpowers ((ι m : uLevi K) : adjointGroup .E7 K)⁆ :
        Subgroup (adjointGroup .E7 K)) < Nat.card K ^ 9 := by
      have : Finite (ModGL .E7 K) := finite_modGL
      have h1 := card_commutator_zpowers_le_mul
        (show uCoreRadical K ≤ radicalU K from inf_le_right) hR
        (leviU_le_normalizer_radicalU ha'N) ha'2 (uComplElt K) uComplElt_mem_radicalU
        (fun h hh => exists_mem_uCoreRadical_mul_eq hq hh)
      rw [hcardQ', Nat.card_prod] at h1
      have hq1 : 1 < Nat.card K := Finite.one_lt_card
      calc _ ≤ Nat.card (uTopGroup K) * (Nat.card K * Nat.card K) := h1
        _ ≤ Nat.card K ^ 6 * (Nat.card K * Nat.card K) :=
            Nat.mul_le_mul_right _ card_uTopGroup_le
        _ = Nat.card K ^ 8 := by ring
        _ < Nat.card K ^ 9 := Nat.pow_lt_pow_right hq1 (by norm_num)
    obtain ⟨X, hX, haX⟩ := exists_mem_leviURootSubgroups_of_card_commutator_lt ha'N
      (orderOf_eq_prime ha'2 ha'1) hlt
    refine ⟨X, hX, haX, ?_⟩
    have hle : uAutImage β W ≤ ⁅radicalU K, X⁆ := by
      rw [← hQa']
      exact commutator_mono (show uCoreRadical K ≤ radicalU K from inf_le_right)
        ((zpowers_le).2 haX)
    have : Finite (ModGL .E7 K) := finite_modGL
    refine (eq_of_le_of_card_ge hle ?_).symm
    rw [card_commutator_radicalU_leviURootSubgroup hX, card_uAutImage β hWΛ, hcardW]
  obtain ⟨X₀, hX₀, -, hX₀W⟩ := key a₀ ha₀ ha₀1
  refine ⟨X₀, hX₀, ?_⟩
  rintro _ ⟨_, ⟨m, hm, rfl⟩, rfl⟩
  have hmX : (m : adjointGroup .E7 K) ∈ Xε := mem_subgroupOf.1 hm
  by_cases hm1 : (m : adjointGroup .E7 K) = 1
  · have : m = 1 := Subtype.ext hm1
    rw [this, map_one]
    exact one_mem _
  · obtain ⟨X, hX, hmX', hXW⟩ := key _ hmX hm1
    rw [rootSubgroup_eq_of_commutator_eq hX hX₀ (hXW.trans hX₀W.symm)] at hmX'
    exact hmX'

theorem not_isPGroup_highRootSL2 : ¬ IsPGroup 2 (EPilot.highRootSL2 .E7 K) := by
  obtain ⟨-, -, ⟨e, -⟩, -⟩ :=
    CFSG.RankThree.Chevalley.even_Chevalley_pinned_root_SL2_maps (τ := .E7) K
      (isRoot_highRoot .E7)
  intro h
  exact CFSG.QuasithinUnique.Lin2.not_isPGroup_sl2 CharTwo.two_eq_zero (h.of_equiv e.symm)

theorem f5aut_u (hq : 4 ≤ Nat.card K)
    (β : (uCoreRadical K ⊔ uLevi K : Subgroup (adjointGroup .E7 K)) ≃*
      (uCoreRadical K ⊔ uLevi K : Subgroup (adjointGroup .E7 K)))
    (hβ : ((uCoreRadical K).subgroupOf (uCoreRadical K ⊔ uLevi K)).map β.toMonoidHom =
      (uCoreRadical K).subgroupOf (uCoreRadical K ⊔ uLevi K)) :
    ∃ c : adjointGroup .E7 K,
      ((((EPilot.highRootSL2 .E7 K).subgroupOf (adjointGroup .E7 K)).subgroupOf (uLevi K)).map
          (EPilot.leviAutOfAut (uCoreRadical K) (uLevi K) disjoint_uCoreRadical_uLevi
            uLevi_le_normalizer_uCoreRadical β hβ).toMonoidHom).map (uLevi K).subtype =
        ((EPilot.highRootSL2 .E7 K).subgroupOf (adjointGroup .E7 K)).map
          (MulAut.conj c).toMonoidHom := by
  set ι := EPilot.leviAutOfAut (uCoreRadical K) (uLevi K) disjoint_uCoreRadical_uLevi
    uLevi_le_normalizer_uCoreRadical β hβ with hι
  set J := (EPilot.highRootSL2 .E7 K).subgroupOf (adjointGroup .E7 K) with hJdef
  set Xp := (rootSubgroup .E7 K (highRoot .E7)).subgroupOf (adjointGroup .E7 K) with hXpdef
  set Xm := (rootSubgroup .E7 K (-highRoot .E7)).subgroupOf (adjointGroup .E7 K) with hXmdef
  have hJ : J = Xp ⊔ Xm :=
    subgroupOf_sup (rootSubgroup_le_adjointGroup _) (rootSubgroup_le_adjointGroup _)
  have hXpM : Xp ≤ uLevi K := by
    have h := rootSubgroup_smul_highRoot_le_uLevi (K := K) 1 (Or.inl rfl)
    rwa [one_smul] at h
  have hXmM : Xm ≤ uLevi K := by
    have h := rootSubgroup_smul_highRoot_le_uLevi (K := K) (-1) (Or.inr rfl)
    rwa [neg_one_smul] at h
  have hJM : J ≤ uLevi K := highRootSL2_le_uLevi
  have himg : ((J.subgroupOf (uLevi K)).map ι.toMonoidHom).map (uLevi K).subtype =
      ((Xp.subgroupOf (uLevi K)).map ι.toMonoidHom).map (uLevi K).subtype ⊔
        ((Xm.subgroupOf (uLevi K)).map ι.toMonoidHom).map (uLevi K).subtype := by
    rw [hJ, subgroupOf_sup hXpM hXmM, Subgroup.map_sup, Subgroup.map_sup]
  obtain ⟨X₀, ⟨c₀, -, rfl⟩, h₀⟩ := exists_map_leviAutOfAut_le hq β hβ 1 (Or.inl rfl)
  obtain ⟨X₁, ⟨c₁, -, rfl⟩, h₁⟩ := exists_map_leviAutOfAut_le hq β hβ (-1) (Or.inr rfl)
  rw [one_smul] at h₀
  rw [neg_one_smul] at h₁
  obtain ⟨d, -, hXp⟩ := rootSubgroup_smul_highRoot_mem_leviURootSubgroups (K := K) 1 (Or.inl rfl)
  rw [one_smul] at hXp
  have hU : uRootGroup K = Xp.map (MulAut.conj d⁻¹).toMonoidHom := by
    rw [hXpdef, hXp, CFSG.LieType.Chevalley.map_conj_map_conj, inv_mul_cancel,
      CFSG.LieType.Chevalley.map_conj_one]
  set g := (c₀ * d⁻¹)⁻¹ * (c₁ * d⁻¹) with hg
  have hsup : (uRootGroup K).map (MulAut.conj c₀).toMonoidHom ⊔
      (uRootGroup K).map (MulAut.conj c₁).toMonoidHom =
        (Xp ⊔ Xp.map (MulAut.conj g).toMonoidHom).map (MulAut.conj (c₀ * d⁻¹)).toMonoidHom := by
    rw [hU, CFSG.LieType.Chevalley.map_conj_map_conj, CFSG.LieType.Chevalley.map_conj_map_conj,
      Subgroup.map_sup, CFSG.LieType.Chevalley.map_conj_map_conj, hg]
    congr 3
    group
  have hle : ((J.subgroupOf (uLevi K)).map ι.toMonoidHom).map (uLevi K).subtype ≤
      (Xp ⊔ Xp.map (MulAut.conj g).toMonoidHom).map (MulAut.conj (c₀ * d⁻¹)).toMonoidHom := by
    rw [himg, ← hsup]
    exact sup_le_sup h₀ h₁
  let eJ : J ≃* (((J.subgroupOf (uLevi K)).map ι.toMonoidHom).map (uLevi K).subtype :
      Subgroup (adjointGroup .E7 K)) :=
    (subgroupOfEquivOfLe hJM).symm.trans
      (((J.subgroupOf (uLevi K)).equivMapOfInjective ι.toMonoidHom ι.injective).trans
        (((J.subgroupOf (uLevi K)).map ι.toMonoidHom).equivMapOfInjective (uLevi K).subtype
          (uLevi K).subtype_injective))
  have hcard : Nat.card (((J.subgroupOf (uLevi K)).map ι.toMonoidHom).map (uLevi K).subtype :
      Subgroup (adjointGroup .E7 K)) = Nat.card J := (Nat.card_congr eJ.toEquiv).symm
  have hnp : ¬ IsPGroup 2 (((J.subgroupOf (uLevi K)).map ι.toMonoidHom).map (uLevi K).subtype :
      Subgroup (adjointGroup .E7 K)) := fun h => not_isPGroup_highRootSL2
    (h.of_equiv (eJ.symm.trans (subgroupOfEquivOfLe EPilot.highRootSL2_le_adjointGroup)))
  rcases isPGroup_or_eq_conj_highRoot_pair_subgroupOf (τ := .E7) (K := K) 2 g with hp | ⟨c, hc⟩
  · exact absurd ((hp.map _).to_le hle) hnp
  · refine ⟨c₀ * d⁻¹ * c, ?_⟩
    rw [hc, CFSG.LieType.Chevalley.map_conj_map_conj, ← hJ] at hle
    have : Finite (ModGL .E7 K) := finite_modGL
    exact eq_of_le_of_card_ge hle (by rw [card_map_of_injective (MulAut.conj _).injective, hcard])

theorem nonempty_centralizer_leviAutOfAut_u (hq : 4 ≤ Nat.card K)
    (β : (uCoreRadical K ⊔ uLevi K : Subgroup (adjointGroup .E7 K)) ≃*
      (uCoreRadical K ⊔ uLevi K : Subgroup (adjointGroup .E7 K)))
    (hβ : ((uCoreRadical K).subgroupOf (uCoreRadical K ⊔ uLevi K)).map β.toMonoidHom =
      (uCoreRadical K).subgroupOf (uCoreRadical K ⊔ uLevi K)) :
    Nonempty (centralizer ((((((EPilot.highRootSL2 .E7 K).subgroupOf
        (adjointGroup .E7 K)).subgroupOf (uLevi K)).map (EPilot.leviAutOfAut (uCoreRadical K)
          (uLevi K) disjoint_uCoreRadical_uLevi uLevi_le_normalizer_uCoreRadical β
            hβ).toMonoidHom).map (uLevi K).subtype : Subgroup (adjointGroup .E7 K)) :
        Set (adjointGroup .E7 K)) ≃* EPilot.perpLevi .E7 K) := by
  obtain ⟨c, hc⟩ := f5aut_u hq β hβ
  rw [hc]
  exact nonempty_centralizer_map_conj_highRootSL2_mulEquiv hq c

end Main

end CFSG.SeitzReduction.E7Pilot
