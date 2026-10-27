module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.CharacterTheory.Semidihedral.Principal.FreeSixCharacterDefectFourSupport

public section

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.Principal
  CFSG.Semidihedral.Principal.FreeSix

open scoped Classical

namespace CFSG.KleinFourBlocks

variable {G : Type*} [Group G]

theorem klein_four_cases {V : Subgroup G} (hV : IsKleinFour V) {t s : G} (htV : t ∈ V)
    (hsV : s ∈ V) (ht1 : t ≠ 1) (hs1 : s ≠ 1) (hst : s ≠ t) {v : G} (hv : v ∈ V) :
    v = 1 ∨ v = t ∨ v = s ∨ v = t * s := by
  have : IsKleinFour V := hV
  by_cases h1 : v = 1
  · exact Or.inl h1
  by_cases h2 : v = t
  · exact Or.inr (Or.inl h2)
  by_cases h3 : v = s
  · exact Or.inr (Or.inr (Or.inl h3))
  right; right; right
  have hmul := IsKleinFour.eq_mul_of_ne_all (x := (⟨t, htV⟩ : V)) (y := ⟨s, hsV⟩)
    (z := ⟨v, hv⟩) (fun h => ht1 (congrArg Subtype.val h)) (fun h => hs1 (congrArg Subtype.val h))
    (fun h => hst (congrArg Subtype.val h).symm) (fun h => h1 (congrArg Subtype.val h))
    (fun h => h2 (congrArg Subtype.val h)) (fun h => h3 (congrArg Subtype.val h))
  exact congrArg Subtype.val hmul

theorem klein_four_eq_closure {V : Subgroup G} (hV : IsKleinFour V) {t s : G} (htV : t ∈ V)
    (hsV : s ∈ V) (ht1 : t ≠ 1) (hs1 : s ≠ 1) (hst : s ≠ t) :
    V = Subgroup.closure ({t, s} : Set G) := by
  have ht : t ∈ Subgroup.closure ({t, s} : Set G) := Subgroup.subset_closure (by simp)
  have hs : s ∈ Subgroup.closure ({t, s} : Set G) := Subgroup.subset_closure (by simp)
  apply le_antisymm
  · intro v hv
    rcases klein_four_cases hV htV hsV ht1 hs1 hst hv with h | h | h | h <;> rw [h]
    · exact Subgroup.one_mem _
    · exact ht
    · exact hs
    · exact Subgroup.mul_mem _ ht hs
  · rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact htV
    · exact hsV

theorem mem_dV_of_commute_pair {V : Subgroup G} (hV : IsKleinFour V) {t s : G} (htV : t ∈ V)
    (hsV : s ∈ V) (ht1 : t ≠ 1) (hs1 : s ≠ 1) (hst : s ≠ t) {x : G} (hxt : t * x = x * t)
    (hxs : s * x = x * s) : x ∈ dV V := by
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  rcases klein_four_cases hV htV hsV ht1 hs1 hst hv with h | h | h | h <;> rw [h]
  · rw [one_mul, mul_one]
  · exact hxt
  · exact hxs
  · rw [mul_assoc, hxs, ← mul_assoc, hxt, mul_assoc]

theorem exists_normalizer_swap {V : Subgroup G} (hV : IsKleinFour V)
    (hAut : Function.Surjective V.normalizerMonoidHom) {a b : G} (ha : a ∈ V) (hb : b ∈ V)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) :
    ∃ m ∈ mV V, m * a * m⁻¹ = b ∧ m * b * m⁻¹ = a ∧
      ∀ c ∈ V, c ≠ a → c ≠ b → m * c * m⁻¹ = c := by
  have : IsKleinFour V := hV
  set a' : V := ⟨a, ha⟩ with ha'
  set b' : V := ⟨b, hb⟩ with hb'
  have ha1' : a' ≠ 1 := fun h => ha1 (congrArg Subtype.val h)
  have hb1' : b' ≠ 1 := fun h => hb1 (congrArg Subtype.val h)
  let σ : V ≃* V := IsKleinFour.mulEquiv (Equiv.swap a' b')
    (Equiv.swap_apply_of_ne_of_ne ha1'.symm hb1'.symm)
  obtain ⟨m, hm⟩ := hAut σ
  have hcalc : ∀ x : V, (m : G) * (x : G) * (m : G)⁻¹ = ((σ x : V) : G) := fun x => by
    rw [← hm]; rfl
  refine ⟨m, m.2, ?_, ?_, ?_⟩
  · rw [show a = (a' : G) from rfl, hcalc a']
    exact congrArg Subtype.val (Equiv.swap_apply_left a' b')
  · rw [show b = (b' : G) from rfl, hcalc b']
    exact congrArg Subtype.val (Equiv.swap_apply_right a' b')
  · intro c hc hca hcb
    have := hcalc ⟨c, hc⟩
    rw [this]
    exact congrArg Subtype.val (Equiv.swap_apply_of_ne_of_ne
      (fun h => hca (congrArg Subtype.val h)) (fun h => hcb (congrArg Subtype.val h)))

theorem isConj_of_mem_V {V : Subgroup G} (hV : IsKleinFour V)
    (hAut : Function.Surjective V.normalizerMonoidHom) {a b : G} (ha : a ∈ V) (hb : b ∈ V)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) : IsConj a b := by
  obtain ⟨m, -, hm, -⟩ := exists_normalizer_swap hV hAut ha hb ha1 hb1
  exact isConj_iff.mpr ⟨m, hm⟩

theorem exists_y_splitting {V : Subgroup G} [Finite G] (hV : IsKleinFour V)
    (hAut : Function.Surjective V.normalizerMonoidHom) {t s : G} (htV : t ∈ V) (hsV : s ∈ V)
    (ht1 : t ≠ 1) (hs1 : s ≠ 1) (hst : s ≠ t) :
    ∃ y : G, y ∈ cT t ∧ y ∈ mV V ∧ y * s * y⁻¹ = t * s ∧
      ∀ x ∈ cT t ⊓ mV V, x ∈ dV V ∨ y⁻¹ * x ∈ dV V := by
  have htt : t * t = 1 := FreeSix.mul_self hV htV
  have htsV : t * s ∈ V := V.mul_mem htV hsV
  have hts1 : t * s ≠ 1 := fun h => hst (mul_left_cancel (h.trans htt.symm))
  obtain ⟨m, hmM, hms, -, hfix⟩ := exists_normalizer_swap hV hAut hsV htsV hs1 hts1
  have hmt : m * t * m⁻¹ = t := hfix t htV (Ne.symm hst) (fun h => hs1
    (mul_left_cancel (a := t) (by rw [mul_one]; exact h.symm)))
  have hmC : m ∈ cT t := by
    apply DihedralAssociates.mem_centralizer_zpowers_of_commute
    calc m * t = m * t * m⁻¹ * m := by group
      _ = t * m := by rw [hmt]
  have hmD : m ∉ dV V := by
    intro hD
    have hcomm : s * m = m * s := Subgroup.mem_centralizer_iff.mp hD s hsV
    have h1 : m * s * m⁻¹ = s := by rw [← hcomm, mul_inv_cancel_right]
    rw [hms] at h1
    exact ht1 (mul_right_cancel (h1.trans (one_mul s).symm))
  refine ⟨m, hmC, hmM, hms, fun x hx => ?_⟩
  let L : Subgroup (mV V) := (cT t).subgroupOf (mV V)
  let H' : Subgroup L := ((dV V).subgroupOf (mV V)).subgroupOf L
  have hidx : H'.index = 2 := relIndex_dV_cT hV hAut htV ht1
  let yL : L := ⟨⟨m, hmM⟩, hmC⟩
  let xL : L := ⟨⟨x, hx.2⟩, hx.1⟩
  have hyL : yL ∉ H' := hmD
  by_cases hxL : xL ∈ H'
  · exact Or.inl hxL
  · right
    have h : yL⁻¹ * xL ∈ H' :=
      (Subgroup.mul_mem_iff_of_index_two hidx).mpr
        (iff_of_false (fun h' => hyL (inv_mem_iff.mp h')) hxL)
    exact h

theorem hfour_of_hAut {V : Subgroup G} (hV : IsKleinFour V)
    (hAut : Function.Surjective V.normalizerMonoidHom) {t : G} (htV : t ∈ V) (ht1 : t ≠ 1) :
    ∀ U : Subgroup G, IsKleinFour U → t ∈ U → U ≤ cT t → subgroupsConjugate U V →
      ∃ c ∈ cT t, U.map (MulAut.conj c).toMonoidHom = V := by
  intro U _ htU _ ⟨g, hg⟩
  have hmapV : ∀ m ∈ mV V, V.map (MulAut.conj m).toMonoidHom = V := by
    intro m hm
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp hm y).mp hy
    · intro hx
      refine ⟨m⁻¹ * x * m, ?_, ?_⟩
      · have h' := (Subgroup.mem_normalizer_iff.mp ((mV V).inv_mem hm) x).mp hx
        rwa [inv_inv] at h'
      · change m * (m⁻¹ * x * m) * m⁻¹ = x
        group
  have ht'V : g * t * g⁻¹ ∈ V := by
    rw [← hg]
    exact ⟨t, htU, rfl⟩
  have ht'1 : g * t * g⁻¹ ≠ 1 := fun h => ht1 (conj_eq_one_iff.mp h)
  obtain ⟨m, hmM, hmt', -, -⟩ := exists_normalizer_swap hV hAut ht'V htV ht'1 ht1
  have hct : (m * g) * t * (m * g)⁻¹ = t := by
    calc (m * g) * t * (m * g)⁻¹ = m * (g * t * g⁻¹) * m⁻¹ := by group
      _ = t := hmt'
  refine ⟨m * g, ?_, ?_⟩
  · apply DihedralAssociates.mem_centralizer_zpowers_of_commute
    calc (m * g) * t = (m * g) * t * (m * g)⁻¹ * (m * g) := by group
      _ = t * (m * g) := by rw [hct]
  · rw [← conjugation_subgroup_map_mul U g m, hg]
    exact hmapV m hmM

theorem closure_pair_cT_eq_vInC {V : Subgroup G} (hV : IsKleinFour V) {t : G} (sC : cT t)
    (htV : t ∈ V) (hsV : (sC : G) ∈ V) (ht1 : t ≠ 1) (hs1 : (sC : G) ≠ 1) (hst : (sC : G) ≠ t) :
    Subgroup.closure ({⟨t, element_mem_centralizer_zpowers t⟩, sC} : Set (cT t)) =
      V.subgroupOf (cT t) := by
  apply Subgroup.map_injective (cT t).subtype_injective
  rw [Subgroup.map_subgroupOf_eq_of_le (le_cT hV htV), MonoidHom.map_closure, Set.image_pair]
  exact (klein_four_eq_closure hV htV hsV ht1 hs1 hst).symm

theorem card_centralizer_singleton_eq_card_dV {V : Subgroup G} (hV : IsKleinFour V) {t : G}
    (sC : cT t) (htV : t ∈ V) (hsV : (sC : G) ∈ V) (ht1 : t ≠ 1) (hs1 : (sC : G) ≠ 1)
    (hst : (sC : G) ≠ t) :
    Nat.card (Subgroup.centralizer ({sC} : Set (cT t))) = Nat.card (dV V) := by
  have hmap : (Subgroup.centralizer ({sC} : Set (cT t))).map (cT t).subtype = dV V := by
    ext x
    simp only [Subgroup.mem_map, Subgroup.coe_subtype, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine mem_dV_of_commute_pair hV htV hsV ht1 hs1 hst ?_ (congrArg Subtype.val hy).symm
      exact Subgroup.mem_centralizer_iff.mp y.2 t (Subgroup.mem_zpowers t)
    · intro hx
      refine ⟨⟨x, dV_le_cT htV hx⟩, Subtype.ext ?_, rfl⟩
      exact Subgroup.mem_centralizer_iff.mp hx _ hsV |>.symm
  rw [← hmap, Subgroup.card_map_of_injective (cT t).subtype_injective]

end CFSG.KleinFourBlocks
