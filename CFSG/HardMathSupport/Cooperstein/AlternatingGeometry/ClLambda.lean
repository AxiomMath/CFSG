module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ClNodes
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.IsolatedBlocksAuto
public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.SFour.OffenderHoff
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ClIsoCount

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm MulAction CFSG.AGLEmbedding CFSG.Quasithin CFSG.Open CFSG.RankThree.PartTwo
  CFSG.QuasithinUnique CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.Offender (IsExp2 orbitStab)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem hnf_of_unmatched {S L : Subgroup G} {d : ℕ} (θ : ↥(L ⊔ S) →* Perm (Fin d))
    (hz : ∃ z : Fin d, ∀ y, z ≠ y →
      swap z y ∉ (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm (Fin d)))) :
    ∀ A : Subgroup G, IsMaxElemAbelian S A →
      ¬ ((¬ ∃ p, ∀ g ∈ (A.subgroupOf (L ⊔ S)).map θ, g p = p) ∧
        (∀ i : Fin d, Nat.card (orbit ((A.subgroupOf (L ⊔ S)).map θ) i) = 2) ∧
        Nat.card (orbitStab ((A.subgroupOf (L ⊔ S)).map θ)) =
          Nat.card ((A.subgroupOf (L ⊔ S)).map θ)) := by
  classical
  rintro A hAm ⟨-, h2, hcard⟩
  obtain ⟨z, hzy⟩ := hz
  set E := (A.subgroupOf (L ⊔ S)).map θ with hE
  have hAJ : A ≤ thompsonJ S := le_iSup₂ (f := fun (A : Subgroup G) (_ : IsMaxElemAbelian S A) => A) A hAm
  have hEW : E ≤ ((thompsonJ S).subgroupOf (L ⊔ S)).map θ :=
    Subgroup.map_mono (Subgroup.comap_mono hAJ)
  have hEeq : E = orbitStab E :=
    Subgroup.eq_of_le_of_card_ge Offender.le_orbitStab hcard.le
  have hlt : 1 < (orbit E z : Set (Fin d)).ncard := by
    rw [← Nat.card_coe_set_eq, h2 z]; norm_num
  obtain ⟨a, ha, b, hb, hab⟩ := (Set.one_lt_ncard (Set.toFinite _)).1 hlt
  obtain ⟨y, hy, hyz⟩ : ∃ y ∈ (orbit E z : Set (Fin d)), y ≠ z := by
    by_cases haz : a = z
    · exact ⟨b, hb, fun h => hab (haz.trans h.symm)⟩
    · exact ⟨a, ha, haz⟩
  obtain ⟨⟨e, he⟩, rfl⟩ := hy
  have hsw : swap z (e z) ∈ E := by
    rw [hEeq]; exact Classif.swap_mem_orbitStab he z
  exact hzy (e z) (Ne.symm hyz) (hEW hsw)

theorem eOffenderData_of_not_full {S L : Subgroup G} (hA : Asc81bHyp (L ⊔ S) S) {d : ℕ}
    (hd : d = 7 ∨ 9 ≤ d) (π : ↥⁅blockV S L, L⁆ →* Multiplicative (altHeart d))
    (θ : ↥(L ⊔ S) →* Perm (Fin d)) (hπ : Function.Surjective π)
    (hequiv : SectionEquiv ⁅blockV S L, L⁆ (L ⊔ S) π θ)
    (hθV : ∀ m : ↥(L ⊔ S), θ m = 1 → (m : G) ∈ Subgroup.centralizer (blockV S L : Set G))
    (hnf : ∀ A : Subgroup G, IsMaxElemAbelian S A →
      ¬ ((¬ ∃ p, ∀ g ∈ (A.subgroupOf (L ⊔ S)).map θ, g p = p) ∧
        (∀ i : Fin d, Nat.card (orbit ((A.subgroupOf (L ⊔ S)).map θ) i) = 2) ∧
        Nat.card (orbitStab ((A.subgroupOf (L ⊔ S)).map θ)) =
          Nat.card ((A.subgroupOf (L ⊔ S)).map θ))) :
    EOffenderData S (blockV S L) := by
  have hMV : L ⊔ S ≤ Subgroup.normalizer (blockV S L : Set G) :=
    CFSG.HardMathSupport.Cooperstein.Coordinator.sup_le_normalizer_blockV S L
  have hUV : ⁅blockV S L, L⁆ ≤ blockV S L := by
    rw [Subgroup.commutator_le]
    intro v hv l hl
    rw [commutatorElement_def]
    have := (Subgroup.mem_normalizer_iff.1 (hMV ((le_sup_left : L ≤ L ⊔ S) hl)) v⁻¹).1
      ((blockV S L).inv_mem hv)
    simpa [mul_assoc] using (blockV S L).mul_mem hv this
  refine ⟨CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.isElemAbelian_blockV S L,
    (CFSG.QuasithinUnique.Setup.omegaOneCenterOf_le _).trans hA.twoCore_le,
    fun x hx => hMV ((le_sup_right : S ≤ L ⊔ S) hx), fun A hAmax => ?_⟩
  have hAM : A ≤ L ⊔ S := hAmax.1.trans le_sup_right
  have h1 := altFix_index_le hπ hequiv (A := A)
  have hoff := hoff_of_not_full hA hd π θ hπ hequiv hθV hnf A hAmax
  have h4 := relIndex_le_card_image (blockV S L) hAM θ hθV
  have hVne : (Subgroup.centralizer (A : Set G)).relIndex (blockV S L) ≠ 0 := by
    unfold Subgroup.relIndex
    exact Subgroup.index_ne_zero_of_finite
  have h5 := Subgroup.relIndex_le_of_le_right (H := Subgroup.centralizer (A : Set G)) hUV hVne
  rw [Subgroup.inf_relIndex_left, Subgroup.inf_relIndex_left]
  exact h4.trans (hoff.trans (h1.trans h5))

theorem false_of_moved_isoPair {X S L : Subgroup G} (hX : CFSG.Open.IsKGroup ↥X)
    (hA : Asc81bHyp X S) (hL : IsWeakSBlock X S L) {m : ℕ} (hm : 8 < m)
    (e : ↥(barM (L ⊔ S) L) ⧸ Subgroup.center ↥(barM (L ⊔ S) L) ≃* alternatingGroup (Fin m))
    {θ : ↥(L ⊔ S) →* Perm (Fin m)} (hNS : NaturalSectionTheta S L m θ)
    (hθS : ∀ m' : ↥(L ⊔ S), θ m' = 1 → (m' : G) ∈ S)
    (hunm : ∃ z : Fin m, ∀ y, z ≠ y →
      swap z y ∉ (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm (Fin m))))
    {p q : Fin m} (hiso : IsIsoPair (((thompsonJ S).subgroupOf (L ⊔ S)).map θ) p q)
    (s : ↥(L ⊔ S)) (hsS : (s : G) ∈ S) (hs1 : θ s p ≠ p) (hs2 : θ s p ≠ q)
    (hcount : Nat.card {x : Fin m // ∃ y, x < y ∧
        IsIsoPair (((thompsonJ S).subgroupOf (L ⊔ S)).map θ) x y} = 3 ∨
      5 ≤ Nat.card {x : Fin m // ∃ y, x < y ∧
        IsIsoPair (((thompsonJ S).subgroupOf (L ⊔ S)).map θ) x y}) : False := by
  obtain ⟨hSL, hA', hLs, hpS, hkerP, hsh⟩ := theta_node_data hX hA hL hm e hNS
  obtain ⟨π, hπ, hkerπ, hAd, hequiv, hθV⟩ := hNS
  have hnf := hnf_of_unmatched (S := S) (L := L) θ hunm
  have hd : m = 7 ∨ 9 ≤ m := Or.inr (by omega)
  have hD := eOffenderData_of_not_full hA' hd π θ hπ hequiv hθV hnf
  have hJ : ∀ m' : ↥(L ⊔ S), (m' : G) ∈ thompsonJ S →
      (θ m' p = p ∧ θ m' q = q) ∨ (θ m' p = q ∧ θ m' q = p) := by
    intro m' hm'
    have hw : θ m' ∈ ((thompsonJ S).subgroupOf (L ⊔ S)).map θ :=
      ⟨m', Subgroup.mem_subgroupOf.2 hm', rfl⟩
    have h1 := hiso.2.2 _ hw
    have h2 := hiso.symm'.2.2 _ hw
    have hpq := hiso.1
    have hinj := (θ m').injective
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exact Or.inl ⟨h1, h2⟩
    · exact absurd (hinj (h1.trans h2.symm)) hpq
    · exact absurd (hinj (h1.trans h2.symm)) hpq
    · exact Or.inr ⟨h1, h2⟩
  have hne' := commutator_ne_bot_of_moved_pair_of_not_full hA' hSL hd π θ hπ hequiv hθV hnf
    hiso.1 hJ s hsS hs1 hs2
  exact false_of_isoPairs hA' hSL hLs.perfect (by omega) π θ hπ hkerπ hAd hequiv hθV hθS hD hcount
    hne'

namespace Classif.Pre


variable {d : ℕ} {W : Subgroup (Perm (Fin d))} {ι : Type*} {E : ι → Subgroup (Perm (Fin d))}
  (P : Pre W E)

theorem exists_isIsoPair_iff (hex : ∃ z, partner P.twoGroup z = z) (x : Fin d) :
    (∃ y, IsIsoPair W x y) ↔ partner P.twoGroup x ≠ x := by
  constructor
  · rintro ⟨y, hy⟩
    rw [partner_eq_of_swap_mem P.twoGroup hy.1 hy.2.1]
    exact Ne.symm hy.1
  · intro hx
    refine ⟨partner P.twoGroup x, Ne.symm hx, swap_partner_mem P.twoGroup hx, fun w hw => ?_⟩
    exact P.blockTrivial_of_unmatched hex w hw x hx

theorem two_mul_isoCount_eq (hex : ∃ z, partner P.twoGroup z = z) :
    2 * Nat.card {x : Fin d // ∃ y, x < y ∧ IsIsoPair W x y} =
      Nat.card {x : Fin d // partner P.twoGroup x ≠ x} := by
  rw [two_mul_isoCount]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x => P.exists_isIsoPair_iff hex x)

end Classif.Pre

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
