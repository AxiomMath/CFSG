module

public import CFSG.Quasithin.Background.BlueprintB2Thompson
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.Quasithin.Background.BlueprintB2Defs

public section

namespace CFSG.QuasithinUnique.Setup.Campbell

open Subgroup CFSG CFSG.Quasithin CFSG.Quasithin.BlueprintB2

section Ambient

variable {S : Type*} [Group S]

@[expose] def elemFamilyIn (p : ℕ) (Q : Subgroup S) : Set (Subgroup S) :=
  Subgroup.map Q.subtype '' elemThompsonFamily Q p

@[expose] def elemThompsonIn (p : ℕ) (Q : Subgroup S) : Subgroup S :=
  (elemThompson Q p).map Q.subtype

@[expose] def elemCenterIn (p : ℕ) (Q : Subgroup S) : Subgroup S :=
  (elemThompsonCenterTorsion Q p).map Q.subtype

variable {p : ℕ} {Q A : Subgroup S}

theorem map_subtype_le (B : Subgroup Q) : B.map Q.subtype ≤ Q := by
  rintro _ ⟨a, -, rfl⟩
  exact a.2

theorem mem_elemFamilyIn [Finite S] [Fact p.Prime] :
    A ∈ elemFamilyIn p Q ↔ A ≤ Q ∧ IsElementaryAbelian p A ∧ Nat.card A = p ^ pRank p Q := by
  constructor
  · rintro ⟨A', ⟨hA', hc⟩, rfl⟩
    refine ⟨map_subtype_le A', isElementaryAbelian_map hA' _, ?_⟩
    rw [Subgroup.card_map_of_injective Q.subtype_injective, hc]
  · rintro ⟨hAQ, hA, hc⟩
    refine ⟨A.subgroupOf Q, ⟨isElementaryAbelian_subgroupOf hA, ?_⟩,
      Subgroup.map_subgroupOf_eq_of_le hAQ⟩
    rw [card_subgroupOf_eq hAQ, hc]

theorem le_of_mem_elemFamilyIn [Finite S] [Fact p.Prime] (hA : A ∈ elemFamilyIn p Q) : A ≤ Q :=
  (mem_elemFamilyIn.mp hA).1

theorem isElementaryAbelian_of_mem_elemFamilyIn [Finite S] [Fact p.Prime] (hA : A ∈ elemFamilyIn p Q) :
    IsElementaryAbelian p A :=
  (mem_elemFamilyIn.mp hA).2.1

theorem elemThompsonIn_eq : elemThompsonIn p Q = sSup (elemFamilyIn p Q) := by
  unfold elemThompsonIn elemFamilyIn elemThompson
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun A' hA' => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_sSup ⟨A', hA', rfl⟩
  · refine sSup_le ?_
    rintro _ ⟨A', hA', rfl⟩
    exact Subgroup.map_mono (le_sSup hA')

theorem le_elemThompsonIn (hA : A ∈ elemFamilyIn p Q) : A ≤ elemThompsonIn p Q := by
  rw [elemThompsonIn_eq]; exact le_sSup hA

theorem mem_elemCenterIn_iff [Finite S] [Fact p.Prime] {x : S} :
    x ∈ elemCenterIn p Q ↔ x ∈ Q ∧ ∀ A ∈ elemFamilyIn p Q, x ∈ A := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, fun A hA => ?_⟩
    obtain ⟨A', hA', rfl⟩ := hA
    exact ⟨y, mem_elemThompsonCenterTorsion_iff_forall.mp hy A' hA', rfl⟩
  · rintro ⟨hxQ, hx⟩
    refine ⟨⟨x, hxQ⟩, mem_elemThompsonCenterTorsion_iff_forall.mpr fun A' hA' => ?_, rfl⟩
    have := hx (A'.map Q.subtype) ⟨A', hA', rfl⟩
    obtain ⟨y, hy, hyx⟩ := this
    have : y = ⟨x, hxQ⟩ := Subtype.ext hyx
    rwa [this] at hy

theorem elemCenterIn_le [Finite S] [Fact p.Prime] (hA : A ∈ elemFamilyIn p Q) : elemCenterIn p Q ≤ A :=
  fun _ hx => (mem_elemCenterIn_iff.mp hx).2 A hA

theorem elemCenterIn_le_self [Finite S] [Fact p.Prime] : elemCenterIn p Q ≤ Q :=
  fun _ hx => (mem_elemCenterIn_iff.mp hx).1

theorem card_le_pow_pRank_of_le [Finite S] [Fact p.Prime] (hAQ : A ≤ Q) (hA : IsElementaryAbelian p A) :
    Nat.card A ≤ p ^ pRank p Q := by
  have h := card_le_pow_pRank (R := Q) (isElementaryAbelian_subgroupOf (Y := Q) hA)
  rwa [card_subgroupOf_eq hAQ] at h

theorem pRank_mono [Finite S] [Fact p.Prime] {D : Subgroup S} (hDQ : D ≤ Q) : pRank p D ≤ pRank p Q := by
  obtain ⟨A, hA, hc⟩ := exists_card_eq_pow_pRank D p
  have h := card_le_pow_pRank_of_le (p := p) ((map_subtype_le A).trans hDQ)
    (isElementaryAbelian_map hA _)
  rw [Subgroup.card_map_of_injective D.subtype_injective, hc] at h
  exact (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp h

theorem pRank_subgroup_le [Finite S] [Fact p.Prime] (Q : Subgroup S) : pRank p Q ≤ pRank p S := by
  obtain ⟨A, hA, hc⟩ := exists_card_eq_pow_pRank Q p
  have h := card_le_pow_pRank (R := S) (isElementaryAbelian_map hA Q.subtype)
  rw [Subgroup.card_map_of_injective Q.subtype_injective, hc] at h
  exact (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp h

theorem pRank_le_of_card_le [Finite S] [Fact p.Prime] {B : Subgroup S} (hBQ : B ≤ Q) (hB : IsElementaryAbelian p B)
    {r : ℕ} (hr : Nat.card B = p ^ r) : r ≤ pRank p Q := by
  have h := card_le_pow_pRank_of_le hBQ hB
  rw [hr] at h
  exact (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp h

end Ambient

section Calc

variable {G : Type*} [Group G]

open scoped commutatorElement in
@[expose] def commMod (E' V : Subgroup G) [V.Normal] : Subgroup G where
  carrier := {x | ∀ e ∈ E', ⁅e, x⁆ ∈ V}
  one_mem' := fun e _ => by simp [commutatorElement_def]
  mul_mem' := by
    intro x y hx hy e he
    have h1 : ⁅e, x * y⁆ = ⁅e, x⁆ * (x * ⁅e, y⁆ * x⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [h1]
    exact mul_mem (hx e he) ((inferInstance : V.Normal).conj_mem _ (hy e he) x)
  inv_mem' := by
    intro x hx e he
    have h1 : ⁅e, x⁻¹⁆ = x⁻¹ * ⁅e, x⁆⁻¹ * x⁻¹⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [h1]
    exact (inferInstance : V.Normal).conj_mem _ (inv_mem (hx e he)) x⁻¹

open scoped commutatorElement in
theorem mem_commMod {E' V : Subgroup G} [V.Normal] {x : G} :
    x ∈ commMod E' V ↔ ∀ e ∈ E', ⁅e, x⁆ ∈ V := Iff.rfl

theorem commutator_le_iff_le_commMod {E' X V : Subgroup G} [V.Normal] :
    ⁅E', X⁆ ≤ V ↔ X ≤ commMod E' V := by
  rw [Subgroup.commutator_le]
  exact ⟨fun h x hx e he => h e he x hx, fun h e he x hx => h hx e he⟩

end Calc

section EqualRank

variable {R : Type*} [Group R] {p : ℕ}

theorem isElementaryAbelian_sup_of_le_centralizer {E C : Subgroup R} (hE : IsElementaryAbelian p E)
    (hC : IsElementaryAbelian p C) (h : C ≤ Subgroup.centralizer (E : Set R)) :
    IsElementaryAbelian p (E ⊔ C : Subgroup R) := by
  have := hE
  have := hC
  exact IsElementaryAbelian.sup_of_le_centralizer h

theorem equal_rank_elementary_centralizer_replacement [Finite R] [Fact p.Prime]
    (_hR : IsPGroup p R) (V : Subgroup R) [V.Normal] (hV : IsElementaryAbelian p V)
    (Q : Subgroup R) (hQ : Q = Subgroup.centralizer (V : Set R))
    (hineq : ∀ A ∈ elemThompsonFamily R p,
      (A ⊓ Subgroup.centralizer (V : Set R)).relIndex A ≤
        (V ⊓ Subgroup.centralizer (A : Set R)).relIndex V) :
    (∀ A ∈ elemThompsonFamily R p,
      (V ⊓ Subgroup.centralizer (A : Set R)).relIndex V =
          (A ⊓ Subgroup.centralizer (V : Set R)).relIndex A ∧
        IsElementaryAbelian p ((A ⊓ Subgroup.centralizer (V : Set R)) ⊔ V : Subgroup R) ∧
        Nat.card ((A ⊓ Subgroup.centralizer (V : Set R)) ⊔ V : Subgroup R) = p ^ pRank p R ∧
        (A ⊓ Subgroup.centralizer (V : Set R)) ⊔ V ≤ Q) ∧
      pRank p Q = pRank p R ∧ elemThompsonIn p Q ≤ elemThompson R p ∧
      elemThompsonCenterTorsion R p ≤ elemCenterIn p Q ∧ V ≤ elemCenterIn p Q ∧
      (∀ A ∈ elemThompsonFamily R p,
        elemCenterIn p Q ≤ (A ⊓ Subgroup.centralizer (V : Set R)) ⊔ V ∧
          ⁅elemCenterIn p Q, A⁆ ≤ V) ∧
      ⁅elemCenterIn p Q, elemThompson R p⁆ ≤ V := by
  open scoped commutatorElement Pointwise in
  classical
  have hVQ : V ≤ Subgroup.centralizer (V : Set R) := fun v hv =>
    Subgroup.mem_centralizer_iff.mpr fun w hw => (isElementaryAbelian_iff.mp hV).1 w hw v hv
  have key : ∀ A ∈ elemThompsonFamily R p,
      (V ⊓ Subgroup.centralizer (A : Set R)).relIndex V =
          (A ⊓ Subgroup.centralizer (V : Set R)).relIndex A ∧
        IsElementaryAbelian p ((A ⊓ Subgroup.centralizer (V : Set R)) ⊔ V : Subgroup R) ∧
        Nat.card ((A ⊓ Subgroup.centralizer (V : Set R)) ⊔ V : Subgroup R) = p ^ pRank p R := by
    intro A hA
    obtain ⟨hAel, hmax⟩ := mem_elemThompsonFamily_iff.mp hA
    have hcard : Nat.card A = p ^ pRank p R := hA.2
    have hCA : A ⊓ Subgroup.centralizer (V : Set R) ≤ A := inf_le_left
    have hCel : IsElementaryAbelian p (A ⊓ Subgroup.centralizer (V : Set R) : Subgroup R) :=
      isElementaryAbelian_of_le hCA hAel
    have hCV : A ⊓ Subgroup.centralizer (V : Set R) ≤ Subgroup.centralizer (V : Set R) := inf_le_right
    have hle := relIndex_inf_centralizer_le hV hAel hmax
    have heq : (V ⊓ Subgroup.centralizer (A : Set R)).relIndex V =
        (A ⊓ Subgroup.centralizer (V : Set R)).relIndex A := le_antisymm hle (hineq A hA)
    refine ⟨heq, ?_, ?_⟩
    · have := isElementaryAbelian_sup_of_le_centralizer hV hCel hCV
      rwa [sup_comm] at this
    · have hVA : V ⊓ Subgroup.centralizer (A : Set R) = A ⊓ V :=
        inf_centralizer_eq_inf_of_max hV hAel hmax
      have h1 := Subgroup.relIndex_mul_card (V ⊓ Subgroup.centralizer (A : Set R)) V
      have h1' : Nat.card ((V ⊓ Subgroup.centralizer (A : Set R)) ⊓ V : Subgroup R) =
          Nat.card (A ⊓ V : Subgroup R) := by
        rw [inf_of_le_left inf_le_left, hVA]
      rw [h1', heq] at h1
      have h2 := Subgroup.relIndex_mul_card (A ⊓ Subgroup.centralizer (V : Set R)) A
      rw [inf_of_le_left hCA] at h2
      have hprod := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
        (A ⊓ Subgroup.centralizer (V : Set R)) V (fun x hx y hy =>
          (Subgroup.mem_centralizer_iff.mp hx.2 y hy).symm)).1
      have h5 : (A ⊓ Subgroup.centralizer (V : Set R)) ⊓ V = A ⊓ V := by
        ext x
        constructor
        · rintro ⟨⟨hxA, -⟩, hxV⟩
          exact ⟨hxA, hxV⟩
        · rintro ⟨hxA, hxV⟩
          exact ⟨⟨hxA, hVQ hxV⟩, hxV⟩
      rw [h5] at hprod
      have hw : 0 < Nat.card (A ⊓ V : Subgroup R) := Nat.card_pos
      have : Nat.card ((A ⊓ Subgroup.centralizer (V : Set R)) ⊔ V : Subgroup R) *
          Nat.card (A ⊓ V : Subgroup R) = Nat.card A * Nat.card (A ⊓ V : Subgroup R) := by
        rw [hprod, ← h1, ← h2]; ring
      rw [Nat.eq_of_mul_eq_mul_right hw this, hcard]
  subst hQ
  obtain ⟨A₀, hA₀⟩ := elemThompsonFamily_nonempty R p
  obtain ⟨hk₀, hBel₀, hBcard₀⟩ := key A₀ hA₀
  have hB₀Q : (A₀ ⊓ Subgroup.centralizer (V : Set R)) ⊔ V ≤ Subgroup.centralizer (V : Set R) :=
    sup_le inf_le_right hVQ
  have hQrk : pRank p (Subgroup.centralizer (V : Set R)) = pRank p R :=
    le_antisymm (pRank_subgroup_le _) (pRank_le_of_card_le hB₀Q hBel₀ hBcard₀)
  have hfam : ∀ A' ∈ elemFamilyIn p (Subgroup.centralizer (V : Set R)),
      A' ∈ elemThompsonFamily R p := by
    intro A' hA'
    obtain ⟨-, hA'e, hA'c⟩ := mem_elemFamilyIn.mp hA'
    exact ⟨hA'e, by rw [hA'c, hQrk]⟩
  have hperA : ∀ A ∈ elemThompsonFamily R p,
      (A ⊓ Subgroup.centralizer (V : Set R)) ⊔ V ∈
        elemFamilyIn p (Subgroup.centralizer (V : Set R)) := by
    intro A hA
    obtain ⟨-, hBe, hBc⟩ := key A hA
    exact mem_elemFamilyIn.mpr ⟨sup_le inf_le_right hVQ, hBe, by rw [hBc, hQrk]⟩
  have hcommA : ∀ A ∈ elemThompsonFamily R p,
      ⁅elemCenterIn p (Subgroup.centralizer (V : Set R)), A⁆ ≤ V := by
    intro A hA
    obtain ⟨-, hBe, hBc⟩ := key A hA
    have hBin := hperA A hA
    have hEB : elemCenterIn p (Subgroup.centralizer (V : Set R)) ≤
        (A ⊓ Subgroup.centralizer (V : Set R)) ⊔ V := elemCenterIn_le hBin
    have hAel := (mem_elemThompsonFamily_iff.mp hA).1
    rw [Subgroup.commutator_le]
    intro e he a ha
    have hset := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
      (A ⊓ Subgroup.centralizer (V : Set R)) V (fun x hx y hy =>
          (Subgroup.mem_centralizer_iff.mp hx.2 y hy).symm)).2
    have he' := hEB he
    have : e ∈ ((A ⊓ Subgroup.centralizer (V : Set R) : Subgroup R) : Set R) * (V : Set R) := by
      rw [← hset]; exact he'
    obtain ⟨c, hc, v, hv, rfl⟩ := this
    have hca : c * a = a * c := ((isElementaryAbelian_iff.mp hAel).1 a ha c hc.1).symm
    have hw : ⁅v, a⁆ ∈ V := by
      have := (inferInstance : V.Normal).conj_mem v⁻¹ (inv_mem hv) a
      have h2 := mul_mem hv this
      simpa [commutatorElement_def, mul_assoc] using h2
    have hcw : c * ⁅v, a⁆ = ⁅v, a⁆ * c := (Subgroup.mem_centralizer_iff.mp hc.2 _ hw).symm
    have hcomm : ⁅c * v, a⁆ = ⁅v, a⁆ := by
      have e1 : ⁅c * v, a⁆ = c * ⁅v, a⁆ * (a * c⁻¹ * a⁻¹) := by
        simp only [commutatorElement_def]; group
      have e2 : a * c⁻¹ * a⁻¹ = c⁻¹ := by
        have h3 : a * c⁻¹ = c⁻¹ * a := by
          have := congrArg (fun z => c⁻¹ * z * c⁻¹) hca
          simpa [mul_assoc] using this
        rw [h3]; group
      rw [e1, e2, hcw]; group
    rw [hcomm]; exact hw
  refine ⟨fun A hA => ?_, hQrk, ?_, ?_, ?_, fun A hA => ?_, ?_⟩
  · obtain ⟨h1, h2, h3⟩ := key A hA
    exact ⟨h1, h2, h3, sup_le inf_le_right hVQ⟩
  · rw [elemThompsonIn_eq]
    exact sSup_le fun A hA => le_sSup (hfam A hA)
  · intro x hx
    have hxall := mem_elemThompsonCenterTorsion_iff_forall.mp hx
    refine mem_elemCenterIn_iff.mpr ⟨?_, fun A' hA' => hxall A' (hfam A' hA')⟩
    exact hB₀Q (hxall _ ⟨hBel₀, hBcard₀⟩)
  · intro v hv
    refine mem_elemCenterIn_iff.mpr ⟨hVQ hv, fun A' hA' => ?_⟩
    have hA'R := hfam A' hA'
    obtain ⟨hA'Q, hA'e, -⟩ := mem_elemFamilyIn.mp hA'
    refine mem_of_mem_centralizer_of_pow_eq_one hA'e (mem_elemThompsonFamily_iff.mp hA'R).2
      ?_ ((isElementaryAbelian_iff.mp hV).2 v hv)
    exact Subgroup.mem_centralizer_iff.mpr fun a ha =>
      (Subgroup.mem_centralizer_iff.mp (hA'Q ha) v hv).symm
  · exact ⟨elemCenterIn_le (hperA A hA), hcommA A hA⟩
  · rw [commutator_le_iff_le_commMod]
    exact sSup_le fun A hA => commutator_le_iff_le_commMod.mp (hcommA A hA)

end EqualRank

section CommonFamily

variable {S : Type*} [Group S] [Finite S] {p : ℕ} [Fact p.Prime]

theorem common_Thompson_family_centralizer_identification (_hS : IsPGroup p S)
    (Q₁ Q₂ : Subgroup S) (hr : pRank p Q₁ = pRank p Q₂)
    (hC : Subgroup.centralizer (elemCenterIn p Q₂ : Set S) ≤ Q₂)
    (hne : (elemFamilyIn p Q₁ ∩ elemFamilyIn p Q₂).Nonempty) (D : Subgroup S)
    (hD : D = Q₁ ⊓ Subgroup.centralizer ((elemCenterIn p Q₁ ⊔ elemCenterIn p Q₂ : Subgroup S) :
      Set S)) :
    pRank p D = pRank p Q₁ ∧ elemFamilyIn p D = elemFamilyIn p Q₁ ∩ elemFamilyIn p Q₂ ∧
      elemThompsonIn p D = sSup (elemFamilyIn p Q₁ ∩ elemFamilyIn p Q₂) := by
  have hle : ∀ A ∈ elemFamilyIn p Q₁ ∩ elemFamilyIn p Q₂, A ≤ D := by
    rintro A ⟨hA1, hA2⟩
    rw [hD]
    refine le_inf (le_of_mem_elemFamilyIn hA1) fun a ha => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxA : x ∈ A := (sup_le (elemCenterIn_le hA1) (elemCenterIn_le hA2)) hx
    exact ((isElementaryAbelian_iff.mp (isElementaryAbelian_of_mem_elemFamilyIn hA1)).1 x hxA a ha)
  obtain ⟨A₀, hA₀⟩ := hne
  have hDQ₁ : D ≤ Q₁ := by rw [hD]; exact inf_le_left
  have hDF₂ : D ≤ Subgroup.centralizer (elemCenterIn p Q₂ : Set S) := by
    rw [hD]
    refine inf_le_right.trans (Subgroup.centralizer_le ?_)
    exact fun x hx => (le_sup_right : elemCenterIn p Q₂ ≤ elemCenterIn p Q₁ ⊔ elemCenterIn p Q₂) hx
  have hDQ₂ : D ≤ Q₂ := hDF₂.trans hC
  have hrank : pRank p D = pRank p Q₁ := by
    refine le_antisymm (pRank_mono hDQ₁) ?_
    obtain ⟨-, hA0e, hA0c⟩ := mem_elemFamilyIn.mp hA₀.1
    exact pRank_le_of_card_le (hle A₀ hA₀) hA0e hA0c
  have hfam : elemFamilyIn p D = elemFamilyIn p Q₁ ∩ elemFamilyIn p Q₂ := by
    ext A
    constructor
    · intro hA
      obtain ⟨hAD, hAe, hAc⟩ := mem_elemFamilyIn.mp hA
      exact ⟨mem_elemFamilyIn.mpr ⟨hAD.trans hDQ₁, hAe, by rw [hAc, hrank]⟩,
        mem_elemFamilyIn.mpr ⟨hAD.trans hDQ₂, hAe, by rw [hAc, hrank, hr]⟩⟩
    · intro hA
      obtain ⟨-, hAe, hAc⟩ := mem_elemFamilyIn.mp hA.1
      exact mem_elemFamilyIn.mpr ⟨hle A hA, hAe, by rw [hAc, hrank]⟩
  exact ⟨hrank, hfam, by rw [elemThompsonIn_eq, hfam]⟩

end CommonFamily

end CFSG.QuasithinUnique.Setup.Campbell
