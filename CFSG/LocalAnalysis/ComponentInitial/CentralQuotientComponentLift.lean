module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBCentralQuotientDerived
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents

public section

namespace CFSG.LocalAnalysis.ComponentInitial.CentralQuotientLift

open Subgroup CFSG.ComponentClassification

theorem commutator_le_of_index_le_two {H : Type*} [Group H] [Finite H] {N : Subgroup H}
    [N.Normal] (hidx : N.index ≤ 2) : _root_.commutator H ≤ N := by
  rw [← Subgroup.Normal.quotient_commutative_iff_commutator_le]
  have hpos : 0 < Nat.card (H ⧸ N) := Nat.card_pos
  rw [Subgroup.index_eq_card] at hidx
  rcases (by omega : Nat.card (H ⧸ N) = 1 ∨ Nat.card (H ⧸ N) = 2) with h1 | h2
  · have : Subsingleton (H ⧸ N) := (Nat.card_eq_one_iff_unique.mp h1).1
    exact ⟨⟨fun a b => Subsingleton.elim _ _⟩⟩
  · have : Fact (Nat.Prime (Nat.card (H ⧸ N))) := ⟨by rw [h2]; exact Nat.prime_two⟩
    have : IsCyclic (H ⧸ N) := isCyclic_of_prime_card rfl
    exact IsCyclic.isMulCommutative

theorem exists_mul_ne_of_isComponent {G : Type*} [Group G] {B : Subgroup G}
    (hB : CFSG.IsComponent B) : ∃ x y : B, x * y ≠ y * x := by
  obtain ⟨-, -, a, b, hab⟩ := hB.1
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  exact ⟨x, y, fun h => hab (by rw [← QuotientGroup.mk_mul, h, QuotientGroup.mk_mul])⟩

theorem fst_eq_or_snd_eq_of_isComponent_prod {G₁ G₂ : Type*} [Group G₁] [Group G₂] [Finite G₁]
    [Finite G₂] {L : Subgroup (G₁ × G₂)} (hL : CFSG.IsComponent L) :
    (∀ x ∈ L, x.2 = 1) ∨ ∀ x ∈ L, x.1 = 1 := by
  have hN₁ := Subgroup.prod_normal (⊤ : Subgroup G₁) (⊥ : Subgroup G₂)
  have hN₂ := Subgroup.prod_normal (⊥ : Subgroup G₁) (⊤ : Subgroup G₂)
  rcases component_normal_subgroup hL hN₁ with h1 | h1
  · exact Or.inl fun x hx => (mem_prod.mp (h1 hx)).2
  rcases component_normal_subgroup hL hN₂ with h2 | h2
  · exact Or.inr fun x hx => (mem_prod.mp (h2 hx)).1
  exfalso
  obtain ⟨p, q, hpq⟩ := exists_mul_ne_of_isComponent hL
  apply hpq
  apply Subtype.ext
  have hc₁ := commutator_eq_bot_iff_le_centralizer.mp h1 p.2
  have hc₂ := commutator_eq_bot_iff_le_centralizer.mp h2 p.2
  have hq : (q : G₁ × G₂) = ((q : G₁ × G₂).1, 1) * (1, (q : G₁ × G₂).2) := by simp
  have e₁ := mem_centralizer_iff.mp hc₁ ((q : G₁ × G₂).1, 1)
    (mem_prod.mpr ⟨mem_top _, one_mem _⟩)
  have e₂ := mem_centralizer_iff.mp hc₂ (1, (q : G₁ × G₂).2)
    (mem_prod.mpr ⟨one_mem _, mem_top _⟩)
  change (p : G₁ × G₂) * q = q * p
  rw [hq, ← mul_assoc, ← e₁, mul_assoc, ← e₂, ← mul_assoc]

theorem eq_of_isComponent_of_quasisimple {X : Type*} [Group X] [Finite X] {S L : Subgroup X}
    (hS : CFSG.IsQuasisimple S) (hSX : _root_.commutator X ≤ S) (hL : CFSG.IsComponent L) :
    L = S := by
  have hLL : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp hL.1.1
  have hLS : L ≤ S := by
    rw [← hLL]
    exact (commutator_mono le_top le_top).trans (by rw [← _root_.commutator_def]; exact hSX)
  rcases quasisimple_subnormal_subgroups hS hL.2.subgroupOf with htop | hcen
  · apply le_antisymm hLS
    intro s hs
    have h1 : (⟨s, hs⟩ : S) ∈ L.subgroupOf S := htop ▸ mem_top _
    exact Subgroup.mem_subgroupOf.mp h1
  · exfalso
    obtain ⟨p, q, hpq⟩ := exists_mul_ne_of_isComponent hL
    apply hpq
    apply Subtype.ext
    have hp : (⟨p, hLS p.2⟩ : S) ∈ center S := hcen (Subgroup.mem_subgroupOf.mpr p.2)
    have h1 := mem_center_iff.mp hp ⟨q, hLS q.2⟩
    exact (congrArg Subtype.val h1).symm

section Lift

variable {G : Type*} [Group G] (Z : Subgroup G) [Z.Normal]

@[expose] def centralizerProj (T : G) :
    centralizer {T} →* centralizer {(QuotientGroup.mk' Z) T} :=
  ((QuotientGroup.mk' Z).comp (centralizer {T}).subtype).codRestrict _ fun x => by
    rw [mem_centralizer_singleton_iff]
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
    rw [← map_mul, ← map_mul, mem_centralizer_singleton_iff.mp x.2]

theorem centralizerProj_apply (T : G) (x : centralizer {T}) :
    (centralizerProj Z T x : G ⧸ Z) = (QuotientGroup.mk' Z) (x : G) :=
  rfl

variable {Z}

theorem centralizerProj_ker_le_center (hZ : Z ≤ center G) (T : G) :
    (centralizerProj Z T).ker ≤ center (centralizer {T}) := by
  intro x hx
  have h1 : (QuotientGroup.mk' Z) (x : G) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact mem_center_iff.mpr fun y => Subtype.ext (mem_center_iff.mp (hZ h1) y)

theorem le_range_of_perfect {T : G}
    (hcomm : _root_.commutator (centralizer {(QuotientGroup.mk' Z) T}) ≤
      (centralizerProj Z T).range)
    {B : Subgroup (centralizer {(QuotientGroup.mk' Z) T})} (hB : ⁅B, B⁆ = B) :
    B ≤ (centralizerProj Z T).range := by
  rw [← hB]
  refine (commutator_mono le_top le_top).trans ?_
  rw [← _root_.commutator_def]
  exact hcomm

theorem comap_le_centralizer (hZ : Z ≤ center G) {T : G}
    {B : Subgroup (centralizer {(QuotientGroup.mk' Z) T})}
    (hB : B ≤ (centralizerProj Z T).range) :
    (B.map (centralizer {(QuotientGroup.mk' Z) T}).subtype).comap (QuotientGroup.mk' Z) ≤
      centralizer {T} := by
  intro g hg
  obtain ⟨b, hb, hbg⟩ := mem_map.mp (mem_comap.mp hg)
  obtain ⟨x, hx⟩ := hB hb
  have h1 : (QuotientGroup.mk' Z) (x : G) = (QuotientGroup.mk' Z) g := by
    rw [← hbg, ← hx]
    rfl
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h1
  have hg' : g = x * ((x : G)⁻¹ * g) := by group
  rw [hg']
  exact mul_mem x.2 (center_le_centralizer _ (hZ h1))

theorem comap_eq_map_comap (hZ : Z ≤ center G) {T : G}
    {B : Subgroup (centralizer {(QuotientGroup.mk' Z) T})}
    (hB : B ≤ (centralizerProj Z T).range) :
    (B.map (centralizer {(QuotientGroup.mk' Z) T}).subtype).comap (QuotientGroup.mk' Z) =
      (B.comap (centralizerProj Z T)).map (centralizer {T}).subtype := by
  ext g
  constructor
  · intro hg
    refine ⟨⟨g, comap_le_centralizer hZ hB hg⟩, ?_, rfl⟩
    obtain ⟨b, hb, hbg⟩ := mem_map.mp (mem_comap.mp hg)
    have : centralizerProj Z T ⟨g, comap_le_centralizer hZ hB hg⟩ = b := Subtype.ext hbg.symm
    exact mem_comap.mpr (this.symm ▸ hb)
  · rintro ⟨x, hx, rfl⟩
    exact mem_comap.mpr ⟨_, hx, rfl⟩

theorem lift_component (hZ : Z ≤ center G) {T : G}
    (hcomm : _root_.commutator (centralizer {(QuotientGroup.mk' Z) T}) ≤
      (centralizerProj Z T).range)
    {B : Subgroup (centralizer {(QuotientGroup.mk' Z) T})} (hB : CFSG.IsComponent B)
    {Q : Subgroup (G ⧸ Z)}
    (hQB : Q ≤ centralizer ((B.map (centralizer {(QuotientGroup.mk' Z) T}).subtype :
      Subgroup (G ⧸ Z)) : Set (G ⧸ Z)))
    (hQ : Q ≠ ⊥) (hQp : ⁅Q, Q⁆ = Q) :
    CFSG.IsComponent ⁅B.comap (centralizerProj Z T), B.comap (centralizerProj Z T)⁆ ∧
      ⁅B.comap (centralizerProj Z T), B.comap (centralizerProj Z T)⁆.map
        (centralizerProj Z T) = B ∧
      ⁅(B.map (centralizer {(QuotientGroup.mk' Z) T}).subtype).comap (QuotientGroup.mk' Z),
        (B.map (centralizer {(QuotientGroup.mk' Z) T}).subtype).comap (QuotientGroup.mk' Z)⁆ =
        ⁅B.comap (centralizerProj Z T), B.comap (centralizerProj Z T)⁆.map
          (centralizer {T}).subtype ∧
      ⁅⁅Q.comap (QuotientGroup.mk' Z), Q.comap (QuotientGroup.mk' Z)⁆,
        ⁅Q.comap (QuotientGroup.mk' Z), Q.comap (QuotientGroup.mk' Z)⁆⁆ =
        ⁅Q.comap (QuotientGroup.mk' Z), Q.comap (QuotientGroup.mk' Z)⁆ ∧
      ⁅Q.comap (QuotientGroup.mk' Z), Q.comap (QuotientGroup.mk' Z)⁆.map
        (QuotientGroup.mk' Z) = Q ∧
      ⁅Q.comap (QuotientGroup.mk' Z), Q.comap (QuotientGroup.mk' Z)⁆ ≠ ⊥ ∧
      ⁅Q.comap (QuotientGroup.mk' Z), Q.comap (QuotientGroup.mk' Z)⁆ ≤
        centralizer ((⁅B.comap (centralizerProj Z T), B.comap (centralizerProj Z T)⁆.map
          (centralizer {T}).subtype : Subgroup G) : Set G) := by
  have hπs : Function.Surjective (QuotientGroup.mk' Z) := QuotientGroup.mk'_surjective Z
  have hπker : (QuotientGroup.mk' Z).ker ≤ center G := by rw [QuotientGroup.ker_mk']; exact hZ
  have hBB : ⁅B, B⁆ = B := Subgroup.isPerfect_iff.mp hB.1.1
  have hBN := le_range_of_perfect hcomm hBB
  obtain ⟨M, hM⟩ : ∃ M : Subgroup (centralizerProj Z T).range,
      M = B.subgroupOf (centralizerProj Z T).range := ⟨_, rfl⟩
  have hcomap : M.comap (centralizerProj Z T).rangeRestrict = B.comap (centralizerProj Z T) := by
    ext x
    rw [hM, mem_comap, mem_comap, mem_subgroupOf, MonoidHom.coe_rangeRestrict]
  have hMq : CFSG.IsQuasisimple M := by
    rw [hM]
    exact (isQuasisimple_congr (subgroupOfEquivOfLe hBN)).2 hB.1
  have : Group.IsPerfect M := hMq.1
  have hcentral : (centralizerProj Z T).rangeRestrict.ker ≤ center (centralizer {T}) := by
    rw [MonoidHom.ker_rangeRestrict]
    exact centralizerProj_ker_le_center hZ T
  have hsurj := (centralizerProj Z T).rangeRestrict_surjective
  have hderiv : CatalogueBCentralQuotient.derivedPreimage (centralizerProj Z T).rangeRestrict M =
      ⁅B.comap (centralizerProj Z T), B.comap (centralizerProj Z T)⁆ := by
    rw [CatalogueBCentralQuotient.derivedPreimage_eq_commutator, hcomap]
  have hmap := CatalogueBCentralQuotient.derivedPreimage_map
    (centralizerProj Z T).rangeRestrict hsurj M
  have hsub := CatalogueBCentralQuotient.derivedPreimage_subnormal
    (centralizerProj Z T).rangeRestrict M (by rw [hM]; exact hB.2.subgroupOf)
  have : Group.IsPerfect (CatalogueBCentralQuotient.derivedPreimage
      (centralizerProj Z T).rangeRestrict M) :=
    CatalogueBCentralQuotient.derivedPreimage_perfect _ hsurj hcentral M
  have hq := (CatalogueBCentralQuotient.quasisimple_map_iff_of_perfect
    (centralizerProj Z T).rangeRestrict hcentral
    (CatalogueBCentralQuotient.derivedPreimage (centralizerProj Z T).rangeRestrict M)).2
    (by rw [hmap]; exact hMq)
  rw [hderiv] at hq hsub hmap
  have hLcomp : CFSG.IsComponent
      ⁅B.comap (centralizerProj Z T), B.comap (centralizerProj Z T)⁆ := ⟨hq, hsub⟩
  have hLB : ⁅B.comap (centralizerProj Z T), B.comap (centralizerProj Z T)⁆.map
      (centralizerProj Z T) = B := by
    have h2 := congrArg (Subgroup.map (centralizerProj Z T).range.subtype) hmap
    rwa [Subgroup.map_map, hM, map_subgroupOf_eq_of_le hBN,
      MonoidHom.subtype_comp_rangeRestrict] at h2
  have hPL : ⁅(B.map (centralizer {(QuotientGroup.mk' Z) T}).subtype).comap (QuotientGroup.mk' Z),
      (B.map (centralizer {(QuotientGroup.mk' Z) T}).subtype).comap (QuotientGroup.mk' Z)⁆ =
        ⁅B.comap (centralizerProj Z T), B.comap (centralizerProj Z T)⁆.map
          (centralizer {T}).subtype := by
    rw [comap_eq_map_comap hZ hBN, map_commutator]
  have : Group.IsPerfect Q := Subgroup.isPerfect_iff.mpr hQp
  have hQperf := CatalogueBCentralQuotient.derivedPreimage_perfect _ hπs hπker Q
  have hQmap := CatalogueBCentralQuotient.derivedPreimage_map _ hπs Q
  rw [CatalogueBCentralQuotient.derivedPreimage_eq_commutator] at hQperf hQmap
  have hQhat : ⁅Q.comap (QuotientGroup.mk' Z), Q.comap (QuotientGroup.mk' Z)⁆ ≠ ⊥ := fun h =>
    hQ (by rw [← hQmap, h, Subgroup.map_bot])
  have hLperf : ⁅⁅B.comap (centralizerProj Z T), B.comap (centralizerProj Z T)⁆.map
        (centralizer {T}).subtype,
      ⁅B.comap (centralizerProj Z T), B.comap (centralizerProj Z T)⁆.map
        (centralizer {T}).subtype⁆ =
        ⁅B.comap (centralizerProj Z T), B.comap (centralizerProj Z T)⁆.map
          (centralizer {T}).subtype := by
    rw [← map_commutator, Subgroup.isPerfect_iff.mp hLcomp.1.1]
  have hcent : ⁅⁅B.comap (centralizerProj Z T), B.comap (centralizerProj Z T)⁆.map
        (centralizer {T}).subtype,
      ⁅Q.comap (QuotientGroup.mk' Z), Q.comap (QuotientGroup.mk' Z)⁆⁆ ≤ center G := by
    rw [← hPL]
    refine (commutator_mono (commutator_le_self _) (commutator_le_self _)).trans ?_
    rw [commutator_le]
    intro p hp r hr
    apply hπker
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    obtain ⟨b, hb, hbp⟩ := mem_map.mp (mem_comap.mp hp)
    rw [← hbp]
    exact mem_centralizer_iff.mp (hQB (mem_comap.mp hr)) _ (mem_map_of_mem _ hb)
  have hQcent : ⁅Q.comap (QuotientGroup.mk' Z), Q.comap (QuotientGroup.mk' Z)⁆ ≤
      centralizer ((⁅B.comap (centralizerProj Z T), B.comap (centralizerProj Z T)⁆.map
        (centralizer {T}).subtype : Subgroup G) : Set G) := by
    rw [← commutator_eq_bot_iff_le_centralizer, commutator_comm]
    exact perfect_double_commutator hLperf
      (commutator_eq_bot_iff_le_centralizer.mpr (hcent.trans (center_le_centralizer _)))
  exact ⟨hLcomp, hLB, hPL, Subgroup.isPerfect_iff.mp hQperf, hQmap, hQhat, hQcent⟩

theorem exists_mulEquiv_of_inf_eq_one {T : G} {L : Subgroup (centralizer {T})}
    {B : Subgroup (centralizer {(QuotientGroup.mk' Z) T})}
    (hLB : L.map (centralizerProj Z T) = B) (hinj : ∀ x ∈ L, (x : G) ∈ Z → x = 1) :
    ∃ e : L.map (centralizer {T}).subtype ≃* B, ∀ g,
      ((e g : centralizer {(QuotientGroup.mk' Z) T}) : G ⧸ Z) = QuotientGroup.mk' Z (g : G) := by
  obtain ⟨ρ, hρ⟩ : ∃ ρ : L →* B, ∀ x : L,
      (ρ x : centralizer {(QuotientGroup.mk' Z) T}) = centralizerProj Z T x :=
    ⟨((centralizerProj Z T).comp L.subtype).codRestrict B fun x => by
      rw [← hLB]
      exact mem_map_of_mem _ x.2, fun _ => rfl⟩
  have hρinj : Function.Injective ρ := by
    refine (injective_iff_map_eq_one ρ).mpr fun x hx => ?_
    have h2 : ((ρ x : centralizer {(QuotientGroup.mk' Z) T}) : G ⧸ Z) = 1 := by
      rw [hx]
      rfl
    rw [hρ, centralizerProj_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    exact Subtype.ext (hinj x x.2 h2)
  have hρsurj : Function.Surjective ρ := by
    intro y
    have hy : (y : centralizer {(QuotientGroup.mk' Z) T}) ∈ L.map (centralizerProj Z T) := by
      rw [hLB]
      exact y.2
    obtain ⟨x, hx, hxy⟩ := hy
    exact ⟨⟨x, hx⟩, Subtype.ext (by rw [hρ]; exact hxy)⟩
  obtain ⟨e₂, he₂⟩ : ∃ e₂ : L ≃* L.map (centralizer {T}).subtype,
      e₂ = L.equivMapOfInjective _ Subtype.val_injective := ⟨_, rfl⟩
  refine ⟨e₂.symm.trans (MulEquiv.ofBijective ρ ⟨hρinj, hρsurj⟩), fun g => ?_⟩
  change ((ρ (e₂.symm g) : centralizer {(QuotientGroup.mk' Z) T}) : G ⧸ Z) = _
  rw [hρ, centralizerProj_apply]
  congr 1
  have h1 := coe_equivMapOfInjective_apply L (centralizer {T}).subtype Subtype.val_injective
    (e₂.symm g)
  rw [← he₂, MulEquiv.apply_symm_apply] at h1
  exact h1.symm

end Lift

end CFSG.LocalAnalysis.ComponentInitial.CentralQuotientLift
