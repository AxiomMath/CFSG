module

public import CFSG.GH74.Uniqueness.Bender.AutFixed
public import CFSG.Blueprint.Catalog
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents

public section

namespace CFSG.GH74.Generic.S45.LQ

theorem isPerfect_of_simple_nonab {F : Type} [Group F] (hs : IsSimpleGroup F)
    (hnab : ∃ a b : F, a * b ≠ b * a) : Group.IsPerfect F := by
  refine ⟨?_⟩
  rcases hs.eq_bot_or_eq_top_of_normal (commutator F) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (((commutator_eq_bot_iff F).1 h).is_comm.comm a b)
  · exact h

theorem stated_of_lieModel_PSL {S : Type} [Group S] {n p f : ℕ}
    (h : CFSG.Blueprint.LieModel S .PSL n p f) :
    CFSG.Assembly.LowTwoRank.StatedClassicalModel S .PSL n p f :=
  CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)

end CFSG.GH74.Generic.S45.LQ

namespace CFSG.GH74.Generic.S45.LAlt

open CFSG CFSG.Blueprint Subgroup
open CFSG.GH74.Uniqueness.Bender

theorem isSubnormal_map_of_normal_range {G G' : Type*} [Group G] [Group G'] (f : G →* G')
    (hfn : f.range.Normal) {H : Subgroup G} (hH : H.IsSubnormal) : (H.map f).IsSubnormal := by
  have h1 : H.map f ≤ f.range := Subgroup.map_le_range f H
  have h2 : ((H.map f).subgroupOf f.range).IsSubnormal := by
    have : (H.map f).subgroupOf f.range = H.map f.rangeRestrict := by
      ext ⟨x, hx⟩
      obtain ⟨g, rfl⟩ := hx
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map]
      constructor
      · rintro ⟨h, hh, hf⟩
        exact ⟨h, hh, Subtype.ext hf⟩
      · rintro ⟨h, hh, hf⟩
        exact ⟨h, hh, congrArg Subtype.val hf⟩
    rw [this]
    exact hH.map f.rangeRestrict_surjective
  exact Subgroup.IsSubnormal.trans h1 h2 hfn.isSubnormal

end CFSG.GH74.Generic.S45.LAlt

namespace CFSG.GH74.Generic.S45

open CFSG CFSG.Blueprint Subgroup
open CFSG.GH74.Uniqueness.Bender CFSG.GH74.Generic.S45.LAlt

structure QData (S : Type) [Group S] (ya : MulAut S) (Lb : Subgroup S) (q : ℕ) : Prop where
  sq : ya * ya = 1
  ne : ya ≠ 1
  le : Lb ≤ autFixed ya
  sub : (Lb.subgroupOf (autFixed ya)).IsSubnormal
  simple : IsSimpleGroup ↥Lb
  nonab : ∃ a b : ↥Lb, a * b ≠ b * a
  no4 : ∀ x ∈ Lb, ¬ 4 ∣ orderOf x
  q5 : 5 ≤ q
  odd : Odd q
  mod8 : q % 8 = 3 ∨ q % 8 = 5
  card : Nat.card ↥Lb * 2 = q * (q ^ 2 - 1)
  model : ∀ P : ℕ → Prop, P q → ∃ p f : ℕ, p.Prime ∧ 1 ≤ f ∧ P (p ^ f) ∧ LieModel ↥Lb .PSL 2 p f

theorem center_eq_bot_of_simple_nonab {F : Type} [Group F] (hs : IsSimpleGroup F)
    (hnab : ∃ a b : F, a * b ≠ b * a) : Subgroup.center F = ⊥ := by
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center F) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    exact hab ((Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b)) a)

theorem isQuasisimple_of_simple_nonab {F : Type} [Group F] (hs : IsSimpleGroup F)
    (hnab : ∃ a b : F, a * b ≠ b * a) : CFSG.IsQuasisimple F := by
  have hperf : Group.IsPerfect F := LQ.isPerfect_of_simple_nonab hs hnab
  have hcenter : Subgroup.center F = ⊥ := by
    rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center F) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      exact hab ((Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b)) a)
  let e : F ⧸ Subgroup.center F ≃* F :=
    (QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot
  refine ⟨hperf, MulEquiv.isSimpleGroup e, ?_⟩
  obtain ⟨a, b, hab⟩ := hnab
  refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
  have := congrArg e h
  rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at this

theorem QData.isComponent {S : Type} [Group S] {ya : MulAut S} {Lb : Subgroup S} {q : ℕ}
    (hQ : QData S ya Lb q) : CFSG.IsComponent (Lb.subgroupOf (autFixed ya)) := by
  refine ⟨?_, hQ.sub⟩
  have hq : CFSG.IsQuasisimple ↥Lb := isQuasisimple_of_simple_nonab hQ.simple hQ.nonab
  exact (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr
    (Subgroup.subgroupOfEquivOfLe hQ.le)).2 hq

theorem exists_component_conj {S : Type} [Group S] (hZ : Subgroup.center S = ⊥) (ya : MulAut S)
    {Lb : Subgroup S} (hLb : Lb ≤ autFixed ya) (hsub : (Lb.subgroupOf (autFixed ya)).IsSubnormal)
    (hLs : IsSimpleGroup ↥Lb) (hLnab : ∃ a b : ↥Lb, a * b ≠ b * a) :
    ∃ L' : Subgroup (MulAut S),
      CFSG.Assembly.IsComponentOf L'
        (CFSG.ComponentClassification.OuterAutomorphisms.inner S ⊓
          Subgroup.centralizer ({ya} : Set (MulAut S))) ∧ Nonempty (↥Lb ≃* ↥L') := by
  classical
  let ι : S →* MulAut S := MulAut.conj
  have hι : Function.Injective ι := by
    intro g g' h
    have hc : g'⁻¹ * g ∈ Subgroup.center S := Subgroup.mem_center_iff.2 fun x => by
      have hx := congrArg (fun φ : MulAut S => φ x) h
      simp only [ι, MulAut.conj_apply] at hx
      calc x * (g'⁻¹ * g) = g'⁻¹ * (g' * x * g'⁻¹) * g := by group
        _ = g'⁻¹ * (g * x * g⁻¹) * g := by rw [hx]
        _ = g'⁻¹ * g * x := by group
    rw [hZ, Subgroup.mem_bot] at hc
    exact (inv_mul_eq_one.1 hc).symm
  let D : Subgroup (MulAut S) :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner S ⊓ Subgroup.centralizer ({ya} : Set (MulAut S))
  have hconj : ∀ s : S, ya * MulAut.conj s * ya⁻¹ = MulAut.conj (ya s) := fun s => by
    ext x
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]
  have hmemD : ∀ s : S, ι s ∈ D ↔ s ∈ autFixed ya := by
    intro s
    constructor
    · intro hD
      have h := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hD).2
      rw [mem_autFixed_iff]
      apply hι
      have h1 := hconj s
      calc MulAut.conj (ya s) = ya * MulAut.conj s * ya⁻¹ := h1.symm
        _ = (MulAut.conj s * ya) * ya⁻¹ := by rw [← h]
        _ = MulAut.conj s := by group
    · intro h
      rw [mem_autFixed_iff] at h
      refine Subgroup.mem_inf.2 ⟨⟨s, rfl⟩, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      have h1 := hconj s
      rw [h] at h1
      calc MulAut.conj s * ya = (ya * MulAut.conj s * ya⁻¹) * ya := by rw [h1]
        _ = ya * MulAut.conj s := by group
  let f : ↥(autFixed ya) →* ↥D :=
    (ι.comp (autFixed ya).subtype).codRestrict D (fun x => (hmemD x).2 x.2)
  have hfs : Function.Surjective f := by
    rintro ⟨x, hxD⟩
    obtain ⟨⟨s, rfl⟩, hxc⟩ := Subgroup.mem_inf.1 hxD
    exact ⟨⟨s, (hmemD s).1 hxD⟩, rfl⟩
  have hfn : f.range.Normal := by
    rw [MonoidHom.range_eq_top_of_surjective f hfs]
    infer_instance
  have hsubD := isSubnormal_map_of_normal_range f hfn hsub
  let L' : Subgroup (MulAut S) := Lb.map ι
  have hL'D : L' ≤ D := by
    rintro _ ⟨l, hl, rfl⟩
    exact (hmemD l).2 (hLb hl)
  have heq : ((Lb.subgroupOf (autFixed ya)).map f) = L'.subgroupOf D := by
    ext ⟨x, hx⟩
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨c, hc, hcx⟩
      exact ⟨c, hc, congrArg Subtype.val hcx⟩
    · rintro ⟨l, hl, hlx⟩
      exact ⟨⟨l, hLb hl⟩, hl, Subtype.ext hlx⟩
  let eLb : ↥Lb ≃* ↥L' :=
    MulEquiv.ofBijective (ι.subgroupMap Lb)
      ⟨fun a b hab => Subtype.ext (hι (congrArg Subtype.val hab)), ι.subgroupMap_surjective Lb⟩
  let e2 : ↥(L'.subgroupOf D) ≃* ↥Lb := (Subgroup.subgroupOfEquivOfLe hL'D).trans eLb.symm
  have hs2 : IsSimpleGroup ↥(L'.subgroupOf D) := by
    have : IsSimpleGroup ↥Lb := hLs
    exact e2.isSimpleGroup
  have hnab2 : ∃ a b : ↥(L'.subgroupOf D), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hLnab
    refine ⟨e2.symm a, e2.symm b, fun h => hab ?_⟩
    have := congrArg e2 h
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at this
  refine ⟨L', ?_, ⟨eLb⟩⟩
  rw [CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hL'D]
  exact ⟨isQuasisimple_of_simple_nonab hs2 hnab2, by rw [← heq]; exact hsubD⟩

end CFSG.GH74.Generic.S45
