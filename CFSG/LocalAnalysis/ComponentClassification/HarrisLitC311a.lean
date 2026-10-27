module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitBlowup
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitL219A

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.C311

open CFSG Subgroup

theorem nonabelian_of_quotient {L : Type*} [Group L] {N : Subgroup L} [N.Normal]
    (h : ∃ a b : L ⧸ N, a * b ≠ b * a) : ∃ a b : L, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := h
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  exact ⟨a, b, fun h => hab (by rw [← QuotientGroup.mk_mul, h, QuotientGroup.mk_mul])⟩

theorem nonabelian_of_harrisF {p : ℕ} {Y : Type} [Group Y] (h : HarrisF p Y) :
    ∃ a b : Y, a * b ≠ b * a := by
  induction h with
  | base hY =>
    obtain ⟨n, -, hm⟩ := hY
    exact nonabelian_of_lieModel_psl2 hm
  | blowup _ _ hB ih =>
    obtain ⟨-, -, α, -, L, -, ⟨e⟩⟩ := hB
    obtain ⟨a, b, hab⟩ := ih
    obtain ⟨x, y, hxy⟩ := nonabelian_of_quotient (N := Open.fusionZStar ↥L)
      ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩
    refine ⟨((x : ↥(fixedPoints α)) : _), ((y : ↥(fixedPoints α)) : _), fun h => hxy ?_⟩
    exact Subtype.ext (Subtype.ext h)

theorem catalog_of_harrisF {p : ℕ} {Y : Type} [Group Y] (h : HarrisF p Y) :
    Blueprint.Catalog Y := by
  induction h with
  | base hY =>
    obtain ⟨n, -, hm⟩ := hY
    exact Blueprint.lieModel_catalog _ _ _ _ _ hm
  | blowup _ hX _ _ => exact hX

theorem exists_not_mem_pPrimeCore {J : Type*} [Group J] (hJ : IsTwoQuasisimple J) :
    ∃ x : J, x ∉ pPrimeCore 2 J := by
  by_contra hall
  push Not at hall
  obtain ⟨-, hs, -⟩ := hJ.2
  obtain ⟨u, v, huv⟩ := hs.exists_pair_ne
  apply huv
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective u
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective v
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective u
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective v
  have hu : (QuotientGroup.mk u : J ⧸ pPrimeCore 2 J) = 1 :=
    (QuotientGroup.eq_one_iff u).mpr (hall u)
  have hv : (QuotientGroup.mk v : J ⧸ pPrimeCore 2 J) = 1 :=
    (QuotientGroup.eq_one_iff v).mpr (hall v)
  rw [hu, hv]

theorem pPrimeCore_le_center_of_isQuasisimple {J : Type*} [Group J] (hJ2 : IsTwoQuasisimple J)
    (hJ : IsQuasisimple J) : pPrimeCore 2 J ≤ center J := by
  rcases LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hJ (pPrimeCore 2 J) with h | h
  · exact h
  · obtain ⟨x, hx⟩ := exists_not_mem_pPrimeCore hJ2
    exact absurd (h ▸ mem_top x) hx

theorem oddCore_eq_pPrimeCore_two (X : Type*) [Group X] : CFSG.oddCore X = pPrimeCore 2 X := by
  unfold CFSG.oddCore CFSG.pPrimeCore
  congr 1
  ext L
  simp only [Set.mem_ofPred_eq, Nat.coprime_two_left]

theorem isQuasisimple_of_open {X : Type*} [Group X] (h : Open.IsQuasisimple X) :
    IsQuasisimple X :=
  ⟨⟨h.1⟩, h.2, Helpers.quasisimple_central_quotient_nonabelian X h⟩

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_of_isPerfect {S : Subgroup G} [S.Normal] (hC : centralizer (S : Set G) = ⊥)
    [Group.IsSolvable (OuterAutomorphisms.Outer S)] {J : Subgroup G} [Group.IsPerfect J] :
    J ≤ S := by
  intro j hj
  obtain ⟨s, hs⟩ := OuterAutomorphisms.perfect_action_inner
    ((MulAut.conjNormal (H := S)).comp J.subtype) ⟨j, hj⟩
  have hjs : (s : G)⁻¹ * j ∈ centralizer (S : Set G) := by
    rw [mem_centralizer_iff]
    intro x hx
    have h1 := congrArg (fun φ : MulAut S => ((φ ⟨x, hx⟩ : S) : G)) hs
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, MulAut.conjNormal_apply,
      MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h1
    calc x * ((s : G)⁻¹ * j) = (s : G)⁻¹ * ((s : G) * x * (s : G)⁻¹) * j := by group
      _ = (s : G)⁻¹ * (j * x * j⁻¹) * j := by rw [h1]
      _ = (s : G)⁻¹ * j * x := by group
  rw [hC, mem_bot] at hjs
  have : j = s := by
    calc j = (s : G) * ((s : G)⁻¹ * j) := by group
      _ = s := by rw [hjs, mul_one]
  rw [this]
  exact s.2

@[expose] def infEquivSubgroupOf (S C : Subgroup G) : ↥(S ⊓ C) ≃* ↥(S.subgroupOf C) where
  toFun x := ⟨⟨x, x.2.2⟩, x.2.1⟩
  invFun y := ⟨y.1.1, y.2, y.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem isQuasisimple_of_fixed {S : Subgroup G} [S.Normal] {a : G} {J : Subgroup G}
    (hJS : J ≤ S) (hJ : IsTwoComponentIn J (centralizer {a}))
    (hfix : ∀ L : Subgroup (FixedCommutingProduct.fixedSubgroup (MulAut.conjNormal (H := S) a)),
      IsPComponent 2 L → IsQuasisimple L) :
    IsQuasisimple J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJC := hJ.1
  have hP := (isTwoComponentIn_iff hJC).mp hJ
  have hJSC : J ≤ S ⊓ centralizer {a} := le_inf hJS hJC
  have hP2 : IsPComponent 2 (J.subgroupOf (S ⊓ centralizer {a})) :=
    CatalogueBPrimeJoin.pComponent_subgroupOf_of_le hJSC inf_le_right hP
  let e := (infEquivSubgroupOf S (centralizer {a})).trans (FixedNormalCentralizer.equivalence S a)
  have hq := hfix _ (isPComponent_map_mulEquiv e hP2)
  exact LocalCores.isQuasisimple_of_mulEquiv
    (((J.subgroupOf (S ⊓ centralizer {a})).equivMapOfInjective _ e.injective).symm.trans
      (subgroupOfEquivOfLe hJSC)) hq

omit [Finite G] in
theorem normalizer_zpowers_eq_centralizer {a : G} (ha : orderOf a = 2) :
    normalizer (zpowers a : Set G) = centralizer {a} := by
  apply le_antisymm
  · intro g hg
    rw [mem_centralizer_singleton_iff]
    have h1 : g * a * g⁻¹ ∈ zpowers a := (mem_normalizer_iff.mp hg a).mp (mem_zpowers a)
    rcases eq_one_or_eq_of_mem_zpowers_two ha h1 with h | h
    · exfalso
      have : a = 1 := by
        calc a = g⁻¹ * (g * a * g⁻¹) * g := by group
          _ = 1 := by rw [h]; group
      rw [this, orderOf_one] at ha
      omega
    · calc g * a = g * a * g⁻¹ * g := by group
        _ = a * g := by rw [h]
  · intro g hg
    rw [mem_normalizer_iff]
    intro x
    have hga := mem_centralizer_singleton_iff.mp hg
    have hconj : ∀ k : ℤ, g * a ^ k * g⁻¹ = a ^ k := by
      intro k
      have hc : Commute g a := hga
      rw [(hc.zpow_right k).eq, mul_inv_cancel_right]
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k, (hconj k).symm⟩
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      have h2 : g * x * g⁻¹ = g * a ^ k * g⁻¹ := by rw [← hk, hconj]
      exact (by simpa using h2 : x = a ^ k).symm

theorem isQuasisimple_of_bad {a : G} (ha : orderOf a = 2) {J : Subgroup G}
    (hJ : IsTwoComponentIn J (centralizer {a}))
    (hbad : TwoComponents.badSubgroup (normalizer (zpowers a : Set G)) = ⊥) :
    IsQuasisimple J := by
  rw [normalizer_zpowers_eq_centralizer ha] at hbad
  obtain ⟨hJC, hT⟩ := L219.isTwoComponentIn_iff_twoComponents.mp hJ
  by_contra hq
  have hle : J.subgroupOf (centralizer {a}) ≤
      TwoComponents.badSubgroup (centralizer ({a} : Set G)) := by
    apply le_sSup
    refine ⟨hT, fun h => hq ?_⟩
    exact LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hJC)
      (isQuasisimple_of_open h)
  rw [hbad, le_bot_iff] at hle
  obtain ⟨x, hx⟩ := exists_not_mem_pPrimeCore hJ.2.2
  apply hx
  have hx1 : (⟨x, hJC x.2⟩ : centralizer ({a} : Set G)) ∈ J.subgroupOf (centralizer {a}) := x.2
  rw [hle, mem_bot] at hx1
  have h3 : (x : G) = 1 := congrArg (fun y : centralizer ({a} : Set G) => (y : G)) hx1
  have : x = 1 := Subtype.ext h3
  rw [this]
  exact one_mem _

omit [Finite G] in
theorem isTwoComponentIn_subgroupOf {H : Subgroup G} {a : G} (ha : a ∈ H) {J : Subgroup G}
    (hJH : J ≤ H) (hJ : IsTwoComponentIn J (centralizer {a})) :
    IsTwoComponentIn (J.subgroupOf H) (centralizer {(⟨a, ha⟩ : H)}) := by
  obtain ⟨hJC, hsub, hq⟩ := hJ
  have hJHC : J ≤ H ⊓ centralizer {a} := le_inf hJH hJC
  have hle : J.subgroupOf H ≤ centralizer {(⟨a, ha⟩ : H)} := by
    intro x hx
    rw [mem_centralizer_singleton_iff]
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp (hJC hx)
  refine ⟨hle, ?_, isTwoQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hJH).symm hq⟩
  have h1 : (J.subgroupOf (H ⊓ centralizer {a})).IsSubnormal :=
    CatalogueBPrimeJoin.subgroupOf_isSubnormal_of_le inf_le_right hsub
  let f : ↥(H ⊓ centralizer ({a} : Set G)) ≃* ↥(centralizer ({(⟨a, ha⟩ : H)} : Set H)) :=
    { toFun := fun x => ⟨⟨x, x.2.1⟩, by
        rw [mem_centralizer_singleton_iff]
        exact Subtype.ext (mem_centralizer_singleton_iff.mp x.2.2)⟩
      invFun := fun y => ⟨y.1.1, y.1.2, mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_centralizer_singleton_iff.mp y.2))⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  have h2 := h1.map f.surjective (f := f.toMonoidHom)
  have heq : (J.subgroupOf (H ⊓ centralizer {a})).map f.toMonoidHom =
      (J.subgroupOf H).subgroupOf (centralizer {(⟨a, ha⟩ : H)}) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      exact ⟨f.symm y, hy, f.apply_symm_apply y⟩
  rw [heq] at h2
  exact h2

end CFSG.ComponentClassification.HarrisLit.C311
