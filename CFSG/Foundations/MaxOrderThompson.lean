module

public import CFSG.GroupTheory.ThompsonIsomorphism
public import CFSG.ThirdParty.BrauerInduction.Background.Group.InternalDirectProduct
public import CFSG.GroupTheory.CommutingProductFixedSubgroup
public import CFSG.RankThree.PGroups.ZJCenterIntersection
public import CFSG.Foundations.MaxCardThompson
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG

open Subgroup

universe u v

section General

variable {G : Type u} [Group G]

theorem mem_maxOrderAbelianFamily_iff {A : Subgroup G} :
    A ∈ maxOrderAbelianFamily G ↔ IsMulCommutative A ∧ Nat.card A = maxAbelianOrder G :=
  Iff.rfl

theorem le_orderThompson {A : Subgroup G} (hA : A ∈ maxOrderAbelianFamily G) :
    A ≤ orderThompson G :=
  le_sSup hA

theorem orderThompson_eq_iSup : orderThompson G = ⨆ A ∈ maxOrderAbelianFamily G, A :=
  sSup_eq_iSup

theorem orderThompson_eq_iSup_subtype :
    orderThompson G = ⨆ A : maxOrderAbelianFamily G, (A : Subgroup G) :=
  sSup_eq_iSup' _

theorem orderZJ_le_orderThompson : orderZJ G ≤ orderThompson G :=
  map_subtype_le _

theorem orderZJ_eq_inf_centralizer :
    orderZJ G = orderThompson G ⊓ centralizer (orderThompson G : Set G) :=
  center_map_subtype_eq_inf_centralizer _

instance orderZJ_isMulCommutative : IsMulCommutative (orderZJ G) := by
  unfold orderZJ
  infer_instance

theorem map_mem_maxOrderAbelianFamily {H : Type v} [Group H] (e : G ≃* H) {A : Subgroup G}
    (hA : A ∈ maxOrderAbelianFamily G) : A.map e.toMonoidHom ∈ maxOrderAbelianFamily H :=
  image_maxOrderAbelianFamily e ▸ ⟨A, hA, rfl⟩

instance orderThompson_characteristic : (orderThompson G).Characteristic :=
  characteristic_iff_map_eq.mpr map_orderThompson

instance orderZJ_characteristic : (orderZJ G).Characteristic :=
  characteristic_iff_map_eq.mpr map_orderZJ

theorem ambientOrderThompson_le (S : Subgroup G) : ambientOrderThompson S ≤ S :=
  map_subtype_le _

theorem ambientOrderZJ_le (S : Subgroup G) : ambientOrderZJ S ≤ S :=
  map_subtype_le _

theorem ambientOrderZJ_le_ambientOrderThompson (S : Subgroup G) :
    ambientOrderZJ S ≤ ambientOrderThompson S :=
  map_mono orderZJ_le_orderThompson

instance ambientOrderZJ_isMulCommutative (S : Subgroup G) :
    IsMulCommutative (ambientOrderZJ S) := by
  unfold ambientOrderZJ
  infer_instance

theorem normalizer_le_normalizer_ambientOrderZJ (S : Subgroup G) :
    normalizer (S : Set G) ≤ normalizer (ambientOrderZJ S : Set G) :=
  normalizer_le_normalizer_image_of_characteristic S (orderZJ S)

theorem normalizer_le_normalizer_ambientOrderThompson (S : Subgroup G) :
    normalizer (S : Set G) ≤ normalizer (ambientOrderThompson S : Set G) :=
  normalizer_le_normalizer_image_of_characteristic S (orderThompson S)

end General

section Finite

variable {G : Type u} [Group G] [Finite G]

theorem maxAbelianOrder_bddAbove :
    BddAbove {n : ℕ | ∃ A : Subgroup G, IsMulCommutative A ∧ Nat.card A = n} :=
  ⟨Nat.card G, by rintro _ ⟨A, -, rfl⟩; exact A.card_le_card_group⟩

theorem card_le_maxAbelianOrder_of_isMulCommutative {A : Subgroup G} (hA : IsMulCommutative A) :
    Nat.card A ≤ maxAbelianOrder G :=
  RankThree.PGroups.card_le_maxAbelianOrder hA

theorem maxOrderAbelianFamily_nonempty : (maxOrderAbelianFamily G).Nonempty :=
  RankThree.PGroups.exists_mem_maxOrderAbelianFamily

theorem isMaxCardAbelian_iff_mem_maxOrderAbelianFamily {A : Subgroup G} :
    IsMaxCardAbelian A ↔ A ∈ maxOrderAbelianFamily G := by
  constructor
  · rintro ⟨hA, hmax⟩
    refine ⟨hA, le_antisymm (card_le_maxAbelianOrder_of_isMulCommutative hA) ?_⟩
    obtain ⟨B, hB, hcard⟩ := maxOrderAbelianFamily_nonempty (G := G)
    exact hcard ▸ hmax B hB
  · rintro ⟨hA, hcard⟩
    exact ⟨hA, fun B hB => hcard ▸ card_le_maxAbelianOrder_of_isMulCommutative hB⟩

theorem setOf_isMaxCardAbelian_eq :
    {A : Subgroup G | IsMaxCardAbelian A} = maxOrderAbelianFamily G :=
  Set.ext fun _ => isMaxCardAbelian_iff_mem_maxOrderAbelianFamily

theorem maxCardThompson_eq_orderThompson : maxCardThompson G = orderThompson G := by
  unfold maxCardThompson orderThompson
  rw [setOf_isMaxCardAbelian_eq]

theorem maxCardZJ_eq_orderZJ : maxCardZJ G = orderZJ G := by
  unfold maxCardZJ orderZJ
  rw [maxCardThompson_eq_orderThompson]

theorem mem_maxOrderAbelianFamily_iff_forall_card_le {A : Subgroup G} :
    A ∈ maxOrderAbelianFamily G ↔
      IsMulCommutative A ∧ ∀ B : Subgroup G, IsMulCommutative B → Nat.card B ≤ Nat.card A :=
  isMaxCardAbelian_iff_mem_maxOrderAbelianFamily.symm

theorem eq_of_mem_maxOrderAbelianFamily_of_le {A B : Subgroup G}
    (hA : A ∈ maxOrderAbelianFamily G) (hB : IsMulCommutative B) (hAB : A ≤ B) : A = B :=
  eq_of_le_of_card_ge hAB (hA.2 ▸ card_le_maxAbelianOrder_of_isMulCommutative hB)

theorem mem_of_mem_centralizer_of_mem_maxOrderAbelianFamily {A : Subgroup G}
    (hA : A ∈ maxOrderAbelianFamily G) {x : G} (hx : x ∈ centralizer (A : Set G)) : x ∈ A := by
  have hAx := eq_of_mem_maxOrderAbelianFamily_of_le hA
    (RankThree.PGroups.isMulCommutative_sup_zpowers hA.1 hx) le_sup_left
  rw [hAx]
  exact mem_sup_right (mem_zpowers x)

theorem centralizer_eq_self_of_mem_maxOrderAbelianFamily {A : Subgroup G}
    (hA : A ∈ maxOrderAbelianFamily G) : centralizer (A : Set G) = A :=
  le_antisymm (fun _ hx => mem_of_mem_centralizer_of_mem_maxOrderAbelianFamily hA hx)
    (le_centralizer_iff_isMulCommutative.mpr hA.1)

theorem center_le_of_mem_maxOrderAbelianFamily {A : Subgroup G}
    (hA : A ∈ maxOrderAbelianFamily G) : center G ≤ A :=
  fun _ hx => mem_of_mem_centralizer_of_mem_maxOrderAbelianFamily hA (center_le_centralizer _ hx)

theorem orderZJ_eq_sInf : orderZJ G = sInf (maxOrderAbelianFamily G) :=
  RankThree.PGroups.zj_center_intersection

theorem orderZJ_eq_iInf : orderZJ G = ⨅ A ∈ maxOrderAbelianFamily G, A := by
  rw [orderZJ_eq_sInf, sInf_eq_iInf]

theorem orderZJ_eq_iInf_subtype :
    orderZJ G = ⨅ A : maxOrderAbelianFamily G, (A : Subgroup G) := by
  rw [orderZJ_eq_sInf, sInf_eq_iInf']

theorem orderZJ_le_of_mem_maxOrderAbelianFamily {A : Subgroup G}
    (hA : A ∈ maxOrderAbelianFamily G) : orderZJ G ≤ A := by
  rw [orderZJ_eq_sInf]
  exact sInf_le hA

theorem mem_orderZJ_iff {x : G} : x ∈ orderZJ G ↔ ∀ A ∈ maxOrderAbelianFamily G, x ∈ A := by
  rw [orderZJ_eq_sInf, mem_sInf]

theorem center_le_orderThompson : center G ≤ orderThompson G := by
  obtain ⟨A, hA⟩ := maxOrderAbelianFamily_nonempty (G := G)
  exact (center_le_of_mem_maxOrderAbelianFamily hA).trans (le_orderThompson hA)

theorem center_le_orderZJ_of_finite : center G ≤ orderZJ G := by
  rw [orderZJ_eq_sInf]
  exact le_sInf fun _ hA => center_le_of_mem_maxOrderAbelianFamily hA

theorem orderZJ_ne_bot_of_isPGroup [Nontrivial G] {p : ℕ} (hp : p.Prime) (hG : IsPGroup p G) :
    orderZJ G ≠ ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  intro hbot
  have hcenter : center G = ⊥ := le_bot_iff.mp (hbot ▸ center_le_orderZJ_of_finite)
  exact hG.bot_lt_center.ne hcenter.symm

theorem orderThompson_eq_top [IsMulCommutative G] : orderThompson G = ⊤ :=
  top_le_iff.mp ((center_eq_top (G := G)).symm.le.trans center_le_orderThompson)

theorem orderZJ_eq_top [IsMulCommutative G] : orderZJ G = ⊤ :=
  top_le_iff.mp ((center_eq_top (G := G)).symm.le.trans center_le_orderZJ_of_finite)

theorem subgroupOf_mem_maxOrderAbelianFamily {A H : Subgroup G}
    (hA : A ∈ maxOrderAbelianFamily G) (hAH : A ≤ H) :
    A.subgroupOf H ∈ maxOrderAbelianFamily H :=
  isMaxCardAbelian_iff_mem_maxOrderAbelianFamily.mp
    ((isMaxCardAbelian_iff_mem_maxOrderAbelianFamily.mpr hA).subgroupOf hAH)

theorem map_subtype_mem_maxOrderAbelianFamily {H M : Subgroup G}
    (hM : M ∈ maxOrderAbelianFamily G) (hMH : M ≤ H) {B : Subgroup H}
    (hB : B ∈ maxOrderAbelianFamily H) : B.map H.subtype ∈ maxOrderAbelianFamily G :=
  isMaxCardAbelian_iff_mem_maxOrderAbelianFamily.mp
    ((isMaxCardAbelian_iff_mem_maxOrderAbelianFamily.mpr hM).map_subtype hMH
      (isMaxCardAbelian_iff_mem_maxOrderAbelianFamily.mpr hB))

theorem maxAbelianOrder_subgroup_eq {H M : Subgroup G} (hM : M ∈ maxOrderAbelianFamily G)
    (hMH : M ≤ H) : maxAbelianOrder H = maxAbelianOrder G := by
  have h := (subgroupOf_mem_maxOrderAbelianFamily hM hMH).2
  rw [Nat.card_congr (subgroupOfEquivOfLe hMH).toEquiv] at h
  exact h.symm.trans hM.2

theorem orderZJ_le_ambientOrderZJ {H M : Subgroup G} (hM : M ∈ maxOrderAbelianFamily G)
    (hMH : M ≤ H) : orderZJ G ≤ ambientOrderZJ H := by
  intro x hx
  have hxH : x ∈ H := hMH (orderZJ_le_of_mem_maxOrderAbelianFamily hM hx)
  refine ⟨⟨x, hxH⟩, mem_orderZJ_iff.mpr fun B hB => ?_, rfl⟩
  obtain ⟨y, hy, hyx⟩ := orderZJ_le_of_mem_maxOrderAbelianFamily
    (map_subtype_mem_maxOrderAbelianFamily hM hMH hB) hx
  have : y = ⟨x, hxH⟩ := Subtype.ext hyx
  exact this ▸ hy

end Finite


section Products

theorem maxAbelianOrder_prod {R P : Type*} [Group R] [Group P] [Finite R] [Finite P]
    [IsMulCommutative R] :
    maxAbelianOrder (R × P) = Nat.card R * maxAbelianOrder P := by
  obtain ⟨A₀, hA₀⟩ := maxOrderAbelianFamily_nonempty (G := P)
  apply le_antisymm
  · unfold maxAbelianOrder
    apply csSup_le
      (s := {n : ℕ | ∃ A : Subgroup (R × P), IsMulCommutative A ∧ Nat.card A = n})
      ⟨1, ⊥, inferInstance, Subgroup.card_bot⟩
    rintro n ⟨B, hB, rfl⟩
    let f : B →* P := (MonoidHom.snd R P).comp B.subtype
    have hcardker := Subgroup.card_ker_mul_card_range f
    have hker_le : Nat.card f.ker ≤ Nat.card R := by
      refine Nat.card_le_card_of_injective
        (fun k : f.ker => ((k : B) : R × P).1) ?_
      intro x y hxy
      have hx2 : ((x : B) : R × P).2 = 1 := by
        have := MonoidHom.mem_ker.mp x.2
        simpa [f] using this
      have hy2 : ((y : B) : R × P).2 = 1 := by
        have := MonoidHom.mem_ker.mp y.2
        simpa [f] using this
      apply Subtype.ext
      apply Subtype.ext
      exact Prod.ext hxy (by rw [hx2, hy2])
    have hrange_comm : IsMulCommutative f.range := by
      rw [isMulCommutative_iff]
      intro x y
      obtain ⟨b, hb⟩ := x.2
      obtain ⟨c, hc⟩ := y.2
      apply Subtype.ext
      change (x : P) * (y : P) = (y : P) * (x : P)
      rw [← hb, ← hc, ← map_mul, ← map_mul]
      exact congrArg f (isMulCommutative_iff.mp hB b c)
    have hrange_le : Nat.card f.range ≤ maxAbelianOrder P :=
      card_le_maxAbelianOrder_of_isMulCommutative hrange_comm
    change Nat.card B ≤ Nat.card R * maxAbelianOrder P
    rw [← hcardker]
    exact Nat.mul_le_mul hker_le hrange_le
  · have hcommA : IsMulCommutative ((⊤ : Subgroup R).prod A₀) := by
      rw [isMulCommutative_iff]
      intro x y
      apply Subtype.ext
      apply Prod.ext
      · exact (IsMulCommutative.is_comm (M := R)).comm
          ((x : R × P).1) ((y : R × P).1)
      · have hx : ((x : R × P).2) ∈ A₀ := (Subgroup.mem_prod.mp x.2).2
        have hy : ((y : R × P).2) ∈ A₀ := (Subgroup.mem_prod.mp y.2).2
        exact congrArg Subtype.val
          (isMulCommutative_iff.mp hA₀.1 ⟨(x : R × P).2, hx⟩ ⟨(y : R × P).2, hy⟩)
    have hcard : Nat.card ((⊤ : Subgroup R).prod A₀) =
        Nat.card R * maxAbelianOrder P := by
      rw [Nat.card_congr (Subgroup.prodEquiv (⊤ : Subgroup R) A₀).toEquiv, Nat.card_prod,
        Subgroup.card_top, hA₀.2]
    have hle := card_le_maxAbelianOrder_of_isMulCommutative hcommA
    rw [← hcard]
    exact hle

theorem mem_maxOrderAbelianFamily_prod_iff {R P : Type*} [Group R] [Group P]
    [Finite R] [Finite P] [IsMulCommutative R] {B : Subgroup (R × P)} :
    B ∈ maxOrderAbelianFamily (R × P) ↔
      ∃ A ∈ maxOrderAbelianFamily P, B = (⊤ : Subgroup R).prod A := by
  constructor
  · intro hB
    let f : B →* P := (MonoidHom.snd R P).comp B.subtype
    have hcardB : Nat.card B = Nat.card R * maxAbelianOrder P := by
      rw [hB.2, maxAbelianOrder_prod]
    have hprod_eq : Nat.card f.ker * Nat.card f.range =
        Nat.card R * maxAbelianOrder P := by
      rw [Subgroup.card_ker_mul_card_range f, hcardB]
    have hker_le : Nat.card f.ker ≤ Nat.card R := by
      refine Nat.card_le_card_of_injective
        (fun k : f.ker => ((k : B) : R × P).1) ?_
      intro x y hxy
      have hx2 : ((x : B) : R × P).2 = 1 := by
        have := MonoidHom.mem_ker.mp x.2
        simpa [f] using this
      have hy2 : ((y : B) : R × P).2 = 1 := by
        have := MonoidHom.mem_ker.mp y.2
        simpa [f] using this
      apply Subtype.ext
      apply Subtype.ext
      exact Prod.ext hxy (by rw [hx2, hy2])
    have hrange_comm : IsMulCommutative f.range := by
      rw [isMulCommutative_iff]
      intro x y
      obtain ⟨b, hb⟩ := x.2
      obtain ⟨c, hc⟩ := y.2
      apply Subtype.ext
      change (x : P) * (y : P) = (y : P) * (x : P)
      rw [← hb, ← hc, ← map_mul, ← map_mul]
      exact congrArg f (isMulCommutative_iff.mp hB.1 b c)
    have hrange_le : Nat.card f.range ≤ maxAbelianOrder P :=
      card_le_maxAbelianOrder_of_isMulCommutative hrange_comm
    have hker_eq : Nat.card f.ker = Nat.card R := by
      by_contra hne
      have hlt : Nat.card f.ker < Nat.card R := lt_of_le_of_ne hker_le hne
      have hltprod : Nat.card f.ker * Nat.card f.range <
          Nat.card R * maxAbelianOrder P :=
        calc Nat.card f.ker * Nat.card f.range
            < Nat.card R * Nat.card f.range :=
              Nat.mul_lt_mul_of_lt_of_le hlt le_rfl (Nat.card_pos)
          _ ≤ Nat.card R * maxAbelianOrder P := Nat.mul_le_mul_left _ hrange_le
      rw [hprod_eq] at hltprod
      exact (Nat.lt_irrefl _ hltprod)
    have hprod_eq' : Nat.card R * Nat.card f.range =
        Nat.card R * maxAbelianOrder P := by
      rw [hker_eq] at hprod_eq
      exact hprod_eq
    have hrange_eq : Nat.card f.range = maxAbelianOrder P :=
      Nat.mul_left_cancel (Nat.card_pos (α := R)) hprod_eq'
    refine ⟨f.range, mem_maxOrderAbelianFamily_iff.mpr ⟨hrange_comm, hrange_eq⟩, ?_⟩
    apply Subgroup.eq_of_le_of_card_ge
    · intro b hb
      exact Subgroup.mem_prod.mpr
        ⟨Subgroup.mem_top _, ⟨⟨b, hb⟩, rfl⟩⟩
    · have hcard_prod : Nat.card ((⊤ : Subgroup R).prod f.range) = Nat.card B := by
        rw [Nat.card_congr (Subgroup.prodEquiv (⊤ : Subgroup R) f.range).toEquiv,
          Nat.card_prod, Subgroup.card_top, hrange_eq, hcardB]
      exact le_of_eq hcard_prod
  · rintro ⟨A, hA, rfl⟩
    have hcommA : IsMulCommutative ((⊤ : Subgroup R).prod A) := by
      rw [isMulCommutative_iff]
      intro x y
      apply Subtype.ext
      apply Prod.ext
      · exact (IsMulCommutative.is_comm (M := R)).comm
          ((x : R × P).1) ((y : R × P).1)
      · have hx : ((x : R × P).2) ∈ A := (Subgroup.mem_prod.mp x.2).2
        have hy : ((y : R × P).2) ∈ A := (Subgroup.mem_prod.mp y.2).2
        exact congrArg Subtype.val
          (isMulCommutative_iff.mp hA.1 ⟨(x : R × P).2, hx⟩ ⟨(y : R × P).2, hy⟩)
    refine mem_maxOrderAbelianFamily_iff.mpr ⟨hcommA, ?_⟩
    rw [Nat.card_congr (Subgroup.prodEquiv (⊤ : Subgroup R) A).toEquiv, Nat.card_prod,
      Subgroup.card_top, hA.2, maxAbelianOrder_prod]

theorem orderThompson_prod {R P : Type*} [Group R] [Group P] [Finite R] [Finite P]
    [IsMulCommutative R] :
    orderThompson (R × P) = (⊤ : Subgroup R).prod (orderThompson P) := by
  apply le_antisymm
  · rw [orderThompson_eq_iSup_subtype]
    refine iSup_le ?_
    intro B
    obtain ⟨A, hA, hB⟩ :=
      (mem_maxOrderAbelianFamily_prod_iff (R := R) (P := P)).mp B.2
    rw [hB]
    exact Subgroup.prod_mono le_top (le_orderThompson hA)
  · rw [Subgroup.prod_le_iff]
    constructor
    · rintro _ ⟨r, -, rfl⟩
      obtain ⟨A, hA⟩ := maxOrderAbelianFamily_nonempty (G := P)
      have hRA : (⊤ : Subgroup R).prod A ≤ orderThompson (R × P) :=
        le_orderThompson ((mem_maxOrderAbelianFamily_prod_iff (R := R) (P := P)).mpr
          ⟨A, hA, rfl⟩)
      exact hRA (Subgroup.mem_prod.mpr ⟨Subgroup.mem_top r, Subgroup.one_mem A⟩)
    · rw [orderThompson_eq_iSup_subtype, Subgroup.map_iSup]
      refine iSup_le ?_
      intro A
      rintro _ ⟨a, ha, rfl⟩
      have hRA : (⊤ : Subgroup R).prod (A : Subgroup P) ≤ orderThompson (R × P) :=
        le_orderThompson ((mem_maxOrderAbelianFamily_prod_iff (R := R) (P := P)).mpr
          ⟨(A : Subgroup P), A.2, rfl⟩)
      exact hRA (Subgroup.mem_prod.mpr ⟨Subgroup.mem_top (1 : R), ha⟩)

theorem maxAbelianOrder_sup_of_internalDirectProduct {G : Type*} [Group G] [Finite G]
    {R P : Subgroup G} (hR : IsMulCommutative R)
    (hcomm : ∀ r ∈ R, ∀ p ∈ P, r * p = p * r) (hdisj : R ⊓ P = ⊥) :
    maxAbelianOrder ↥(R ⊔ P) = Nat.card R * maxAbelianOrder ↥P := by
  let e : (↥R × ↥P) ≃* ↥(R ⊔ P) :=
    Subgroup.mulEquivProdOfInternalDirect R P (R ⊔ P) le_sup_left le_sup_right
      (fun {c p} hc hp => show Commute c p from hcomm c hc p hp) hdisj
      (fun {h} hh => CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hcomm hh)
  rw [← maxAbelianOrder_eq_of_mulEquiv e]
  exact maxAbelianOrder_prod

theorem ambientOrderThompson_sup_of_internalDirectProduct {G : Type*} [Group G] [Finite G]
    {R P : Subgroup G} (hR : IsMulCommutative R)
    (hcomm : ∀ r ∈ R, ∀ p ∈ P, r * p = p * r) (hdisj : R ⊓ P = ⊥) :
    ambientOrderThompson (R ⊔ P) = R ⊔ ambientOrderThompson P := by
  let e : (↥R × ↥P) ≃* ↥(R ⊔ P) :=
    Subgroup.mulEquivProdOfInternalDirect R P (R ⊔ P) le_sup_left le_sup_right
      (fun {c p} hc hp => show Commute c p from hcomm c hc p hp) hdisj
      (fun {h} hh => CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hcomm hh)
  have he_apply : ∀ (r : ↥R) (p : ↥P),
      ((e (r, p) : ↥(R ⊔ P)) : G) = (r : G) * (p : G) := by
    intro r p
    simp only [e, Subgroup.mulEquivProdOfInternalDirect]
    rfl
  have hprod : orderThompson (↥R × ↥P) = (⊤ : Subgroup ↥R).prod (orderThompson ↥P) :=
    orderThompson_prod
  have hmap := congrArg (fun H : Subgroup (↥R × ↥P) => H.map e.toMonoidHom) hprod
  rw [map_orderThompson e] at hmap
  have hmapG := congrArg (fun H : Subgroup ↥(R ⊔ P) => H.map (R ⊔ P).subtype) hmap
  rw [ambientOrderThompson]
  rw [hmapG, Subgroup.map_map]
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨⟨r, p⟩, ⟨-, hp⟩, hx⟩
    have hp' : (p : G) ∈ ambientOrderThompson P :=
      Subgroup.mem_map_of_mem P.subtype hp
    have hm : (r : G) * (p : G) ∈ R ⊔ ambientOrderThompson P :=
      Subgroup.mul_mem_sup r.2 hp'
    rw [← hx]
    change ((e (r, p) : ↥(R ⊔ P)) : G) ∈ R ⊔ ambientOrderThompson P
    rw [he_apply]
    exact hm
  · intro hx
    have hcommJP : ∀ r ∈ R, ∀ j ∈ ambientOrderThompson P, r * j = j * r := by
      intro r hr j hj
      rw [ambientOrderThompson] at hj
      obtain ⟨j₀, hj₀, rfl⟩ := hj
      exact hcomm r hr (j₀ : P) j₀.2
    obtain ⟨r, hr, p, hp, hxp⟩ :=
      CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hcommJP hx
    rw [ambientOrderThompson] at hp
    obtain ⟨p₀, hp₀, rfl⟩ := hp
    refine ⟨(⟨r, hr⟩, p₀), ⟨Subgroup.mem_top _, hp₀⟩, ?_⟩
    change ((e (⟨r, hr⟩, p₀) : ↥(R ⊔ P)) : G) = x
    rw [he_apply]
    exact hxp

theorem ambientOrderThompson_le_of_le_of_maxAbelianOrder_eq {G : Type*} [Group G]
    {H S : Subgroup G} [Finite S] (hHS : H ≤ S)
    (hmax : maxAbelianOrder H = maxAbelianOrder S) :
    ambientOrderThompson H ≤ ambientOrderThompson S := by
  rw [ambientOrderThompson, ambientOrderThompson]
  refine Subgroup.map_le_iff_le_comap.mpr ?_
  rw [orderThompson_eq_iSup_subtype]
  refine iSup_le ?_
  intro A a ha
  have hAmap_le : (A : Subgroup H).map H.subtype ≤ S := by
    rintro _ ⟨x, hx, rfl⟩
    exact hHS x.2
  let A' : Subgroup S := ((A : Subgroup H).map H.subtype).subgroupOf S
  have hA'comm : IsMulCommutative A' := by
    have hmapcomm : IsMulCommutative ((A : Subgroup H).map H.subtype) :=
      @Subgroup.map_isMulCommutative ↥H G _ _ (A : Subgroup H) H.subtype A.2.1
    exact Subgroup.subgroupOf_isMulCommutative (K := S)
      (H := (A : Subgroup H).map H.subtype)
  have hA'mem : A' ∈ maxOrderAbelianFamily S := by
    refine mem_maxOrderAbelianFamily_iff.mpr ⟨hA'comm, ?_⟩
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAmap_le).toEquiv,
      Subgroup.card_map_of_injective H.subtype_injective, A.2.2, hmax]
  have hale : (⟨(a : G), hHS a.2⟩ : S) ∈ orderThompson S :=
    le_orderThompson hA'mem (by
      rw [Subgroup.mem_subgroupOf]
      exact Subgroup.mem_map_of_mem H.subtype ha)
  exact Subgroup.mem_map_of_mem S.subtype hale

end Products


theorem maxAbelianOrder_eq_of_outside_bound
    {G : Type*} [Group G] [Finite G]
    {S W R P : Subgroup G}
    (hWS : W ≤ S)
    (hWmax : maxAbelianOrder ↥W = Nat.card R * maxAbelianOrder ↥P)
    (hbound : ∀ B : Subgroup G, B ≤ S → IsMulCommutative B → ¬ B ≤ W →
      Nat.card B ≤ 8 * maxAbelianOrder ↥P)
    (hRcard : Nat.card R = 16)
    (ha : 0 < maxAbelianOrder ↥P) :
    maxAbelianOrder ↥S = maxAbelianOrder ↥W := by
  classical
  have hle : maxAbelianOrder ↥W ≤ maxAbelianOrder ↥S := by
    obtain ⟨B, hB⟩ := maxOrderAbelianFamily_nonempty (G := ↥W)
    letI : IsMulCommutative B := hB.1
    have hBcomm : IsMulCommutative (B.map W.subtype) :=
      Subgroup.map_isMulCommutative (H := B) W.subtype
    have hBcard : Nat.card (B.map W.subtype) = Nat.card B :=
      Subgroup.card_map_of_injective W.subtype_injective
    have hBle : B.map W.subtype ≤ S := (Subgroup.map_subtype_le B).trans hWS
    let C : Subgroup ↥S := (B.map W.subtype).subgroupOf S
    have hCcomm : IsMulCommutative C :=
      Subgroup.subgroupOf_isMulCommutative (K := S) (H := B.map W.subtype)
    have hCcard : Nat.card C = Nat.card (B.map W.subtype) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBle).toEquiv
    have hcard := card_le_maxAbelianOrder_of_isMulCommutative (G := ↥S) hCcomm
    calc maxAbelianOrder ↥W = Nat.card B := hB.2.symm
      _ = Nat.card (B.map W.subtype) := hBcard.symm
      _ = Nat.card C := hCcard.symm
      _ ≤ maxAbelianOrder ↥S := hcard
  have hge : maxAbelianOrder ↥S ≤ maxAbelianOrder ↥W := by
    obtain ⟨A, hA⟩ := maxOrderAbelianFamily_nonempty (G := ↥S)
    letI : IsMulCommutative A := hA.1
    have hAcomm : IsMulCommutative (A.map S.subtype) :=
      Subgroup.map_isMulCommutative (H := A) S.subtype
    have hAcard : Nat.card (A.map S.subtype) = Nat.card A :=
      Subgroup.card_map_of_injective S.subtype_injective
    have hAle : Nat.card A ≤ maxAbelianOrder ↥W := by
      by_cases hAW : A.map S.subtype ≤ W
      · let B : Subgroup ↥W := (A.map S.subtype).subgroupOf W
        have hBcomm : IsMulCommutative B :=
          Subgroup.subgroupOf_isMulCommutative (K := W)
            (H := (A : Subgroup ↥S).map S.subtype)
        have hBcard : Nat.card B = Nat.card (A.map S.subtype) :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAW).toEquiv
        have hcard := card_le_maxAbelianOrder_of_isMulCommutative (G := ↥W) hBcomm
        calc Nat.card A = Nat.card (A.map S.subtype) := hAcard.symm
          _ = Nat.card B := hBcard.symm
          _ ≤ maxAbelianOrder ↥W := hcard
      · have hb := hbound (A.map S.subtype) (Subgroup.map_subtype_le A) hAcomm hAW
        have hlt : 8 * maxAbelianOrder ↥P < 16 * maxAbelianOrder ↥P := by omega
        calc Nat.card A = Nat.card (A.map S.subtype) := hAcard.symm
          _ ≤ 8 * maxAbelianOrder ↥P := hb
          _ ≤ 16 * maxAbelianOrder ↥P := le_of_lt hlt
          _ = maxAbelianOrder ↥W := by rw [hWmax, hRcard]
    calc maxAbelianOrder ↥S = Nat.card A := hA.2.symm
      _ ≤ maxAbelianOrder ↥W := hAle
  exact le_antisymm hge hle

end CFSG
