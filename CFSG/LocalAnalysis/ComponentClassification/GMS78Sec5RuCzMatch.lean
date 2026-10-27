module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuCzMatchCore
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuCzMatchModel

public section

namespace CFSG.ComponentClassification.GMS78.RuCz

open Subgroup CFSG.Open CFSG.LieType.BorelTits CFSG.CosetTable CFSG.GMS78Ru CFSG.GMS78RuSim
  CFSG.GMS78RuQ CFSG.GMS78RuN CFSG.ComponentClassification.GMS78.RuPi7
  CFSG.ComponentClassification.GMS78.RuAsm CFSG.ComponentClassification.GMS78.RuN
  CFSG.Sporadic.Bridge

@[expose] noncomputable def czJ0 : Subgroup Pi7 := Subgroup.closure (czImg '' {i | i < 6})

theorem czJ0_le_ruM12 : czJ0 ≤ ruM12 := by
  refine (closure_le _).2 ?_
  rintro _ ⟨i, hi, rfl⟩
  exact czImg_mem_ruM12 (by simp only [Set.mem_ofPred_eq] at hi; omega)

theorem czJ0_le_ruM2 : czJ0 ≤ ruM2 := czJ0_le_ruM12.trans (letterSub_mono (by decide))

@[expose] def toFin7 (w : List (ℕ × Bool)) : List (Fin 7 × Bool) :=
  w.map fun l => (⟨l.1 % 7, Nat.mod_lt _ (by decide)⟩, l.2)

theorem wordProd_pi7L (w : List (ℕ × Bool)) (hw : ∀ l ∈ w, l.1 < 7) :
    wordProd pi7L w = pi7Word (toFin7 w) := by
  induction w with
  | nil => simp [wordProd, toFin7, pi7Word_nil]
  | cons l w ih =>
    have hl : l.1 < 7 := hw l List.mem_cons_self
    have e1 : toFin7 (l :: w) = [(⟨l.1 % 7, Nat.mod_lt _ (by decide)⟩, l.2)] ++ toFin7 w := rfl
    rw [wordProd_cons, ih fun l' hl' => hw l' (List.mem_cons_of_mem _ hl'), e1, pi7Word_append]
    congr 1
    obtain ⟨i, b⟩ := l
    simp only at hl
    have e : (⟨i % 7, Nat.mod_lt _ (by decide)⟩ : Fin 7) = ⟨i, hl⟩ :=
      Fin.ext (Nat.mod_eq_of_lt hl)
    rw [e, pi7L_of_lt hl]
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact (pi7Word_letter_inv _).symm
    · simp only [↓reduceIte]
      exact (pi7Word_letter _).symm

theorem czmJWord_eq : ∀ i < 6, czmJWord i = toFin7 (l10Word i) := by decide

theorem czImg_eq {i : ℕ} (hi : i < 6) : czImg i = pi7Word (czmJWord i) := by
  rw [czImg, wordProd_pi7L _ fun l hl => by have := l10Word_lt i (by omega) l hl; omega,
    czmJWord_eq i hi]

theorem pi7Word_invRev (w : List (Fin 7 × Bool)) :
    pi7Word (FreeGroup.invRev w) = (pi7Word w)⁻¹ := by
  unfold pi7Word
  rw [← map_inv, FreeGroup.inv_mk]

theorem czmRep_letters : ∀ i < 24, ∀ p ∈ czmRep i, p.1 ∈ ([0, 1, 2, 3, 4] : List (Fin 7)) := by
  decide

theorem czmRep_renumber : ∀ i < 24, (renumber ruSub2 (czmRep i)).isSome = true ∧
    (renumber ruSub2 (FreeGroup.invRev (czmRep i))).isSome = true := by
  decide

theorem czmJWord_renumber : ∀ i < 6, (renumber ruSub2 (czmJWord i)).isSome = true ∧
    (renumber ruSub2 (FreeGroup.invRev (czmJWord i))).isSome = true := by
  decide

section Checks

theorem ruM2EquivModel_conj_word {w : List (Fin 7 × Bool)}
    (hw : (renumber ruSub2 w).isSome = true)
    (hwi : (renumber ruSub2 (FreeGroup.invRev w)).isSome = true) (g x : ↥ruM2)
    (hg : (g : Pi7) = pi7Word w) {p : NTrip} (hp : p ∈ czmX0)
    (hx : ruM2EquivModel x = toModel p) :
    ruM2EquivModel (g * x * g⁻¹) = toModel (czmConjW w p) := by
  have hgi : ((g⁻¹ : ↥ruM2) : Pi7) = pi7Word (FreeGroup.invRev w) := by
    rw [Subgroup.coe_inv, hg, pi7Word_invRev]
  rw [map_mul, map_mul, ruM2EquivModel_word hw g hg, ruM2EquivModel_word hwi _ hgi, hx, czmConjW,
    (toModel_czmConj (lift_ruNImg w).1 (lift_ruNImg _).1 (czmX0_parts hp).1).2]

theorem ruZ0_sq : ruZ0 * ruZ0 = 1 := by
  have e : ruM2EquivModel (⟨ruZ0, ruZ0_mem_ruM2⟩ * ⟨ruZ0, ruZ0_mem_ruM2⟩) =
      ruM2EquivModel 1 := by
    rw [map_mul, ruM2EquivModel_ruZ0, toModel_czmZ0, ← map_mul, map_one]
    have h : (⟨0, 4⟩ : RuR) * ⟨0, 4⟩ = 1 := by
      rw [RuR.mul_def, RuR.one_def]
      refine RuR.ext (by decide) ?_
      change (4 : Fin 8) ^^^ 4 ^^^ nBeta 0 0 = 0
      rw [nBeta_zero_left]
      decide
    rw [h, map_one]
  exact congrArg Subtype.val (ruM2EquivModel.injective e)

theorem mem_zpowers_ruZ0 {c : Pi7} (hc : c ∈ zpowers ruZ0) : c = 1 ∨ c = ruZ0 := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hc
  have h2 : ruZ0 ^ (2 : ℤ) = 1 := by rw [zpow_two, ruZ0_sq]
  rcases Int.even_or_odd k with ⟨n, rfl⟩ | ⟨n, rfl⟩
  · left
    rw [← two_mul, zpow_mul, h2, one_zpow]
  · right
    rw [zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]

theorem czX0_comm_ruZ0 {x : Pi7} (hx : x ∈ czX0) : x * ruZ0 = ruZ0 * x := by
  obtain ⟨hx2, a, ha, hax⟩ := mem_czPre.1 hx
  have hc : (⟨0, 4⟩ : RuR) ∈ center RuR := by
    rw [center_RuR]
    rfl
  have e : ruM2EquivModel (⟨x, hx2⟩ * ⟨ruZ0, ruZ0_mem_ruM2⟩) =
      ruM2EquivModel (⟨ruZ0, ruZ0_mem_ruM2⟩ * ⟨x, hx2⟩) := by
    rw [map_mul, map_mul, ← hax, ruM2EquivModel_ruZ0, toModel_czmZ0, ← map_mul, ← map_mul,
      (mem_center_iff.1 hc a).symm]
  exact congrArg Subtype.val (ruM2EquivModel.injective e)

theorem exists_czmX0_of_mem {x : Pi7} (hx : x ∈ czX0) :
    ∃ hx2 : x ∈ ruM2, ∃ p ∈ czmX0, ruM2EquivModel ⟨x, hx2⟩ = toModel p := by
  obtain ⟨hx2, hxM⟩ := mem_czPre.1 hx
  obtain ⟨p, hp, hpx⟩ := exists_czmX0 hxM
  exact ⟨hx2, p, hp, hpx.symm⟩

theorem conj_zpowers_ruZ0 {g c : Pi7} (hg : g ∈ ruM12) (hc : c ∈ zpowers ruZ0) :
    g * c * g⁻¹ = c := by
  rcases mem_zpowers_ruZ0 hc with rfl | rfl
  · group
  · rw [mem_centralizer_singleton_iff.1 (ruM12_le_centralizer_ruZ0 hg), mul_inv_cancel_right]

@[expose] noncomputable def czK1 : Subgroup Pi7 where
  carrier := {g | g ∈ ruM12 ∧ ∀ x ∈ czX0, g * x * g⁻¹ * x⁻¹ ∈ zpowers ruZ0}
  mul_mem' := by
    rintro g h ⟨hg, hgx⟩ ⟨hh, hhx⟩
    refine ⟨mul_mem hg hh, fun x hx => ?_⟩
    have e : g * h * x * (g * h)⁻¹ * x⁻¹ =
        g * (h * x * h⁻¹ * x⁻¹) * g⁻¹ * (g * x * g⁻¹ * x⁻¹) := by group
    rw [e, conj_zpowers_ruZ0 hg (hhx x hx)]
    exact mul_mem (hhx x hx) (hgx x hx)
  one_mem' := ⟨one_mem _, fun x _ => by
    rw [one_mul, inv_one, mul_one, mul_inv_cancel]
    exact one_mem _⟩
  inv_mem' := by
    rintro g ⟨hg, hgx⟩
    refine ⟨inv_mem hg, fun x hx => ?_⟩
    have hy : g⁻¹ * x * g ∈ czX0 := by
      have := (mem_normalizer_iff.1 (ruM12_le_normalizer_czX0 (inv_mem hg)) x).1 hx
      rwa [inv_inv] at this
    have e : g⁻¹ * x * g⁻¹⁻¹ * x⁻¹ = (g * (g⁻¹ * x * g) * g⁻¹ * (g⁻¹ * x * g)⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem (hgx _ hy)

theorem czK1_le_ruM12 : czK1 ≤ ruM12 := fun _ h => h.1

theorem not_mem_czK1_of_lt {i j : ℕ} (hij : i < j) (hj : j < 24)
    (h : (pi7Word (czmRep i))⁻¹ * pi7Word (czmRep j) ∈ czK1) : False := by
  have hi : i < 24 := by omega
  have hcheck := czm_rep_check
  simp only [czmRepCheck, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, List.any_eq_true] at hcheck
  rcases hcheck i hi j hj with h1 | ⟨p, hp, hne⟩
  · exact h1 hij
  have hgi12 : pi7Word (czmRep i) ∈ ruM12 := pi7Word_mem_letterSub (czmRep_letters i hi)
  have hgj12 : pi7Word (czmRep j) ∈ ruM12 := pi7Word_mem_letterSub (czmRep_letters j hj)
  obtain ⟨gi, hgi⟩ : ∃ g : ↥ruM2, (g : Pi7) = pi7Word (czmRep i) :=
    ⟨⟨_, letterSub_mono (by decide) hgi12⟩, rfl⟩
  obtain ⟨gj, hgj⟩ : ∃ g : ↥ruM2, (g : Pi7) = pi7Word (czmRep j) :=
    ⟨⟨_, letterSub_mono (by decide) hgj12⟩, rfl⟩
  obtain ⟨x, hxm⟩ : ∃ x : ↥ruM2, ruM2EquivModel x = toModel p :=
    ⟨_, MulEquiv.apply_symm_apply _ _⟩
  have hxX : (x : Pi7) ∈ czX0 := mem_czPre.2 ⟨x.2, by
    rw [Subtype.coe_eta, hxm]
    exact (czmX0_parts hp).2⟩
  have ei := ruM2EquivModel_conj_word (czmRep_renumber i hi).1 (czmRep_renumber i hi).2 gi x
    hgi hp hxm
  have ej := ruM2EquivModel_conj_word (czmRep_renumber j hj).1 (czmRep_renumber j hj).2 gj x
    hgj hp hxm
  have hvi := (toModel_czmConj (lift_ruNImg (czmRep i)).1
    (lift_ruNImg (FreeGroup.invRev (czmRep i))).1 (czmX0_parts hp).1).1
  have hvj := (toModel_czmConj (lift_ruNImg (czmRep j)).1
    (lift_ruNImg (FreeGroup.invRev (czmRep j))).1 (czmX0_parts hp).1).1
  refine (Bool.eq_false_iff.1 hne) ?_
  rw [czmSame_iff (y := czmConjW (czmRep i) p) (y' := czmConjW (czmRep j) p) hvi hvj, ← ei, ← ej,
    ← ruM2EquivModel_ruZ0, ← map_mul]
  have hc := h.2 _ hxX
  have hyj : ((gj * x * gj⁻¹ : ↥ruM2) : Pi7) = pi7Word (czmRep i) *
      ((pi7Word (czmRep i))⁻¹ * pi7Word (czmRep j) * (x : Pi7) *
        ((pi7Word (czmRep i))⁻¹ * pi7Word (czmRep j))⁻¹ * (x : Pi7)⁻¹) *
      (pi7Word (czmRep i))⁻¹ * ((gi * x * gi⁻¹ : ↥ruM2) : Pi7) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hgi, hgj]
    group
  rw [conj_zpowers_ruZ0 hgi12 hc] at hyj
  rcases mem_zpowers_ruZ0 hc with hc1 | hcz
  · left
    rw [hc1, one_mul] at hyj
    exact congrArg ruM2EquivModel (Subtype.ext hyj.symm)
  · right
    rw [hcz] at hyj
    have hyiX : ((gi * x * gi⁻¹ : ↥ruM2) : Pi7) ∈ czX0 := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hgi]
      exact (mem_normalizer_iff.1 (ruM12_le_normalizer_czX0 hgi12) _).1 hxX
    congr 1
    apply Subtype.ext
    rw [show ((gj * x * gj⁻¹ * ⟨ruZ0, ruZ0_mem_ruM2⟩ : ↥ruM2) : Pi7) =
      ((gj * x * gj⁻¹ : ↥ruM2) : Pi7) * ruZ0 from rfl, hyj]
    generalize ((gi * x * gi⁻¹ : ↥ruM2) : Pi7) = y at hyiX ⊢
    rw [mul_assoc, czX0_comm_ruZ0 hyiX, ← mul_assoc, ruZ0_sq, one_mul]

theorem card_czK1_le :
    Nat.card czK1 ≤ 2048 := by
  have hfin : Finite Pi7 := card_pi7_le.1
  let g : Fin 24 → Pi7 := fun i => pi7Word (czmRep i)
  have hg : ∀ i, g i ∈ ruM12 := fun i => pi7Word_mem_letterSub (czmRep_letters i i.2)
  have hd : ∀ i j, (g i)⁻¹ * g j ∈ czK1 → i = j := by
    intro i j h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hij | hij
    · exact not_mem_czK1_of_lt hij j.2 h
    · have h' : (g j)⁻¹ * g i ∈ czK1 := by
        have := inv_mem h
        rwa [mul_inv_rev, inv_inv] at this
      exact not_mem_czK1_of_lt hij i.2 h'
  have h24 := card_mul_le_of_distinct czK1_le_ruM12 g hg hd
  rw [card_ruM12] at h24
  omega

theorem czJ0_le_czK1 : czJ0 ≤ czK1 := by
  have hcheck := czm_j_check
  simp only [czmJCheck, List.all_eq_true, List.mem_range] at hcheck
  refine (closure_le _).2 ?_
  rintro _ ⟨i, hi, rfl⟩
  simp only [Set.mem_ofPred_eq] at hi
  have hi12 : czImg i ∈ ruM12 := czImg_mem_ruM12 (by omega)
  refine ⟨hi12, fun x hx => ?_⟩
  obtain ⟨hx2, p, hp, hxp⟩ := exists_czmX0_of_mem hx
  obtain ⟨g, hg⟩ : ∃ g : ↥ruM2, (g : Pi7) = pi7Word (czmJWord i) :=
    ⟨⟨_, letterSub_mono (by decide) ((czImg_eq hi) ▸ hi12)⟩, rfl⟩
  have e := ruM2EquivModel_conj_word (czmJWord_renumber i hi).1 (czmJWord_renumber i hi).2 g
    ⟨x, hx2⟩ hg hp hxp
  have hv := (toModel_czmConj (lift_ruNImg (czmJWord i)).1
    (lift_ruNImg (FreeGroup.invRev (czmJWord i))).1 (czmX0_parts hp).1).1
  have hs : toModel (czmConjW (czmJWord i) p) = toModel p ∨
      toModel (czmConjW (czmJWord i) p) = toModel p * toModel czmZ0 :=
    (czmSame_iff hv (czmX0_parts hp).1).1 (hcheck i hi p hp)
  rw [← e, ← hxp, ← ruM2EquivModel_ruZ0, ← map_mul] at hs
  have hgx : czImg i * x * (czImg i)⁻¹ = ((g * ⟨x, hx2⟩ * g⁻¹ : ↥ruM2) : Pi7) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hg, czImg_eq hi]
  rw [hgx]
  rcases hs with hs | hs
  · rw [ruM2EquivModel.injective hs, mul_inv_cancel]
    exact one_mem _
  · rw [ruM2EquivModel.injective hs]
    change x * ruZ0 * x⁻¹ ∈ zpowers ruZ0
    rw [czX0_comm_ruZ0 hx, mul_inv_cancel_right]
    exact mem_zpowers _

end Checks

section Card

theorem card_czJ0_ge : 2048 ≤ Nat.card czJ0 := by
  obtain ⟨hfi, hidx0⟩ := czm_sub_index
  set H : Subgroup P12 :=
    Subgroup.closure (PresentedGroup.of '' {j : Fin sub9.length | j.val < 6}) with hH
  have hsubs : ∀ w ∈ (subsetOf sub9.length [0, 1, 2, 3, 4, 5]).map fun x => [(x, true)],
      PresentedGroup.mk _ (FreeGroup.mk w) ∈ H := by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hw
    have hx6 : x.val < 6 := by
      unfold subsetOf at hx
      have h2 := (List.mem_filter.1 hx).2
      simp only [List.contains_iff_mem, List.mem_cons, List.not_mem_nil, or_false] at h2
      omega
    exact Subgroup.subset_closure ⟨x, hx6, rfl⟩
  have hle : genSub {r | r ∈ p12Rels.map FreeGroup.mk} (subsetOf sub9.length [0, 1, 2, 3, 4, 5]) ≤
      H := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨x, hx, rfl⟩
    exact hsubs [(x, true)] (List.mem_map_of_mem hx)
  have hidx : H.index ≤ 24 :=
    (Nat.le_of_dvd (Nat.pos_of_ne_zero hfi.index_ne_zero) (Subgroup.index_dvd_of_le hle)).trans
      hidx0
  have hP : Nat.card P12 = 49152 := by rw [Nat.card_congr p12Equiv.toEquiv, card_ruM12]
  have hmul := H.card_mul_index
  rw [hP] at hmul
  have himg : (H.map p12Equiv.toMonoidHom).map ruM12.subtype = czJ0 := by
    rw [Subgroup.map_map, hH, MonoidHom.map_closure, czJ0, ← Set.image_comp]
    refine congrArg Subgroup.closure (Set.ext fun g => ?_)
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨j.val, hj, (p12Equiv_of j).symm⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, by rw [sub9_length]; simp only [Set.mem_ofPred_eq] at hi; omega⟩, hi,
        p12Equiv_of _⟩
  have hcard : Nat.card czJ0 = Nat.card H := by
    rw [← himg, Subgroup.card_map_of_injective ruM12.subtype_injective,
      Subgroup.card_map_of_injective (f := p12Equiv.toMonoidHom) p12Equiv.injective]
  rw [hcard]
  have h1 : Nat.card H * H.index ≤ Nat.card H * 24 := Nat.mul_le_mul_left _ hidx
  omega

theorem czK1_eq_czJ0 : czK1 = czJ0 := by
  have hfin : Finite Pi7 := card_pi7_le.1
  exact (Subgroup.eq_of_le_of_card_ge czJ0_le_czK1 (card_czK1_le.trans card_czJ0_ge)).symm

theorem card_czJ0 : Nat.card czJ0 = 2048 :=
  le_antisymm (czK1_eq_czJ0 ▸ card_czK1_le) card_czJ0_ge

theorem mem_czJ0_of_comm {g : Pi7} (hg : g ∈ ruM12)
    (h : ∀ x ∈ czX0, g * x * g⁻¹ * x⁻¹ ∈ zpowers ruZ0) : g ∈ czJ0 :=
  czK1_eq_czJ0 ▸ ⟨hg, h⟩

end Card

section Match

variable {G : Type} [Group G] {f : G} {A Q X R : Subgroup G}

theorem le_map_czJ0 (f₂ : ↥ruM2 ≃* ↥(normalizer (A : Set G)))
    (hz : ∀ m : ↥ruM2, (m : Pi7) = ruZ0 → ((f₂ m : ↥(normalizer (A : Set G))) : G) = f)
    (hA : ∀ m : ↥ruM2, (m : Pi7) ∈ ruA0 ↔ ((f₂ m : ↥(normalizer (A : Set G))) : G) ∈ A)
    (hR : R = pCoreOf 2 (normalizer (A : Set G))) (hQ : Nat.card Q = 2 ^ 11)
    (σ : ↥(centralizer ({f} : Set G)) →* Equiv.Perm (Fin 5))
    (hker : σ.ker = Q.subgroupOf (centralizer ({f} : Set G)))
    (hXQ : ∀ u ∈ Q, ∀ x ∈ X, u * x * u⁻¹ * x⁻¹ ∈ zpowers f)
    (hXu : ∀ Y : Subgroup G, A ≤ Y → Y ≤ R → Nat.card Y = 32 →
      centralizer ({f} : Set G) ⊓ normalizer (R : Set G) ≤ normalizer (Y : Set G) → Y = X) :
    ∀ g ∈ Q, ∃ m : ↥ruM2, (m : Pi7) ∈ czJ0 ∧ ((f₂ m : ↥(normalizer (A : Set G))) : G) = g :=
  le_map_of_model ruZ0_mem_ruM2 (letterSub_mono (by decide))
    (fun _ hm => mem_ruM12_iff_comm_ruZ0 hm) card_ruM12 ruA0_le_czX0 czX0_le_czR0 czR0_le_ruM2
    card_czX0 ruM12_le_normalizer_czX0 czR0_subgroupOf_eq_pCore
    (fun _ hm => mem_ruA0_iff_comm_czR0 hm) (fun _ hg h => mem_czJ0_of_comm hg h) f₂ hz hA hR
    hQ σ hker hXQ hXu

theorem map_czJ0_eq (f₂ : ↥ruM2 ≃* ↥(normalizer (A : Set G)))
    (hz : ∀ m : ↥ruM2, (m : Pi7) = ruZ0 → ((f₂ m : ↥(normalizer (A : Set G))) : G) = f)
    (hA : ∀ m : ↥ruM2, (m : Pi7) ∈ ruA0 ↔ ((f₂ m : ↥(normalizer (A : Set G))) : G) ∈ A)
    (hR : R = pCoreOf 2 (normalizer (A : Set G))) (hQ : Nat.card Q = 2 ^ 11)
    (σ : ↥(centralizer ({f} : Set G)) →* Equiv.Perm (Fin 5))
    (hker : σ.ker = Q.subgroupOf (centralizer ({f} : Set G)))
    (hXQ : ∀ u ∈ Q, ∀ x ∈ X, u * x * u⁻¹ * x⁻¹ ∈ zpowers f)
    (hXu : ∀ Y : Subgroup G, A ≤ Y → Y ≤ R → Nat.card Y = 32 →
      centralizer ({f} : Set G) ⊓ normalizer (R : Set G) ≤ normalizer (Y : Set G) → Y = X) :
    ∀ g : G, g ∈ Q ↔
      ∃ m : ↥ruM2, (m : Pi7) ∈ czJ0 ∧ ((f₂ m : ↥(normalizer (A : Set G))) : G) = g := by
  have hle := le_map_czJ0 f₂ hz hA hR hQ σ hker hXQ hXu
  set F : ↥ruM2 →* G := (normalizer (A : Set G)).subtype.comp f₂.toMonoidHom with hF
  have hFinj : Function.Injective F := Subtype.val_injective.comp f₂.injective
  have hQY : Q ≤ (czJ0.subgroupOf ruM2).map F := fun g hg => by
    obtain ⟨m, hm, hmg⟩ := hle g hg
    exact ⟨m, hm, hmg⟩
  have hY : Nat.card ((czJ0.subgroupOf ruM2).map F) = 2048 := by
    rw [Subgroup.card_map_of_injective hFinj,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe czJ0_le_ruM2).toEquiv, card_czJ0]
  have hfinY : Finite ((czJ0.subgroupOf ruM2).map F) :=
    Nat.finite_of_card_ne_zero (by rw [hY]; norm_num)
  have heq := Subgroup.eq_of_le_of_card_ge hQY (by rw [hY, hQ]; norm_num)
  intro g
  rw [heq]
  exact ⟨fun ⟨m, hm, hmg⟩ => ⟨m, hm, hmg⟩, fun ⟨m, hm, hmg⟩ => ⟨m, hm, hmg⟩⟩

end Match

end CFSG.ComponentClassification.GMS78.RuCz
