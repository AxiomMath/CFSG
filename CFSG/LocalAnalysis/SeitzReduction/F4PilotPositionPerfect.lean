module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotZCentral
public import CFSG.LocalAnalysis.SeitzReduction.Inheritance
public import CFSG.LocalAnalysis.ComponentInitial.AlternatingOuterBound

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.ComponentInitial (outer_isomorphism)

section Quotient

variable {H : Type*} [Group H]

theorem injective_subgroupMap_mk'_of_inf_eq_bot (N : Subgroup H) [N.Normal] {P : Subgroup H}
    (hPN : P ⊓ N = ⊥) : Function.Injective ((QuotientGroup.mk' N).subgroupMap P) := by
  intro x y hxy
  have h1 : (QuotientGroup.mk' N) (x : H) = (QuotientGroup.mk' N) (y : H) :=
    congrArg Subtype.val hxy
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h1
  have h2 : (x : H)⁻¹ * y ∈ P ⊓ N := ⟨P.mul_mem (P.inv_mem x.2) y.2, h1⟩
  rw [hPN, mem_bot, inv_mul_eq_one] at h2
  exact Subtype.ext h2

@[expose] noncomputable def mapMkEquivOfInfEqBot (N : Subgroup H) [N.Normal] (P : Subgroup H)
    (hPN : P ⊓ N = ⊥) : P ≃* P.map (QuotientGroup.mk' N) :=
  MulEquiv.ofBijective ((QuotientGroup.mk' N).subgroupMap P)
    ⟨injective_subgroupMap_mk'_of_inf_eq_bot N hPN, (QuotientGroup.mk' N).subgroupMap_surjective P⟩

theorem coe_mapMkEquivOfInfEqBot_apply (N : Subgroup H) [N.Normal] (P : Subgroup H)
    (hPN : P ⊓ N = ⊥) (x : P) :
    ((mapMkEquivOfInfEqBot N P hPN x : P.map (QuotientGroup.mk' N)) : H ⧸ N) =
      QuotientGroup.mk' N (x : H) :=
  rfl

theorem card_map_mk'_of_inf_eq_bot (N : Subgroup H) [N.Normal] {P : Subgroup H}
    (hPN : P ⊓ N = ⊥) : Nat.card (P.map (QuotientGroup.mk' N)) = Nat.card P :=
  (Nat.card_congr (mapMkEquivOfInfEqBot N P hPN).toEquiv).symm

end Quotient

section Quasisimple

theorem isQuasisimple_open_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (hA : CFSG.Open.IsQuasisimple A) : CFSG.Open.IsQuasisimple B := by
  obtain ⟨hp, hs⟩ := hA
  have hc : (center A).map (e : A →* B) = center B := map_center_eq e
  refine ⟨?_, (QuotientGroup.congr _ _ e hc).symm.isSimpleGroup⟩
  rw [_root_.commutator_def] at hp ⊢
  rw [← map_top_of_surjective (e : A →* B) e.surjective, ← map_commutator, hp]

theorem center_eq_bot_congr {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (hA : center A = ⊥) : center B = ⊥ := by
  rw [← map_center_eq e, hA, Subgroup.map_bot]

theorem inf_oddCore_eq_bot {H : Type*} [Group H] [Finite H] {D : Subgroup H}
    (hDq : CFSG.Open.IsQuasisimple D) (hZD : center D = ⊥) : D ⊓ oddCore H = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have h : (⟨x, hx.1⟩ : D) ∈ center D :=
    oddCore_subgroupOf_le_center hDq (mem_subgroupOf.2 hx.2)
  rw [hZD, mem_bot] at h
  exact mem_bot.2 (congrArg Subtype.val h)

end Quasisimple

section LemmaA

variable {H : Type*} [Group H] [Finite H]

theorem not_normal_map_oddCore_of_perfect_le {t : H} (ht : orderOf t = 2) {D : Subgroup H}
    (hDq : CFSG.Open.IsQuasisimple D) (hZD : center D = ⊥) (hOut : Group.IsSolvable (Outer D))
    (hDt : D ≤ centralizer ({t} : Set H))
    (hsyl : ∀ U : Subgroup (H ⧸ oddCore H), IsPGroup 2 U →
      U ≤ centralizer (D.map (QuotientGroup.mk' (oddCore H)) : Set (H ⧸ oddCore H)) →
      Nat.card U ≤ 2)
    {y : H} (hyD : y ∈ D) (hy1 : y ≠ 1) {t' : H} (ht' : t' = y ∨ t' = t * y)
    {P : Subgroup H} (hP : ⁅P, P⁆ = P) (hPt' : P ≤ centralizer ({t'} : Set H))
    (hPO : P ⊓ oddCore H = ⊥) (hcard : Nat.card D ≤ Nat.card P) :
    ¬ (D.map (QuotientGroup.mk' (oddCore H))).Normal := by
  intro hnorm
  set π := QuotientGroup.mk' (oddCore H) with hπ
  have hDO : D ⊓ oddCore H = ⊥ := inf_oddCore_eq_bot hDq hZD
  set eD := mapMkEquivOfInfEqBot (oddCore H) D hDO with heD
  have htc := mk_mem_center_of_normal_map_oddCore hDt hsyl hnorm
  have hCD := centralizer_map_oddCore_eq_zpowers ht hDt hsyl hnorm
  have hPbar : P.map π ≤ D.map π := by
    have hOutbar : Group.IsSolvable (Outer (D.map π)) := (outer_isomorphism eD).2.1 hOut
    have hsolv : Group.IsSolvable (centralizer (D.map π : Set (H ⧸ oddCore H)) ⊓ ⊤ :
        Subgroup (H ⧸ oddCore H)) := by
      rw [inf_top_eq, hCD]
      infer_instance
    have hN : (⊤ : Subgroup (H ⧸ oddCore H)) ≤ normalizer (D.map π : Set (H ⧸ oddCore H)) := by
      rw [normalizer_eq_top_iff.2 hnorm]
    exact perfect_le_of_isSolvable_outer hOutbar le_top hN hsolv
      (by rw [← map_commutator, hP]) le_top
  have htc' : π t ∈ center (H ⧸ oddCore H) := htc
  have hPy : P.map π ≤ centralizer ({π y} : Set (H ⧸ oddCore H)) := by
    rintro _ ⟨p, hp, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have h := mem_centralizer_singleton_iff.1 (hPt' hp)
    rcases ht' with rfl | rfl
    · have h' := congrArg π h
      simpa only [map_mul] using h'
    · have h' := congrArg π h
      simp only [map_mul] at h'
      have hc : π p * π t = π t * π p := mem_center_iff.1 htc' (π p)
      have key : π t * (π p * π y) = π t * (π y * π p) := by
        calc π t * (π p * π y) = (π t * π p) * π y := by rw [mul_assoc]
          _ = (π p * π t) * π y := by rw [hc]
          _ = π p * (π t * π y) := by rw [mul_assoc]
          _ = π t * π y * π p := h'
          _ = π t * (π y * π p) := by rw [mul_assoc]
      exact mul_left_cancel key
  have hle : P.map π ≤ D.map π ⊓ centralizer ({π y} : Set (H ⧸ oddCore H)) := le_inf hPbar hPy
  have heq : D.map π ⊓ centralizer ({π y} : Set (H ⧸ oddCore H)) = D.map π := by
    refine eq_of_le_of_card_ge inf_le_left ?_
    calc Nat.card (D.map π) = Nat.card D := card_map_mk'_of_inf_eq_bot _ hDO
      _ ≤ Nat.card P := hcard
      _ = Nat.card (P.map π) := (card_map_mk'_of_inf_eq_bot _ hPO).symm
      _ ≤ _ := card_le_of_le hle
  have hZbar : center (D.map π) = ⊥ := center_eq_bot_congr eD hZD
  have hyc : (⟨π y, y, hyD, rfl⟩ : D.map π) ∈ center (D.map π) := by
    rw [mem_center_iff]
    intro d
    have hd : (d : H ⧸ oddCore H) ∈ centralizer ({π y} : Set (H ⧸ oddCore H)) :=
      (heq.ge d.2).2
    exact Subtype.ext (mem_centralizer_singleton_iff.1 hd)
  rw [hZbar, mem_bot] at hyc
  have h1 : eD ⟨y, hyD⟩ = 1 := Subtype.ext (congrArg Subtype.val hyc)
  rw [map_eq_one_iff eD eD.injective] at h1
  exact hy1 (congrArg Subtype.val h1)

theorem not_normal_map_oddCore_subgroupOf_of_mulEquiv {G : Type*} [Group G] [Finite G]
    {H : Subgroup G} {t : G} (htH : t ∈ H) (ht : orderOf t = 2) {D : Subgroup G} (hDH : D ≤ H)
    (hDq : CFSG.Open.IsQuasisimple D) (hZD : center D = ⊥) (hOut : Group.IsSolvable (Outer D))
    (hDt : D ≤ centralizer ({t} : Set G))
    (hsyl : ∀ U : Subgroup (H ⧸ oddCore H), IsPGroup 2 U →
      U ≤ centralizer ((D.subgroupOf H).map (QuotientGroup.mk' (oddCore H)) :
        Set (H ⧸ oddCore H)) → Nat.card U ≤ 2)
    {y : G} (hyD : y ∈ D) (hy1 : y ≠ 1) {t' : G} (ht' : t' = y ∨ t' = t * y)
    {P : Subgroup G} (hPH : P ≤ H) (hPt' : P ≤ centralizer ({t'} : Set G))
    (hPD : Nonempty (P ≃* D)) :
    ¬ ((D.subgroupOf H).map (QuotientGroup.mk' (oddCore H))).Normal := by
  obtain ⟨ePD⟩ := hPD
  have eD : D ≃* D.subgroupOf H := (subgroupOfEquivOfLe hDH).symm
  have eP : P ≃* P.subgroupOf H := (subgroupOfEquivOfLe hPH).symm
  have hDq' : CFSG.Open.IsQuasisimple (D.subgroupOf H) := isQuasisimple_open_of_mulEquiv eD hDq
  have hZD' : center (D.subgroupOf H) = ⊥ := center_eq_bot_congr eD hZD
  have hOut' : Group.IsSolvable (Outer (D.subgroupOf H)) := (outer_isomorphism eD).2.1 hOut
  have hPq : CFSG.Open.IsQuasisimple (P.subgroupOf H) :=
    isQuasisimple_open_of_mulEquiv (eD.symm.trans (ePD.symm.trans eP)) hDq'
  have hZP : center (P.subgroupOf H) = ⊥ :=
    center_eq_bot_congr (eD.symm.trans (ePD.symm.trans eP)) hZD'
  have hDt' : D.subgroupOf H ≤ centralizer ({⟨t, htH⟩} : Set H) := fun d hd =>
    mem_centralizer_singleton_iff.2 (Subtype.ext
      (mem_centralizer_singleton_iff.1 (hDt (mem_subgroupOf.1 hd))))
  have hyH : y ∈ H := hDH hyD
  have ht'H : t' ∈ H := by
    rcases ht' with rfl | rfl
    · exact hyH
    · exact H.mul_mem htH hyH
  have hPt'' : P.subgroupOf H ≤ centralizer ({⟨t', ht'H⟩} : Set H) := fun p hp =>
    mem_centralizer_singleton_iff.2 (Subtype.ext
      (mem_centralizer_singleton_iff.1 (hPt' (mem_subgroupOf.1 hp))))
  have hPperf : ⁅P.subgroupOf H, P.subgroupOf H⁆ = P.subgroupOf H := by
    have h := hPq.1
    have : Group.IsPerfect (P.subgroupOf H) := Group.isPerfect_def.2 h
    exact commutator_eq_self
  refine not_normal_map_oddCore_of_perfect_le (H := H) (t := ⟨t, htH⟩) ?_ hDq' hZD' hOut' hDt'
    hsyl (y := ⟨y, hyH⟩) (mem_subgroupOf.2 hyD) ?_ (t' := ⟨t', ht'H⟩) ?_ hPperf hPt''
    (inf_oddCore_eq_bot hPq hZP) ?_
  · rw [orderOf_mk, ht]
  · intro h
    exact hy1 (congrArg Subtype.val h)
  · rcases ht' with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  · rw [Nat.card_congr eD.symm.toEquiv, Nat.card_congr eP.symm.toEquiv,
      Nat.card_congr ePD.toEquiv]

theorem not_normal_map_oddCore_centralizer_of_mulEquiv {G : Type*} [Group G] [Finite G]
    {X : Subgroup G} {t : G} (htX : t ∈ centralizer (X : Set G)) (ht : orderOf t = 2)
    {D : Subgroup G} (hDX : D ≤ centralizer (X : Set G)) (hDq : CFSG.Open.IsQuasisimple D)
    (hZD : center D = ⊥) (hOut : Group.IsSolvable (Outer D))
    (hDt : D ≤ centralizer ({t} : Set G))
    (hsyl : ∀ U : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
      IsPGroup 2 U →
      U ≤ centralizer ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) :
        Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
      Nat.card U ≤ 2)
    {y : G} (hyD : y ∈ D) (hy1 : y ≠ 1) {t' : G} (ht' : t' = y ∨ t' = t * y)
    {P : Subgroup G} (hP : P ≤ centralizer (X : Set G) ⊓ centralizer ({t'} : Set G))
    (hPD : Nonempty (P ≃* D)) :
    ¬ ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal :=
  not_normal_map_oddCore_subgroupOf_of_mulEquiv htX ht hDX hDq hZD hOut hDt hsyl hyD hy1 ht'
    (hP.trans inf_le_left) (hP.trans inf_le_right) hPD

end LemmaA

end CFSG.SeitzReduction.F4Pilot
