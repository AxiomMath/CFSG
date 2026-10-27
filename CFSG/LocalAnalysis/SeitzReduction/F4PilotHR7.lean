module

public import CFSG.LocalAnalysis.SeitzReduction.Inheritance
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotAutD
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotLeviSp6
import CFSG.GroupTheory.LocalCores.Layer
import CFSG.RankThree.PartOne.KF.LayerGen

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section Automizer

variable {G : Type*} [Group G]

theorem card_le_two_of_forall_fix_eq_one [Finite G] {L : Subgroup G} {t : G}
    (hCtN : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) (ht : orderOf t = 2)
    {X D : Subgroup G}
    (hAut : ∀ β : MulAut L, (∀ a : L, (a : G) ∈ X → β a = a) → (∀ a : L, (a : G) ∈ D → β a = a) →
      ∀ n : ℕ, β ^ 2 ^ n = 1 → β = 1)
    {U : Subgroup G} (hU : IsPGroup 2 U)
    (hUC : U ≤ centralizer (X : Set G) ⊓ centralizer ({t} : Set G) ⊓ centralizer (D : Set G)) :
    Nat.card U ≤ 2 := by
  have hUL : U ≤ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := by
    intro u hu
    obtain ⟨⟨huX, hut⟩, huD⟩ := hUC hu
    have huN : u ∈ normalizer (L : Set G) := hCtN hut
    obtain ⟨n, hn⟩ := hU ⟨u, hu⟩
    have hun : u ^ 2 ^ n = 1 := by
      have := congrArg Subtype.val hn
      simpa using this
    set β := L.normalizerMonoidHom ⟨u, huN⟩ with hβ
    have hβapp : ∀ a : L, ((β a : L) : G) = u * a * u⁻¹ := fun a => by
      simp [hβ, normalizerMonoidHom_apply_apply_coe]
    have hβX : ∀ a : L, (a : G) ∈ X → β a = a := fun a ha => by
      apply Subtype.ext
      rw [hβapp, ← mem_centralizer_iff.1 huX _ ha, mul_inv_cancel_right]
    have hβD : ∀ a : L, (a : G) ∈ D → β a = a := fun a ha => by
      apply Subtype.ext
      rw [hβapp, ← mem_centralizer_iff.1 huD _ ha, mul_inv_cancel_right]
    have hβn : β ^ 2 ^ n = 1 := by
      rw [hβ, ← map_pow]
      have : (⟨u, huN⟩ : normalizer (L : Set G)) ^ 2 ^ n = 1 := Subtype.ext (by simpa using hun)
      rw [this, map_one]
    have h1 := hAut β hβX hβD n hβn
    refine ⟨mem_centralizer_iff.2 fun l hl => ?_, hut⟩
    have h2 := congrArg (fun γ : MulAut L => ((γ ⟨l, hl⟩ : L) : G)) h1
    simp only [hβapp, MulAut.one_apply] at h2
    calc l * u = u * l * u⁻¹ * u := by rw [h2]
      _ = u * l := by group
  rw [hK] at hUL
  calc Nat.card U ≤ Nat.card (zpowers t) := card_le_of_le hUL
    _ = 2 := by rw [Nat.card_zpowers, ht]

theorem standard_inheritance_of_forall_fix_eq_one [Finite G] {L : Subgroup G}
    (hL : standardComponentIsStandard L) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {X : Subgroup G} (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hD : D = inSubgroup layer (L ⊓ centralizer (X : Set G)))
    (hDq : CFSG.Open.IsQuasisimple D)
    (hAut : ∀ β : MulAut L, (∀ a : L, (a : G) ∈ X → β a = a) → (∀ a : L, (a : G) ∈ D → β a = a) →
      ∀ n : ℕ, β ^ 2 ^ n = 1 → β = 1) :
    CFSG.Open.IsComponentOf
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))))
        (centralizer ({QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩} :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))))) ∧
      (∀ U : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
        IsPGroup 2 U →
        U ≤ centralizer ((D.subgroupOf (centralizer (X : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
        Nat.card U ≤ 2) ∧
      standardComponentIsStandard ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) :=
  standard_inheritance hL htC ht htX hD hDq fun _ hU hUC =>
    card_le_two_of_forall_fix_eq_one
      (CFSG.EvenSmallLie.centralizer_le_normalizer_of_standard hL htC ht) hK ht hAut hU hUC

theorem eq_one_of_mem_sup_of_mem_centralizer {Y D : Subgroup G}
    (hYD : Y ≤ centralizer (D : Set G)) (hZ : center D = ⊥) (hY : Odd (Nat.card Y))
    {g : G} (hg : g ∈ Y ⊔ D) (hgD : g ∈ centralizer (D : Set G)) {n : ℕ} (hgn : g ^ 2 ^ n = 1) :
    g = 1 := by
  have hYN : Y ≤ normalizer (D : Set G) := hYD.trans (Subgroup.centralizer_le_normalizer _)
  have hg' : g ∈ ((Y ⊔ D : Subgroup G) : Set G) := hg
  rw [coe_mul_of_left_le_normalizer_right _ _ hYN] at hg'
  obtain ⟨y, hy, d, hd, rfl⟩ := Set.mem_mul.1 hg'
  have hdC : d ∈ centralizer (D : Set G) := by
    have := mul_mem (inv_mem (hYD hy)) hgD
    rwa [inv_mul_cancel_left] at this
  have hd1 : d = 1 := by
    have : (⟨d, hd⟩ : D) ∈ center D := by
      rw [mem_center_iff]
      intro z
      exact Subtype.ext (mem_centralizer_iff.1 hdC z z.2)
    rw [hZ, mem_bot] at this
    exact congrArg Subtype.val this
  subst hd1
  rw [mul_one] at hgn ⊢
  have h1 : orderOf y ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hgn
  have h2 : orderOf y ∣ Nat.card Y := by
    have := orderOf_dvd_natCard (⟨y, hy⟩ : Y)
    rwa [orderOf_mk] at this
  have h3 : Nat.Coprime (2 ^ n) (Nat.card Y) := Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hY)
  exact orderOf_eq_one_iff.1 ((h3.coprime_dvd_left h1).eq_one_of_dvd h2)

end Automizer

section Transport

variable {G C : Type*} [Group G] [Group C] {L : Subgroup G}

theorem map_subgroupOf_map_symm (e : L ≃* C) (A : Subgroup C) :
    (((A.map e.symm.toMonoidHom).map L.subtype).subgroupOf L).map e.toMonoidHom = A := by
  rw [subgroupOf, comap_map_eq_self_of_injective L.subtype_injective, map_map]
  ext x
  simp

theorem inf_centralizer_map_symm (e : L ≃* C) (A : Subgroup C) :
    L ⊓ centralizer (((A.map e.symm.toMonoidHom).map L.subtype : Subgroup G) : Set G) =
      ((centralizer (A : Set C)).map e.symm.toMonoidHom).map L.subtype := by
  ext g
  constructor
  · rintro ⟨hgL, hgc⟩
    refine ⟨e.symm (e ⟨g, hgL⟩), ⟨e ⟨g, hgL⟩, mem_centralizer_iff.2 fun a ha => ?_, rfl⟩, by simp⟩
    have h := mem_centralizer_iff.1 hgc ((e.symm a : L) : G) ⟨e.symm a, ⟨a, ha, rfl⟩, rfl⟩
    have h' : e.symm a * ⟨g, hgL⟩ = ⟨g, hgL⟩ * e.symm a := Subtype.ext h
    have := congrArg e h'
    simpa using this
  · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    refine ⟨(e.symm c).2, mem_centralizer_iff.2 ?_⟩
    rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    have h := mem_centralizer_iff.1 hc a ha
    simp only [MulEquiv.coe_toMonoidHom, coe_subtype]
    rw [← coe_mul, ← coe_mul, ← map_mul, ← map_mul, h]

omit [Group C] in
theorem le_centralizer_self_of_isCyclic {Y : Subgroup G} (hY : IsCyclic Y) :
    Y ≤ centralizer (Y : Set G) := by
  intro a ha
  rw [mem_centralizer_iff]
  intro b hb
  let := IsCyclic.commGroup (α := Y)
  exact congrArg Subtype.val (mul_comm (⟨b, hb⟩ : Y) ⟨a, ha⟩)

theorem map_le_centralizer_map (φ : C →* G) {Y D : Subgroup C}
    (h : Y ≤ centralizer (D : Set C)) : Y.map φ ≤ centralizer (D.map φ : Set G) := by
  rintro _ ⟨y, hy, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨d, hd, rfl⟩
  rw [← map_mul, ← map_mul, mem_centralizer_iff.1 (h hy) d hd]

omit [Group C] in
theorem inSubgroup_layer_eq_self {D : Subgroup G} (hD : CFSG.IsQuasisimple D) :
    inSubgroup layer D = D := by
  have htop : layer D = ⊤ := by
    refine eq_top_iff.2 (CFSG.LocalCores.component_le_layer ⟨?_, IsSubnormal.top⟩)
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hD
  rw [inSubgroup, htop, ← MonoidHom.range_eq_map, range_subtype]

omit [Group C] in
theorem inSubgroup_layer_sup_eq {Y D : Subgroup G}
    (hYD : Y ≤ centralizer (D : Set G)) (hY : Y ≤ centralizer (Y : Set G))
    (hD : CFSG.IsQuasisimple D) : inSubgroup layer (Y ⊔ D) = D := by
  have hDH : D ≤ Y ⊔ D := le_sup_right
  have hYN : Y ≤ normalizer (D : Set G) := hYD.trans (Subgroup.centralizer_le_normalizer _)
  have hHN : Y ⊔ D ≤ normalizer (D : Set G) := sup_le hYN le_normalizer
  have hnormal : (D.subgroupOf (Y ⊔ D)).Normal := ⟨fun n hn g => by
    rw [mem_subgroupOf] at hn ⊢
    simpa using (mem_normalizer_iff.1 (hHN g.2) n).1 hn⟩
  have hq : CFSG.IsQuasisimple (D.subgroupOf (Y ⊔ D)) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hDH).symm hD
  have hc : ∀ {y d : G}, y ∈ Y → d ∈ D → y * d = d * y := fun hy hd =>
    (mem_centralizer_iff.1 (hYD hy) _ hd).symm
  have hsolv : Group.IsSolvable ((Y ⊔ D : Subgroup G) ⧸ D.subgroupOf (Y ⊔ D)) := by
    refine Group.isSolvable_of_comm fun a b => ?_
    induction a using QuotientGroup.induction_on with
    | H a =>
      induction b using QuotientGroup.induction_on with
      | H b =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, mem_subgroupOf]
        have ha : (a : G) ∈ ((Y ⊔ D : Subgroup G) : Set G) := a.2
        have hb : (b : G) ∈ ((Y ⊔ D : Subgroup G) : Set G) := b.2
        rw [coe_mul_of_left_le_normalizer_right _ _ hYN] at ha hb
        obtain ⟨y₁, hy₁, d₁, hd₁, h₁⟩ := Set.mem_mul.1 ha
        obtain ⟨y₂, hy₂, d₂, hd₂, h₂⟩ := Set.mem_mul.1 hb
        have e1 : y₁ * d₁ * (y₂ * d₂) = y₁ * y₂ * (d₁ * d₂) :=
          calc y₁ * d₁ * (y₂ * d₂) = y₁ * (d₁ * y₂) * d₂ := by group
            _ = y₁ * (y₂ * d₁) * d₂ := by rw [← hc hy₂ hd₁]
            _ = y₁ * y₂ * (d₁ * d₂) := by group
        have e2 : y₂ * d₂ * (y₁ * d₁) = y₁ * y₂ * (d₂ * d₁) :=
          calc y₂ * d₂ * (y₁ * d₁) = y₂ * (d₂ * y₁) * d₁ := by group
            _ = y₂ * (y₁ * d₂) * d₁ := by rw [← hc hy₁ hd₂]
            _ = y₂ * y₁ * (d₂ * d₁) := by group
            _ = y₁ * y₂ * (d₂ * d₁) := by rw [mem_centralizer_iff.1 (hY hy₁) y₂ hy₂]
        have key : ((a : G) * b)⁻¹ * (b * a) = d₂⁻¹ * d₁⁻¹ * d₂ * d₁ := by
          rw [← h₁, ← h₂, e1, e2]
          group
        simp only [coe_mul, coe_inv]
        rw [key]
        exact mul_mem (mul_mem (mul_mem (inv_mem hd₂) (inv_mem hd₁)) hd₂) hd₁
  rw [inSubgroup, CFSG.RankThree.PartOne.KFU.layer_eq_of_normal hnormal hq hsolv,
    subgroupOf_map_subtype, inf_of_le_left hDH]

theorem inSubgroup_layer_inf_centralizer_map_symm (e : L ≃* C) {A Y D : Subgroup C}
    (hA : centralizer (A : Set C) = Y ⊔ D) (hYD : Y ≤ centralizer (D : Set C))
    (hY : Y ≤ centralizer (Y : Set C)) (hD : CFSG.IsQuasisimple D) :
    inSubgroup layer
        (L ⊓ centralizer (((A.map e.symm.toMonoidHom).map L.subtype : Subgroup G) : Set G)) =
      (D.map e.symm.toMonoidHom).map L.subtype := by
  rw [inf_centralizer_map_symm, hA, Subgroup.map_sup, Subgroup.map_sup]
  refine inSubgroup_layer_sup_eq (map_le_centralizer_map _ (map_le_centralizer_map _ hYD))
    (map_le_centralizer_map _ (map_le_centralizer_map _ hY)) ?_
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
    ((D.equivMapOfInjective e.symm.toMonoidHom e.symm.injective).trans
      ((D.map e.symm.toMonoidHom).equivMapOfInjective L.subtype L.subtype_injective)) hD

end Transport

section F4

variable {K : Type} [Field K]

section Roots


private theorem c3PerpRoots_eq_c3LeviRoots : c3PerpRoots = c3LeviRoots := by
  ext γ
  rw [mem_c3PerpRoots_iff, mem_c3LeviRoots]

private theorem mem_C3Levi_iff_mem_c3PerpLevi {x : adjointGroup .F4 K} :
    x ∈ C3Levi K ↔ (x : ModGL .F4 K) ∈ c3PerpLevi K := by
  rw [mem_C3Levi_iff, c3PerpLevi, c3PerpRoots_eq_c3LeviRoots]

end Roots


theorem eq_one_of_fix_C3Levi {f : ℕ} (hf : 1 ≤ f) [Finite K] [CharP K 2]
    (hK : Nat.card K = 2 ^ f) {X : Subgroup (adjointGroup .F4 K)}
    (h2 : ∀ g ∈ centralizer (X : Set (adjointGroup .F4 K)) ⊓
      centralizer (C3Levi K : Set (adjointGroup .F4 K)), ∀ n : ℕ, g ^ 2 ^ n = 1 → g = 1)
    (β : MulAut (adjointGroup .F4 K)) (hβX : ∀ x ∈ X, β x = x) (hβD : ∀ x ∈ C3Levi K, β x = x)
    (n : ℕ) (hβn : β ^ 2 ^ n = 1) : β = 1 := by
  obtain ⟨g, rfl, hgD⟩ := exists_eq_conj_of_fix_c3PerpLevi hf hK β
    (fun x hx => hβD x (mem_C3Levi_iff_mem_c3PerpLevi.2 hx))
  have hgX : g ∈ centralizer (X : Set _) := mem_centralizer_iff.2 fun x hx => by
    have := hβX x hx
    rw [MulAut.conj_apply] at this
    calc x * g = g * x * g⁻¹ * g := by rw [this]
      _ = g * x := by group
  have hgD' : g ∈ centralizer (C3Levi K : Set _) := mem_centralizer_iff.2 fun x hx =>
    (hgD x (mem_C3Levi_iff_mem_c3PerpLevi.1 hx)).symm
  have hgn : g ^ 2 ^ n = 1 := by
    have hc : MulAut.conj (g ^ 2 ^ n) = 1 := by rw [map_pow, hβn]
    have hz : g ^ 2 ^ n ∈ center (adjointGroup .F4 K) := by
      rw [mem_center_iff]
      intro y
      have := congrArg (fun γ : MulAut _ => γ y) hc
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc y * g ^ 2 ^ n = g ^ 2 ^ n * y * (g ^ 2 ^ n)⁻¹ * g ^ 2 ^ n := by rw [this]
        _ = g ^ 2 ^ n * y := by group
    rw [center_adjointGroup_eq_bot] at hz
    exact hz
  rw [h2 g ⟨hgX, hgD'⟩ n hgn, map_one]

theorem eq_one_of_mem_inf_of_le_sup [Finite K] [CharP K 2] {X Y : Subgroup (adjointGroup .F4 K)}
    (hXc : centralizer (X : Set (adjointGroup .F4 K)) ≤ Y ⊔ C3Levi K)
    (hYD : Y ≤ centralizer (C3Levi K : Set (adjointGroup .F4 K))) (hYodd : Odd (Nat.card Y)) :
    ∀ g ∈ centralizer (X : Set (adjointGroup .F4 K)) ⊓
      centralizer (C3Levi K : Set (adjointGroup .F4 K)), ∀ n : ℕ, g ^ 2 ^ n = 1 → g = 1 :=
  fun _ hg _ hgn => eq_one_of_mem_sup_of_mem_centralizer hYD center_C3Levi_eq_bot hYodd
    (hXc hg.1) hg.2 hgn

variable {G : Type*} [Group G] {L : Subgroup G}

theorem eq_one_of_fix_map_C3Levi {f : ℕ} (hf : 1 ≤ f) [Finite K] [CharP K 2]
    (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .F4 K) {X D : Subgroup G}
    (hDe : D = ((C3Levi K).map e.symm.toMonoidHom).map L.subtype)
    (h2 : ∀ g ∈ centralizer (((X.subgroupOf L).map e.toMonoidHom : Subgroup (adjointGroup .F4 K)) :
        Set (adjointGroup .F4 K)) ⊓ centralizer (C3Levi K : Set (adjointGroup .F4 K)),
      ∀ n : ℕ, g ^ 2 ^ n = 1 → g = 1)
    (β : MulAut L) (hβX : ∀ a : L, (a : G) ∈ X → β a = a) (hβD : ∀ a : L, (a : G) ∈ D → β a = a)
    (n : ℕ) (hβn : β ^ 2 ^ n = 1) : β = 1 := by
  have key : MulAut.congr e β = 1 := by
    refine eq_one_of_fix_C3Levi hf hK h2 _ (fun x hx => ?_) (fun x hx => ?_) n ?_
    · obtain ⟨a, ha, rfl⟩ := hx
      rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply]
      simp only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
      rw [hβX a (mem_subgroupOf.1 ha)]
    · rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply]
      have hmem : ((e.symm x : L) : G) ∈ D := by
        rw [hDe]
        exact ⟨e.symm x, ⟨x, hx, rfl⟩, rfl⟩
      rw [hβD _ hmem, MulEquiv.apply_symm_apply]
    · rw [← map_pow, hβn, map_one]
  have := congrArg (MulAut.congr e).symm key
  rwa [MulEquiv.symm_apply_apply, map_one] at this

theorem isQuasisimple_map_C3Levi [Finite K] [CharP K 2] (e : L ≃* adjointGroup .F4 K) :
    CFSG.IsQuasisimple (((C3Levi K).map e.symm.toMonoidHom).map L.subtype) :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (((C3Levi K).equivMapOfInjective e.symm.toMonoidHom e.symm.injective).trans
      (((C3Levi K).map e.symm.toMonoidHom).equivMapOfInjective L.subtype L.subtype_injective))
    (isQuasisimple_C3Levi (K := K))

theorem isQuasisimple_open_map_C3Levi [Finite K] [CharP K 2] (e : L ≃* adjointGroup .F4 K) :
    CFSG.Open.IsQuasisimple (((C3Levi K).map e.symm.toMonoidHom).map L.subtype) :=
  ⟨(isQuasisimple_map_C3Levi e).1.commutator_eq_top, (isQuasisimple_map_C3Levi e).2.1⟩

theorem neighbour_standard [Finite G] (hL : standardComponentIsStandard L) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {f : ℕ} (hKc : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .F4 K)
    {X : Subgroup G} (htX : t ∈ centralizer (X : Set G))
    {Y : Subgroup (adjointGroup .F4 K)}
    (hYD : Y ≤ centralizer (C3Levi K : Set (adjointGroup .F4 K))) (hYodd : Odd (Nat.card Y))
    (hXc : centralizer (((X.subgroupOf L).map e.toMonoidHom : Subgroup (adjointGroup .F4 K)) :
      Set (adjointGroup .F4 K)) ≤ Y ⊔ C3Levi K)
    {D : Subgroup G} (hDe : D = ((C3Levi K).map e.symm.toMonoidHom).map L.subtype)
    (hD : D = inSubgroup layer (L ⊓ centralizer (X : Set G))) :
    CFSG.Open.IsComponentOf
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))))
        (centralizer ({QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩} :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))))) ∧
      (∀ U : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
        IsPGroup 2 U →
        U ≤ centralizer ((D.subgroupOf (centralizer (X : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
        Nat.card U ≤ 2) ∧
      standardComponentIsStandard ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) := by
  have := finite_of_natCard_eq_two_pow hKc
  have := charP_two_of_natCard_eq_two_pow hKc
  have hf := one_le_of_natCard_eq_two_pow hKc
  have hDq : CFSG.Open.IsQuasisimple D := hDe ▸ isQuasisimple_open_map_C3Levi e
  exact standard_inheritance_of_forall_fix_eq_one hL htC ht hK htX hD hDq
    (eq_one_of_fix_map_C3Levi hf hKc e hDe (eq_one_of_mem_inf_of_le_sup hXc hYD hYodd))

theorem neighbour_standard_of_centralizer_eq [Finite G] (hL : standardComponentIsStandard L)
    {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {f : ℕ} (hKc : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .F4 K)
    {X : Subgroup G} (hXL : X ≤ L) (htX : t ∈ centralizer (X : Set G)) (hXodd : Odd (Nat.card X))
    (hXc : centralizer (((X.subgroupOf L).map e.toMonoidHom : Subgroup (adjointGroup .F4 K)) :
      Set (adjointGroup .F4 K)) = (X.subgroupOf L).map e.toMonoidHom ⊔ C3Levi K)
    {D : Subgroup G} (hDe : D = ((C3Levi K).map e.symm.toMonoidHom).map L.subtype)
    (hD : D = inSubgroup layer (L ⊓ centralizer (X : Set G))) :
    CFSG.Open.IsComponentOf
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))))
        (centralizer ({QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩} :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))))) ∧
      (∀ U : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
        IsPGroup 2 U →
        U ≤ centralizer ((D.subgroupOf (centralizer (X : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
        Nat.card U ≤ 2) ∧
      standardComponentIsStandard ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) := by
  refine neighbour_standard hL htC ht hK hKc e htX ?_ ?_ hXc.le hDe hD
  · rw [le_centralizer_iff, hXc]
    exact le_sup_right
  · rw [card_map_of_injective e.injective, Nat.card_congr (subgroupOfEquivOfLe hXL).toEquiv]
    exact hXodd

theorem neighbour_standard_of_centralizer_eq_sup [Finite G] (hL : standardComponentIsStandard L)
    {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {f : ℕ} (hKc : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .F4 K)
    {A Y : Subgroup (adjointGroup .F4 K)}
    (hA : centralizer (A : Set (adjointGroup .F4 K)) = Y ⊔ C3Levi K)
    (hYD : Y ≤ centralizer (C3Levi K : Set (adjointGroup .F4 K)))
    (hYc : Y ≤ centralizer (Y : Set (adjointGroup .F4 K))) (hYodd : Odd (Nat.card Y))
    {X : Subgroup G} (hX : X = (A.map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G))
    {D : Subgroup G} (hDe : D = ((C3Levi K).map e.symm.toMonoidHom).map L.subtype) :
    CFSG.Open.IsComponentOf
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))))
        (centralizer ({QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩} :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))))) ∧
      (∀ U : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
        IsPGroup 2 U →
        U ≤ centralizer ((D.subgroupOf (centralizer (X : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
        Nat.card U ≤ 2) ∧
      standardComponentIsStandard ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) := by
  have := finite_of_natCard_eq_two_pow hKc
  have := charP_two_of_natCard_eq_two_pow hKc
  refine neighbour_standard hL htC ht hK hKc e htX hYD hYodd ?_ hDe ?_
  · rw [hX, map_subgroupOf_map_symm, hA]
  · rw [hX, inSubgroup_layer_inf_centralizer_map_symm e hA hYD hYc isQuasisimple_C3Levi, hDe]

end F4

end CFSG.SeitzReduction.F4Pilot
