module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryAffinePerm
public import CFSG.LocalAnalysis.SeitzReduction.RankOneStageChain

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.LocalAnalysis

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace AffineModel

section Defs

variable {V : Type} [CommGroup V] (M : Subgroup (MulAut V))

abbrev D : Type := V ⋊[M.subtype] M

@[expose] def rootV : Subgroup (D M) := (SemidirectProduct.inl : V →* D M).range

@[expose] def rootR (t : V) : Subgroup (D M) := zpowers (SemidirectProduct.inl t)

@[expose] def rootU (U : Subgroup V) : Subgroup (D M) := U.map SemidirectProduct.inl

@[expose] def rootX (U : Subgroup V) (H : Subgroup (MulAut V))
    (hHU : ∀ h ∈ H, ∀ u ∈ U, h u ∈ U) : Subgroup (D M) where
  carrier := {g | g.left ∈ U ∧ (g.right : MulAut V) ∈ H}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨mul_mem ha (hHU _ ha' _ hb), mul_mem ha' hb'⟩
  one_mem' := ⟨one_mem U, one_mem H⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    exact ⟨hHU _ (inv_mem ha') _ (inv_mem ha), inv_mem ha'⟩

end Defs

section Basic

variable {V : Type} [CommGroup V] {M : Subgroup (MulAut V)}

open SemidirectProduct

theorem conj_inl (g : D M) (s : V) : g * inl s * g⁻¹ = inl ((g.right : MulAut V) s) := by
  ext
  · simp [SemidirectProduct.mul_left, SemidirectProduct.inv_left]
  · simp

theorem conj_left (g x : D M) :
    (g * x * g⁻¹).left = g.left * (g.right : MulAut V) x.left *
      (((g.right : MulAut V) * (x.right : MulAut V) * (g.right : MulAut V)⁻¹) g.left)⁻¹ := by
  simp only [SemidirectProduct.mul_left, SemidirectProduct.inv_left, SemidirectProduct.mul_right]
  simp only [map_mul, Subgroup.coe_subtype, MulAut.mul_apply, map_inv]

theorem conj_right (g x : D M) :
    ((g * x * g⁻¹).right : MulAut V) =
      (g.right : MulAut V) * (x.right : MulAut V) * (g.right : MulAut V)⁻¹ := by
  simp

theorem mem_rootV {g : D M} : g ∈ rootV M ↔ g.right = 1 := by
  rw [rootV, range_inl_eq_ker_rightHom, MonoidHom.mem_ker]
  rfl

instance rootV_normal : (rootV M).Normal := by
  rw [rootV, range_inl_eq_ker_rightHom]
  infer_instance

theorem inl_mem_rootV (s : V) : (inl s : D M) ∈ rootV M := ⟨s, rfl⟩

theorem rootR_eq_map (t : V) : rootR M t = (zpowers t).map inl := by
  rw [rootR, MonoidHom.map_zpowers]

theorem rootU_le_rootV (U : Subgroup V) : rootU M U ≤ rootV M := by
  rintro _ ⟨u, -, rfl⟩
  exact inl_mem_rootV u

theorem rootR_le_rootV (t : V) : rootR M t ≤ rootV M := by
  rw [rootR_eq_map]
  rintro _ ⟨s, -, rfl⟩
  exact inl_mem_rootV s

theorem sup_eq_rootV {U : Subgroup V} {t : V} (hUt : IsCompl U (zpowers t)) :
    rootU M U ⊔ rootR M t = rootV M := by
  rw [rootU, rootR_eq_map, ← Subgroup.map_sup, hUt.sup_eq_top, rootV, MonoidHom.range_eq_map]

theorem rootU_inf_rootR {U : Subgroup V} {t : V} (hUt : IsCompl U (zpowers t)) :
    rootU M U ⊓ rootR M t = ⊥ := by
  rw [rootU, rootR_eq_map, ← Subgroup.map_inf_eq _ _ _ inl_injective, hUt.inf_eq_bot,
    Subgroup.map_bot]

theorem rootU_normal {U : Subgroup V} (hMU : ∀ m ∈ M, ∀ u ∈ U, m u ∈ U) :
    (rootU M U).Normal where
  conj_mem := by
    rintro _ ⟨u, hu, rfl⟩ g
    rw [conj_inl]
    exact ⟨_, hMU _ g.right.2 u hu, rfl⟩

theorem eq_one_or_eq_of_mem_zpowers {G : Type*} [Group G] {t x : G} (ht : t ^ 2 = 1)
    (hx : x ∈ zpowers t) : x = 1 ∨ x = t := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
  have hk := Int.mul_ediv_add_emod k 2
  have h2 : t ^ (2 * (k / 2)) = 1 := by rw [zpow_mul, zpow_two, ← sq, ht, one_zpow]
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · left
    rw [← hk, h0, add_zero, h2]
  · right
    rw [← hk, h1, zpow_add, h2, one_mul, zpow_one]

theorem mem_centralizer_rootR {t : V} {g : D M} :
    g ∈ centralizer (rootR M t : Set (D M)) ↔ (g.right : MulAut V) t = t := by
  constructor
  · intro hg
    have h1 := mem_centralizer_iff.mp hg (inl t) (mem_zpowers _)
    have h2 : g * inl t * g⁻¹ = inl t := by rw [← h1, mul_inv_cancel_right]
    rw [conj_inl] at h2
    exact inl_injective h2
  · intro hg
    have hc : Commute (inl t : D M) g := by
      have h2 : g * inl t * g⁻¹ = inl t := by rw [conj_inl, hg]
      calc (inl t : D M) * g = g * inl t * g⁻¹ * g := by rw [h2]
        _ = g * inl t := by group
    rw [mem_centralizer_iff]
    intro r hr
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hr
    exact (hc.zpow_left k).eq

theorem mem_normalizer_rootR {t : V} (ht2 : t ^ 2 = 1) (ht : t ≠ 1) {g : D M} :
    g ∈ normalizer (rootR M t : Set (D M)) ↔ (g.right : MulAut V) t = t := by
  constructor
  · intro hg
    have h1 : g * inl t * g⁻¹ ∈ rootR M t := (mem_normalizer_iff.mp hg _).mp (mem_zpowers _)
    rw [conj_inl, rootR_eq_map, Subgroup.mem_map_iff_mem inl_injective] at h1
    rcases eq_one_or_eq_of_mem_zpowers ht2 h1 with h | h
    · exact absurd ((map_eq_one_iff _ (g.right : MulAut V).injective).mp h) ht
    · exact h
  · intro hg
    exact centralizer_le_normalizer _ (mem_centralizer_rootR.mpr hg)

theorem mem_centralizer_rootU {U : Subgroup V} {g : D M} :
    g ∈ centralizer (rootU M U : Set (D M)) ↔ ∀ u ∈ U, (g.right : MulAut V) u = u := by
  constructor
  · intro hg u hu
    have h1 := mem_centralizer_iff.mp hg (inl u) ⟨u, hu, rfl⟩
    have h2 : g * inl u * g⁻¹ = inl u := by rw [← h1, mul_inv_cancel_right]
    rw [conj_inl] at h2
    exact inl_injective h2
  · intro hg
    rw [mem_centralizer_iff]
    rintro _ ⟨u, hu, rfl⟩
    have h2 : g * inl u * g⁻¹ = inl u := by rw [conj_inl, hg u hu]
    calc (inl u : D M) * g = g * inl u * g⁻¹ * g := by rw [h2]
      _ = g * inl u := by group

theorem eq_one_of_fix {U : Subgroup V} {t : V} (hUt : IsCompl U (zpowers t)) {m : MulAut V}
    (hmt : m t = t) (hmU : ∀ u ∈ U, m u = u) : m = 1 := by
  ext v
  have hv : v ∈ U ⊔ zpowers t := by rw [hUt.sup_eq_top]; exact mem_top v
  obtain ⟨u, hu, z, hz, rfl⟩ := Subgroup.mem_sup.mp hv
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hz
  rw [MulAut.one_apply, map_mul, map_zpow, hmt, hmU u hu]

theorem normalizer_inf_centralizer {U : Subgroup V} {t : V} (hV : ∀ v : V, v ^ 2 = 1)
    (ht : t ≠ 1) (hUt : IsCompl U (zpowers t)) :
    normalizer (rootR M t : Set (D M)) ⊓ centralizer (rootU M U : Set (D M)) =
      rootU M U ⊔ rootR M t := by
  rw [sup_eq_rootV hUt]
  apply le_antisymm
  · intro g hg
    obtain ⟨hgN, hgC⟩ := mem_inf.mp hg
    rw [mem_normalizer_rootR (hV t) ht] at hgN
    rw [mem_centralizer_rootU] at hgC
    rw [mem_rootV]
    exact Subtype.ext (eq_one_of_fix hUt hgN hgC)
  · intro g hg
    have h1 : (g.right : MulAut V) = 1 := by rw [mem_rootV.mp hg]; rfl
    refine mem_inf.mpr ⟨(mem_normalizer_rootR (hV t) ht).mpr (by rw [h1]; rfl),
      mem_centralizer_rootU.mpr fun u _ => by rw [h1]; rfl⟩

end Basic

structure Hyp {V : Type} [CommGroup V] (M H : Subgroup (MulAut V)) (U : Subgroup V) (t : V)
    (n : ℕ) : Prop where
  sq : ∀ v : V, v ^ 2 = 1
  three_le : 3 ≤ n
  card_U : Nat.card U = 2 ^ n
  compl : IsCompl U (zpowers t)
  ne_one : t ≠ 1
  mem_U : ∀ m ∈ M, ∀ u ∈ U, m u ∈ U
  le : H ≤ M
  fix : ∀ h ∈ H, h t = t
  normal : ∀ m ∈ M, m t = t → ∀ h ∈ H, m * h * m⁻¹ ∈ H
  cyclic : IsCyclic H
  regular : ∀ u v : U, u ≠ 1 → v ≠ 1 → ∃! h : H, (h : MulAut V) u = v

section Stage

variable {V : Type} [CommGroup V] {M H : Subgroup (MulAut V)} {U : Subgroup V} {t : V} {n : ℕ}

open SemidirectProduct

instance instFiniteD [Finite V] : Finite (D M) := by
  have : Finite (MulAut V) :=
    Finite.of_injective (fun m : MulAut V => (m : V → V)) DFunLike.coe_injective
  exact Finite.of_equiv _ SemidirectProduct.equivProd.symm

namespace Hyp

variable (h : Hyp M H U t n)
include h

theorem mem_U_H : ∀ x ∈ H, ∀ u ∈ U, x u ∈ U := fun x hx => h.mem_U x (h.le hx)

theorem mul_inv_apply_mem {m : MulAut V} (hm : m ∈ M) (hmt : m t = t) (w : V) :
    w * (m w)⁻¹ ∈ U := by
  have hw : w ∈ U ⊔ zpowers t := by rw [h.compl.sup_eq_top]; exact mem_top w
  obtain ⟨u, hu, z, hz, rfl⟩ := Subgroup.mem_sup.mp hw
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hz
  rw [map_mul, map_zpow, hmt, mul_inv_rev,
    show u * t ^ k * ((t ^ k)⁻¹ * (m u)⁻¹) = u * (m u)⁻¹ by group]
  exact mul_mem hu (inv_mem (h.mem_U m hm u hu))

theorem rootX_le_centralizer : rootX M U H h.mem_U_H ≤ centralizer (rootR M t : Set (D M)) :=
  fun _ hx => mem_centralizer_rootR.mpr (h.fix _ hx.2)

theorem rootX_le_normalizer : rootX M U H h.mem_U_H ≤ normalizer (rootR M t : Set (D M)) :=
  le_trans h.rootX_le_centralizer (centralizer_le_normalizer _)

theorem conj_mem_rootX {g : D M} (hg : g ∈ normalizer (rootR M t : Set (D M))) {x : D M}
    (hx : x ∈ rootX M U H h.mem_U_H) : g * x * g⁻¹ ∈ rootX M U H h.mem_U_H := by
  have hgt := (mem_normalizer_rootR (h.sq t) h.ne_one).mp hg
  have hk : (g.right : MulAut V) * (x.right : MulAut V) * (g.right : MulAut V)⁻¹ ∈ H :=
    h.normal _ g.right.2 hgt _ hx.2
  refine ⟨?_, ?_⟩
  · rw [conj_left, mul_comm g.left, mul_assoc]
    exact mul_mem (h.mem_U _ g.right.2 _ hx.1)
      (h.mul_inv_apply_mem (h.le hk) (h.fix _ hk) g.left)
  · rw [conj_right]
    exact hk

theorem rootX_normal :
    ((rootX M U H h.mem_U_H).subgroupOf (normalizer (rootR M t : Set (D M)))).Normal := by
  rw [normal_subgroupOf_iff_le_normalizer h.rootX_le_normalizer]
  intro g hg
  rw [mem_normalizer_iff]
  intro x
  refine ⟨fun hx => h.conj_mem_rootX hg hx, fun hx => ?_⟩
  have h1 := h.conj_mem_rootX (inv_mem hg) hx
  rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at h1

theorem rootU_le_rootX : rootU M U ≤ rootX M U H h.mem_U_H := by
  rintro _ ⟨u, hu, rfl⟩
  exact ⟨hu, one_mem H⟩

theorem card_rootU : Nat.card (rootU M U) = 2 ^ n := by
  rw [rootU, Subgroup.card_map_of_injective inl_injective, h.card_U]

theorem exists_ne_one_U : ∃ u ∈ U, u ≠ 1 := by
  have h1 : 1 < Nat.card U := by
    rw [h.card_U]
    exact Nat.one_lt_two_pow (by have := h.three_le; omega)
  have : Finite U := Nat.finite_of_card_ne_zero (by omega)
  have : Nontrivial U := Finite.one_lt_card_iff_nontrivial.mp h1
  obtain ⟨⟨u, hu⟩, hu1⟩ := exists_ne (1 : U)
  exact ⟨u, hu, fun h1 => hu1 (Subtype.ext h1)⟩

theorem card_H : Nat.card H = 2 ^ n - 1 := by
  classical
  have : Finite U := Nat.finite_of_card_ne_zero (by rw [h.card_U]; positivity)
  obtain ⟨u₀, hu₀, hu₀1⟩ := h.exists_ne_one_U
  have hu₀' : (⟨u₀, hu₀⟩ : U) ≠ 1 := fun h1 => hu₀1 (congrArg Subtype.val h1)
  let f : H → {u : U // u ≠ 1} := fun k => ⟨⟨(k : MulAut V) u₀, h.mem_U_H _ k.2 _ hu₀⟩,
    fun h1 => hu₀1 ((map_eq_one_iff _ (k : MulAut V).injective).mp (congrArg Subtype.val h1))⟩
  have hf : Function.Bijective f := by
    refine ⟨fun k₁ k₂ hk => ?_, fun v => ?_⟩
    · have hk' : (k₁ : MulAut V) u₀ = (k₂ : MulAut V) u₀ :=
        congrArg (fun w : {u : U // u ≠ 1} => ((w : U) : V)) hk
      obtain ⟨k, -, hku⟩ := h.regular ⟨u₀, hu₀⟩ ⟨(k₂ : MulAut V) u₀, h.mem_U_H _ k₂.2 _ hu₀⟩
        hu₀' (f k₂).2
      exact (hku k₁ hk').trans (hku k₂ rfl).symm
    · obtain ⟨k, hk, -⟩ := h.regular ⟨u₀, hu₀⟩ v hu₀' v.2
      exact ⟨k, Subtype.ext (Subtype.ext hk)⟩
  rw [Nat.card_congr (Equiv.ofBijective f hf), ← h.card_U]
  have h2 := Nat.card_congr (Equiv.sumCompl (fun u : U => u = 1))
  rw [Nat.card_sum, Nat.card_unique] at h2
  have h3 : Nat.card {u : U // u ≠ 1} = Nat.card {u : U // ¬ u = 1} := rfl
  omega

theorem card_rootX : Nat.card (rootX M U H h.mem_U_H) = 2 ^ n * (2 ^ n - 1) := by
  let e : rootX M U H h.mem_U_H ≃ U × H :=
    { toFun g := (⟨g.1.left, g.2.1⟩, ⟨g.1.right, g.2.2⟩)
      invFun p := ⟨⟨p.1, ⟨p.2, h.le p.2.2⟩⟩, ⟨p.1.2, p.2.2⟩⟩
      left_inv g := rfl
      right_inv p := rfl }
  rw [Nat.card_congr e, Nat.card_prod, h.card_U, h.card_H]

theorem exists_sylow_rootU :
    ∃ T : Sylow 2 (rootX M U H h.mem_U_H),
      (T : Subgroup _) = (rootU M U).subgroupOf (rootX M U H h.mem_U_H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card ((rootU M U).subgroupOf (rootX M U H h.mem_U_H)) = 2 ^ n := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.rootU_le_rootX).toEquiv, h.card_rootU]
  have hp : IsPGroup 2 ((rootU M U).subgroupOf (rootX M U H h.mem_U_H)) :=
    IsPGroup.of_card hcard
  have hidx : ((rootU M U).subgroupOf (rootX M U H h.mem_U_H)).index = 2 ^ n - 1 := by
    have h1 := Subgroup.card_mul_index ((rootU M U).subgroupOf (rootX M U H h.mem_U_H))
    rw [hcard, h.card_rootX] at h1
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h1
  have hodd : ¬ 2 ∣ ((rootU M U).subgroupOf (rootX M U H h.mem_U_H)).index := by
    rw [hidx]
    have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by have := h.three_le; omega)
    have h3 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    omega
  exact ⟨hp.toSylow hodd, IsPGroup.toSylow_coe hp hodd⟩

@[expose] def rootH (M H : Subgroup (MulAut V)) : Subgroup (D M) :=
  (H.subgroupOf M).map (inr : M →* D M)

omit h in
theorem card_rootH (hHM : H ≤ M) : Nat.card (rootH M H) = Nat.card H := by
  rw [rootH, Subgroup.card_map_of_injective inr_injective,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHM).toEquiv]

theorem singer :
    IsCyclic (GMSNormalizerQuotient (rootX M U H h.mem_U_H) (rootU M U)) ∧
      Nat.card (GMSNormalizerQuotient (rootX M U H h.mem_U_H) (rootU M U)) = 2 ^ n - 1 ∧
      ∀ u v : rootU M U, u ≠ 1 → v ≠ 1 →
        ∃! c : GMSNormalizerQuotient (rootX M U H h.mem_U_H) (rootU M U),
          gmsQuotConjAct (rootX M U H h.mem_U_H) (rootU M U) c u = v := by
  have hUn := rootU_normal (M := M) h.mem_U
  have hcyc : IsCyclic (H.subgroupOf M) := by
    have := h.cyclic
    exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe h.le).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe h.le).symm.surjective
  have hHcyc : IsCyclic (rootH M H) :=
    isCyclic_of_surjective ((inr : M →* D M).subgroupMap (H.subgroupOf M))
      ((inr : M →* D M).subgroupMap_surjective _)
  have hHX : rootH M H ≤ rootX M U H h.mem_U_H := by
    rintro _ ⟨k, hk, rfl⟩
    exact ⟨one_mem U, (mem_subgroupOf.mp hk : (k : MulAut V) ∈ H)⟩
  have hN : rootX M U H h.mem_U_H ⊓ normalizer (rootU M U : Set (D M)) ≤
      rootU M U ⊔ rootH M H := by
    intro x hx
    have hxX := (mem_inf.mp hx).1
    rw [← inl_left_mul_inr_right x]
    exact mul_mem (mem_sup_left ⟨x.left, hxX.1, rfl⟩)
      (mem_sup_right ⟨x.right, mem_subgroupOf.mpr hxX.2, rfl⟩)
  have hreg : ∀ x ∈ rootU M U, x ≠ 1 → ∀ y ∈ rootU M U, y ≠ 1 →
      ∃! d : rootH M H, (d : D M) * x * (d : D M)⁻¹ = y := by
    rintro _ ⟨u, hu, rfl⟩ hu1 _ ⟨v, hv, rfl⟩ hv1
    have hu1' : (⟨u, hu⟩ : U) ≠ 1 := fun h1 => hu1 (by
      rw [show u = 1 from congrArg Subtype.val h1, map_one])
    have hv1' : (⟨v, hv⟩ : U) ≠ 1 := fun h1 => hv1 (by
      rw [show v = 1 from congrArg Subtype.val h1, map_one])
    obtain ⟨k, hk, hku⟩ := h.regular ⟨u, hu⟩ ⟨v, hv⟩ hu1' hv1'
    refine ⟨⟨inr ⟨k, h.le k.2⟩, ⟨k, h.le k.2⟩, mem_subgroupOf.mpr k.2, rfl⟩, ?_, ?_⟩
    · change inr _ * inl u * (inr _)⁻¹ = inl v
      rw [conj_inl]
      exact congrArg inl hk
    · rintro ⟨d, k', hk', rfl⟩ hd
      change inr k' * inl u * (inr k')⁻¹ = inl v at hd
      rw [conj_inl] at hd
      have h1 := hku ⟨k', mem_subgroupOf.mp hk'⟩ (inl_injective hd)
      apply Subtype.ext
      change inr k' = inr ⟨k, h.le k.2⟩
      congr 1
      exact Subtype.ext (congrArg (fun x : H => (x : MulAut V)) h1)
  have hU1 : ∃ x ∈ rootU M U, x ≠ 1 := by
    obtain ⟨u, hu, hu1⟩ := h.exists_ne_one_U
    exact ⟨inl u, ⟨u, hu, rfl⟩, fun h1 => hu1 (inl_injective (by rw [h1, map_one]))⟩
  obtain ⟨hc, hcard, hreg'⟩ := gmsNormalizerQuotient_of_regular_complement h.rootU_le_rootX
    (fun x hx y hy => by
      obtain ⟨u, -, rfl⟩ := hx
      obtain ⟨v, -, rfl⟩ := hy
      rw [← map_mul, ← map_mul, mul_comm])
    hHX (le_normalizer_of_normal) hN hHcyc hreg hU1
  exact ⟨hc, by rw [hcard, card_rootH h.le, h.card_H], hreg'⟩

end Hyp

theorem isElementaryAbelian_of_le_rootV (hV : ∀ v : V, v ^ 2 = 1) {A : Subgroup (D M)}
    (hA : A ≤ rootV M) : IsElementaryAbelian 2 A where
  is_comm := ⟨fun a b => by
    obtain ⟨v, hv⟩ := hA a.2
    obtain ⟨w, hw⟩ := hA b.2
    apply Subtype.ext
    change (a : D M) * b = b * a
    rw [← hv, ← hw, ← map_mul, ← map_mul, mul_comm]⟩
  exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a => by
    obtain ⟨v, hv⟩ := hA a.2
    apply Subtype.ext
    change (a : D M) ^ 2 = 1
    rw [← hv, ← map_pow, hV, map_one]

namespace Hyp

variable (h : Hyp M H U t n)
include h

theorem card_rootR : Nat.card (rootR M t) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [rootR, Nat.card_zpowers, orderOf_injective _ inl_injective]
  exact orderOf_eq_prime (h.sq t) h.ne_one

theorem exists_P [Finite V] : ∃ P : Subgroup (D M), P ≤ normalizer (rootR M t : Set (D M)) ∧
    (∃ T : Sylow 2 (normalizer (rootR M t : Set (D M))),
      (T : Subgroup _) = P.subgroupOf (normalizer (rootR M t : Set (D M)))) ∧ rootV M ≤ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := normalizer (rootR M t : Set (D M))
  have hVN : rootV M ≤ N := fun g hg => (mem_normalizer_rootR (h.sq t) h.ne_one).mpr (by
    rw [mem_rootV.mp hg]
    rfl)
  have hp : IsPGroup 2 ((rootV M).subgroupOf N) := by
    intro x
    refine ⟨1, ?_⟩
    obtain ⟨v, hv⟩ := mem_subgroupOf.mp x.2
    have h2 : ((x : N) : D M) ^ 2 = 1 := by rw [← hv, ← map_pow, h.sq, map_one]
    apply Subtype.ext
    apply Subtype.ext
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one, pow_one]
    exact h2
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  refine ⟨(Q : Subgroup N).map N.subtype, map_subtype_le _, ⟨Q, ?_⟩, fun g hg => ?_⟩
  · rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective N.subtype_injective]
  · exact ⟨⟨g, hVN hg⟩, hQ (mem_subgroupOf.mpr hg), rfl⟩

theorem smallRootStage [Finite V] : ∃ P : Subgroup (D M),
    SmallRootStage (rootR M t) (rootX M U H h.mem_U_H) (rootU M U) P n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hPN, hPsyl, hVP⟩ := h.exists_P
  have hR := h.card_rootR
  have hUn := rootU_normal (M := M) h.mem_U
  have hsup := sup_eq_rootV (M := M) h.compl
  have hNC := normalizer_inf_centralizer (M := M) (U := U) h.sq h.ne_one h.compl
  refine ⟨P, ⟨h.three_le, ⟨by rw [hR]; exact even_two, fun g hg => by
      rw [card_inf_conj_eq_one_of_card_eq_two hR hg]; exact odd_one⟩,
    ⟨isElementaryAbelian_of_le_rootV h.sq (rootR_le_rootV t), le_rfl, ?_⟩,
    ⟨h.rootX_le_normalizer, h.rootX_normal, h.rootX_le_centralizer⟩,
    ⟨isElementaryAbelian_of_le_rootV h.sq (rootU_le_rootV U), h.rootU_le_rootX,
      h.exists_sylow_rootU, h.card_rootU⟩,
    h.singer,
    ⟨hPN, hPsyl, le_trans (rootU_le_rootV U) hVP, le_trans (rootR_le_rootV t) hVP,
      le_normalizer_of_normal, rootU_inf_rootR h.compl, ?_, ?_⟩⟩, hR, hNC⟩
  ·
    have hp : IsPGroup 2 (⊤ : Subgroup (rootR M t)) :=
      IsPGroup.of_card (n := 1) (by rw [Subgroup.card_top, hR, pow_one])
    exact ⟨hp.toSylow (by rw [Subgroup.index_top]; norm_num),
      by rw [IsPGroup.toSylow_coe, Subgroup.subgroupOf_self]⟩
  ·
    apply le_antisymm
    · rw [← hNC]
      exact inf_le_inf_right _ hPN
    · rw [hsup]
      refine le_inf hVP fun g hg => mem_centralizer_iff.mpr ?_
      rintro _ ⟨u, -, rfl⟩
      obtain ⟨v, rfl⟩ := hg
      rw [← map_mul, ← map_mul, mul_comm]
  · rw [hsup]
    infer_instance

end Hyp

end Stage

section Delta

variable {V : Type} [CommGroup V] {M H : Subgroup (MulAut V)} {U : Subgroup V} {t : V} {n : ℕ}

open SemidirectProduct

abbrev Orbit (M : Subgroup (MulAut V)) (t : V) : Type := MulAction.orbit M t

abbrev orbitImage (M : Subgroup (MulAut V)) (t : V) : Subgroup (Equiv.Perm (Orbit M t)) :=
  (MulAction.toPermHom M (Orbit M t)).range

theorem map_zpowers_inl (g : D M) (s : V) :
    (zpowers (inl s : D M)).map (MulAut.conj g).toMonoidHom =
      zpowers (inl ((g.right : MulAut V) s)) := by
  rw [MonoidHom.map_zpowers]
  congr 1
  exact conj_inl g s

namespace Hyp

variable (h : Hyp M H U t n)
include h

theorem zpowers_mem {s : V} (hs : s ∈ MulAction.orbit M t) :
    zpowers (inl s : D M) ∈ gmsRootConjugates (rootU M U ⊔ rootR M t) (rootR M t) := by
  obtain ⟨m, rfl⟩ := hs
  refine ⟨(inr m)⁻¹, ?_, ?_⟩
  · rw [inv_inv, rootR, map_zpowers_inl]
    rfl
  · rw [sup_eq_rootV h.compl, zpowers_le]
    exact inl_mem_rootV _

theorem ne_one_of_mem_orbit {s : V} (hs : s ∈ MulAction.orbit M t) : s ≠ 1 := by
  obtain ⟨m, rfl⟩ := hs
  exact fun h1 => h.ne_one ((map_eq_one_iff _ (m : MulAut V).injective).mp h1)

@[expose] noncomputable def orbitEquiv :
    Orbit M t ≃ gmsRootConjugates (rootU M U ⊔ rootR M t) (rootR M t) :=
  Equiv.ofBijective (fun s => ⟨zpowers (inl (s : V)), h.zpowers_mem s.2⟩) ⟨fun s s' hss => by
    have hss' : zpowers (inl (s : V) : D M) = zpowers (inl (s' : V)) := congrArg Subtype.val hss
    have h1 : (inl (s : V) : D M) ∈ zpowers (inl (s' : V)) := by
      rw [← hss']
      exact mem_zpowers _
    rcases eq_one_or_eq_of_mem_zpowers (by rw [← map_pow, h.sq, map_one]) h1 with h2 | h2
    · exact absurd (inl_injective (h2.trans (map_one _).symm)) (h.ne_one_of_mem_orbit s.2)
    · exact Subtype.ext (inl_injective h2), fun Q => by
    obtain ⟨g, hg, -⟩ := Q.2
    refine ⟨⟨((g⁻¹).right : MulAut V) t, (g⁻¹).right, rfl⟩, Subtype.ext ?_⟩
    change zpowers _ = (Q : Subgroup (D M))
    rw [hg, rootR, map_zpowers_inl]⟩

theorem orbitEquiv_apply (s : Orbit M t) :
    (h.orbitEquiv s : Subgroup (D M)) = zpowers (inl (s : V)) :=
  rfl

theorem action_orbitEquiv
    (g : normalizer ((rootU M U ⊔ rootR M t : Subgroup (D M)) : Set (D M))) (s : Orbit M t) :
    gmsRootConjugateAction (rootU M U ⊔ rootR M t) (rootR M t) g (h.orbitEquiv s) =
      h.orbitEquiv ((g : D M).right • s) := by
  apply Subtype.ext
  change (zpowers (inl (s : V))).map (MulAut.conj (g : D M)).toMonoidHom = _
  rw [map_zpowers_inl, orbitEquiv_apply]
  rfl

theorem range_eq : (gmsRootConjugateAction (rootU M U ⊔ rootR M t) (rootR M t)).range =
    (orbitImage M t).map h.orbitEquiv.permCongrHom.toMonoidHom := by
  have key : ∀ g : normalizer ((rootU M U ⊔ rootR M t : Subgroup (D M)) : Set (D M)),
      gmsRootConjugateAction (rootU M U ⊔ rootR M t) (rootR M t) g =
        h.orbitEquiv.permCongrHom (MulAction.toPermHom M (Orbit M t) (g : D M).right) := by
    intro g
    ext Q : 1
    obtain ⟨s, rfl⟩ := h.orbitEquiv.surjective Q
    rw [action_orbitEquiv, permCongrHom_apply_apply, Equiv.symm_apply_apply]
    rfl
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    exact ⟨_, ⟨(g : D M).right, rfl⟩, (key g).symm⟩
  · rintro _ ⟨_, ⟨m, rfl⟩, rfl⟩
    have hm : (inr m : D M) ∈
        normalizer ((rootU M U ⊔ rootR M t : Subgroup (D M)) : Set (D M)) := by
      rw [sup_eq_rootV h.compl]
      exact le_normalizer_of_normal (mem_top _)
    exact ⟨⟨inr m, hm⟩, key ⟨inr m, hm⟩⟩

theorem ncard_eq : (gmsRootConjugates (rootU M U ⊔ rootR M t) (rootR M t)).ncard =
    Nat.card (Orbit M t) := by
  rw [← Nat.card_coe_set_eq, Nat.card_congr h.orbitEquiv.symm]

end Hyp

end Delta

section Regular

variable {V : Type} [CommGroup V] {M : Subgroup (MulAut V)} {t : V}

theorem hasRegularNormalSubgroup_of_card_le_two [Finite V] (h2 : Nat.card (Orbit M t) ≤ 2) :
    HasRegularNormalSubgroup (orbitImage M t) := by
  classical
  refine ⟨orbitImage M t, le_rfl, by rw [Subgroup.subgroupOf_self]; infer_instance,
    fun a b => ?_⟩
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq M a b
  refine ⟨⟨MulAction.toPermHom M (Orbit M t) m, m, rfl⟩, hm, ?_⟩
  rintro ⟨σ, hσ⟩ hσa
  apply Subtype.ext
  ext c : 1
  change σ c = (MulAction.toPermHom M (Orbit M t) m) c
  by_cases hc : c = a
  · rw [hc]
    exact hσa.trans hm.symm
  · have hcard : Nat.card {x : Orbit M t // x ≠ b} ≤ 1 := by
      have h3 := Nat.card_congr (Equiv.sumCompl (fun x : Orbit M t => x = b))
      rw [Nat.card_sum, Nat.card_unique] at h3
      have h4 : Nat.card {x : Orbit M t // x ≠ b} = Nat.card {x : Orbit M t // ¬ x = b} := rfl
      omega
    have : Subsingleton {x : Orbit M t // x ≠ b} :=
      Finite.card_le_one_iff_subsingleton.mp hcard
    have h1 : σ c ≠ b := fun h1 => hc (σ.injective (h1.trans hσa.symm))
    have h2 : (MulAction.toPermHom M (Orbit M t) m) c ≠ b := fun h2 =>
      hc ((MulAction.toPermHom M (Orbit M t) m).injective (h2.trans hm.symm))
    exact congrArg Subtype.val (Subsingleton.elim (⟨σ c, h1⟩ : {x // x ≠ b}) ⟨_, h2⟩)

theorem card_orbit_one [Finite V] : Nat.card (Orbit M (1 : V)) = 1 := by
  have : Subsingleton (Orbit M (1 : V)) := ⟨fun x y => by
    obtain ⟨_, m, rfl⟩ := x
    obtain ⟨_, m', rfl⟩ := y
    apply Subtype.ext
    change (m • (1 : V)) = m' • (1 : V)
    rw [smul_one, smul_one]⟩
  have : Nonempty (Orbit M (1 : V)) := ⟨⟨1, MulAction.mem_orbit_self 1⟩⟩
  exact Nat.card_unique

theorem regularNormal_or_projective_of_affineModel_of_input (hHKS : SmallRootRegularNormalInput)
    [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {U : Subgroup V} {n : ℕ} (hn : 3 ≤ n)
    (hU : Nat.card U = 2 ^ n) (hUt : IsCompl U (zpowers t)) {H : Subgroup (MulAut V)}
    (hMU : ∀ m ∈ M, ∀ u ∈ U, m u ∈ U) (hHM : H ≤ M) (hHt : ∀ h ∈ H, h t = t)
    (hHn : ∀ m ∈ M, m t = t → ∀ h ∈ H, m * h * m⁻¹ ∈ H) (hHc : IsCyclic H)
    (hHreg : ∀ u v : U, u ≠ 1 → v ≠ 1 → ∃! h : H, (h : MulAut V) u = v)
    (hcat : NonabelianSimpleNormalCatalog (orbitImage M t)) :
    HasRegularNormalSubgroup (orbitImage M t) ∨ (n = 3 ∧ IsProjectiveEight (orbitImage M t)) := by
  by_cases h2 : Nat.card (Orbit M t) ≤ 2
  · exact Or.inl (hasRegularNormalSubgroup_of_card_le_two h2)
  have ht : t ≠ 1 := by
    rintro rfl
    rw [card_orbit_one] at h2
    exact h2 (by norm_num)
  have h : Hyp M H U t n := ⟨hV, hn, hU, hUt, ht, hMU, hHM, hHt, hHn, hHc, hHreg⟩
  obtain ⟨P, hP⟩ := h.smallRootStage
  have h3 : 3 ≤ (gmsRootConjugates (rootU M U ⊔ rootR M t) (rootR M t)).ncard := by
    rw [h.ncard_eq]
    omega
  have hcat' : NonabelianSimpleNormalCatalog
      (gmsRootConjugateAction (rootU M U ⊔ rootR M t) (rootR M t)).range := by
    rw [h.range_eq]
    refine NonabelianSimpleNormalCatalog.of_map_permCongr h.orbitEquiv.symm ?_
    rwa [map_permCongrHom_symm_map]
  rcases hHKS (D M) (rootR M t) (rootX M U H h.mem_U_H) (rootU M U) P n hP h3 hcat' with
    hreg | ⟨hn3, hproj⟩
  · left
    rw [gmsHasRegularNormal_iff, h.range_eq] at hreg
    have h1 := hreg.map_permCongr h.orbitEquiv.symm
    rwa [map_permCongrHom_symm_map] at h1
  · right
    refine ⟨hn3, ?_⟩
    rw [gmsProjectiveEight_iff, h.range_eq] at hproj
    have h1 := hproj.map_permCongr h.orbitEquiv.symm
    rwa [map_permCongrHom_symm_map] at h1

end Regular

end AffineModel

end CFSG.SeitzReduction.RankOne
