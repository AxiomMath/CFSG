module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Defs
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem isComponent_subgroupOf_of_le {L K H : Subgroup G} (hLK : L ≤ K) (hKH : K ≤ H)
    (h : IsComponent (L.subgroupOf H)) : IsComponent (L.subgroupOf K) := by
  refine ⟨?_, ?_⟩
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLK).symm
      (CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe (hLK.trans hKH)) h.1)
  · have := h.2.comap (Subgroup.inclusion hKH)
    convert this using 1
    ext x
    simp [Subgroup.mem_subgroupOf]

theorem IsComponentIn.le {K H : Subgroup G} (h : IsComponentIn K H) : K ≤ H :=
  h.1

theorem IsComponentIn.isQuasisimple {K H : Subgroup G} (h : IsComponentIn K H) :
    IsQuasisimple K :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe h.1) h.2.1

theorem IsComponentIn.ne_bot {K H : Subgroup G} (h : IsComponentIn K H) : K ≠ ⊥ := by
  intro hbot
  have hnt := CFSG.LocalCores.isQuasisimple_nontrivial h.isQuasisimple
  rw [hbot] at hnt
  exact (not_nontrivial_iff_subsingleton.mpr inferInstance) hnt

theorem isComponentIn_of_subnormal {K H : Subgroup G} (hKH : K ≤ H) (hq : IsQuasisimple K)
    (hs : (K.subgroupOf H).IsSubnormal) : IsComponentIn K H :=
  ⟨hKH, CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKH).symm hq, hs⟩

theorem isComponentIn_of_normal {K H : Subgroup G} (hKH : K ≤ H) (hq : IsQuasisimple K)
    (hn : (K.subgroupOf H).Normal) : IsComponentIn K H :=
  isComponentIn_of_subnormal hKH hq hn.isSubnormal

theorem IsComponentIn.not_le_centralizer {K H : Subgroup G} (h : IsComponentIn K H) :
    ¬ K ≤ centralizer (K : Set G) := by
  intro hle
  obtain ⟨-, -, a, b, hab⟩ := h.isQuasisimple
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  apply hab
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext (Subgroup.mem_centralizer_iff.1 (hle a.2) (b : G) b.2).symm

theorem IsComponentIn.mono {K H H' : Subgroup G} (h : IsComponentIn K H) (hK : K ≤ H')
    (hH : H' ≤ H) : IsComponentIn K H' :=
  ⟨hK, isComponent_subgroupOf_of_le hK hH h.2⟩

theorem IsComponentIn.map_conj {K H : Subgroup G} (h : IsComponentIn K H) {x : G} (hx : x ∈ H) :
    IsComponentIn (K.map (MulAut.conj x).toMonoidHom) H := by
  have hle : K.map (MulAut.conj x).toMonoidHom ≤ H := by
    rintro _ ⟨m, hm, rfl⟩
    exact H.mul_mem (H.mul_mem hx (h.1 hm)) (H.inv_mem hx)
  refine ⟨hle, ?_⟩
  have hc := CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj (⟨x, hx⟩ : ↥H)) h.2
  have heq : (K.map (MulAut.conj x).toMonoidHom).subgroupOf H =
      (K.subgroupOf H).map (MulAut.conj (⟨x, hx⟩ : ↥H)).toMonoidHom := by
    ext ⟨y, hy⟩
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · rintro ⟨m, hm, hmy⟩
      refine ⟨⟨m, h.1 hm⟩, hm, ?_⟩
      apply Subtype.ext
      simpa using hmy
    · rintro ⟨⟨m, hmX⟩, hm, hmy⟩
      refine ⟨m, hm, ?_⟩
      simpa using congrArg Subtype.val hmy
  rw [heq]
  exact hc

theorem IsComponentIn.map_mulEquiv {K H : Subgroup G} (h : IsComponentIn K H) (φ : G ≃* G) :
    IsComponentIn (K.map φ.toMonoidHom) (H.map φ.toMonoidHom) := by
  refine ⟨Subgroup.map_mono h.1, ?_⟩
  let e : ↥H ≃* ↥(H.map φ.toMonoidHom) := H.equivMapOfInjective φ.toMonoidHom φ.injective
  have hc := CFSG.LocalCores.isComponent_map_mulEquiv e h.2
  have heq : (K.subgroupOf H).map e.toMonoidHom =
      (K.map φ.toMonoidHom).subgroupOf (H.map φ.toMonoidHom) := by
    apply Subgroup.map_injective (Subgroup.subtype_injective (H.map φ.toMonoidHom))
    rw [Subgroup.map_map]
    have hcomp : ((H.map φ.toMonoidHom).subtype).comp e.toMonoidHom =
        φ.toMonoidHom.comp H.subtype := by
      ext m
      rfl
    rw [hcomp, ← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le h.1,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (Subgroup.map_mono h.1)]
  rw [heq] at hc
  exact hc

theorem IsComponentIn.conjugate {K H : Subgroup G} (h : IsComponentIn K H) {x : G} (hx : x ∈ H) :
    IsComponentIn (CFSG.conjugate K x) H := by
  unfold CFSG.conjugate
  exact h.map_conj (H.inv_mem hx)

theorem IsComponentIn.commute_of_ne [Finite G] {X Y H : Subgroup G} (hX : IsComponentIn X H)
    (hY : IsComponentIn Y H) (hne : X ≠ Y) : ∀ a ∈ X, ∀ b ∈ Y, a * b = b * a := by
  rcases CFSG.LocalCores.distinct_components_commute hX.2 hY.2 with h | h
  · exfalso
    apply hne
    have h1 := congrArg (Subgroup.map H.subtype) h
    rwa [Subgroup.map_subgroupOf_eq_of_le hX.1, Subgroup.map_subgroupOf_eq_of_le hY.1] at h1
  · intro a ha b hb
    have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.1 h
    have ha' : (⟨a, hX.1 ha⟩ : ↥H) ∈ X.subgroupOf H := ha
    have hb' : (⟨b, hY.1 hb⟩ : ↥H) ∈ Y.subgroupOf H := hb
    have := Subgroup.mem_centralizer_iff.1 (hle ha') _ hb'
    exact congrArg Subtype.val this.symm

theorem IsComponentIn.eq_of_le [Finite G] {X Y H : Subgroup G} (hX : IsComponentIn X H)
    (hY : IsComponentIn Y H) (hle : X ≤ Y) : X = Y := by
  by_contra hne
  apply hX.not_le_centralizer
  have hXY : X ≤ centralizer (Y : Set G) := by
    intro a ha
    exact Subgroup.mem_centralizer_iff.2 fun b hb =>
      (hX.commute_of_ne hY hne a ha b hb).symm
  exact hXY.trans (Subgroup.centralizer_le hle)

theorem conjugate_eq_self_of_le_centralizer {K : Subgroup G} {x : G}
    (h : K ≤ centralizer ({x} : Set G)) : CFSG.conjugate K x = K := by
  have hcomm : ∀ k ∈ K, x⁻¹ * k * x = k := by
    intro k hk
    have hkx : x * k = k * x := Subgroup.mem_centralizer_iff.1 (h hk) x (Set.mem_singleton x)
    calc x⁻¹ * k * x = x⁻¹ * (k * x) := by group
      _ = x⁻¹ * (x * k) := by rw [hkx.symm]
      _ = k := by group
  unfold CFSG.conjugate
  apply le_antisymm
  · rintro g ⟨k, hk, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [hcomm k hk]
    exact hk
  · intro g hg
    refine ⟨g, hg, ?_⟩
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using hcomm g hg

theorem conjugate_conjugate_of_orderOf_eq_two {K : Subgroup G} {x : G} (hx : orderOf x = 2) :
    CFSG.conjugate (CFSG.conjugate K x) x = K := by
  have hx2 : x * x = 1 := by
    have h := pow_orderOf_eq_one x
    rw [hx] at h
    simpa only [pow_two] using h
  have hthis : ∀ k : G, x⁻¹ * (x⁻¹ * k * x) * x = k := by
    intro k
    have h1 : x⁻¹ * (x⁻¹ * k * x) * x = (x * x)⁻¹ * k * (x * x) := by
      rw [mul_inv_rev]
      group
    rw [h1, hx2]
    group
  unfold CFSG.conjugate
  ext g
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  constructor
  · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    rw [hthis k]
    exact hk
  · intro hg
    refine ⟨_, ⟨g, hg, rfl⟩, ?_⟩
    rw [hthis g]

theorem commutator_zpowers_eq_bot_of_le_centralizer {K : Subgroup G} {x : G}
    (h : K ≤ centralizer ({x} : Set G)) : ⁅K, zpowers x⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.zpowers_eq_closure,
    Subgroup.centralizer_closure]
  exact h

theorem WalterChain.trans {X Y Z : Subgroup G} (h₁ : WalterChain X Y) (h₂ : WalterChain Y Z) :
    WalterChain X Z :=
  Relation.ReflTransGen.trans h₁ h₂

end CFSG.OddStandard.SmallF3.Omega
