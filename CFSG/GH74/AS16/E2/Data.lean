module

public import CFSG.GH74.AS16.E2.Bender
public import CFSG.GH74.AS16.E2.Leaves
public import CFSG.GH74.E2.TermBasic

public section

namespace CFSG.GH74.AS16.E2

open Subgroup CFSG CFSG.Blueprint
open CFSG.GH74.E2 hiding Hyp

theorem center_trivial {G : Type*} [Group G] {L : Subgroup G} (hZ : center ↥L = ⊥) :
    ∀ g ∈ L, g ∈ centralizer (L : Set G) → g = 1 := by
  intro g hg hgc
  have hmem : (⟨g, hg⟩ : ↥L) ∈ center ↥L :=
    Subgroup.mem_center_iff.2 fun k => Subtype.ext (Subgroup.mem_centralizer_iff.1 hgc k k.2)
  rw [hZ, Subgroup.mem_bot] at hmem
  exact congrArg Subtype.val hmem

theorem center_trivial' {G : Type*} [Group G] {L : Subgroup G} (hZ : center ↥L = ⊥) :
    ∀ l ∈ L, (∀ x ∈ L, l * x = x * l) → l = 1 := fun l hl hc =>
  center_trivial hZ l hl (Subgroup.mem_centralizer_iff.2 fun x hx => (hc x hx).symm)

section Cfg

variable {G : Type} [Group G] [Finite G] {T : Sylow 2 G} {z : G} {L : Subgroup G}

theorem Cfg.cen_le_normalizer (h : Cfg G T z L) : Cen z ≤ normalizer (L : Set G) := by
  intro g hg
  have hc := conjugate_eq_of_unique h.pair.isComp
    (fun K' hK' => (h.uniq z h.pair.orderOf_eq L K' h.pair.isComp hK').symm) hg
  exact (AS16.conjugate_eq_self_iff L g).1 hc

theorem Cfg.le_normalizer (h : Cfg G T z L) : (T : Subgroup G) ≤ normalizer (L : Set G) := by
  intro t ht
  apply h.cen_le_normalizer
  exact mem_Cen.2 (h.pair.central t ht).symm

theorem Cfg.isSylowOf_inf (h : Cfg G T z L) :
    CFSG.ABGLocalTools.IsSylowOf 2 ((T : Subgroup G) ⊓ L) L :=
  (CFSG.ABGLocalTools.IsSylowOf.of_le (isSylowOf_top T) h.le_normalizer le_top).inf_of_le_normalizer
    Subgroup.le_normalizer le_rfl

theorem Cfg.decomp (h : Cfg G T z L) (hZ : center ↥L = ⊥)
    (hout : ∀ (φ : MulAut ↥L) (n : ℕ), φ ^ 2 ^ n = 1 → ∃ k : ↥L, ∀ x : ↥L, φ x = k * x * k⁻¹) :
    ∀ t ∈ (T : Subgroup G), ∃ s ∈ (T : Subgroup G) ⊓ L,
      ∃ c ∈ (T : Subgroup G) ⊓ centralizer (L : Set G), t = s * c := by
  refine exists_decomp_of_inner T.isPGroup' (center_trivial' hZ) ?_ ?_
  · intro P hP hPL hle
    exact h.isSylowOf_inf.eq_of_le hle hPL hP
  · intro t ht
    have htN := h.le_normalizer ht
    obtain ⟨n, hn⟩ := T.isPGroup' ⟨t, ht⟩
    have hn' : t ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    have hφn : (L.normalizerMonoidHom ⟨t, htN⟩) ^ 2 ^ n = 1 := by
      rw [← map_pow]
      have : (⟨t, htN⟩ : normalizer (L : Set G)) ^ 2 ^ n = 1 :=
        Subtype.ext (by simpa using hn')
      rw [this, map_one]
    obtain ⟨k, hk⟩ := hout _ n hφn
    refine ⟨(k : G), k.2, fun x hx => ?_⟩
    have := congrArg Subtype.val (hk ⟨x, hx⟩)
    exact this

theorem Cfg.tC_cyclic (h : Cfg G T z L) (hZ : center ↥L = ⊥) {U : Subgroup ↥L}
    (hU : IsPGroup 2 U) (hr : 3 ≤ Group.rank U) :
    IsCyclic ↥((T : Subgroup G) ⊓ centralizer (L : Set G)) := by
  apply isCyclic_of_rank_le_one
  refine rank_le_one_of_gen4 h.hyp.gen4 (U := U.map L.subtype) (hU.map L.subtype)
    T.isPGroup'.to_inf_left ?_ ?_ ?_
  · rintro _ ⟨u, _, rfl⟩ c hc
    exact Subgroup.mem_centralizer_iff.1 hc.2 u u.2
  · rw [Subgroup.eq_bot_iff_forall]
    rintro g ⟨⟨u, _, rfl⟩, _, hgC⟩
    exact center_trivial hZ u u.2 hgC
  · have hrk : Group.rank ↥(U.map L.subtype) = Group.rank ↥U :=
      Group.rank_congr (Subgroup.equivMapOfInjective U L.subtype L.subtype_injective).symm
    omega

end Cfg

structure L28Data : Prop where
  out_inner : ∀ (K : Type) [Group K] [Finite K], ShapeL28 K → ∀ (φ : MulAut K) (n : ℕ),
    φ ^ 2 ^ n = 1 → ∃ k : K, ∀ x : K, φ x = k * x * k⁻¹
  sylow_comm : ∀ (K : Type) [Group K] [Finite K], ShapeL28 K → ∀ Q : Subgroup K, IsPGroup 2 Q →
    ¬ 2 ∣ Q.index → ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a

theorem noPairL28_of (hD3 : K0Data3) (hL : L28Data) : NoPairOf ShapeL28 := by
  intro G _ _ T z L hcfg _ hsh
  have hZ : center ↥L = ⊥ := hD3.center_bot ↥L (Or.inl hsh)
  obtain ⟨U, hU, hr⟩ := hD3.rank_ge3 ↥L (Or.inl hsh)
  have hdec := hcfg.decomp hZ (hL.out_inner ↥L hsh)
  have hcyc := hcfg.tC_cyclic hZ hU hr
  have hsyl := hcfg.isSylowOf_inf
  rw [CFSG.ABGLocalTools.isSylowOf_iff] at hsyl
  have hTL : ∀ a ∈ (T : Subgroup G) ⊓ L, ∀ b ∈ (T : Subgroup G) ⊓ L, a * b = b * a := by
    intro a ha b hb
    have := hL.sylow_comm ↥L hsh (((T : Subgroup G) ⊓ L).subgroupOf L) hsyl.2.1.comap_subtype
      hsyl.2.2 ⟨a, ha.2⟩ ha ⟨b, hb.2⟩ hb
    exact congrArg Subtype.val this
  apply hcfg.hyp.sylow_nonabelian T
  refine IsMulCommutative.of_comm fun a b => Subtype.ext ?_
  obtain ⟨s, hs, c, hc, hac⟩ := hdec a a.2
  obtain ⟨s', hs', c', hc', hbc⟩ := hdec b b.2
  have e1 : Commute s s' := hTL s hs s' hs'
  have e2 : Commute s c' := Subgroup.mem_centralizer_iff.1 hc'.2 s hs.2
  have e3 : Commute c s' := (Subgroup.mem_centralizer_iff.1 hc.2 s' hs'.2).symm
  have e4 : Commute c c' :=
    congrArg Subtype.val (cyclic_mul_comm (X := ↥((T : Subgroup G) ⊓ centralizer (L : Set G)))
      ⟨c, hc⟩ ⟨c', hc'⟩)
  show (a : G) * b = b * a
  rw [hac, hbc]
  exact (Commute.mul_left (Commute.mul_right e1 e2) (Commute.mul_right e3 e4)).eq

structure SzData : Prop where
  out_inner : ∀ (K : Type) [Group K] [Finite K], ShapeSz8 K → ∀ (φ : MulAut K) (n : ℕ),
    φ ^ 2 ^ n = 1 → ∃ k : K, ∀ x : K, φ x = k * x * k⁻¹
  sylow : ∀ (K : Type) [Group K] [Finite K], ShapeSz8 K → ∀ Q : Subgroup K, IsPGroup 2 Q →
    ¬ 2 ∣ Q.index → BenderTable (⊤ : Subgroup K) Q

theorem noPairSz8_of (hD3 : K0Data3) (hS : SzData) : NoPairOf ShapeSz8 := by
  intro G _ _ T z L hcfg _ hsh
  have hZ : center ↥L = ⊥ :=
    hD3.center_bot ↥L (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hsh))))))))
  obtain ⟨U, hU, hr⟩ := hD3.rank_ge3_sz ↥L (Or.inl hsh)
  have hdec := hcfg.decomp hZ (hS.out_inner ↥L hsh)
  have hcyc := hcfg.tC_cyclic hZ hU hr
  have hsyl := hcfg.isSylowOf_inf
  rw [CFSG.ABGLocalTools.isSylowOf_iff] at hsyl
  have hB : BenderTable L ((T : Subgroup G) ⊓ L) := by
    have h1 := (hS.sylow ↥L hsh (((T : Subgroup G) ⊓ L).subgroupOf L) hsyl.2.1.comap_subtype
      hsyl.2.2).of_subtype
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr inf_le_right] at h1
    exact h1
  exact false_of_bender hcfg.hyp.simple hcfg.hyp.nonabelian hcfg.pair.orderOf_eq
    hcfg.pair.mem_sylow hcfg.pair.central
    (fun l hl => Subgroup.mem_centralizer_singleton_iff.1 (hcfg.pair.isComp.1 hl))
    hdec (center_trivial hZ) hcyc hB

end CFSG.GH74.AS16.E2
