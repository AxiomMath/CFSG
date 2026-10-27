module

public import CFSG.LocalAnalysis.OddStandard.Seitz77PlaneAbs
public import CFSG.LocalAnalysis.OddStandard.Seitz77PlaneASide
public import CFSG.LocalAnalysis.ComponentClassification.AS81OstromWagner

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.Open CFSG.ABGLocalTools Equiv

structure IsRegularNormal {G : Type*} [Group G] (E : Subgroup G) (t : G) (X : Subgroup G) :
    Prop where
  le_normalizer : X ≤ normalizer (E : Set G)
  centralizer_le : centralizer (E : Set G) ≤ X
  normalizer_le : normalizer (E : Set G) ≤ normalizer (X : Set G)
  mul_self_mem : ∀ p ∈ X, p * p ∈ centralizer (E : Set G)
  commutator_mem : ∀ p ∈ X, ∀ q ∈ X, p * q * p⁻¹ * q⁻¹ ∈ centralizer (E : Set G)
  relIndex_eq : (X ⊓ centralizer (E : Set G)).relIndex X = 16
  exists_conj : ∀ x ∈ E, IsConj t x → ∃ p ∈ X, p * t * p⁻¹ = x

namespace Datum

theorem image_conjAct_eq {G : Type} [Group G] {A : Subgroup G} (d : Datum A) {W : Subgroup G}
    {n : G}
    (hn : n ∈ normalizer ((d.E W : Subgroup G) : Set G)) (L : Set G)
    (hL : ∀ z ∈ d.pts W, n * z * n⁻¹ ∈ L ↔ z ∈ L) :
    ((d.ptsAction W ⟨n, hn⟩ : Perm ↥(d.pts W)) : ↥(d.pts W) → ↥(d.pts W)) ''
      {x : ↥(d.pts W) | (x : G) ∈ L} = {x : ↥(d.pts W) | (x : G) ∈ L} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (hL x x.2).2 hx
  · intro hy
    refine ⟨(d.ptsAction W ⟨n, hn⟩).symm y, ?_, Equiv.apply_symm_apply _ _⟩
    have hyz : (((d.ptsAction W ⟨n, hn⟩).symm y : ↥(d.pts W)) : G) ∈ d.pts W :=
      Subtype.property _
    have e : n * (((d.ptsAction W ⟨n, hn⟩).symm y : ↥(d.pts W)) : G) * n⁻¹ = (y : G) := by
      exact congrArg Subtype.val (Equiv.apply_symm_apply (d.ptsAction W ⟨n, hn⟩) y)
    exact (hL _ hyz).1 (by rw [e]; exact hy)

end Datum

namespace Facts

section Plane

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {V₁ V₂ W : Subgroup G}

theorem goodLine (F : Facts A) (d : Datum A) (hR : Radicals d.V V₁ V₂) (hα : d.Alpha)
    (hW : W = V₁ ∨ W = V₂) (AS : ASide A d.V W) :
    GoodLine (d.ptsAction W).range {x : ↥(d.pts W) | (x : G) ∈ d.line₀ W}
      ⟨d.t, d.t_mem_pts W⟩ := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  ·
    exact (d.mem_line₀_iff F hR hα hW).2 ⟨1, one_mem _, (one_mul _).symm⟩
  ·
    have h1 : Subtype.val '' {x : ↥(d.pts W) | (x : G) ∈ d.line₀ W} = d.line₀ W := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨⟨x, hx.1⟩, hx, rfl⟩
    rw [← Set.ncard_image_of_injective _ Subtype.val_injective, h1]
    exact F.ncard_line₀ d hR hα hW
  ·
    intro p₁ p₂ q₁ q₂ hp hq
    refine exists_two_trans (o := ⟨d.t, d.t_mem_pts W⟩) (fun p => ?_) (fun p q hp hq => ?_) hp hq
    · obtain ⟨n, hn, hnp⟩ := F.exists_conj_t d hR hα hW AS p.2
      exact ⟨d.ptsAction W ⟨n, hn⟩, ⟨_, rfl⟩, Subtype.ext hnp⟩
    · obtain ⟨n, hn, hnt, hnp⟩ := F.exists_conj_fix d hR hα hW AS p.2 q.2
        (fun h => hp (Subtype.ext h)) (fun h => hq (Subtype.ext h))
      exact ⟨d.ptsAction W ⟨n, hn⟩, ⟨_, rfl⟩, Subtype.ext hnt, Subtype.ext hnp⟩
  ·
    rintro a ha
    obtain ⟨n, hn, hL, hna⟩ := F.exists_stab d hR hα hW AS ha
    exact ⟨d.ptsAction W ⟨n, hn⟩, ⟨_, rfl⟩, d.image_conjAct_eq hn _ hL, Subtype.ext hna⟩
  ·
    rintro δ ⟨⟨n, hn⟩, rfl⟩ hδo b hb hbo hδb
    have hnt : n * d.t * n⁻¹ = d.t := congrArg Subtype.val hδo
    have hbt : (b : G) ≠ d.t := fun h => hbo (Subtype.ext h)
    exact d.image_conjAct_eq hn _ fun z hz =>
      F.line₀_spread d hR hα hW AS hn hnt hb hbt hδb hz

theorem exists_regularNormal (F : Facts A) (d : Datum A)
    (hR : Radicals d.V V₁ V₂) (hα : d.Alpha) (hW : W = V₁ ∨ W = V₂) (AS : ASide A d.V W) :
    ∃ X : Subgroup G, IsRegularNormal (d.E W : Subgroup G) d.t X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := normalizer ((d.E W : Subgroup G) : Set G) with hNdef
  set ρ := d.ptsAction W with hρ
  obtain ⟨T, hTΓ, hΓT, hTe, hT16, hTt⟩ := (F.goodLine d hR hα hW AS).exists_translations
    CFSG.ComponentClassification.AS81.ostromWagnerAG24 (F.card_pts d hR hα hW)
  set X' : Subgroup ↥N := T.comap ρ with hX'
  have hker : ∀ n : ↥N, ρ n = 1 ↔ (n : G) ∈ centralizer ((d.E W : Subgroup G) : Set G) :=
    fun n => F.ptsAction_eq_one_iff d hR hα hW n
  have hX'n : ∀ m : ↥N, ∀ p ∈ X', m * p * m⁻¹ ∈ X' := by
    intro m p hp
    have hm : ρ m ∈ normalizer (T : Set (Perm ↥(d.pts W))) := hΓT ⟨m, rfl⟩
    show ρ (m * p * m⁻¹) ∈ T
    rw [map_mul, map_mul, map_inv]
    exact (mem_normalizer_iff.mp hm (ρ p)).mp hp
  set X := X'.map N.subtype with hX
  have hXN : X ≤ N := map_subtype_le _
  have hCN : centralizer ((d.E W : Subgroup G) : Set G) ≤ N := Subgroup.centralizer_le_normalizer _
  refine ⟨X, ⟨hXN, fun c hc => ⟨⟨c, hCN hc⟩, ?_, rfl⟩, fun n hn => ?_, ?_, ?_, ?_, ?_⟩⟩
  ·
    show ρ ⟨c, hCN hc⟩ ∈ T
    rw [(hker ⟨c, hCN hc⟩).2 hc]
    exact T.one_mem
  ·
    rw [mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨⟨n, hn⟩ * p * ⟨n, hn⟩⁻¹, hX'n _ p hp, rfl⟩
    · rintro ⟨p, hp, hpx⟩
      refine ⟨⟨n, hn⟩⁻¹ * p * ⟨n, hn⟩⁻¹⁻¹, hX'n _ p hp, ?_⟩
      have hpx' : (p : G) = n * x * n⁻¹ := hpx
      simp only [coe_subtype, coe_mul, coe_inv, inv_inv, hpx']
      group
  ·
    rintro _ ⟨p, hp, rfl⟩
    have hpT : ρ p ∈ T := hp
    have h1 : ρ (p * p) = 1 := by
      rw [map_mul, ← sq]
      exact hTe.2 _ hpT
    exact (hker (p * p)).1 h1
  ·
    rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
    have hpT : ρ p ∈ T := hp
    have hqT : ρ q ∈ T := hq
    have hcomm : ρ p * ρ q = ρ q * ρ p :=
      congrArg Subtype.val (hTe.1.is_comm.comm ⟨_, hpT⟩ ⟨_, hqT⟩)
    have h1 : ρ (p * q * p⁻¹ * q⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
      group
    exact (hker (p * q * p⁻¹ * q⁻¹)).1 h1
  ·
    set C' : Subgroup ↥N := (centralizer ((d.E W : Subgroup G) : Set G)).subgroupOf N with hC'
    set f := ρ.comp X'.subtype with hf
    have hfker : f.ker = C'.subgroupOf X' := by
      ext p
      rw [MonoidHom.mem_ker, mem_subgroupOf, hf, MonoidHom.comp_apply, coe_subtype]
      exact hker p
    have hrange : f.range = T := by
      rw [hf, MonoidHom.range_comp, range_subtype, hX', map_comap_eq, inf_eq_right.mpr hTΓ]
    have hidx : (C'.subgroupOf X').index = 16 := by
      rw [← hfker, index_ker, hrange, hT16]
    have hinf : X ⊓ centralizer ((d.E W : Subgroup G) : Set G) = (X' ⊓ C').map N.subtype := by
      rw [map_inf_eq _ _ _ N.subtype_injective, hC', subgroupOf_map_subtype,
        inf_eq_left.mpr hCN]
    rw [hinf, relIndex_map_map_of_injective _ _ N.subtype_injective, inf_relIndex_left]
    exact hidx
  ·
    intro x hxE hxc
    have hx : x ∈ d.pts W := ⟨hxE, hxc⟩
    obtain ⟨τ, hτ, hτx⟩ := hTt ⟨d.t, d.t_mem_pts W⟩ ⟨x, hx⟩
    obtain ⟨n, rfl⟩ := hTΓ hτ
    exact ⟨(n : G), ⟨n, hτ, rfl⟩, congrArg Subtype.val hτx⟩

end Plane

end Facts

end CFSG.OddStandard.Seitz77
