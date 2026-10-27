module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneHypStar
public import CFSG.Sporadic.Schreier.TitsOuter
public import CFSG.Sporadic.Schreier.TitsAutD

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Sporadic.Schreier.Tits

structure TitsSetting (G : Type) [Group G] [Finite G] (L : Subgroup G) : Prop where
  std : CFSG.EvenSmallLie.StandardSetting G L
  center_eq_bot : center L = ⊥
  model : LieModel L .Tits 0 2 1

namespace TitsSetting

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem even_card_centralizer (h : TitsSetting G L) :
    Even (Nat.card (centralizer (L : Set G))) :=
  h.std.standard.2.1

theorem even_card (h : TitsSetting G L) : Even (Nat.card G) :=
  even_iff_two_dvd.2 ((even_iff_two_dvd.1 h.even_card_centralizer).trans
    (Subgroup.card_subgroup_dvd_card _))

theorem center_G_eq_bot (h : TitsSetting G L) : center G = ⊥ := by
  have := h.std.simple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G) with hc | hc
  · exact hc
  · exfalso
    obtain ⟨a, b, hab⟩ := h.std.nonab
    exact hab (mem_center_iff.1 (hc ▸ mem_top a : a ∈ center G) b).symm

theorem commutator_eq_top (h : TitsSetting G L) : commutator G = ⊤ := by
  have := h.std.simple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator G) with hc | hc
  · exfalso
    obtain ⟨a, b, hab⟩ := h.std.nonab
    rw [_root_.commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer] at hc
    exact hab (mem_centralizer_iff.1 (hc (mem_top b)) a (mem_top a))
  · exact hc

theorem inf_centralizer_eq_bot (h : TitsSetting G L) : L ⊓ centralizer (L : Set G) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxL, hxC⟩
  have hx : (⟨x, hxL⟩ : L) ∈ center L :=
    mem_center_iff.2 fun y => Subtype.ext (mem_centralizer_iff.1 hxC y y.2)
  rw [h.center_eq_bot, mem_bot] at hx
  exact mem_bot.2 (congrArg Subtype.val hx)

theorem exists_involution (h : TitsSetting G L) :
    ∃ t ∈ centralizer (L : Set G), orderOf t = 2 := by
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 2
    (even_iff_two_dvd.1 h.even_card_centralizer)
  exact ⟨u, u.2, by rwa [orderOf_coe]⟩

theorem reeTitsModel (h : TitsSetting G L) : ReeTitsModel L .Tits 2 1 := by
  rcases h.model with ⟨hcl, -⟩ | ⟨-, hce, -⟩ | ⟨-, -, hree⟩ | ⟨-, hsz, -⟩
  · exact absurd hcl (by decide)
  · exact absurd hce (by decide)
  · exact hree
  · exact absurd hsz (by decide)

@[expose] def quotientCenterEquiv (h : TitsSetting G L) : L ≃* L ⧸ center L :=
  QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq h.center_eq_bot.symm)

theorem hypothesisOneStar (h : TitsSetting G L) (θ : L ≃* titsD)
    (hI : CFSG.SeitzReduction.RankOne.HypothesisOneStar titsD) :
    CFSG.SeitzReduction.RankOne.HypothesisOneStar (L ⧸ center L) :=
  CFSG.SeitzReduction.RankOne.hypothesisOneStar_of_mulEquiv
    (θ.symm.trans h.quotientCenterEquiv) hI

end TitsSetting

structure Data (G : Type) [Group G] where
  L : Subgroup G
  t : G
  θ : L ≃* titsD
  ρ : centralizer ({t} : Set G) →* titsA

structure Data.Hyp {G : Type} [Group G] [Finite G] (d : Data G) : Prop where
  setting : TitsSetting G d.L
  t_mem : d.t ∈ centralizer (d.L : Set G)
  t_two : orderOf d.t = 2
  ρ_apply : ∀ (x : centralizer ({d.t} : Set G)) (l m : d.L), (m : G) = x * l * (x : G)⁻¹ →
    ((d.θ m : titsD) : Equiv.Perm (Fin 1755)) =
      (d.ρ x : Equiv.Perm (Fin 1755)) * (d.θ l : Equiv.Perm (Fin 1755)) *
        (d.ρ x : Equiv.Perm (Fin 1755))⁻¹

namespace Data

variable {G : Type} [Group G] [Finite G] {d : Data G}

omit [Finite G] in
theorem t_mem_centralizer (d : Data G) : d.t ∈ centralizer ({d.t} : Set G) :=
  mem_centralizer_singleton_iff.2 rfl

theorem Hyp.std (hd : d.Hyp) : CFSG.EvenSmallLie.StandardSetting G d.L := hd.setting.std

theorem Hyp.center_eq_bot (hd : d.Hyp) : center d.L = ⊥ := hd.setting.center_eq_bot

theorem Hyp.t_ne_one (hd : d.Hyp) : d.t ≠ 1 := fun h => by
  have h2 := hd.t_two
  rw [h, orderOf_one] at h2
  exact absurd h2 (by decide)

theorem Hyp.t_not_mem_center (hd : d.Hyp) : d.t ∉ center G := fun h => by
  rw [hd.setting.center_G_eq_bot, mem_bot] at h
  exact hd.t_ne_one h

theorem Hyp.t_not_mem (hd : d.Hyp) : d.t ∉ d.L := fun h => by
  have ht : d.t ∈ d.L ⊓ centralizer (d.L : Set G) := mem_inf.2 ⟨h, hd.t_mem⟩
  rw [hd.setting.inf_centralizer_eq_bot, mem_bot] at ht
  exact hd.t_ne_one ht

theorem Hyp.normality (hd : d.Hyp) :
    centralizer ({d.t} : Set G) ≤ normalizer (d.L : Set G) ∧
      d.L ≤ centralizer ({d.t} : Set G) ∧
      (d.L.subgroupOf (centralizer ({d.t} : Set G))).Normal ∧
      CFSG.Assembly.IsComponentOf d.L (centralizer ({d.t} : Set G)) ∧
      ((centralizer (d.L : Set G) ⊓ centralizer ({d.t} : Set G)).subgroupOf
        (centralizer ({d.t} : Set G))).Normal :=
  CFSG.LocalAnalysis.ComponentInitial.standard_involution_centralizer_normality
    hd.std.standard hd.t_mem hd.t_two

theorem Hyp.le_normalizer (hd : d.Hyp) :
    centralizer ({d.t} : Set G) ≤ normalizer (d.L : Set G) :=
  hd.normality.1

theorem Hyp.L_le (hd : d.Hyp) : d.L ≤ centralizer ({d.t} : Set G) := hd.normality.2.1

theorem Hyp.normal (hd : d.Hyp) : (d.L.subgroupOf (centralizer ({d.t} : Set G))).Normal :=
  hd.normality.2.2.1

theorem Hyp.conj_mem (hd : d.Hyp) (x : centralizer ({d.t} : Set G)) {l : G} (hl : l ∈ d.L) :
    (x : G) * l * (x : G)⁻¹ ∈ d.L :=
  (mem_normalizer_iff.1 (hd.le_normalizer x.2) l).1 hl

theorem Hyp.θ_conj (hd : d.Hyp) (x : centralizer ({d.t} : Set G)) (l : d.L) :
    ((d.θ ⟨(x : G) * l * (x : G)⁻¹, hd.conj_mem x l.2⟩ : titsD) : Equiv.Perm (Fin 1755)) =
      (d.ρ x : Equiv.Perm (Fin 1755)) * (d.θ l : Equiv.Perm (Fin 1755)) *
        (d.ρ x : Equiv.Perm (Fin 1755))⁻¹ :=
  hd.ρ_apply x l _ rfl

theorem Hyp.titsConj_ρ (hd : d.Hyp)
    (x : centralizer ({d.t} : Set G)) (l : d.L) :
    titsConj (d.ρ x) (d.θ l) = d.θ ⟨(x : G) * l * (x : G)⁻¹, hd.conj_mem x l.2⟩ :=
  Subtype.ext (by rw [coe_titsConj_apply, hd.θ_conj])

theorem Hyp.ρ_eq_θ
    (hd : d.Hyp) (l : d.L) :
    (d.ρ ⟨l, hd.L_le l.2⟩ : Equiv.Perm (Fin 1755)) = (d.θ l : Equiv.Perm (Fin 1755)) := by
  have h : d.ρ ⟨l, hd.L_le l.2⟩ = ⟨d.θ l, titsD_le_titsA (d.θ l).2⟩ := by
    apply titsConj_injective
    refine MulEquiv.ext fun e => ?_
    obtain ⟨m, rfl⟩ := d.θ.surjective e
    rw [hd.titsConj_ρ]
    apply Subtype.ext
    rw [coe_titsConj_apply]
    have hm : (⟨(l : G) * m * (l : G)⁻¹, hd.conj_mem ⟨l, hd.L_le l.2⟩ m.2⟩ : d.L) =
        l * m * l⁻¹ := rfl
    rw [hm, map_mul, map_mul, map_inv]
    rfl
  rw [h]

theorem Hyp.ρ_eq_one_iff
    (hd : d.Hyp) (x : centralizer ({d.t} : Set G)) :
    d.ρ x = 1 ↔ (x : G) ∈ centralizer (d.L : Set G) := by
  constructor
  · intro h1
    rw [mem_centralizer_iff]
    intro l hl
    have h2 := hd.θ_conj x ⟨l, hl⟩
    rw [h1, OneMemClass.coe_one, one_mul, inv_one, mul_one] at h2
    have h3 : (⟨(x : G) * l * (x : G)⁻¹, hd.conj_mem x hl⟩ : d.L) = ⟨l, hl⟩ :=
      d.θ.injective (Subtype.ext h2)
    have h4 : (x : G) * l * (x : G)⁻¹ = l := congrArg Subtype.val h3
    calc l * x = (x : G) * l * (x : G)⁻¹ * x := by rw [h4]
      _ = x * l := by group
  · intro hx
    apply titsConj_injective
    rw [map_one]
    refine MulEquiv.ext fun e => ?_
    obtain ⟨m, rfl⟩ := d.θ.surjective e
    rw [hd.titsConj_ρ, MulAut.one_apply]
    congr 1
    apply Subtype.ext
    change (x : G) * m * (x : G)⁻¹ = m
    rw [← mem_centralizer_iff.1 hx m m.2, mul_inv_cancel_right]

theorem Hyp.ker_ρ
    (hd : d.Hyp) :
    d.ρ.ker.map (centralizer ({d.t} : Set G)).subtype =
      centralizer (d.L : Set G) ⊓ centralizer ({d.t} : Set G) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨(hd.ρ_eq_one_iff y).1 hy, y.2⟩
  · rintro ⟨hxL, hxt⟩
    exact ⟨⟨x, hxt⟩, (hd.ρ_eq_one_iff ⟨x, hxt⟩).2 hxL, rfl⟩

theorem Hyp.ρ_t
    (hd : d.Hyp) : d.ρ ⟨d.t, d.t_mem_centralizer⟩ = 1 :=
  (hd.ρ_eq_one_iff _).2 hd.t_mem

theorem Hyp.card_centralizer
    (hd : d.Hyp) :
    Nat.card (centralizer ({d.t} : Set G)) =
      Nat.card (centralizer (d.L : Set G) ⊓ centralizer ({d.t} : Set G) : Subgroup G) *
        Nat.card d.ρ.range := by
  rw [← hd.ker_ρ, card_map_of_injective (subtype_injective _),
    ← Nat.card_congr (QuotientGroup.quotientKerEquivRange d.ρ).toEquiv, mul_comm]
  exact card_eq_card_quotient_mul_card_subgroup _

theorem Hyp.exists_sylow_kernel (hd : d.Hyp) :
    ∃ S : Sylow 2 (centralizer (d.L : Set G)), ⟨d.t, hd.t_mem⟩ ∈ S ∧
      IsCyclic (S : Subgroup (centralizer (d.L : Set G))) ∧
      (∀ x ∈ S, orderOf x = 2 → x = ⟨d.t, hd.t_mem⟩) ∧
      centralizer (d.L : Set G) ⊓ centralizer ({d.t} : Set G) =
        (S : Subgroup (centralizer (d.L : Set G))).map (centralizer (d.L : Set G)).subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set tC : centralizer (d.L : Set G) := ⟨d.t, hd.t_mem⟩ with htCdef
  have htC2 : orderOf tC = 2 := by rw [htCdef, orderOf_mk, hd.t_two]
  have hp : IsPGroup 2 (zpowers tC) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, htC2, pow_one])
  obtain ⟨S, hS⟩ := hp.exists_le_sylow
  have htS : tC ∈ (S : Subgroup (centralizer (d.L : Set G))) := hS (mem_zpowers tC)
  have hcyc := hd.std.isCyclic_sylow S
  obtain ⟨-, huniq, -, -, -, -, hCH, -, -⟩ :=
    CFSG.ComponentClassification.StandardRecognition.standard_cyclic_local_centralizer_kernel
      hd.std.standard S hcyc htS htC2 (hd.std.core d.t hd.t_two)
  exact ⟨S, htS, hcyc, huniq, hCH⟩

theorem Hyp.isCyclic_kernel (hd : d.Hyp) :
    IsCyclic (centralizer (d.L : Set G) ⊓ centralizer ({d.t} : Set G) : Subgroup G) ∧
      IsPGroup 2 (centralizer (d.L : Set G) ⊓ centralizer ({d.t} : Set G) : Subgroup G) := by
  obtain ⟨S, -, hcyc, -, hCH⟩ := hd.exists_sylow_kernel
  have e : (S : Subgroup (centralizer (d.L : Set G))) ≃*
      (centralizer (d.L : Set G) ⊓ centralizer ({d.t} : Set G) : Subgroup G) :=
    ((S : Subgroup (centralizer (d.L : Set G))).equivMapOfInjective _
      (subtype_injective _)).trans (MulEquiv.subgroupCongr hCH.symm)
  exact ⟨e.isCyclic.1 hcyc, S.isPGroup'.of_equiv e⟩

theorem Hyp.eq_t_of_mem_kernel (hd : d.Hyp) {x : G}
    (hx : x ∈ centralizer (d.L : Set G) ⊓ centralizer ({d.t} : Set G)) (hx2 : orderOf x = 2) :
    x = d.t := by
  obtain ⟨S, -, -, huniq, hCH⟩ := hd.exists_sylow_kernel
  rw [hCH] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact congrArg Subtype.val (huniq y hy (by rwa [← orderOf_coe]))

theorem Hyp.kernel_eq_zpowers (hd : d.Hyp)
    (hI : CFSG.SeitzReduction.RankOne.HypothesisOneStar titsD) :
    centralizer (d.L : Set G) ⊓ centralizer ({d.t} : Set G) = zpowers d.t :=
  CFSG.SeitzReduction.RankOne.inf_centralizer_eq_zpowers_of_standard_star hd.std
    hd.center_eq_bot (hd.setting.hypothesisOneStar d.θ hI) hd.t_mem hd.t_two

theorem Hyp.ker_ρ_eq_zpowers
    (hd : d.Hyp) (hI : CFSG.SeitzReduction.RankOne.HypothesisOneStar titsD) :
    d.ρ.ker.map (centralizer ({d.t} : Set G)).subtype = zpowers d.t := by
  rw [hd.ker_ρ, hd.kernel_eq_zpowers hI]

theorem Hyp.card_centralizer_eq_two_mul
    (hd : d.Hyp) (hI : CFSG.SeitzReduction.RankOne.HypothesisOneStar titsD) :
    Nat.card (centralizer ({d.t} : Set G)) = 2 * Nat.card d.ρ.range := by
  rw [hd.card_centralizer, hd.kernel_eq_zpowers hI, Nat.card_zpowers, hd.t_two]

theorem Hyp.map_L
    (hd : d.Hyp) :
    (d.L.subgroupOf (centralizer ({d.t} : Set G))).map d.ρ = titsD.subgroupOf titsA := by
  ext a
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : (x : G) ∈ d.L := hx
    rw [mem_subgroupOf, hd.ρ_eq_θ ⟨x, hx'⟩]
    exact (d.θ ⟨x, hx'⟩).2
  · intro ha
    rw [mem_subgroupOf] at ha
    refine ⟨⟨d.θ.symm ⟨a, ha⟩, hd.L_le (d.θ.symm ⟨a, ha⟩).2⟩,
      mem_subgroupOf.2 (d.θ.symm ⟨a, ha⟩).2, Subtype.ext ?_⟩
    rw [hd.ρ_eq_θ (d.θ.symm ⟨a, ha⟩), MulEquiv.apply_symm_apply]

theorem Hyp.titsD_le_range
    (hd : d.Hyp) : titsD.subgroupOf titsA ≤ d.ρ.range := by
  rw [← hd.map_L]
  exact map_le_range _ _

theorem Hyp.range_ρ
    (hd : d.Hyp) : d.ρ.range = titsD.subgroupOf titsA ∨ d.ρ.range = ⊤ := by
  have hle := hd.titsD_le_range
  have h := relIndex_mul_index hle
  rw [titsD_index] at h
  rcases (Nat.dvd_prime Nat.prime_two).1 (Dvd.intro_left _ h) with h1 | h2
  · exact Or.inr (index_eq_one.1 h1)
  · left
    rw [h2] at h
    exact le_antisymm (relIndex_eq_one.1 (by omega)) hle

theorem Hyp.ρ_mem_titsD_iff
    (hd : d.Hyp) (x : centralizer ({d.t} : Set G)) :
    (d.ρ x : Equiv.Perm (Fin 1755)) ∈ titsD ↔
      ∃ l ∈ d.L, l⁻¹ * (x : G) ∈ centralizer (d.L : Set G) := by
  constructor
  · intro hx
    refine ⟨d.θ.symm ⟨_, hx⟩, (d.θ.symm ⟨_, hx⟩).2, ?_⟩
    have hl : d.ρ ⟨d.θ.symm ⟨_, hx⟩, hd.L_le (d.θ.symm ⟨_, hx⟩).2⟩ = d.ρ x :=
      Subtype.ext (by rw [hd.ρ_eq_θ, MulEquiv.apply_symm_apply])
    have h1 : d.ρ ((⟨d.θ.symm ⟨_, hx⟩, hd.L_le (d.θ.symm ⟨_, hx⟩).2⟩ :
        centralizer ({d.t} : Set G))⁻¹ * x) = 1 := by
      rw [map_mul, map_inv, hl, inv_mul_cancel]
    exact (hd.ρ_eq_one_iff _).1 h1
  · rintro ⟨l, hl, hs⟩
    have h1 : d.ρ ((⟨l, hd.L_le hl⟩ : centralizer ({d.t} : Set G))⁻¹ * x) = 1 :=
      (hd.ρ_eq_one_iff _).2 hs
    rw [map_mul, map_inv, inv_mul_eq_one] at h1
    rw [← h1, hd.ρ_eq_θ ⟨l, hl⟩]
    exact (d.θ _).2

theorem Hyp.involution_mem
    (hd : d.Hyp) {x : G} (hx : x ∈ centralizer ({d.t} : Set G)) (hx2 : x ^ 2 = 1) :
    x ∈ d.L ∨ d.t * x ∈ d.L := by
  have hρD : (d.ρ ⟨x, hx⟩ : Equiv.Perm (Fin 1755)) ∈ titsD := by
    have hsq : (d.ρ ⟨x, hx⟩ : Equiv.Perm (Fin 1755)) ^ 2 = 1 := by
      have hX2 : (⟨x, hx⟩ : centralizer ({d.t} : Set G)) ^ 2 = 1 := Subtype.ext hx2
      rw [← Subgroup.coe_pow, ← map_pow, hX2, map_one, OneMemClass.coe_one]
    by_cases h1 : (d.ρ ⟨x, hx⟩ : Equiv.Perm (Fin 1755)) = 1
    · rw [h1]
      exact one_mem _
    · exact titsA_involution_mem_D (d.ρ ⟨x, hx⟩).2 (orderOf_eq_prime hsq h1)
  obtain ⟨l, hl, hsL⟩ := (hd.ρ_mem_titsD_iff ⟨x, hx⟩).1 hρD
  obtain ⟨s, hsdef⟩ : ∃ s : G, s = l⁻¹ * x := ⟨_, rfl⟩
  have hs : s ∈ centralizer (d.L : Set G) ⊓ centralizer ({d.t} : Set G) := by
    rw [hsdef]
    exact mem_inf.2 ⟨hsL, mul_mem (inv_mem (hd.L_le hl)) hx⟩
  have hxs : x = l * s := by rw [hsdef, mul_inv_cancel_left]
  have hcomm : l * s = s * l := mem_centralizer_iff.1 (mem_inf.1 hs).1 l hl
  have h1 : l ^ 2 * s ^ 2 = 1 := by
    rw [← hx2, hxs]
    calc l ^ 2 * s ^ 2 = l * (l * s) * s := by simp only [sq, mul_assoc]
      _ = l * (s * l) * s := by rw [hcomm]
      _ = (l * s) ^ 2 := by simp only [sq, mul_assoc]
  have hl2 : l ^ 2 = 1 := by
    have hls : l ^ 2 = (s ^ 2)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have hmem : l ^ 2 ∈ d.L ⊓ centralizer (d.L : Set G) :=
      mem_inf.2 ⟨pow_mem hl 2, hls ▸ inv_mem (pow_mem (mem_inf.1 hs).1 2)⟩
    rw [hd.setting.inf_centralizer_eq_bot, mem_bot] at hmem
    exact hmem
  have hs2 : s ^ 2 = 1 := by rwa [hl2, one_mul] at h1
  by_cases hs1 : s = 1
  · left
    rw [hxs, hs1, mul_one]
    exact hl
  · right
    have hst : s = d.t := hd.eq_t_of_mem_kernel hs (orderOf_eq_prime hs2 hs1)
    have htl : d.t * l = l * d.t := (mem_centralizer_iff.1 hd.t_mem l hl).symm
    have ht2 : d.t * d.t = 1 := by rw [← sq, ← hd.t_two, pow_orderOf_eq_one]
    rw [hxs, hst, ← mul_assoc, htl, mul_assoc, ht2, mul_one]
    exact hl

theorem exists_hyp
    {L : Subgroup G} (h : TitsSetting G L) {t : G} (ht : t ∈ centralizer (L : Set G))
    (ht2 : orderOf t = 2) : ∃ d : Data G, d.L = L ∧ d.t = t ∧ d.Hyp := by
  obtain ⟨θ⟩ := titsModelEquiv L 2 1 h.reeTitsModel
  have hTN : centralizer ({t} : Set G) ≤ normalizer (L : Set G) :=
    (CFSG.LocalAnalysis.ComponentInitial.standard_involution_centralizer_normality
      h.std.standard ht ht2).1
  let ρ : centralizer ({t} : Set G) →* titsA :=
    titsConjEquiv.symm.toMonoidHom.comp ((MulAut.congr θ).toMonoidHom.comp
      (L.normalizerMonoidHom.comp (inclusion hTN)))
  refine ⟨⟨L, t, θ, ρ⟩, rfl, rfl, h, ht, ht2, fun x l m hm => ?_⟩
  have key : titsConj (ρ x) = MulAut.congr θ (L.normalizerMonoidHom (inclusion hTN x)) :=
    titsConjEquiv.apply_symm_apply (MulAut.congr θ (L.normalizerMonoidHom (inclusion hTN x)))
  have hm' : m = L.normalizerMonoidHom (inclusion hTN x) l :=
    Subtype.ext (by rw [hm, normalizerMonoidHom_apply_apply_coe]; rfl)
  have h2 := congrArg (fun φ : MulAut titsD => ((φ (θ l) : titsD) : Equiv.Perm (Fin 1755))) key
  simp only [coe_titsConj_apply, MulAut.congr_apply, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply] at h2
  rw [hm', ← h2]

theorem exists_data
    {L : Subgroup G} (h : TitsSetting G L) : ∃ d : Data G, d.L = L ∧ d.Hyp := by
  obtain ⟨t, ht, ht2⟩ := h.exists_involution
  obtain ⟨d, hdL, -, hd⟩ := exists_hyp h ht ht2
  exact ⟨d, hdL, hd⟩

end Data

end CFSG.LocalAnalysis.EvenBN.Tits
