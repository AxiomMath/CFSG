module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.LargeExtraspecial.GLRTransfer
public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionZStar
public import CFSG.LocalAnalysis.OddStandard.L34SeitzSimple
public import CFSG.LocalAnalysis.OddStandard.SmallAltFiveSector

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.Open CFSG.Blueprint
open CFSG.ABGLocalTools (IsSylowOf)

structure Hyp (G : Type) [Group G] [Finite G] (A : Subgroup G) : Prop where
  simple : IsSimpleGroup G
  nonab : ∃ a b : G, a * b ≠ b * a
  standard : standardComponentIsStandard A
  odd : Odd (Nat.card (center A))
  cyc : ∀ S : Sylow 2 (centralizer (A : Set G)), IsCyclic ↥S
  model : LieModel (A ⧸ center A) .PSL 3 2 2

theorem seitz77SimpleL34_of_false
    (h : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G), Hyp G A → False) :
    Seitz77SimpleL34 :=
  fun G _ _ hs hnab A hA hodd hcyc h34 => (h G A ⟨hs, hnab, hA, hodd, hcyc, h34⟩).elim

section Defs

variable {G : Type*} [Group G]

theorem map_center_subtype_eq_inf_centralizer (P : Subgroup G) :
    (center P).map P.subtype = P ⊓ centralizer (P : Set G) := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z.2, mem_centralizer_iff.mpr fun y hy =>
      congrArg Subtype.val (mem_center_iff.mp hz ⟨y, hy⟩)⟩
  · rintro ⟨hxP, hxC⟩
    exact ⟨⟨x, hxP⟩, mem_center_iff.mpr fun y => Subtype.ext (mem_centralizer_iff.mp hxC y y.2),
      rfl⟩

structure Datum (A : Subgroup G) where
  R : Sylow 2 (centralizer (A : Set G))
  t : G
  sector : Sector A R t
  P : Subgroup G
  hP : IsSylowOf 2 P (normalizer (A : Set G))
  hRP : sg A R ≤ P

end Defs

theorem Hyp.exists_datum {G : Type} [Group G] [Finite G] {A : Subgroup G} (h : Hyp G A) :
    Nonempty (Datum A) := by
  classical
  have hCeven : 2 ∣ Nat.card (centralizer (A : Set G)) := even_iff_two_dvd.mp h.standard.2.1
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := centralizer (A : Set G)) 2 hCeven
  have hcp : IsPGroup 2 (zpowers c) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hc, pow_one])
  obtain ⟨R, hcR⟩ := hcp.exists_le_sylow
  have hcR' : c ∈ (R : Subgroup (centralizer (A : Set G))) := hcR (mem_zpowers c)
  have hsec : Sector A R (c : G) :=
    ⟨h.standard, h.cyc R, ⟨c, hcR', rfl⟩, by rw [Subgroup.orderOf_coe, hc]⟩
  have hRN : IsPGroup 2 ((sg A R).subgroupOf (normalizer (A : Set G))) :=
    isPGroup_sg.comap_subtype
  obtain ⟨Q, hQ⟩ := hRN.exists_le_sylow
  refine ⟨⟨R, c, hsec, (Q : Subgroup (normalizer (A : Set G))).map
    (normalizer (A : Set G)).subtype, ⟨Q, rfl⟩, ?_⟩⟩
  intro x hx
  exact ⟨⟨x, sg_le_normalizer hx⟩, hQ (mem_subgroupOf.mpr hx), rfl⟩

namespace Datum

section Local

variable {G : Type*} [Group G] {A : Subgroup G} (d : Datum A)

theorem P_le_normalizer : d.P ≤ normalizer (A : Set G) := d.hP.le

theorem t_mem_P : d.t ∈ d.P := d.hRP (t_mem_sg d.sector)

theorem P_inf_centralizer_eq : d.P ⊓ centralizer (A : Set G) = sg A d.R :=
  sg_maximal inf_le_right d.hP.isPGroup.to_inf_left (le_inf d.hRP sg_le_centralizer)

theorem P_le_centralizer [Finite G] : d.P ≤ centralizer ({d.t} : Set G) := by
  intro x hx
  have hyP : x * d.t * x⁻¹ ∈ d.P := d.P.mul_mem (d.P.mul_mem hx d.t_mem_P) (d.P.inv_mem hx)
  have hy : x * d.t * x⁻¹ ∈ d.P ⊓ centralizer (A : Set G) :=
    ⟨hyP, centralizer_normalized (d.hP.le hx) (t_mem_centralizer d.sector)⟩
  rw [P_inf_centralizer_eq] at hy
  have hy2 : orderOf (x * d.t * x⁻¹) = 2 := by
    rw [← (SemiconjBy.conj_mk x d.t).orderOf_eq]
    exact d.sector.t_order
  have hxt := eq_t_of_orderOf_eq_two d.sector hy hy2
  rw [mem_centralizer_singleton_iff]
  calc x * d.t = x * d.t * x⁻¹ * x := by group
    _ = d.t * x := by rw [hxt]

theorem t_mem_center_P [Finite G] : d.t ∈ d.P ⊓ centralizer (d.P : Set G) :=
  ⟨d.t_mem_P, mem_centralizer_iff.mpr fun _ hy =>
    mem_centralizer_singleton_iff.mp (d.P_le_centralizer hy)⟩

theorem P_isSylow_centralizer [Finite G] : IsSylowOf 2 d.P (centralizer ({d.t} : Set G)) :=
  d.hP.of_le d.P_le_centralizer (centralizer_t_facts d.sector).1

theorem centralizer_T_eq [Finite G] (T : Sylow 2 G) (h : d.P ≤ T) :
    (T : Subgroup G) ⊓ centralizer ({d.t} : Set G) = d.P :=
  d.hP.eq_of_le (le_inf h d.P_le_centralizer)
    (inf_le_right.trans (centralizer_t_facts d.sector).1) T.isPGroup'.to_inf_left

theorem exists_conj_center [Finite G] (T : Sylow 2 G) (h : d.P ≤ T) (hne : d.P ≠ T) :
    ∃ g ∈ (T : Subgroup G), g ∈ normalizer (d.P : Set G) ∧ g ∉ d.P ∧
      g⁻¹ * d.t * g ∈ d.P ⊓ centralizer (d.P : Set G) ∧ g⁻¹ * d.t * g ≠ d.t := by
  classical
  have hI : d.P.subgroupOf (T : Subgroup G) < ⊤ := by
    refine lt_of_le_of_ne le_top fun htop => hne (le_antisymm h fun x hx => ?_)
    have hx' : (⟨x, hx⟩ : (T : Subgroup G)) ∈ d.P.subgroupOf (T : Subgroup G) := by
      rw [htop]
      trivial
    exact mem_subgroupOf.mp hx'
  have : Group.IsNilpotent (T : Subgroup G) := T.isPGroup'.isNilpotent
  have hnc : NormalizerCondition (T : Subgroup G) :=
    Group.normalizerCondition_of_isNilpotent (G := (T : Subgroup G))
  obtain ⟨x, hxN, hxnot⟩ := IsConcreteLE.exists_of_lt (hnc _ hI)
  have hgN : (x : G) ∈ normalizer (d.P : Set G) := by
    have hxsub : x ∈ (normalizer (d.P : Set G)).subgroupOf (T : Subgroup G) := by
      rw [subgroupOf_normalizer_eq h]
      exact hxN
    exact mem_subgroupOf.mp hxsub
  have hgP : (x : G) ∉ d.P := fun hx => hxnot (mem_subgroupOf.mpr hx)
  refine ⟨x, x.2, hgN, hgP, ⟨?_, ?_⟩, ?_⟩
  · exact (mem_normalizer_iff''.mp hgN d.t).mp d.t_mem_P
  · refine mem_centralizer_iff.mpr fun y hy => ?_
    have hy' : (x : G) * y * (x : G)⁻¹ ∈ d.P := (mem_normalizer_iff.mp hgN y).mp hy
    have key := mem_centralizer_singleton_iff.mp (d.P_le_centralizer hy')
    calc y * ((x : G)⁻¹ * d.t * x) = (x : G)⁻¹ * ((x : G) * y * (x : G)⁻¹ * d.t) * x := by group
      _ = (x : G)⁻¹ * (d.t * ((x : G) * y * (x : G)⁻¹)) * x := by rw [key]
      _ = (x : G)⁻¹ * d.t * x * y := by group
  · intro heq
    apply hgP
    rw [← d.centralizer_T_eq T h]
    refine ⟨x.2, mem_centralizer_singleton_iff.mpr ?_⟩
    calc (x : G) * d.t = (x : G) * ((x : G)⁻¹ * d.t * x) := by rw [heq]
      _ = d.t * (x : G) := by group

end Local

section Simple

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} (d : Datum A)

theorem exists_conj_commuting (h : Hyp G A) :
    ∃ g : G, g⁻¹ * d.t * g ≠ d.t ∧ g⁻¹ * d.t * g * d.t = d.t * (g⁻¹ * d.t * g) := by
  classical
  have := h.simple
  by_contra hcon
  have hcomm : ∀ g : G, g⁻¹ * d.t * g * d.t = d.t * (g⁻¹ * d.t * g) → g⁻¹ * d.t * g = d.t :=
    fun g hg => by_contra fun hne => hcon ⟨g, hne, hg⟩
  obtain ⟨T, hPT⟩ := d.hP.isPGroup.exists_le_sylow
  have hPT_eq : d.P = T := by
    by_contra hne
    obtain ⟨g, -, -, -, hgz, hgne⟩ := d.exists_conj_center T hPT hne
    exact hgne (hcomm g (mem_centralizer_iff.mp hgz.2 d.t d.t_mem_P).symm)
  have htT : d.t ∈ (T : Subgroup G) := hPT_eq ▸ d.t_mem_P
  have hTc : ∀ s ∈ (T : Subgroup G), s * d.t = d.t * s := fun s hs =>
    mem_centralizer_singleton_iff.mp (d.P_le_centralizer (hPT_eq ▸ hs))
  have hz2 : orderOf (⟨d.t, htT⟩ : (T : Subgroup G)) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact d.sector.t_order
  have hzZ : (⟨d.t, htT⟩ : (T : Subgroup G)) ∈ center (T : Subgroup G) := by
    rw [mem_center_iff]
    intro s
    exact Subtype.ext (hTc s s.2)
  obtain ⟨hfac, -⟩ :=
    CFSG.ComponentClassification.StandardRecognition.glauberman_zStar_central_sylow_involution_univ
      T ⟨d.t, htT⟩ hzZ hz2 fun g hg => hcomm g (hTc _ hg)
  have hev : Even (Nat.card G) := by
    rw [even_iff_two_dvd, ← d.sector.t_order]
    exact orderOf_dvd_natCard d.t
  have hoddCore : Odd (Nat.card (CFSG.oddCore G)) := by
    have h2 : CFSG.oddCore G = CFSG.pPrimeCore 2 G := by
      simp only [CFSG.oddCore, CFSG.pPrimeCore, Nat.coprime_two_left]
    rw [h2]
    exact Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := G))
  have hbot : CFSG.oddCore G = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.oddCore G) with h1 | h1
    · exact h1
    · rw [h1, Subgroup.card_top] at hoddCore
      exact absurd hev (Nat.not_even_iff_odd.mpr hoddCore)
  have htc : d.t ∈ center G := by
    rw [mem_center_iff]
    intro g
    obtain ⟨c, hc, k, hk, hgck⟩ := hfac g
    rw [hbot, mem_bot] at hk
    rw [hgck, hk, mul_one]
    exact mem_centralizer_singleton_iff.mp hc
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G) with h1 | h1
  · rw [h1, mem_bot] at htc
    have := d.sector.t_order
    rw [htc, orderOf_one] at this
    exact absurd this (by norm_num)
  · obtain ⟨a, b, hab⟩ := h.nonab
    exact hab (mem_center_iff.mp (h1 ▸ mem_top a) b).symm

end Simple

end Datum

theorem exists_conj_mem_of_index_two {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) {T M : Subgroup G} (hT : IsPGroup 2 T)
    (hTidx : ¬ 2 ∣ T.index) (hMT : M ≤ T) (hM : M.relIndex T = 2) {g d : G} (hgT : g ∈ T)
    (hgM : g ∉ M) (hgd : g * g = d) (hd : d * d = 1)
    (hdM : ∀ x : G, x⁻¹ * d * x ∈ T → x⁻¹ * d * x ∈ M) :
    ∃ x : G, x⁻¹ * g * x ∈ M :=
  let ⟨x, hx, _⟩ := CFSG.LargeExtraspecial.GLR.exists_extremal_conj_mem_of_sq_eq_of_isSimpleGroup
    hnab hT hTidx hMT hM hgT hgM hgd hd hdM
  ⟨x, hx⟩

theorem exists_conj_mem_of_index_two_of_mul_self {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) {T M : Subgroup G} (hT : IsPGroup 2 T)
    (hTidx : ¬ 2 ∣ T.index) (hMT : M ≤ T) (hM : M.relIndex T = 2) {g : G} (hgT : g ∈ T)
    (hgM : g ∉ M) (hg : g * g = 1) :
    ∃ x : G, x⁻¹ * g * x ∈ M :=
  exists_conj_mem_of_index_two hnab hT hTidx hMT hM hgT hgM hg (by rw [mul_one])
    fun x _ => by rw [mul_one, inv_mul_cancel]; exact M.one_mem

end CFSG.OddStandard.Seitz77
