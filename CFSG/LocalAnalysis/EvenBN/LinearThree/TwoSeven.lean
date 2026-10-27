module

public import CFSG.LocalAnalysis.EvenBN.LinearThree.TwoSix
public import CFSG.LocalAnalysis.EvenBN.GMSK.LayerRankOne
public import CFSG.LocalAnalysis.EvenBN.GMSK.ConsumerSections
public import CFSG.LocalAnalysis.EvenBN.GMSK.U3Facts
public import CFSG.CGT.Timmesfeld75.Lemma27
public import CFSG.LocalAnalysis.EvenBN.GMSK.LayerListK
import CFSG.LocalAnalysis.SteinbergBKOddNormalQuotientStandard
import CFSG.LocalAnalysis.EvenBN.GMSK.LayerRankOneBender
public import CFSG.CGT.Timmesfeld75.GoldschmidtMilestone

public section

namespace CFSG.LocalAnalysis.EvenBN.LinearThree

open Subgroup CFSG.Open CFSG.Blueprint
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.OddStandard.Seitz77 (Datum)

theorem exists_ne_one_mem_centralizer_of_pGroup
    {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime] {T U : Subgroup H}
    (hT : IsPGroup p T) (hUT : U ≤ T) (hUn : T ≤ normalizer (U : Set H)) (hU : U ≠ ⊥) :
    ∃ u ∈ U, u ≠ 1 ∧ u ∈ centralizer (T : Set H) := by
  have : Group.IsNilpotent T := hT.isNilpotent
  have hnormal : (U.subgroupOf T).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hUn
  have hne : U.subgroupOf T ≠ ⊥ := by
    intro h
    apply hU
    rw [← Subgroup.map_subgroupOf_eq_of_le hUT, h, Subgroup.map_bot]
  obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  refine ⟨y, hy.1, fun h => hy1 (Subtype.ext (Subtype.ext h)), ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy.2 ⟨t, ht⟩)

namespace WData

variable {G : Type} [Group G] {A : Subgroup G} {d : Datum A} {Vi : Subgroup G} {q : ℕ}

abbrev N (w : WData d Vi q) : Subgroup G := normalizer (w.W : Set G)

abbrev WN (w : WData d Vi q) : Subgroup w.N := w.W.subgroupOf w.N

abbrev Nbar (w : WData d Vi q) : Type := w.N ⧸ w.WN

abbrev Ntil (w : WData d Vi q) : Type := w.Nbar ⧸ standardComponentOddCore w.Nbar

abbrev projBar (w : WData d Vi q) : w.N →* w.Nbar := QuotientGroup.mk' w.WN

abbrev projTil (w : WData d Vi q) : w.Nbar →* w.Ntil := QuotientGroup.mk' _

abbrev tN (w : WData d Vi q) : w.N := ⟨d.t, w.t_norm⟩

abbrev tbar (w : WData d Vi q) : w.Nbar := w.projBar w.tN

abbrev ttil (w : WData d Vi q) : w.Ntil := w.projTil w.tbar

abbrev Lbar (w : WData d Vi q) (L : Subgroup G) : Subgroup w.Nbar :=
  (L.subgroupOf w.N).map w.projBar

abbrev Ltil (w : WData d Vi q) (L : Subgroup G) : Subgroup w.Ntil := (w.Lbar L).map w.projTil

theorem projBar_eq_one_iff (w : WData d Vi q) (x : w.N) : w.projBar x = 1 ↔ (x : G) ∈ w.W :=
  QuotientGroup.eq_one_iff x

theorem projBar_eq_iff (w : WData d Vi q) (x y : w.N) :
    w.projBar x = w.projBar y ↔ (x : G)⁻¹ * y ∈ w.W :=
  QuotientGroup.eq

theorem exists_eq_mul_of_commute (w : WData d Vi q) {x : w.N}
    (hx : w.projBar x * w.tbar = w.tbar * w.projBar x) :
    ∃ y ∈ w.W, ∃ c : G, c * d.t = d.t * c ∧ (x : G) = y * c := by
  have ht2 := d.t_mul_self
  have htinv : d.t⁻¹ = d.t := inv_eq_of_mul_eq_one_right ht2
  have h1 : (((x * w.tN)⁻¹ * (w.tN * x) : w.N) : G) ∈ w.W := by
    rw [← w.projBar_eq_one_iff, map_mul, map_inv, map_mul, map_mul, hx, inv_mul_cancel]
  have h1' : d.t⁻¹ * (x : G)⁻¹ * d.t * x ∈ w.W := by
    simpa [mul_assoc] using h1
  set y : G := (x : G) * d.t * (x : G)⁻¹ * d.t with hy
  have hyW : y ∈ w.W := by
    have := (mem_normalizer_iff.mp x.2 _).mp h1'
    rw [hy]
    rw [htinv] at this
    simpa [mul_assoc] using this
  have hy2 : y * y = 1 := by rw [← sq]; exact w.elem.2 y hyW
  have hyt : y * d.t = d.t * y := by
    have hyt' : y * d.t = (x : G) * d.t * (x : G)⁻¹ := by
      rw [hy, mul_assoc _ d.t d.t, ht2, mul_one]
    have e1 : y * d.t * (y * d.t) = 1 := by
      rw [hyt']
      calc (x : G) * d.t * (x : G)⁻¹ * ((x : G) * d.t * (x : G)⁻¹) =
          (x : G) * (d.t * d.t) * (x : G)⁻¹ := by group
        _ = 1 := by rw [ht2]; group
    have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
    have e3 : d.t * y * d.t = y := by
      calc d.t * y * d.t = y⁻¹ * (y * d.t * (y * d.t)) := by group
        _ = y := by rw [e1, mul_one, hyinv]
    calc y * d.t = (d.t * y * d.t) * d.t := by rw [e3]
      _ = d.t * y * (d.t * d.t) := by group
      _ = d.t * y := by rw [ht2, mul_one]
  have hyV : y ∈ Vi := by
    rw [← w.fix]
    exact ⟨hyW, mem_centralizer_singleton_iff.mpr hyt⟩
  obtain ⟨w₀, hw₀, hc⟩ := w.comm_onto y hyV
  refine ⟨w₀, hw₀, w₀⁻¹ * x, ?_, by group⟩
  have h2 : w₀ * d.t * w₀⁻¹ = (x : G) * d.t * (x : G)⁻¹ := by
    have e2 : w₀ * d.t * w₀⁻¹ = d.t * y := by
      rw [← hc]
      calc w₀ * d.t * w₀⁻¹ = (d.t * d.t) * w₀ * d.t * w₀⁻¹ := by rw [ht2, one_mul]
        _ = d.t * (d.t * w₀ * d.t * w₀⁻¹) := by group
    rw [e2, ← hyt, hy, mul_assoc _ d.t d.t, ht2, mul_one]
  calc w₀⁻¹ * x * d.t = w₀⁻¹ * ((x : G) * d.t * (x : G)⁻¹) * x := by group
    _ = w₀⁻¹ * (w₀ * d.t * w₀⁻¹) * x := by rw [h2]
    _ = d.t * (w₀⁻¹ * x) := by group

theorem W_le_N (w : WData d Vi q) : w.W ≤ w.N := le_normalizer

theorem orderOf_tbar (w : WData d Vi q) : orderOf w.tbar = 2 := by
  refine orderOf_eq_prime ?_ ?_
  · rw [sq, ← map_mul]
    refine (w.projBar_eq_one_iff _).mpr ?_
    change d.t * d.t ∈ w.W
    rw [d.t_mul_self]
    exact one_mem _
  · intro h
    exact w.t_not_mem ((w.projBar_eq_one_iff _).mp h)

variable [Finite G]

theorem mem_normalizer_Vi (w : WData d Vi q) {c : G} (hcN : c ∈ w.N)
    (hct : c * d.t = d.t * c) : c ∈ normalizer (Vi : Set G) := by
  refine Subgroup.mem_normalizer_fintype fun v hv => ?_
  rw [← w.fix] at hv ⊢
  refine ⟨(mem_normalizer_iff.mp hcN v).mp hv.1, mem_centralizer_singleton_iff.mpr ?_⟩
  have hvt := mem_centralizer_singleton_iff.mp hv.2
  calc c * v * c⁻¹ * d.t = c * v * (c⁻¹ * d.t) := by group
    _ = c * v * (d.t * c⁻¹) := by
        rw [show c⁻¹ * d.t = d.t * c⁻¹ from (Commute.inv_left (show Commute c d.t from hct)).eq]
    _ = c * (v * d.t) * c⁻¹ := by group
    _ = c * (d.t * v) * c⁻¹ := by rw [hvt]
    _ = (c * d.t) * v * c⁻¹ := by group
    _ = d.t * (c * v * c⁻¹) := by rw [hct]; group

theorem mem_normalizer_adj_of_commute (w : WData d Vi q) (hWV : Vi ≤ d.V) {x : w.N}
    (hx : w.projBar x * w.tbar = w.tbar * w.projBar x) :
    (x : G) ∈ normalizer ((Vi ⊔ zpowers d.t : Subgroup G) : Set G) := by
  obtain ⟨y, hy, c, hct, hxy⟩ := w.exists_eq_mul_of_commute hx
  have hyE : y ∈ normalizer ((Vi ⊔ zpowers d.t : Subgroup G) : Set G) :=
    (w.sup_le_inf_centralizer (mem_sup_left hy)).1
  have hcN : c ∈ w.N := by
    have : c = y⁻¹ * x := by rw [hxy]; group
    rw [this]
    exact mul_mem (inv_mem (w.W_le_N hy)) x.2
  have hcE : c ∈ normalizer ((Vi ⊔ zpowers d.t : Subgroup G) : Set G) :=
    mem_normalizer_adj d hWV (w.mem_normalizer_Vi hcN hct) (by
      rw [hct, mul_inv_cancel_right]
      exact mem_sup_right (mem_zpowers _))
  rw [hxy]
  exact mul_mem hyE hcE

omit [Finite G] in
theorem commute_of_mem_normalizer_adj (w : WData d Vi q) {x : w.N}
    (hx : (x : G) ∈ normalizer ((Vi ⊔ zpowers d.t : Subgroup G) : Set G)) :
    w.projBar x * w.tbar = w.tbar * w.projBar x := by
  have ht' : (x : G) * d.t * (x : G)⁻¹ ∈ Vi ⊔ zpowers d.t :=
    (mem_normalizer_iff.mp hx d.t).mp (mem_sup_right (mem_zpowers _))
  have htV : (x : G) * d.t * (x : G)⁻¹ ∉ Vi := fun h1 => by
    have h2 := (mem_normalizer_iff.mp x.2 d.t).mpr (w.le_W h1)
    exact w.t_not_mem h2
  have hv := (w.mem_adj_iff.mp ht').resolve_left htV
  rw [← map_mul, ← map_mul, w.projBar_eq_iff]
  have e : ((x * w.tN : w.N) : G)⁻¹ * ((w.tN * x : w.N) : G) =
      (x : G)⁻¹ * ((x : G) * d.t * (x : G)⁻¹ * d.t) * x := by
    simp only [Subgroup.coe_mul, mul_inv_rev]
    rw [inv_eq_of_mul_eq_one_right d.t_mul_self]
    group
  rw [e]
  have := (mem_normalizer_iff.mp (inv_mem x.2) _).mp (w.le_W hv)
  simpa [mul_assoc] using this

section Levi

open CFSG.LieType.Chevalley (SL2)
open Matrix

variable {K : Type} [Field K]

omit [Finite G] in
theorem lev_mem_N (w : WData d Vi q) (D : LeviData A Vi K) (B : SL2 K) : D.lev B ∈ w.N :=
  w.levi_norm ⟨D.lev_mem B, D.lev_mem_normalizer B⟩

noncomputable def levN (w : WData d Vi q) (D : LeviData A Vi K) : SL2 K →* w.N :=
  D.lev.codRestrict w.N (w.lev_mem_N D)

noncomputable def levBar (w : WData d Vi q) (D : LeviData A Vi K) : SL2 K →* w.Nbar :=
  w.projBar.comp (w.levN D)

omit [Finite G] in
theorem levBar_injective (w : WData d Vi q) (D : LeviData A Vi K) :
    Function.Injective (w.levBar D) := by
  rw [injective_iff_map_eq_one]
  intro B hB
  have h1 : D.lev B ∈ w.W := (w.projBar_eq_one_iff _).mp hB
  have h2 : D.lev B ∈ Vi := by
    have h3 : D.lev B ∈ w.W ⊓ centralizer ({d.t} : Set G) :=
      ⟨h1, mem_centralizer_singleton_iff.mpr (d.comm_t_of_mem (D.lev_mem B))⟩
    rwa [w.fix] at h3
  have hB1 : ∀ v : Fin 2 → K, (B : Matrix (Fin 2) (Fin 2) K) *ᵥ v = v := by
    intro v
    have hc : D.lev B * D.ι (Multiplicative.ofAdd v) = D.ι (Multiplicative.ofAdd v) * D.lev B :=
      comm_of_isElemAbelian w.elem (w.le_W h2) (w.le_W (D.ι_mem_W _))
    have h3 := D.lev_conj B (Multiplicative.ofAdd v)
    rw [hc, mul_inv_cancel_right, toAdd_ofAdd] at h3
    exact (Multiplicative.ofAdd.injective (D.ι_injective h3)).symm
  exact Subtype.ext (Matrix.ext_iff_mulVec.mpr fun v => by
    rw [hB1 v, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec])

omit [Finite G] in
theorem range_levBar (w : WData d Vi q) (D : LeviData A Vi K) :
    (w.levBar D).range = w.Lbar D.lev.range := by
  have h : D.lev.range.subgroupOf w.N = (w.levN D).range := by
    ext x
    simp only [mem_subgroupOf, MonoidHom.mem_range, levN, MonoidHom.codRestrict_apply,
      Subtype.ext_iff]
  rw [levBar, MonoidHom.range_comp, Lbar, h]

noncomputable def lbarEquiv (w : WData d Vi q) (D : LeviData A Vi K) :
    w.Lbar D.lev.range ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
  ((MonoidHom.ofInjective (w.levBar_injective D)).trans
    (MulEquiv.subgroupCongr (w.range_levBar D))).symm

omit [Finite G] in
theorem commutator_levRange [Finite K] [CharP K 2] (hK : 3 ≤ Nat.card K)
    (D : LeviData A Vi K) : ⁅D.lev.range, D.lev.range⁆ = D.lev.range := by
  obtain ⟨μ, hμ⟩ := exists_unit_ne_one (K := K) hK
  have hperf : commutator (SL2 K) = ⊤ :=
    Matrix.SL2.commutator_eq_top μ.ne_zero (sq_ne_one_of_charTwo hμ)
  rw [MonoidHom.range_eq_map, ← map_commutator, ← commutator_def, hperf]

omit [Finite G] in
theorem commutator_parabolic_le (D : LeviData A Vi K) :
    ⁅A ⊓ normalizer (Vi : Set G), A ⊓ normalizer (Vi : Set G)⁆ ≤ Vi ⊔ D.lev.range := by
  set M : Subgroup G := Vi ⊔ D.lev.range with hM
  have hdec : ∀ x ∈ A ⊓ normalizer (Vi : Set G), ∃ m ∈ M, ∃ l : Kˣ, x = m * D.tor l := by
    intro x hx
    obtain ⟨u, l, B, rfl⟩ := (D.mem_normalizer_iff x hx.1).mp hx.2
    refine ⟨D.ι u * D.lev B, mul_mem (mem_sup_left (D.ι_mem_W u)) (mem_sup_right ⟨B, rfl⟩),
      l, ?_⟩
    rw [mul_assoc, D.tor_comm l B, ← mul_assoc]
  have htorM : ∀ l : Kˣ, ∀ m ∈ M, D.tor l * m * (D.tor l)⁻¹ ∈ M := by
    intro l
    have hle : M ≤ M.comap (MulAut.conj (D.tor l)).toMonoidHom := by
      refine sup_le (fun v hv => ?_) ?_
      · rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        exact mem_sup_left ((mem_normalizer_iff.mp (D.tor_mem_normalizer l) v).mp hv)
      · rintro _ ⟨B, rfl⟩
        rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, D.tor_comm l B,
          mul_inv_cancel_right]
        exact mem_sup_right ⟨B, rfl⟩
    intro m hm
    have := hle hm
    rwa [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
  rw [Subgroup.commutator_le]
  intro x hx y hy
  obtain ⟨m₁, hm₁, l₁, rfl⟩ := hdec x hx
  obtain ⟨m₂, hm₂, l₂, rfl⟩ := hdec y hy
  have hcomm : D.tor l₁ * D.tor l₂ = D.tor l₂ * D.tor l₁ := by
    rw [← map_mul, ← map_mul, mul_comm]
  rw [commutatorElement_def]
  have e : m₁ * D.tor l₁ * (m₂ * D.tor l₂) * (m₁ * D.tor l₁)⁻¹ * (m₂ * D.tor l₂)⁻¹ =
      m₁ * (D.tor l₁ * m₂ * (D.tor l₁)⁻¹) *
        (D.tor l₁ * D.tor l₂ * (D.tor l₁)⁻¹ * (D.tor l₂)⁻¹) *
        (D.tor l₂ * m₁⁻¹ * (D.tor l₂)⁻¹) * m₂⁻¹ := by group
  have e2 : D.tor l₁ * D.tor l₂ * (D.tor l₁)⁻¹ * (D.tor l₂)⁻¹ = 1 := by
    rw [hcomm]; group
  rw [e, e2, mul_one]
  exact mul_mem (mul_mem (mul_mem hm₁ (htorM l₁ m₂ hm₂)) (htorM l₂ _ (inv_mem hm₁)))
    (inv_mem hm₂)

omit [Finite G] in
theorem conj_levRange_le [Finite K] [CharP K 2] (hK : 3 ≤ Nat.card K) (D : LeviData A Vi K)
    {c : G} (hcA : c ∈ normalizer (A : Set G)) (hcV : c ∈ normalizer (Vi : Set G)) :
    D.lev.range.map (MulAut.conj c).toMonoidHom ≤ Vi ⊔ D.lev.range := by
  set X := D.lev.range.map (MulAut.conj c).toMonoidHom with hXdef
  have hX : ⁅X, X⁆ = X := by rw [hXdef, ← map_commutator, commutator_levRange hK D]
  have hXP : X ≤ A ⊓ normalizer (Vi : Set G) := by
    rintro _ ⟨_, ⟨B, rfl⟩, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hn : c * D.lev B * c⁻¹ ∈ normalizer (Vi : Set G) :=
      mul_mem (mul_mem hcV (D.lev_mem_normalizer B)) (inv_mem hcV)
    exact Subgroup.mem_inf.mpr ⟨(mem_normalizer_iff.mp hcA _).mp (D.lev_mem B), hn⟩
  rw [← hX]
  exact (commutator_mono hXP hXP).trans (commutator_parabolic_le D)

omit [Finite G] in
theorem levRange_le_normalizer (D : LeviData A Vi K) :
    D.lev.range ≤ normalizer (Vi : Set G) := by
  rintro _ ⟨B, rfl⟩
  exact D.lev_mem_normalizer B

omit [Finite G] in
theorem levRange_le_N (w : WData d Vi q) (D : LeviData A Vi K) : D.lev.range ≤ w.N := by
  rintro _ ⟨B, rfl⟩
  exact w.lev_mem_N D B

omit [Finite G] in
theorem Lbar_le_centralizer (w : WData d Vi q) (D : LeviData A Vi K) :
    w.Lbar D.lev.range ≤ centralizer ({w.tbar} : Set w.Nbar) := by
  rintro _ ⟨z, hz, rfl⟩
  rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
  congr 1
  obtain ⟨B, hB⟩ := (mem_subgroupOf.mp hz)
  exact Subtype.ext (by
    change (z : G) * d.t = d.t * z
    rw [← hB]
    exact d.comm_t_of_mem (D.lev_mem B))

theorem Lbar_normal [Finite K] [CharP K 2] (hK : 3 ≤ Nat.card K) (w : WData d Vi q)
    (D : LeviData A Vi K) :
    ((w.Lbar D.lev.range).subgroupOf (centralizer ({w.tbar} : Set w.Nbar))).Normal := by
  refine ⟨fun x hx n => ?_⟩
  rw [mem_subgroupOf] at hx ⊢
  obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective w.WN (n : w.Nbar)
  have hyc : w.projBar y * w.tbar = w.tbar * w.projBar y := by
    rw [hy]
    exact mem_centralizer_singleton_iff.mp n.2
  obtain ⟨u, hu, c, hct, hyuc⟩ := w.exists_eq_mul_of_commute hyc
  have hcN : c ∈ w.N := by
    have e : c = u⁻¹ * y := by rw [hyuc]; group
    rw [e]
    exact mul_mem (inv_mem (w.W_le_N hu)) y.2
  have hcA : c ∈ normalizer (A : Set G) :=
    (OddStandard.centralizer_t_facts d.sector).1 (mem_centralizer_singleton_iff.mpr hct)
  have hcV := w.mem_normalizer_Vi hcN hct
  obtain ⟨z, hz, hzx⟩ := hx
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← hzx]
  have hz' : (z : G) ∈ D.lev.range := mem_subgroupOf.mp hz
  have hcz : c * z * c⁻¹ ∈ Vi ⊔ D.lev.range := by
    have := conj_levRange_le hK D hcA hcV (Subgroup.mem_map_of_mem _ hz')
    rwa [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
  rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left _ _ (levRange_le_normalizer D),
    Set.mem_mul] at hcz
  obtain ⟨v, hv, l, hl, hvl⟩ := hcz
  have hlN : l ∈ w.N := w.levRange_le_N D hl
  refine ⟨⟨l, hlN⟩, mem_subgroupOf.mpr hl, ?_⟩
  change w.projBar ⟨l, hlN⟩ = (n : w.Nbar) * w.projBar z * (n : w.Nbar)⁻¹
  rw [← hy, ← map_mul, ← map_inv, ← map_mul, w.projBar_eq_iff]
  have e : ((⟨l, hlN⟩ : w.N) : G)⁻¹ * ((y * z * y⁻¹ : w.N) : G) =
      (l⁻¹ * (u * v) * l) * u⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hyuc, show (u * c) * (z : G) * (u * c)⁻¹ = u * (c * z * c⁻¹) * u⁻¹ by group, ← hvl]
    group
  rw [e]
  have hlW : l⁻¹ * (u * v) * l ∈ w.W := by
    have := (mem_normalizer_iff.mp (inv_mem hlN) (u * v)).mp (mul_mem hu (w.le_W hv))
    simpa using this
  exact mul_mem hlW (inv_mem hu)

theorem exists_sylow_centralizer_Lbar {f : ℕ} (hf : 3 ≤ f) {V₁ V₂ : Subgroup G}
    (hR : Radicals d.V V₁ V₂ (2 ^ f)) (hW : Vi = V₁ ∨ Vi = V₂)
    (hN : normalizer ((Vi ⊔ zpowers d.t : Subgroup G) : Set G) ≤ normalizer (Vi : Set G))
    (w : WData d Vi (2 ^ f)) (D : LeviData A Vi K) :
    ∃ S : Sylow 2 ↥(centralizer (w.Lbar D.lev.range : Set w.Nbar) ⊓
        centralizer ({w.tbar} : Set w.Nbar)),
      (S : Subgroup _).map (centralizer (w.Lbar D.lev.range : Set w.Nbar) ⊓
        centralizer ({w.tbar} : Set w.Nbar)).subtype = zpowers w.tbar := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hWV, -, hVc⟩ := hR.property hW
  set B := centralizer (w.Lbar D.lev.range : Set w.Nbar) ⊓
    centralizer ({w.tbar} : Set w.Nbar) with hBdef
  have htB : zpowers w.tbar ≤ B := by
    rw [zpowers_le]
    exact ⟨mem_centralizer_iff.mpr fun x hx => mem_centralizer_singleton_iff.mp
      (w.Lbar_le_centralizer D hx), mem_centralizer_singleton_iff.mpr rfl⟩
  have hz2 : IsPGroup 2 (zpowers w.tbar) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, w.orderOf_tbar, pow_one])
  obtain ⟨S, hS⟩ := (hz2.comap_subtype (K := B)).exists_le_sylow
  refine ⟨S, le_antisymm ?_ fun x hx => ⟨⟨x, htB hx⟩, hS (mem_subgroupOf.mpr hx), rfl⟩⟩
  set S' : Subgroup w.Nbar := (S : Subgroup B).map B.subtype with hS'
  have hS'B : S' ≤ B := map_subtype_le _
  have hS'2 : IsPGroup 2 S' := S.isPGroup'.map _
  set SG : Subgroup G := (S'.comap w.projBar).map w.N.subtype with hSG
  have hmemSG : ∀ x : G, x ∈ SG ↔ ∃ hx : x ∈ w.N, w.projBar ⟨x, hx⟩ ∈ S' := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
    · rintro ⟨hx, hx'⟩
      exact ⟨⟨x, hx⟩, hx', rfl⟩
  have hSG2 : IsPGroup 2 SG := by
    rintro ⟨x, hx⟩
    obtain ⟨hxN, hxS⟩ := (hmemSG x).mp hx
    obtain ⟨k, hk⟩ := hS'2 ⟨_, hxS⟩
    have hk' : w.projBar (⟨x, hxN⟩ ^ 2 ^ k) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val hk
    have hW1 := (w.projBar_eq_one_iff _).mp hk'
    refine ⟨k + 1, Subtype.ext ?_⟩
    have h2 := w.elem.2 _ hW1
    simp only [Subgroup.coe_pow, OneMemClass.coe_one] at h2 ⊢
    rw [pow_succ, pow_mul, h2]
  have hWSG : w.W ≤ SG := fun x hx =>
    (hmemSG x).mpr ⟨w.W_le_N hx, by rw [(w.projBar_eq_one_iff _).mpr hx]; exact one_mem _⟩
  have hSGE : SG ≤ normalizer ((Vi ⊔ zpowers d.t : Subgroup G) : Set G) := by
    intro x hx
    obtain ⟨hxN, hxS⟩ := (hmemSG x).mp hx
    exact w.mem_normalizer_adj_of_commute hWV
      ((mem_centralizer_singleton_iff.mp (hS'B hxS).2).trans rfl)
  have hSGV : SG ≤ normalizer (Vi : Set G) := hSGE.trans hN
  have hVne : Vi ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hVc
    have : 1 < (2 ^ f) ^ 2 := Nat.one_lt_pow (by norm_num) (Nat.one_lt_two_pow (by omega))
    omega
  obtain ⟨v, hv, hv1, hvC⟩ := exists_ne_one_mem_centralizer_of_pGroup hSG2
    ((w.le_W).trans hWSG) hSGV hVne
  have hSGC : SG ≤ centralizer (Vi : Set G) := by
    intro s hs
    rw [mem_centralizer_iff]
    intro v' hv'
    by_cases hv'1 : v' = 1
    · rw [hv'1, one_mul, mul_one]
    obtain ⟨Bm, hBm⟩ := D.transitive v hv v' hv' hv1 hv'1
    obtain ⟨hsN, hsS⟩ := (hmemSG s).mp hs
    set l := D.lev Bm with hl
    have hlN : l ∈ w.N := w.lev_mem_N D Bm
    have hcomm : w.projBar ⟨s, hsN⟩ * w.projBar ⟨l, hlN⟩ =
        w.projBar ⟨l, hlN⟩ * w.projBar ⟨s, hsN⟩ :=
      (mem_centralizer_iff.mp (hS'B hsS).1 _ ⟨⟨l, hlN⟩, mem_subgroupOf.mpr ⟨Bm, rfl⟩, rfl⟩).symm
    rw [← map_mul, ← map_mul, w.projBar_eq_iff] at hcomm
    have ha : l⁻¹ * s⁻¹ * l * s ∈ w.W := by
      simpa [mul_assoc] using hcomm
    have he : s * l * s⁻¹ * l⁻¹ ∈ w.W := by
      have := (mem_normalizer_iff.mp (mul_mem hlN hsN) _).mp (inv_mem ha)
      have e : l * s * (l⁻¹ * s⁻¹ * l * s)⁻¹ * (l * s)⁻¹ = s * l * s⁻¹ * l⁻¹ := by group
      rwa [e] at this
    have hsv : s * v * s⁻¹ = v := by
      rw [mem_centralizer_iff.mp hvC s hs, mul_inv_cancel_right]
    set e := s * l * s⁻¹ * l⁻¹ with he_def
    have hev' : e * v' = v' * e := comm_of_isElemAbelian w.elem he (w.le_W hv')
    have key : s * v' * s⁻¹ = v' := by
      calc s * v' * s⁻¹ = s * (l * v * l⁻¹) * s⁻¹ := by rw [hBm]
        _ = (e * l) * (s * v * s⁻¹) * (e * l)⁻¹ := by rw [he_def]; group
        _ = e * (l * v * l⁻¹) * e⁻¹ := by rw [hsv]; group
        _ = e * v' * e⁻¹ := by rw [hBm]
        _ = v' := by rw [hev', mul_inv_cancel_right]
    calc v' * s = s * v' * s⁻¹ * s := by rw [key]
      _ = s * v' := by group
  have hSGX : SG ≤ w.W ⊔ zpowers d.t := w.le_sup_of_isPGroup SG hSG2 (le_inf hSGE hSGC)
  intro x hx
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective w.WN x
  have hyX : (y : G) ∈ w.W ⊔ zpowers d.t := hSGX ((hmemSG y).mpr ⟨y.2, hx⟩)
  rcases w.mem_sup_iff.mp hyX with h1 | h1
  · have : w.projBar y = 1 := (w.projBar_eq_one_iff _).mpr h1
    change w.projBar y ∈ zpowers w.tbar
    rw [this]
    exact one_mem _
  · have : w.projBar y = w.tbar := by
      rw [w.projBar_eq_iff]
      have ht := (mem_normalizer_iff.mp w.t_norm _).mp h1
      have htinv : d.t⁻¹ = d.t := inv_eq_of_mul_eq_one_right d.t_mul_self
      have e : d.t * ((y : G) * d.t) * d.t⁻¹ = ((y : G)⁻¹ * d.t)⁻¹ := by
        calc d.t * ((y : G) * d.t) * d.t⁻¹ = d.t * y * (d.t * d.t⁻¹) := by group
          _ = d.t * y := by rw [mul_inv_cancel, mul_one]
          _ = ((y : G)⁻¹ * d.t)⁻¹ := by rw [_root_.mul_inv_rev, inv_inv, htinv]
      rw [e] at ht
      simpa using inv_mem ht
    change w.projBar y ∈ zpowers w.tbar
    rw [this]
    exact mem_zpowers _

end Levi

end WData

section Generic

open CFSG.LocalAnalysis.EvenBN.GMSK

theorem exists_four_of_mulEquiv_SL2 {H : Type*} [Group H] {J : Subgroup H} {k : Type}
    [Field k] [Fintype k] {n : ℕ} (hn : 2 ≤ n) (hk : Fintype.card k = 2 ^ n)
    (φ : J ≃* Matrix.SpecialLinearGroup (Fin 2) k) :
    ∃ E : Subgroup H, E ≤ J ∧ CFSG.Assembly.IsElemAbelian 2 E ∧ Nat.card E = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 := two_eq_zero_of_card (K := k) (by omega) hk
  obtain ⟨E, hE, hE4⟩ := exists_elementaryAbelian_four h2
    (hk ▸ pow_dvd_pow 2 hn : 2 ^ 2 ∣ Fintype.card k)
  set g : Multiplicative k →* H := J.subtype.comp (φ.symm.toMonoidHom.comp (sl2Upper k))
  have hg : Function.Injective g :=
    J.subtype_injective.comp (φ.symm.injective.comp sl2Upper_injective)
  have hEg : CFSG.IsElementaryAbelian 2 (E.map g) := CFSG.IsElementaryAbelian.map g
  refine ⟨E.map g, ?_, ⟨hEg.toIsMulCommutative, fun x hx =>
    CFSG.elemPow_eq_one_of_isElementaryAbelian x hx⟩, by rw [card_map_of_injective hg, hE4]⟩
  rintro _ ⟨x, -, rfl⟩
  exact (φ.symm (sl2Upper k x)).2

theorem isSimpleGroup_of_mulEquiv_SL2 {H : Type*} [Group H] {J : Subgroup H} {k : Type}
    [Field k] [Fintype k] {n : ℕ} (hn : 2 ≤ n) (hk : Fintype.card k = 2 ^ n)
    (φ : J ≃* Matrix.SpecialLinearGroup (Fin 2) k) : IsSimpleGroup J := by
  have h2 := two_eq_zero_of_card (K := k) (by omega) hk
  have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) k) :=
    sl2_isSimpleGroup h2 (hk ▸ (Nat.pow_le_pow_right (by norm_num) hn : 2 ^ 2 ≤ 2 ^ n))
  exact φ.isSimpleGroup

theorem exists_mul_ne_of_mulEquiv_SL2 {H : Type*} [Group H] {J : Subgroup H} {k : Type}
    [Field k] (φ : J ≃* Matrix.SpecialLinearGroup (Fin 2) k) : ∃ x y : J, x * y ≠ y * x := by
  obtain ⟨x, y, hxy⟩ := sl2_exists_mul_ne (K := k)
  exact ⟨φ.symm x, φ.symm y, fun e => hxy (by simpa using congrArg φ e)⟩

theorem odd_index_of_odd_index_map {X : Type*} [Group X] [Finite X] (R : Subgroup X) [R.Normal]
    (hR : Odd (Nat.card R)) (H : Subgroup X) (hH : ¬ 2 ∣ (H.map (QuotientGroup.mk' R)).index) :
    ¬ 2 ∣ H.index := by
  have h1 := index_map (H := H) (QuotientGroup.mk' R)
  rw [QuotientGroup.ker_mk', (QuotientGroup.mk' R).range_eq_top_of_surjective
    (QuotientGroup.mk'_surjective R), index_top, mul_one] at h1
  have h2 := relIndex_mul_index (le_sup_left : H ≤ H ⊔ R)
  rw [sup_comm, ABGLocalTools.relIndex_sup_eq_relIndex_of_normal R H, sup_comm] at h2
  have h3 : Odd (H.relIndex R) := hR.of_dvd_nat (relIndex_dvd_card H R)
  intro h2dvd
  rw [← h2] at h2dvd
  rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2dvd with h4 | h4
  · exact (Nat.not_even_iff_odd.mpr h3) (even_iff_two_dvd.mpr h4)
  · exact hH (h1 ▸ h4)

end Generic

namespace WData

variable {G : Type} [Group G] {A : Subgroup G} {d : Datum A} {Vi : Subgroup G} {q : ℕ}
variable [Finite G]

open CFSG.LocalAnalysis.EvenBN.GMSK

theorem comap_centralizer_tbar (w : WData d Vi q) (hWV : Vi ≤ d.V) :
    (centralizer ({w.tbar} : Set w.Nbar)).comap w.projBar =
      (normalizer ((Vi ⊔ zpowers d.t : Subgroup G) : Set G)).subgroupOf w.N := by
  ext x
  rw [mem_comap, mem_subgroupOf, mem_centralizer_singleton_iff]
  exact ⟨fun hx => w.mem_normalizer_adj_of_commute hWV hx,
    fun hx => w.commute_of_mem_normalizer_adj hx⟩

theorem lbar_data {f : ℕ} (hf : 3 ≤ f) {V₁ V₂ : Subgroup G}
    (hR : Radicals d.V V₁ V₂ (2 ^ f)) (hW : Vi = V₁ ∨ Vi = V₂)
    (hN : normalizer ((Vi ⊔ zpowers d.t : Subgroup G) : Set G) ≤ normalizer (Vi : Set G))
    (w : WData d Vi (2 ^ f))
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f)
    (D : LeviData A Vi K) :
    IsSimpleGroup (w.Lbar D.lev.range) ∧ (∃ x y : w.Lbar D.lev.range, x * y ≠ y * x) ∧
      (∃ E : Subgroup w.Nbar, E ≤ w.Lbar D.lev.range ∧ CFSG.Assembly.IsElemAbelian 2 E ∧
        Nat.card E = 4) ∧
      orderOf w.tbar = 2 ∧ w.Lbar D.lev.range ≤ centralizer ({w.tbar} : Set w.Nbar) ∧
      ((w.Lbar D.lev.range).subgroupOf (centralizer ({w.tbar} : Set w.Nbar))).Normal ∧
      ∃ S : Sylow 2 ↥(centralizer (w.Lbar D.lev.range : Set w.Nbar) ⊓
          centralizer ({w.tbar} : Set w.Nbar)),
        (S : Subgroup _).map (centralizer (w.Lbar D.lev.range : Set w.Nbar) ⊓
          centralizer ({w.tbar} : Set w.Nbar)).subtype = zpowers w.tbar := by
  have := Fintype.ofFinite K
  have hKc : Fintype.card K = 2 ^ f := by rw [Fintype.card_eq_nat_card, hK]
  have hK3 : 3 ≤ Nat.card K := by
    rw [hK]
    calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact ⟨isSimpleGroup_of_mulEquiv_SL2 (by omega) hKc (w.lbarEquiv D),
    exists_mul_ne_of_mulEquiv_SL2 (w.lbarEquiv D),
    exists_four_of_mulEquiv_SL2 (by omega) hKc (w.lbarEquiv D), w.orderOf_tbar,
    w.Lbar_le_centralizer D, w.Lbar_normal hK3 D, w.exists_sylow_centralizer_Lbar hf hR hW hN D⟩

theorem Ltil_not_normal {f : ℕ} (hf : 3 ≤ f)
    {V₁ V₂ : Subgroup G} (hR : Radicals d.V V₁ V₂ (2 ^ f)) (hW : Vi = V₁ ∨ Vi = V₂)
    (hN : normalizer ((Vi ⊔ zpowers d.t : Subgroup G) : Set G) ≤ normalizer (Vi : Set G))
    (w : WData d Vi (2 ^ f))
    (h26 : ∀ S : Subgroup G,
      IsSylowOf 2 S (normalizer ((Vi ⊔ zpowers d.t : Subgroup G) : Set G)) →
        ¬ IsSylowOf 2 S (normalizer (w.W : Set G)))
    {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2 ^ f) (D : LeviData A Vi K) : ¬ (w.Ltil D.lev.range).Normal := by
  intro hnorm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hWV, -, -⟩ := hR.property hW
  obtain ⟨hsimp, hnab, hE, ht, hJa, hJn, hsyl⟩ := w.lbar_data hf hR hW hN hK D
  obtain ⟨-, -, htt, -, -, -, -, hCt, -, -, ⟨S₀, hS₀⟩, hconj⟩ :=
    CFSG.LocalAnalysis.SteinbergBK.simple_involution_centralizer_odd_normal_quotient_standardness
      hnab hE ht hJa hJn hsyl (standardComponentOddCore w.Nbar)
      (odd_card_standardComponentOddCore _)
  have hsylC : IsSylowOf 2 (zpowers w.ttil) (centralizer (w.Ltil D.lev.range : Set w.Ntil)) :=
    ⟨S₀, hS₀⟩
  set J : Subgroup w.Ntil := w.Ltil D.lev.range with hJ
  set C : Subgroup w.Ntil := centralizer (J : Set w.Ntil) with hC
  have hCn : C.Normal := Subgroup.normal_centralizer
  have httC : w.ttil ∈ C := by
    rw [hC, mem_centralizer_iff]
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, ← map_mul, mem_centralizer_singleton_iff.mp (hJa hx)]
  have htop : C ⊔ centralizer ({w.ttil} : Set w.Ntil) = ⊤ := by
    refine eq_top_iff.mpr fun n _ => ?_
    have hb : n * w.ttil * n⁻¹ ∈ C := hCn.conj_mem _ httC n
    have hb2 : orderOf (n * w.ttil * n⁻¹) = 2 := by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
      exact htt
    obtain ⟨g, hg, hgt⟩ := hconj _ hb hb2
    have hgn : g * n ∈ centralizer ({w.ttil} : Set w.Ntil) := by
      rw [mem_centralizer_singleton_iff]
      calc g * n * w.ttil = g * (n * w.ttil * n⁻¹) * n := by group
        _ = g * (g⁻¹ * w.ttil * g) * n := by rw [hgt]
        _ = w.ttil * (g * n) := by group
    have e : n = g⁻¹ * (g * n) := by group
    rw [e]
    exact mul_mem (mem_sup_left (inv_mem hg)) (mem_sup_right hgn)
  have hodd1 : ¬ 2 ∣ (centralizer ({w.ttil} : Set w.Ntil)).index := by
    have h1 := ABGLocalTools.relIndex_sup_eq_relIndex_of_normal C
      (centralizer ({w.ttil} : Set w.Ntil))
    rw [htop, relIndex_top_right] at h1
    rw [h1]
    have hz : zpowers w.ttil ≤ centralizer ({w.ttil} : Set w.Ntil) :=
      zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl)
    have h2 := (ABGLocalTools.isSylowOf_iff.mp hsylC).2.2
    exact fun h3 => h2 (h3.trans (relIndex_dvd_of_le_left C hz))
  have hodd2 : ¬ 2 ∣ (centralizer ({w.tbar} : Set w.Nbar)).index :=
    odd_index_of_odd_index_map _ (odd_card_standardComponentOddCore _) _
      (by rw [← hCt]; exact hodd1)
  have hodd3 : ¬ 2 ∣ (normalizer ((Vi ⊔ zpowers d.t : Subgroup G) : Set G)).relIndex w.N := by
    rw [Subgroup.relIndex, ← w.comap_centralizer_tbar hWV,
      index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)]
    exact hodd2
  obtain ⟨S, hS⟩ := ABGLocalTools.exists_isSylowOf 2
    (normalizer ((Vi ⊔ zpowers d.t : Subgroup G) : Set G))
  refine h26 S hS
    (ABGLocalTools.isSylowOf_iff.mpr ⟨hS.le.trans w.normal, hS.isPGroup, fun h4 => ?_⟩)
  rw [← relIndex_mul_relIndex S _ w.N hS.le w.normal] at h4
  rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h4 with h5 | h5
  · exact (ABGLocalTools.isSylowOf_iff.mp hS).2.2 h5
  · exact hodd3 h5

omit [Finite G] in
theorem conj_mem_centralizer_W (w : WData d Vi q) {n : G} (hn : n ∈ w.N) {c : G}
    (hc : c ∈ centralizer (w.W : Set G)) : n * c * n⁻¹ ∈ centralizer (w.W : Set G) := by
  rw [mem_centralizer_iff] at hc ⊢
  intro y hy
  have hy' : n⁻¹ * y * n ∈ w.W := by
    have := (mem_normalizer_iff.mp (inv_mem hn) y).mp hy
    simpa using this
  have h1 := hc _ hy'
  calc y * (n * c * n⁻¹) = n * ((n⁻¹ * y * n) * c) * n⁻¹ := by group
    _ = n * (c * (n⁻¹ * y * n)) * n⁻¹ := by rw [h1]
    _ = n * c * n⁻¹ * y := by group

theorem isSylowOf_centralizer_W (w : WData d Vi q) :
    IsSylowOf 2 w.W (centralizer (w.W : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer (w.W : Set G) with hC
  have hWC : w.W ≤ C := fun x hx =>
    mem_centralizer_iff.mpr fun y hy => comm_of_isElemAbelian w.elem hy hx
  have htC : d.t ∈ normalizer (C : Set G) :=
    Subgroup.mem_normalizer_fintype fun x hx => w.conj_mem_centralizer_W w.t_norm hx
  set M : Subgroup G := C ⊔ zpowers d.t with hM
  have hMN : M ≤ normalizer (C : Set G) := sup_le le_normalizer (zpowers_le.mpr htC)
  have hEM : w.W ⊔ zpowers d.t ≤ M := sup_le (hWC.trans le_sup_left) le_sup_right
  obtain ⟨Q, hQ⟩ := (w.isPGroup_sup.comap_subtype (K := M)).exists_le_sylow
  have hQM : IsSylowOf 2 ((Q : Subgroup M).map M.subtype) M := ⟨Q, rfl⟩
  have hEQ : w.W ⊔ zpowers d.t ≤ (Q : Subgroup M).map M.subtype := fun x hx =>
    ⟨⟨x, hEM hx⟩, hQ (mem_subgroupOf.mpr hx), rfl⟩
  have hMV : M ≤ centralizer (Vi : Set G) := by
    refine sup_le (Subgroup.centralizer_le w.le_W) (zpowers_le.mpr ?_)
    exact mem_centralizer_iff.mpr fun v hv => (mem_centralizer_singleton_iff.mp
      (w.le_centralizer_t hv))
  have hQeq := w.isSylowOf_centralizer.eq_of_le hEQ (hQM.le.trans hMV) hQM.isPGroup
  have hinf := hQM.inf_of_le_normalizer le_sup_left hMN
  rw [hQeq] at hinf
  have htW : d.t ∉ C := by
    intro htC'
    have h1 : w.W ≤ centralizer ({d.t} : Set G) := fun x hx =>
      mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp htC' x hx)
    exact w.lt.ne (w.fix.symm.trans (inf_eq_left.mpr h1))
  have heq : (w.W ⊔ zpowers d.t) ⊓ C = w.W := by
    refine le_antisymm (fun x hx => ?_) (le_inf le_sup_left hWC)
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
    rcases w.mem_sup_iff.mp hx1 with h1 | h1
    · exact h1
    · exfalso
      apply htW
      have := mul_mem (inv_mem hx2) (hWC h1)
      rwa [inv_mul_cancel_left] at this
  rwa [heq] at hinf

theorem projTil_projBar_eq_one (w : WData d Vi q) {x : w.N}
    (hx : (x : G) ∈ centralizer (w.W : Set G)) : w.projTil (w.projBar x) = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer (w.W : Set G) with hC
  have hCN : C ≤ w.N := Subgroup.centralizer_le_normalizer _
  have hCn : (C.subgroupOf w.N).Normal := ⟨fun c hc n => by
    rw [mem_subgroupOf] at hc ⊢
    simpa using w.conj_mem_centralizer_W n.2 hc⟩
  have hCbn : ((C.subgroupOf w.N).map w.projBar).Normal :=
    hCn.map _ (QuotientGroup.mk'_surjective _)
  have hodd : Odd (Nat.card ((C.subgroupOf w.N).map w.projBar)) := by
    rw [← relIndex_ker, QuotientGroup.ker_mk', relIndex_subgroupOf hCN]
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp
      (ABGLocalTools.isSylowOf_iff.mp w.isSylowOf_centralizer_W).2.2)
  have hle : (C.subgroupOf w.N).map w.projBar ≤ standardComponentOddCore w.Nbar :=
    le_sSup ⟨hCbn, hodd⟩
  exact (QuotientGroup.eq_one_iff _).mpr (hle ⟨x, mem_subgroupOf.mpr hx, rfl⟩)

theorem card_Ntil_dvd (w : WData d Vi q) :
    Nat.card w.Ntil ∣ Nat.card (MulAut.conjNormal (H := w.WN)).range := by
  set ρ : w.N →* w.Ntil := w.projTil.comp w.projBar with hρ
  have hρs : Function.Surjective ρ :=
    (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
  have hker : (MulAut.conjNormal (H := w.WN)).ker ≤ ρ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    refine w.projTil_projBar_eq_one (mem_centralizer_iff.mpr fun y hy => ?_)
    have h1 := congrArg (fun φ : MulAut w.WN => ((φ ⟨⟨y, w.W_le_N hy⟩, hy⟩ : w.WN) : G)) hx
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h1
    calc y * (x : G) = (x : G) * y * (x : G)⁻¹ * x := by
          rw [show ((x : G) * y * (x : G)⁻¹) = y from by simpa using h1]
      _ = (x : G) * y := by group
  have h2 := index_dvd_of_le hker
  rwa [index_ker, index_ker, ρ.range_eq_top_of_surjective hρs, Subgroup.card_top] at h2

theorem not_lieModel_PSU3 {f : ℕ} (hf : 2 ≤ f) (w : WData d Vi (2 ^ f)) :
    ¬ LieModel (CFSG.layer w.Ntil) .PSU 3 2 f := by
  intro hU
  obtain ⟨e⟩ := exists_mulEquiv_psu3_of_lieModel_PSU3 hU
  have h1 : Nat.card (CFSG.Open.PSU3 2 f) ∣ Nat.card w.Ntil := by
    rw [← Nat.card_congr e.toEquiv]
    exact card_subgroup_dvd_card _
  have hWN : Nat.card w.WN = 2 ^ (4 * f) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe w.W_le_N).toEquiv, w.card, ← pow_mul, mul_comm]
  have := CFSG.CGT.Timmesfeld75.lemma27_psu3 hf (h1.trans w.card_Ntil_dvd)
    (MulAut.conjNormal (H := w.WN)).range.subtype (subtype_injective _) hWN
  omega

omit [Finite G] in
theorem ttil_mem_centralizer (w : WData d Vi q) {K : Type} [Field K] (D : LeviData A Vi K) :
    w.ttil ∈ centralizer (w.Ltil D.lev.range : Set w.Ntil) := by
  rw [mem_centralizer_iff]
  rintro _ ⟨x, hx, rfl⟩
  rw [← map_mul, ← map_mul, mem_centralizer_singleton_iff.mp (w.Lbar_le_centralizer D hx)]

theorem orderOf_ttil (w : WData d Vi q) : orderOf w.ttil = 2 := by
  refine orderOf_eq_prime (by rw [← map_pow, sq, ← sq, ← w.orderOf_tbar, pow_orderOf_eq_one,
    map_one]) fun h1 => ?_
  have hmem : w.tbar ∈ standardComponentOddCore w.Nbar := (QuotientGroup.eq_one_iff _).mp h1
  have hdvd : orderOf w.tbar ∣ Nat.card (standardComponentOddCore w.Nbar) := by
    have := orderOf_dvd_natCard (⟨w.tbar, hmem⟩ : standardComponentOddCore w.Nbar)
    rwa [Subgroup.orderOf_mk] at this
  rw [w.orderOf_tbar] at hdvd
  exact (Nat.not_even_iff_odd.mpr (odd_card_standardComponentOddCore _))
    (even_iff_two_dvd.mpr hdvd)

omit [Finite G] in
theorem N_ne_top [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) {f : ℕ} (hf : 1 ≤ f)
    (w : WData d Vi (2 ^ f)) : w.N ≠ ⊤ := by
  intro htop
  have hn : w.W.Normal := normalizer_eq_top_iff.mp htop
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal w.W with h1 | h1
  · have h2 := w.card
    rw [h1, Subgroup.card_bot] at h2
    have : 1 < (2 ^ f) ^ 4 := Nat.one_lt_pow (by norm_num) (Nat.one_lt_two_pow (by omega))
    omega
  · obtain ⟨a, b, hab⟩ := hnonab
    exact hab (comm_of_isElemAbelian w.elem (h1 ▸ mem_top a) (h1 ▸ mem_top b))

theorem not_two_dvd_relIndex_ttil (w : WData d Vi q) {K : Type} [Field K] (D : LeviData A Vi K)
    (hS : ∀ S : Sylow 2 (centralizer (w.Ltil D.lev.range : Set w.Ntil)), Nat.card S = 2) :
    ¬ 2 ∣ (zpowers w.ttil).relIndex (centralizer (w.Ltil D.lev.range : Set w.Ntil)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer (w.Ltil D.lev.range : Set w.Ntil)
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 C))
  have h1 := Sylow.card_eq_multiplicity S
  rw [hS S] at h1
  refine (ABGLocalTools.isSylowOf_iff.mp (ABGLocalTools.isSylowOf_of_card
    (zpowers_le.mpr (w.ttil_mem_centralizer D)) ?_)).2.2
  rw [Nat.card_zpowers, w.orderOf_ttil, ← h1]

end WData

namespace WData

variable {G : Type} [Group G] {A : Subgroup G} {d : Datum A} {Vi : Subgroup G} {q : ℕ}

structure CaseA (f : ℕ) (w : WData d Vi (2 ^ f)) (L : Subgroup G) : Prop where
  layer : SteinbergBV.OneOrTwoLayerConclusion (w.Ltil L) w.ttil
  simple : IsSimpleGroup (CFSG.layer w.Ntil)
  lt_layer : w.Ltil L < CFSG.layer w.Ntil
  moves : ∃ x ∈ CFSG.layer w.Ntil, w.ttil⁻¹ * x * w.ttil ≠ x
  model : LieModel (CFSG.layer w.Ntil) .PSL 2 2 (2 * f)

structure CaseB (w : WData d Vi q) (L : Subgroup G) : Prop where
  layer : SteinbergBV.OneOrTwoLayerConclusion (w.Ltil L) w.ttil
  factors : ∃ M₁ M₂ : Subgroup w.Ntil, CFSG.IsComponent M₁ ∧ CFSG.IsComponent M₂ ∧ M₁ ≠ M₂ ∧
    IsSimpleGroup M₁ ∧ (∃ x y : M₁, x * y ≠ y * x) ∧
    IsSimpleGroup M₂ ∧ (∃ x y : M₂, x * y ≠ y * x) ∧
    M₁ ⊔ M₂ = CFSG.layer w.Ntil ∧ M₁ ⊓ M₂ = ⊥ ∧ ⁅M₁, M₂⁆ = ⊥ ∧
    M₁.map (MulAut.conj w.ttil⁻¹).toMonoidHom = M₂ ∧
    w.Ltil L = CFSG.layer w.Ntil ⊓ centralizer ({w.ttil} : Set w.Ntil) ∧
    ∃ ψ : CFSG.layer w.Ntil ≃* (w.Ltil L) × (w.Ltil L),
      (∀ (j : w.Ntil) (hjL : j ∈ w.Ltil L) (hjE : j ∈ CFSG.layer w.Ntil),
        ψ ⟨j, hjE⟩ = (⟨j, hjL⟩, ⟨j, hjL⟩)) ∧
      ∀ (x : w.Ntil) (hx : x ∈ CFSG.layer w.Ntil) (hxt : w.ttil⁻¹ * x * w.ttil ∈ CFSG.layer w.Ntil),
        ψ ⟨w.ttil⁻¹ * x * w.ttil, hxt⟩ = (ψ ⟨x, hx⟩).swap

end WData

@[expose] def LinearThreeExclusion27 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (f : ℕ), Hyp G A f →
    ∀ (d : Datum A) (V₁ V₂ Vi : Subgroup G), Radicals d.V V₁ V₂ (2 ^ f) → (Vi = V₁ ∨ Vi = V₂) →
    ∀ (w : WData d Vi (2 ^ f)) (K : Type) [Field K] [Finite K] (D : LeviData A Vi K),
      Nat.card K = 2 ^ f →
      SteinbergBV.OneOrTwoLayerConclusion (w.Ltil D.lev.range) w.ttil →
      IsSimpleGroup (CFSG.layer w.Ntil) → ¬ LieModel (CFSG.layer w.Ntil) .PSL 3 2 f

@[expose] def G2ThreeExclusion27 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G), Hyp G A 3 →
    ∀ (d : Datum A) (V₁ V₂ Vi : Subgroup G), Radicals d.V V₁ V₂ (2 ^ 3) → (Vi = V₁ ∨ Vi = V₂) →
    ∀ (w : WData d Vi (2 ^ 3)) (K : Type) [Field K] [Finite K] (D : LeviData A Vi K),
      Nat.card K = 2 ^ 3 →
      SteinbergBV.OneOrTwoLayerConclusion (w.Ltil D.lev.range) w.ttil →
      IsSimpleGroup (CFSG.layer w.Ntil) → ¬ LieModel (CFSG.layer w.Ntil) .G2 0 3 1

namespace WData

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {d : Datum A} {Vi : Subgroup G}

open CFSG.LocalAnalysis.EvenBN.GMSK

theorem caseA_or_caseB_of_layerOutcome {f : ℕ} (hf : 3 ≤ f) {V₁ V₂ : Subgroup G}
    (hR : Radicals d.V V₁ V₂ (2 ^ f)) (hW : Vi = V₁ ∨ Vi = V₂)
    (hN : normalizer ((Vi ⊔ zpowers d.t : Subgroup G) : Set G) ≤ normalizer (Vi : Set G))
    (w : WData d Vi (2 ^ f))
    (h26 : ∀ S : Subgroup G,
      IsSylowOf 2 S (normalizer ((Vi ⊔ zpowers d.t : Subgroup G) : Set G)) →
        ¬ IsSylowOf 2 S (normalizer (w.W : Set G)))
    {K : Type} [Field K] [Finite K] (D : LeviData A Vi K) (hKc : Nat.card K = 2 ^ f)
    (hL3 : SteinbergBV.OneOrTwoLayerConclusion (w.Ltil D.lev.range) w.ttil →
      IsSimpleGroup (CFSG.layer w.Ntil) → ¬ LieModel (CFSG.layer w.Ntil) .PSL 3 2 f)
    (hG23 : f = 3 → SteinbergBV.OneOrTwoLayerConclusion (w.Ltil D.lev.range) w.ttil →
      IsSimpleGroup (CFSG.layer w.Ntil) → ¬ LieModel (CFSG.layer w.Ntil) .G2 0 3 1)
    (hout : standardComponentOddCore w.Ntil = ⊥ → StdLinearData w.Ntil (w.Ltil D.lev.range) f →
      (∀ S : Sylow 2 (centralizer (w.Ltil D.lev.range : Set w.Ntil)), Nat.card S = 2) →
      LayerOutcome w.Ntil (w.Ltil D.lev.range) f) :
    w.CaseA f D.lev.range ∨ w.CaseB D.lev.range := by
  have : CharP K 2 :=
    ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two (by omega) hKc
  have := Fintype.ofFinite K
  have hKf : Fintype.card K = 2 ^ f := by rw [Fintype.card_eq_nat_card, hKc]
  have hK3 : 3 ≤ Nat.card K := by
    rw [hKc]
    calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨hstd, hS2⟩ := stdLinearData_odd_quotient (by omega) hKf (w.lbarEquiv D) w.orderOf_tbar
    (w.Lbar_le_centralizer D) (w.Lbar_normal hK3 D)
    (w.exists_sylow_centralizer_Lbar hf hR hW hN D)
    (standardComponentOddCore w.Nbar) (odd_card_standardComponentOddCore _)
    (w.Ltil_not_normal hf hR hW hN h26 hKc D)
  have hO : standardComponentOddCore w.Ntil = ⊥ := standardComponentOddCore_quotient_eq_bot _
  have hlayer := oneOrTwoLayer_of_stdLinearData hO hstd w.orderOf_ttil
    (w.ttil_mem_centralizer D) (w.not_two_dvd_relIndex_ttil D hS2)
  have hout := hout hO hstd hS2
  obtain ⟨-, -, -, hDE, -, halt, -⟩ := id hlayer
  rcases halt with ⟨⟨hDs, -, hAD, hnt⟩, -⟩ |
    ⟨⟨M₁, M₂, hM₁, hM₂, hne, hs₁, hn₁, hs₂, hn₂, hsup, hinf, hcomm, hconj, hJ, ψ, hψ₁, hψ₂⟩, -⟩
  ·
    rw [hDE] at hDs hAD hnt
    have hsimp : IsSimpleGroup (CFSG.layer w.Ntil) := hDs
    refine Or.inl ⟨hlayer, hsimp, hAD, hnt, ?_⟩
    rcases hout with ⟨⟨ψ⟩⟩ | (hA | hU | hL) | ⟨hf2, -⟩ | ⟨hf3, hG2⟩
    · have : Nontrivial (w.Ltil D.lev.range) := by
        have := hstd.isSimpleGroup
        infer_instance
      exact absurd hsimp (not_isSimpleGroup_of_mulEquiv_prod ψ)
    · exact hA
    · exact absurd hU (WData.not_lieModel_PSU3 (by omega) w)
    · exact absurd hL (hL3 hlayer hsimp)
    · omega
    · exact absurd hG2 (hG23 hf3 hlayer hsimp)
  ·
    rw [hDE] at hsup hJ
    refine Or.inr ⟨hlayer, M₁, M₂, hM₁, hM₂, hne, hs₁, hn₁, hs₂, hn₂, hsup, hinf, hcomm, hconj,
      hJ, (MulEquiv.subgroupCongr hDE).symm.trans ψ, fun j hjL hjE => ?_, fun x hx hxt => ?_⟩
    · exact hψ₁ j hjL (hDE ▸ hjE)
    · exact hψ₂ x (hDE ▸ hx) (hDE ▸ hxt)

end WData

namespace Hyp

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {f : ℕ}

open CFSG.LocalAnalysis.EvenBN.GMSK

theorem seitz27 (hG : CFSG.CGT.Timmesfeld75.Goldschmidt1974)
    (hGMS : GMSLinearStandardLayerListKRankOneStatement) (hL3 : LinearThreeExclusion27)
    (hG23 : G2ThreeExclusion27) (hK : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    (h : Hyp G A f) (d : Datum A) {V₁ V₂ Vi : Subgroup G} (hR : Radicals d.V V₁ V₂ (2 ^ f))
    (hW : Vi = V₁ ∨ Vi = V₂) (w : WData d Vi (2 ^ f)) {K : Type} [Field K] [Finite K]
    (D : LeviData A Vi K) (hKc : Nat.card K = 2 ^ f) :
    w.CaseA f D.lev.range ∨ w.CaseB D.lev.range := by
  have := h.simple
  exact w.caseA_or_caseB_of_layerOutcome h.three_le hR hW (h.normalizer_adj_le d hR hW)
    (fun _ hS => h.not_isSylowOf_normalizer hG d hR hW w hS) D hKc
    (hL3 G A f h d V₁ V₂ Vi hR hW w K D hKc)
    (fun hf3 => by subst hf3; exact hG23 G A h d V₁ V₂ Vi hR hW w K D hKc)
    fun hO hstd hS2 => hGMS w.Ntil ((isKGroupCat_of_section_of_kProper hK
      (w.N_ne_top h.nonab (by have := h.three_le; omega)) w.WN).quotient _) hO f
      (w.Ltil D.lev.range) hstd hS2

end Hyp

section Certified

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {f : ℕ}


theorem Hyp.seitz27_of_certificates (hL3 : LinearThreeExclusion27) (hG23 : G2ThreeExclusion27)
    (hK : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G) (h : Hyp G A f) (d : Datum A)
    {V₁ V₂ Vi : Subgroup G} (hR : Radicals d.V V₁ V₂ (2 ^ f)) (hW : Vi = V₁ ∨ Vi = V₂)
    (w : WData d Vi (2 ^ f)) {K : Type} [Field K] [Finite K] (D : LeviData A Vi K)
    (hKc : Nat.card K = 2 ^ f) :
    w.CaseA f D.lev.range ∨ w.CaseB D.lev.range :=
  h.seitz27 CFSG.CGT.Timmesfeld75.goldschmidt1974_of_milestone
    GMSK.gmsLinearStandardLayerListKRankOne hL3 hG23 hK d hR hW w D hKc

end Certified

end CFSG.LocalAnalysis.EvenBN.LinearThree
