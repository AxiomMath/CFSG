module

public import CFSG.LocalAnalysis.EvenBN.U5.LinModelDefs
public import CFSG.LocalAnalysis.EvenBN.U5.LinSec42E

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Blueprint
open CFSG.ABGLocalTools (IsSylowOf)
open scoped commutatorElement

namespace Lin43Out

section Arith

variable {G : Type*} [Group G]

theorem mem_of_two_pow_odd_pow (E : Subgroup G) {z : G} {a m : ℕ} (hz : z ^ 2 ^ a = 1)
    (hm : Odd m) (hzm : z ^ m ∈ E) : z ∈ E := by
  have hk : orderOf z ∣ 2 ^ a := orderOf_dvd_of_pow_eq_one hz
  have hcop : m.Coprime (orderOf z) :=
    Nat.Coprime.coprime_dvd_right hk (Nat.Coprime.pow_right a (Nat.coprime_two_right.2 hm))
  obtain ⟨s, hs⟩ := exists_pow_eq_self_of_coprime hcop
  have := E.pow_mem hzm s
  rwa [hs] at this

theorem comm_mul_central {c c' : G} (hc : c ∈ Subgroup.center G) (hc' : c' ∈ Subgroup.center G)
    (a b : G) : ⁅a * c, b * c'⁆ = ⁅a, b⁆ := by
  have hc1 : ∀ g : G, c * g = g * c := fun g => (Subgroup.mem_center_iff.1 hc g).symm
  have hc2 : ∀ g : G, c' * g = g * c' := fun g => (Subgroup.mem_center_iff.1 hc' g).symm
  calc ⁅a * c, b * c'⁆ = a * (c * b) * c' * c⁻¹ * a⁻¹ * c'⁻¹ * b⁻¹ := by
        simp only [commutatorElement_def]; group
    _ = a * (b * c) * c' * c⁻¹ * a⁻¹ * c'⁻¹ * b⁻¹ := by rw [hc1 b]
    _ = a * b * (c * c') * c⁻¹ * a⁻¹ * c'⁻¹ * b⁻¹ := by group
    _ = a * b * (c' * c) * c⁻¹ * a⁻¹ * c'⁻¹ * b⁻¹ := by rw [hc1 c']
    _ = a * b * (c' * a⁻¹) * c'⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * c') * c'⁻¹ * b⁻¹ := by rw [hc2 a⁻¹]
    _ = ⁅a, b⁆ := by simp only [commutatorElement_def]; group

end Arith

section AutTrivial

variable {Γ : Type*} [Group Γ]

theorem aut_trivial {E N : Subgroup Γ} [E.Normal] (hEN : E ≤ N)
    (hcen : ∀ x ∈ N, ∀ g : Γ, ⁅x, g⁆ ∈ E)
    (hperf : (⊤ : Subgroup Γ) ≤ ⁅(⊤ : Subgroup Γ), (⊤ : Subgroup Γ)⁆ ⊔ E)
    (α : Γ ≃* Γ) (hαE : ∀ e ∈ E, α e ∈ E) (hα : ∀ g : Γ, g⁻¹ * α g ∈ N) (g : Γ) :
    g⁻¹ * α g ∈ E := by
  let T : Subgroup Γ :=
    { carrier := {g | g⁻¹ * α g ∈ E}
      mul_mem' := by
        intro a b ha hb
        have h1 : (a * b)⁻¹ * α (a * b) = (b⁻¹ * (a⁻¹ * α a) * b) * (b⁻¹ * α b) := by
          simp only [map_mul, mul_inv_rev]; group
        show (a * b)⁻¹ * α (a * b) ∈ E
        rw [h1]
        refine E.mul_mem ?_ hb
        have := ‹E.Normal›.conj_mem _ ha b⁻¹
        simpa using this
      one_mem' := by simp
      inv_mem' := by
        intro a ha
        have h1 : (a⁻¹)⁻¹ * α a⁻¹ = a * (a⁻¹ * α a)⁻¹ * a⁻¹ := by
          simp only [map_inv, inv_inv, mul_inv_rev]; group
        show (a⁻¹)⁻¹ * α a⁻¹ ∈ E
        rw [h1]
        exact ‹E.Normal›.conj_mem _ (E.inv_mem ha) a }
  have hET : E ≤ T := fun e he =>
    show e⁻¹ * α e ∈ E from E.mul_mem (E.inv_mem he) (hαE e he)
  have hcomm : ⁅(⊤ : Subgroup Γ), (⊤ : Subgroup Γ)⁆ ≤ T := by
    rw [Subgroup.commutator_le]
    intro a _ b _
    obtain ⟨na, hna, hαa⟩ : ∃ n ∈ N, α a = a * n := ⟨a⁻¹ * α a, hα a, by simp⟩
    obtain ⟨nb, hnb, hαb⟩ : ∃ n ∈ N, α b = b * n := ⟨b⁻¹ * α b, hα b, by simp⟩
    let q : Γ →* Γ ⧸ E := QuotientGroup.mk' E
    have hcentral : ∀ n ∈ N, q n ∈ Subgroup.center (Γ ⧸ E) := by
      intro n hn
      rw [Subgroup.mem_center_iff]
      intro z
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective z
      show ((g * n : Γ) : Γ ⧸ E) = ((n * g : Γ) : Γ ⧸ E)
      rw [QuotientGroup.eq]
      have e : (g * n)⁻¹ * (n * g) = ⁅n⁻¹, g⁻¹⁆ := by
        rw [commutatorElement_def]; group
      rw [e]
      exact hcen n⁻¹ (N.inv_mem hn) g⁻¹
    have hq : q (⁅a, b⁆⁻¹ * α ⁅a, b⁆) = 1 := by
      rw [map_commutatorElement α a b, hαa, hαb]
      simp only [map_mul, map_inv, map_commutatorElement]
      rw [comm_mul_central (hcentral na hna) (hcentral nb hnb), inv_mul_cancel]
    have hmem : ⁅a, b⁆⁻¹ * α ⁅a, b⁆ ∈ E := (QuotientGroup.eq_one_iff _).1 hq
    exact hmem
  have hall : (⊤ : Subgroup Γ) ≤ T := hperf.trans (sup_le hcomm hET)
  exact hall (Subgroup.mem_top g)

end AutTrivial

section Act

variable {G : Type*} [Group G] {L N R : Subgroup G}

@[expose] def conjL (hRL : R ≤ normalizer (L : Set G)) (r : ↥R) : ↥L ≃* ↥L :=
  L.normalizerMonoidHom ⟨(r : G), hRL r.2⟩

theorem conjL_coe (hRL : R ≤ normalizer (L : Set G)) (r : ↥R) (x : ↥L) :
    ((conjL hRL r x : ↥L) : G) = (r : G) * x * (r : G)⁻¹ := rfl

theorem conjL_mul (hRL : R ≤ normalizer (L : Set G)) (r s : ↥R) (x : ↥L) :
    conjL hRL (r * s) x = conjL hRL r (conjL hRL s x) :=
  Subtype.ext (by simp only [conjL_coe, Subgroup.coe_mul, mul_inv_rev]; group)

theorem conjL_one (hRL : R ≤ normalizer (L : Set G)) (x : ↥L) : conjL hRL 1 x = x :=
  Subtype.ext (by simp only [conjL_coe, Subgroup.coe_one]; group)

theorem map_conjL (hRL : R ≤ normalizer (L : Set G))
    (hRN : ∀ r ∈ R, ∀ n ∈ N, r * n * r⁻¹ ∈ N) (r : ↥R) :
    (N.subgroupOf L).map (conjL hRL r : ↥L ≃* ↥L).toMonoidHom = N.subgroupOf L := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : (x : G) ∈ N := hx
    show ((conjL hRL r x : ↥L) : G) ∈ N
    rw [conjL_coe]
    exact hRN r r.2 x hx'
  · intro hy
    have hy' : (y : G) ∈ N := hy
    refine ⟨conjL hRL r⁻¹ y, ?_, ?_⟩
    · show ((conjL hRL r⁻¹ y : ↥L) : G) ∈ N
      rw [conjL_coe]
      exact hRN ((r⁻¹ : ↥R) : G) (r⁻¹).2 y hy'
    · show conjL hRL r (conjL hRL r⁻¹ y) = y
      rw [← conjL_mul, mul_inv_cancel, conjL_one]

variable [(N.subgroupOf L).Normal]

@[expose] def outAct (hRL : R ≤ normalizer (L : Set G)) (hRN : ∀ r ∈ R, ∀ n ∈ N, r * n * r⁻¹ ∈ N) :
    ↥R →* MulAut (↥L ⧸ N.subgroupOf L) where
  toFun r := QuotientGroup.congr (N.subgroupOf L) (N.subgroupOf L) (conjL hRL r)
    (map_conjL hRL hRN r)
  map_one' := by
    refine MulEquiv.ext fun z => ?_
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
    show ((conjL hRL 1 x : ↥L) : ↥L ⧸ N.subgroupOf L) = (x : ↥L ⧸ N.subgroupOf L)
    rw [conjL_one]
  map_mul' r s := by
    refine MulEquiv.ext fun z => ?_
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
    show ((conjL hRL (r * s) x : ↥L) : ↥L ⧸ N.subgroupOf L) =
      ((conjL hRL r (conjL hRL s x) : ↥L) : ↥L ⧸ N.subgroupOf L)
    rw [conjL_mul]

theorem outAct_mk (hRL : R ≤ normalizer (L : Set G))
    (hRN : ∀ r ∈ R, ∀ n ∈ N, r * n * r⁻¹ ∈ N) (r : ↥R) (x : ↥L) :
    outAct hRL hRN r (x : ↥L ⧸ N.subgroupOf L) =
      ((conjL hRL r x : ↥L) : ↥L ⧸ N.subgroupOf L) := rfl

theorem outAct_of_mem (hRL : R ≤ normalizer (L : Set G))
    (hRN : ∀ r ∈ R, ∀ n ∈ N, r * n * r⁻¹ ∈ N) (r : ↥R) (hr : (r : G) ∈ L) :
    outAct hRL hRN r = MulAut.conj ((⟨(r : G), hr⟩ : ↥L) : ↥L ⧸ N.subgroupOf L) := by
  refine MulEquiv.ext fun z => ?_
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
  have h1 : (MulAut.conj ((⟨(r : G), hr⟩ : ↥L) : ↥L ⧸ N.subgroupOf L) :
      MulAut (↥L ⧸ N.subgroupOf L)) (x : ↥L ⧸ N.subgroupOf L) =
      (((⟨(r : G), hr⟩ : ↥L) * x * (⟨(r : G), hr⟩ : ↥L)⁻¹ : ↥L) : ↥L ⧸ N.subgroupOf L) := rfl
  rw [h1, outAct_mk]
  exact congrArg (fun a : ↥L => (a : ↥L ⧸ N.subgroupOf L)) (Subtype.ext (by simp [conjL_coe]))

end Act

section Inner

variable {G : Type*} [Group G] {L E N R : Subgroup G}

structure OutCtx (L E N R : Subgroup G) : Prop where
  EL : E ≤ L
  LE : L ≤ normalizer (E : Set G)
  EN : E ≤ N
  NL : N ≤ L
  LN : L ≤ normalizer (N : Set G)
  cen : ∀ x ∈ N, ∀ y ∈ L, ⁅x, y⁆ ∈ E
  perf : L ≤ ⁅L, L⁆ ⊔ E
  odd : Odd (E.relIndex (centralizerSection L E))
  RL : R ≤ normalizer (L : Set G)
  RE : R ≤ normalizer (E : Set G)
  RN : ∀ r ∈ R, ∀ n ∈ N, r * n * r⁻¹ ∈ N
  R2 : IsPGroup 2 R

theorem E_le_C (hEL : E ≤ L) (hLE : L ≤ normalizer (E : Set G)) :
    E ≤ centralizerSection L E := by
  intro e he
  refine ⟨le_normalizer (hEL he), le_normalizer he, fun g hg => ?_⟩
  have h1 : g⁻¹ * (e * g * e⁻¹) = (g⁻¹ * e * g) * e⁻¹ := by group
  rw [h1]
  have h2 := (mem_normalizer_iff.1 (hLE (L.inv_mem hg)) e).1 he
  rw [inv_inv] at h2
  exact E.mul_mem h2 (E.inv_mem he)

theorem pow_relIndex_mem (hEL : E ≤ L) (hLE : L ≤ normalizer (E : Set G)) {y : G}
    (hy : y ∈ centralizerSection L E) : y ^ E.relIndex (centralizerSection L E) ∈ E := by
  have hCE : centralizerSection L E ≤ normalizer (E : Set G) := fun c hc => hc.2.1
  haveI : (E.subgroupOf (centralizerSection L E)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (E_le_C hEL hLE)).2 hCE
  have h1 := Subgroup.pow_index_mem (E.subgroupOf (centralizerSection L E)) ⟨y, hy⟩
  have h2 : ((⟨y, hy⟩ ^ E.relIndex (centralizerSection L E) : ↥(centralizerSection L E)) : G) ∈ E :=
    h1
  rwa [Subgroup.coe_pow] at h2

theorem mem_L_of_inner (h : OutCtx L E N R) {r : G} (hr : r ∈ R) (x : ↥L)
    (hx : ∀ g : ↥L, ((x * g * x⁻¹ : ↥L) : G)⁻¹ * (r * (g : G) * r⁻¹) ∈ N) : r ∈ L := by
  have hxL : (x : G) ∈ L := x.2
  have hyL : (x : G)⁻¹ * r ∈ normalizer (L : Set G) :=
    mul_mem (inv_mem (le_normalizer hxL)) (h.RL hr)
  have hyE : (x : G)⁻¹ * r ∈ normalizer (E : Set G) :=
    mul_mem (inv_mem (h.LE hxL)) (h.RE hr)
  haveI hEn : (E.subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.EL).2 h.LE
  let α : ↥L ≃* ↥L := L.normalizerMonoidHom ⟨(x : G)⁻¹ * r, hyL⟩
  have hαcoe : ∀ g : ↥L, ((α g : ↥L) : G) = ((x : G)⁻¹ * r) * g * ((x : G)⁻¹ * r)⁻¹ :=
    fun g => rfl
  have hEN' : E.subgroupOf L ≤ N.subgroupOf L := fun e he => h.EN he
  have hcen' : ∀ x' ∈ N.subgroupOf L, ∀ g : ↥L, ⁅x', g⁆ ∈ E.subgroupOf L :=
    fun x' hx' g => h.cen x' hx' g g.2
  have hperf' : (⊤ : Subgroup ↥L) ≤ ⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆ ⊔ E.subgroupOf L := by
    intro g _
    have hmap : (⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆ ⊔ E.subgroupOf L).map L.subtype =
        ⁅L, L⁆ ⊔ E := by
      rw [Subgroup.map_sup, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 h.EL]
    have h1 : L.subtype g ∈
        (⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆ ⊔ E.subgroupOf L).map L.subtype := by
      rw [hmap]
      exact h.perf g.2
    exact (Subgroup.mem_map_iff_mem L.subtype_injective).1 h1
  have hαE' : ∀ e ∈ E.subgroupOf L, α e ∈ E.subgroupOf L := fun e he =>
    (mem_normalizer_iff.1 hyE e).1 he
  have hα' : ∀ g : ↥L, g⁻¹ * α g ∈ N.subgroupOf L := by
    intro g
    have h1 := hx g
    have h2 : (x : G)⁻¹ * (((x * g * x⁻¹ : ↥L) : G)⁻¹ * (r * (g : G) * r⁻¹)) *
        ((x : G)⁻¹)⁻¹ ∈ N := (mem_normalizer_iff.1 (h.LN (L.inv_mem hxL)) _).1 h1
    show ((g⁻¹ * α g : ↥L) : G) ∈ N
    have e : ((g⁻¹ * α g : ↥L) : G) = (x : G)⁻¹ *
        (((x * g * x⁻¹ : ↥L) : G)⁻¹ * (r * (g : G) * r⁻¹)) * ((x : G)⁻¹)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hαcoe]
      group
    rw [e]
    exact h2
  have hall : ∀ g : ↥L, g⁻¹ * α g ∈ E.subgroupOf L :=
    aut_trivial (E := E.subgroupOf L) (N := N.subgroupOf L) hEN' hcen' hperf' α hαE' hα'
  have hyC : (x : G)⁻¹ * r ∈ centralizerSection L E := by
    refine ⟨hyL, hyE, fun g hg => ?_⟩
    have h3 := hall ⟨g, hg⟩
    exact h3
  have hym := pow_relIndex_mem h.EL h.LE hyC
  haveI : (L.subgroupOf (normalizer (L : Set G))).Normal := Subgroup.normal_in_normalizer
  let q : ↥(normalizer (L : Set G)) →*
      ↥(normalizer (L : Set G)) ⧸ L.subgroupOf (normalizer (L : Set G)) := QuotientGroup.mk' _
  let rB : ↥(normalizer (L : Set G)) := ⟨r, h.RL hr⟩
  let xB : ↥(normalizer (L : Set G)) := ⟨(x : G), le_normalizer hxL⟩
  let yB : ↥(normalizer (L : Set G)) := ⟨(x : G)⁻¹ * r, hyL⟩
  have hrB : rB = xB * yB := Subtype.ext (by simp [rB, xB, yB])
  have hqx : q xB = 1 := (QuotientGroup.eq_one_iff xB).2 (Subgroup.mem_subgroupOf.2 hxL)
  have hq1 : q rB = q yB := by rw [hrB, map_mul, hqx, one_mul]
  have hqm : (q yB) ^ E.relIndex (centralizerSection L E) = 1 := by
    rw [← map_pow]
    refine (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 (h.EL hym))
  obtain ⟨a, ha⟩ := h.R2 ⟨r, hr⟩
  have h2a : r ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
  have hz : (q rB) ^ 2 ^ a = 1 := by
    rw [← map_pow]
    have : rB ^ 2 ^ a = 1 := Subtype.ext (by simpa [rB] using h2a)
    rw [this, map_one]
  have hq0 : q rB ∈ (⊥ : Subgroup _) :=
    mem_of_two_pow_odd_pow ⊥ hz h.odd (by rw [hq1, hqm]; exact one_mem _)
  have hq00 : q rB = 1 := hq0
  exact Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff rB).1 hq00)

end Inner

section Count

variable {G : Type} [Group G] {L E N R : Subgroup G} [(N.subgroupOf L).Normal]

theorem inner_iff (h : OutCtx L E N R) (r : ↥R) :
    outAct h.RL h.RN r ∈ (MulAut.conj : (↥L ⧸ N.subgroupOf L) →*
      MulAut (↥L ⧸ N.subgroupOf L)).range ↔ (r : G) ∈ L := by
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
    refine mem_L_of_inner h r.2 x (fun g => ?_)
    have h1 : ((x * g * x⁻¹ : ↥L) : ↥L ⧸ N.subgroupOf L) =
        ((conjL h.RL r g : ↥L) : ↥L ⧸ N.subgroupOf L) :=
      congrArg (fun σ : MulAut (↥L ⧸ N.subgroupOf L) => σ (g : ↥L ⧸ N.subgroupOf L)) hz
    have h3 : (x * g * x⁻¹ : ↥L)⁻¹ * conjL h.RL r g ∈ N.subgroupOf L := QuotientGroup.eq.1 h1
    exact h3
  · intro hrL
    exact ⟨_, (outAct_of_mem h.RL h.RN r hrL).symm⟩

variable [Finite G]

theorem card_le_four_inf (h : OutCtx L E N R) (hF7 : LinCase.L3FixedStatement) {f : ℕ}
    (hf : 1 ≤ f) (hX : LieModel (↥L ⧸ N.subgroupOf L) .PSL 3 2 (2 * f)) {Y : Subgroup G}
    (hYR : Y ≤ R) (hY : CFSG.IsElementaryAbelian 2 Y) :
    Nat.card Y ≤ 4 * Nat.card (Y ⊓ L : Subgroup G) := by
  let fY : ↥Y →* MulAut (↥L ⧸ N.subgroupOf L) :=
    (outAct h.RL h.RN).comp (Subgroup.inclusion hYR)
  have hA : CFSG.IsElementaryAbelian 2 fY.range := by
    have h1 : CFSG.IsElementaryAbelian 2 (Y.subgroupOf R) :=
      CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mp
        ((CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mpr hY).subgroupOf R)
    have h2 := h1.subgroup_map (outAct h.RL h.RN)
    have h3 : fY.range = (Y.subgroupOf R).map (outAct h.RL h.RN) := by
      rw [MonoidHom.range_comp, Subgroup.inclusion_range]
    rw [h3]
    exact h2
  have hF := (hF7 f hf _ hX).1 fY.range hA
  have hcomap : (MulAut.conj : (↥L ⧸ N.subgroupOf L) →*
      MulAut (↥L ⧸ N.subgroupOf L)).range.comap fY = (Y ⊓ L).subgroupOf Y := by
    ext y
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    show outAct h.RL h.RN (Subgroup.inclusion hYR y) ∈ (MulAut.conj : (↥L ⧸ N.subgroupOf L) →*
      MulAut (↥L ⧸ N.subgroupOf L)).range ↔ (y : G) ∈ Y ⊓ L
    rw [inner_iff h]
    exact ⟨fun hy => ⟨y.2, hy⟩, fun hy => hy.2⟩
  have hidx : ((Y ⊓ L).subgroupOf Y).index = (MulAut.conj : (↥L ⧸ N.subgroupOf L) →*
      MulAut (↥L ⧸ N.subgroupOf L)).range.relIndex fY.range := by
    rw [← hcomap, Subgroup.index_comap]
  have hrel : (MulAut.conj : (↥L ⧸ N.subgroupOf L) →*
      MulAut (↥L ⧸ N.subgroupOf L)).range.relIndex fY.range ≤ 4 := by
    have h1 := Subgroup.relIndex_mul_card (H := (MulAut.conj : (↥L ⧸ N.subgroupOf L) →*
      MulAut (↥L ⧸ N.subgroupOf L)).range) (K := fY.range)
    rw [inf_comm] at h1
    have hpos : 0 < Nat.card (fY.range ⊓ (MulAut.conj : (↥L ⧸ N.subgroupOf L) →*
      MulAut (↥L ⧸ N.subgroupOf L)).range : Subgroup (MulAut (↥L ⧸ N.subgroupOf L))) :=
      Nat.card_pos
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    rw [h1]
    exact hF
  have hcard : Nat.card ((Y ⊓ L).subgroupOf Y) * ((Y ⊓ L).subgroupOf Y).index = Nat.card Y :=
    Subgroup.card_mul_index _
  have hcard2 : Nat.card ((Y ⊓ L).subgroupOf Y) = Nat.card (Y ⊓ L : Subgroup G) := by
    rw [← Subgroup.card_map_of_injective Y.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.2 inf_le_left]
  rw [← hcard, hcard2, hidx]
  calc Nat.card (Y ⊓ L : Subgroup G) * (MulAut.conj : (↥L ⧸ N.subgroupOf L) →*
        MulAut (↥L ⧸ N.subgroupOf L)).range.relIndex fY.range
      ≤ Nat.card (Y ⊓ L : Subgroup G) * 4 := Nat.mul_le_mul_left _ hrel
    _ = 4 * Nat.card (Y ⊓ L : Subgroup G) := mul_comm _ _

theorem card_fix_le (h : OutCtx L E N R) (hF7 : LinCase.L3FixedStatement) {f : ℕ}
    (hf : 1 ≤ f) (hX : LieModel (↥L ⧸ N.subgroupOf L) .PSL 3 2 (2 * f)) {r : G} (hr : r ∈ R)
    (hrL : r ∉ L) {Z : Subgroup G} (hZL : Z ≤ L) (hZ : CFSG.IsElementaryAbelian 2 Z)
    (hfix : ∀ z ∈ Z, r * z = z * r) :
    Nat.card (Z ⊔ E : Subgroup G) ≤ (2 ^ f) ^ 2 * Nat.card E := by
  let rR : ↥R := ⟨r, hr⟩
  have hσ : outAct h.RL h.RN rR ∉ (MulAut.conj : (↥L ⧸ N.subgroupOf L) →*
      MulAut (↥L ⧸ N.subgroupOf L)).range := fun hin => hrL ((inner_iff h rR).1 hin)
  have hZt : CFSG.IsElementaryAbelian 2 (imgSE L N Z) := by
    have h1 : CFSG.IsElementaryAbelian 2 (Z.subgroupOf L) :=
      CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mp
        ((CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mpr hZ).subgroupOf L)
    exact h1.subgroup_map _
  have hfix' : ∀ z ∈ imgSE L N Z, outAct h.RL h.RN rR z = z := by
    rintro _ ⟨x, hx, rfl⟩
    show outAct h.RL h.RN rR (x : ↥L ⧸ N.subgroupOf L) = (x : ↥L ⧸ N.subgroupOf L)
    rw [outAct_mk]
    refine congrArg (fun a : ↥L => (a : ↥L ⧸ N.subgroupOf L)) (Subtype.ext ?_)
    rw [conjL_coe]
    have h1 : r * (x : G) = (x : G) * r := hfix x hx
    show r * (x : G) * r⁻¹ = (x : G)
    rw [h1]
    group
  have hbound := (hF7 f hf _ hX).2 (outAct h.RL h.RN rR) hσ (imgSE L N Z) hZt hfix'
  have hNZ : N ⊓ Z = E ⊓ Z := by
    apply le_antisymm
    · rintro z ⟨hzN, hzZ⟩
      refine ⟨?_, hzZ⟩
      have hzL : z ∈ L := h.NL hzN
      have hzC : z ∈ centralizerSection L E := by
        refine ⟨le_normalizer hzL, h.LE hzL, fun g hg => ?_⟩
        have h1 := h.cen z hzN g⁻¹ (L.inv_mem hg)
        have e : g⁻¹ * (z * g * z⁻¹) = (⁅z, g⁻¹⁆)⁻¹ := by
          rw [commutatorElement_def]; group
        rw [e]
        exact E.inv_mem h1
      have hzm := pow_relIndex_mem h.EL h.LE hzC
      have hz2 : z ^ 2 ^ 1 = 1 := by
        have := (CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mpr hZ).2 z hzZ
        simpa using this
      exact mem_of_two_pow_odd_pow E hz2 h.odd hzm
    · exact inf_le_inf_right _ h.EN
  have hcard1 := lin_card_image_mul L N Z hZL
  rw [hNZ] at hcard1
  have hcard2 := Common.card_sup_mul_card_inf_eq (A := E) (B := Z) (hZL.trans h.LE)
  have hk : 0 < Nat.card (E ⊓ Z : Subgroup G) := Nat.card_pos
  have heq : Nat.card (E ⊔ Z : Subgroup G) = Nat.card E * Nat.card (imgSE L N Z) := by
    refine Nat.eq_of_mul_eq_mul_right hk ?_
    calc Nat.card (E ⊔ Z : Subgroup G) * Nat.card (E ⊓ Z : Subgroup G)
        = Nat.card E * Nat.card Z := hcard2
      _ = Nat.card E * (Nat.card (imgSE L N Z) * Nat.card (E ⊓ Z : Subgroup G)) := by
        rw [hcard1]
      _ = Nat.card E * Nat.card (imgSE L N Z) * Nat.card (E ⊓ Z : Subgroup G) := by ring
  rw [sup_comm, heq]
  calc Nat.card E * Nat.card (imgSE L N Z) ≤ Nat.card E * (2 ^ f) ^ 2 :=
        Nat.mul_le_mul_left _ hbound
    _ = (2 ^ f) ^ 2 * Nat.card E := mul_comm _ _

end Count

end Lin43Out

end CFSG.LocalAnalysis.EvenBN.U5
