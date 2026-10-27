module

public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB41Main
public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB42Abs
public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB42P
public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB42Coord
public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseAClose2

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.LocalAnalysis.ComponentInitial.FieldFourCover
open scoped commutatorElement

theorem isSylowOf_ge_of_normal {G : Type} [Group G] [Finite G] {T U Y : Subgroup G}
    (h : IsSylowOf 2 T U) (hYU : Y ≤ U) (hY : IsPGroup 2 Y)
    (hN : U ≤ normalizer (Y : Set G)) : Y ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, rfl⟩ := h
  have hnorm : (Y.subgroupOf U).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYU).mpr hN
  have hY' : IsPGroup 2 (Y.subgroupOf U) := hY.comap_subtype
  calc Y = (Y.subgroupOf U).map U.subtype := (Subgroup.map_subgroupOf_eq_of_le hYU).symm
    _ ≤ P.toSubgroup.map U.subtype := Subgroup.map_mono (hY'.le_sylow_of_normal P)

section Seitz

variable {G : Type} [Group G] [Finite G] {A R : Subgroup G} {t : G}

theorem CaseB.P_le_Ninf (c : CaseB A R t) : c.P ≤ c.Ninf :=
  le_prOf c.H.hP.perfect c.P_le_N

theorem CaseB.V_le_P (h : Hyp G A) (d : Datum A)
    {R' : Subgroup G} (hR : Radicals d.V R R') (c : CaseB A R d.t) : d.V ≤ c.P := by
  have hRA : R ≤ A := hR.le₁.trans inf_le_right
  refine c.H.hP.le_of_sylow hRA (fun r hr s hs => ?_) hR.card₁ d.V_isSylow (h.card_V d) ?_
  · exact comm_of_isElemAbelian_two hR.elem₁ hr hs
  · intro v hv
    refine Subgroup.mem_normalizer_fintype fun r hr => ?_
    have h1 := hR.normal₁.conj_mem ⟨r, hR.le₁ hr⟩ (mem_subgroupOf.mpr hr) ⟨v, hv⟩
    exact mem_subgroupOf.mp h1

theorem CaseB.V_le_Ninf (h : Hyp G A) (d : Datum A)
    {R' : Subgroup G} (hR : Radicals d.V R R') (c : CaseB A R d.t) : d.V ≤ c.Ninf :=
  (c.V_le_P h d hR).trans c.P_le_Ninf

theorem CaseB.exists_prod2 (h : Hyp G A) (d : Datum A)
    {R' : Subgroup G} (hR : Radicals d.V R R') (c : CaseB A R d.t) {M₁ M₂ : Subgroup G}
    (F : c.Factors M₁ M₂) : ∃ S : Subgroup G, Prod2 M₁ M₂ S d.V d.t := by
  have hVN : d.V ≤ c.Ninf := c.V_le_Ninf h d hR
  have hQP : d.V ⊔ zpowers d.t ≤ d.P :=
    sup_le inf_le_left (zpowers_le.mpr d.t_mem_P)
  have hQ2 : IsPGroup 2 (d.V ⊔ zpowers d.t : Subgroup G) := d.hP.isPGroup.to_le hQP
  have htN : d.t ∈ normalizer (c.Ninf : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun m hm => ?_
    exact prOf_conj_le d.t (fun y hy => c.N.mul_mem (c.N.mul_mem c.t_mem_N hy)
      (c.N.inv_mem c.t_mem_N)) hm
  have hQN : d.V ⊔ zpowers d.t ≤ normalizer (c.Ninf : Set G) :=
    sup_le (hVN.trans Subgroup.le_normalizer) (zpowers_le.mpr htN)
  have hQL : ∀ q ∈ d.V ⊔ zpowers d.t, ∀ l ∈ c.Ninf, q * l * q⁻¹ ∈ c.Ninf :=
    fun q hq l hl => (mem_normalizer_iff.mp (hQN hq) l).mp hl
  obtain ⟨S, hS, hVS, hSinv⟩ :=
    exists_sylow_invariant hQ2 hQL le_sup_left hVN
  refine ⟨S, ?_⟩
  exact
    { odd2 := ⟨fun x hx m hm => F.norm₁ x (F.ninf_eq ▸ hx) m hm,
        fun x hx m hm => F.norm₂ x (F.ninf_eq ▸ hx) m hm, F.odd_inf⟩
      t_sq := c.t_mul_self
      swap₁ := F.swap₁
      swap₂ := F.swap₂
      sylow := F.ninf_eq ▸ hS
      inv := fun s hs => hSinv d.t (mem_sup_right (mem_zpowers d.t)) s hs
      V_le := hVS
      V_comm := fun v hv => d.V_comm_t hv
      card_V := h.card_V d
      card₁ := F.sylow_card₁ }

variable {M₁ M₂ S V : Subgroup G}

theorem CaseB.inf_le_S (c : CaseB A R t) (F : c.Factors M₁ M₂) (P : Prod2 M₁ M₂ S V t) :
    c.W ⊓ M₁ ≤ S ⊓ M₁ ∧ c.W ⊓ M₂ ≤ S ⊓ M₂ := by
  have hW2 : IsPGroup 2 c.W := IsPGroup.of_card (n := 8) c.W_card
  have hN : ∀ m ∈ M₁ ⊔ M₂, m ∈ c.N := by
    intro m hm
    rw [← F.ninf_eq] at hm
    exact prOf_le c.N hm
  constructor
  · refine isSylowOf_ge_of_normal P.sylow₁ inf_le_right hW2.to_inf_left ?_
    intro m hm
    refine Subgroup.mem_normalizer_fintype fun y hy => ⟨?_, F.norm₁ m
      (F.ninf_eq ▸ mem_sup_left hm) y hy.2⟩
    exact (mem_normalizer_iff.mp (hN m (mem_sup_left hm)) y).mp hy.1
  · refine isSylowOf_ge_of_normal P.sylow₂ inf_le_right hW2.to_inf_left ?_
    intro m hm
    refine Subgroup.mem_normalizer_fintype fun y hy => ⟨?_, F.norm₂ m
      (F.ninf_eq ▸ mem_sup_right hm) y hy.2⟩
    exact (mem_normalizer_iff.mp (hN m (mem_sup_right hm)) y).mp hy.1

theorem CaseB.W_le_S (c : CaseB A R t) (F : c.Factors M₁ M₂) (P : Prod2 M₁ M₂ S V t) :
    c.W ≤ S := by
  rw [← F.W_eq]
  exact sup_le ((c.inf_le_S F P).1.trans inf_le_left) ((c.inf_le_S F P).2.trans inf_le_left)

theorem CaseB.diag_mem_R_iff (c : CaseB A R t) (F : c.Factors M₁ M₂) (P : Prod2 M₁ M₂ S V t)
    {a : G} (ha : a ∈ S ⊓ M₁) : a * (t * a * t⁻¹) ∈ R ↔ a ∈ c.W := by
  constructor
  · intro hR
    have hRW : a * (t * a * t⁻¹) ∈ c.W := c.R_le_W hR
    rw [← F.W_eq] at hRW
    have hWc : ∀ x ∈ c.W ⊓ M₁, ∀ y ∈ c.W ⊓ M₂, x * y = y * x :=
      fun x hx y hy => comm_of_isElemAbelian_two c.W_elem hx.1 hy.1
    obtain ⟨f₁, hf₁, f₂, hf₂, hff⟩ := mem_sup_of_forall_comm hWc hRW
    have hf₁A : f₁ ∈ S ⊓ M₁ := (c.inf_le_S F P).1 hf₁
    have hf₂B : f₂ ∈ S ⊓ M₂ := (c.inf_le_S F P).2 hf₂
    have h1 : f₁⁻¹ * a = f₂ * (t * a * t⁻¹)⁻¹ := by
      calc f₁⁻¹ * a = f₁⁻¹ * (a * (t * a * t⁻¹)) * (t * a * t⁻¹)⁻¹ := by group
        _ = f₁⁻¹ * (f₁ * f₂) * (t * a * t⁻¹)⁻¹ := by rw [← hff]
        _ = f₂ * (t * a * t⁻¹)⁻¹ := by group
    have hmem : f₁⁻¹ * a ∈ (S ⊓ M₁) ⊓ (S ⊓ M₂) := by
      refine ⟨(S ⊓ M₁).mul_mem ((S ⊓ M₁).inv_mem hf₁A) ha, ?_⟩
      rw [h1]
      exact (S ⊓ M₂).mul_mem hf₂B ((S ⊓ M₂).inv_mem (P.swap_A ha))
    rw [P.inf_AB, Subgroup.mem_bot] at hmem
    have : a = f₁ := (inv_mul_eq_one.mp hmem).symm
    rw [this]
    exact hf₁.1
  · intro haW
    have hat : t * a * t⁻¹ ∈ c.W := (mem_normalizer_iff.mp c.t_mem_N a).mp haW
    have hmem : a * (t * a * t⁻¹) ∈ c.W ⊓ centralizer ({t} : Set G) :=
      ⟨c.W.mul_mem haW hat, mem_centralizer_singleton_iff.mpr (P.diag_mem ha).2⟩
    rw [c.W_inf_centralizer_t] at hmem
    exact hmem

theorem CaseB.exists_coord (h : Hyp G A) (d : Datum A)
    {R' : Subgroup G} (hR : Radicals d.V R R') (c : CaseB A R d.t) {M₁ M₂ S : Subgroup G}
    (F : c.Factors M₁ M₂) (P : Prod2 M₁ M₂ S d.V d.t) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = 4 ∧
      ∃ e : ↥(S ⊓ M₁) ≃* ↥(unipAll k),
        (∀ a : ↥(S ⊓ M₁), (a : G) ∈ c.W ↔ e a ∈ radOne k) ∧
        (∀ a : ↥(S ⊓ M₁), (a : G) * (d.t * a * d.t⁻¹) ∈ R ↔ e a ∈ radOne k) ∧
        (∀ a : ↥(S ⊓ M₁), (a : G) * (d.t * a * d.t⁻¹) ∈ R' ↔ e a ∈ radTwo k) := by
  obtain ⟨k, _, _, hk, ⟨φ⟩⟩ := h.exists_equiv_unip_V d
  obtain ⟨φ', hφR, hφR'⟩ := exists_equiv_radicals hk φ hR.le₁ hR.le₂ hR.elem₁ hR.elem₂
    hR.card₁ hR.card₂ hR.ne
  refine ⟨k, inferInstance, inferInstance, hk, P.deltaEquiv.trans φ', ?_⟩
  have hchar : ∀ (X : Subgroup G) (a : ↥(S ⊓ M₁)),
      (P.deltaEquiv.trans φ') a ∈ (X.subgroupOf d.V).map φ'.toMonoidHom ↔
        (a : G) * (d.t * a * d.t⁻¹) ∈ X := by
    intro X a
    show φ'.toMonoidHom (P.deltaEquiv a) ∈ (X.subgroupOf d.V).map φ'.toMonoidHom ↔ _
    rw [Subgroup.mem_map_iff_mem φ'.injective, mem_subgroupOf]
    rfl
  refine ⟨fun a => ?_, fun a => ?_, fun a => ?_⟩
  · rw [← hφR, hchar R a]
    exact (c.diag_mem_R_iff F P a.2).symm
  · rw [← hφR, hchar R a]
  · rw [← hφR', hchar R' a]

end Seitz

end CFSG.OddStandard.Seitz77
