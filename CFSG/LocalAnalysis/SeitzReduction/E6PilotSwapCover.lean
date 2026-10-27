module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotSwapLift
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotSwapBasic

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.SeitzReduction.F4Pilot (F4Work swapDiagHom swapDiagHom_apply)

section Structure

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K]

variable (e : L ≃* adjointGroup .E6 K) (t : G)

structure SwapFactorCover (N : E6Neighbour) where
  Kc : Subgroup G
  perfect : ⁅Kc, Kc⁆ = Kc
  le_centralizer : Kc.map (MulAut.conj t).toMonoidHom ≤ centralizer (Kc : Set G)
  sup_eq : Kc ⊔ Kc.map (MulAut.conj t).toMonoidHom = neighbourCore e N
  odd_card_inf : Odd (Nat.card (Kc ⊓ Kc.map (MulAut.conj t).toMonoidHom : Subgroup G))
  normalizer_le : ∀ s ∈ centralizer (modelToG e (N.torus K) : Set G), Odd (orderOf s) →
    s ∈ normalizer (Kc : Set G)
  ε : Kc →* N.levi K
  surjective : Function.Surjective ε
  eq_one_iff : ∀ k : Kc, ε k = 1 ↔ (k : G) ∈ Kc.map (MulAut.conj t).toMonoidHom
  diag : ∀ k : Kc, (k : G) * (t * k * t⁻¹) = ((e.symm (ε k : adjointGroup .E6 K) : L) : G)

variable {e t}

end Structure

section Diagonal

variable {G : Type*} [Group G] {A : Subgroup G} {t : G}

theorem swapDiagHom_mem_centralizer (hcomm : A.map (MulAut.conj t).toMonoidHom ≤
      centralizer (A : Set G)) (htt : t * t = 1) (a : A) :
    swapDiagHom hcomm a ∈ centralizer ({t} : Set G) := by
  rw [mem_centralizer_singleton_iff, swapDiagHom_apply]
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hc : (a : G) * (t * a * t⁻¹) = t * a * t⁻¹ * a :=
    mem_centralizer_iff.1 (hcomm ⟨a, a.2, rfl⟩) a a.2
  calc (a : G) * (t * a * t⁻¹) * t = t * a * t⁻¹ * a * t := by rw [hc]
    _ = t * a * t⁻¹ * a * t⁻¹ := by rw [htinv]
    _ = t * (a * (t * a * t⁻¹)) := by rw [htinv]; group

theorem exists_swapDiagHom_mul_of_mem (hcomm : A.map (MulAut.conj t).toMonoidHom ≤
      centralizer (A : Set G)) (htt : t * t = 1) {d : G}
    (hd : d ∈ A ⊔ A.map (MulAut.conj t).toMonoidHom) (hdt : d ∈ centralizer ({t} : Set G)) :
    ∃ c : A, ∃ w ∈ A ⊓ A.map (MulAut.conj t).toMonoidHom, d = swapDiagHom hcomm c * w := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  obtain ⟨a, ha, b, hb, rfl⟩ := swapExists_mul_of_mem_sup hcomm hd
  obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 hb
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hdt ⊢
  have hcom : ∀ x ∈ A, ∀ y ∈ A, Commute x (t * y * t⁻¹) := fun x hx y hy =>
    mem_centralizer_iff.1 (hcomm ⟨y, hy, rfl⟩) x hx
  have h1 : t * (a * (t * c * t⁻¹)) * t⁻¹ = c * (t * a * t⁻¹) := by
    calc t * (a * (t * c * t⁻¹)) * t⁻¹ = (t * a * t⁻¹) * ((t * t) * c * (t * t)⁻¹) := by group
      _ = (t * a * t⁻¹) * c := by rw [htt]; group
      _ = c * (t * a * t⁻¹) := ((hcom c hc a ha).eq).symm
  have h2 : t * (a * (t * c * t⁻¹)) * t⁻¹ = a * (t * c * t⁻¹) := by
    rw [mem_centralizer_singleton_iff] at hdt
    rw [← hdt]
    group
  have hw : c⁻¹ * a = t * (a * c⁻¹) * t⁻¹ := by
    have h3 : c * (t * a * t⁻¹) = a * (t * c * t⁻¹) := h1.symm.trans h2
    calc c⁻¹ * a = c⁻¹ * (a * (t * c * t⁻¹)) * (t * c * t⁻¹)⁻¹ := by group
      _ = c⁻¹ * (c * (t * a * t⁻¹)) * (t * c * t⁻¹)⁻¹ := by rw [h3]
      _ = t * (a * c⁻¹) * t⁻¹ := by group
  have hwA : c⁻¹ * a ∈ A := mul_mem (inv_mem hc) ha
  have hwAt : c⁻¹ * a ∈ A.map (MulAut.conj t).toMonoidHom :=
    ⟨a * c⁻¹, mul_mem ha (inv_mem hc), by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact hw.symm⟩
  refine ⟨⟨c, hc⟩, c⁻¹ * a, Subgroup.mem_inf.2 ⟨hwA, hwAt⟩, ?_⟩
  · rw [swapDiagHom_apply]
    simp only
    have h4 : Commute (t * c * t⁻¹) (c⁻¹ * a) := (hcom _ hwA c hc).symm
    calc a * (t * c * t⁻¹) = c * (c⁻¹ * a) * (t * c * t⁻¹) := by group
      _ = c * ((c⁻¹ * a) * (t * c * t⁻¹)) := by group
      _ = c * ((t * c * t⁻¹) * (c⁻¹ * a)) := by rw [h4.eq]
      _ = c * (t * c * t⁻¹) * (c⁻¹ * a) := by group

theorem swapDiagHom_range_eq (hcomm : A.map (MulAut.conj t).toMonoidHom ≤
      centralizer (A : Set G)) (htt : t * t = 1) {D : Subgroup G} (hDp : ⁅D, D⁆ = D)
    (hD : D ≤ A ⊔ A.map (MulAut.conj t).toMonoidHom) (hDt : D ≤ centralizer ({t} : Set G))
    (hle : (swapDiagHom hcomm).range ≤ D) : (swapDiagHom hcomm).range = D := by
  refine le_antisymm hle (F4Pilot.perfect_le_of_forall_exists_commute hDp hle fun d hd => ?_)
  obtain ⟨c, w, ⟨hwA, hwAt⟩, hdw⟩ := exists_swapDiagHom_mul_of_mem hcomm htt (hD hd) (hDt hd)
  refine ⟨swapDiagHom hcomm c, ⟨c, rfl⟩, w, hdw, fun b hb => ?_⟩
  have hwc : w ∈ centralizer ((A ⊔ A.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) :=
    F4Pilot.centralizer_inf_centralizer_le_centralizer_sup ⟨hcomm hwAt,
      mem_centralizer_iff.2 fun y hy => (mem_centralizer_iff.1 (hcomm hy) w hwA).symm⟩
  exact (mem_centralizer_iff.1 hwc b (hD hb)).symm

theorem swapDiagHom_eq_one_iff (hcomm : A.map (MulAut.conj t).toMonoidHom ≤
      centralizer (A : Set G)) (htt : t * t = 1) {D : Subgroup G}
    (hD : D ≤ A ⊔ A.map (MulAut.conj t).toMonoidHom) (hZ : center D = ⊥)
    (hle : (swapDiagHom hcomm).range ≤ D) (a : A) :
    swapDiagHom hcomm a = 1 ↔ (a : G) ∈ A.map (MulAut.conj t).toMonoidHom := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  constructor
  · intro ha
    rw [swapDiagHom_apply] at ha
    refine ⟨(a : G)⁻¹, inv_mem a.2, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc t * (a : G)⁻¹ * t⁻¹ = (t * a * t⁻¹)⁻¹ := by group
      _ = a := (eq_inv_of_mul_eq_one_left ha).symm
  · intro hat
    have hcen : ∀ x : G, x ∈ A → x ∈ A.map (MulAut.conj t).toMonoidHom →
        x ∈ centralizer ((A ⊔ A.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) :=
      fun x hxA hxAt => F4Pilot.centralizer_inf_centralizer_le_centralizer_sup ⟨hcomm hxAt,
        mem_centralizer_iff.2 fun y hy => (mem_centralizer_iff.1 (hcomm hy) x hxA).symm⟩
    have hta : t * (a : G) * t⁻¹ ∈ A := by
      obtain ⟨b, hb, hba⟩ := hat
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hba
      have hb' : t * (a : G) * t⁻¹ = b := by
        rw [← hba]
        calc t * (t * b * t⁻¹) * t⁻¹ = (t * t) * b * (t * t)⁻¹ := by group
          _ = b := by rw [htt]; group
      rw [hb']
      exact hb
    have hδc : swapDiagHom hcomm a ∈
        centralizer ((A ⊔ A.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) := by
      rw [swapDiagHom_apply]
      exact mul_mem (hcen _ a.2 hat) (hcen _ hta ⟨a, a.2, rfl⟩)
    have hδD : swapDiagHom hcomm a ∈ D := hle ⟨a, rfl⟩
    have hZ' : (⟨_, hδD⟩ : D) ∈ center D := by
      rw [mem_center_iff]
      intro y
      exact Subtype.ext (mem_centralizer_iff.1 hδc y (hD y.2))
    rw [hZ, mem_bot] at hZ'
    exact congrArg Subtype.val hZ'

end Diagonal

section Root

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]

omit
  [Finite G] in
@[expose] noncomputable def swapLeviEquiv (e : L ≃* adjointGroup .E6 K) :
    a5Levi K ≃* rootLeviG e :=
  ((a5Levi K).equivMapOfInjective _ e.symm.injective).trans
    (((a5Levi K).map e.symm.toMonoidHom).equivMapOfInjective _ L.subtype_injective)

omit
  [Finite G] in
theorem coe_swapLeviEquiv (e : L ≃* adjointGroup .E6 K) (x : a5Levi K) :
    ((swapLeviEquiv e x : rootLeviG e) : G) = ((e.symm (x : adjointGroup .E6 K) : L) : G) :=
  rfl

theorem swapPerfect_le_rootLeviG {t : G} {f : ℕ} (hw : F4Work L K t f) (hf : 2 ≤ f)
    (e : L ≃* adjointGroup .E6 K) {P : Subgroup G} (hP : ⁅P, P⁆ = P)
    (hPt : P ≤ centralizer ({t} : Set G)) (hPX : P ≤ centralizer (rootTorusG e : Set G)) :
    P ≤ rootLeviG e := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hw.card_eq
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hw.card_eq
  have hq : 4 ≤ Nat.card K := by
    rw [hw.card_eq]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have htC := hw.mem_centralizer
  set X : Subgroup G := rootTorusG e with hXdef
  set D : Subgroup G := rootLeviG e with hDdef
  have hX : X = (((EPilot.highTorusLine .E6 K).subgroupOf (adjointGroup .E6 K)).map
      e.symm.toMonoidHom).map L.subtype := rfl
  have hDe : D = ((a5Levi K).map e.symm.toMonoidHom).map L.subtype := rfl
  have hOut : Group.IsSolvable (Outer L) :=
    ⟨⟨3, derivedSeries_outer_eq_bot_of_mulEquiv e (exceptional_E_pinned_model_Schreier K).1⟩⟩
  have hPL : P ≤ L := std_perfect_le hw.standard hOut htC hw.orderOf_eq hP hPt
  have hPLX : P ≤ L ⊓ centralizer (X : Set G) := le_inf hPL hPX
  rw [hX, F4Pilot.inf_centralizer_map_symm, centralizer_highTorusLine_eq (Or.inl rfl) hq,
    Subgroup.map_sup, Subgroup.map_sup, ← hX] at hPLX
  have hXD : X ≤ centralizer (D : Set G) := by
    rw [hX, hDe]
    exact le_centralizer_iff.mp
      (F4Pilot.map_map_symm_le_centralizer e highTorusLine_subgroupOf_le_centralizer_perpLevi)
  have hXX : X ≤ centralizer (X : Set G) := by
    rw [hX]
    exact F4Pilot.map_map_symm_le_centralizer e highTorusLine_subgroupOf_le_centralizer_self
  have hXsolv : Group.IsSolvable X := Group.isSolvable_of_comm fun a b =>
    Subtype.ext (mem_centralizer_iff.1 (hXX b.2) a a.2)
  exact perfect_le_of_le_sup (hXD.trans (centralizer_le_normalizer _)) hXsolv hP
    (by rw [sup_comm]; exact hPLX)

theorem nonempty_swapFactorCover_high {t : G} {f : ℕ} (hw : F4Work L K t f) (hf : 2 ≤ f)
    (e : L ≃* adjointGroup .E6 K) (hk : RootSwapKind e t) :
    Nonempty (SwapFactorCover e t .high) := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hw.card_eq
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hw.card_eq
  have htt : t * t = 1 := by rw [← sq, ← hw.orderOf_eq, pow_orderOf_eq_one]
  have htC := hw.mem_centralizer
  obtain ⟨Kc, hc, hodd, hsup, hperf, hnorm⟩ := exists_swapDecomposition_high hw hf e hk
  set D : Subgroup G := rootLeviG e with hDdef
  set δ := swapDiagHom hc with hδ
  have hEX : neighbourCore e .high ≤ centralizer (rootTorusG e : Set G) := by
    rw [neighbourCore_high_eq_perfectCore_rootTorusG]
    exact CFSG.Quasithin.perfectCore_le _
  have htop : ⁅(⊤ : Subgroup Kc), (⊤ : Subgroup Kc)⁆ = (⊤ : Subgroup Kc) := by
    have h1 := commutator_subgroupOf_eq_self (le_refl Kc) hperf
    rwa [subgroupOf_self] at h1
  have hrp : ⁅δ.range, δ.range⁆ = δ.range := by
    rw [MonoidHom.range_eq_map, ← map_commutator, htop]
  have hrt : δ.range ≤ centralizer ({t} : Set G) := by
    rintro _ ⟨k, rfl⟩
    exact swapDiagHom_mem_centralizer hc htt k
  have hrX : δ.range ≤ centralizer (rootTorusG e : Set G) := by
    rintro _ ⟨k, rfl⟩
    rw [swapDiagHom_apply]
    have h1 : (k : G) ∈ neighbourCore e .high := hsup ▸ mem_sup_left k.2
    have h2 : t * (k : G) * t⁻¹ ∈ neighbourCore e .high := hsup ▸ mem_sup_right ⟨k, k.2, rfl⟩
    exact mul_mem (hEX h1) (hEX h2)
  have hle : δ.range ≤ D := swapPerfect_le_rootLeviG hw hf e hrp hrt hrX
  have hDp : ⁅D, D⁆ = D := isPerfect_iff.mp (isQuasisimple_map_a5Levi e).1
  have hDE : D ≤ Kc ⊔ Kc.map (MulAut.conj t).toMonoidHom := by
    rw [hsup, neighbourCore_high_eq_perfectCore_rootTorusG]
    exact CFSG.Quasithin.le_perfectCore_of_perfect
      (F4Pilot.map_map_symm_le_centralizer e highTorusLine_subgroupOf_le_centralizer_perpLevi) hDp
  have hDt : D ≤ centralizer ({t} : Set G) := fun d hd =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htC d (map_subtype_le _ hd))
  have hrange := swapDiagHom_range_eq hc htt hDp hDE hDt hle
  have hZ : center D = ⊥ := center_map_a5Levi_eq_bot e
  obtain ⟨δ', hδ'⟩ : ∃ δ' : Kc →* D, ∀ k, (δ' k : G) = δ k :=
    ⟨δ.codRestrict D fun k => hle ⟨k, rfl⟩, fun _ => rfl⟩
  obtain ⟨ε, hεapp⟩ : ∃ ε : Kc →* E6Neighbour.high.levi K, ∀ k,
      ε k = MulEquiv.subgroupCongr (E6Neighbour.levi_high K).symm ((swapLeviEquiv e).symm (δ' k)) :=
    ⟨((MulEquiv.subgroupCongr (E6Neighbour.levi_high K).symm).toMonoidHom.comp
      (swapLeviEquiv e).symm.toMonoidHom).comp δ', fun _ => rfl⟩
  refine ⟨⟨Kc, hperf, hc, hsup, hodd, ?_, ε, ?_, ?_, ?_⟩⟩
  · intro s hs hso
    rw [E6Neighbour.torus_high] at hs
    exact hnorm s hs hso
  · intro y
    obtain ⟨x, rfl⟩ := (MulEquiv.subgroupCongr (E6Neighbour.levi_high K).symm).surjective y
    obtain ⟨k, hk⟩ : (swapLeviEquiv e x : G) ∈ δ.range := hrange ▸ (swapLeviEquiv e x).2
    refine ⟨k, ?_⟩
    have h1 : δ' k = swapLeviEquiv e x := Subtype.ext ((hδ' k).trans hk)
    rw [hεapp, h1, MulEquiv.symm_apply_apply]
  · intro k
    rw [← swapDiagHom_eq_one_iff hc htt hDE hZ hle k, hεapp, MulEquiv.map_eq_one_iff,
      MulEquiv.map_eq_one_iff, ← hδ']
    exact ⟨fun h1 => by rw [h1]; rfl, fun h1 => Subtype.ext h1⟩
  · intro k
    have h1 : ((ε k : E6Neighbour.high.levi K) : adjointGroup .E6 K) =
        (((swapLeviEquiv e).symm (δ' k) : a5Levi K) : adjointGroup .E6 K) := by
      rw [hεapp, MulEquiv.subgroupCongr_apply]
    have h2 : ((e.symm (((swapLeviEquiv e).symm (δ' k) : a5Levi K) : adjointGroup .E6 K) : L) :
        G) = (δ' k : G) := by
      rw [← coe_swapLeviEquiv, MulEquiv.apply_symm_apply]
    rw [h1, h2, hδ', swapDiagHom_apply]

end Root

end CFSG.SeitzReduction.E6Pilot
