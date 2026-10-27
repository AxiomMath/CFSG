module

public import CFSG.CGT.Timmesfeld75.Sec4TwoSix
public import CFSG.CGT.Timmesfeld75.Sec4Three
public import CFSG.CGT.Timmesfeld75.Sec4CaseIKernel
public import CFSG.CGT.Timmesfeld75.Sec4CaseIJIdent
public import CFSG.CGT.Timmesfeld75.Sec3Thirteen
public import CFSG.CGT.Timmesfeld75.Sec4NoAAssembly
public import CFSG.CGT.T75B.QuotAut
import CFSG.Timmesfeld.Bridge.Asc72Bender
public import CFSG.CGT.Timmesfeld75.Sec3TenCaseA
public import CFSG.CGT.Timmesfeld75.Sec4CaseIBasic
public import CFSG.CGT.Timmesfeld75.Sec4CaseIIIFour
public import CFSG.CGT.Timmesfeld75.Sec4CaseIJFamily
public import CFSG.CGT.Timmesfeld75.Sec4CaseIPGroup
public import CFSG.CGT.Timmesfeld75.Sec4CaseIPartition4
public import CFSG.CGT.Timmesfeld75.Sec5FiveEng
public import CFSG.CGT.Timmesfeld75.Step511Card
public import CFSG.CGT.Timmesfeld75.Step57Reduction
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
public import CFSG.Permutation.BurnsideSchur
public import CFSG.Timmesfeld.Moufang.Three
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Special.TwoCore

public section

namespace CFSG.CGT.T75B

open CFSG.Open CFSG.CGT.Timmesfeld75 CFSG.BenderSuzuki
open scoped commutatorElement

section Bender

variable {B : Type*} [Group B] [Finite B]

theorem eq_center_sylow_of_strongWC (hB : IsBenderGroup B) {T' : Subgroup B} (hT' : StrongWC T')
    (hbot : T' ≠ ⊥) {Q : Sylow 2 B} (hTQ : T' ≤ (Q : Subgroup B)) :
    T' = (Subgroup.center (Q : Subgroup B)).map (Q : Subgroup B).subtype := by
  obtain ⟨⟨x, hxT⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hbot
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hcomm : ∀ t ∈ T', ∀ q ∈ (Q : Subgroup B), Commute t q := fun t ht q hq =>
    CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.commute_of_mul_self_eq_one hB Q (hTQ ht)
      (by rw [← pow_two]; exact hT'.1.2 t ht) q hq
  apply le_antisymm
  · intro t ht
    refine ⟨⟨t, hTQ ht⟩, Subgroup.mem_center_iff.2 fun q => ?_, rfl⟩
    exact Subtype.ext (hcomm t ht q q.2).symm.eq
  · rintro _ ⟨z, hz, rfl⟩
    refine mem_of_commute_sylow_of_strongWC hB hT' hxT hx1' Q hTQ z.2 fun q hq => ?_
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨q, hq⟩)

end Bender

section Quot

variable {G : Type} [Group G] [Finite G] {T T₁ T₂ : Subgroup G} {a : G}

theorem mk_mem_center_iff [((sec4N T T₁ T₂).subgroupOf (sec4Y T T₁ T₂)).Normal]
    {y : ↥(sec4Y T T₁ T₂)} :
    (QuotientGroup.mk y : ↥(sec4Y T T₁ T₂) ⧸ (sec4N T T₁ T₂).subgroupOf (sec4Y T T₁ T₂)) ∈
      Subgroup.center (↥(sec4Y T T₁ T₂) ⧸ (sec4N T T₁ T₂).subgroupOf (sec4Y T T₁ T₂)) ↔
      Sec4ActsTriv T T₁ T₂ (y : G) := by
  refine ⟨fun hz => ?_, mk_mem_center_of_actsTriv⟩
  have hinv : Sec4ActsTriv T T₁ T₂ ((y : G)⁻¹) := by
    intro y' hy'
    have hy'inv : (y' : G)⁻¹ ∈ sec4Y T T₁ T₂ := (sec4Y T T₁ T₂).inv_mem hy'
    have hc := Subgroup.mem_center_iff.1 hz (QuotientGroup.mk (⟨y'⁻¹, hy'inv⟩ : ↥(sec4Y T T₁ T₂)))
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at hc
    have h1 := Subgroup.mem_subgroupOf.1 hc
    have e : ⁅(y : G)⁻¹, y'⁆ = (((⟨y'⁻¹, hy'inv⟩ : ↥(sec4Y T T₁ T₂)) * y)⁻¹ *
        (y * (⟨y'⁻¹, hy'inv⟩ : ↥(sec4Y T T₁ T₂))) : ↥(sec4Y T T₁ T₂)) := by
      simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e]
    exact h1
  have h2 : (y : G) ∈ sec4Ker T T₁ T₂ := by simpa using (sec4Ker T T₁ T₂).inv_mem hinv
  exact mem_sec4Ker.1 h2

theorem _root_.CFSG.CGT.Timmesfeld75.Sec4Hyp.exists_mem_not_mem_sec4N (h : Sec4Hyp T T₁ a T₂) :
    ∃ t ∈ T, t ∉ sec4N T T₁ T₂ := by
  by_contra hcon
  push Not at hcon
  have hle : T ≤ sec4N T T₁ T₂ := hcon
  have h1 : T ⊓ sec4N T T₁ T₂ = T := inf_eq_left.2 hle
  rw [h.inf_sec4N_eq] at h1
  have hlt := card_normIn_lt_card_of_maxPair h.pair
  rw [h1] at hlt
  exact lt_irrefl _ hlt

theorem _root_.CFSG.CGT.Timmesfeld75.Sec4Hyp.exists_pi
    (hAsc : AschbacherNoPolarInput) (h : Sec4Hyp T T₁ a T₂)
    (hq : 2 * Nat.card (normIn T T₁) < Nat.card T) :
    ∃ (f : ℕ) (P : Type) (_ : Group P) (_ : Finite P) (π : ↥(sec4Y T T₁ T₂) →* P)
      (_ : P ≃* PSU3Model f), 2 ≤ f ∧ Function.Surjective π ∧
      (∀ y : ↥(sec4Y T T₁ T₂), π y = 1 ↔ Sec4ActsTriv T T₁ T₂ (y : G)) ∧
      ∃ S : Sylow 2 P, (T.subgroupOf (sec4Y T T₁ T₂)).map π =
        (Subgroup.center (S : Subgroup P)).map (S : Subgroup P).subtype := by
  obtain ⟨-, f, hf, -, hNormal, ⟨e⟩⟩ := h.sec4_two hAsc hq
  have := hNormal
  let π : ↥(sec4Y T T₁ T₂) →* (↥(sec4Y T T₁ T₂) ⧸ (sec4N T T₁ T₂).subgroupOf (sec4Y T T₁ T₂)) ⧸
      Subgroup.center (↥(sec4Y T T₁ T₂) ⧸ (sec4N T T₁ T₂).subgroupOf (sec4Y T T₁ T₂)) :=
    (QuotientGroup.mk' (Subgroup.center (↥(sec4Y T T₁ T₂) ⧸
      (sec4N T T₁ T₂).subgroupOf (sec4Y T T₁ T₂)))).comp
      (QuotientGroup.mk' ((sec4N T T₁ T₂).subgroupOf (sec4Y T T₁ T₂)))
  have hsurj : Function.Surjective π :=
    (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
  have hker : ∀ y : ↥(sec4Y T T₁ T₂), π y = 1 ↔ Sec4ActsTriv T T₁ T₂ (y : G) := by
    intro y
    refine Iff.trans ?_ mk_mem_center_iff
    exact QuotientGroup.eq_one_iff _
  have hTbar := h.strongWC_img_of_le h.sec4Y_le_normalizer (left_le_sec4Y : T ≤ sec4Y T T₁ T₂)
  have hTZ := h.img_inf_center_eq_bot_of_le le_rfl h.sec4Y_le_normalizer
    (left_le_sec4Y : T ≤ sec4Y T T₁ T₂)
  have hT' := hTbar.map_center hTZ
  have hmap : ((T.subgroupOf (sec4Y T T₁ T₂)).map (QuotientGroup.mk'
      ((sec4N T T₁ T₂).subgroupOf (sec4Y T T₁ T₂)))).map (QuotientGroup.mk' (Subgroup.center
        (↥(sec4Y T T₁ T₂) ⧸ (sec4N T T₁ T₂).subgroupOf (sec4Y T T₁ T₂)))) =
      (T.subgroupOf (sec4Y T T₁ T₂)).map π := by
    rw [Subgroup.map_map]
  rw [hmap] at hT'
  have hB : IsBenderGroup ((↥(sec4Y T T₁ T₂) ⧸ (sec4N T T₁ T₂).subgroupOf (sec4Y T T₁ T₂)) ⧸
      Subgroup.center (↥(sec4Y T T₁ T₂) ⧸ (sec4N T T₁ T₂).subgroupOf (sec4Y T T₁ T₂))) :=
    IsBenderGroup.isPSU3 f hf e
  have hbot : (T.subgroupOf (sec4Y T T₁ T₂)).map π ≠ ⊥ := by
    obtain ⟨t, htT, htN⟩ := h.exists_mem_not_mem_sec4N
    have htY : t ∈ sec4Y T T₁ T₂ := left_le_sec4Y htT
    intro hb
    have hmem : π ⟨t, htY⟩ ∈ (T.subgroupOf (sec4Y T T₁ T₂)).map π :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 htT)
    rw [hb, Subgroup.mem_bot] at hmem
    have hact := (hker ⟨t, htY⟩).1 hmem
    have hK : t ∈ T ⊓ sec4Ker T T₁ T₂ := ⟨htT, hact⟩
    rw [h.inf_sec4Ker_eq] at hK
    exact htN (normIn_le_sec4N_left hK)
  obtain ⟨Q, hQ⟩ := (isPGroup_two_of_isElemAbelian hT'.1).exists_le_sylow
  exact ⟨f, _, inferInstance, inferInstance, π, e, hf, hsurj, hker, Q,
    eq_center_sylow_of_strongWC hB hT' hbot hQ⟩

theorem _root_.CFSG.CGT.Timmesfeld75.Sec4Hyp.conj_eq_of_map_eq (h : Sec4Hyp T T₁ a T₂)
    {P : Type*} [Group P] (π : ↥(sec4Y T T₁ T₂) →* P)
    (hker : ∀ y : ↥(sec4Y T T₁ T₂), π y = 1 → Sec4ActsTriv T T₁ T₂ (y : G)) {g : G}
    (hg : g ∈ sec4Y T T₁ T₂)
    (hmap : ((conjSubgroup g T).subgroupOf (sec4Y T T₁ T₂)).map π =
      (T.subgroupOf (sec4Y T T₁ T₂)).map π) : conjSubgroup g T = T := by
  by_contra hne
  obtain ⟨t, htT, htN⟩ := h.exists_mem_not_mem_sec4N
  have hgN : g ∈ Subgroup.normalizer (sec4N T T₁ T₂ : Set G) := h.sec4Y_le_normalizer hg
  obtain ⟨c, hcT, hcN⟩ : ∃ c ∈ conjSubgroup g T, c ∉ sec4N T T₁ T₂ := by
    by_contra hcon
    push Not at hcon
    have h1 : g * t * g⁻¹ ∈ sec4N T T₁ T₂ := hcon _ (conj_mem_conjSubgroup g htT)
    have h2 := (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer
      (sec4N T T₁ T₂ : Set G)).inv_mem hgN) _).1 h1
    exact htN (by simpa [mul_assoc] using h2)
  have hcY : c ∈ sec4Y T T₁ T₂ := conjSubgroup_le_sec4Y hg hcT
  have hmem : π ⟨c, hcY⟩ ∈ ((conjSubgroup g T).subgroupOf (sec4Y T T₁ T₂)).map π :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hcT)
  rw [hmap] at hmem
  obtain ⟨t₀, ht₀, hπt₀⟩ := Subgroup.mem_map.1 hmem
  have ht₀T : (t₀ : G) ∈ T := Subgroup.mem_subgroupOf.1 ht₀
  have hz : Sec4ActsTriv T T₁ T₂ ((t₀ : G)⁻¹ * c) := by
    have h1 : π (t₀⁻¹ * ⟨c, hcY⟩) = 1 := by rw [map_mul, map_inv, hπt₀, inv_mul_cancel]
    exact hker _ h1
  have hz' : Sec4ActsTriv T T₁ T₂ (((t₀ : G)⁻¹ * c)⁻¹) :=
    (sec4Ker T T₁ T₂).inv_mem hz
  have htinv : t⁻¹ ∈ sec4Y T T₁ T₂ := (sec4Y T T₁ T₂).inv_mem (left_le_sec4Y htT)
  have h3 := hz' _ htinv
  have hTab := h.pair.wc.1
  have hcomm : (t₀ : G)⁻¹ * t * t₀ = t := by
    have := elemAbelian_mul_comm hTab ht₀T htT
    calc (t₀ : G)⁻¹ * t * t₀ = (t₀ : G)⁻¹ * (t * t₀) := by group
      _ = (t₀ : G)⁻¹ * (t₀ * t) := by rw [this]
      _ = t := by group
  have hmain : (c * t)⁻¹ * (t * c) ∈ sec4N T T₁ T₂ := by
    have e : (c * t)⁻¹ * (t * c) = (⁅((t₀ : G)⁻¹ * c)⁻¹, t⁻¹⁆)⁻¹ := by
      have e1 : c = (t₀ : G) * ((t₀ : G)⁻¹ * c) := by group
      set z : G := (t₀ : G)⁻¹ * c with hzdef
      calc (c * t)⁻¹ * (t * c) = t⁻¹ * z⁻¹ * ((t₀ : G)⁻¹ * t * t₀) * z := by rw [e1]; group
        _ = t⁻¹ * z⁻¹ * t * z := by rw [hcomm]
        _ = (⁅z⁻¹, t⁻¹⁆)⁻¹ := by simp only [commutatorElement_def]; group
    rw [e]
    exact (sec4N T T₁ T₂).inv_mem h3
  exact h.not_comm_mod_sec4N hgN hne htT htN hcT hcN hmain

omit [Finite G] in
theorem map_conj_subgroupOf {P : Type*} [Group P] {Y T : Subgroup G} (π : ↥Y →* P) {g : G}
    (hg : g ∈ Y) :
    ((conjSubgroup g T).subgroupOf Y).map π = conjSubgroup (π ⟨g, hg⟩) ((T.subgroupOf Y).map π) := by
  rw [← map_conjSubgroup, conjSubgroup_subgroupOf]

theorem _root_.CFSG.CGT.Timmesfeld75.Sec4Hyp.conj_eq_conj_of_map_eq (h : Sec4Hyp T T₁ a T₂)
    {P : Type*} [Group P] (π : ↥(sec4Y T T₁ T₂) →* P)
    (hker : ∀ y : ↥(sec4Y T T₁ T₂), π y = 1 → Sec4ActsTriv T T₁ T₂ (y : G)) {y y' : G}
    (hy : y ∈ sec4Y T T₁ T₂) (hy' : y' ∈ sec4Y T T₁ T₂)
    (hmap : ((conjSubgroup y' T).subgroupOf (sec4Y T T₁ T₂)).map π =
      ((conjSubgroup y T).subgroupOf (sec4Y T T₁ T₂)).map π) :
    conjSubgroup y' T = conjSubgroup y T := by
  have hg : y⁻¹ * y' ∈ sec4Y T T₁ T₂ := (sec4Y T T₁ T₂).mul_mem ((sec4Y T T₁ T₂).inv_mem hy) hy'
  have e : conjSubgroup (y⁻¹ * y') T = conjSubgroup y⁻¹ (conjSubgroup y' T) := by
    rw [conjSubgroup_conjSubgroup]
  have hmap' : ((conjSubgroup (y⁻¹ * y') T).subgroupOf (sec4Y T T₁ T₂)).map π =
      (T.subgroupOf (sec4Y T T₁ T₂)).map π := by
    rw [map_conj_subgroupOf π hg]
    have h1 := map_conj_subgroupOf (T := T) π hy'
    have h2 := map_conj_subgroupOf (T := T) π hy
    rw [h1, h2] at hmap
    have e3 : (⟨y⁻¹ * y', hg⟩ : ↥(sec4Y T T₁ T₂)) = ⟨y, hy⟩⁻¹ * ⟨y', hy'⟩ := rfl
    rw [e3, map_mul, map_inv, ← conjSubgroup_conjSubgroup, hmap, conjSubgroup_conjSubgroup,
      inv_mul_cancel, conjSubgroup_one]
  have := h.conj_eq_of_map_eq π hker hg hmap'
  rw [e] at this
  have e2 : conjSubgroup y (conjSubgroup y⁻¹ (conjSubgroup y' T)) = conjSubgroup y' T := by
    rw [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]
  rw [← e2, this]

theorem commutator_mul_central {H : Type*} [Group H] {a b z z' : H} (hz : ∀ g, z * g = g * z)
    (hz' : ∀ g, z' * g = g * z') : ⁅a * z, b * z'⁆ = ⁅a, b⁆ := by
  have hconj : ∀ g, z * g * z⁻¹ = g := fun g => by rw [hz g]; group
  have hconj' : ∀ g, z' * g * z'⁻¹ = g := fun g => by rw [hz' g]; group
  simp only [commutatorElement_def]
  calc a * z * (b * z') * (a * z)⁻¹ * (b * z')⁻¹
      = a * (z * (b * z') * z⁻¹) * a⁻¹ * z'⁻¹ * b⁻¹ := by group
    _ = a * (b * z') * a⁻¹ * z'⁻¹ * b⁻¹ := by rw [hconj]
    _ = a * b * (z' * a⁻¹ * z'⁻¹) * b⁻¹ := by group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [hconj']

theorem _root_.CFSG.CGT.Timmesfeld75.Sec4Hyp.actsTriv_of_pi_conj (h : Sec4Hyp T T₁ a T₂)
    (hq : 2 * Nat.card (normIn T T₁) < Nat.card T) {P : Type*} [Group P]
    (π : ↥(sec4Y T T₁ T₂) →* P)
    (hker : ∀ y : ↥(sec4Y T T₁ T₂), π y = 1 → Sec4ActsTriv T T₁ T₂ (y : G)) {w : G}
    (hwY : ∀ y ∈ sec4Y T T₁ T₂, w * y * w⁻¹ ∈ sec4Y T T₁ T₂)
    (hwN : w ∈ Subgroup.normalizer (sec4N T T₁ T₂ : Set G))
    (hw : ∀ y : ↥(sec4Y T T₁ T₂), π ⟨w * y * w⁻¹, hwY y y.2⟩ = π y) :
    Sec4ActsTriv T T₁ T₂ w := by
  have hN := h.normal_sec4N
  have hwX : w ∈ Subgroup.normalizer ((sec4Y T T₁ T₂ : Subgroup G) : Set G) :=
    mem_normalizer_of_conjSubgroup_eq (conjSubgroup_eq_of_le (conjSubgroup_le_of_forall_mem hwY))
  obtain ⟨φ, hφ⟩ := exists_quotient_conj_equiv (X := sec4Y T T₁ T₂) (N := sec4N T T₁ T₂) hwX hwN
  have hcen : ∀ yb : ↥(sec4Y T T₁ T₂) ⧸ (sec4N T T₁ T₂).subgroupOf (sec4Y T T₁ T₂),
      yb⁻¹ * φ yb ∈ Subgroup.center (↥(sec4Y T T₁ T₂) ⧸
        (sec4N T T₁ T₂).subgroupOf (sec4Y T T₁ T₂)) := by
    intro yb
    induction yb using QuotientGroup.induction_on with
    | H y =>
      rw [hφ y, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
      refine mk_mem_center_iff.2 ?_
      refine hker _ ?_
      rw [map_mul, map_inv, hw y, inv_mul_cancel]
  have hfix : ∀ a b : ↥(sec4Y T T₁ T₂) ⧸ (sec4N T T₁ T₂).subgroupOf (sec4Y T T₁ T₂),
      φ ⁅a, b⁆ = ⁅a, b⁆ := by
    intro a b
    rw [map_commutatorElement]
    have e1 : φ a = a * (a⁻¹ * φ a) := by group
    have e2 : φ b = b * (b⁻¹ * φ b) := by group
    rw [e1, e2]
    exact commutator_mul_central (fun g => (Subgroup.mem_center_iff.1 (hcen a) g).symm)
      (fun g => (Subgroup.mem_center_iff.1 (hcen b) g).symm)
  have hle : commutator (↥(sec4Y T T₁ T₂) ⧸ (sec4N T T₁ T₂).subgroupOf (sec4Y T T₁ T₂)) ≤
      MonoidHom.eqLocus φ.toMonoidHom (MonoidHom.id _) := by
    rw [commutator_eq_closure]
    refine Subgroup.closure_le _ |>.2 ?_
    rintro _ ⟨a, b, rfl⟩
    exact hfix a b
  rw [h.commutator_quotient_eq_top hq] at hle
  intro y hy
  have h1 : φ (QuotientGroup.mk (⟨y, hy⟩ : ↥(sec4Y T T₁ T₂))) =
      QuotientGroup.mk (⟨y, hy⟩ : ↥(sec4Y T T₁ T₂)) := hle (Subgroup.mem_top _)
  rw [hφ, QuotientGroup.eq] at h1
  have h2 : (w * y * w⁻¹)⁻¹ * y ∈ sec4N T T₁ T₂ := by
    have := Subgroup.mem_subgroupOf.1 h1
    simpa using this
  have h2' : y⁻¹ * (w * y * w⁻¹) ∈ sec4N T T₁ T₂ := by
    have := (sec4N T T₁ T₂).inv_mem h2
    simpa [mul_assoc] using this
  have h3 := (Subgroup.mem_normalizer_iff.1 (h.sec4Y_le_normalizer hy) _).1 h2'
  have e : y * (y⁻¹ * (w * y * w⁻¹)) * y⁻¹ = ⁅w, y⁆ := by
    simp only [commutatorElement_def]
    group
  rw [← e]
  exact h3

theorem _root_.CFSG.CGT.Timmesfeld75.Sec4Hyp.exists_induced_aut (_h : Sec4Hyp T T₁ a T₂)
    {P : Type*} [Group P] (π : ↥(sec4Y T T₁ T₂) →* P) (hπ : Function.Surjective π)
    (hker : ∀ y : ↥(sec4Y T T₁ T₂), π y = 1 ↔ Sec4ActsTriv T T₁ T₂ (y : G)) {w : G}
    (hww : w * w = 1) (hwY : ∀ y ∈ sec4Y T T₁ T₂, w * y * w⁻¹ ∈ sec4Y T T₁ T₂)
    (hwN : w ∈ Subgroup.normalizer (sec4N T T₁ T₂ : Set G)) :
    ∃ α : MulAut P, (∀ y : ↥(sec4Y T T₁ T₂), α (π y) = π ⟨w * y * w⁻¹, hwY y y.2⟩) ∧
      α * α = 1 := by
  have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hww
  have hwX : w ∈ Subgroup.normalizer ((sec4Y T T₁ T₂ : Subgroup G) : Set G) :=
    mem_normalizer_of_conjSubgroup_eq (conjSubgroup_eq_of_le (conjSubgroup_le_of_forall_mem hwY))
  let ψ : ↥(sec4Y T T₁ T₂) ≃* ↥(sec4Y T T₁ T₂) := (sec4Y T T₁ T₂).normalizerMonoidHom ⟨w, hwX⟩
  have hψ : ∀ y : ↥(sec4Y T T₁ T₂), ((ψ y : ↥(sec4Y T T₁ T₂)) : G) = w * y * w⁻¹ := fun y => by
    simp [ψ]
  have hψψ : ∀ y, ψ (ψ y) = y := by
    intro y
    apply Subtype.ext
    rw [hψ, hψ, hwi]
    calc w * (w * (y : G) * w) * w = (w * w) * y * (w * w) := by group
      _ = y := by rw [hww]; group
  have hψk : ∀ y : ↥(sec4Y T T₁ T₂), π y = 1 → π (ψ y) = 1 := by
    intro y hy
    refine (hker _).2 ?_
    have hact := (hker y).1 hy
    rw [hψ]
    intro y' hy'
    have hy'' : w⁻¹ * y' * w⁻¹⁻¹ ∈ sec4Y T T₁ T₂ := by
      rw [hwi]
      exact hwY y' hy'
    have e : ⁅w * (y : G) * w⁻¹, y'⁆ = w * ⁅(y : G), w⁻¹ * y' * w⁻¹⁻¹⁆ * w⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact conj_mem_of_mem_normalizer hwN (hact _ hy'')
  obtain ⟨α, hα, hαα⟩ := exists_involution_of_surjective π hπ ψ hψk hψψ
  exact ⟨α, fun y => by rw [hα]; rfl, hαα⟩

end Quot

end CFSG.CGT.T75B
