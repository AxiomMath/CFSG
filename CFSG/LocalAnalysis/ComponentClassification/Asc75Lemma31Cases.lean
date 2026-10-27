module

public import CFSG.LocalAnalysis.ComponentClassification.Asc75Lemma31Basic
public import CFSG.Goldschmidt.Steps.G2Odd

public section

namespace CFSG.ComponentClassification.Asc75Lemma31

open Subgroup CFSG.Open CFSG.Goldschmidt CFSG.Goldschmidt.G2 CFSG.QuasithinUnique
open scoped Pointwise commutatorElement

section Elementary

variable {G : Type*} [Group G]

theorem mem_normalizer_of_conjSub_eq {g : G} {H : Subgroup G} (hg : conjSub g H = H) :
    g ∈ normalizer (H : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  have h1 := mem_conjSub (g := g) (A := H) (x := x)
  rw [hg] at h1
  exact h1

theorem conjSub_bot (g : G) : conjSub g (⊥ : Subgroup G) = ⊥ :=
  Subgroup.map_bot _

theorem conj_ne_one {x u : G} (hu : u ≠ 1) : x⁻¹ * u * x ≠ 1 := by
  intro h1
  apply hu
  calc u = x * (x⁻¹ * u * x) * x⁻¹ := by group
    _ = 1 := by rw [h1]; group

theorem conj_ne_one' {x u : G} (hu : u ≠ 1) : x * u * x⁻¹ ≠ 1 := by
  intro h1
  apply hu
  calc u = x⁻¹ * (x * u * x⁻¹) * x := by group
    _ = 1 := by rw [h1]; group

theorem eq_of_card_eq_two {K : Subgroup G} (hK : Nat.card K = 2) {a c : G} (ha : a ∈ K)
    (hc : c ∈ K) (ha1 : a ≠ 1) (hc1 : c ≠ 1) : a = c := by
  obtain ⟨z, -, hz⟩ := (Nat.card_eq_two_iff' (1 : K)).mp hK
  have h1 := hz ⟨a, ha⟩ fun h => ha1 (congrArg Subtype.val h)
  have h2 := hz ⟨c, hc⟩ fun h => hc1 (congrArg Subtype.val h)
  exact congrArg Subtype.val (h1.trans h2.symm)

theorem exists_natPow_eq [Finite G] {a z : G} (hz : z ∈ zpowers a) : ∃ k : ℕ, a ^ k = z :=
  (Submonoid.mem_powers_iff z a).mp (mem_powers_iff_mem_zpowers.mpr hz)

theorem card_ne_one (K : Type*) [Group K] [Finite K] :
    Nat.card {b : K // b ≠ 1} = Nat.card K - 1 := by
  classical
  have := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype,
    Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]

theorem commute_of_mem_fixGrp {V : Subgroup G} {y z u : G} (hz : z ∈ zpowers y)
    (hu : u ∈ fixGrp V y) : z * u = u * z := by
  have hy : y ∈ centralizer ({u} : Set G) :=
    mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp (mem_inf.mp hu).2).symm
  exact mem_centralizer_singleton_iff.mp (zpowers_le.mpr hy hz)

end Elementary

variable {G : Type} [Group G] [Finite G]

theorem transitive_of_onanHyp {A X : Subgroup G} {y : G} (h : ONanHyp A X y)
    (hI : ∀ X₀ : Subgroup G, X₀ ≤ X → X ⊓ centralizer (A : Set G) ≤ X₀ →
      (X₀.subgroupOf X).index ≠ 2)
    (hN : ∀ x ∈ X, conjSub x (A ⊓ centralizer ({y} : Set G)) = A ⊓ centralizer ({y} : Set G) →
      x⁻¹ * y * x ∈ zpowers y ⊔ centralizer (A : Set G)) :
    ∀ b ∈ A, ∀ c ∈ A, b ≠ 1 → c ≠ 1 → ∃ x ∈ X, x⁻¹ * b * x = c := by
  by_contra hT
  have : Fact (IsElemAbelian 2 A) := ⟨h.elem⟩
  have hL := linHyp_of_onanHyp h
  set ρ := conjRep h.le with hρ
  set η := ρ ⟨y, h.mem⟩ with hη
  have hXt : ¬ ONan.IsTransitiveNonzero ρ.range := fun ht =>
    hT ((transitive_iff_of_onanHyp h).mpr ht)
  have hnorm := normalizes_of_onanHyp h hN
  have hCV : fixSp η ≠ ⊤ := by
    intro h0
    apply hL.comSp_ne_bot
    have := hL.isCompl.inf_eq_bot
    rwa [h0, inf_top_eq] at this
  have hR : ONan.IsTransitiveOnSummand (Subgroup.zpowers η) (comSp η) (fixSp η) :=
    ⟨fun r hr a ha => apply_mem_comSp (mul_comm_of_mem_zpowers hr) ha,
      fun r hr c hc => apply_eq_of_mem_zpowers hr hc,
      fun a ha b hb ha0 hb0 => hL.exists_zpowers ha hb ha0 hb0⟩
  have hTI : ONan.IsTI ρ.range (fixSp η) := by
    intro x hx hne
    by_contra hxC
    apply hne
    rw [inf_comm]
    exact hL.ti x hx hxC
  have hRnorm : ∀ x ∈ ρ.range, ONan.image x (fixSp η) = fixSp η →
      ∀ r ∈ Subgroup.zpowers η, x * r * x⁻¹ ∈ Subgroup.zpowers η := by
    intro x hx hxC r hr
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hr
    rw [← conj_zpow]
    exact Subgroup.zpow_mem _ (hnorm x hx hxC) j
  have horb := ONan.onan_irreducible_intransitive_TI ρ.range (Subgroup.zpowers η) hL.zpowers_le
    (irreducible_of_onanHyp h) hXt (comSp η) (fixSp η) hL.isCompl hL.two_le_finrank_comSp
    hL.fixSp_ne_bot hCV hR inferInstance
    (fun r hr a ha ha0 hra => hL.eq_one_of_apply_eq hr ha ha0 hra) hTI hRnorm
  have horb' : MulAction.orbit ρ.range (fixSp η) = ONan.orbit ρ.range (fixSp η) := by
    ext D
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have hidx2 : (MulAction.stabilizer ρ.range (fixSp η)).index = 2 := by
    rw [MulAction.index_stabilizer, horb', horb]
  apply index_ne_two_of_onanHyp h hI
    ((MulAction.stabilizer ρ.range (fixSp η)).map ρ.range.subtype) (Subgroup.map_subtype_le _)
  rw [show ((MulAction.stabilizer ρ.range (fixSp η)).map ρ.range.subtype).subgroupOf ρ.range =
      MulAction.stabilizer ρ.range (fixSp η) from
    Subgroup.comap_map_eq_self_of_injective ρ.range.subtype_injective _]
  exact hidx2

@[expose] def comClosure (V X : Subgroup G) (y : G) : Subgroup G :=
  ⨆ (x : G) (_ : x ∈ X), conjSub x (comGrp V y)

section Closure

variable {V X : Subgroup G} {y : G}

omit [Finite G] in
theorem comGrp_le_comClosure : comGrp V y ≤ comClosure V X y := by
  have h1 := le_iSup₂_of_le (f := fun (x : G) (_ : x ∈ X) => conjSub x (comGrp V y)) 1
    (one_mem X) le_rfl
  rwa [G2.conjSub_one] at h1

omit [Finite G] in
theorem conjSub_comClosure_le {g : G} (hg : g ∈ X) :
    conjSub g (comClosure V X y) ≤ comClosure V X y := by
  change (comClosure V X y).map (MulAut.conj g⁻¹).toMonoidHom ≤ _
  rw [comClosure, Subgroup.map_iSup]
  refine iSup_le fun x => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hx => ?_
  change conjSub g (conjSub x (comGrp V y)) ≤ _
  rw [G2.conjSub_conjSub]
  exact le_iSup₂_of_le (f := fun (x : G) (_ : x ∈ X) => conjSub x (comGrp V y)) (x * g)
    (mul_mem hx hg) le_rfl

theorem conjSub_comClosure {g : G} (hg : g ∈ X) :
    conjSub g (comClosure V X y) = comClosure V X y :=
  eq_of_le_of_card_ge (conjSub_comClosure_le hg) (card_conjSub g _).ge

theorem le_normalizer_comClosure : X ≤ normalizer (comClosure V X y : Set G) :=
  fun _ hg => mem_normalizer_of_conjSub_eq (conjSub_comClosure hg)

end Closure

namespace Hyp

variable {V X : Subgroup G} {y : G} (h : Hyp V X y)
include h

omit [Finite G] in
theorem conjSub_le {x : G} (hx : x ∈ X) {H : Subgroup G} (hH : H ≤ V) : conjSub x H ≤ V := by
  have h1 := conjSub_mono x hH
  rwa [conjSub_eq_of_mem_normalizer (h.le hx)] at h1

omit h in
theorem conjSub_fixGrp {z : G} (hz : z ∈ zpowers y) : conjSub z (fixGrp V y) = fixGrp V y := by
  refine (eq_of_le_of_card_ge (fun u hu => ?_) (card_conjSub z _).le).symm
  rw [mem_conjSub, commute_of_mem_fixGrp hz hu, mul_inv_cancel_right]
  exact hu

omit [Finite G] in
theorem conjSub_inf_conjSub {x x' : G} (hx : x ∈ X) (hx' : x' ∈ X)
    (hne : conjSub x (fixGrp V y) ≠ conjSub x' (fixGrp V y)) :
    conjSub x (fixGrp V y) ⊓ conjSub x' (fixGrp V y) = ⊥ := by
  have heq : conjSub x' (fixGrp V y) = conjSub x (conjSub (x' * x⁻¹) (fixGrp V y)) := by
    rw [G2.conjSub_conjSub, inv_mul_cancel_right]
  have hne' : conjSub (x' * x⁻¹) (fixGrp V y) ≠ fixGrp V y := by
    intro h1
    rw [h1] at heq
    exact hne heq.symm
  have hti : fixGrp V y ⊓ conjSub (x' * x⁻¹) (fixGrp V y) = ⊥ :=
    h.ti _ (mul_mem hx' (inv_mem hx)) hne'
  rw [heq, ← G2.conjSub_inf, hti, conjSub_bot]

omit [Finite G] in
theorem comGrp_ne_bot : comGrp V y ≠ ⊥ := by
  intro h0
  apply h.not_mem
  rw [mem_centralizer_iff]
  intro v hv
  have h1 : ⁅v, y⁆ ∈ comGrp V y := commutator_mem_commutator hv (mem_zpowers y)
  rwa [h0, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1

omit [Finite G] in
theorem exists_zpow_of_mem_sup {g : G} (hg : g ∈ zpowers y ⊔ centralizer (V : Set G)) :
    ∃ j : ℤ, (y ^ j)⁻¹ * g ∈ centralizer (V : Set G) := by
  have hyN : ∀ j : ℤ, ∀ c ∈ centralizer (V : Set G),
      y ^ j * c * (y ^ j)⁻¹ ∈ centralizer (V : Set G) := by
    intro j c hc
    have hyj : y ^ j ∈ normalizer (V : Set G) := zpow_mem (h.le h.mem) j
    rw [mem_centralizer_iff]
    intro a ha
    have ha' : (y ^ j)⁻¹ * a * y ^ j ∈ V := by
      have := (mem_normalizer_iff.mp (inv_mem hyj) a).mp ha
      simpa using this
    have := mem_centralizer_iff.mp hc _ ha'
    calc a * (y ^ j * c * (y ^ j)⁻¹) = y ^ j * (((y ^ j)⁻¹ * a * y ^ j) * c) * (y ^ j)⁻¹ := by
          group
      _ = y ^ j * (c * ((y ^ j)⁻¹ * a * y ^ j)) * (y ^ j)⁻¹ := by rw [this]
      _ = y ^ j * c * (y ^ j)⁻¹ * a := by group
  let T : Subgroup G :=
    { carrier := {g | ∃ j : ℤ, (y ^ j)⁻¹ * g ∈ centralizer (V : Set G)}
      mul_mem' := by
        rintro a b ⟨j, hj⟩ ⟨j', hj'⟩
        refine ⟨j + j', ?_⟩
        have h2 := mul_mem (hyN (-j') _ hj) hj'
        convert h2 using 1
        rw [zpow_add, zpow_neg]
        group
      one_mem' := ⟨0, by simp⟩
      inv_mem' := by
        rintro a ⟨j, hj⟩
        refine ⟨-j, ?_⟩
        have h1 := hyN j _ (inv_mem hj)
        convert h1 using 1
        rw [zpow_neg]
        group }
  have hle : zpowers y ⊔ centralizer (V : Set G) ≤ T := by
    refine sup_le (zpowers_le.mpr ⟨1, by simp⟩) fun c hc => ⟨0, ?_⟩
    simpa using hc
  exact hle hg

theorem conjSub_comGrp_eq {x : G} (hx : x ∈ X)
    (hxy : x⁻¹ * y * x ∈ zpowers y ⊔ centralizer (V : Set G)) :
    conjSub x (comGrp V y) = comGrp V y := by
  have : Fact (IsElemAbelian 2 V) := ⟨h.elem⟩
  obtain ⟨j, hj⟩ := h.exists_zpow_of_mem_sup hxy
  have hc : conjRep h.le (((⟨y, h.mem⟩ : X) ^ j)⁻¹ * (⟨x⁻¹, X.inv_mem hx⟩ * ⟨y, h.mem⟩ *
      (⟨x⁻¹, X.inv_mem hx⟩ : X)⁻¹)) = 1 := by
    rw [conjRep_eq_one_iff]
    simpa using hj
  have hcomp : conjRep h.le ⟨x⁻¹, X.inv_mem hx⟩ * conjRep h.le ⟨y, h.mem⟩ *
      (conjRep h.le ⟨x⁻¹, X.inv_mem hx⟩)⁻¹ = conjRep h.le ⟨y, h.mem⟩ ^ j := by
    have h1 : (⟨x⁻¹, X.inv_mem hx⟩ * ⟨y, h.mem⟩ * (⟨x⁻¹, X.inv_mem hx⟩ : X)⁻¹ : X) =
        (⟨y, h.mem⟩ : X) ^ j * (((⟨y, h.mem⟩ : X) ^ j)⁻¹ *
          (⟨x⁻¹, X.inv_mem hx⟩ * ⟨y, h.mem⟩ * (⟨x⁻¹, X.inv_mem hx⟩ : X)⁻¹)) := by group
    rw [← map_inv, ← map_mul, ← map_mul, h1, map_mul, hc, mul_one, map_zpow]
  have hsmul := h.linHyp.smul_comSp_of_normalizes (hcomp ▸ zpow_mem_zpowers _ j)
  rw [← h.sub_comGrp, conjRep_smul_sub] at hsmul
  change sub V (conjSub x⁻¹⁻¹ (comGrp V y)) = sub V (comGrp V y) at hsmul
  rw [inv_inv, sub_eq_sub_iff, inf_eq_right.mpr (h.conjSub_le hx h.comGrp_le),
    inf_eq_right.mpr h.comGrp_le] at hsmul
  exact hsmul

omit [Finite G] in
theorem inf_comGrp_ne_bot {x₀ : G} (hx₀ : x₀ ∈ X) (hU : conjSub x₀ (fixGrp V y) ≠ fixGrp V y)
    {M : Subgroup G} (hMV : M ≤ V) (hMX : X ≤ normalizer (M : Set G)) (hM : M ≠ ⊥) :
    M ⊓ comGrp V y ≠ ⊥ := by
  have hcomm : ∀ m ∈ M, m ∉ centralizer ({y} : Set G) → M ⊓ comGrp V y ≠ ⊥ := by
    intro m hm hmy h0
    have hmem : ⁅m, y⁆ ∈ M ⊓ comGrp V y := by
      refine mem_inf.mpr ⟨?_, commutator_mem_commutator (hMV hm) (mem_zpowers y)⟩
      rw [commutatorElement_def, mul_assoc, mul_assoc]
      refine mul_mem hm ?_
      rw [← mul_assoc]
      exact (mem_normalizer_iff.mp (hMX h.mem) m⁻¹).mp (inv_mem hm)
    rw [h0, mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact hmy (mem_centralizer_singleton_iff.mpr hmem)
  obtain ⟨⟨m, hm⟩, hm1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hM
  have hm1' : m ≠ 1 := fun h1 => hm1 (Subtype.ext h1)
  by_cases hmy : m ∈ centralizer ({y} : Set G)
  ·
    have hm' : x₀⁻¹ * m * x₀ ∈ M := by
      have := (mem_normalizer_iff.mp (hMX (inv_mem hx₀)) m).mp hm
      rwa [inv_inv] at this
    refine hcomm _ hm' fun hmy' => conj_ne_one (x := x₀) hm1' ?_
    have hmem : x₀⁻¹ * m * x₀ ∈ fixGrp V y ⊓ conjSub x₀ (fixGrp V y) :=
      ⟨⟨hMV hm', hmy'⟩, conj_mem_conjSub ⟨hMV hm, hmy⟩⟩
    rwa [h.ti x₀ hx₀ hU, mem_bot] at hmem
  · exact hcomm m hm hmy

omit [Finite G] in
theorem comClosure_le_of_inf_ne_bot {M : Subgroup G} (hMX : X ≤ normalizer (M : Set G))
    (hMW : M ⊓ comGrp V y ≠ ⊥) : comClosure V X y ≤ M := by
  obtain ⟨⟨w₀, hw₀M, hw₀W⟩, hw₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hMW
  have hw₀1' : w₀ ≠ 1 := fun h1 => hw₀1 (Subtype.ext h1)
  have hWM : comGrp V y ≤ M := by
    intro w hw
    by_cases hw1 : w = 1
    · rw [hw1]
      exact one_mem M
    obtain ⟨k, hk⟩ := h.trans w₀ hw₀W w hw hw₀1' hw1
    have := (mem_normalizer_iff.mp (hMX (inv_mem (pow_mem h.mem k))) w₀).mp hw₀M
    rwa [inv_inv, hk] at this
  refine iSup₂_le fun x hx => ?_
  have h1 := conjSub_mono x hWM
  rwa [conjSub_eq_of_mem_normalizer (hMX hx)] at h1

omit [Finite G] in
theorem comClosure_le_of_ne_bot {x₀ : G} (hx₀ : x₀ ∈ X)
    (hU : conjSub x₀ (fixGrp V y) ≠ fixGrp V y) {M : Subgroup G} (hMV : M ≤ V)
    (hMX : X ≤ normalizer (M : Set G)) (hM : M ≠ ⊥) : comClosure V X y ≤ M :=
  h.comClosure_le_of_inf_ne_bot hMX (h.inf_comGrp_ne_bot hx₀ hU hMV hMX hM)

omit [Finite G] in
theorem comClosure_le : comClosure V X y ≤ V :=
  iSup₂_le fun _ hx => h.conjSub_le hx h.comGrp_le

section CaseThree

variable (hW : ∀ x ∈ X, conjSub x (comGrp V y) = comGrp V y)
include hW

theorem conjSub_fixGrp_inf_comGrp {x : G} (hx : x ∈ X) :
    conjSub x (fixGrp V y) ⊓ comGrp V y = ⊥ := by
  rw [← hW x hx, ← G2.conjSub_inf, h.inf_eq_bot, conjSub_bot]

theorem mem_centralizer_of_conjSub_eq {x z : G} (hx : x ∈ X)
    (hxU : conjSub x (fixGrp V y) ≠ fixGrp V y) (hz : z ∈ zpowers y)
    (hzx : conjSub z (conjSub x (fixGrp V y)) = conjSub x (fixGrp V y)) :
    z ∈ centralizer (V : Set G) := by
  obtain ⟨⟨u, hu⟩, hu1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp h.ne_bot
  have hu'U : x⁻¹ * u * x ∈ conjSub x (fixGrp V y) := conj_mem_conjSub hu
  have hu'nU : x⁻¹ * u * x ∉ fixGrp V y := fun h1 => conj_ne_one (x := x)
    (fun h2 => hu1 (Subtype.ext h2)) (by
      have hmem : x⁻¹ * u * x ∈ fixGrp V y ⊓ conjSub x (fixGrp V y) := ⟨h1, hu'U⟩
      rwa [h.ti x hx hxU, mem_bot] at hmem)
  obtain ⟨a, ha, b, hb, hab⟩ := h.exists_mul (h.conjSub_le hx inf_le_left hu'U)
  have hb1 : b ≠ 1 := by
    rintro rfl
    rw [mul_one] at hab
    exact hu'nU (hab ▸ ha)
  have hza : z⁻¹ * a * z = a := by
    rw [mul_assoc, ← commute_of_mem_fixGrp hz ha, ← mul_assoc, inv_mul_cancel, one_mul]
  have hmem1 : z⁻¹ * (x⁻¹ * u * x) * z ∈ conjSub x (fixGrp V y) := by
    have := conj_mem_conjSub (g := z) hu'U
    rwa [hzx] at this
  have hmem : b⁻¹ * (z⁻¹ * b * z) ∈ conjSub x (fixGrp V y) ⊓ comGrp V y := by
    refine mem_inf.mpr ⟨?_, mul_mem (inv_mem hb) (h.conj_mem_comGrp hb hz)⟩
    have h1 := mul_mem (inv_mem hu'U) hmem1
    have h2 : (x⁻¹ * u * x)⁻¹ * (z⁻¹ * (x⁻¹ * u * x) * z) = b⁻¹ * (z⁻¹ * b * z) := by
      rw [hab]
      calc (a * b)⁻¹ * (z⁻¹ * (a * b) * z) = (a * b)⁻¹ * ((z⁻¹ * a * z) * (z⁻¹ * b * z)) := by
            group
        _ = b⁻¹ * (z⁻¹ * b * z) := by rw [hza]; group
    rwa [h2] at h1
  rw [h.conjSub_fixGrp_inf_comGrp hW hx, mem_bot] at hmem
  have hzb : z⁻¹ * b * z = b := by
    calc z⁻¹ * b * z = b * (b⁻¹ * (z⁻¹ * b * z)) := by group
      _ = b := by rw [hmem, mul_one]
  exact h.mem_centralizer_of_conj_eq hz hb hb1 hzb

theorem case_three {x₀ : G} (hx₀ : x₀ ∈ X) (hU : conjSub x₀ (fixGrp V y) ≠ fixGrp V y) :
    (∀ x ∈ X, ∀ x' ∈ X, conjSub x (fixGrp V y) ≠ fixGrp V y →
      conjSub x' (fixGrp V y) ≠ fixGrp V y →
      ∃ k : ℕ, conjSub (y ^ k) (conjSub x (fixGrp V y)) = conjSub x' (fixGrp V y)) ∧
    ∀ v ∈ V, v ∉ comGrp V y ↔ ∃ x ∈ X, v ∈ conjSub x (fixGrp V y) ∧ v ≠ 1 := by
  classical
  let ι := {S : Subgroup G // ∃ x ∈ X, S = conjSub x (fixGrp V y)}
  have : Finite ι := Finite.of_injective (fun S : ι => ((S.1 : Subgroup G) : Set G))
    fun a b hab => Subtype.ext (SetLike.coe_injective hab)
  obtain ⟨⟨w₀, hw₀⟩, hw₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp h.comGrp_ne_bot
  have hw₀1' : w₀ ≠ 1 := fun h1 => hw₀1 (Subtype.ext h1)
  have hk : ∀ w : comGrp V y, (w : G) ≠ 1 → ∃ k : ℕ, (y ^ k)⁻¹ * w₀ * y ^ k = w :=
    fun w hw => h.trans w₀ hw₀ w w.2 hw₀1' hw
  choose! k hk using hk
  have hne : ∀ j : ℕ, conjSub (y ^ j) (conjSub x₀ (fixGrp V y)) ≠ fixGrp V y := by
    intro j h1
    apply hU
    have := congrArg (conjSub (y ^ j)⁻¹) h1
    rwa [G2.conjSub_conjSub (y ^ j)⁻¹ (y ^ j), mul_inv_cancel, G2.conjSub_one,
      conjSub_fixGrp (inv_mem (npow_mem_zpowers y j))] at this
  let f : comGrp V y → ι := fun w =>
    if (w : G) = 1 then ⟨fixGrp V y, 1, one_mem X, (G2.conjSub_one _).symm⟩
    else ⟨conjSub (y ^ k w) (conjSub x₀ (fixGrp V y)), x₀ * y ^ k w,
      mul_mem hx₀ (pow_mem h.mem _), G2.conjSub_conjSub _ _ _⟩
  have hf1 : ∀ w : comGrp V y, (w : G) = 1 → (f w).1 = fixGrp V y := fun w hw => by
    simp only [f, ite_eq_left hw]
  have hf2 : ∀ w : comGrp V y, (w : G) ≠ 1 →
      (f w).1 = conjSub (y ^ k w) (conjSub x₀ (fixGrp V y)) := fun w hw => by
    simp only [f, ite_eq_right hw]
  have hf : Function.Injective f := by
    intro w w' hww'
    have hval := congrArg Subtype.val hww'
    by_cases hw : (w : G) = 1 <;> by_cases hw' : (w' : G) = 1
    · exact Subtype.ext (hw.trans hw'.symm)
    · rw [hf1 w hw, hf2 w' hw'] at hval
      exact absurd hval.symm (hne _)
    · rw [hf2 w hw, hf1 w' hw'] at hval
      exact absurd hval (hne _)
    · rw [hf2 w hw, hf2 w' hw'] at hval
      have hz : y ^ k w * (y ^ k w')⁻¹ ∈ zpowers y :=
        mul_mem (npow_mem_zpowers y _) (inv_mem (npow_mem_zpowers y _))
      have hzH : conjSub (y ^ k w * (y ^ k w')⁻¹) (conjSub x₀ (fixGrp V y)) =
          conjSub x₀ (fixGrp V y) := by
        rw [← G2.conjSub_conjSub (y ^ k w')⁻¹ (y ^ k w), hval,
          G2.conjSub_conjSub (y ^ k w')⁻¹ (y ^ k w'), mul_inv_cancel, G2.conjSub_one]
      have hzC := h.mem_centralizer_of_conjSub_eq hW hx₀ hU hz hzH
      have hcomm : (w' : G) * (y ^ k w * (y ^ k w')⁻¹) = y ^ k w * (y ^ k w')⁻¹ * w' :=
        mem_centralizer_iff.mp hzC w' (h.comGrp_le w'.2)
      apply Subtype.ext
      calc (w : G) = (y ^ k w)⁻¹ * w₀ * y ^ k w := (hk w hw).symm
        _ = (y ^ k w)⁻¹ * (y ^ k w' * ((y ^ k w')⁻¹ * w₀ * y ^ k w') * (y ^ k w')⁻¹) *
            y ^ k w := by group
        _ = (y ^ k w)⁻¹ * (y ^ k w' * w' * (y ^ k w')⁻¹) * y ^ k w := by rw [hk w' hw']
        _ = (y ^ k w * (y ^ k w')⁻¹)⁻¹ * ((w' : G) * (y ^ k w * (y ^ k w')⁻¹)) := by group
        _ = (y ^ k w * (y ^ k w')⁻¹)⁻¹ * (y ^ k w * (y ^ k w')⁻¹ * w') := by rw [hcomm]
        _ = w' := by group
  have hU2 : 2 ≤ Nat.card (fixGrp V y) := (Subgroup.one_lt_card_iff_ne_bot _).mpr h.ne_bot
  have hVW : Nat.card V - Nat.card (comGrp V y) =
      Nat.card (comGrp V y) * (Nat.card (fixGrp V y) - 1) := by
    rw [h.card_eq, Nat.mul_sub_one, Nat.mul_comm]
  obtain ⟨hle, hcov⟩ := card_mul_le h.comGrp_le (fun S : ι => S.1)
    (by
      rintro ⟨S, x, hx, rfl⟩ ⟨S', x', hx', rfl⟩ hSS'
      exact h.conjSub_inf_conjSub hx hx' fun h1 => hSS' (Subtype.ext h1))
    (by
      rintro ⟨S, x, hx, rfl⟩
      exact h.conjSub_le hx inf_le_left)
    (by
      rintro ⟨S, x, hx, rfl⟩
      exact h.conjSub_fixGrp_inf_comGrp hW hx)
    (c := Nat.card (fixGrp V y)) (by
      rintro ⟨S, x, hx, rfl⟩
      exact card_conjSub x _)
  rw [hVW] at hle hcov
  have hcard : Nat.card ι ≤ Nat.card (comGrp V y) :=
    Nat.le_of_mul_le_mul_right hle (by omega)
  have hcardeq : Nat.card ι = Nat.card (comGrp V y) :=
    le_antisymm hcard (Nat.card_le_card_of_injective f hf)
  have hbij := hf.bijective_of_nat_card_le hcard
  have hsurj : ∀ x ∈ X, conjSub x (fixGrp V y) ≠ fixGrp V y →
      ∃ j : ℕ, conjSub (y ^ j) (conjSub x₀ (fixGrp V y)) = conjSub x (fixGrp V y) := by
    intro x hx hxU
    obtain ⟨w, hw⟩ := hbij.2 ⟨conjSub x (fixGrp V y), x, hx, rfl⟩
    have hval := congrArg Subtype.val hw
    by_cases hw1 : (w : G) = 1
    · rw [hf1 w hw1] at hval
      exact absurd hval.symm hxU
    · rw [hf2 w hw1] at hval
      exact ⟨k w, hval⟩
  refine ⟨fun x hx x' hx' hxU hx'U => ?_, fun v hv => ⟨fun hvW => ?_, ?_⟩⟩
  · obtain ⟨a, ha⟩ := hsurj x hx hxU
    obtain ⟨b, hb⟩ := hsurj x' hx' hx'U
    obtain ⟨c, hc⟩ := exists_natPow_eq
      (mul_mem (inv_mem (npow_mem_zpowers y a)) (npow_mem_zpowers y b))
    refine ⟨c, ?_⟩
    rw [← ha, ← hb, G2.conjSub_conjSub (y ^ c) (y ^ a), hc, mul_inv_cancel_left]
  · obtain ⟨⟨S, x, hx, rfl⟩, hvS⟩ := hcov (by rw [hcardeq]) v hv hvW
    exact ⟨x, hx, hvS, fun h1 => hvW (h1 ▸ one_mem _)⟩
  · rintro ⟨x, hx, hvx, hv1⟩ hvW
    have hmem : v ∈ conjSub x (fixGrp V y) ⊓ comGrp V y := ⟨hvx, hvW⟩
    rw [h.conjSub_fixGrp_inf_comGrp hW hx, mem_bot] at hmem
    exact hv1 hmem

end CaseThree

end Hyp

end CFSG.ComponentClassification.Asc75Lemma31
