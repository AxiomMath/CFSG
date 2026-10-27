module

public import CFSG.GroupTheory.ThompsonAxB
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentInvolutionNormalizer
public import CFSG.GroupTheory.PCore.Defs
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentActionBasic

public section

namespace CFSG.ComponentClassification.AschbacherToolkit

open CFSG.Open
open scoped commutatorElement

variable {G : Type*} [Group G]

@[expose] def oddGenerated (Y : Subgroup G) : Subgroup G :=
  Subgroup.closure {y | y ∈ Y ∧ Odd (orderOf y)}

theorem oddGenerated_le (Y : Subgroup G) : oddGenerated Y ≤ Y := by
  rw [oddGenerated, Subgroup.closure_le]
  exact fun _ hy => hy.1

theorem normalizer_le_normalizer_map_characteristic (H : Subgroup G) (K : Subgroup H)
    [hK : K.Characteristic] :
    Subgroup.normalizer (H : Set G) ≤
      Subgroup.normalizer ((K.map H.subtype : Subgroup G) : Set G) := by
  intro g hg
  let e := H.normalizerMonoidHom ⟨g, hg⟩
  have hconj : (MulAut.conj g).toMonoidHom.comp H.subtype = H.subtype.comp e.toMonoidHom := by
    ext h
    exact (Subgroup.normalizerMonoidHom_apply_apply_coe H ⟨g, hg⟩ h).symm
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  rw [Subgroup.map_map]
  change K.map ((MulAut.conj g).toMonoidHom.comp H.subtype) = _
  rw [hconj, ← Subgroup.map_map]
  congr 1
  exact Subgroup.characteristic_iff_map_eq.mp hK e

theorem inf_eq_bot_of_isPGroup_of_coprime {p : ℕ} [Fact p.Prime] [Finite G] {P N : Subgroup G}
    (hP : IsPGroup p P) (hN : ¬ p ∣ Nat.card N) : P ⊓ N = ⊥ := by
  have hPN : IsPGroup p (P ⊓ N : Subgroup G) := hP.to_le inf_le_left
  obtain ⟨k, hk⟩ := hPN.exists_card_eq
  have hdvd : Nat.card (P ⊓ N : Subgroup G) ∣ Nat.card N :=
    Subgroup.card_dvd_of_le inf_le_right
  rcases k with _ | k
  · rw [pow_zero] at hk
    exact Subgroup.card_eq_one.mp hk
  · exfalso
    apply hN
    rw [hk] at hdvd
    exact (dvd_pow_self p (Nat.succ_ne_zero k)).trans hdvd

variable [Finite G]

theorem twoCore_centralizer_centralizes (X : Subgroup G) (a : G)
    (hX : X = (CFSG.oddCore X).map X.subtype ⊔ (Layer.subgroup X).map X.subtype)
    (hinv : Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (X : Set G)) :
    CFSG.pCore 2 G ⊓ Subgroup.centralizer ({a} : Set G) ≤ Subgroup.centralizer (X : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := CFSG.pCore 2 G with hQ
  set Qa := Q ⊓ Subgroup.centralizer ({a} : Set G) with hQa
  set O := (CFSG.oddCore X).map X.subtype with hO
  set E := (Layer.subgroup X).map X.subtype with hE
  have hQtwo : IsPGroup 2 Q := CFSG.pCore_isPGroup
  have hQaX : Qa ≤ Subgroup.normalizer (X : Set G) := inf_le_right.trans hinv
  have hOchar : (CFSG.oddCore X).Characteristic := OddCore.characteristic X
  have hQaO : Qa ≤ Subgroup.normalizer (O : Set G) :=
    hQaX.trans (normalizer_le_normalizer_map_characteristic X (CFSG.oddCore X))
  have hOodd : ¬ 2 ∣ Nat.card O := by
    rw [hO, Subgroup.card_map_of_injective X.subtype_injective]
    have h : Odd (Nat.card (CFSG.oddCore X)) := OddCore.odd_card X
    exact fun h2 => (Nat.not_even_iff_odd.mpr h) (even_iff_two_dvd.mpr h2)
  have hcommO : ⁅Qa, O⁆ = ⊥ := by
    have h1 : ⁅Qa, O⁆ ≤ Q :=
      (Subgroup.commutator_mono inf_le_left le_top).trans (Subgroup.commutator_le_left Q ⊤)
    have h2 : ⁅Qa, O⁆ ≤ O := Subgroup.le_normalizer_iff_commutator_le_right.mp hQaO
    have h3 := inf_eq_bot_of_isPGroup_of_coprime hQtwo hOodd
    exact eq_bot_iff.mpr ((le_inf h1 h2).trans h3.le)
  have hQaE : Qa ≤ Subgroup.normalizer (E : Set G) :=
    hQaX.trans (AschbacherComponentInvolution.normalizer_preserves_layer_image X)
  have hEX : E ≤ X := Subgroup.map_subtype_le _
  let QX : Subgroup X := Q.subgroupOf X
  have hQXn : QX.Normal := Subgroup.normal_subgroupOf
  have hQXtwo : IsPGroup 2 QX := hQtwo.comap_subtype
  have : Group.IsNilpotent QX := hQXtwo.isNilpotent
  have hQXsub : IsSubnormal QX ⊤ :=
    IsSubnormal.step le_top (Subgroup.normal_subgroupOf) (IsSubnormal.refl ⊤)
  have hlayer : ⁅Layer.subgroup X, QX⁆ = ⊥ := Layer.commutes_with_solvable_subnormal QX hQXsub
  have hEQX : ⁅E, Q ⊓ X⁆ = ⊥ := by
    have hmap := congrArg (Subgroup.map X.subtype) hlayer
    rw [Subgroup.map_commutator, Subgroup.map_bot] at hmap
    rwa [show QX.map X.subtype = Q ⊓ X from Subgroup.subgroupOf_map_subtype Q X] at hmap
  have hcommE : ⁅Qa, E⁆ = ⊥ := by
    have h1 : ⁅Qa, E⁆ ≤ Q :=
      (Subgroup.commutator_mono inf_le_left le_top).trans (Subgroup.commutator_le_left Q ⊤)
    have h2 : ⁅Qa, E⁆ ≤ E := Subgroup.le_normalizer_iff_commutator_le_right.mp hQaE
    have h3 : ⁅⁅Qa, E⁆, E⁆ = ⊥ := by
      rw [Subgroup.commutator_comm]
      exact eq_bot_iff.mpr ((Subgroup.commutator_mono le_rfl (le_inf h1 (h2.trans hEX))).trans
        hEQX.le)
    have : Group.IsPerfect (Layer.subgroup X) := Layer.perfect X
    have : Group.IsPerfect E := Group.IsPerfect.map X.subtype
    exact AschbacherComponentAction.perfect_three_subgroup_action E Qa h3
  have hO' := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommO
  have hE' := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommE
  intro q hq
  apply Subgroup.mem_centralizer_iff.mpr
  have hle : O ⊔ E ≤ Subgroup.centralizer ({q} : Set G) := by
    apply sup_le
    · intro x hx
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp (hO' hq) x hx)
    · intro x hx
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp (hE' hq) x hx)
  intro x hx
  rw [hX] at hx
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hx)

theorem lemma_2_6_two (X : Subgroup G) (a : G) (ha : orderOf a = 2)
    (hX : X = (CFSG.oddCore X).map X.subtype ⊔ (Layer.subgroup X).map X.subtype)
    (hinv : Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (X : Set G)) :
    ⁅oddGenerated (X ⊓ Subgroup.centralizer ({a} : Set G)), CFSG.pCore 2 G⁆ = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := CFSG.pCore 2 G with hQ
  have hQtwo : IsPGroup 2 Q := CFSG.pCore_isPGroup
  have hcent := twoCore_centralizer_centralizes X a hX hinv
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer, oddGenerated, Subgroup.closure_le]
  rintro b ⟨⟨hbX, hbC⟩, hbodd⟩
  have hab : Commute b a := Subgroup.mem_centralizer_singleton_iff.mp hbC
  let α : Subgroup.zpowers b →* MulAut Q := MulAut.conjNormal.comp (Subgroup.zpowers b).subtype
  let β : Subgroup.zpowers a →* MulAut Q := MulAut.conjNormal.comp (Subgroup.zpowers a).subtype
  have hA : ¬ 2 ∣ Nat.card (Subgroup.zpowers b) := by
    rw [Nat.card_zpowers]
    exact fun h => (Nat.not_even_iff_odd.mpr hbodd) (even_iff_two_dvd.mpr h)
  have hB : IsPGroup 2 (Subgroup.zpowers a) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha, pow_one])
  have hcomm : ∀ x y, α x * β y = β y * α x := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hc : Commute (b ^ i) (a ^ j) := hab.zpow_zpow i j
    ext r
    simp only [α, β, MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
      MulAut.mul_apply, MulAut.conjNormal_apply]
    calc b ^ i * (a ^ j * r * (a ^ j)⁻¹) * (b ^ i)⁻¹
        = (b ^ i * a ^ j) * r * (b ^ i * a ^ j)⁻¹ := by group
      _ = (a ^ j * b ^ i) * r * (a ^ j * b ^ i)⁻¹ := by rw [hc.eq]
      _ = a ^ j * (b ^ i * r * (b ^ i)⁻¹) * (a ^ j)⁻¹ := by group
  have hfix : ∀ x r, (∀ y, β y r = r) → α x r = r := by
    rintro ⟨x, hx⟩ r hr
    have hra : (r : G) ∈ Subgroup.centralizer ({a} : Set G) := by
      have h := congrArg Subtype.val (hr ⟨a, Subgroup.mem_zpowers a⟩)
      simp only [β, MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
        MulAut.conjNormal_apply] at h
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      calc (r : G) * a = (a * r * a⁻¹) * a := by rw [h]
        _ = a * r := by group
    have hrX := hcent ⟨r.2, hra⟩
    have hxX : x ∈ X := (Subgroup.zpowers_le.mpr hbX) hx
    apply Subtype.ext
    simp only [α, MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
      MulAut.conjNormal_apply]
    rw [Subgroup.mem_centralizer_iff.mp hrX x hxX]
    group
  have hb := CFSG.GroupTheory.thompson_A_times_B hQtwo hA hB α β hcomm hfix
    ⟨b, Subgroup.mem_zpowers b⟩
  apply Subgroup.mem_centralizer_iff.mpr
  intro q hq
  have h := congrArg Subtype.val (congrArg (fun φ : MulAut Q => φ ⟨q, hq⟩) hb)
  simp only [α, MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
    MulAut.conjNormal_apply, MulAut.one_apply] at h
  calc q * b = (b * q * b⁻¹) * b := by rw [h]
    _ = b * q := by group

end CFSG.ComponentClassification.AschbacherToolkit
