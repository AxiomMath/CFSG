module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Qt

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open Sec2V4
open scoped Pointwise commutatorElement

namespace Sec2

variable {G : Type} [Group G]

theorem zpowers_two_cases {b w : G} (hb : orderOf b = 2) (hw : w ∈ zpowers b) : w = 1 ∨ w = b := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hw
  have hk : b ^ k = b ^ (k % 2) := by
    have := (zpow_mod_orderOf b k).symm
    rwa [hb, Nat.cast_ofNat] at this
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [hk, h, zpow_zero]
  · right
    rw [hk, h, zpow_one]

theorem isQ8Cube_data [Finite G] {B : Subgroup G} (hB : IsQ8Cube B) :
    ∃ b₀ ∈ B, orderOf b₀ = 2 ∧ (∀ a ∈ B, ∀ b ∈ B, a * b * a⁻¹ * b⁻¹ ∈ zpowers b₀) ∧
      (∀ a ∈ B, a * a ∈ zpowers b₀) ∧ IsPGroup 2 B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hp, hcomm, hfr, hcard⟩ := hB.1
  have hne : center B ≠ ⊥ := by
    intro h
    rw [h, card_bot] at hcard
    norm_num at hcard
  obtain ⟨⟨c, hc⟩, hc1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  have hc1' : c ≠ 1 := fun h => hc1 (Subtype.ext h)
  have hc2 : c ^ 2 = 1 := by
    have h1 := pow_card_eq_one' (G := center B) (x := ⟨c, hc⟩)
    rw [hcard] at h1
    exact congrArg Subtype.val h1
  have hco : orderOf c = 2 := orderOf_eq_prime hc2 hc1'
  have hcen : center B = zpowers c :=
    (Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hc) (by rw [hcard, Nat.card_zpowers, hco])).symm
  refine ⟨(c : G), c.2, by rw [Subgroup.orderOf_coe, hco], fun a ha b hb => ?_, fun a ha => ?_, hp⟩
  · have h1 : ⁅(⟨a, ha⟩ : B), ⟨b, hb⟩⁆ ∈ center B := by
      rw [← hcomm, _root_.commutator_def]
      exact Subgroup.commutator_mem_commutator (mem_top _) (mem_top _)
    rw [hcen] at h1
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp h1
    refine mem_zpowers_iff.mpr ⟨k, ?_⟩
    have h2 := congrArg Subtype.val hk
    simpa [commutatorElement_def] using h2
  · have h1 : (⟨a, ha⟩ : B) ^ 2 ∈ frattini B := by
      have h3 := (CFSG.GroupTheory.frattini_elementary_quotient hp).2.2.1
        (QuotientGroup.mk ⟨a, ha⟩)
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h3
      exact h3
    rw [hfr, hcen] at h1
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp h1
    refine mem_zpowers_iff.mpr ⟨k, ?_⟩
    have h2 := congrArg Subtype.val hk
    simpa [sq] using h2

theorem exists_elem_sixteen [Finite G] {U : Subgroup G} (hU2 : IsPGroup 2 U)
    (hsq : ∀ a ∈ U, a * a = 1) (hcomm : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a)
    (h16 : 16 ≤ Nat.card U) : ∃ V : Subgroup G, V ≤ U ∧ IsElemAbelian 2 V ∧ Nat.card V = 16 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hU2.exists_card_eq
  have hk4 : 4 ≤ k := by
    by_contra h
    push Not at h
    have : 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hdvd : 2 ^ 4 ∣ Nat.card U := hk ▸ pow_dvd_pow 2 hk4
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 2 hdvd
  refine ⟨K.map U.subtype, map_subtype_le K, ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun a ha => ?_⟩, ?_⟩
  · exact hcomm _ (map_subtype_le K a.2) _ (map_subtype_le K b.2)
  · rw [sq]
    exact hsq a (map_subtype_le K ha)
  · rw [card_map_of_injective U.subtype_injective, hK]
    norm_num

variable {S Z H : Subgroup G} {x t z : G}

theorem TData.conj_mem_H (hSH : S ≤ H) (ht : TData S H x t) {k : G} (hk : k ∈ H) :
    t * k * t⁻¹ ∈ H ∧ (t * k * t⁻¹) * k⁻¹ ∈ S := by
  obtain ⟨s, hs, l, hl, rfl, hlt⟩ := ht.compl k hk
  have hts : t * s * t⁻¹ ∈ S := (mem_normalizer_iff.mp ht.normS s).mp hs
  have e : t * (s * l) * t⁻¹ = (t * s * t⁻¹) * l := by
    calc t * (s * l) * t⁻¹ = t * s * t⁻¹ * (t * l) * t⁻¹ := by group
      _ = t * s * t⁻¹ * (l * t) * t⁻¹ := by rw [hlt]
      _ = (t * s * t⁻¹) * l := by group
  rw [e]
  refine ⟨H.mul_mem (hSH hts) hl, ?_⟩
  have e2 : t * s * t⁻¹ * l * (s * l)⁻¹ = (t * s * t⁻¹) * s⁻¹ := by group
  rw [e2]
  exact S.mul_mem hts (S.inv_mem hs)

theorem Coord.φ_conj_t (C : Coord S Z H) (hSH : S ≤ H) (ht : TData S H x t) {k : G}
    (hk : k ∈ H) : C.φ ⟨t * k * t⁻¹, (ht.conj_mem_H hSH hk).1⟩ = C.φ ⟨k, hk⟩ := by
  have hker : (⟨t * k * t⁻¹, (ht.conj_mem_H hSH hk).1⟩ * (⟨k, hk⟩ : ↥H)⁻¹ : ↥H) ∈ C.φ.ker := by
    rw [C.ker, mem_subgroupOf]
    exact (ht.conj_mem_H hSH hk).2
  have := MonoidHom.mem_ker.mp hker
  rw [map_mul, map_inv, mul_inv_eq_one] at this
  exact this

theorem Coord.φ_y (C : Coord S Z H) (hS2 : IsPGroup 2 S) {y : G} (hyH : y ∈ H)
    (hy3 : orderOf y = 3) : C.φ ⟨y, hyH⟩ ^ 3 = 1 ∧ C.φ ⟨y, hyH⟩ ≠ 1 := by
  refine ⟨?_, fun h => ?_⟩
  · rw [← map_pow]
    have : (⟨y, hyH⟩ : ↥H) ^ 3 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, ← hy3, pow_orderOf_eq_one]
      rfl)
    rw [this, map_one]
  · have hyS : y ∈ S := by
      have hker : (⟨y, hyH⟩ : ↥H) ∈ C.φ.ker := h
      rw [C.ker] at hker
      exact hker
    obtain ⟨k, hk⟩ := hS2 ⟨y, hyS⟩
    have hk' : y ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hdvd : 3 ∣ 2 ^ k := hy3 ▸ orderOf_dvd_of_pow_eq_one hk'
    have := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 3) hdvd
    omega


@[expose] def Coord.imgA5 (C : Coord S Z H) (B : Subgroup G) :
    Subgroup (alternatingGroup (Fin 5)) :=
  (C.φ.comp (Subgroup.inclusion (inf_le_right : B ⊓ H ≤ H))).range

theorem Coord.mem_imgA5 (C : Coord S Z H) (B : Subgroup G) {σ : alternatingGroup (Fin 5)} :
    σ ∈ C.imgA5 B ↔ ∃ k, ∃ hk : k ∈ B ⊓ H, C.φ ⟨k, hk.2⟩ = σ := by
  constructor
  · rintro ⟨⟨k, hk⟩, rfl⟩
    exact ⟨k, hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨k, hk⟩, rfl⟩

theorem Coord.card_inf_H [Finite G] (C : Coord S Z H) (hSH : S ≤ H) (B : Subgroup G) :
    Nat.card (B ⊓ H : Subgroup G) = Nat.card (B ⊓ S : Subgroup G) * Nat.card (C.imgA5 B) := by
  let ρ : ↥(B ⊓ H) →* alternatingGroup (Fin 5) := C.φ.comp (Subgroup.inclusion inf_le_right)
  have hker : Nat.card ρ.ker = Nat.card (B ⊓ S : Subgroup G) := by
    refine Nat.card_congr
      { toFun := fun k => ⟨k.1.1, k.1.2.1, ?_⟩
        invFun := fun s => ⟨⟨s.1, s.2.1, hSH s.2.2⟩, ?_⟩
        left_inv := fun k => rfl
        right_inv := fun s => rfl }
    · have h2 : (Subgroup.inclusion inf_le_right k.1 : ↥H) ∈ C.φ.ker := MonoidHom.mem_ker.mp k.2
      rw [C.ker] at h2
      exact h2
    · rw [MonoidHom.mem_ker]
      have h2 : (⟨s.1, hSH s.2.2⟩ : ↥H) ∈ C.φ.ker := by
        rw [C.ker]
        exact s.2.2
      exact h2
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv, hker] at h
  rw [h]
  exact mul_comm _ _

theorem Coord.isPGroup_imgA5 (C : Coord S Z H) {B : Subgroup G} (hp : IsPGroup 2 B) :
    IsPGroup 2 (C.imgA5 B) :=
  IsPGroup.of_surjective (hp.to_le inf_le_left)
    (C.φ.comp (Subgroup.inclusion (inf_le_right : B ⊓ H ≤ H))).rangeRestrict
    (MonoidHom.rangeRestrict_surjective _)

theorem Coord.card_imgA5_cases (C : Coord S Z H) {y : G} (hyH : y ∈ H)
    (hy : C.φ ⟨y, hyH⟩ ^ 3 = 1 ∧ C.φ ⟨y, hyH⟩ ≠ 1) {B : Subgroup G}
    (hyB : y ∈ normalizer (B : Set G)) (hp : IsPGroup 2 B) :
    Nat.card (C.imgA5 B) = 1 ∨ Nat.card (C.imgA5 B) = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpE := C.isPGroup_imgA5 hp
  have hle := card_le_four_of_isPGroup hpE
  obtain ⟨k, hk⟩ := hpE.exists_card_eq
  have hk2 : k ≤ 2 := by
    by_contra h
    push Not at h
    have : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h
    omega
  interval_cases k
  · left
    simpa using hk
  · exfalso
    have hne : C.imgA5 B ≠ ⊥ := by
      intro h
      rw [h, card_bot] at hk
      norm_num at hk
    obtain ⟨⟨e, he⟩, he1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
    have he1' : e ≠ 1 := fun h => he1 (Subtype.ext h)
    have he2 : e ^ 2 = 1 := by
      have h1 := pow_card_eq_one' (G := C.imgA5 B) (x := ⟨e, he⟩)
      rw [hk, pow_one] at h1
      exact congrArg Subtype.val h1
    have heo : orderOf e = 2 := orderOf_eq_prime he2 he1'
    have hEe : C.imgA5 B = zpowers e := (Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr he)
      (by rw [hk, Nat.card_zpowers, heo, pow_one])).symm
    have hae : C.φ ⟨y, hyH⟩ * e * (C.φ ⟨y, hyH⟩)⁻¹ ∈ C.imgA5 B := by
      obtain ⟨k, hk, hke⟩ := (C.mem_imgA5 B).mp he
      refine (C.mem_imgA5 B).mpr ⟨y * k * y⁻¹, ⟨(mem_normalizer_iff.mp hyB k).mp hk.1,
        H.mul_mem (H.mul_mem hyH hk.2) (H.inv_mem hyH)⟩, ?_⟩
      rw [← hke]
      have e1 : (⟨y * k * y⁻¹, H.mul_mem (H.mul_mem hyH hk.2) (H.inv_mem hyH)⟩ : ↥H) =
          ⟨y, hyH⟩ * ⟨k, hk.2⟩ * (⟨y, hyH⟩)⁻¹ := rfl
      rw [e1, map_mul, map_mul, map_inv]
    rw [hEe] at hae
    rcases zpowers_two_cases heo hae with h | h
    · apply he1'
      calc e = (C.φ ⟨y, hyH⟩)⁻¹ * (C.φ ⟨y, hyH⟩ * e * (C.φ ⟨y, hyH⟩)⁻¹) * C.φ ⟨y, hyH⟩ := by
            group
        _ = 1 := by rw [h]; group
    · apply he1'
      refine alt5_eq_one_of_comm_three he2 hy.1 hy.2 ?_
      calc e * C.φ ⟨y, hyH⟩ = (C.φ ⟨y, hyH⟩ * e * (C.φ ⟨y, hyH⟩)⁻¹) * C.φ ⟨y, hyH⟩ := by rw [h]
        _ = C.φ ⟨y, hyH⟩ * e := by group
  · right
    simpa using hk

structure QSetting (S Z H : Subgroup G) (x t z : G) : Prop where
  hS : Special S Z
  hSH : S ≤ H
  hHS : H ≤ normalizer (S : Set G)
  hx : XData S Z x
  hxH : x ∈ normalizer (H : Set G)
  hxH' : ∀ h ∈ H, x⁻¹ * h⁻¹ * x * h ∈ S
  ht : TData S H x t
  hzZ : z ∈ Z
  hz1 : z ≠ 1
  hz : ∀ c ∈ Z, (t * c * t⁻¹ = c ↔ c ∈ zpowers z)

namespace QSetting

@[expose] def Q (hD : QSetting S Z H x t z) : Subgroup G := hD.hS.Qt hD.ht.normS hD.ht.sq

theorem false_of_card_four [Finite G] (C : Coord S Z H) (hD : QSetting S Z H x t z)
    {B : Subgroup G} (hB : IsQ8Cube B) {b₀ : G} (hb₀Z : b₀ ∈ Z)
    (hcomm : ∀ a ∈ B, ∀ b ∈ B, a * b * a⁻¹ * b⁻¹ ∈ zpowers b₀)
    (h16 : 16 ≤ Nat.card (B ⊓ S : Subgroup G)) (hE : Nat.card (C.imgA5 B) = 4) : False := by
  obtain ⟨hsq, hcm, hcard, -⟩ :=
    C.fixS_elem hD.hS hD.hHS hD.hx hD.hxH hD.hxH' hD.ht hD.hzZ hD.hz1 hD.hz hE
  have hle : B ⊓ S ≤ C.fixS hD.hS (C.imgA5 B) := by
    intro s hs
    refine ⟨hs.2, fun σ hσ => ?_⟩
    obtain ⟨k, hk, rfl⟩ := (C.mem_imgA5 B).mp hσ
    have h1 := C.Ψ_conj hD.hS ⟨k, hk.2⟩ hs.2
    rw [← h1]
    have hks : k * s * k⁻¹ ∈ S := (mem_normalizer_iff.mp (hD.hHS hk.2) s).mp hs.2
    exact (C.Ψ_eq_iff hD.hS hks hs.2).mpr (zpowers_le.mpr hb₀Z (hcomm k hk.1 s hs.1))
  have heq : B ⊓ S = C.fixS hD.hS (C.imgA5 B) :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcard]; exact h16)
  apply hB.2.2
  refine ⟨B ⊓ S, inf_le_left, ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun a ha => ?_⟩, ?_⟩
  · exact hcm _ (hle a.2) _ (hle b.2)
  · rw [sq]
    exact hsq a (hle ha)
  · rw [heq, hcard]

theorem mem_or_t_mem [Finite G] (C : Coord S Z H) (hD : QSetting S Z H x t z) {T : Subgroup G}
    (hTH : ∀ τ ∈ T, τ ∈ H ∨ t * τ ∈ H) {y : G} (hyH : y ∈ H)
    (hy : C.φ ⟨y, hyH⟩ ^ 3 = 1 ∧ C.φ ⟨y, hyH⟩ ≠ 1) {B : Subgroup G} (hBT : B ≤ T)
    (hyB : y ∈ normalizer (B : Set G)) (hBHS : ∀ k ∈ B ⊓ H, k ∈ S) {b : G} (hb : b ∈ B) :
    b ∈ S ∨ t * b ∈ S := by
  have ht := hD.ht
  rcases hTH b (hBT hb) with hbH | hbH
  · exact Or.inl (hBHS b ⟨hb, hbH⟩)
  right
  obtain ⟨h, hhH, rfl⟩ : ∃ h ∈ H, t * h = b := ⟨t * b, hbH, (eq_t_mul ht.sq b).symm⟩
  rw [← eq_t_mul ht.sq h]
  have hk : h * y⁻¹ * h⁻¹ ∈ H := H.mul_mem (H.mul_mem hhH (H.inv_mem hyH)) (H.inv_mem hhH)
  have htk := ht.conj_mem_H hD.hSH hk
  have hc : C.φ ⟨h, hhH⟩ * C.φ ⟨y, hyH⟩ = C.φ ⟨y, hyH⟩ * C.φ ⟨h, hhH⟩ := by
    have hmemB : y * (t * h) * y⁻¹ * (t * h)⁻¹ ∈ B :=
      B.mul_mem ((mem_normalizer_iff.mp hyB _).mp hb) (B.inv_mem hb)
    have e1 : y * (t * h) * y⁻¹ * (t * h)⁻¹ = y * (t * (h * y⁻¹ * h⁻¹) * t⁻¹) := by group
    rw [e1] at hmemB
    have hmemS := hBHS _ ⟨hmemB, H.mul_mem hyH htk.1⟩
    have hker : (⟨y, hyH⟩ * ⟨t * (h * y⁻¹ * h⁻¹) * t⁻¹, htk.1⟩ : ↥H) ∈ C.φ.ker := by
      rw [C.ker]
      exact hmemS
    have h1 := MonoidHom.mem_ker.mp hker
    rw [map_mul, C.φ_conj_t hD.hSH ht hk] at h1
    have e2 : (⟨h * y⁻¹ * h⁻¹, hk⟩ : ↥H) = ⟨h, hhH⟩ * (⟨y, hyH⟩)⁻¹ * (⟨h, hhH⟩)⁻¹ := rfl
    rw [e2, map_mul, map_mul, map_inv, map_inv] at h1
    calc C.φ ⟨h, hhH⟩ * C.φ ⟨y, hyH⟩ = (C.φ ⟨y, hyH⟩ * (C.φ ⟨h, hhH⟩ * (C.φ ⟨y, hyH⟩)⁻¹ *
          (C.φ ⟨h, hhH⟩)⁻¹))⁻¹ * C.φ ⟨y, hyH⟩ * C.φ ⟨h, hhH⟩ := by group
      _ = C.φ ⟨y, hyH⟩ * C.φ ⟨h, hhH⟩ := by rw [h1, inv_one, one_mul]
  have hsq : C.φ ⟨h, hhH⟩ ^ 2 = 1 := by
    have hth := ht.conj_mem_H hD.hSH hhH
    have hmemB : (t * h) * (t * h) ∈ B := B.mul_mem hb hb
    have e1 : (t * h) * (t * h) = (t * h * t⁻¹) * h := by
      rw [ht.inv_eq]
      group
    rw [e1] at hmemB
    have hmemS := hBHS _ ⟨hmemB, H.mul_mem hth.1 hhH⟩
    have hker : (⟨t * h * t⁻¹, hth.1⟩ * ⟨h, hhH⟩ : ↥H) ∈ C.φ.ker := by
      rw [C.ker]
      exact hmemS
    have h1 := MonoidHom.mem_ker.mp hker
    rw [map_mul, C.φ_conj_t hD.hSH ht hhH] at h1
    rw [sq]
    exact h1
  have h1 := alt5_eq_one_of_comm_three hsq hy.1 hy.2 hc
  have hker : (⟨h, hhH⟩ : ↥H) ∈ C.φ.ker := h1
  rw [C.ker] at hker
  exact hker

theorem eq_Q_of_card_one [Finite G] (C : Coord S Z H) (hD : QSetting S Z H x t z)
    {T : Subgroup G} (hTH : ∀ τ ∈ T, τ ∈ H ∨ t * τ ∈ H) {y : G} (hyH : y ∈ H)
    (hy : C.φ ⟨y, hyH⟩ ^ 3 = 1 ∧ C.φ ⟨y, hyH⟩ ≠ 1) {B : Subgroup G} (hB : IsQ8Cube B)
    (hBT : B ≤ T) (hyB : y ∈ normalizer (B : Set G)) {b₀ : G} (hb₀ : orderOf b₀ = 2)
    (hb₀Z : b₀ ∈ Z) (hcomm : ∀ a ∈ B, ∀ b ∈ B, a * b * a⁻¹ * b⁻¹ ∈ zpowers b₀)
    (hE : Nat.card (C.imgA5 B) = 1) : B = hD.Q := by
  have hS := hD.hS
  have ht := hD.ht
  have hb₀1 : b₀ ≠ 1 := fun h => by rw [h, orderOf_one] at hb₀; norm_num at hb₀
  have hBHS : ∀ k ∈ B ⊓ H, k ∈ S := by
    intro k hk
    have h1 : C.φ ⟨k, hk.2⟩ ∈ C.imgA5 B := (C.mem_imgA5 B).mpr ⟨k, hk, rfl⟩
    rw [(Subgroup.card_eq_one).mp hE, mem_bot] at h1
    have h3 : (⟨k, hk.2⟩ : ↥H) ∈ C.φ.ker := h1
    rw [C.ker] at h3
    exact h3
  have hBS : ∀ b ∈ B, b ∈ S ∨ t * b ∈ S := fun b hb =>
    hD.mem_or_t_mem C hTH hyH hy hBT hyB hBHS hb
  have hnd₀ := C.nondeg hS hD.hHS hD.hx hb₀Z hb₀1
  obtain ⟨b₁, hb₁, hb₁S⟩ : ∃ b₁ ∈ B, b₁ ∉ S := by
    by_contra h
    push Not at h
    have h1 := C.card_le_of_isotropic hS hb₀Z hb₀1 hnd₀ (fun u hu => h u hu) hcomm
    rw [hB.2.1] at h1
    norm_num at h1
  obtain ⟨s₁, hs₁S, rfl⟩ : ∃ s₁ ∈ S, t * s₁ = b₁ :=
    ⟨t * b₁, (hBS b₁ hb₁).resolve_left hb₁S, (eq_t_mul ht.sq b₁).symm⟩
  have hB0iso : ∀ u ∈ B ⊓ S, ∀ u' ∈ B ⊓ S, u * u' * u⁻¹ * u'⁻¹ ∈ zpowers b₀ :=
    fun u hu u' hu' => hcomm u hu.1 u' hu'.1
  have hc1 := card_le_two_mul_card_inf (U := B) (W := S) (g := t) hBS
  have hc2 := C.card_le_of_isotropic hS hb₀Z hb₀1 hnd₀ inf_le_right hB0iso
  rw [hB.2.1] at hc1
  have h64 : Nat.card (B ⊓ S : Subgroup G) = 64 := by omega
  have hZB : Z ≤ B ⊓ S := C.Z_le_of_isotropic hS hb₀Z hb₀1 hnd₀ inf_le_right hB0iso h64
  have hb₀z : b₀ = z := by
    obtain ⟨c, hcZ, hcz⟩ := exists_mem_Z_not_mem hS hD.hz1 hD.hzZ
    have hγ : c * (t * s₁) * c⁻¹ * (t * s₁)⁻¹ = c * t * c⁻¹ * t⁻¹ := by
      have h1 : s₁ * c⁻¹ * s₁⁻¹ = c⁻¹ := hS.conj_Z (Z.inv_mem hcZ) hs₁S
      calc c * (t * s₁) * c⁻¹ * (t * s₁)⁻¹ = c * t * (s₁ * c⁻¹ * s₁⁻¹) * t⁻¹ := by group
        _ = c * t * c⁻¹ * t⁻¹ := by rw [h1]
    have hγz : c * t * c⁻¹ * t⁻¹ ∈ zpowers z := comm_t_Z hS ht hD.hz hcZ
    have hγ1 : c * t * c⁻¹ * t⁻¹ ≠ 1 := by
      intro h
      apply hcz
      refine (hD.hz c hcZ).mp ?_
      calc t * c * t⁻¹ = (c * t * c⁻¹ * t⁻¹)⁻¹ * c := by group
        _ = c := by rw [h, inv_one, one_mul]
    have h1 := hcomm c (hZB hcZ).1 _ hb₁
    rw [hγ] at h1
    rcases zpowers_two_cases hb₀ h1 with h | h
    · exact absurd h hγ1
    · rcases hS.eq_one_or_eq hD.hzZ hγz with h' | h'
      · exact absurd h' hγ1
      · exact h.symm.trans h'
  have hB0W : B ⊓ S ≤ hS.Wt t := by
    intro w hw
    refine ⟨hw.2, ?_⟩
    have h1 : w * (t * s₁) * w⁻¹ * (t * s₁)⁻¹ ∈ Z := zpowers_le.mpr hb₀Z (hcomm w hw.1 _ hb₁)
    have h2 : t * (w * s₁ * w⁻¹ * s₁⁻¹) * t⁻¹ ∈ Z :=
      conj_mem_Z_of_normS hS ht.normS (hS.comm_mem hw.2 hs₁S)
    have e : w * t * w⁻¹ * t⁻¹ =
        (w * (t * s₁) * w⁻¹ * (t * s₁)⁻¹) * (t * (w * s₁ * w⁻¹ * s₁⁻¹) * t⁻¹)⁻¹ := by group
    rw [e]
    exact Z.mul_mem h1 (Z.inv_mem h2)
  have hBeq : B ⊓ S = hS.Wt t :=
    Subgroup.eq_of_le_of_card_ge hB0W (by rw [h64, C.card_Wt hS hD.hx ht])
  have hperp := C.perp_eq_of_isotropic hS hD.hzZ hD.hz1 (C.nondeg hS hD.hHS hD.hx hD.hzZ hD.hz1)
    (hS.Z_le_Wt ht.normS) hS.Wt_le (fun u hu u' hu' => comm_mem_zpowers hS hD.hz hu hu')
    (C.card_Wt hS hD.hx ht)
  have hs₁W : s₁ ∈ hS.Wt t := by
    rw [← hperp]
    refine ⟨hs₁S, fun u hu => ?_⟩
    have huB : u ∈ B := (hBeq.symm ▸ hu.1 : u ∈ B ⊓ S).1
    have h1 : u * (t * s₁) * u⁻¹ * (t * s₁)⁻¹ ∈ zpowers z := hb₀z ▸ hcomm u huB _ hb₁
    have h2 : u * t * u⁻¹ * t⁻¹ ∈ zpowers z :=
      C.comm_t_mem hS hD.hHS hD.hx ht hD.hzZ hD.hz1 hD.hz hu.1
    have h3 : t * (u * s₁ * u⁻¹ * s₁⁻¹) * t⁻¹ ∈ zpowers z := by
      have e : t * (u * s₁ * u⁻¹ * s₁⁻¹) * t⁻¹ =
          (u * t * u⁻¹ * t⁻¹)⁻¹ * (u * (t * s₁) * u⁻¹ * (t * s₁)⁻¹) := by group
      rw [e]
      exact mul_mem (inv_mem h2) h1
    have h4 : u * s₁ * u⁻¹ * s₁⁻¹ ∈ zpowers z := by
      have h5 := conj_eq_of_mem_zpowers hD.hz hD.hzZ h3
      have e : u * s₁ * u⁻¹ * s₁⁻¹ = t * (t * (u * s₁ * u⁻¹ * s₁⁻¹) * t⁻¹) * t⁻¹ := by
        calc u * s₁ * u⁻¹ * s₁⁻¹ = (t * t) * (u * s₁ * u⁻¹ * s₁⁻¹) * (t * t)⁻¹ := by
              rw [ht.sq]; group
          _ = t * (t * (u * s₁ * u⁻¹ * s₁⁻¹) * t⁻¹) * t⁻¹ := by group
      rw [e, h5]
      exact h3
    have h6 := inv_mem h4
    rwa [Special.comm_inv] at h6
  have hWB : hS.Wt t ≤ B := hBeq ▸ inf_le_left
  have htB : t ∈ B := by
    have e : t = (t * s₁) * s₁⁻¹ := by group
    rw [e]
    exact B.mul_mem hb₁ (B.inv_mem (hWB hs₁W))
  have hQB : hD.Q ≤ B := hS.Qt_le ht.normS ht.sq hWB htB
  refine (Subgroup.eq_of_le_of_card_ge hQB ?_).symm
  rw [hB.2.1]
  show 2 ^ 7 ≤ Nat.card (hS.Qt ht.normS ht.sq)
  rw [hS.card_Qt ht.normS ht.sq ht.notS, C.card_Wt hS hD.hx ht]
  norm_num

theorem eq_Q [Finite G] (C : Coord S Z H) (hD : QSetting S Z H x t z) {T : Subgroup G}
    (hTH : ∀ τ ∈ T, τ ∈ H ∨ t * τ ∈ H) {y : G} (hyH : y ∈ H) (hy3 : orderOf y = 3)
    {B : Subgroup G} (hB : IsQ8Cube B) (hBT : B ≤ T) (hyB : y ∈ normalizer (B : Set G)) :
    B = hD.Q := by
  obtain ⟨b₀, -, hb₀, hcomm, hsq, hp⟩ := isQ8Cube_data hB
  have hS2 : IsPGroup 2 S := IsPGroup.of_card (n := 10) (by rw [C.card_S hD.hS]; norm_num)
  have hy := C.φ_y hS2 hyH hy3
  have h16 : 16 ≤ Nat.card (B ⊓ S : Subgroup G) := by
    have h1 := card_le_two_mul_card_inf (U := B) (W := H) (g := t) (fun b hb => hTH b (hBT hb))
    have h2 := C.card_inf_H hD.hSH B
    have h3 := card_le_four_of_isPGroup (C.isPGroup_imgA5 hp)
    rw [hB.2.1, h2] at h1
    nlinarith
  have hb₀Z : b₀ ∈ Z := by
    by_contra hb₀Z
    have hcz : ∀ c ∈ Z, c ∈ zpowers b₀ → c = 1 := fun c hc hcb => by
      rcases zpowers_two_cases hb₀ hcb with h | h
      · exact h
      · exact absurd (h ▸ hc) hb₀Z
    obtain ⟨V, hV, hVe, hV16⟩ := exists_elem_sixteen (hp.to_le inf_le_left)
      (fun a ha => hcz _ (hD.hS.sq a ha.2) (hsq a ha.1))
      (fun a ha b hb => by
        have h1 := hcz _ (hD.hS.comm_mem ha.2 hb.2) (hcomm a ha.1 b hb.1)
        calc a * b = (a * b * a⁻¹ * b⁻¹) * b * a := by group
          _ = b * a := by rw [h1, one_mul]) h16
    exact hB.2.2 ⟨V, hV.trans inf_le_left, hVe, hV16⟩
  rcases C.card_imgA5_cases hyH hy hyB hp with hE | hE
  · exact hD.eq_Q_of_card_one C hTH hyH hy hB hBT hyB hb₀ hb₀Z hcomm hE
  · exact (hD.false_of_card_four C hB hb₀Z hcomm h16 hE).elim

end QSetting

end Sec2

end CFSG.ComponentClassification.AS81
