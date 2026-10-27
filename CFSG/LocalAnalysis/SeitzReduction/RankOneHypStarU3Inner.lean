module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneHypStarOuter
public import CFSG.LocalAnalysis.ComponentClassification.GMS78BasicUnitary
public import CFSG.LocalAnalysis.ComponentClassification.Asc76BenderFactsAut

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.ComponentClassification CFSG.ComponentClassification.AschbacherToolkit.Bender
open scoped commutatorElement

section Generic

variable {G : Type*} [Group G]

theorem conj_mul_mul_inv_mul_inv (u : MulAut G) (c : G) :
    MulAut.conj c * u * (MulAut.conj c)⁻¹ * u⁻¹ = MulAut.conj (c * (u c)⁻¹) := by
  rw [map_mul, map_inv, mulAut_conj_apply_eq]
  group

theorem zpowers_le_normalizer_of_conj_mem [Finite G] {E : Subgroup G} {u : G}
    (hEu : ∀ e ∈ E, u * e * u⁻¹ ∈ E) : zpowers u ≤ normalizer (E : Set G) := by
  rw [zpowers_le, mem_normalizer_iff]
  have hle : E.map (MulAut.conj u).toMonoidHom ≤ E := by
    rintro _ ⟨e, he, rfl⟩
    exact hEu e he
  have heq : E.map (MulAut.conj u).toMonoidHom = E :=
    eq_of_le_of_card_ge hle (by rw [card_map_of_injective (MulAut.conj u).injective])
  intro h
  refine ⟨hEu h, fun hh => ?_⟩
  rw [← heq] at hh
  obtain ⟨e, he, hee⟩ := hh
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hee
  rwa [← mul_left_cancel (mul_right_cancel hee)]

theorem exists_mul_zpow_of_mem_sup [Finite G] {E : Subgroup G} {u : G}
    (hEu : ∀ e ∈ E, u * e * u⁻¹ ∈ E) {h : G} (hh : h ∈ E ⊔ zpowers u) :
    ∃ e ∈ E, ∃ k : ℤ, h = e * u ^ k := by
  rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left E (zpowers u)
    (zpowers_le_normalizer_of_conj_mem hEu), Set.mem_mul] at hh
  obtain ⟨e, he, a, ha, rfl⟩ := hh
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp ha
  exact ⟨e, he, k, rfl⟩

theorem eq_one_of_mem_odd_of_mem_isPGroup {E T : Subgroup G} (hE : Odd (Nat.card E))
    (hT : IsPGroup 2 T) {g : G} (hgE : g ∈ E) (hgT : g ∈ T) : g = 1 := by
  obtain ⟨k, hk⟩ := hT ⟨g, hgT⟩
  have h1 : orderOf g ∣ 2 ^ k :=
    orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
  have h2 : orderOf g ∣ Nat.card E := Subgroup.orderOf_dvd_natCard E hgE
  have hcop : Nat.Coprime (2 ^ k) (Nat.card E) :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hE)
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2)

theorem mem_zpowers_of_mem_sup_of_mem [Finite G] {E T : Subgroup G} {u : G}
    (hEu : ∀ e ∈ E, u * e * u⁻¹ ∈ E) (huT : u ∈ T) (hET : ∀ e ∈ E, e ∈ T → e = 1) {h : G}
    (hh : h ∈ E ⊔ zpowers u) (hhT : h ∈ T) : h ∈ zpowers u := by
  obtain ⟨e, he, k, rfl⟩ := exists_mul_zpow_of_mem_sup hEu hh
  have heT : e ∈ T := by
    have := mul_mem hhT (inv_mem (zpow_mem huT k))
    rwa [mul_inv_cancel_right] at this
  rw [hET e he heT, one_mul]
  exact zpow_mem (mem_zpowers u) k

theorem zpow_cases_of_pow_four {u : G} (hu : u ^ 4 = 1) (m : ℤ) :
    u ^ m = 1 ∨ u ^ m = u ∨ u ^ m = u ^ 2 ∨ u ^ m = u⁻¹ := by
  have h4 : u ^ (4 : ℤ) = 1 := by rw [show (4 : ℤ) = ((4 : ℕ) : ℤ) from rfl, zpow_natCast, hu]
  rw [zpow_eq_zpow_emod m h4]
  have h0 := Int.emod_nonneg m (by norm_num : (4 : ℤ) ≠ 0)
  have hlt := Int.emod_lt_of_pos m (by norm_num : (0 : ℤ) < 4)
  rcases (by omega : m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3) with h | h | h | h <;>
    rw [h]
  · exact Or.inl (zpow_zero u)
  · exact Or.inr (Or.inl (zpow_one u))
  · exact Or.inr (Or.inr (Or.inl (by rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast])))
  · refine Or.inr (Or.inr (Or.inr ?_))
    rw [eq_inv_iff_mul_eq_one, ← zpow_add_one]
    exact h4

theorem commutatorElement_mul_left_of_commute {a b z : G} (ha : Commute z a) (hb : Commute z b) :
    ⁅z * a, b⁆ = ⁅a, b⁆ := by
  have hc : Commute z ⁅a, b⁆ := by
    rw [commutatorElement_def]
    exact ((ha.mul_right hb).mul_right ha.inv_right).mul_right hb.inv_right
  have hzb : ⁅z, b⁆ = 1 := commutatorElement_eq_one_iff_commute.mpr hb
  calc ⁅z * a, b⁆ = z * ⁅a, b⁆ * z⁻¹ * ⁅z, b⁆ := by simp only [commutatorElement_def]; group
    _ = ⁅a, b⁆ := by rw [hzb, mul_one, hc.eq, mul_inv_cancel_right]

theorem commutatorElement_mul_right_of_commute {a b z : G} (ha : Commute z a)
    (hb : Commute z b) : ⁅a, z * b⁆ = ⁅a, b⁆ := by
  have hc : Commute z ⁅a, b⁆ := by
    rw [commutatorElement_def]
    exact ((ha.mul_right hb).mul_right ha.inv_right).mul_right hb.inv_right
  have haz : ⁅a, z⁆ = 1 := commutatorElement_eq_one_iff_commute.mpr ha.symm
  calc ⁅a, z * b⁆ = ⁅a, z⁆ * (z * ⁅a, b⁆ * z⁻¹) := by simp only [commutatorElement_def]; group
    _ = ⁅a, b⁆ := by rw [haz, one_mul, hc.eq, mul_inv_cancel_right]

theorem index_centralizer_le_two [Finite G] {R : Subgroup G} {s w : G}
    (hw : ∀ r ∈ R, r * w = w * r) (hw2 : w ^ 2 = 1)
    (h : ∀ t ∈ R, t * s * t⁻¹ * s⁻¹ = 1 ∨ t * s * t⁻¹ * s⁻¹ = w) :
    ((centralizer {s}).subgroupOf R).index ≤ 2 := by
  have hmem : ∀ t ∈ R, t * s * t⁻¹ * s⁻¹ ∈ zpowers w := fun t ht => by
    rcases h t ht with h1 | h1 <;> rw [h1]
    · exact one_mem _
    · exact mem_zpowers w
  have hcomm : ∀ a ∈ zpowers w, ∀ b ∈ zpowers w, a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hb
    exact (Commute.zpow_zpow_self w i j).eq
  have hwc : ∀ a ∈ zpowers w, ∀ r ∈ R, r * a = a * r := by
    intro a ha r hr
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ha
    exact ((Commute.zpow_right (show Commute r w from hw r hr) i)).eq
  let ψ : R →* zpowers w :=
    { toFun := fun t => ⟨t * s * (t : G)⁻¹ * s⁻¹, hmem t t.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun t₁ t₂ => by
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        set c₁ := (t₁ : G) * s * (t₁ : G)⁻¹ * s⁻¹ with hc₁
        set c₂ := (t₂ : G) * s * (t₂ : G)⁻¹ * s⁻¹ with hc₂
        have h₂ : (t₁ : G) * c₂ = c₂ * t₁ := hwc c₂ (hmem t₂ t₂.2) t₁ t₁.2
        calc (t₁ : G) * t₂ * s * ((t₁ : G) * t₂)⁻¹ * s⁻¹ = ((t₁ : G) * c₂) * (t₁ : G)⁻¹ * c₁ := by
              rw [hc₁, hc₂]; group
          _ = c₂ * c₁ := by rw [h₂, mul_inv_cancel_right]
          _ = c₁ * c₂ := hcomm _ (hmem t₂ t₂.2) _ (hmem t₁ t₁.2) }
  have hker : ψ.ker = (centralizer {s}).subgroupOf R := by
    ext t
    rw [MonoidHom.mem_ker, mem_subgroupOf, mem_centralizer_singleton_iff]
    constructor
    · intro h1
      have h2 : (t : G) * s * (t : G)⁻¹ * s⁻¹ = 1 := congrArg Subtype.val h1
      calc (t : G) * s = (t : G) * s * (t : G)⁻¹ * s⁻¹ * (s * t) := by group
        _ = s * t := by rw [h2, one_mul]
    · intro h1
      apply Subtype.ext
      change (t : G) * s * (t : G)⁻¹ * s⁻¹ = 1
      rw [h1]
      group
  rw [← hker, index_ker]
  calc Nat.card ψ.range ≤ Nat.card (zpowers w) := card_le_card_group _
    _ = orderOf w := Nat.card_zpowers w
    _ ≤ 2 := orderOf_le_of_pow_eq_one (by norm_num) hw2

end Generic

theorem hypOneStar_u3_inner {D : Type} [Group D] [Finite D] {f : ℕ} (hf : 2 ≤ f)
    (e : D ≃* CFSG.Open.PSU3 2 f) {x u : MulAut D} (hx : orderOf x = 2)
    (hu : u ^ 2 = x) {z : D} (hxz : x = MulAut.conj z) {E : Subgroup (MulAut D)}
    (hEodd : Odd (Nat.card E)) (hEu : ∀ e ∈ E, u * e * u⁻¹ ∈ E) :
    ∃ c : D, MulAut.conj c * x = x * MulAut.conj c ∧
      MulAut.conj c * u * (MulAut.conj c)⁻¹ ∉ E ⊔ zpowers u := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut D) :=
    Finite.of_injective (fun β : MulAut D => (β : D → D)) DFunLike.coe_injective
  have hq4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hZ := Asc76X.center_eq_bot_of_mulEquiv_psu3 hf e
  have hinj : ∀ a b : D, MulAut.conj a = MulAut.conj b → a = b := by
    intro a b hab
    have hc : a⁻¹ * b ∈ center D := by
      rw [mem_center_iff]
      intro y
      have h1 := congrArg (fun φ : MulAut D => φ y) hab
      simp only [MulAut.conj_apply] at h1
      calc y * (a⁻¹ * b) = a⁻¹ * (a * y * a⁻¹) * b := by group
        _ = a⁻¹ * (b * y * b⁻¹) * b := by rw [h1]
        _ = a⁻¹ * b * y := by group
    rw [hZ, mem_bot] at hc
    exact inv_mul_eq_one.mp hc
  have hx2 : x ^ 2 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hx
    exact absurd hx (by norm_num)
  have hu4 : u ^ 4 = 1 := by rw [show 4 = 2 * 2 from rfl, pow_mul, hu, hx2]
  have hu_ord : orderOf u = 2 ^ 2 :=
    orderOf_eq_prime_pow (p := 2) (n := 1) (by rw [pow_one, hu]; exact hx1) (by simpa using hu4)
  have hxu : x * u = u * x := by
    rw [← hu]
    exact ((Commute.refl u).pow_left 2).eq
  have hz2 : z ^ 2 = 1 := hinj _ _ (by rw [map_pow, ← hxz, hx2, map_one])
  have hz1 : z ≠ 1 := by
    rintro rfl
    exact hx1 (by rw [hxz, map_one])
  have hzz : z * z = 1 := by rw [← sq]; exact hz2
  have huz : u z = z := by
    apply hinj
    rw [mulAut_conj_apply_eq, ← hxz, ← hxu, mul_inv_cancel_right]
  have hB := Asc76X.fusionBenderBorel_of_mulEquiv_psu3 hf e
  have hzP : IsPGroup 2 (zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime hz2 hz1]; rfl)
  obtain ⟨R, hzR'⟩ := hzP.exists_le_sylow
  have hzR : z ∈ (R : Subgroup D) := hzR' (mem_zpowers z)
  have hzc : z ∈ centralizer ((R : Subgroup D) : Set D) :=
    Asc76X.mem_centralizer_of_fusionBenderBorel hB (by omega) R hzR hz2
  have hzr : ∀ r ∈ (R : Subgroup D), r * z = z * r := fun r hr => mem_centralizer_iff.mp hzc r hr
  have hzZ : z ∈ sylowCenter (R : Subgroup D) := mem_sylowCenter.mpr ⟨hzR, fun t ht => hzr t ht⟩
  obtain ⟨hRcard, hZcard, -, hsq, hcomcard⟩ := GMS78.sylow_psu3 hf e R
  have hZ2 : ∀ w ∈ sylowCenter (R : Subgroup D), w ^ 2 = 1 := (benderBorel_sylowCenter hB R).2.1
  have huR : u • R = R := by
    by_contra hne
    have hbot := Asc76X.inf_eq_bot_of_fusionBenderBorel hB hne
    have hz' : z ∈ ((u • R : Sylow 2 D) : Subgroup D) := by
      rw [Sylow.pointwise_smul_def]
      have := smul_mem_pointwise_smul z u (R : Subgroup D) hzR
      rwa [MulAut.smul_def, huz] at this
    have hzinf : z ∈ ((u • R : Sylow 2 D) : Subgroup D) ⊓ (R : Subgroup D) := ⟨hz', hzR⟩
    rw [hbot, mem_bot] at hzinf
    exact hz1 hzinf
  have huRm : ∀ r ∈ (R : Subgroup D), u r ∈ (R : Subgroup D) := by
    intro r hr
    have := smul_mem_pointwise_smul r u (R : Subgroup D) hr
    rw [MulAut.smul_def, ← Sylow.pointwise_smul_def, huR] at this
    exact this
  set IR : Subgroup (MulAut D) := (R : Subgroup D).map (MulAut.conj : D →* MulAut D) with hIR
  have hIR2 : IsPGroup 2 IR := R.isPGroup'.map _
  have hu2 : IsPGroup 2 (zpowers u) := IsPGroup.of_card (by rw [Nat.card_zpowers, hu_ord])
  have huN : zpowers u ≤ normalizer (IR : Set (MulAut D)) :=
    zpowers_le_normalizer_of_conj_mem fun h hh => by
      obtain ⟨r, hr, rfl⟩ := hh
      exact ⟨u r, huRm r hr, mulAut_conj_apply_eq u r⟩
  set T : Subgroup (MulAut D) := zpowers u ⊔ IR with hT
  have hT2 : IsPGroup 2 T := IsPGroup.to_sup_of_normal_right' hu2 hIR2 huN
  have huT : u ∈ T := (le_sup_left : zpowers u ≤ T) (mem_zpowers u)
  have hIRT : IR ≤ T := le_sup_right
  have hET : ∀ g ∈ E, g ∈ T → g = 1 := fun g hgE hgT =>
    eq_one_of_mem_odd_of_mem_isPGroup hEodd hT2 hgE hgT
  by_contra hneg
  push Not at hneg
  have key : ∀ r ∈ (R : Subgroup D), ∃ m : ℤ, MulAut.conj (r * (u r)⁻¹) = u ^ m := by
    intro r hr
    have hcx : MulAut.conj r * x = x * MulAut.conj r := by
      rw [hxz, ← map_mul, ← map_mul, hzr r hr]
    have hrT : MulAut.conj r ∈ T := hIRT ⟨r, hr, rfl⟩
    have h2 : MulAut.conj r * u * (MulAut.conj r)⁻¹ ∈ T :=
      mul_mem (mul_mem hrT huT) (inv_mem hrT)
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (mem_zpowers_of_mem_sup_of_mem hEu huT hET
      (hneg r hcx) h2)
    refine ⟨k - 1, ?_⟩
    rw [← conj_mul_mul_inv_mul_inv, ← hk, zpow_sub_one]
  have hcommZ : ∀ r ∈ (R : Subgroup D), ∀ s ∈ (R : Subgroup D),
      r * s * r⁻¹ * s⁻¹ ∈ sylowCenter (R : Subgroup D) := by
    intro r hr s hs
    have ha : (r ^ 2)⁻¹ * s = s * (r ^ 2)⁻¹ := by
      have h1 := (mem_sylowCenter.mp (hsq r hr)).2 s hs
      calc (r ^ 2)⁻¹ * s = (r ^ 2)⁻¹ * (s * r ^ 2) * (r ^ 2)⁻¹ := by group
        _ = (r ^ 2)⁻¹ * (r ^ 2 * s) * (r ^ 2)⁻¹ := by rw [h1]
        _ = s * (r ^ 2)⁻¹ := by group
    have h1 : r * s * r⁻¹ * s⁻¹ = (r * s) ^ 2 * (r ^ 2)⁻¹ * (s ^ 2)⁻¹ :=
      calc r * s * r⁻¹ * s⁻¹ = r * s * r * ((r ^ 2)⁻¹ * s) * (s ^ 2)⁻¹ := by group
        _ = r * s * r * (s * (r ^ 2)⁻¹) * (s ^ 2)⁻¹ := by rw [ha]
        _ = (r * s) ^ 2 * (r ^ 2)⁻¹ * (s ^ 2)⁻¹ := by rw [sq (r * s)]; group
    rw [h1]
    exact mul_mem (mul_mem (hsq _ (mul_mem hr hs)) (inv_mem (hsq r hr))) (inv_mem (hsq s hs))
  have hcomm_le : ⁅(R : Subgroup D), (R : Subgroup D)⁆ ≤ sylowCenter (R : Subgroup D) :=
    commutator_le.mpr fun r hr s hs => by
      rw [commutatorElement_def]
      exact hcommZ r hr s hs
  have hcomm_card : Nat.card (⁅(R : Subgroup D), (R : Subgroup D)⁆ : Subgroup D) = 2 ^ f := by
    have hmap : (_root_.commutator (R : Subgroup D)).map (R : Subgroup D).subtype =
        ⁅(R : Subgroup D), (R : Subgroup D)⁆ := by
      rw [_root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map, range_subtype]
    rw [← hmap, card_map_of_injective (subtype_injective _), hcomcard]
  have hZeq : sylowCenter (R : Subgroup D) = ⁅(R : Subgroup D), (R : Subgroup D)⁆ :=
    (eq_of_le_of_card_ge hcomm_le (by rw [hZcard, hcomm_card])).symm
  by_cases hA : ∃ s ∈ (R : Subgroup D), u = MulAut.conj s
  ·
    obtain ⟨s, hsR, hus⟩ := hA
    have hs2 : s ^ 2 = z := hinj _ _ (by rw [map_pow, ← hus, hu, hxz])
    have hsZ : s ∉ sylowCenter (R : Subgroup D) := fun h => hz1 (by rw [← hs2]; exact hZ2 s h)
    have hcs : ∀ t ∈ (R : Subgroup D), t * s * t⁻¹ * s⁻¹ = 1 ∨ t * s * t⁻¹ * s⁻¹ = z := by
      intro t ht
      obtain ⟨m, hm⟩ := key t ht
      have hut : u t = s * t * s⁻¹ := by rw [hus, MulAut.conj_apply]
      rw [hut, hus, ← map_zpow] at hm
      have hm' : t * s * t⁻¹ * s⁻¹ = s ^ m := by
        rw [← hinj _ _ hm]
        group
      have hC := hcommZ t ht s hsR
      rw [hm'] at hC ⊢
      have hs4 : s ^ 4 = 1 := by rw [show 4 = 2 * 2 from rfl, pow_mul, hs2, hz2]
      rcases zpow_cases_of_pow_four hs4 m with h | h | h | h <;> rw [h] at hC ⊢
      · exact Or.inl rfl
      · exact absurd hC hsZ
      · exact Or.inr hs2
      · exact absurd (by simpa using inv_mem hC) hsZ
    obtain ⟨n, hn, hcent⟩ := centPairAt_of_mulEquiv_psu3 hf e R s hsR hsZ
    have hnR : ∀ r, r ∈ (R : Subgroup D) ↔ n * r * n⁻¹ ∈ (R : Subgroup D) :=
      mem_normalizer_iff.mp hn
    have hcs' : ∀ t ∈ (R : Subgroup D), t * (n⁻¹ * s * n) * t⁻¹ * (n⁻¹ * s * n)⁻¹ = 1 ∨
        t * (n⁻¹ * s * n) * t⁻¹ * (n⁻¹ * s * n)⁻¹ = n⁻¹ * z * n := by
      intro t ht
      have hid : t * (n⁻¹ * s * n) * t⁻¹ * (n⁻¹ * s * n)⁻¹ =
          n⁻¹ * ((n * t * n⁻¹) * s * (n * t * n⁻¹)⁻¹ * s⁻¹) * n := by group
      rw [hid]
      rcases hcs (n * t * n⁻¹) ((hnR t).mp ht) with h | h <;> rw [h]
      · exact Or.inl (by group)
      · exact Or.inr rfl
    have hz'c : ∀ r ∈ (R : Subgroup D), r * (n⁻¹ * z * n) = n⁻¹ * z * n * r := by
      intro r hr
      have h1 := hzr (n * r * n⁻¹) ((hnR r).mp hr)
      calc r * (n⁻¹ * z * n) = n⁻¹ * ((n * r * n⁻¹) * z) * n := by group
        _ = n⁻¹ * (z * (n * r * n⁻¹)) * n := by rw [h1]
        _ = n⁻¹ * z * n * r := by group
    have hz'2 : (n⁻¹ * z * n) ^ 2 = 1 := by
      rw [sq, show n⁻¹ * z * n * (n⁻¹ * z * n) = n⁻¹ * (z * z) * n by group, hzz]
      group
    have hA₁ := index_centralizer_le_two hzr hz2 hcs
    have hA₂ := index_centralizer_le_two hz'c hz'2 hcs'
    have hle : (centralizer {s}).subgroupOf (R : Subgroup D) ⊓
        (centralizer {n⁻¹ * s * n}).subgroupOf (R : Subgroup D) ≤
          (sylowCenter (R : Subgroup D)).subgroupOf (R : Subgroup D) := by
      intro t ht
      rw [mem_inf, mem_subgroupOf, mem_subgroupOf, mem_centralizer_singleton_iff,
        mem_centralizer_singleton_iff] at ht
      rw [mem_subgroupOf]
      exact hcent t t.2 ht.1 ht.2
    have hidx := index_inf_le.trans (Nat.mul_le_mul hA₁ hA₂)
    have hcard1 := (card_le_of_le hle).trans_eq
      ((Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv).trans hZcard)
    have hRc := card_mul_index ((centralizer {s}).subgroupOf (R : Subgroup D) ⊓
        (centralizer {n⁻¹ * s * n}).subgroupOf (R : Subgroup D))
    rw [hRcard] at hRc
    have h3 : (2 ^ f) ^ 3 ≤ 2 ^ f * (2 * 2) := hRc ▸ Nat.mul_le_mul hcard1 hidx
    have h16 : 2 ^ f * 16 ≤ (2 ^ f) ^ 3 :=
      calc 2 ^ f * 16 = 2 ^ f * (4 * 4) := rfl
        _ ≤ 2 ^ f * (2 ^ f * 2 ^ f) := Nat.mul_le_mul_left _ (Nat.mul_le_mul hq4 hq4)
        _ = (2 ^ f) ^ 3 := by ring
    linarith
  ·
    have hδ : ∀ r ∈ (R : Subgroup D), u r = r ∨ u r = z * r := by
      intro r hr
      obtain ⟨m, hm⟩ := key r hr
      have hw : r * (u r)⁻¹ ∈ (R : Subgroup D) := mul_mem hr (inv_mem (huRm r hr))
      rcases zpow_cases_of_pow_four hu4 m with h | h | h | h <;> rw [h] at hm
      · left
        have h1 := hinj _ _ (hm.trans (map_one _).symm)
        exact (mul_inv_eq_one.mp h1).symm
      · exact absurd ⟨_, hw, hm.symm⟩ hA
      · right
        rw [hu, hxz] at hm
        have h1 := hinj _ _ hm
        calc u r = (r * (u r)⁻¹)⁻¹ * r := by group
          _ = z⁻¹ * r := by rw [h1]
          _ = z * r := by rw [inv_eq_of_mul_eq_one_right hzz]
      · exact absurd ⟨(r * (u r)⁻¹)⁻¹, inv_mem hw, by rw [map_inv, hm, inv_inv]⟩ hA
    have huZ : ∀ w ∈ sylowCenter (R : Subgroup D), u w = w := by
      have hle : ⁅(R : Subgroup D), (R : Subgroup D)⁆ ≤
          MonoidHom.eqLocus (u : D →* D) (MonoidHom.id D) :=
        commutator_le.mpr fun r hr s hs => by
          change u ⁅r, s⁆ = ⁅r, s⁆
          have hzr' : Commute z r := (hzr r hr).symm
          have hzs : Commute z s := (hzr s hs).symm
          rw [map_commutatorElement]
          rcases hδ r hr with h1 | h1 <;> rcases hδ s hs with h2 | h2 <;> rw [h1, h2]
          · exact commutatorElement_mul_right_of_commute hzr' hzs
          · exact commutatorElement_mul_left_of_commute hzr' hzs
          · rw [commutatorElement_mul_left_of_commute hzr' ((Commute.refl z).mul_right hzs),
              commutatorElement_mul_right_of_commute hzr' hzs]
      intro w hw
      rw [hZeq] at hw
      exact hle hw
    obtain ⟨-, -, t, ht, hnot⟩ := autControlAt_of_mulEquiv_psu3 hf e R u huRm huZ ⟨2, hu4⟩
      fun s hs h => hA ⟨s, hs, h⟩
    apply hnot
    rcases hδ t ht with h | h
    · rw [h, inv_mul_cancel]
      exact one_mem _
    · rw [h, ← hzr t ht, ← mul_assoc, inv_mul_cancel, one_mul]
      exact hzZ

end CFSG.SeitzReduction.RankOne
