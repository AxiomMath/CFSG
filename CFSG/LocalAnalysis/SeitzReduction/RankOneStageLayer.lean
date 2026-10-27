module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneStageTranslations
public import CFSG.LocalAnalysis.SeitzReduction.RankOneGMS28

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.SteinbergBV CFSG.LocalAnalysis.SteinbergBX
open CFSG.ABGLocalTools

section Square

variable {G : Type*} [Group G]

theorem mul_sq_of_commutator_central {x y c : G} (hc : y⁻¹ * x⁻¹ * y * x = c)
    (hcc : ∀ w : G, c * w = w * c) : (x * y) ^ 2 = x ^ 2 * y ^ 2 * c := by
  have hyx : y * x = x * y * c := by
    calc y * x = x * y * (y⁻¹ * x⁻¹ * y * x) := by group
      _ = x * y * c := by rw [hc]
  rw [sq, sq, sq]
  calc x * y * (x * y) = x * (y * x) * y := by group
    _ = x * (x * y * c) * y := by rw [hyx]
    _ = x * x * y * (c * y) := by group
    _ = x * x * y * (y * c) := by rw [hcc y]
    _ = x * x * (y * y) * c := by group

theorem forall_sq_eq_one_of_central_transitive [Finite G] {z : G} (hz1 : z ≠ 1)
    (hz2 : z ^ 2 = 1) (hzc : ∀ w : G, z * w = w * z) (hsq : ∀ x : G, x ^ 2 = 1 ∨ x ^ 2 = z)
    (hcomm : ∀ x y : G, y⁻¹ * x⁻¹ * y * x = 1 ∨ y⁻¹ * x⁻¹ * y * x = z)
    (h16 : 16 ≤ Nat.card G) (δ : MulAut G) (hδz : δ z = z)
    (htrans : ∀ x y : G, x ≠ 1 → x ≠ z → y ≠ 1 → y ≠ z →
      ∃ k : ℕ, (δ ^ k) x = y ∨ (δ ^ k) x = y * z) :
    ∀ x : G, x ^ 2 = 1 := by
  classical
  have hδkz : ∀ k : ℕ, (δ ^ k) z = z := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [pow_succ, MulAut.mul_apply, hδz, ih]
  have hzz : z * z = 1 := by rw [← sq]; exact hz2
  have hsqz : ∀ x : G, (x * z) ^ 2 = x ^ 2 := by
    intro x
    rw [sq, sq]
    calc x * z * (x * z) = x * (z * x) * z := by group
      _ = x * (x * z) * z := by rw [hzc x]
      _ = x * x * (z * z) := by group
      _ = x * x := by rw [hzz, mul_one]
  by_contra hne
  push Not at hne
  obtain ⟨x₀, hx₀⟩ := hne
  have hx₀z : x₀ ^ 2 = z := (hsq x₀).resolve_left hx₀
  have hx₀1 : x₀ ≠ 1 := by rintro rfl; simp at hx₀
  have hx₀z' : x₀ ≠ z := by rintro rfl; exact hx₀ hz2
  have hall : ∀ y : G, y ≠ 1 → y ≠ z → y ^ 2 = z := by
    intro y hy1 hyz
    obtain ⟨k, hk | hk⟩ := htrans x₀ y hx₀1 hx₀z' hy1 hyz
    · rw [← hk, ← map_pow, hx₀z, hδkz]
    · rw [← hsqz y, ← hk, ← map_pow, hx₀z, hδkz]
  have hcz : ∀ x y : G, x ≠ 1 → x ≠ z → y ≠ 1 → y ≠ z → x * y ≠ 1 → x * y ≠ z →
      y⁻¹ * x⁻¹ * y * x = z := by
    intro x y hx1 hxz hy1 hyz hxy1 hxyz
    rcases hcomm x y with h1 | h1
    · exfalso
      have h2 := mul_sq_of_commutator_central h1 (fun w => by rw [one_mul, mul_one])
      rw [hall x hx1 hxz, hall y hy1 hyz, hall (x * y) hxy1 hxyz, mul_one, hzz] at h2
      exact hz1 h2
    · exact h1
  have hcard : ∀ l : List G, l.length < 16 → ∃ w : G, w ∉ l := by
    intro l hl
    have : Fintype G := Fintype.ofFinite G
    by_contra hall'
    push Not at hall'
    have h1 : Fintype.card G ≤ l.toFinset.card := by
      rw [← Finset.card_univ]
      exact Finset.card_le_card (fun w _ => List.mem_toFinset.mpr (hall' w))
    have h2 := List.toFinset_card_le l
    rw [Nat.card_eq_fintype_card] at h16
    omega
  obtain ⟨a, ha⟩ := hcard [1, z] (by simp)
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at ha
  obtain ⟨ha1, haz⟩ := ha
  obtain ⟨b, hb⟩ := hcard [1, z, a, a * z] (by simp)
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hb
  obtain ⟨hb1, hbz, hba, hbaz⟩ := hb
  obtain ⟨c, hc⟩ := hcard [1, z, a, a * z, b, b * z, a * b, a * b * z] (by simp)
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hc
  obtain ⟨hc1, hcz', hca, hcaz, hcb, hcbz, hcab, hcabz⟩ := hc
  have hinv : ∀ w : G, w ≠ 1 → w ≠ z → w⁻¹ = w * z := by
    intro w hw1 hwz
    rw [inv_eq_iff_mul_eq_one]
    calc w * (w * z) = w ^ 2 * z := by rw [sq, mul_assoc]
      _ = 1 := by rw [hall w hw1 hwz, hzz]
  have hmul_ne : ∀ x y : G, x ≠ 1 → x ≠ z → y ≠ x * z → y ≠ x → x * y ≠ 1 ∧ x * y ≠ z := by
    intro x y hx1 hxz hy1 hy2
    constructor
    · intro h1
      apply hy1
      rw [← hinv x hx1 hxz]
      exact (inv_eq_of_mul_eq_one_right h1).symm
    · intro h1
      apply hy2
      have : y = x⁻¹ * z := by rw [← h1]; group
      rw [this, hinv x hx1 hxz, mul_assoc, hzz, mul_one]
  obtain ⟨hab1, habz⟩ := hmul_ne a b ha1 haz hbaz hba
  obtain ⟨hac1, hacz⟩ := hmul_ne a c ha1 haz hcaz hca
  obtain ⟨hbc1, hbcz⟩ := hmul_ne b c hb1 hbz hcbz hcb
  obtain ⟨habc1, habcz⟩ := hmul_ne (a * b) c hab1 habz hcabz hcab
  have e1 := hcz a b ha1 haz hb1 hbz hab1 habz
  have e2 := hcz a c ha1 haz hc1 hcz' hac1 hacz
  have e3 := hcz a (b * c) ha1 haz hbc1 hbcz (by rwa [← mul_assoc]) (by rwa [← mul_assoc])
  have hb' : b⁻¹ * a⁻¹ * b = z * a⁻¹ := by
    calc b⁻¹ * a⁻¹ * b = b⁻¹ * a⁻¹ * b * a * a⁻¹ := by group
      _ = z * a⁻¹ := by rw [e1]
  have key : (b * c)⁻¹ * a⁻¹ * (b * c) * a = 1 := by
    calc (b * c)⁻¹ * a⁻¹ * (b * c) * a = c⁻¹ * (b⁻¹ * a⁻¹ * b) * c * a := by group
      _ = c⁻¹ * (z * a⁻¹) * c * a := by rw [hb']
      _ = c⁻¹ * (a⁻¹ * z) * c * a := by rw [hzc a⁻¹]
      _ = c⁻¹ * a⁻¹ * (z * c) * a := by group
      _ = c⁻¹ * a⁻¹ * (c * z) * a := by rw [hzc c]
      _ = c⁻¹ * a⁻¹ * c * (z * a) := by group
      _ = c⁻¹ * a⁻¹ * c * (a * z) := by rw [hzc a]
      _ = (c⁻¹ * a⁻¹ * c * a) * z := by group
      _ = 1 := by rw [e2, hzz]
  rw [e3] at key
  exact hz1 key

end Square

namespace SmallRootStage

variable {D : Type} [Group D] [Finite D] {R X U P : Subgroup D} {n : ℕ}

theorem exists_isTorus_translations (h : SmallRootStage R X U P n)
    (hE : GMSHasRegularNormal U R) {t : D} (hS : GMS28.Setup R R X U P n t) :
    (∀ u ∈ U, ∃ x ∈ normalizer ((U ⊔ R : Subgroup D) : Set D) ⊓ centralizer (U : Set D),
      x * t * x⁻¹ = u * t) ∧
    GMS28.IsV₁ U R P (normalizer ((U ⊔ R : Subgroup D) : Set D) ⊓ centralizer (U : Set D)) ∧
    ∃ d ∈ X ⊓ normalizer (U : Set D), X ⊓ normalizer (U : Set D) = U ⊔ zpowers d ∧
      GMS28.IsTorus U R (normalizer ((U ⊔ R : Subgroup D) : Set D) ⊓ centralizer (U : Set D))
        t d d := by
  obtain ⟨E, hEN, hEn, hreg⟩ := hE
  have htr := hS.exists_tr_conj_eq E hEN hEn hreg
  set W := normalizer ((U ⊔ R : Subgroup D) : Set D) ⊓ centralizer (U : Set D) with hW
  have hWcard : Nat.card W = 2 * 2 ^ n * 2 ^ n := h.card_translations hS htr
  have hW2 : IsPGroup 2 W := IsPGroup.of_card (n := 2 * n + 1) (by rw [hWcard]; ring)
  have hV₁ : GMS28.IsV₁ U R P W :=
    ⟨isSylowOf_iff.mpr ⟨le_rfl, hW2, by rw [relIndex_self]; norm_num⟩, hS.V_le_tr,
      hS.P_le_normalizer_V.trans hS.normalizer_V_le_normalizer_tr⟩
  obtain ⟨d, hdN, hdord, hNX, hdtr, -⟩ := h.exists_singer
  obtain ⟨hn3, -, -, ⟨-, -, hXC⟩, -⟩ := h.1
  have hdV : d ∈ normalizer ((U ⊔ R : Subgroup D) : Set D) := gms_NXU_le_L h.1 hdN
  have hdodd : Odd (orderOf d) := by
    have h8 : 8 ≤ 2 ^ n :=
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
    have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
    rw [hdord]
    exact Nat.odd_iff.mpr (by omega)
  refine ⟨htr, hV₁, d, hdN, hNX, ⟨(mem_inf.mp hdN).2, hdtr, hS.normalizer_V_le_normalizer_tr hdV,
    hdV, (mem_centralizer_iff.mp (hXC (mem_inf.mp hdN).1) t hS.mem).symm, hdodd,
    fun _ _ => rfl⟩⟩

theorem sq_mem_translations (h : SmallRootStage R X U P n)
    (h3 : 3 ≤ (gmsRootConjugates (U ⊔ R) R).ncard) (hE : GMSHasRegularNormal U R) :
    ∀ x ∈ normalizer ((U ⊔ R : Subgroup D) : Set D) ⊓ centralizer (U : Set D), x * x ∈ U := by
  classical
  obtain ⟨t, htR, ht1⟩ := h.exists_ne_one
  have hS := h.setup h3 htR ht1
  obtain ⟨htr, hV₁, d, hdN, -, hT⟩ := h.exists_isTorus_translations hE hS
  set W := normalizer ((U ⊔ R : Subgroup D) : Set D) ⊓ centralizer (U : Set D) with hW
  have hWcard : Nat.card W = 2 * 2 ^ n * 2 ^ n := h.card_translations hS htr
  obtain ⟨hn3, -, -, -, ⟨-, -, -, hUcard⟩, -⟩ := h.1
  have hUW : U ≤ W := le_sup_left.trans hS.V_le_tr
  have hWU : W ≤ normalizer (U : Set D) := inf_le_right.trans (centralizer_le_normalizer _)
  have : (U.subgroupOf W).Normal := (normal_subgroupOf_iff_le_normalizer hUW).mpr hWU
  have hsqV : ∀ x ∈ W, x * x ∈ U ⊔ R := by
    intro x hx
    rw [← hV₁.comm_eq_one_iff_mem hS (mul_mem hx hx), hS.comm_mul hx hx]
    exact hS.mul_self_U (hS.comm_mem hx)
  have hcommV : ∀ x ∈ W, ∀ y ∈ W, y⁻¹ * x⁻¹ * y * x ∈ U ⊔ R := by
    intro x hx y hy
    have hyx : y⁻¹ * x⁻¹ ∈ W := mul_mem (inv_mem hy) (inv_mem hx)
    rw [← hV₁.comm_eq_one_iff_mem hS (mul_mem (mul_mem hyx hy) hx),
      hS.comm_mul (mul_mem hyx hy) hx, hS.comm_mul hyx hy, hS.comm_mul (inv_mem hy) (inv_mem hx),
      hV₁.comm_inv hS hx, hV₁.comm_inv hS hy]
    have := hS.mul_self_U (mul_mem (hS.comm_mem hy) (hS.comm_mem hx))
    simpa only [mul_assoc] using this
  obtain ⟨π, hπdef⟩ : ∃ π : W →* W ⧸ U.subgroupOf W, π = QuotientGroup.mk' (U.subgroupOf W) :=
    ⟨_, rfl⟩
  have hπsurj : Function.Surjective π := by
    rw [hπdef]
    exact QuotientGroup.mk'_surjective _
  have hπeq : ∀ x y : W, π x = π y ↔ (x : D)⁻¹ * y ∈ U := fun x y => by
    rw [hπdef, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, mem_subgroupOf]
    simp
  have hπone : ∀ x : W, π x = 1 ↔ (x : D) ∈ U := fun x => by
    rw [← map_one π, hπeq, OneMemClass.coe_one, mul_one, inv_mem_iff]
  have htW : t ∈ W := hS.V_le_tr hS.t_mem_V
  obtain ⟨z, hz⟩ : ∃ z, z = π ⟨t, htW⟩ := ⟨_, rfl⟩
  have hVcase : ∀ w : W, (w : D) ∈ U ⊔ R → π w = 1 ∨ π w = z := by
    intro w hwV
    rcases hS.mem_or_mul_mem hwV with h1 | h1
    · exact Or.inl ((hπone w).mpr h1)
    · right
      rw [hz, hπeq]
      show (w : D)⁻¹ * t ∈ U
      have e : (w : D)⁻¹ * t = ((w : D) * t)⁻¹ := by
        rw [mul_inv_rev, hS.inv_t]
        exact hS.commute_V (inv_mem hwV) hS.t_mem_V
      rw [e]
      exact inv_mem h1
  have hz1 : z ≠ 1 := fun h1 => hS.t_notMem_U ((hπone ⟨t, htW⟩).mp (hz ▸ h1))
  have hz2 : z ^ 2 = 1 := by
    have h1 : (⟨t, htW⟩ : W) ^ 2 = 1 := Subtype.ext (by
      rw [coe_pow, sq]
      exact hS.mul_self_t)
    rw [hz, ← map_pow, h1, map_one]
  have hzc : ∀ w, z * w = w * z := by
    intro w
    obtain ⟨x, rfl⟩ := hπsurj w
    rw [hz, ← map_mul, ← map_mul, hπeq]
    show (t * (x : D))⁻¹ * ((x : D) * t) ∈ U
    have e : (t * (x : D))⁻¹ * ((x : D) * t) = (x : D)⁻¹ * t * (x : D)⁻¹⁻¹ * t := by
      rw [inv_inv, mul_inv_rev, hS.inv_t]
      group
    rw [e]
    exact hS.comm_mem (inv_mem x.2)
  have hsq' : ∀ w, w ^ 2 = 1 ∨ w ^ 2 = z := by
    intro w
    obtain ⟨x, rfl⟩ := hπsurj w
    rw [← map_pow, sq]
    exact hVcase (x * x) (hsqV x x.2)
  have hcomm' : ∀ a b, b⁻¹ * a⁻¹ * b * a = 1 ∨ b⁻¹ * a⁻¹ * b * a = z := by
    intro a b
    obtain ⟨x, rfl⟩ := hπsurj a
    obtain ⟨y, rfl⟩ := hπsurj b
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
    exact hVcase _ (hcommV x x.2 y y.2)
  have h16 : 16 ≤ Nat.card (W ⧸ U.subgroupOf W) := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (U.subgroupOf W)
    rw [hWcard, Nat.card_congr (subgroupOfEquivOfLe hUW).toEquiv, hUcard] at h1
    have hpos : 0 < 2 ^ n := by positivity
    have h2 : Nat.card (W ⧸ U.subgroupOf W) = 2 * 2 ^ n := Nat.eq_of_mul_eq_mul_right hpos h1.symm
    have h8 : 8 ≤ 2 ^ n :=
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
    omega
  have hdW : d ∈ normalizer (W : Set D) := hT.mem_normalizer
  have hdU : d ∈ normalizer (U : Set D) := (mem_inf.mp hdN).2
  have hdWk : ∀ (k : ℕ) (x : W), d ^ k * (x : D) * (d ^ k)⁻¹ ∈ W := fun k x =>
    (mem_normalizer_iff.mp (pow_mem hdW k) x).mp x.2
  obtain ⟨δ, hδπ⟩ : ∃ δ : MulAut (W ⧸ U.subgroupOf W), ∀ x : W,
      δ (π x) = π ⟨d * x * d⁻¹, (mem_normalizer_iff.mp hdW x).mp x.2⟩ := by
    set e : MulAut W := W.normalizerMonoidHom ⟨d, hdW⟩ with he
    have heapp : ∀ x : W, ((e x : W) : D) = d * x * d⁻¹ := fun x =>
      normalizerMonoidHom_apply_apply_coe W ⟨d, hdW⟩ x
    have hemap : (U.subgroupOf W).map (e : W →* W) = U.subgroupOf W := by
      ext x
      rw [mem_map]
      constructor
      · rintro ⟨y, hy, rfl⟩
        rw [mem_subgroupOf] at hy ⊢
        change ((e y : W) : D) ∈ U
        rw [heapp]
        exact (mem_normalizer_iff.mp hdU y).mp hy
      · intro hx
        rw [mem_subgroupOf] at hx
        have h1 : d⁻¹ * (x : D) * d ∈ W := by
          have := (mem_normalizer_iff.mp (inv_mem hdW) x).mp x.2
          simpa using this
        have h2 : d⁻¹ * (x : D) * d ∈ U := by
          have := (mem_normalizer_iff.mp (inv_mem hdU) x).mp hx
          simpa using this
        refine ⟨⟨d⁻¹ * x * d, h1⟩, mem_subgroupOf.mpr h2, Subtype.ext ?_⟩
        change ((e ⟨d⁻¹ * x * d, h1⟩ : W) : D) = x
        rw [heapp]
        group
    refine ⟨QuotientGroup.congr (U.subgroupOf W) (U.subgroupOf W) e hemap, fun x => ?_⟩
    rw [hπdef, QuotientGroup.congr_mk']
    exact congrArg _ (Subtype.ext (heapp x))
  have hδpow : ∀ (k : ℕ) (x : W), (δ ^ k) (π x) = π ⟨d ^ k * x * (d ^ k)⁻¹, hdWk k x⟩ := by
    intro k
    induction k with
    | zero =>
      intro x
      rw [pow_zero, MulAut.one_apply]
      exact congrArg π (Subtype.ext (by simp))
    | succ k ih =>
      intro x
      rw [pow_succ, MulAut.mul_apply, hδπ, ih]
      refine congrArg π (Subtype.ext ?_)
      show d ^ k * (d * (x : D) * d⁻¹) * (d ^ k)⁻¹ = d ^ (k + 1) * x * (d ^ (k + 1))⁻¹
      group
  have hδz : δ z = z := by
    rw [hz, hδπ]
    refine congrArg π (Subtype.ext ?_)
    show d * t * d⁻¹ = t
    rw [hT.commute, mul_inv_cancel_right]
  have htrans' : ∀ x y : W ⧸ U.subgroupOf W, x ≠ 1 → x ≠ z → y ≠ 1 → y ≠ z →
      ∃ k : ℕ, (δ ^ k) x = y ∨ (δ ^ k) x = y * z := by
    intro x y hx1 hxz hy1 hyz
    obtain ⟨a, rfl⟩ := hπsurj x
    obtain ⟨b, rfl⟩ := hπsurj y
    have haV : (a : D) ∉ U ⊔ R := fun h1 => (hVcase a h1).elim hx1 hxz
    have hbV : (b : D) ∉ U ⊔ R := fun h1 => (hVcase b h1).elim hy1 hyz
    obtain ⟨k, hk⟩ := hT.exists_pow_conj hV₁ hS b.2 hbV a.2 haV
    refine ⟨k, ?_⟩
    rw [hδpow]
    set c : W := ⟨d ^ k * a * (d ^ k)⁻¹, hdWk k a⟩ with hc
    have hbc : π c = π b * π (b⁻¹ * c) := by rw [← map_mul, mul_inv_cancel_left]
    rcases hVcase (b⁻¹ * c) hk with h1 | h1
    · left
      rw [hbc, h1, mul_one]
    · right
      rw [hbc, h1]
  have hall := forall_sq_eq_one_of_central_transitive hz1 hz2 hzc hsq' hcomm' h16 δ hδz htrans'
  intro x hx
  have h1 := hall (π ⟨x, hx⟩)
  rw [← map_pow, hπone, coe_pow, sq] at h1
  exact h1

end SmallRootStage

variable {D : Type} [Group D] [Finite D] {R X U P : Subgroup D} {n : ℕ}

theorem smallRoot_layer (h : SmallRootStage R X U P n)
    (h3 : 3 ≤ (gmsRootConjugates (U ⊔ R) R).ncard) (hE : GMSHasRegularNormal U R) :
    let V := U ⊔ R
    let W := normalizer (V : Set D) ⊓ centralizer (U : Set D)
    let Y := normalizer (V : Set D) ⊓ normalizer (R : Set D)
    (∀ x ∈ W, x * x ∈ U) ∧ (∀ x ∈ W, ∀ y ∈ W, x * y * x⁻¹ * y⁻¹ ∈ U) ∧
    ∃ Up : Subgroup D, U ≤ Up ∧ Up ≤ W ∧ Up ⊓ (U ⊔ R) = U ∧ Up ⊔ R = W ∧
      Y ≤ normalizer (Up : Set D) ∧ X ⊓ normalizer (U : Set D) ≤ normalizer (Up : Set D) ∧
      (∀ r ∈ R, r ≠ 1 → ∀ x ∈ Up, x * r * x⁻¹ * r⁻¹ ∈ U) ∧
      (∀ r ∈ R, r ≠ 1 → ∀ x ∈ Up, x * r * x⁻¹ * r⁻¹ = 1 → x ∈ U) ∧
      (∀ r ∈ R, r ≠ 1 → ∀ u ∈ U, ∃ x ∈ Up, x * r * x⁻¹ * r⁻¹ = u) := by
  intro V W Y
  have hsq : ∀ x ∈ W, x * x ∈ U := h.sq_mem_translations h3 hE
  obtain ⟨t, htR, ht1⟩ := h.exists_ne_one
  have hS := h.setup h3 htR ht1
  obtain ⟨htr, hV₁, d, hdN, hNX, hT⟩ := h.exists_isTorus_translations hE hS
  have hWA : ∀ r ∈ W, ∀ a ∈ U, r * a = a * r := fun r hr a ha =>
    (mem_centralizer_iff.mp (mem_inf.mp hr).2 a ha).symm
  have hcomm : ∀ x ∈ W, ∀ y ∈ W, x * y * x⁻¹ * y⁻¹ ∈ U := fun x hx y hy =>
    GMS28.commutator_mem_of_sq_mem hWA hsq hx hy
  obtain ⟨U₁, hAU, hUV₁, hUV, hsup, -, -, hdN₁, hV₁N, -, hcU₁, -, hcker, hconto, -, -, hmax⟩ :=
    hV₁.exists_U₁ hS htr hT hdN hsq
  have hUW : U ≤ W := le_sup_left.trans hS.V_le_tr
  have hNXU : X ⊓ normalizer (U : Set D) ≤ normalizer (U₁ : Set D) := by
    rw [hNX]
    exact sup_le (hUW.trans hV₁N) (zpowers_le.mpr hdN₁)
  have hY : Y ≤ normalizer (U₁ : Set D) := by
    intro y hy
    obtain ⟨hyV, hyR⟩ := mem_inf.mp hy
    have hyU : y ∈ normalizer (U : Set D) := hS.normalizer_V_le hyV
    have hyW : y ∈ normalizer (W : Set D) := hS.normalizer_V_le_normalizer_tr hyV
    obtain ⟨-, -, hyNXU, -⟩ := gms_LR_normalizes h.1 hyV hyR
    have hydy : y⁻¹ * d * y ∈ X ⊓ normalizer (U : Set D) := by
      have := (mem_normalizer_iff.mp (inv_mem hyNXU) d).mp hdN
      rwa [inv_inv] at this
    obtain ⟨U', hU'⟩ : ∃ U' : Subgroup D, U' = U₁.map (MulAut.conj y).toMonoidHom := ⟨_, rfl⟩
    have hmemU' : ∀ x, x ∈ U' ↔ y⁻¹ * x * y ∈ U₁ := fun x => by rw [hU', mem_map_conj_iff]
    have hconjU : ∀ a ∈ U, y⁻¹ * a * y ∈ U := fun a ha => by
      have := (mem_normalizer_iff.mp (inv_mem hyU) a).mp ha
      rwa [inv_inv] at this
    have hAU' : U ≤ U' := fun a ha => (hmemU' a).mpr (hAU (hconjU a ha))
    have hU'W : U' ≤ W := fun x hx => by
      have h1 := (mem_normalizer_iff.mp hyW _).mp (hUV₁ ((hmemU' x).mp hx))
      rwa [show y * (y⁻¹ * x * y) * y⁻¹ = x by group] at h1
    have hU'V : U' ⊓ (U ⊔ R) = U := by
      refine le_antisymm (fun x hx => ?_) (le_inf hAU' le_sup_left)
      obtain ⟨hxU', hxV⟩ := mem_inf.mp hx
      have h1 : y⁻¹ * x * y ∈ U := by
        rw [← hUV]
        refine mem_inf.mpr ⟨(hmemU' x).mp hxU', ?_⟩
        have := (mem_normalizer_iff.mp (inv_mem hyV) x).mp hxV
        rwa [inv_inv] at this
      have h2 := (mem_normalizer_iff.mp hyU _).mp h1
      rwa [show y * (y⁻¹ * x * y) * y⁻¹ = x by group] at h2
    have hU'd : ∀ u ∈ U', d * u * d⁻¹ ∈ U' := by
      intro u hu
      rw [hmemU'] at hu ⊢
      have e1 : y⁻¹ * (d * u * d⁻¹) * y =
          (y⁻¹ * d * y) * (y⁻¹ * u * y) * (y⁻¹ * d * y)⁻¹ := by group
      rw [e1]
      exact (mem_normalizer_iff.mp (hNXU hydy) _).mp hu
    have hle := hmax U' hAU' hU'W hU'V hU'd
    refine GMS28.mem_normalizer_of_conj_mem_of_finite fun u hu => hle ?_
    rw [hmemU', show y⁻¹ * (y * u * y⁻¹) * y = u by group]
    exact hu
  have hrt : ∀ r ∈ R, r ≠ 1 → r = t := fun r hr hr1 => (hS.eq_one_or_eq_t hr).resolve_left hr1
  refine ⟨hsq, hcomm, U₁, hAU, hUV₁, hUV, hsup, hY, hNXU, fun r hr hr1 x hx => ?_,
    fun r hr hr1 x hx hx1 => ?_, fun r hr hr1 u hu => ?_⟩
  · rw [hrt r hr hr1, hS.inv_t]
    exact hcU₁ x hx
  · rw [hrt r hr hr1, hS.inv_t] at hx1
    exact (hcker x hx).mp hx1
  · rw [hrt r hr hr1, hS.inv_t]
    exact hconto u hu

namespace SmallRootStage

theorem translations_le_normalizer (h : SmallRootStage R X U P n)
    (h3 : 3 ≤ (gmsRootConjugates (U ⊔ R) R).ncard) (hE : GMSHasRegularNormal U R)
    {Up : Subgroup D} (h1 : U ≤ Up)
    (h2 : Up ≤ normalizer ((U ⊔ R : Subgroup D) : Set D) ⊓ centralizer (U : Set D)) :
    normalizer ((U ⊔ R : Subgroup D) : Set D) ⊓ centralizer (U : Set D) ≤
      normalizer (Up : Set D) := by
  obtain ⟨-, hcomm, -⟩ := smallRoot_layer h h3 hE
  intro w hw
  refine GMS28.mem_normalizer_of_conj_mem_of_finite fun x hx => ?_
  have e : w * x * w⁻¹ = (w * x * w⁻¹ * x⁻¹) * x := by group
  rw [e]
  exact mul_mem (h1 (hcomm w hw x (h2 hx))) hx

theorem card_of_layer (h : SmallRootStage R X U P n)
    (h3 : 3 ≤ (gmsRootConjugates (U ⊔ R) R).ncard) {Up : Subgroup D} (h1 : U ≤ Up)
    (h2 : Up ≤ normalizer ((U ⊔ R : Subgroup D) : Set D) ⊓ centralizer (U : Set D))
    (h3' : Up ⊓ (U ⊔ R) = U)
    (h8 : ∀ r ∈ R, r ≠ 1 → ∀ u ∈ U, ∃ x ∈ Up, x * r * x⁻¹ * r⁻¹ = u) :
    Nat.card Up = 2 ^ n * 2 ^ n := by
  obtain ⟨t, htR, ht1⟩ := h.exists_ne_one
  have hS := h.setup h3 htR ht1
  obtain ⟨-, -, -, -, ⟨-, -, -, hUcard⟩, -⟩ := h.1
  let φ : Up →* U :=
    { toFun := fun x => ⟨(x : D) * t * (x : D)⁻¹ * t, hS.comm_mem (h2 x.2)⟩
      map_one' := Subtype.ext (by simp [hS.mul_self_t])
      map_mul' := fun a b => Subtype.ext (hS.comm_mul (h2 a.2) (h2 b.2)) }
  have hsurj : Function.Surjective φ := fun u => by
    obtain ⟨x, hx, hxt⟩ := h8 t htR ht1 u u.2
    refine ⟨⟨x, hx⟩, Subtype.ext ?_⟩
    change x * t * x⁻¹ * t = u
    rw [hS.inv_t] at hxt
    exact hxt
  have hker : φ.ker = U.subgroupOf Up := by
    ext x
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    have e1 : φ x = 1 ↔ (x : D) * t * (x : D)⁻¹ * t = 1 :=
      ⟨fun h4 => congrArg Subtype.val h4, fun h4 => Subtype.ext h4⟩
    rw [e1, h.comm_eq_one_iff_mem hS (h2 x.2)]
    constructor
    · intro h4
      have h5 := mem_inf.mpr ⟨x.2, h4⟩
      rwa [h3'] at h5
    · exact fun h4 => mem_sup_left h4
  have h4 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hsurj).toEquiv, hker,
    Nat.card_congr (subgroupOfEquivOfLe h1).toEquiv, hUcard] at h4
  exact h4

theorem comm_conj_of_mem_normalizer (h : SmallRootStage R X U P n)
    (h3 : 3 ≤ (gmsRootConjugates (U ⊔ R) R).ncard) {r : D} (hr : r ∈ R) (hr1 : r ≠ 1) {y : D}
    (hy : y ∈ normalizer (R : Set D)) (x : D) :
    (y * x * y⁻¹) * r * (y * x * y⁻¹)⁻¹ * r⁻¹ = y * (x * r * x⁻¹ * r⁻¹) * y⁻¹ := by
  have hS := h.setup h3 hr hr1
  have hyr : y * r * y⁻¹ = r :=
    GMS28.conj_eq_of_mem_normalizer_zpowers hS.mul_self_t hr1 (hS.eq_zpowers ▸ hy)
  have hyr' : y⁻¹ * r * y = r := by
    calc y⁻¹ * r * y = y⁻¹ * (y * r * y⁻¹) * y := by rw [hyr]
      _ = r := by group
  have hyr'' : y⁻¹ * r⁻¹ * y = r⁻¹ := by
    calc y⁻¹ * r⁻¹ * y = (y⁻¹ * r * y)⁻¹ := by group
      _ = r⁻¹ := by rw [hyr']
  calc (y * x * y⁻¹) * r * (y * x * y⁻¹)⁻¹ * r⁻¹
      = y * x * (y⁻¹ * r * y) * x⁻¹ * (y⁻¹ * r⁻¹ * y) * y⁻¹ := by group
    _ = y * (x * r * x⁻¹ * r⁻¹) * y⁻¹ := by rw [hyr', hyr'']; group

end SmallRootStage

end CFSG.SeitzReduction.RankOne
