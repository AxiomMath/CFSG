module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicJ2EndBasic
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicStandard17
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo1Cen2B

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Co1

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoSporadic CFSG.ComponentClassification.RankTwoSporadic.J2End

section Four

variable {U : Type*} [Group U] {a b : U}

theorem fourSet_mul (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) {x y : U}
    (hx : x ∈ fourSet a b) (hy : y ∈ fourSet a b) : x * y ∈ fourSet a b := by
  have e1 : a * (a * b) = b := by rw [← mul_assoc, ha, one_mul]
  have e2 : b * (a * b) = a := by rw [← mul_assoc, ← hab, mul_assoc, hb, mul_one]
  have e3 : a * b * a = b := by rw [mul_assoc, ← hab, ← mul_assoc, ha, one_mul]
  have e4 : a * b * b = a := by rw [mul_assoc, hb, mul_one]
  have e5 : a * b * (a * b) = 1 := by rw [← mul_assoc, e3, hb]
  have m1 : (1 : U) ∈ fourSet a b := Or.inl rfl
  have ma : a ∈ fourSet a b := Or.inr (Or.inl rfl)
  have mb : b ∈ fourSet a b := Or.inr (Or.inr (Or.inl rfl))
  have mab : a * b ∈ fourSet a b := Or.inr (Or.inr (Or.inr rfl))
  rcases mem_four hx with h1 | h1 | h1 | h1 <;> rcases mem_four hy with h2 | h2 | h2 | h2 <;>
    rw [h1, h2]
  · rw [one_mul]; exact m1
  · rw [one_mul]; exact ma
  · rw [one_mul]; exact mb
  · rw [one_mul]; exact mab
  · rw [mul_one]; exact ma
  · rw [ha]; exact m1
  · exact mab
  · rw [e1]; exact mb
  · rw [mul_one]; exact mb
  · rw [← hab]; exact mab
  · rw [hb]; exact m1
  · rw [e2]; exact ma
  · rw [mul_one]; exact mab
  · rw [e3]; exact mb
  · rw [e4]; exact ma
  · rw [e5]; exact m1

theorem fourSet_inv (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) {x : U}
    (hx : x ∈ fourSet a b) : x⁻¹ ∈ fourSet a b := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  rcases mem_four hx with h | h | h | h <;> rw [h]
  · rw [inv_one]; exact Or.inl rfl
  · rw [hai]; exact Or.inr (Or.inl rfl)
  · rw [hbi]; exact Or.inr (Or.inr (Or.inl rfl))
  · rw [mul_inv_rev, hai, hbi, ← hab]; exact Or.inr (Or.inr (Or.inr rfl))

theorem mem_closure_pair_iff (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) {x : U} :
    x ∈ closure ({a, b} : Set U) ↔ x ∈ fourSet a b := by
  constructor
  · intro hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with rfl | hy
      · exact Or.inr (Or.inl rfl)
      · rw [Set.mem_singleton_iff.mp hy]
        exact Or.inr (Or.inr (Or.inl rfl))
    | one => exact Or.inl rfl
    | mul y z _ _ hy hz => exact fourSet_mul ha hb hab hy hz
    | inv y _ hy => exact fourSet_inv ha hb hab hy
  · intro hx
    rcases mem_four hx with h | h | h | h <;> rw [h]
    · exact one_mem _
    · exact subset_closure (Set.mem_insert _ _)
    · exact subset_closure (Set.mem_insert_of_mem _ rfl)
    · exact mul_mem (subset_closure (Set.mem_insert _ _))
        (subset_closure (Set.mem_insert_of_mem _ rfl))

end Four

theorem mem_of_isSylowOf_of_commute {G : Type*} [Group G] [Finite G] {P H : Subgroup G}
    (hP : IsSylowOf 2 P H) {x : G} (hxH : x ∈ H) (hx2 : x ^ 2 = 1)
    (hxP : ∀ y ∈ P, x * y = y * x) : x ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx : IsPGroup 2 (zpowers x) := by
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (orderOf_dvd_of_pow_eq_one (show x ^ (2 ^ 1) = 1 by simpa using hx2))
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  have hPN : P ≤ normalizer (zpowers x : Set G) := fun y hy =>
    Subgroup.centralizer_le_normalizer _ (by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨n, rfl⟩
      exact Commute.zpow_left (hxP y hy) n)
  have hQ := IsPGroup.to_sup_of_normal_right' hP.isPGroup hx hPN
  have heq := hP.eq_of_le le_sup_left (sup_le hP.le (zpowers_le.mpr hxH)) hQ
  rw [← heq]
  exact mem_sup_right (mem_zpowers x)

section Action

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {W : Type*} [Group W]
  {ψ : normalizer (A : Set G) →* W}

omit [Finite G] in
theorem eq_of_map_eq (hψ : IsActionHom A ⊤ ψ) (hZ : Odd (Nat.card (center A)))
    {u v : normalizer (A : Set G)} (hu : (u : G) ^ 2 = 1) (hv : (v : G) ^ 2 = 1)
    (hA : (u : G)⁻¹ * v ∈ A) (h : ψ u = ψ v) : u = v := by
  have hK : (u : G)⁻¹ * v ∈ centralizer (A : Set G) := by
    have h1 : ψ (u⁻¹ * v) = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
    simpa using (hψ.eq_one_iff _).mp h1
  have hc : (u : G) * ((u : G)⁻¹ * v) = ((u : G)⁻¹ * v) * u :=
    commute_of_map_mem hψ (mem_top (ψ u)) hA hK
  have hz2 : ((u : G)⁻¹ * v) ^ 2 = 1 := by
    have e : (v : G) ^ 2 = ((u : G)⁻¹ * v) ^ 2 := by
      calc (v : G) ^ 2 = ((u : G) * ((u : G)⁻¹ * v)) ^ 2 := by group
        _ = (u : G) ^ 2 * ((u : G)⁻¹ * v) ^ 2 := Commute.mul_pow hc 2
        _ = ((u : G)⁻¹ * v) ^ 2 := by rw [hu, one_mul]
    rw [← e, hv]
  have hz := eq_one_of_mem_of_sq_eq_one hZ hA hK hz2
  apply Subtype.ext
  calc (u : G) = u * ((u : G)⁻¹ * v) := by rw [hz, mul_one]
    _ = v := by group

theorem exists_decomp (hψ : IsActionHom A ⊤ ψ) (hZ : Odd (Nat.card (center A)))
    {R : Subgroup G} (hR : IsSylowOf 2 R (centralizer (A : Set G)))
    {t : normalizer (A : Set G)} (ht2 : (t : G) ^ 2 = 1) (htR : ∀ r ∈ R, (t : G) * r = r * t) :
    ∃ d : G, ∃ hd : d ∈ A, ∃ r ∈ R, (t : G) = d * r ∧ d ^ 2 = 1 ∧
      ψ ⟨d, le_normalizer hd⟩ = ψ t := by
  obtain ⟨a, ha, hae⟩ := hψ.exists_eq (ψ t) (mem_top _)
  set k : G := a⁻¹ * t with hk
  have hkK : k ∈ centralizer (A : Set G) := by
    have h1 : ψ ((⟨a, le_normalizer ha⟩ : normalizer (A : Set G))⁻¹ * t) = 1 := by
      rw [map_mul, map_inv, hae, inv_mul_cancel]
    simpa using (hψ.eq_one_iff _).mp h1
  have hak : a * k = k * a := mem_centralizer_iff.mp hkK a ha
  have htak : (t : G) = a * k := by rw [hk]; group
  have hk2 : k ^ 2 = (a ^ 2)⁻¹ := by
    have h1 : (a * k) ^ 2 = 1 := by rw [← htak]; exact ht2
    rw [Commute.mul_pow hak 2] at h1
    exact eq_inv_of_mul_eq_one_right h1
  have hk2A : k ^ 2 ∈ A := by rw [hk2]; exact A.inv_mem (pow_mem ha 2)
  have hk2K : k ^ 2 ∈ centralizer (A : Set G) := pow_mem hkK 2
  obtain ⟨j, hj⟩ := odd_orderOf_of_mem hZ hk2A hk2K
  set r : G := k ^ (2 * j + 1) with hr
  have hrK : r ∈ centralizer (A : Set G) := pow_mem hkK _
  have hr2 : r ^ 2 = 1 := by
    calc r ^ 2 = (k ^ 2) ^ (2 * j + 1) := by rw [hr, ← pow_mul, ← pow_mul, mul_comm]
      _ = 1 := by rw [← hj, pow_orderOf_eq_one]
  have hkR : ∀ s ∈ R, k * s = s * k := by
    intro s hs
    have h1 : a⁻¹ * s = s * a⁻¹ := mem_centralizer_iff.mp (hR.le hs) a⁻¹ (A.inv_mem ha)
    calc k * s = a⁻¹ * ((t : G) * s) := by rw [hk, mul_assoc]
      _ = a⁻¹ * (s * t) := by rw [htR s hs]
      _ = (a⁻¹ * s) * t := by rw [mul_assoc]
      _ = (s * a⁻¹) * t := by rw [h1]
      _ = s * k := by rw [hk, mul_assoc]
  have hrR : r ∈ R := mem_of_isSylowOf_of_commute hR hrK hr2 fun s hs =>
    Commute.pow_left (hkR s hs) _
  have hd : (t : G) * r⁻¹ = a * ((k ^ 2) ^ j)⁻¹ := by
    rw [htak, hr]
    group
  have hdA : (t : G) * r⁻¹ ∈ A := by
    rw [hd]
    exact A.mul_mem ha (A.inv_mem (pow_mem hk2A j))
  have htr : (t : G) * r = r * t := htR r hrR
  have hrN : r ∈ normalizer (A : Set G) := Subgroup.centralizer_le_normalizer _ hrK
  refine ⟨(t : G) * r⁻¹, hdA, r, hrR, by group, ?_, ?_⟩
  · have hc : Commute (t : G) r⁻¹ := Commute.inv_right htr
    rw [hc.mul_pow, ht2, one_mul, inv_pow, hr2, inv_one]
  · have h1 : ψ ⟨r, hrN⟩ = 1 := (hψ.eq_one_iff _).mpr hrK
    have e : (⟨(t : G) * r⁻¹, le_normalizer hdA⟩ : normalizer (A : Set G)) =
        t * (⟨r, hrN⟩ : normalizer (A : Set G))⁻¹ := Subtype.ext rfl
    rw [e, map_mul, map_inv, h1, inv_one, mul_one]

omit [Finite G] in
theorem commute_of_decomp (hψ : IsActionHom A ⊤ ψ) (hZ : Odd (Nat.card (center A)))
    {c : G} (hc : c ∈ A) {t : normalizer (A : Set G)} {d r : G} (hd : d ∈ A)
    (hrK : r ∈ centralizer (A : Set G)) (htdr : (t : G) = d * r) (hd2 : d ^ 2 = 1)
    (hψd : ψ ⟨d, le_normalizer hd⟩ = ψ t)
    (h : ψ ⟨c, le_normalizer hc⟩ * ψ t = ψ t * ψ ⟨c, le_normalizer hc⟩) :
    c * t = t * c := by
  set cN : normalizer (A : Set G) := ⟨c, le_normalizer hc⟩ with hcN
  set dN : normalizer (A : Set G) := ⟨d, le_normalizer hd⟩ with hdN
  have hv : dN = cN * dN * cN⁻¹ := by
    refine eq_of_map_eq hψ hZ hd2 ?_ ?_ ?_
    · change (c * d * c⁻¹) ^ 2 = 1
      rw [conj_pow, hd2, mul_one, mul_inv_cancel]
    · change d⁻¹ * (c * d * c⁻¹) ∈ A
      exact A.mul_mem (A.inv_mem hd) (A.mul_mem (A.mul_mem hc hd) (A.inv_mem hc))
    · rw [map_mul, map_mul, map_inv, hψd, h, mul_inv_cancel_right]
  have hcd : c * d * c⁻¹ = d := (congrArg Subtype.val hv).symm
  have hcr : c * r = r * c := mem_centralizer_iff.mp hrK c hc
  rw [htdr]
  calc c * (d * r) = (c * d * c⁻¹) * (c * r) := by group
    _ = d * (r * c) := by rw [hcd, hcr]
    _ = d * r * c := by group

theorem mem_of_swap (hA : AS76b.Hyp31 A) (hψ : IsActionHom A ⊤ ψ)
    (hZ : Odd (Nat.card (center A))) {g : G} (hg : g ∉ normalizer (A : Set G)) {T R : Subgroup G}
    (hT : IsSylowOf 2 T (rightConjugate (centralizer (A : Set G)) g)) (hTab : ∀ x ∈ T, x ^ 2 = 1)
    (hR : IsSylowOf 2 R (centralizer (A : Set G))) (hRc : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x)
    {s s' : normalizer (A : Set G)} (hs : (s : G) ∈ T) (hs' : (s' : G) ∈ T) (hs1 : (s : G) ≠ 1)
    (hsR : ∀ r ∈ R, (s : G) * r = r * s) (hs'R : ∀ r ∈ R, (s' : G) * r = r * s')
    (hss' : ψ s * ψ s' = ψ s' * ψ s) {c' : W} (hcs : c' * ψ s = ψ s * c')
    (hcs' : c' * ψ s' = ψ s * ψ s' * c') : (s : G) ∈ A := by
  have hK := tightlyEmbedded_centralizer_of_standard hA.standard
  obtain ⟨d, hd, r, hrR, hsdr, hd2, hψd⟩ := exists_decomp hψ hZ hR (hTab s hs) hsR
  obtain ⟨d', hd', r', hr'R, hs'dr, hd'2, hψd'⟩ := exists_decomp hψ hZ hR (hTab s' hs') hs'R
  have hrK : r ∈ centralizer (A : Set G) := hR.le hrR
  have hr'K : r' ∈ centralizer (A : Set G) := hR.le hr'R
  obtain ⟨c, hc, hce⟩ := hψ.exists_eq c' (mem_top _)
  have hcsG : c * s = s * c :=
    commute_of_decomp hψ hZ hc hd hrK hsdr hd2 hψd (by rw [hce]; exact hcs)
  have hcN := mem_normalizer_of_commute_of_tightlyEmbedded
    (tightlyEmbedded_rightConjugate' hK g) (hT.le hs) hs1 (hTab s hs) hcsG
  have hcs'K : c * s' * c⁻¹ ∈ rightConjugate (centralizer (A : Set G)) g :=
    (mem_normalizer_iff.mp hcN s').mp (hT.le hs')
  have hds' : d * s' = s' * d :=
    commute_of_decomp hψ hZ hd hd' hr'K hs'dr hd'2 hψd' (by rw [hψd]; exact hss')
  have hdr' : d * r' = r' * d := mem_centralizer_iff.mp hr'K d hd
  have hdd' : d * d' = d' * d := by
    have h1 : d * d' * r' = d' * d * r' := by
      calc d * d' * r' = d * s' := by rw [hs'dr, mul_assoc]
        _ = s' * d := hds'
        _ = d' * (r' * d) := by rw [hs'dr, mul_assoc]
        _ = d' * d * r' := by rw [← hdr', mul_assoc]
    exact mul_right_cancel h1
  have hu2 : (d * d') ^ 2 = 1 := by rw [(Commute.mul_pow hdd' 2), hd2, hd'2, one_mul]
  have hv2 : (c * d' * c⁻¹) ^ 2 = 1 := by rw [conj_pow, hd'2, mul_one, mul_inv_cancel]
  have huA : d * d' ∈ A := A.mul_mem hd hd'
  have hvA : c * d' * c⁻¹ ∈ A := A.mul_mem (A.mul_mem hc hd') (A.inv_mem hc)
  have huv : (⟨d * d', le_normalizer huA⟩ : normalizer (A : Set G)) =
      ⟨c * d' * c⁻¹, le_normalizer hvA⟩ := by
    refine eq_of_map_eq hψ hZ hu2 hv2 (A.mul_mem (A.inv_mem huA) hvA) ?_
    have e1 : (⟨d * d', le_normalizer huA⟩ : normalizer (A : Set G)) =
        ⟨d, le_normalizer hd⟩ * ⟨d', le_normalizer hd'⟩ := Subtype.ext rfl
    have e2 : (⟨c * d' * c⁻¹, le_normalizer hvA⟩ : normalizer (A : Set G)) =
        ⟨c, le_normalizer hc⟩ * ⟨d', le_normalizer hd'⟩ * ⟨c, le_normalizer hc⟩⁻¹ :=
      Subtype.ext rfl
    rw [e1, e2, map_mul, map_mul, map_mul, map_inv, hψd, hψd', hce, hcs', mul_inv_cancel_right]
  have hcd' : c * d' * c⁻¹ = d * d' := (congrArg Subtype.val huv).symm
  have hcr' : c * r' = r' * c := mem_centralizer_iff.mp hr'K c hc
  have hd'r : d' * r = r * d' := mem_centralizer_iff.mp hrK d' hd'
  have hrr' : r * r' = r' * r := hRc r hrR r' hr'R
  have hconj : c * s' * c⁻¹ = d * d' * r' := by
    rw [hs'dr]
    calc c * (d' * r') * c⁻¹ = (c * d' * c⁻¹) * (c * r' * c⁻¹) := by group
      _ = d * d' * r' := by rw [hcd', hcr', mul_inv_cancel_right]
  have hrinv : r⁻¹ = ((s : G) * s')⁻¹ * (c * s' * c⁻¹) := by
    rw [hconj, hsdr, hs'dr]
    have e : d * r * (d' * r') = d * d' * (r' * r) := by
      calc d * r * (d' * r') = d * (r * d') * r' := by group
        _ = d * (d' * r) * r' := by rw [hd'r]
        _ = d * d' * (r * r') := by group
        _ = d * d' * (r' * r) := by rw [hrr']
    rw [e]
    group
  have hrKg : r ∈ rightConjugate (centralizer (A : Set G)) g := by
    have h1 : r⁻¹ ∈ rightConjugate (centralizer (A : Set G)) g := by
      rw [hrinv]
      exact mul_mem (inv_mem (mul_mem (hT.le hs) (hT.le hs'))) hcs'K
    simpa using inv_mem h1
  have hdr : d * r = r * d := mem_centralizer_iff.mp hrK d hd
  have hr2 : r ^ 2 = 1 := by
    have h1 := hTab s hs
    rw [hsdr, Commute.mul_pow hdr 2, hd2, one_mul] at h1
    exact h1
  have hr1 := eq_one_of_mem_inf hA hg hrK hrKg hr2
  rw [hsdr, hr1, mul_one]
  exact hd

theorem conj_comm {U : Type*} [Group U] (w : U) {c x : U} (h : c * x = x * c) :
    w * c * w⁻¹ * (w * x * w⁻¹) = w * x * w⁻¹ * (w * c * w⁻¹) := by
  calc w * c * w⁻¹ * (w * x * w⁻¹) = w * (c * x) * w⁻¹ := by group
    _ = w * (x * c) * w⁻¹ := by rw [h]
    _ = w * x * w⁻¹ * (w * c * w⁻¹) := by group

theorem conj_swap {U : Type*} [Group U] (w : U) {c x x' : U} (h : c * x' = x * x' * c) :
    w * c * w⁻¹ * (w * x' * w⁻¹) = w * x * w⁻¹ * (w * x' * w⁻¹) * (w * c * w⁻¹) := by
  calc w * c * w⁻¹ * (w * x' * w⁻¹) = w * (c * x') * w⁻¹ := by group
    _ = w * (x * x' * c) * w⁻¹ := by rw [h]
    _ = w * x * w⁻¹ * (w * x' * w⁻¹) * (w * c * w⁻¹) := by group

theorem le_of_swap [Finite W] (h32 : AS76b.Lemma32) (hA : AS76b.Hyp31 A) (hψ : IsActionHom A ⊤ ψ)
    (hZ : Odd (Nat.card (center A))) {g : G} (hg : g ∉ normalizer (A : Set G)) {T R : Subgroup G}
    (hT : IsSylowOf 2 T (rightConjugate (centralizer (A : Set G)) g))
    (hTN : T ≤ normalizer (A : Set G)) (hR : IsSylowOf 2 R (centralizer (A : Set G)))
    (hTR : ∀ t ∈ T, ∀ r ∈ R, t * r = r * t)
    {e₁ e₂ c₁ c₂ w : W} (he₁ : e₁ * e₁ = 1) (he₂ : e₂ * e₂ = 1) (he : e₁ * e₂ = e₂ * e₁)
    (he₁1 : e₁ ≠ 1) (he₂1 : e₂ ≠ 1) (hc₁ : c₁ * e₁ = e₁ * c₁) (hc₁' : c₁ * e₂ = e₁ * e₂ * c₁)
    (hc₂ : c₂ * e₂ = e₂ * c₂) (hc₂' : c₂ * e₁ = e₂ * e₁ * c₂)
    (hw : (T.subgroupOf (normalizer (A : Set G))).map ψ =
      (closure ({e₁, e₂} : Set W)).map (MulAut.conj w).toMonoidHom) :
    T ≤ A := by
  have hTab := sq_eq_one_of_isSylowOf h32 hA hT
  have hRab := h32 G A hA R hR
  have hRc : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x := fun x hx y hy => comm_of_isElemAbelian hRab hx hy
  have hbot := inf_centralizer_eq_bot hA hg hT
  have hinj : ∀ s (hs : s ∈ T) s' (hs' : s' ∈ T), ψ ⟨s, hTN hs⟩ = ψ ⟨s', hTN hs'⟩ → s = s' := by
    intro s hs s' hs' h
    have h1 : ψ (⟨s, hTN hs⟩⁻¹ * ⟨s', hTN hs'⟩) = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
    have hK' : s⁻¹ * s' ∈ centralizer (A : Set G) := by simpa using (hψ.eq_one_iff _).mp h1
    have hT' : s⁻¹ * s' ∈ T := mul_mem (inv_mem hs) hs'
    have : s⁻¹ * s' ∈ T ⊓ centralizer (A : Set G) := mem_inf.mpr ⟨hT', hK'⟩
    rw [hbot, mem_bot] at this
    calc s = s * (s⁻¹ * s') := by rw [this, mul_one]
      _ = s' := by group
  have hsurj : ∀ x ∈ closure ({e₁, e₂} : Set W), ∃ s, ∃ hs : s ∈ T,
      ψ ⟨s, hTN hs⟩ = w * x * w⁻¹ := by
    intro x hx
    have h1 : w * x * w⁻¹ ∈ (T.subgroupOf (normalizer (A : Set G))).map ψ := by
      rw [hw]
      exact ⟨x, hx, rfl⟩
    obtain ⟨m, hm, hme⟩ := h1
    exact ⟨m, hm, hme⟩
  have hover : ∀ s (hs : s ∈ T), ∃ x ∈ closure ({e₁, e₂} : Set W),
      ψ ⟨s, hTN hs⟩ = w * x * w⁻¹ := by
    intro s hs
    have h1 : ψ ⟨s, hTN hs⟩ ∈ (T.subgroupOf (normalizer (A : Set G))).map ψ := ⟨_, hs, rfl⟩
    rw [hw] at h1
    obtain ⟨x, hx, hxe⟩ := h1
    exact ⟨x, hx, hxe.symm⟩
  obtain ⟨t₁, ht₁, hψ₁⟩ := hsurj e₁ (subset_closure (Set.mem_insert _ _))
  obtain ⟨t₂, ht₂, hψ₂⟩ := hsurj e₂ (subset_closure (Set.mem_insert_of_mem _ rfl))
  have hne : ∀ {x : W}, x ≠ 1 → w * x * w⁻¹ ≠ 1 := fun hx h => hx (by
    have := congrArg (fun y => w⁻¹ * y * w) h
    simpa [mul_assoc] using this)
  have ht1 : ∀ {s : G} (hs : s ∈ T) {x : W}, ψ ⟨s, hTN hs⟩ = w * x * w⁻¹ → x ≠ 1 → s ≠ 1 :=
    fun hs x hx hx1 h1 => hne hx1 (by
      rw [← hx, show (⟨_, hTN hs⟩ : normalizer (A : Set G)) = 1 from Subtype.ext h1, map_one])
  have hss' : ψ ⟨t₁, hTN ht₁⟩ * ψ ⟨t₂, hTN ht₂⟩ = ψ ⟨t₂, hTN ht₂⟩ * ψ ⟨t₁, hTN ht₁⟩ := by
    rw [hψ₁, hψ₂]
    exact conj_comm w he
  have hA₁ : t₁ ∈ A := mem_of_swap (s := ⟨t₁, hTN ht₁⟩) (s' := ⟨t₂, hTN ht₂⟩) hA hψ hZ hg hT hTab
    hR hRc ht₁ ht₂ (ht1 ht₁ hψ₁ he₁1) (hTR t₁ ht₁) (hTR t₂ ht₂) hss' (c' := w * c₁ * w⁻¹)
    (by rw [hψ₁]; exact conj_comm w hc₁) (by rw [hψ₁, hψ₂]; exact conj_swap w hc₁')
  have hA₂ : t₂ ∈ A := mem_of_swap (s := ⟨t₂, hTN ht₂⟩) (s' := ⟨t₁, hTN ht₁⟩) hA hψ hZ hg hT hTab
    hR hRc ht₂ ht₁ (ht1 ht₂ hψ₂ he₂1) (hTR t₂ ht₂) (hTR t₁ ht₁) hss'.symm (c' := w * c₂ * w⁻¹)
    (by rw [hψ₂]; exact conj_comm w hc₂) (by rw [hψ₁, hψ₂]; exact conj_swap w hc₂')
  intro s hs
  obtain ⟨x, hx, hxe⟩ := hover s hs
  have hx4 := (mem_closure_pair_iff he₁ he₂ he).mp hx
  have hψ₁₂ : ψ ⟨t₁ * t₂, hTN (mul_mem ht₁ ht₂)⟩ = w * (e₁ * e₂) * w⁻¹ := by
    rw [show (⟨t₁ * t₂, hTN (mul_mem ht₁ ht₂)⟩ : normalizer (A : Set G)) =
      ⟨t₁, hTN ht₁⟩ * ⟨t₂, hTN ht₂⟩ from Subtype.ext rfl, map_mul, hψ₁, hψ₂]
    group
  rcases mem_four hx4 with h | h | h | h <;> rw [h] at hxe
  · have : s = 1 := hinj s hs 1 (one_mem _) (by
      rw [hxe, mul_one, mul_inv_cancel, ← map_one ψ]; rfl)
    rw [this]
    exact one_mem _
  · rw [hinj s hs t₁ ht₁ (hxe.trans hψ₁.symm)]
    exact hA₁
  · rw [hinj s hs t₂ ht₂ (hxe.trans hψ₂.symm)]
    exact hA₂
  · rw [hinj s hs (t₁ * t₂) (mul_mem ht₁ ht₂) (hxe.trans hψ₁₂.symm)]
    exact mul_mem hA₁ hA₂

theorem exc17_of_sylow [Finite W] (h32 : AS76b.Lemma32) (hA : AS76b.Hyp31 A) {X₀ : Type*}
    [Group X₀] {X : Subgroup W} (hW : AutModel X₀ W X) (hWX : ⁅(⊤ : Subgroup W), ⊤⁆ ≤ X)
    (e : ↥A ⧸ center ↥A ≃* X₀) (hψ : IsActionHom A X ψ) {Exc : Subgroup W → Prop}
    (hc : YCensus17 X Exc) {g : G} (hg : g ∉ normalizer (A : Set G)) {T : Subgroup G}
    (hT1 : IsSylowOf 2 T (rightConjugate (centralizer (A : Set G)) g ⊓ normalizer (A : Set G)))
    (hT2 : IsSylowOf 2 T (rightConjugate (centralizer (A : Set G)) g)) :
    Exc ((T.subgroupOf (normalizer (A : Set G))).map ψ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hYc : YCensus X (fun E => Exc E ∨ PWitness X E) := fun E h1 h2 h3 =>
    (hc E h1 h2 (fun h => h3 (Or.inl h))).resolve_right (fun h => h3 (Or.inr h))
  rcases exc_of_sylow h32 hA hψ hYc hg hT1 hT2 with hExc | hPW
  · exact hExc
  exfalso
  have hR := h32 G A hA
  have hK := tightlyEmbedded_centralizer_of_standard hA.standard
  set A' := rightConjugate A g
  have hCA' : centralizer (A' : Set G) = rightConjugate (centralizer (A : Set G)) g :=
    centralizer_rightConjugate A g
  have hK2 : ∀ k ∈ centralizer (A' : Set G), IsPGroup 2 (zpowers k) → k ^ 2 = 1 := by
    intro k hk hk2
    rw [hCA'] at hk
    have hkK : g * k * g⁻¹ ∈ centralizer (A : Set G) := (mem_rightConjugate_iff _ g k).mp hk
    have h2 : IsPGroup 2 (zpowers (g * k * g⁻¹)) := by
      have := hk2.map (MulAut.conj g).toMonoidHom
      rwa [MonoidHom.map_zpowers] at this
    have hsq := sq_eq_one_of_isPGroup_zpowers hR hkK h2
    have hc' : (g * k * g⁻¹) ^ 2 = g * k ^ 2 * g⁻¹ := conj_pow
    rw [hc'] at hsq
    have := congrArg (fun y => g⁻¹ * y * g) hsq
    simpa [mul_assoc] using this
  have hTC : T ≤ centralizer (A' : Set G) := hCA' ▸ hT2.le
  have hQ : ∀ t ∈ T, t ≠ 1 → ∀ c ∈ A, c * t = t * c → c ∈ normalizer (A' : Set G) := by
    intro t ht ht1 c _ hct
    have ht2 : t ^ 2 = 1 := hK2 t (hTC ht) (hT2.isPGroup.to_le (zpowers_le.mpr ht))
    have hcK := mem_normalizer_of_commute_of_tightlyEmbedded
      (tightlyEmbedded_rightConjugate' hK g) (hT2.le ht) ht1 ht2 hct
    rw [RankTwoSporadic.mem_normalizer_rightConjugate_iff, hA.standard.2.2.2.1] at hcK
    exact RankTwoSporadic.mem_normalizer_rightConjugate_iff.mpr hcK
  let eA : ↥A' ≃* ↥A := rightConjugateEquiv' A g
  have hA'p : commutator ↥A' = ⊤ := by
    have : Group.IsPerfect ↥A := (Group.isPerfect_def).2 hA.standard.1.1
    exact (Group.isPerfect_def).1
      (Group.IsPerfect.ofSurjective (f := eA.symm.toMonoidHom) eA.symm.surjective)
  let e' : ↥A' ⧸ center ↥A' ≃* X₀ :=
    (QuotientGroup.congr (center ↥A') (center ↥A) eA (map_center_eq eA)).trans e
  obtain ⟨ψ', hψ'⟩ := exists_isActionHom hW hA'p e'
  exact not_pWitness_map hψ hψ' hWX hTC hQ hK2 hPW

end Action

end CFSG.ComponentClassification.RankTwoSporadic.Co1
