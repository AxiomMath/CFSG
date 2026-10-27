module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.CoverFixCount
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.QuatPair

public section

namespace CFSG.EvenSporadicStandard.Induction.CoverFix

open Subgroup

variable {K G : Type*} [Group K] [Group G]

theorem commutator_mul_central {a b z w : K} (hz : z ∈ center K) (hw : w ∈ center K) :
    (a * z) * (b * w) * (a * z)⁻¹ * (b * w)⁻¹ = a * b * a⁻¹ * b⁻¹ := by
  have hz' := Subgroup.mem_center_iff.mp hz
  have hw' := Subgroup.mem_center_iff.mp hw
  have hzw : z * w * z⁻¹ = w := by rw [← hz' w]; group
  calc a * z * (b * w) * (a * z)⁻¹ * (b * w)⁻¹ =
      a * (z * b) * w * z⁻¹ * a⁻¹ * w⁻¹ * b⁻¹ := by group
    _ = a * (b * z) * w * z⁻¹ * a⁻¹ * w⁻¹ * b⁻¹ := by rw [← hz' b]
    _ = a * b * (z * w * z⁻¹) * a⁻¹ * w⁻¹ * b⁻¹ := by group
    _ = a * b * (w * a⁻¹) * w⁻¹ * b⁻¹ := by rw [hzw]; group
    _ = a * b * (a⁻¹ * w) * w⁻¹ * b⁻¹ := by rw [← hw' a⁻¹]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem inv_mul_apply_mem_center (π : K →* G) (hZ : π.ker ≤ center K) {α : MulAut K}
    {β : MulAut G} (h : ∀ x, π (α x) = β (π x)) {a : K} (ha : β (π a) = π a) :
    a⁻¹ * α a ∈ center K := hZ (by
  rw [MonoidHom.mem_ker, map_mul, map_inv, h a, ha, inv_mul_cancel])

theorem exists_comm_involution (π : K →* G) (hπ : Function.Surjective π) (hZ : π.ker ≤ center K)
    {α : MulAut K} {β : MulAut G} (h : ∀ x, π (α x) = β (π x)) {x y : G} (hxy : Q8Rel x y)
    (hxf : β x = x) (hyf : β y = y) : ∃ z : K, α z = z ∧ z * z = 1 ∧ π z = x * x := by
  obtain ⟨a, rfl⟩ := hπ x
  obtain ⟨b, rfl⟩ := hπ y
  have hda := inv_mul_apply_mem_center π hZ h hxf
  have hdb := inv_mul_apply_mem_center π hZ h hyf
  refine ⟨a * b * a⁻¹ * b⁻¹, ?_, ?_, ?_⟩
  · have e : α (a * b * a⁻¹ * b⁻¹) = (a * (a⁻¹ * α a)) * (b * (b⁻¹ * α b)) *
        (a * (a⁻¹ * α a))⁻¹ * (b * (b⁻¹ * α b))⁻¹ := by
      simp only [map_mul, map_inv, mul_inv_cancel_left]
    rw [e]
    exact commutator_mul_central hda hdb
  · have h3 : b⁻¹ * a * b * a ∈ center K := hZ (by
      rw [MonoidHom.mem_ker]
      simp only [map_mul, map_inv]
      calc (π b)⁻¹ * π a * π b * π a = (π b)⁻¹ * (π a * π b * π a) := by group
        _ = 1 := by rw [hxy.conj_eq]; group)
    have h2 : a * a * (b * b)⁻¹ ∈ center K := hZ (by
      rw [MonoidHom.mem_ker]
      simp only [map_mul, map_inv]
      rw [hxy.sq_eq]
      group)
    exact commutator_sq_eq_one h3 h2
  · simp only [map_mul, map_inv]
    have h1 : π a * π b = π b * (π a)⁻¹ := by
      calc π a * π b = (π a * π b * π a) * (π a)⁻¹ := by group
        _ = π b * (π a)⁻¹ := by rw [hxy.conj_eq]
    have h2 : π b * (π a)⁻¹ * (π b)⁻¹ = π a := by
      calc π b * (π a)⁻¹ * (π b)⁻¹ = (π a * π b) * (π b)⁻¹ := by rw [h1]
        _ = π a := by group
    calc π a * π b * (π a)⁻¹ * (π b)⁻¹ = (π b * (π a)⁻¹) * (π a)⁻¹ * (π b)⁻¹ := by rw [h1]
      _ = (π b * (π a)⁻¹ * (π b)⁻¹) * (π b * (π a)⁻¹ * (π b)⁻¹) := by group
      _ = π a * π a := by rw [h2]

theorem exists_involution_pow {P : Subgroup K} (hP : IsPGroup 2 P) {p : K} (hp : p ∈ P)
    (hp1 : p ≠ 1) : ∃ n : ℕ, p ^ n ∈ P ∧ p ^ n * p ^ n = 1 ∧ p ^ n ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hP) ⟨p, hp⟩
  rw [Subgroup.orderOf_mk] at hk
  have hk1 : k ≠ 0 := by
    rintro rfl
    exact hp1 (orderOf_eq_one_iff.1 (by simpa using hk))
  have h2 : 2 ∣ orderOf p := by
    rw [hk]
    exact dvd_pow_self 2 hk1
  have hne : orderOf p ≠ 0 := by
    rw [hk]
    positivity
  have ho : orderOf (p ^ (orderOf p / 2)) = 2 := orderOf_pow_orderOf_div hne h2
  refine ⟨orderOf p / 2, P.pow_mem hp _, ?_, ?_⟩
  · have := pow_orderOf_eq_one (p ^ (orderOf p / 2))
    rw [ho] at this
    rw [← pow_two]
    exact this
  · intro h1
    rw [h1, orderOf_one] at ho
    omega

theorem exists_fixed_two_subgroup [Finite K] (π : K →* G) (hπ : Function.Surjective π)
    (hZ : π.ker ≤ center K) {α : MulAut K} {β : MulAut G} (h : ∀ x, π (α x) = β (π x))
    {x y : G} (hxy : Q8Rel x y) (hxf : β x = x) (hyf : β y = y) :
    ∃ P : Subgroup K, (∀ p ∈ P, α p = p) ∧ IsPGroup 2 P ∧ Nat.card P = 8 ∧
      ((∀ u ∈ fixed α, u ∈ π.ker → u * u = 1 → u = 1) →
        ∃ p ∈ P, ∃ q ∈ P, p * q ≠ q * p) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set B : Subgroup G := closure ({x, y} : Set G) with hB
  have hBcard : Nat.card B = 2 ^ 3 := by
    rw [hB, card_closure_q8 hxy]
    norm_num
  have hxB : x ∈ B := subset_closure (Set.mem_insert _ _)
  have hyB : y ∈ B := subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have : Finite B := Nat.finite_of_card_ne_zero (by rw [hBcard]; norm_num)
  have hBf : ∀ b ∈ B, β b = b := by
    have hle : B ≤ CoverFix.fixed β := by
      rw [hB, closure_le]
      rintro _ (rfl | rfl)
      · exact hxf
      · exact hyf
    exact fun b hb => hle hb
  obtain ⟨P, hPle, hPcard⟩ := exists_subgroup_card_two_pow π hπ hZ h B hBf hBcard
  have hPf : ∀ p ∈ P, α p = p := fun p hp => (Subgroup.mem_inf.1 (hPle hp)).1
  have hPB : ∀ p ∈ P, π p ∈ B := fun p hp => (Subgroup.mem_inf.1 (hPle hp)).2
  have hP2 : IsPGroup 2 P := IsPGroup.of_card hPcard
  refine ⟨P, hPf, hP2, by rw [hPcard]; norm_num, fun hno => ?_⟩
  have hinj : ∀ p ∈ P, π p = 1 → p = 1 := by
    intro p hp hπp
    by_contra hp1
    obtain ⟨n, hnP, hn2, hn1⟩ := exists_involution_pow hP2 hp hp1
    exact hn1 (hno (p ^ n) (hPf _ hnP) (by rw [MonoidHom.mem_ker, map_pow, hπp, one_pow]) hn2)
  let φ : ↥P →* G := π.comp P.subtype
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro p hp
    exact Subtype.ext (hinj p p.2 hp)
  have hrange : φ.range = B := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨p, rfl⟩
      exact hPB p p.2
    · rw [hBcard, Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv.symm, hPcard]
  obtain ⟨p, hp⟩ : x ∈ φ.range := hrange ▸ hxB
  obtain ⟨q, hq⟩ : y ∈ φ.range := hrange ▸ hyB
  refine ⟨p, p.2, q, q.2, fun hc => hxy.not_commute ?_⟩
  have h1 : π (p * q) = π (q * p) := by rw [show (p : K) * q = q * p from hc]
  rw [map_mul, map_mul] at h1
  have e1 : π p = x := hp
  have e2 : π q = y := hq
  rw [e1, e2] at h1
  exact h1

theorem exists_commuting_two_subgroup [Finite K] (π : K →* G) (hπ : Function.Surjective π)
    (hZ : π.ker ≤ center K) {x y : G} (hxy : Q8Rel x y) {g : K} (hg : π g = x * x) :
    ∃ P : Subgroup K, (∀ p ∈ P, g * p = p * g) ∧ IsPGroup 2 P ∧
      ∃ p ∈ P, ∃ q ∈ P, p * q ≠ q * p := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, rfl⟩ := hπ x
  obtain ⟨b, rfl⟩ := hπ y
  have hw : (a * a)⁻¹ * g ∈ center K := hZ (by
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    rw [hg]
    group)
  have h2 : a * a * (b * b)⁻¹ ∈ center K := hZ (by
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    rw [hxy.sq_eq]
    group)
  have hgaw : g = a * a * ((a * a)⁻¹ * g) := by group
  set w : K := (a * a)⁻¹ * g with hwdef
  have hwc := mem_center_iff.1 hw
  have hsq := sq_commute_right h2
  have hga : g * a = a * g := by
    calc g * a = a * a * w * a := by rw [← hgaw]
      _ = a * a * (w * a) := by group
      _ = a * a * (a * w) := by rw [← hwc a]
      _ = a * (a * a * w) := by group
      _ = a * g := by rw [← hgaw]
  have hgb : g * b = b * g := by
    calc g * b = a * a * w * b := by rw [← hgaw]
      _ = a * a * (w * b) := by group
      _ = a * a * (b * w) := by rw [← hwc b]
      _ = (a * a * b) * w := by group
      _ = (b * (a * a)) * w := by rw [hsq]
      _ = b * (a * a * w) := by group
      _ = b * g := by rw [← hgaw]
  set J : Subgroup K := closure ({a, b} : Set K) with hJ
  have hJg : ∀ p ∈ J, g * p = p * g := by
    have hle : J ≤ centralizer {g} := by
      rw [hJ, closure_le]
      rintro _ (rfl | rfl)
      · exact mem_centralizer_singleton_iff.2 hga.symm
      · exact mem_centralizer_singleton_iff.2 hgb.symm
    intro p hp
    exact (mem_centralizer_singleton_iff.1 (hle hp)).symm
  set B : Subgroup G := closure ({π a, π b} : Set G) with hB
  have hBcard : Nat.card B = 2 ^ 3 := by
    rw [hB, card_closure_q8 hxy]
    norm_num
  have : Finite B := Nat.finite_of_card_ne_zero (by rw [hBcard]; norm_num)
  have hJB : J.map π = B := by
    rw [hJ, MonoidHom.map_closure]
    congr 1
    ext z
    simp [Set.image_insert_eq]
  have hmem : ∀ j : J, π j ∈ B := fun j => hJB ▸ Subgroup.mem_map_of_mem π j.2
  let f : ↥J →* ↥B := (π.comp J.subtype).codRestrict B hmem
  have hf : Function.Surjective f := by
    rintro ⟨z, hz⟩
    rw [← hJB] at hz
    obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.1 hz
    exact ⟨⟨j, hj⟩, rfl⟩
  have P₀ : Sylow 2 ↥J := default
  let Q : Sylow 2 ↥B := P₀.mapSurjective hf
  have hQtop : (Q : Subgroup ↥B) = ⊤ := by
    have hB2 : IsPGroup 2 ↥(⊤ : Subgroup ↥B) :=
      IsPGroup.of_card (n := 3) (by rw [Subgroup.card_top, hBcard])
    exact (Q.is_maximal' hB2 le_top).symm
  have hQ : P₀.map f = ⊤ := by
    have := hQtop
    simpa [Q, Sylow.coe_mapSurjective] using this
  have hxP : (⟨π a, subset_closure (Set.mem_insert _ _)⟩ : B) ∈ P₀.map f := by
    rw [hQ]
    exact Subgroup.mem_top _
  have hyP : (⟨π b, subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))⟩ : B) ∈
      P₀.map f := by
    rw [hQ]
    exact Subgroup.mem_top _
  obtain ⟨p, hp, hpx⟩ := Subgroup.mem_map.1 hxP
  obtain ⟨q, hq, hqy⟩ := Subgroup.mem_map.1 hyP
  have e1 : π (p : K) = π a := congrArg Subtype.val hpx
  have e2 : π (q : K) = π b := congrArg Subtype.val hqy
  refine ⟨(P₀ : Subgroup ↥J).map J.subtype, ?_, P₀.2.map J.subtype, p, ⟨p, hp, rfl⟩, q,
    ⟨q, hq, rfl⟩, fun hc => hxy.not_commute ?_⟩
  · rintro _ ⟨j, -, rfl⟩
    exact hJg j j.2
  · have h1 : π ((p : K) * q) = π ((q : K) * p) := by rw [hc]
    rw [map_mul, map_mul, e1, e2] at h1
    exact h1

end CFSG.EvenSporadicStandard.Induction.CoverFix
