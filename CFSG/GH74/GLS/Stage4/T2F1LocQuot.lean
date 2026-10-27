module

public import CFSG.GH74.GLS.Stage1.Thm6.Prod.Resid

public section

namespace CFSG.GH74.GLS.Stage4.Rest.F1Loc

theorem centralizer_mk_eq_map {X : Type} [Group X] (R : Subgroup X) [R.Normal]
    (hR : ∀ x ∈ R, Odd (orderOf x)) {z : X} (hz : z * z = 1) :
    Subgroup.centralizer ({(QuotientGroup.mk z : X ⧸ R)} : Set (X ⧸ R)) =
      (Subgroup.centralizer ({z} : Set X)).map (QuotientGroup.mk' R) := by
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  ext xbar
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective xbar
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hg
    have hy2 : (g * z * g⁻¹) * (g * z * g⁻¹) = 1 := by
      calc (g * z * g⁻¹) * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
        _ = 1 := by rw [hz]; group
    have hyi : (g * z * g⁻¹)⁻¹ = g * z * g⁻¹ := inv_eq_of_mul_eq_one_right hy2
    have hyz : (g * z * g⁻¹) * z ∈ R := by
      rw [← QuotientGroup.eq_one_iff]
      calc (↑((g * z * g⁻¹) * z) : X ⧸ R) = ↑g * ↑z * (↑g)⁻¹ * ↑z := by
            simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
        _ = ↑z * ↑g * (↑g)⁻¹ * ↑z := by rw [hg]
        _ = ↑(z * z) := by rw [QuotientGroup.mk_mul]; group
        _ = 1 := by rw [hz, QuotientGroup.mk_one]
    obtain ⟨m, hm⟩ := hR _ hyz
    obtain ⟨r', hr'R, hr'sq, hzr'⟩ : ∃ r' ∈ R, r' * r' = (g * z * g⁻¹) * z ∧
        z * r' * z⁻¹ = r'⁻¹ := by
      have hzr : z * ((g * z * g⁻¹) * z) * z⁻¹ = ((g * z * g⁻¹) * z)⁻¹ := by
        rw [hzi]
        calc z * ((g * z * g⁻¹) * z) * z = z * (g * z * g⁻¹) * (z * z) := by group
          _ = z * (g * z * g⁻¹) := by rw [hz, mul_one]
          _ = ((g * z * g⁻¹) * z)⁻¹ := by rw [mul_inv_rev, hyi, hzi]
      refine ⟨((g * z * g⁻¹) * z) ^ (m + 1), R.pow_mem hyz _, ?_, ?_⟩
      · rw [← pow_add]
        have : m + 1 + (m + 1) = orderOf ((g * z * g⁻¹) * z) + 1 := by omega
        rw [this, pow_succ, pow_orderOf_eq_one, one_mul]
      · rw [← conj_pow, hzr, inv_pow]
    have hkey : r' * z * r'⁻¹ = g * z * g⁻¹ := by
      calc r' * z * r'⁻¹ = r' * z * (z * r' * z⁻¹) := by rw [hzr']
        _ = r' * (z * z) * r' * z := by rw [hzi]; group
        _ = r' * r' * z := by rw [hz, mul_one]
        _ = (g * z * g⁻¹) * z * z := by rw [hr'sq]
        _ = g * z * g⁻¹ := by rw [mul_assoc _ z z, hz, mul_one]
    refine ⟨r'⁻¹ * g, Subgroup.mem_centralizer_singleton_iff.2 ?_, ?_⟩
    · calc r'⁻¹ * g * z = r'⁻¹ * (g * z * g⁻¹) * g := by group
        _ = r'⁻¹ * (r' * z * r'⁻¹) * g := by rw [hkey]
        _ = z * (r'⁻¹ * g) := by group
    · rw [QuotientGroup.mk'_apply, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        (QuotientGroup.eq_one_iff r').2 hr'R, inv_one, one_mul]
  · rintro ⟨c, hc, hcg⟩
    have hc := Subgroup.mem_centralizer_singleton_iff.1 hc
    have h := congrArg (QuotientGroup.mk : X → X ⧸ R) hc
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul] at h
    rw [QuotientGroup.mk'_apply] at hcg
    rw [← hcg]
    exact h

private theorem oPrimeResidualOf_eq_closure_aux {G : Type} [Group G] (p : ℕ) (K : Subgroup G) :
    oPrimeResidualOf p K = Subgroup.closure {x : G | x ∈ K ∧ ∃ k : ℕ, x ^ p ^ k = 1} := by
  unfold oPrimeResidualOf oPrimeResidual
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨k, hk⟩, rfl⟩
    exact ⟨y.2, k, by simpa using congrArg Subtype.val hk⟩
  · rintro ⟨hx, k, hk⟩
    exact ⟨⟨x, hx⟩, ⟨k, Subtype.ext (by simpa using hk)⟩, rfl⟩

theorem oPrimeResidualOf_map_mk {X : Type} [Group X] [Finite X] (R : Subgroup X) [R.Normal]
    (A : Subgroup X) :
    oPrimeResidualOf 2 (A.map (QuotientGroup.mk' R)) =
      (oPrimeResidualOf 2 A).map (QuotientGroup.mk' R) := by
  have hmap := Stage1.Thm6.Prod.map_oPrimeResidual ((QuotientGroup.mk' R).subgroupMap A)
    ((QuotientGroup.mk' R).subgroupMap_surjective A) Nat.prime_two
  have hcomm : (A.map (QuotientGroup.mk' R)).subtype.comp ((QuotientGroup.mk' R).subgroupMap A) =
      (QuotientGroup.mk' R).comp A.subtype := by
    ext x
    rfl
  unfold oPrimeResidualOf
  rw [← hmap, Subgroup.map_map, hcomm, ← Subgroup.map_map]

theorem oPrimeResidualOf_eq_of_two_elements {X : Type} [Group X] {A B : Subgroup X} (hAB : A ≤ B)
    (h : ∀ b ∈ B, (∃ k : ℕ, b ^ (2 ^ k) = 1) → b ∈ A) :
    oPrimeResidualOf 2 A = oPrimeResidualOf 2 B := by
  rw [oPrimeResidualOf_eq_closure_aux, oPrimeResidualOf_eq_closure_aux]
  congr 1
  ext x
  constructor
  · rintro ⟨hx, hk⟩
    exact ⟨hAB hx, hk⟩
  · rintro ⟨hx, hk⟩
    exact ⟨h x hx hk, hk⟩

end CFSG.GH74.GLS.Stage4.Rest.F1Loc
