module

public import CFSG.CGT.Timmesfeld75.Sec7One
public import CFSG.CGT.Timmesfeld75.SLTransvectionOrder

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped MatrixGroups Matrix commutatorElement

variable {G : Type} [Group G] {T T₁ : Subgroup G} {n m : ℕ}

theorem pow_mem_of_pow_image_eq_one {H : Subgroup G} [(T.subgroupOf H).Normal] {F : Type*}
    [Field F] {e : ↥H ⧸ T.subgroupOf H ≃* SL(n, F)} {g : ↥H} {j : ℕ}
    (h : (e (QuotientGroup.mk g)) ^ j = 1) : (g : G) ^ j ∈ T := by
  have h1 : e (QuotientGroup.mk (g ^ j)) = 1 := by
    rw [QuotientGroup.mk_pow, map_pow]
    exact h
  have h2 : (QuotientGroup.mk (g ^ j) : ↥H ⧸ T.subgroupOf H) = 1 := by
    apply e.injective
    rw [h1, map_one]
  have h3 := (QuotientGroup.eq_one_iff (N := T.subgroupOf H) (g ^ j)).1 h2
  simpa using Subgroup.mem_subgroupOf.1 h3

theorem Sec6Ctx.false_of_normD_pair (h1 : Sec4NoA) (h62 : Sec62) (h63 : Sec63)
    (hc : Sec6Ctx T T₁ n m) (hA8 : ¬ (n = 4 ∧ m = 1))
    (hnat : NaturalSL T (hSub T (normIn T₁ T)) n m) {x y : G} (hx : x ∈ normD T)
    (hy : y ∈ normD T) {k : ℕ} (hk : Odd k) (hk3 : 3 ≤ k) (ho : orderOf (x * y) = 2 * k) :
    False := by
  have := hc.finite
  have hTab := hc.hy.pair.wc.1
  have hx2 : x * x = 1 := mul_self_eq_one_of_mem_classD hTab hx.1
  have hy2 : y * y = 1 := mul_self_eq_one_of_mem_classD hTab hy.1
  by_cases hxyT : x ∈ T ∨ y ∈ T
  · exact false_of_sq_mem hTab hk3 ho (sq_mem_of_mem_normalizer hx2 hy2 hx.2 hy.2 hxyT)
  push Not at hxyT
  obtain ⟨hxT, hyT⟩ := hxyT
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hN, ε, φ, hcompat, htr⟩ := hc.sec67_transv h1 h63 hA8 hnat
  have := hN
  obtain ⟨hxH, hux⟩ := htr x hx hxT
  obtain ⟨hyH, huy⟩ := htr y hy hyT
  have hw : ε (QuotientGroup.mk (⟨x, hxH⟩ * ⟨y, hyH⟩ : ↥(hSub T (normIn T₁ T)))) =
      ε (QuotientGroup.mk ⟨x, hxH⟩) * ε (QuotientGroup.mk ⟨y, hyH⟩) := by
    rw [QuotientGroup.mk_mul, map_mul]
  rcases IsTransvection.orderOf_mul_cases hux huy with h4 | hodd
  ·
    have h4' : (ε (QuotientGroup.mk (⟨x, hxH⟩ * ⟨y, hyH⟩ :
        ↥(hSub T (normIn T₁ T))))) ^ 4 = 1 := by
      rw [hw]
      exact orderOf_dvd_iff_pow_eq_one.1 h4
    have hmem : (x * y) ^ 4 ∈ T := pow_mem_of_pow_image_eq_one h4'
    have hsq : (x * y) ^ 4 * (x * y) ^ 4 = 1 := elemAbelian_mul_self hTab hmem
    have h8 : (x * y) ^ 8 = 1 := by
      rw [show (8 : ℕ) = 4 + 4 from rfl, pow_add]
      exact hsq
    have hdvd : 2 * k ∣ 8 := by
      rw [← ho]
      exact orderOf_dvd_of_pow_eq_one h8
    obtain ⟨c, rfl⟩ := hk
    have h' : 2 * c + 1 ∣ 4 := by
      have : 2 * (2 * c + 1) ∣ 2 * 4 := by simpa using hdvd
      exact (Nat.mul_dvd_mul_iff_left (by norm_num)).1 this
    have hle := Nat.le_of_dvd (by norm_num) h'
    have hc1 : c = 1 := by omega
    subst hc1
    norm_num at h'
  ·
    set g : ↥(hSub T (normIn T₁ T)) := ⟨x, hxH⟩ * ⟨y, hyH⟩ with hg
    have hpow : (ε (QuotientGroup.mk g)) ^ orderOf (ε (QuotientGroup.mk g)) = 1 :=
      pow_orderOf_eq_one _
    have hmem : (x * y) ^ orderOf (ε (QuotientGroup.mk g)) ∈ T := by
      have := pow_mem_of_pow_image_eq_one (e := ε) (g := g) hpow
      exact this
    have hdvd : orderOf (ε (QuotientGroup.mk g)) ∣ 2 * k := by
      have h1' := orderOf_map_dvd (ε.toMonoidHom.comp (QuotientGroup.mk' _)) g
      have h2' : orderOf g = orderOf (x * y) := (Subgroup.orderOf_coe g).symm
      rw [← ho, ← h2']
      exact h1'
    have hodd' : Odd (orderOf (ε (QuotientGroup.mk g))) := by
      rw [hw]
      exact hodd
    have hcop : Nat.Coprime (orderOf (ε (QuotientGroup.mk g))) 2 := by
      refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 ?_)
      intro h2
      obtain ⟨c, hc⟩ := hodd'
      omega
    have hdk : orderOf (ε (QuotientGroup.mk g)) ∣ k := hcop.dvd_of_dvd_mul_left hdvd
    obtain ⟨r, hr⟩ := hdk
    have hzT : (x * y) ^ k ∈ T := by
      rw [hr, pow_mul]
      exact T.pow_mem hmem r
    exact hc.false_of_center_mem_T h1 h62 h63 hA8 hnat hx.1 hy.1 hk3 ho hzT

theorem Sec6Ctx.pow_four_mem_of_fixed (h1 : Sec4NoA) (h63 : Sec63) (hc : Sec6Ctx T T₁ n m)
    (hA8 : ¬ (n = 4 ∧ m = 1)) (hnat : NaturalSL T (hSub T (normIn T₁ T)) n m) {x c a : G}
    (hx : x ∈ normD T) (hc' : c ∈ normD T) (hcT : c ∉ T) (ha : a ∈ T) (ha1 : a ≠ 1)
    (hac : a ∈ commSub c T) (hxa : x * a = a * x) : (x * c) ^ 4 ∈ T := by
  have := hc.finite
  have hTab := hc.hy.pair.wc.1
  have hx2 : x * x = 1 := mul_self_eq_one_of_mem_classD hTab hx.1
  have hc2 : c * c = 1 := mul_self_eq_one_of_mem_classD hTab hc'.1
  by_cases hxT : x ∈ T
  · have hsq : (x * c) ^ 2 ∈ T := sq_mem_of_mem_normalizer hx2 hc2 hx.2 hc'.2 (Or.inl hxT)
    have e : (x * c) ^ 4 = ((x * c) ^ 2) ^ 2 := by rw [← pow_mul]
    rw [e]
    exact T.pow_mem hsq 2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hN, ε, φ, hcompat, htr⟩ := hc.sec67_transv h1 h63 hA8 hnat
  have := hN
  obtain ⟨hxH, hux⟩ := htr x hx hxT
  obtain ⟨hcH, huc⟩ := htr c hc' hcT
  obtain ⟨fx, vx, hfvx, hvx, hux'⟩ := hux.exists_data
  obtain ⟨fc, vc, hfvc, hvc, huc'⟩ := huc.exists_data
  set α := Multiplicative.toAdd (φ ⟨a, ha⟩) with hα
  have hα0 : α ≠ 0 := by
    intro h0
    have h1' : φ ⟨a, ha⟩ = 1 := by
      have : φ ⟨a, ha⟩ = Multiplicative.ofAdd 0 := by
        rw [← h0]
        rfl
      simpa using this
    have h2' : (⟨a, ha⟩ : ↥T) = 1 := φ.injective (h1'.trans φ.map_one.symm)
    exact ha1 (congrArg Subtype.val h2')
  obtain ⟨t, htT, hat⟩ := (mem_commSub_iff hTab (by rw [pow_two]; exact hc2) hc'.2).1 hac
  have hct : ⁅c, t⁆ ∈ T := comm_mem_of_mem_normalizer hc'.2 htT
  have hcomm := toAdd_phi_comm hcompat hcH hc'.2 htT hct
  have haeq : (⟨a, ha⟩ : ↥T) = ⟨⁅c, t⁆, hct⟩ := Subtype.ext hat
  rw [← haeq] at hcomm
  set τ := Multiplicative.toAdd (φ ⟨t, htT⟩) with hτ
  have hαv : α = fc τ • vc := by
    rw [hα, hcomm, huc' τ]
    abel
  have hxN := hx.2
  have hmem : x * a * x⁻¹ ∈ T := conj_mem_of_mem_normalizer hxN ha
  have hxa' : x * a * x⁻¹ = a := by
    rw [hxa]
    group
  have hfix : (ε (QuotientGroup.mk (⟨x, hxH⟩ : ↥(hSub T (normIn T₁ T)))) :
      SL(n, GaloisField 2 m)) *ᵥ α = α := by
    have h := hcompat ⟨x, hxH⟩ ⟨a, ha⟩ hmem
    have h' : (⟨x * a * x⁻¹, hmem⟩ : ↥T) = ⟨a, ha⟩ := Subtype.ext hxa'
    rw [h'] at h
    have := congrArg Multiplicative.toAdd h
    simpa using this.symm
  have hfx0 : fx α = 0 := by
    have h2 := hux' α
    rw [hfix] at h2
    have h4 : fx α • vx = 0 := by
      have := h2
      simpa using this
    exact (smul_eq_zero.1 h4).resolve_right hvx
  have hl0 : fc τ ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hαv
    exact hα0 hαv
  have hfxvc : fx vc = 0 := by
    rw [hαv, map_smul, smul_eq_mul] at hfx0
    exact (mul_eq_zero.1 hfx0).resolve_left hl0
  have h4 : (ε (QuotientGroup.mk ⟨x, hxH⟩) * ε (QuotientGroup.mk ⟨c, hcH⟩)) ^ 4 = 1 :=
    mul_pow_four_eq_one hfvx hfvc hux' huc' (by rw [hfxvc, zero_mul])
  have h4' : (ε (QuotientGroup.mk (⟨x, hxH⟩ * ⟨c, hcH⟩ :
      ↥(hSub T (normIn T₁ T))))) ^ 4 = 1 := by
    rw [QuotientGroup.mk_mul, map_mul]
    exact h4
  exact pow_mem_of_pow_image_eq_one h4'

end CFSG.CGT.Timmesfeld75
