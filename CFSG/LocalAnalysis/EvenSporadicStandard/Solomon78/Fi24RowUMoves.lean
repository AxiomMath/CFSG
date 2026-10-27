module

public import CFSG.Sporadic.FischerOddCore.Fi24Block

public section

namespace CFSG.EvenSporadicStandard.Solomon78.Fi24Row

open CFSG.Sporadic.FischerOddCore CFSG.Blueprint.Fischer CFSG.Fischer
open CFSG.Sporadic.Fi24 (R J M MR tR D24 jR cls JR)
open scoped Pointwise

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem exists_conj_mem_centralizer_of_sylow {G : Type*} [Group G] [Finite G] (r : G)
    (hr : ∃ k : ℕ, 2 ^ k ∣ Nat.card (Subgroup.centralizer ({r} : Set G)) ∧
      ¬ 2 ^ (k + 1) ∣ Nat.card G)
    {y : G} (hy : y ^ 2 = 1) : ∃ x : G, x * y * x⁻¹ ∈ Subgroup.centralizer ({r} : Set G) := by
  set C := Subgroup.centralizer ({r} : Set G) with hC
  obtain ⟨k, hk1, hk2⟩ := hr
  have hGk : (Nat.card G).factorization 2 ≤ k := by
    by_contra h
    push Not at h
    exact hk2 ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').2 h)
  have hCk : k ≤ (Nat.card C).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').1 hk1
  have hr : (Nat.card G).factorization 2 ≤ (Nat.card C).factorization 2 := hGk.trans hCk
  obtain ⟨S₀⟩ : Nonempty (Sylow 2 C) := inferInstance
  have hS₀ : Nat.card S₀ = 2 ^ (Nat.card C).factorization 2 := Sylow.card_eq_multiplicity S₀
  have hdvd : (Nat.card C).factorization 2 ≤ (Nat.card G).factorization 2 :=
    (Nat.factorization_le_iff_dvd (Nat.card_pos.ne') (Nat.card_pos.ne')).2
      (Subgroup.card_subgroup_dvd_card C) 2
  have hS : Nat.card (S₀.toSubgroup.map C.subtype) = 2 ^ (Nat.card G).factorization 2 := by
    rw [Subgroup.card_map_of_injective C.subtype_injective, hS₀]
    congr 1
    exact le_antisymm hdvd hr |>.symm ▸ rfl
  let S : Sylow 2 G := Sylow.ofCard (S₀.toSubgroup.map C.subtype) hS
  have hy2 : IsPGroup 2 (Subgroup.zpowers y) := by
    have : Nat.card (Subgroup.zpowers y) ∣ 2 := by
      rw [Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one hy
    rcases (Nat.dvd_prime Nat.prime_two).1 this with h | h
    · exact IsPGroup.of_card (n := 0) (by simpa using h)
    · exact IsPGroup.of_card (n := 1) (by simpa using h)
  obtain ⟨P, hP⟩ := hy2.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S P
  have hyP : y ∈ (P : Subgroup G) := hP (Subgroup.mem_zpowers y)
  rw [← hg] at hyP
  have h1 : g⁻¹ * y * g ∈ (S : Subgroup G) := by
    have hyP' : y ∈ (MulAut.conj g • (S : Subgroup G)) := hyP
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hyP'
    simpa [MulAut.smul_def, MulAut.inv_apply, MulAut.conj_symm_apply, mul_assoc] using hyP'
  refine ⟨g⁻¹, ?_⟩
  obtain ⟨c, hc, hcy⟩ := (Subgroup.mem_map).1
    (show g⁻¹ * y * g ∈ S₀.toSubgroup.map C.subtype from h1)
  rw [inv_inv, ← hcy]
  exact c.2


theorem fi23_card_centralizer_u3 :
    Nat.card ↥(Subgroup.centralizer ({fi23U3} : Set CFSG.Sporadic.Fi23.J)) = 318504960 := by
  have hC := (fi24R2_centralizer_structure).1
  have hroot : fi24R2 • CFSG.Sporadic.Fi24.root = CFSG.Sporadic.Fi24.root :=
    (MulAction.mem_stabilizer_iff (G := J)).1 fi24R2_mem_M
  have hsub : MulAction.orbit fi24C CFSG.Sporadic.Fi24.root ⊆ Set.range fi24FPt := by
    rintro _ ⟨c, rfl⟩
    exact exists_fi24FPt (fi24C_smul_fixed c _ hroot)
  have h1 := card_le_ncard_mul_card_stabilizer (G := fi24C) CFSG.Sporadic.Fi24.root
    (Set.toFinite _) hsub
  have hF : (Set.range fi24FPt).ncard = 504 := by
    rw [← Nat.card_coe_set_eq, Nat.card_range_of_injective fi24FPt_injective, Nat.card_fin]
  have hst : Nat.card ↥(MulAction.stabilizer fi24C CFSG.Sporadic.Fi24.root) ≤
      Nat.card ↥(Subgroup.centralizer ({fi23U3} : Set CFSG.Sporadic.Fi23.J)) := by
    have hM : ∀ c : ↥(MulAction.stabilizer fi24C CFSG.Sporadic.Fi24.root), ((c : fi24C) : J) ∈ M :=
      fun c => (MulAction.mem_stabilizer_iff (G := J)).2
        ((MulAction.mem_stabilizer_iff (G := fi24C)).1 c.2)
    have hcomm : ∀ c : ↥(MulAction.stabilizer fi24C CFSG.Sporadic.Fi24.root),
        CFSG.Sporadic.Fi24.fi23EquivM ⟨((c : fi24C) : J), hM c⟩ * fi23U3 =
          fi23U3 * CFSG.Sporadic.Fi24.fi23EquivM ⟨((c : fi24C) : J), hM c⟩ := fun c => by
      have h1 : (⟨((c : fi24C) : J), hM c⟩ : M) * ⟨fi24R2, fi24R2_mem_M⟩ =
          ⟨fi24R2, fi24R2_mem_M⟩ * ⟨((c : fi24C) : J), hM c⟩ := Subtype.ext (by
        rw [Subgroup.coe_mul, Subgroup.coe_mul]
        exact (Subgroup.mem_centralizer_singleton_iff (G := J)).1 (c : fi24C).2)
      have h2 := congrArg CFSG.Sporadic.Fi24.fi23EquivM h1
      rwa [MulEquiv.map_mul, MulEquiv.map_mul, fi23EquivM_fi24R2] at h2
    refine Nat.card_le_card_of_injective
      (fun c => ⟨CFSG.Sporadic.Fi24.fi23EquivM ⟨((c : fi24C) : J), hM c⟩,
        (Subgroup.mem_centralizer_singleton_iff (G := CFSG.Sporadic.Fi23.J)).2 (hcomm c)⟩) ?_
    intro a b hab
    simp only [Subtype.mk.injEq] at hab
    have h := CFSG.Sporadic.Fi24.fi23EquivM.injective hab
    simp only [Subtype.mk.injEq] at h
    exact Subtype.ext (Subtype.ext h)
  have hU : Nat.card ↥(Subgroup.centralizer ({fi23U3} : Set CFSG.Sporadic.Fi23.J)) ≤
      318504960 := by
    obtain ⟨c, hc⟩ := isConj_iff.1 isConj_fi23U2_fi23U3.2
    have e := (centralizerMulEquiv (MulAut.conj c) CFSG.Sporadic.Fi23.t2).trans
      (MulEquiv.subgroupCongr (by rw [MulAut.conj_apply, hc]))
    rw [← Nat.card_congr e.toEquiv]
    exact fi23_card_centralizer_t2
  rw [hF, hC] at h1
  omega

theorem fi23_exists_transposition_commute {y : CFSG.Sporadic.Fi23.J} (hy : y * y = 1) :
    ∃ d' ∈ CFSG.Sporadic.Fi23.D23, y * d' = d' * y := by
  have := Pair.finite CFSG.Sporadic.Fi23.pair_J
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  obtain ⟨x, hx⟩ := exists_fixed_of_odd (α := ↥CFSG.Sporadic.Fi23.D23)
    (by rw [show Nat.card ↥CFSG.Sporadic.Fi23.D23 = 31671 from CFSG.Sporadic.Fi23.card_class_d]
        decide)
    (Pair.conjPerm CFSG.Sporadic.Fi23.pair_J y) (fun x => by
      apply Subtype.ext
      rw [Pair.conjPerm_apply, Pair.conjPerm_apply, hyi]
      calc y * (y * (x : CFSG.Sporadic.Fi23.J) * y) * y = (y * y) * x * (y * y) := by group
        _ = x := by rw [hy, one_mul, mul_one])
  refine ⟨x, x.2, ?_⟩
  have h := congrArg Subtype.val hx
  rw [Pair.conjPerm_apply, hyi] at h
  calc y * (x : CFSG.Sporadic.Fi23.J) = y * x * y * y := by
        rw [mul_assoc (y * x), hy, mul_one]
    _ = x * y := by rw [h]

theorem fi23_u3_sylow {y : CFSG.Sporadic.Fi23.J} (hy : y * y = 1) :
    ∃ n : CFSG.Sporadic.Fi23.J, (n * fi23U3 * n⁻¹) * y = y * (n * fi23U3 * n⁻¹) := by
  have hr : ∃ k : ℕ, 2 ^ k ∣ Nat.card (Subgroup.centralizer ({fi23U3} : Set CFSG.Sporadic.Fi23.J))
      ∧ ¬ 2 ^ (k + 1) ∣ Nat.card CFSG.Sporadic.Fi23.J := by
    refine ⟨18, ?_, ?_⟩
    · rw [fi23_card_centralizer_u3]; norm_num
    · rw [CFSG.Sporadic.Fi23.card_J]; norm_num
  have := Pair.finite CFSG.Sporadic.Fi23.pair_J
  obtain ⟨x, hx⟩ := exists_conj_mem_centralizer_of_sylow fi23U3 hr (y := y) (by rw [sq]; exact hy)
  refine ⟨x⁻¹, ?_⟩
  have h := Subgroup.mem_centralizer_singleton_iff.1 hx
  calc x⁻¹ * fi23U3 * x⁻¹⁻¹ * y = x⁻¹ * (fi23U3 * (x * y * x⁻¹)) * x := by group
    _ = x⁻¹ * ((x * y * x⁻¹) * fi23U3) * x := by rw [h]
    _ = y * (x⁻¹ * fi23U3 * x⁻¹⁻¹) := by group

theorem fi24_isConj_cases (hPF : PolarFacts) {s : J} (hs : s * s = 1) (hs1 : s ≠ 1) :
    IsConj s CFSG.Sporadic.Fi24.tJ ∨ IsConj s fi24R2 :=
  (CFSG.Sporadic.Fi24.isConj_tJ_or_r2 hPF CFSG.Sporadic.Fi23.d1_mem_localClass
    CFSG.Sporadic.Fi23.involution_cover hs hs1).imp id (fun h => h.trans isConj_t2_fi24R2)

theorem fi24_umoves_core {u₁ : J} (hcls : IsConj u₁ CFSG.Sporadic.Fi24.tJ ∨ IsConj u₁ fi24R2)
    {y : CFSG.Sporadic.Fi23.J} (hy : y * y = 1) :
    ∃ x ∈ JR, (x * jR u₁ * x⁻¹) * fi23ToR y = fi23ToR y * (x * jR u₁ * x⁻¹) ∧
      (x * jR u₁ * x⁻¹) * tR = tR * (x * jR u₁ * x⁻¹) := by
  have key : ∀ (ρ : J) (ρF : CFSG.Sporadic.Fi23.J), jR ρ = fi23ToR ρF → IsConj u₁ ρ →
      (∃ n : CFSG.Sporadic.Fi23.J, (n * ρF * n⁻¹) * y = y * (n * ρF * n⁻¹)) →
      ∃ x ∈ JR, (x * jR u₁ * x⁻¹) * fi23ToR y = fi23ToR y * (x * jR u₁ * x⁻¹) ∧
        (x * jR u₁ * x⁻¹) * tR = tR * (x * jR u₁ * x⁻¹) := by
    intro ρ ρF hρ hconj ⟨n, hn⟩
    obtain ⟨c, hc⟩ := isConj_iff.1 hconj
    refine ⟨fi23ToR n * jR c, JR.mul_mem
      (CFSG.Sporadic.Fi24.MR_le_JR (fi23ToR_mem n)) (CFSG.Sporadic.Fi24.jR_mem_JR c), ?_⟩
    have e : fi23ToR n * jR c * jR u₁ * (fi23ToR n * jR c)⁻¹ = fi23ToR (n * ρF * n⁻¹) := by
      rw [map_mul, map_mul, map_inv, ← hρ, ← hc]
      simp only [map_mul, map_inv]
      group
    rw [e]
    refine ⟨?_, CFSG.Sporadic.Fi24.commute_tR_of_mem_MR (fi23ToR_mem _)⟩
    rw [← map_mul, ← map_mul, hn]
  rcases hcls with h | h
  · refine key CFSG.Sporadic.Fi24.tJ CFSG.Sporadic.Fi24.sb ?_ h ?_
    · rw [fi23ToR_apply, ← CFSG.Sporadic.Fi24.fi23EquivM_tJ, MulEquiv.symm_apply_apply]
    · obtain ⟨d', hd', hcomm⟩ := fi23_exists_transposition_commute hy
      obtain ⟨n, hn⟩ := isConj_iff.1 (Pair.isConj CFSG.Sporadic.Fi23.pair_J
        CFSG.Sporadic.Fi24.sb_mem_D23 hd')
      refine ⟨n, ?_⟩
      rw [hn]
      exact hcomm.symm
  · refine key fi24R2 fi23U3 ?_ h (fi23_u3_sylow hy)
    rw [fi23ToR_apply]
    rfl

theorem fi24_umoves (hPF : PolarFacts) {u : R} (hu : u ∈ JR) (hu2 : orderOf u = 2) {w : R}
    (hw : w * w = 1) : ∃ x ∈ JR, (x * u * x⁻¹) * w = w * (x * u * x⁻¹) := by
  by_cases hw1 : w = 1
  · exact ⟨1, JR.one_mem, by rw [hw1]; simp⟩
  obtain ⟨T', hT', hwT'⟩ := CFSG.Sporadic.Fi24.exists_commute_D24 hPF hw
  obtain ⟨g, hg⟩ := CFSG.Sporadic.Fi24.exists_conj_eq_tR hT'
  have hγ : jR g ∈ JR := CFSG.Sporadic.Fi24.jR_mem_JR g
  have hw₀ : (jR g * w * (jR g)⁻¹) * (jR g * w * (jR g)⁻¹) = 1 := by
    calc jR g * w * (jR g)⁻¹ * (jR g * w * (jR g)⁻¹) = jR g * (w * w) * (jR g)⁻¹ := by group
      _ = 1 := by rw [hw]; group
  have hw₀T : (jR g * w * (jR g)⁻¹) * tR = tR * (jR g * w * (jR g)⁻¹) := by
    rw [← hg]
    calc jR g * w * (jR g)⁻¹ * (jR g * T' * (jR g)⁻¹) = jR g * (w * T') * (jR g)⁻¹ := by group
      _ = jR g * (T' * w) * (jR g)⁻¹ := by rw [hwT']
      _ = jR g * T' * (jR g)⁻¹ * (jR g * w * (jR g)⁻¹) := by group
  have hu₀ : jR g * u * (jR g)⁻¹ ∈ JR := CFSG.Sporadic.Fi24.normal_JR.conj_mem u hu (jR g)
  obtain ⟨u₁, hu₁⟩ : ∃ u₁ : J, jR u₁ = jR g * u * (jR g)⁻¹ := by
    have : jR g * u * (jR g)⁻¹ ∈ jR.range := by rw [CFSG.Sporadic.Fi24.range_jR]; exact hu₀
    exact this
  have hu2' : u * u = 1 := by rw [← sq, ← hu2, pow_orderOf_eq_one]
  have hu₁2 : u₁ * u₁ = 1 := by
    apply CFSG.Sporadic.Fi24.jR_injective
    rw [map_mul, hu₁, map_one]
    calc jR g * u * (jR g)⁻¹ * (jR g * u * (jR g)⁻¹) = jR g * (u * u) * (jR g)⁻¹ := by group
      _ = 1 := by rw [hu2']; group
  have hu₁1 : u₁ ≠ 1 := by
    rintro rfl
    rw [map_one] at hu₁
    have : u = 1 := by
      calc u = (jR g)⁻¹ * (jR g * u * (jR g)⁻¹) * jR g := by group
        _ = 1 := by rw [← hu₁]; group
    rw [this, orderOf_one] at hu2
    exact absurd hu2 (by norm_num)
  have hcls := fi24_isConj_cases hPF hu₁2 hu₁1
  have fin : ∀ y : CFSG.Sporadic.Fi23.J, y * y = 1 → ∀ m' : R,
      jR g * w * (jR g)⁻¹ = m' →
      (∀ v : R, v * fi23ToR y = fi23ToR y * v → v * tR = tR * v → v * m' = m' * v) →
      ∃ x ∈ JR, (x * u * x⁻¹) * w = w * (x * u * x⁻¹) := by
    intro y hy m' hε hm'
    obtain ⟨x₀, hx₀, h1, h2⟩ := fi24_umoves_core hcls hy
    rw [hu₁] at h1 h2
    refine ⟨(jR g)⁻¹ * x₀ * jR g, JR.mul_mem (JR.mul_mem (JR.inv_mem hγ) hx₀) hγ, ?_⟩
    have hc : (x₀ * (jR g * u * (jR g)⁻¹) * x₀⁻¹) * (jR g * w * (jR g)⁻¹) =
        (jR g * w * (jR g)⁻¹) * (x₀ * (jR g * u * (jR g)⁻¹) * x₀⁻¹) := by
      rw [hε]
      exact hm' _ h1 h2
    calc (jR g)⁻¹ * x₀ * jR g * u * ((jR g)⁻¹ * x₀ * jR g)⁻¹ * w =
        (jR g)⁻¹ * ((x₀ * (jR g * u * (jR g)⁻¹) * x₀⁻¹) * (jR g * w * (jR g)⁻¹)) * jR g := by
          group
      _ = (jR g)⁻¹ * ((jR g * w * (jR g)⁻¹) * (x₀ * (jR g * u * (jR g)⁻¹) * x₀⁻¹)) * jR g := by
          rw [hc]
      _ = w * ((jR g)⁻¹ * x₀ * jR g * u * ((jR g)⁻¹ * x₀ * jR g)⁻¹) := by group
  have hc : jR g * w * (jR g)⁻¹ ∈ Subgroup.centralizer ({tR} : Set R) :=
    Subgroup.mem_centralizer_singleton_iff.2 hw₀T
  rcases CFSG.Sporadic.Fi24.mem_MR_or_of_commute hc with hm | hm
  · obtain ⟨y, hy⟩ := exists_fi23ToR hm
    have hy2 : y * y = 1 := fi23ToR_injective (by rw [map_mul, hy, hw₀, map_one])
    exact fin y hy2 (fi23ToR y) hy.symm fun v h1 _ => h1
  · obtain ⟨y, hy⟩ := exists_fi23ToR hm
    have hy2 : y * y = 1 := by
      apply fi23ToR_injective
      rw [map_mul, hy, map_one]
      calc jR g * w * (jR g)⁻¹ * tR * (jR g * w * (jR g)⁻¹ * tR) =
          jR g * w * (jR g)⁻¹ * (tR * (jR g * w * (jR g)⁻¹)) * tR := by group
        _ = jR g * w * (jR g)⁻¹ * (jR g * w * (jR g)⁻¹ * tR) * tR := by rw [hw₀T]
        _ = (jR g * w * (jR g)⁻¹ * (jR g * w * (jR g)⁻¹)) * (tR * tR) := by group
        _ = 1 := by rw [hw₀, CFSG.Sporadic.Fi24.tR_mul_tR, mul_one]
    refine fin y hy2 (fi23ToR y * tR) ?_ fun v h1 h2 => ?_
    · rw [hy]
      rw [mul_assoc _ tR tR, CFSG.Sporadic.Fi24.tR_mul_tR, mul_one]
    · calc v * (fi23ToR y * tR) = (v * fi23ToR y) * tR := by group
        _ = (fi23ToR y * v) * tR := by rw [h1]
        _ = fi23ToR y * (v * tR) := by group
        _ = fi23ToR y * (tR * v) := by rw [h2]
        _ = fi23ToR y * tR * v := by group

end CFSG.EvenSporadicStandard.Solomon78.Fi24Row
