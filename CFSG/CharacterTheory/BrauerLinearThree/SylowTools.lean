module

public import CFSG.CharacterTheory.BrauerLinearThree.LocalTools
public import CFSG.LocalAnalysis.ZStar

public section

namespace CFSG.BrauerLinearThree

open scoped commutatorElement

variable {G : Type} [Group G]

theorem le_or_le_of_forall_mem_or {H A B : Subgroup G} (h : ∀ x ∈ H, x ∈ A ∨ x ∈ B) :
    H ≤ A ∨ H ≤ B := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hA, hB⟩ := hcon
  obtain ⟨a, haH, haA⟩ := IsConcreteLE.not_le_iff_exists.mp hA
  obtain ⟨b, hbH, hbB⟩ := IsConcreteLE.not_le_iff_exists.mp hB
  have haB : a ∈ B := (h a haH).resolve_left haA
  have hbA : b ∈ A := (h b hbH).resolve_right hbB
  rcases h (a * b) (H.mul_mem haH hbH) with hab | hab
  · exact haA (by simpa using A.mul_mem hab (A.inv_mem hbA))
  · exact hbB (by simpa using B.mul_mem (B.inv_mem haB) hab)

theorem exists_pow_ne_one_pow_eq_one {p : ℕ} {g : G} (hg : g ≠ 1) {k : ℕ}
    (hk : g ^ (p ^ k) = 1) : ∃ j, g ^ (p ^ j) ≠ 1 ∧ (g ^ (p ^ j)) ^ p = 1 := by
  classical
  have hex : ∃ k, g ^ (p ^ k) = 1 := ⟨k, hk⟩
  obtain ⟨k₀, hk₀, hmin⟩ : ∃ k₀, g ^ (p ^ k₀) = 1 ∧ ∀ j < k₀, g ^ (p ^ j) ≠ 1 :=
    ⟨Nat.find hex, Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩
  have hk₀pos : 0 < k₀ := by
    rcases Nat.eq_zero_or_pos k₀ with h | h
    · rw [h, pow_zero, pow_one] at hk₀
      exact absurd hk₀ hg
    · exact h
  refine ⟨k₀ - 1, hmin _ (Nat.sub_lt hk₀pos one_pos), ?_⟩
  rw [← pow_mul, ← pow_succ, show k₀ - 1 + 1 = k₀ by omega]
  exact hk₀

theorem card_sylow_modEq_one_of_ti [Finite G] {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (hTI : ∀ Q : Sylow p G, ∀ g ∈ (P : Subgroup G), g ∈ (Q : Subgroup G) → g ≠ 1 → Q = P) :
    Nat.card (Sylow p G) ≡ 1 [MOD Nat.card (P : Subgroup G)] := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let : Fintype (Sylow p G) := Fintype.ofFinite _
  have hfix : ∀ g : (P : Subgroup G), g ≠ 1 → MulAction.fixedBy (Sylow p G) g = {P} := by
    intro g hg
    ext Q
    simp only [MulAction.mem_fixedBy, Set.mem_singleton_iff]
    constructor
    · intro hQ
      have hgN : (g : G) ∈ Subgroup.normalizer (Q : Set G) :=
        Sylow.smul_eq_iff_mem_normalizer.mp hQ
      have hmem : (g : G) ∈ (P : Subgroup G) ⊓ Subgroup.normalizer (Q : Set G) := ⟨g.2, hgN⟩
      rw [IsPGroup.inf_normalizer_sylow P.isPGroup' Q] at hmem
      exact hTI Q g g.2 hmem.2 (fun h => hg (Subtype.ext h))
    · rintro rfl
      exact Sylow.smul_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer g.2)
  have hsum := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group
    (P : Subgroup G) (Sylow p G)
  simp only [Fintype.card_eq_nat_card] at hsum
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : (P : Subgroup G))),
    MulAction.fixedBy_one_eq_univ, Nat.card_univ] at hsum
  have h1 : ∀ g ∈ (Finset.univ.erase (1 : (P : Subgroup G))),
      Nat.card (MulAction.fixedBy (Sylow p G) g) = 1 := by
    intro g hg
    rw [hfix g (Finset.ne_of_mem_erase hg)]
    simp
  rw [Finset.sum_congr rfl h1, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, smul_eq_mul, mul_one, Fintype.card_eq_nat_card] at hsum
  set n := Nat.card (Sylow p G)
  set m := Nat.card (P : Subgroup G)
  set k := Nat.card (Quotient (MulAction.orbitRel (P : Subgroup G) (Sylow p G)))
  have hn : 1 ≤ n := Nat.card_pos
  have hm : 1 ≤ m := Nat.card_pos
  have hdvd : m ∣ n - 1 := ⟨k - 1, by rw [Nat.mul_sub_one, mul_comm m k]; omega⟩
  exact ((Nat.modEq_iff_dvd' hn).mpr hdvd).symm

theorem commutatorElement_mem_of_fixed_le {M N : Subgroup G} [Finite M] (hM : Odd (Nat.card M))
    {t : G} (ht : t * t = 1) (htM : ∀ x ∈ M, t * x * t⁻¹ ∈ M)
    (hNc : ∀ n ∈ N, ∀ x ∈ M, n * x = x * n) (htN : ∀ n ∈ N, t * n = n * t)
    (hfix : ∀ x ∈ M, t * x = x * t → x ∈ N) : ∀ a ∈ M, ∀ b ∈ M, ⁅a, b⁆ ∈ N := by
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  let N' : Subgroup M := N.subgroupOf M
  have hN' : N'.Normal := by
    constructor
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have h := hNc n hn g g.2
    have e : ((g * n * g⁻¹ : M) : G) = n := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← h, mul_inv_cancel_right]
    rw [e]
    exact hn
  let σ : M →* M :=
    { toFun := fun x => ⟨t * x * t⁻¹, htM x x.2⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun a b => by apply Subtype.ext; simp only [Subgroup.coe_mul]; group }
  have hσN : N' ≤ N'.comap σ := by
    intro n hn
    rw [Subgroup.mem_subgroupOf] at hn
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    change t * (n : G) * t⁻¹ ∈ N
    rw [htN _ hn, mul_inv_cancel_right]
    exact hn
  let σbar : M ⧸ N' →* M ⧸ N' := QuotientGroup.map N' N' σ hσN
  have hσσ : ∀ x : M, σ (σ x) = x := by
    intro x
    apply Subtype.ext
    change t * (t * (x : G) * t⁻¹) * t⁻¹ = x
    rw [ht']
    calc t * (t * (x : G) * t) * t = (t * t) * x * (t * t) := by group
      _ = x := by rw [ht]; group
  have hinv : Function.Involutive σbar := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      simp only [σbar, QuotientGroup.map_mk]
      rw [hσσ]
  have hfp : MonoidHom.FixedPointFree σbar := by
    intro q hq
    induction q using QuotientGroup.induction_on with
    | H x =>
      simp only [σbar, QuotientGroup.map_mk] at hq
      rw [QuotientGroup.eq] at hq
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      set n : M := (σ x)⁻¹ * x with hn_def
      have hnN : (n : G) ∈ N := by rw [Subgroup.mem_subgroupOf] at hq; exact hq
      have hx : (x : G) = t * x * t⁻¹ * n := by
        rw [hn_def]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        change (x : G) = t * x * t⁻¹ * ((t * x * t⁻¹)⁻¹ * x)
        group
      have hn2 : (n : G) * n = 1 := by
        have h1 : t * (x : G) * t⁻¹ = t * (t * x * t⁻¹ * n) * t⁻¹ := by rw [← hx]
        have h2 : t * (t * (x : G) * t⁻¹ * n) * t⁻¹ = x * n := by
          rw [ht']
          calc t * (t * (x : G) * t * n) * t = (t * t) * x * (t * (n * t)) := by group
            _ = (t * t) * x * (t * (t * n)) := by rw [← htN _ hnN]
            _ = x * n := by rw [← mul_assoc t t, ht]; group
        rw [h2] at h1
        have h3 : (x : G) = x * n * n := by
          calc (x : G) = t * x * t⁻¹ * n := hx
            _ = x * n * n := by rw [h1]
        have := congrArg (fun y => (x : G)⁻¹ * y) h3
        simp only [inv_mul_cancel, mul_assoc, inv_mul_cancel_left] at this
        exact this.symm
      have hn1 : (n : G) = 1 := by
        have hodd := odd_orderOf_of_mem (H := M) hM n.2
        exact eq_one_of_sq_eq_one_of_odd hodd (by rw [sq]; exact hn2)
      have hxt : t * (x : G) = x * t := by
        have : (x : G) = t * x * t⁻¹ := by
          have h' := hx
          rw [hn1, mul_one] at h'
          exact h'
        calc t * (x : G) = t * x * t⁻¹ * t := by group
          _ = x * t := by rw [← this]
      exact hfix x x.2 hxt
  have hcomm := hfp.commute_all_of_involutive hinv
  intro a ha b hb
  have h := hcomm (QuotientGroup.mk (⟨a, ha⟩ : M)) (QuotientGroup.mk (⟨b, hb⟩ : M))
  have h' : (QuotientGroup.mk (⁅(⟨a, ha⟩ : M), ⟨b, hb⟩⁆ : M) : M ⧸ N') = 1 := by
    rw [← QuotientGroup.mk'_apply, map_commutatorElement, commutatorElement_eq_one_iff_commute]
    exact h
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h'
  have e : ((⁅(⟨a, ha⟩ : M), ⟨b, hb⟩⁆ : M) : G) = ⁅a, b⁆ := by
    simp [commutatorElement_def]
  rw [e] at h'
  exact h'

theorem exists_card_dvd_of_isolated [Finite G] (E : Subgroup G) {t : G} (htE : t ∈ E)
    (ht1 : t ≠ 1) (ht2 : t * t = 1)
    (hiso : ∀ e ∈ E, (e * t * e⁻¹) * t = t * (e * t * e⁻¹) → e * t * e⁻¹ = t) :
    ∃ N : Subgroup G, N ≤ E ∧ (∀ e ∈ E, ∀ n ∈ N, e * n * e⁻¹ ∈ N) ∧ Odd (Nat.card N) ∧
      Nat.card E ∣ Nat.card N * Nat.card (E ⊓ Subgroup.centralizer {t} : Subgroup G) := by
  classical
  let : Fintype E := Fintype.ofFinite E
  let t' : E := ⟨t, htE⟩
  have ht1' : t' ≠ 1 := fun h => ht1 (congrArg Subtype.val h)
  have ht2' : t' * t' = 1 := Subtype.ext ht2
  obtain ⟨N, hNn, hNodd, hN⟩ := CFSG.ZStar.glauberman_zStar E t' ht1' ht2' (by
    intro g hg
    apply Subtype.ext
    have := hiso g g.2 (congrArg Subtype.val hg)
    simpa using this)
  have hfac : ∀ e : E, ∃ m ∈ N, t' * (m⁻¹ * e) = (m⁻¹ * e) * t' := by
    intro e
    set n : E := e * t' * e⁻¹ * t'⁻¹ with hn_def
    have hnN : n ∈ N := hN e
    have ht'inv : t'⁻¹ = t' := inv_eq_of_mul_eq_one_right ht2'
    have hconj : e * t' * e⁻¹ = n * t' := by
      rw [hn_def, ht'inv, mul_assoc _ t' t', ht2', mul_one]
    have hinv : t' * n * t' = n⁻¹ := by
      have hsq : (n * t') * (n * t') = 1 := by
        rw [← hconj]
        calc e * t' * e⁻¹ * (e * t' * e⁻¹) = e * (t' * t') * e⁻¹ := by group
          _ = 1 := by rw [ht2']; group
      calc t' * n * t' = n⁻¹ * ((n * t') * (n * t')) := by group
        _ = n⁻¹ := by rw [hsq, mul_one]
    have hodd : Odd (orderOf n) := odd_orderOf_of_mem (H := N) hNodd hnN
    obtain ⟨k, hk⟩ := exists_pow_eq_of_odd_orderOf hodd
    set m : E := n ^ k with hm_def
    have hmN : m ∈ N := N.pow_mem hnN k
    have hm2 : m * m = n := by
      rw [hm_def, ← pow_two, ← pow_mul, mul_comm, pow_mul, hk]
    have hinvm : t' * m * t' = m⁻¹ := by
      have h1 : t' * n ^ k * t'⁻¹ = (t' * n * t'⁻¹) ^ k := conj_pow.symm
      rw [ht'inv] at h1
      rw [hm_def, h1, hinv, inv_pow]
    refine ⟨m, hmN, ?_⟩
    have hmt : m * t' * m⁻¹ = n * t' := by
      have h1 : t' * m⁻¹ * t' = m := by
        rw [show t' * m⁻¹ * t' = (t' * m * t')⁻¹ by simp only [mul_inv_rev, ht'inv, mul_assoc],
          hinvm, inv_inv]
      calc m * t' * m⁻¹ = m * (t' * m⁻¹ * t') * t' := by
            rw [show m * (t' * m⁻¹ * t') * t' = m * t' * m⁻¹ * (t' * t') by group, ht2', mul_one]
        _ = m * m * t' := by rw [h1]
        _ = n * t' := by rw [hm2]
    calc t' * (m⁻¹ * e) = m⁻¹ * (m * t' * m⁻¹) * e := by group
      _ = m⁻¹ * (e * t' * e⁻¹) * e := by rw [hmt, hconj]
      _ = (m⁻¹ * e) * t' := by group
  let C : Subgroup E := Subgroup.centralizer {t'}
  let f : C →* E ⧸ N := (QuotientGroup.mk' N).comp C.subtype
  have hf : Function.Surjective f := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H e =>
      obtain ⟨m, hmN, hm⟩ := hfac e
      refine ⟨⟨m⁻¹ * e, ?_⟩, ?_⟩
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact hm.symm
      · simp only [f, MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply]
        rw [QuotientGroup.eq]
        have := hNn.conj_mem m hmN e⁻¹
        simpa [mul_assoc] using this
  have h1 : Nat.card (E ⧸ N) ∣ Nat.card C := Subgroup.card_dvd_of_surjective hf
  have h2 : Nat.card E = Nat.card (E ⧸ N) * Nat.card N :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup N
  refine ⟨N.map E.subtype, Subgroup.map_subtype_le N, ?_, ?_, ?_⟩
  · intro e he n hn
    obtain ⟨n', hn', rfl⟩ := Subgroup.mem_map.mp hn
    refine Subgroup.mem_map.mpr ⟨⟨e, he⟩ * n' * ⟨e, he⟩⁻¹, hNn.conj_mem n' hn' _, ?_⟩
    simp
  · rw [Subgroup.card_map_of_injective E.subtype_injective]
    exact hNodd
  · rw [Subgroup.card_map_of_injective E.subtype_injective]
    have hC : Nat.card C = Nat.card (E ⊓ Subgroup.centralizer {t} : Subgroup G) := by
      have hmap : C.map E.subtype = (E ⊓ Subgroup.centralizer {t} : Subgroup G) := by
        ext x
        simp only [Subgroup.mem_map, Subgroup.coe_subtype, Subgroup.mem_inf,
          Subgroup.mem_centralizer_singleton_iff]
        constructor
        · rintro ⟨y, hy, rfl⟩
          rw [Subgroup.mem_centralizer_singleton_iff] at hy
          exact ⟨y.2, congrArg Subtype.val hy⟩
        · rintro ⟨hxE, hx⟩
          refine ⟨⟨x, hxE⟩, ?_, rfl⟩
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact Subtype.ext hx
      rw [← hmap, Subgroup.card_map_of_injective E.subtype_injective]
    rw [h2, ← hC, mul_comm]
    exact mul_dvd_mul_left _ h1

theorem false_of_sylow_count {q n ν : ℕ} (hq : 2 ≤ q) (hn : n ≡ 1 [MOD q ^ 3]) (hn1 : n ≠ 1)
    (h : n * ν = (q ^ 3 - 1) * (q + 1)) : False := by
  have hq3 : 8 ≤ q ^ 3 := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
  have hpos : 0 < (q ^ 3 - 1) * (q + 1) := Nat.mul_pos (by omega) (by omega)
  have hn0 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · rw [h0, zero_mul] at h; omega
    · exact h0
  have hν0 : 1 ≤ ν := by
    rcases Nat.eq_zero_or_pos ν with h0 | h0
    · rw [h0, mul_zero] at h; omega
    · exact h0
  obtain ⟨a, ha⟩ := (Nat.modEq_iff_dvd' hn0).mp hn.symm
  have ha1 : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with h0 | h0
    · rw [h0, mul_zero] at ha; omega
    · exact h0
  have hna : (n : ℤ) = 1 + q ^ 3 * a := by
    have : n = 1 + q ^ 3 * a := by omega
    exact_mod_cast this
  have hz : (n : ℤ) * ν = ((q : ℤ) ^ 3 - 1) * (q + 1) := by
    have : (1 : ℕ) ≤ q ^ 3 := by omega
    exact_mod_cast (by rw [h]; push_cast [Nat.cast_sub this]; ring :
      ((n * ν : ℕ) : ℤ) = ((q : ℤ) ^ 3 - 1) * (q + 1))
  set c : ℤ := (q : ℤ) + 1 - a * ν with hc
  have hνc : (ν : ℤ) + q + 1 = (q : ℤ) ^ 3 * c := by
    rw [hc]
    have := hz
    rw [hna] at this
    linear_combination this
  have hq3z : (8 : ℤ) ≤ (q : ℤ) ^ 3 := by exact_mod_cast hq3
  have hc1 : 1 ≤ c := by
    by_contra hcon
    push Not at hcon
    have : c ≤ 0 := by omega
    have : (q : ℤ) ^ 3 * c ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) this
    have : (0 : ℤ) < ν + q + 1 := by positivity
    linarith
  have hqz : (2 : ℤ) ≤ q := by exact_mod_cast hq
  have hν : (q : ℤ) ^ 3 - q - 1 ≤ ν := by nlinarith
  have hn' : (q : ℤ) ^ 3 + 1 ≤ n := by rw [hna]; nlinarith
  have hq2 : (4 : ℤ) ≤ (q : ℤ) ^ 2 := by nlinarith
  have hq3' : 4 * (q : ℤ) ≤ (q : ℤ) ^ 3 := by
    have := mul_le_mul_of_nonneg_left hq2 (show (0 : ℤ) ≤ q by positivity)
    nlinarith
  have hνnn : (0 : ℤ) ≤ (q : ℤ) ^ 3 - q - 1 := by linarith
  have key : ((q : ℤ) ^ 3 + 1) * ((q : ℤ) ^ 3 - q - 1) ≤ n * ν :=
    mul_le_mul hn' hν hνnn (by positivity)
  rw [hz] at key
  have hlast : 0 < (q : ℤ) ^ 3 * ((q : ℤ) ^ 3 - 2 * q - 1) :=
    mul_pos (by positivity) (by linarith)
  nlinarith

end CFSG.BrauerLinearThree
