module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.HeisThirteen
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteenAInputs

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteen

@[expose] def lineCovered (a b : ℕ) : Bool :=
  censusLines.any fun e => (List.range 13).any fun μ =>
    μ != 0 && (μ * e.a) % 13 == a && (μ * e.b) % 13 == b

theorem lines_cover : (List.range 13).all (fun a => (List.range 13).all fun b =>
    (a == 0 && b == 0) || lineCovered a b) = true := by
  decide

theorem lines_shape : censusLines.all (fun e => (e.a == 1 || (e.a == 0 && e.b == 1)) &&
    e.lam % 13 != 0) = true := by
  decide

theorem exists_j_mod (u v : ℕ) (hu : u % 13 ≠ 0) : ∃ j : ℕ, (u * j + v) % 13 = 0 := by
  have h : (List.range 13).all (fun u => (List.range 13).all fun v =>
      u == 0 || (List.range 13).any fun j => (u * j + v) % 13 == 0) = true := by decide
  rw [List.all_eq_true] at h
  have h1 := h (u % 13) (List.mem_range.2 (Nat.mod_lt _ (by norm_num)))
  rw [List.all_eq_true] at h1
  have h2 := h1 (v % 13) (List.mem_range.2 (Nat.mod_lt _ (by norm_num)))
  simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true, List.mem_range] at h2
  rcases h2 with h2 | ⟨j, -, hj⟩
  · exact absurd h2 hu
  · refine ⟨j, ?_⟩
    have hm : u * j + v ≡ u % 13 * j + v % 13 [MOD 13] :=
      Nat.ModEq.add (Nat.ModEq.mul_right j (Nat.mod_modEq u 13).symm) (Nat.mod_modEq v 13).symm
    exact (show (u * j + v) % 13 = (u % 13 * j + v % 13) % 13 from hm).trans hj


section Census

variable {G : Type*} [Group G]

theorem card_sup_of_le_normalizer {H N : Subgroup G}
    (hle : H ≤ Subgroup.normalizer (N : Set G)) (hd : H ⊓ N = ⊥) :
    Nat.card (H ⊔ N : Subgroup G) = Nat.card H * Nat.card N := by
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right H N hle
  rw [← Nat.card_prod]
  symm
  refine Nat.card_congr (Equiv.ofBijective (fun p : H × N => (⟨(p.1 : G) * p.2, by
    rw [← SetLike.mem_coe, hset]; exact Set.mul_mem_mul p.1.2 p.2.2⟩ : ↥(H ⊔ N))) ⟨?_, ?_⟩)
  · rintro ⟨h, n⟩ ⟨h', n'⟩ heq
    have heq' : (h : G) * n = h' * n' := congrArg Subtype.val heq
    have hmem : (h' : G)⁻¹ * h ∈ H ⊓ N := by
      refine Subgroup.mem_inf.2 ⟨H.mul_mem (H.inv_mem h'.2) h.2, ?_⟩
      have : (h' : G)⁻¹ * h = n' * (n : G)⁻¹ := by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← heq', mul_inv_cancel_right]
      rw [this]
      exact N.mul_mem n'.2 (N.inv_mem n.2)
    rw [hd, Subgroup.mem_bot, inv_mul_eq_one] at hmem
    have hh : h = h' := Subtype.ext hmem.symm
    subst hh
    have hn : (n : G) = n' := mul_left_cancel heq'
    exact Prod.ext rfl (Subtype.ext hn)
  · rintro ⟨z, hz⟩
    rw [← SetLike.mem_coe, hset] at hz
    obtain ⟨h, hh, n, hn, rfl⟩ := hz
    exact ⟨(⟨h, hh⟩, ⟨n, hn⟩), rfl⟩

theorem mem_normalizer_of_conj_mem' [Finite G] {N : Subgroup G} {a : G}
    (h : ∀ n ∈ N, a * n * a⁻¹ ∈ N) : a ∈ Subgroup.normalizer (N : Set G) := by
  let φ : N → N := fun n => ⟨a * n * a⁻¹, h n n.2⟩
  have hφ : Function.Injective φ := by
    intro m n hmn
    have := congrArg Subtype.val hmn
    simp only [φ, mul_left_inj, mul_right_inj] at this
    exact Subtype.ext this
  have hsurj := Finite.injective_iff_surjective.1 hφ
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact h y
  · intro hy
    obtain ⟨n, hn⟩ := hsurj ⟨a * y * a⁻¹, hy⟩
    have := congrArg Subtype.val hn
    simp only [φ, mul_left_inj, mul_right_inj] at this
    rw [← this]
    exact n.2

theorem inf_eq_bot_of_not_mem [Finite G] {x : G} (hx : orderOf x = 13) {K : Subgroup G}
    (hxK : x ∉ K) : Subgroup.zpowers x ⊓ K = ⊥ := by
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have hdvd : Nat.card (Subgroup.zpowers x ⊓ K : Subgroup G) ∣ 13 := by
    rw [← hx, ← Nat.card_zpowers]
    exact Subgroup.card_dvd_of_le inf_le_left
  rcases (Nat.dvd_prime (by norm_num)).1 hdvd with h | h
  · exact Subgroup.eq_bot_of_card_eq _ h
  · exfalso
    have hle : (Subgroup.zpowers x ⊓ K : Subgroup G) = Subgroup.zpowers x := by
      refine Subgroup.eq_of_le_of_card_ge inf_le_left ?_
      rw [h, Nat.card_zpowers, hx]
    apply hxK
    have := Subgroup.mem_zpowers x
    rw [← hle] at this
    exact (Subgroup.mem_inf.1 this).2

variable [Finite G] {g d c x : G}

theorem census_generic (hG : (Nat.card G).factorization 13 = 3)
    (hg13 : g ^ 13 = 1) (hd13 : d ^ 13 = 1) (hc13 : c ^ 13 = 1) (hc1 : c ≠ 1)
    (hcg : c * g = g * c) (hcd : c * d = d * c) (hdg : d * g = g * (d * c ^ 4))
    (hlines : ∀ e ∈ censusLines, ∃ W : G,
      W * (g ^ e.a * d ^ e.b) * W⁻¹ = (if e.toC then c else x) ^ e.lam)
    {s : G} (hs : orderOf s = 13) :
    ∃ m : G, ∃ k : ℕ, k % 13 ≠ 0 ∧ (m * s * m⁻¹ = c ^ k ∨ m * s * m⁻¹ = x ^ k) := by
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have hcg' : Commute c g := hcg
  have hcd' : Commute c d := hcd
  have hco : orderOf c = 13 := orderOf_eq_prime hc13 hc1
  have hc4 : c ^ 4 ≠ 1 := by
    intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hco] at this
    norm_num at this
  have hdc : d ∉ Subgroup.zpowers c := by
    intro hd
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hd
    apply hc4
    have h1 : c ^ k * g = g * c ^ k := (hcg'.zpow_left k).eq
    rw [h1] at hdg
    have h2 := mul_left_cancel hdg
    exact (mul_left_cancel (a := c ^ k) (by rw [mul_one]; exact h2.symm)).symm.symm
  have hdo : orderOf d = 13 :=
    orderOf_eq_prime hd13 fun h => hdc (h ▸ Subgroup.one_mem _)
  have hdN : Subgroup.zpowers d ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
    rw [Subgroup.zpowers_le]
    refine mem_normalizer_of_conj_mem' fun n hn => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    rw [← (hcd'.zpow_left k).eq, mul_inv_cancel_right]
    exact Subgroup.zpow_mem_zpowers c k
  have hA := card_sup_of_le_normalizer hdN (inf_eq_bot_of_not_mem hdo hdc)
  rw [Nat.card_zpowers, Nat.card_zpowers, hdo, hco] at hA
  set A := Subgroup.zpowers d ⊔ Subgroup.zpowers c with hAdef
  have hAset := Subgroup.coe_mul_of_left_le_normalizer_right _ _ hdN
  have hAform : ∀ a ∈ A, ∃ i j : ℤ, a = d ^ i * c ^ j := by
    intro a ha
    rw [← SetLike.mem_coe, hAset] at ha
    obtain ⟨u, hu, v, hv, rfl⟩ := ha
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
    exact ⟨i, j, rfl⟩
  have hdA : d ∈ A := Subgroup.mem_sup_left (Subgroup.mem_zpowers d)
  have hcA : c ∈ A := Subgroup.mem_sup_right (Subgroup.mem_zpowers c)
  have hgA : g ∉ A := by
    intro hg
    obtain ⟨i, j, hij⟩ := hAform g hg
    apply hc4
    have h1 : g * d = d * g := by
      rw [hij]
      calc d ^ i * c ^ j * d = d ^ i * (c ^ j * d) := mul_assoc _ _ _
        _ = d ^ i * (d * c ^ j) := by rw [(hcd'.zpow_left j).eq]
        _ = d ^ i * d * c ^ j := (mul_assoc _ _ _).symm
        _ = d * d ^ i * c ^ j := by rw [(Commute.self_zpow d i).eq.symm]
        _ = d * (d ^ i * c ^ j) := mul_assoc _ _ _
    rw [← h1] at hdg
    have h2 := mul_left_cancel hdg
    have h3 : d * c ^ 4 = d * 1 := by rw [mul_one]; exact h2.symm
    exact mul_left_cancel h3
  have hgo : orderOf g = 13 :=
    orderOf_eq_prime hg13 fun h => hgA (h ▸ Subgroup.one_mem _)
  have hgd := gd_conj hcg hcd hdg hc13
  have hgN : Subgroup.zpowers g ≤ Subgroup.normalizer (A : Set G) := by
    rw [Subgroup.zpowers_le]
    refine mem_normalizer_of_conj_mem' fun a ha => ?_
    obtain ⟨i, j, rfl⟩ := hAform a ha
    have e1 : g * (d ^ i * c ^ j) * g⁻¹ = (g * d * g⁻¹) ^ i * (g * c * g⁻¹) ^ j := by
      rw [conj_zpow, conj_zpow]; group
    rw [e1, hgd, show g * c * g⁻¹ = c by rw [← hcg'.eq, mul_inv_cancel_right]]
    exact A.mul_mem (A.zpow_mem (A.mul_mem hdA (A.pow_mem hcA 9)) i) (A.zpow_mem hcA j)
  have hS := card_sup_of_le_normalizer hgN (inf_eq_bot_of_not_mem hgo hgA)
  rw [Nat.card_zpowers, hgo, hA] at hS
  set S := Subgroup.zpowers g ⊔ A with hSdef
  have hSset := Subgroup.coe_mul_of_left_le_normalizer_right _ _ hgN
  let P : Sylow 13 G := Sylow.ofCard S (by rw [hS, hG]; norm_num)
  have hsz : IsPGroup 13 (Subgroup.zpowers s) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hs, pow_one])
  obtain ⟨Q, hQ⟩ := hsz.exists_le_sylow
  obtain ⟨m₀, hm₀⟩ := MulAction.exists_smul_eq G P Q
  have hsQ : s ∈ (Q : Subgroup G) := hQ (Subgroup.mem_zpowers s)
  rw [← hm₀, Sylow.coe_subgroup_smul, Sylow.coe_ofCard] at hsQ
  obtain ⟨t, htS, hts⟩ := (Subgroup.mem_smul_pointwise_iff_exists s (MulAut.conj m₀) S).1 hsQ
  rw [MulAut.smul_def, MulAut.conj_apply] at hts
  suffices ht : ∃ m : G, ∃ k : ℕ, k % 13 ≠ 0 ∧ (m * t * m⁻¹ = c ^ k ∨ m * t * m⁻¹ = x ^ k) by
    obtain ⟨m, k, hk, h⟩ := ht
    refine ⟨m * m₀⁻¹, k, hk, ?_⟩
    have : m * m₀⁻¹ * s * (m * m₀⁻¹)⁻¹ = m * t * m⁻¹ := by rw [← hts]; group
    rw [this]
    exact h
  have hto : orderOf t = 13 := by
    rw [← hs, ← hts, show m₀ * t * m₀⁻¹ = (MulAut.conj m₀) t by simp [MulAut.conj_apply],
      MulEquiv.orderOf_eq]
  have hform : ∃ a b k : ℕ, a < 13 ∧ b < 13 ∧ t = g ^ a * d ^ b * c ^ k := by
    rw [← SetLike.mem_coe, hSset] at htS
    obtain ⟨u, hu, v, hv, rfl⟩ := htS
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    obtain ⟨j, k, rfl⟩ := hAform v hv
    refine ⟨(i % 13).toNat, (j % 13).toNat, (k % 13).toNat, ?_, ?_, ?_⟩
    · omega
    · omega
    · have hz : ∀ (y : G) (n : ℤ), orderOf y = 13 → y ^ n = y ^ (n % 13).toNat := by
        intro y n hy
        have h1 : y ^ n = y ^ (n % 13) := by rw [← zpow_mod_orderOf, hy]; simp
        rw [h1, ← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))]
      rw [hz g i hgo, hz d j hdo, hz c k hco, mul_assoc]
  obtain ⟨a, b, k, ha, hb, rfl⟩ := hform
  have hcov := lines_cover
  rw [List.all_eq_true] at hcov
  have h1 := hcov a (List.mem_range.2 ha)
  rw [List.all_eq_true] at h1
  have h2 := h1 b (List.mem_range.2 hb)
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h2
  rcases h2 with ⟨rfl, rfl⟩ | h2
  ·
    have htc : g ^ 0 * d ^ 0 * c ^ k = c ^ (k % 13) := by
      rw [pow_zero, pow_zero, one_mul, one_mul, ← pow_mod_orderOf, hco]
    refine ⟨1, k % 13, ?_, Or.inl (by rw [htc]; simp)⟩
    intro h0
    rw [Nat.mod_mod] at h0
    rw [htc, h0, pow_zero, orderOf_one] at hto
    norm_num at hto
  unfold lineCovered at h2
  rw [List.any_eq_true] at h2
  obtain ⟨e, he, hμ⟩ := h2
  rw [List.any_eq_true] at hμ
  obtain ⟨μ, hμ13, hμe⟩ := hμ
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hμe
  obtain ⟨⟨hμ0, hae⟩, hbe⟩ := hμe
  have hshape := lines_shape
  rw [List.all_eq_true] at hshape
  have hsh := hshape e he
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hsh
  obtain ⟨hab, hlam⟩ := hsh
  obtain ⟨W, hW⟩ := hlines e he
  obtain ⟨f, hf⟩ := heis_pow hcg hcd hdg hc13 e.a e.b μ
  have hga : g ^ a = g ^ (e.a * μ) := by
    rw [← hae, ← hgo, pow_mod_orderOf, Nat.mul_comm μ e.a]
  have hdb : d ^ b = d ^ (e.b * μ) := by
    rw [← hbe, ← hdo, pow_mod_orderOf, Nat.mul_comm μ e.b]
  set se := g ^ e.a * d ^ e.b with hse
  have hcse : Commute c se := (hcg'.pow_right _).mul_right (hcd'.pow_right _)
  have htse : g ^ a * d ^ b * c ^ k = se ^ μ * c ^ (f + k) := by
    rw [hga, hdb, hf, mul_assoc, ← pow_add]
  rw [htse]
  have hμ0' : μ % 13 ≠ 0 := by
    rw [Nat.mod_eq_of_lt (List.mem_range.1 hμ13)]; exact hμ0
  have hcentral : ∃ y : G, y * (se ^ μ * c ^ (f + k)) * y⁻¹ = se ^ μ := by
    rcases hab with hab1 | ⟨ha0, hb1⟩
    ·
      obtain ⟨j, hj⟩ := exists_j_mod (4 * μ) (f + k) (by omega)
      refine ⟨d ^ j, ?_⟩
      have hconj : d ^ j * se * (d ^ j)⁻¹ = se * c ^ (4 * j) := by
        rw [hse, hab1, pow_one]; exact dpow_conj hcg hcd hdg e.b j
      have hpow : d ^ j * se ^ μ * (d ^ j)⁻¹ = se ^ μ * c ^ (4 * j * μ) := by
        rw [← conj_pow, hconj, (hcse.symm.pow_right _).mul_pow, ← pow_mul]
      calc d ^ j * (se ^ μ * c ^ (f + k)) * (d ^ j)⁻¹ =
          d ^ j * se ^ μ * (d ^ j)⁻¹ * (d ^ j * c ^ (f + k) * (d ^ j)⁻¹) := by group
        _ = se ^ μ * c ^ (4 * j * μ) * c ^ (f + k) := by
            rw [hpow, ← (hcd'.pow_pow (f + k) j).eq, mul_inv_cancel_right]
        _ = se ^ μ := by
            rw [mul_assoc, ← pow_add, ← pow_mod_orderOf c, hco,
              show (4 * j * μ + (f + k)) % 13 = 0 by rw [mul_right_comm]; exact hj, pow_zero,
              mul_one]
    ·
      obtain ⟨j, hj⟩ := exists_j_mod (9 * μ) (f + k) (by omega)
      refine ⟨g ^ j, ?_⟩
      have hsed : se = d := by rw [hse, ha0, hb1, pow_zero, pow_one, one_mul]
      have hpow : g ^ j * se ^ μ * (g ^ j)⁻¹ = se ^ μ * c ^ (9 * j * μ) := by
        rw [← conj_pow, hsed, gpow_conj_d hcg hcd hdg hc13, (hcd'.symm.pow_right _).mul_pow,
          ← pow_mul]
      calc g ^ j * (se ^ μ * c ^ (f + k)) * (g ^ j)⁻¹ =
          g ^ j * se ^ μ * (g ^ j)⁻¹ * (g ^ j * c ^ (f + k) * (g ^ j)⁻¹) := by group
        _ = se ^ μ * c ^ (9 * j * μ) * c ^ (f + k) := by
            rw [hpow, ← (hcg'.pow_pow (f + k) j).eq, mul_inv_cancel_right]
        _ = se ^ μ := by
            rw [mul_assoc, ← pow_add, ← pow_mod_orderOf c, hco,
              show (9 * j * μ + (f + k)) % 13 = 0 by rw [mul_right_comm]; exact hj, pow_zero,
              mul_one]
  obtain ⟨y, hy⟩ := hcentral
  have hWμ : W * se ^ μ * W⁻¹ = ((if e.toC then c else x) ^ e.lam) ^ μ := by
    rw [← conj_pow, hW]
  have hk : (e.lam * μ) % 13 ≠ 0 := by
    intro h0
    have hdvd : 13 ∣ e.lam * μ := Nat.dvd_of_mod_eq_zero h0
    rcases (Nat.Prime.dvd_mul (by norm_num)).1 hdvd with h | h
    · exact hlam (Nat.mod_eq_zero_of_dvd h)
    · exact hμ0' (Nat.mod_eq_zero_of_dvd h)
  refine ⟨W * y, e.lam * μ, hk, ?_⟩
  have hfin : W * y * (se ^ μ * c ^ (f + k)) * (W * y)⁻¹ =
      ((if e.toC then c else x) ^ e.lam) ^ μ := by
    calc W * y * (se ^ μ * c ^ (f + k)) * (W * y)⁻¹ =
        W * (y * (se ^ μ * c ^ (f + k)) * y⁻¹) * W⁻¹ := by group
      _ = W * se ^ μ * W⁻¹ := by rw [hy]
      _ = ((if e.toC then c else x) ^ e.lam) ^ μ := hWμ
  rw [hfin, ← pow_mul]
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

end Census

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteen
