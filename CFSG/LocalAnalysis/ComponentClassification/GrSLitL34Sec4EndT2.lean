module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4EndT

public section

namespace CFSG.ComponentClassification.GrSLit.GrS4

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem eq_one_of_mul_mul_eq_one {B : Subgroup G} (hB : IsElemTwo B) {a b₂ b₃ x y z : G}
    (haB : a ∈ B) (hb₂B : b₂ ∈ B) (ha1 : a ≠ 1) (hb₂1 : b₂ ≠ 1) (hb₂a : b₂ ≠ a) (hb₃1 : b₃ ≠ 1)
    (hb₃a : b₃ ≠ a) (hb₃b : b₃ ≠ b₂) (hb₃ab : b₃ ≠ a * b₂) (hx : x = 1 ∨ x = a)
    (hy : y = 1 ∨ y = b₂) (hz : z = 1 ∨ z = b₃) (h : x * y * z = 1) : x = 1 ∧ y = 1 ∧ z = 1 := by
  have hinv : ∀ u ∈ B, u⁻¹ = u := fun u hu => inv_eq_of_mul_eq_one_right (hB.2 u hu)
  have hab : (a * b₂)⁻¹ = a * b₂ := hinv _ (mul_mem haB hb₂B)
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> rcases hz with hz | hz <;>
    rw [hx, hy, hz] at h ⊢
  · exact ⟨rfl, rfl, rfl⟩
  · exact (hb₃1 (by simpa using h)).elim
  · exact (hb₂1 (by simpa using h)).elim
  · exact (hb₃b ((eq_inv_of_mul_eq_one_right (show b₂ * b₃ = 1 by simpa using h)).trans
      (hinv _ hb₂B))).elim
  · exact (ha1 (by simpa using h)).elim
  · exact (hb₃a ((eq_inv_of_mul_eq_one_right (show a * b₃ = 1 by simpa using h)).trans
      (hinv _ haB))).elim
  · exact (hb₂a ((eq_inv_of_mul_eq_one_right (show a * b₂ = 1 by simpa using h)).trans
      (hinv _ haB))).elim
  · exact (hb₃ab ((eq_inv_of_mul_eq_one_right h).trans hab)).elim

omit [Finite G] in
theorem mul_six_regroup {X Y W X' Y' W' : G} (e1 : W * X' = X' * W) (e2 : Y * X' = X' * Y)
    (e3 : W * Y' = Y' * W) : X * Y * W * (X' * Y' * W') = X * X' * (Y * Y') * (W * W') := by
  calc X * Y * W * (X' * Y' * W') = X * Y * (W * X') * Y' * W' := by group
    _ = X * Y * (X' * W) * Y' * W' := by rw [e1]
    _ = X * (Y * X') * W * Y' * W' := by group
    _ = X * (X' * Y) * W * Y' * W' := by rw [e2]
    _ = X * X' * Y * (W * Y') * W' := by group
    _ = X * X' * Y * (Y' * W) * W' := by rw [e3]
    _ = X * X' * (Y * Y') * (W * W') := by group

omit [Finite G] in
theorem mul_three_comm {X Y W t : G} (h1 : X * t = t * X) (h2 : Y * t = t * Y)
    (h3 : W * t = t * W) : X * Y * W * t = t * (X * Y * W) := by
  calc X * Y * W * t = X * Y * (W * t) := by group
    _ = X * Y * (t * W) := by rw [h3]
    _ = X * (Y * t) * W := by group
    _ = X * (t * Y) * W := by rw [h2]
    _ = X * t * Y * W := by group
    _ = t * X * Y * W := by rw [h1]
    _ = t * (X * Y * W) := by group

theorem structure_of_le_withKernel
    (hTr : L34EightTransvectionFact) {a : G} {J S B T : Subgroup G} (hJper : ⁅J, J⁆ = J)
    (hL34 : IsL34Type (J ⧸ Open.fusionZStar J)) (hS : IsSylowTwoIn S (normalizer (J : Set G)))
    (hSyl : ∃ P : Sylow 2 G, (P : Subgroup G) = S) (haZ : a ∈ S ⊓ zStarIn J) (ha1 : a ≠ 1)
    (hZc : IsCyclic ↥(S ⊓ zStarIn J)) (hZ4 : Nat.card ↥(S ⊓ zStarIn J) = 4)
    (hQc : IsCyclic ↥(S ⊓ coreActionKernel J)) (hBP : B ≤ S ⊓ J) (hB8 : IsEightGroup B)
    (hBZ : B ⊓ zStarIn J = zpowers a) (hSN : S ≤ normalizer (B : Set G))
    (hAut : ∀ σ : ↥B ≃* ↥B, ∃ n ∈ normalizer (B : Set G), ∀ b : ↥B,
      n⁻¹ * (b : G) * n = (σ b : G))
    (hT : T = S ⊓ centralizer (B : Set G)) (hTW : T ≤ withKernel J) :
    Nonempty (↥T ≃* Multiplicative (Fin 3 → ZMod 4)) ∧ (∀ t ∈ T, t * t = 1 → t ∈ B) ∧
      (∀ x ∈ T, ∀ y ∈ T, x * y = y * x) ∧ ∀ t ∈ T, t * t * (t * t) = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS2 : IsPGroup 2 S := isPGroup_of_isSylowTwoIn hS
  set Q : Subgroup G := S ⊓ coreActionKernel J with hQdef
  have hP : IsSylowTwoIn (S ⊓ J) J := isSylowTwoIn_inf hS
  have hZJ : zStarIn J = J ⊓ coreActionKernel J := GSThmB.map_fusionZStar_eq J
  have hZJle : zStarIn J ≤ J := map_subtype_le _
  have hZP : S ⊓ J ⊓ zStarIn J = S ⊓ zStarIn J := by
    rw [inf_assoc, inf_eq_right.mpr hZJle]
  have haB : a ∈ B := (le_of_eq hBZ.symm).trans inf_le_left (mem_zpowers a)
  have haa : a * a = 1 := hB8.1.2 a haB
  have haQ : a ∈ Q := by
    have h := (mem_inf.mp haZ).2
    rw [hZJ] at h
    exact mem_inf.mpr ⟨(mem_inf.mp haZ).1, (mem_inf.mp h).2⟩
  have hSO : ∀ y ∈ S, y ∈ oddIn J → y = 1 := by
    intro y hyS hyO
    have hbot := eq_bot_of_le_two_group_of_le_odd hS2 (GrSLit.odd_card_map_pPrimeCore J)
      (inf_le_left : S ⊓ oddIn J ≤ S) inf_le_right
    have hy : y ∈ S ⊓ oddIn J := mem_inf.mpr ⟨hyS, hyO⟩
    rw [hbot] at hy
    exact hy
  have hPQ : ∀ p ∈ S ⊓ J, ∀ q ∈ Q, p * q = q * p := by
    intro p hp q hq
    have h1 := (mem_coreActionKernel.mp (mem_inf.mp hq).2).2 p (mem_inf.mp hp).2
    have h2 : p⁻¹ * q⁻¹ * p * q = 1 := hSO _ (mul_mem (mul_mem (mul_mem (inv_mem
      (mem_inf.mp hp).1) (inv_mem (mem_inf.mp hq).1)) (mem_inf.mp hp).1) (mem_inf.mp hq).1) h1
    calc p * q = q * (p * (p⁻¹ * q⁻¹ * p * q)) := by group
      _ = q * p := by rw [h2, mul_one]
  have hQab : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x := by
    intro x hx y hy
    have : IsCyclic ↥Q := hQc
    exact congrArg Subtype.val
      ((IsCyclic.isMulCommutative (α := ↥Q)).is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hQB : Q ≤ centralizer (B : Set G) := fun q hq =>
    mem_centralizer_iff.mpr fun b hb => hPQ b (hBP hb) q hq
  have hQT : Q ≤ T := fun q hq => by rw [hT]; exact mem_inf.mpr ⟨(mem_inf.mp hq).1, hQB hq⟩
  have hdec : ∀ t ∈ T, ∃ s ∈ S ⊓ J ⊓ centralizer (B : Set G), ∃ q ∈ Q, t = s * q := by
    intro t ht
    have htS : t ∈ S := by rw [hT] at ht; exact (mem_inf.mp ht).1
    have htC : t ∈ centralizer (B : Set G) := by rw [hT] at ht; exact (mem_inf.mp ht).2
    have hPQsyl := isSylowTwoIn_withKernel hS
    have hle : S ⊓ J ⊔ S ⊓ coreActionKernel J ≤ S ⊓ withKernel J :=
      sup_le (inf_le_inf_left _ le_sup_left) (inf_le_inf_left _ le_sup_right)
    have heq := hPQsyl.eq_of_le hle inf_le_right (hS2.to_le inf_le_left)
    have ht' : t ∈ ((S ⊓ J ⊔ Q : Subgroup G) : Set G) := by
      rw [← heq]
      exact mem_inf.mpr ⟨htS, hTW ht⟩
    rw [coe_mul_of_left_le_normalizer_right (S ⊓ J) Q (fun p hp =>
      mem_normalizer_of_forall_commute fun q hq => hPQ p hp q hq)] at ht'
    obtain ⟨s, hs, q, hq, rfl⟩ := ht'
    refine ⟨s, mem_inf.mpr ⟨hs, ?_⟩, q, hq, rfl⟩
    have h1 : s = s * q * q⁻¹ := by group
    rw [h1]
    exact mul_mem htC (inv_mem (hQB hq))
  have hQcen : ∀ q ∈ Q, ∀ t ∈ T, q * t = t * q := by
    intro q hq t ht
    obtain ⟨s, hs, q', hq', rfl⟩ := hdec t ht
    rw [← mul_assoc, ← hPQ s (mem_inf.mp hs).1 q hq, mul_assoc, hQab q hq q' hq', mul_assoc]
  have hTsyl : IsSylowTwoIn T (centralizer (B : Set G)) := by
    rw [hT]
    exact isSylowTwoIn_inf_centralizer hSyl hSN
  obtain ⟨b₂, hb₂B, hb₂1, hb₂a, -, -⟩ := exists_mem_not_mem_four hB8.2 1 a 1 1
  obtain ⟨b₃, hb₃B, hb₃1, hb₃a, hb₃b, hb₃ab⟩ := exists_mem_not_mem_four hB8.2 1 a b₂ (a * b₂)
  obtain ⟨g₂, hg₂N, hg₂⟩ := exists_mem_normalizer_conj_eq hB8.1 hTsyl hAut haB hb₂B ha1 hb₂1
  obtain ⟨g₃, hg₃N, hg₃⟩ := exists_mem_normalizer_conj_eq hB8.1 hTsyl hAut haB hb₃B ha1 hb₃1
  have hconjT : ∀ {g : G}, g ∈ normalizer (T : Set G) → ∀ q ∈ Q,
      g⁻¹ * q * g ∈ T ∧ ∀ t ∈ T, g⁻¹ * q * g * t = t * (g⁻¹ * q * g) := by
    intro g hg q hq
    have hgi := inv_mem hg
    refine ⟨by simpa using (mem_normalizer_iff.mp hgi q).mp (hQT hq), fun t ht => ?_⟩
    have hgt : g * t * g⁻¹ ∈ T := (mem_normalizer_iff.mp hg t).mp ht
    have h1 := hQcen q hq _ hgt
    calc g⁻¹ * q * g * t = g⁻¹ * (q * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * t * g⁻¹) * q) * g := by rw [h1]
      _ = t * (g⁻¹ * q * g) := by group
  let f : ↥Q × ↥Q × ↥Q → G := fun k =>
    (k.1 : G) * (g₂⁻¹ * (k.2.1 : G) * g₂) * (g₃⁻¹ * (k.2.2 : G) * g₃)
  have hfT : ∀ k, f k ∈ T := fun k => mul_mem (mul_mem (hQT k.1.2) (hconjT hg₂N _ k.2.1.2).1)
    (hconjT hg₃N _ k.2.2.2).1
  have hfcen : ∀ k, ∀ t ∈ T, f k * t = t * f k := by
    intro k t ht
    have h1 := hQcen _ k.1.2 t ht
    have h2 := (hconjT hg₂N _ k.2.1.2).2 t ht
    have h3 := (hconjT hg₃N _ k.2.2.2).2 t ht
    exact mul_three_comm h1 h2 h3
  have hfmul : ∀ k k', f (k * k') = f k * f k' := by
    intro k k'
    have e1 := (hQcen _ k'.1.2 _ (hconjT hg₃N _ k.2.2.2).1).symm
    have e2 := (hQcen _ k'.1.2 _ (hconjT hg₂N _ k.2.1.2).1).symm
    have e3 := ((hconjT hg₂N _ k'.2.1.2).2 _ (hconjT hg₃N _ k.2.2.2).1).symm
    rw [mul_six_regroup e1 e2 e3]
    simp only [f, Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul]
    group
  let μ : ↥Q × ↥Q × ↥Q →* ↥T :=
    { toFun := fun k => ⟨f k, hfT k⟩
      map_one' := Subtype.ext (by simp [f])
      map_mul' := fun k k' => Subtype.ext (hfmul k k') }
  have hμ : ∀ k, ((μ k : ↥T) : G) = f k := fun _ => rfl
  have hQinv : ∀ x : ↥Q, (x : G) * x = 1 → (x : G) = 1 ∨ (x : G) = a := by
    intro x hx
    by_cases hx1 : (x : G) = 1
    · exact Or.inl hx1
    · exact Or.inr (eq_of_mul_self_eq_one_of_isCyclic hQc x.2 haQ hx haa hx1 ha1)
  have hconj1 : ∀ {g c : G}, g⁻¹ * a * g = c → ∀ x : ↥Q, (x : G) * x = 1 →
      g⁻¹ * (x : G) * g = 1 ∨ g⁻¹ * (x : G) * g = c := by
    intro g c hgc x hx
    rcases hQinv x hx with h | h
    · left
      rw [h]
      group
    · right
      rw [h, hgc]
  have hQ2 : IsPGroup 2 Q := hS2.to_le inf_le_left
  obtain ⟨m, hm⟩ := hQ2.exists_card_eq
  have hμinj : Function.Injective μ := by
    rw [injective_iff_map_eq_one]
    intro k hk
    by_contra hk1
    have hpow : k ^ (2 ^ m) = 1 := by
      have hx : ∀ x : ↥Q, x ^ (2 ^ m) = 1 := fun x => by rw [← hm]; exact pow_card_eq_one'
      exact Prod.ext (hx _) (Prod.ext (hx _) (hx _))
    obtain ⟨j, hj, hkj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hpow)
    have hj0 : j ≠ 0 := by
      rintro rfl
      rw [pow_zero, orderOf_eq_one_iff] at hkj
      exact hk1 hkj
    set k' := k ^ (2 ^ (j - 1)) with hk'
    have hk'2 : k' * k' = 1 := by
      rw [hk', ← pow_add, ← two_mul, ← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero hj0),
        ← hkj, pow_orderOf_eq_one]
    have hk'1 : k' ≠ 1 := pow_ne_one_of_lt_orderOf (by positivity) (by
      rw [hkj]
      exact Nat.pow_lt_pow_right (by norm_num) (Nat.sub_lt (Nat.pos_of_ne_zero hj0) one_pos))
    have hμk' : μ k' = 1 := by rw [hk', map_pow, hk, one_pow]
    have hc1 : (k'.1 : G) * k'.1 = 1 := congrArg (fun u => ((u.1 : ↥Q) : G)) hk'2
    have hc2 : (k'.2.1 : G) * k'.2.1 = 1 := congrArg (fun u => ((u.2.1 : ↥Q) : G)) hk'2
    have hc3 : (k'.2.2 : G) * k'.2.2 = 1 := congrArg (fun u => ((u.2.2 : ↥Q) : G)) hk'2
    have h0 := eq_one_of_mul_mul_eq_one hB8.1 haB hb₂B ha1 hb₂1 hb₂a hb₃1 hb₃a hb₃b hb₃ab
      (hQinv _ hc1) (hconj1 hg₂ _ hc2) (hconj1 hg₃ _ hc3) (congrArg Subtype.val hμk')
    apply hk'1
    refine Prod.ext (Subtype.ext h0.1) (Prod.ext (Subtype.ext ?_) (Subtype.ext ?_))
    · have h2 := h0.2.1
      calc (k'.2.1 : G) = g₂ * (g₂⁻¹ * k'.2.1 * g₂) * g₂⁻¹ := by group
        _ = 1 := by rw [h2]; group
    · have h3 := h0.2.2
      calc (k'.2.2 : G) = g₃ * (g₃⁻¹ * k'.2.2 * g₃) * g₃⁻¹ := by group
        _ = 1 := by rw [h3]; group
  have hlow : Nat.card Q ^ 3 ≤ Nat.card T := by
    have h := Nat.card_le_card_of_injective μ hμinj
    rw [Nat.card_prod, Nat.card_prod] at h
    calc Nat.card Q ^ 3 = Nat.card Q * (Nat.card Q * Nat.card Q) := by ring
      _ ≤ Nat.card T := h
  set S₀ : Subgroup G := S ⊓ J ⊓ centralizer (B : Set G) with hS₀
  have hS₀64 : Nat.card S₀ ≤ 64 := card_inf_centralizer_le hTr hJper hL34 hP (by rwa [hZP])
    (by rwa [hZP]) hBP hB8 (by rw [hBZ]) ha1
  let ν : ↥S₀ × ↥Q →* ↥T :=
    { toFun := fun k => ⟨(k.1 : G) * k.2, by
        rw [hT]
        refine mem_inf.mpr ⟨mul_mem (mem_inf.mp (mem_inf.mp k.1.2).1).1 (mem_inf.mp k.2.2).1, ?_⟩
        exact mul_mem (mem_inf.mp k.1.2).2 (hQB k.2.2)⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun k k' => Subtype.ext (by
        simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul]
        have h := hPQ _ (mem_inf.mp k'.1.2).1 _ k.2.2
        calc (k.1 : G) * k'.1 * (k.2 * k'.2) = k.1 * ((k'.1 : G) * k.2) * k'.2 := by group
          _ = k.1 * ((k.2 : G) * k'.1) * k'.2 := by rw [h]
          _ = k.1 * k.2 * (k'.1 * k'.2) := by group) }
  have hνsurj : Function.Surjective ν := by
    rintro ⟨t, ht⟩
    obtain ⟨s, hs, q, hq, rfl⟩ := hdec t ht
    exact ⟨(⟨s, hs⟩, ⟨q, hq⟩), rfl⟩
  have hZS₀ : S ⊓ zStarIn J ≤ S₀ := by
    intro z hz
    refine mem_inf.mpr ⟨mem_inf.mpr ⟨(mem_inf.mp hz).1, hZJle (mem_inf.mp hz).2⟩, ?_⟩
    have hzQ : z ∈ Q := by
      have h := (mem_inf.mp hz).2
      rw [hZJ] at h
      exact mem_inf.mpr ⟨(mem_inf.mp hz).1, (mem_inf.mp h).2⟩
    exact hQB hzQ
  have hZQ : S ⊓ zStarIn J ≤ Q := fun z hz => by
    have h := (mem_inf.mp hz).2
    rw [hZJ] at h
    exact mem_inf.mpr ⟨(mem_inf.mp hz).1, (mem_inf.mp h).2⟩
  have hker : 4 ≤ Nat.card ν.ker := by
    rw [← hZ4]
    refine Nat.card_le_card_of_injective (fun z => ⟨(⟨z, hZS₀ z.2⟩, ⟨(z : G)⁻¹, inv_mem (hZQ z.2)⟩),
      MonoidHom.mem_ker.mpr (Subtype.ext (by simp [ν]))⟩) ?_
    intro z z' h
    exact Subtype.ext (congrArg (fun u : ↥ν.ker => (((u : ↥S₀ × ↥Q).1 : ↥S₀) : G)) h)
  have hup : 4 * Nat.card T ≤ 64 * Nat.card Q := by
    have h1 := Subgroup.card_ker_mul_card_range ν
    rw [MonoidHom.range_eq_top.mpr hνsurj, Subgroup.card_top, Nat.card_prod] at h1
    nlinarith [h1, hker, hS₀64]
  have hZ4' : 4 ≤ Nat.card Q := by
    rw [← hZ4]
    exact card_le_of_le hZQ
  have hcube : Nat.card Q ^ 3 ≤ 16 * Nat.card Q := by omega
  have hQ4 : Nat.card Q = 4 := by
    by_contra hne
    have h5 : 5 ≤ Nat.card Q := by omega
    have h25 : 25 * Nat.card Q ≤ Nat.card Q ^ 3 := by
      calc 25 * Nat.card Q = 5 * 5 * Nat.card Q := by ring
        _ ≤ Nat.card Q * Nat.card Q * Nat.card Q := by gcongr
        _ = Nat.card Q ^ 3 := by ring
    omega
  have hT64 : Nat.card T = 64 := by
    rw [hQ4] at hlow hup
    omega
  have hμbij : Function.Bijective μ := by
    rw [Nat.bijective_iff_injective_and_card]
    refine ⟨hμinj, ?_⟩
    rw [Nat.card_prod, Nat.card_prod, hQ4, hT64]
  let eμ : ↥Q × ↥Q × ↥Q ≃* ↥T := MulEquiv.ofBijective μ hμbij
  have hpre : ∀ t ∈ T, ∃ k, f k = t := fun t ht => by
    obtain ⟨k, hk⟩ := hμbij.2 ⟨t, ht⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · let eQ : Multiplicative (ZMod 4) ≃* ↥Q :=
      (ZMod.ringEquivCongr hQ4).toAddEquiv.toMultiplicative.symm.trans (zmodCyclicMulEquiv hQc)
    let e3 : Multiplicative (Fin 3 → ZMod 4) ≃*
        Multiplicative (ZMod 4) × Multiplicative (ZMod 4) × Multiplicative (ZMod 4) :=
      { toFun := fun v => (Multiplicative.ofAdd (Multiplicative.toAdd v 0),
          Multiplicative.ofAdd (Multiplicative.toAdd v 1),
          Multiplicative.ofAdd (Multiplicative.toAdd v 2))
        invFun := fun w => Multiplicative.ofAdd ![Multiplicative.toAdd w.1,
          Multiplicative.toAdd w.2.1, Multiplicative.toAdd w.2.2]
        left_inv := fun v => by
          funext i
          fin_cases i <;> rfl
        right_inv := fun w => rfl
        map_mul' := fun v w => rfl }
    exact ⟨(eμ.symm.trans (eQ.symm.prodCongr (eQ.symm.prodCongr eQ.symm))).trans e3.symm⟩
  · intro t ht htt
    obtain ⟨k, rfl⟩ := hpre t ht
    have hkk : k * k = 1 := by
      apply hμinj
      rw [map_mul, map_one]
      exact Subtype.ext (by rw [Subgroup.coe_mul, hμ, htt]; rfl)
    have hc1 : (k.1 : G) * k.1 = 1 := congrArg (fun u => ((u.1 : ↥Q) : G)) hkk
    have hc2 : (k.2.1 : G) * k.2.1 = 1 := congrArg (fun u => ((u.2.1 : ↥Q) : G)) hkk
    have hc3 : (k.2.2 : G) * k.2.2 = 1 := congrArg (fun u => ((u.2.2 : ↥Q) : G)) hkk
    have hmemB : ∀ {u c : G}, c ∈ B → (u = 1 ∨ u = c) → u ∈ B := by
      rintro u c hc (rfl | rfl)
      · exact one_mem B
      · exact hc
    exact mul_mem (mul_mem (hmemB haB (hQinv _ hc1)) (hmemB hb₂B (hconj1 hg₂ _ hc2)))
      (hmemB hb₃B (hconj1 hg₃ _ hc3))
  · intro x hx y hy
    obtain ⟨k, rfl⟩ := hpre x hx
    exact hfcen k y hy
  · intro t ht
    obtain ⟨k, rfl⟩ := hpre t ht
    have hk4 : k ^ 4 = 1 := by
      have hx : ∀ x : ↥Q, x ^ 4 = 1 := fun x => by rw [← hQ4]; exact pow_card_eq_one'
      exact Prod.ext (hx _) (Prod.ext (hx _) (hx _))
    have h : (μ k) ^ 4 = 1 := by rw [← map_pow, hk4, map_one]
    have h' := congrArg Subtype.val h
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one, hμ] at h'
    calc f k * f k * (f k * f k) = f k ^ 4 := by
          rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq, sq]
      _ = 1 := h'

end CFSG.ComponentClassification.GrSLit.GrS4
