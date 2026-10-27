module

public import CFSG.CGT.Hall82.TheoremASetting

public section

namespace CFSG.CGT.Hall82.TheoremA

open CFSG.RankThree.PartTwo (altHeart)
open CFSG.HardMathSupport.Cooperstein.Coordinator (altAct)

private theorem altHeart_add_self {n : ℕ} (a : altHeart n) : a + a = 0 := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective a
  rw [← QuotientAddGroup.mk_add]
  have : x + x = 0 := by
    apply Subtype.ext
    funext p
    have h2 : ∀ c : ZMod 2, c + c = 0 := by decide
    exact h2 _
  rw [this]; rfl

private theorem conj_eq_of_sq {H : Type*} [Group H] {z : H} (hzc : ∀ x : H, x * z = z * x)
    (hz : z * z = 1) {x y : H} (hx : x * x = z) (hy : y * y = z) (hxy : x * y * (x * y) = z) :
    x * y * x⁻¹ = z * y := by
  have hxi : x⁻¹ = x * z := inv_eq_of_mul_eq_one_right (by rw [← mul_assoc, hx, hz])
  have hyi : y⁻¹ = y * z := inv_eq_of_mul_eq_one_right (by rw [← mul_assoc, hy, hz])
  have h1 : x * y * x = y := by
    have h2 : x * y * x * y = z := (mul_assoc (x * y) x y).trans hxy
    calc x * y * x = z * y⁻¹ := eq_mul_inv_of_mul_eq h2
      _ = z * (y * z) := by rw [hyi]
      _ = z * y * z := (mul_assoc z y z).symm
      _ = y * z * z := by rw [← hzc y]
      _ = y := by rw [mul_assoc, hz, mul_one]
  calc x * y * x⁻¹ = x * y * (x * z) := by rw [hxi]
    _ = x * y * x * z := (mul_assoc (x * y) x z).symm
    _ = y * z := by rw [h1]
    _ = z * y := hzc y

private theorem class_mul {H : Type*} [Group H] {n : ℕ}
    {π : H →* Multiplicative (altHeart n)} (x y : H) :
    Multiplicative.toAdd (π (x * y)) = Multiplicative.toAdd (π x) + Multiplicative.toAdd (π y) := by
  rw [map_mul]; rfl

private theorem class_sq_zero {H : Type*} [Group H] {n : ℕ}
    {π : H →* Multiplicative (altHeart n)} (x : H) : Multiplicative.toAdd (π (x * x)) = 0 := by
  rw [class_mul]; exact altHeart_add_self _

variable {G : Type} [Group G] [Finite G] {M : Subgroup G}
  {θ : ↥M →* Equiv.Perm (Fin 6)} {z : G}
  {π : ↥(CFSG.Open.pCoreOf 2 M) →* Multiplicative (altHeart 6)}

namespace Setting

private def zv (S : Setting G M θ z π) : ↥(CFSG.Open.pCoreOf 2 M) := ⟨z, S.z_mem⟩

private theorem zv_mul_zv (S : Setting G M θ z π) : zv S * zv S = 1 :=
  Subtype.ext S.z_sq

private theorem zv_ne_one (S : Setting G M θ z π) : zv S ≠ 1 :=
  fun h => S.z_ne (congrArg Subtype.val h)

private theorem mul_zv_comm (S : Setting G M θ z π) (x : ↥(CFSG.Open.pCoreOf 2 M)) :
    x * zv S = zv S * x :=
  Subtype.ext (S.z_comm x (S.V_le x.2))

private theorem mul_zv_sq (S : Setting G M θ z π) (x : ↥(CFSG.Open.pCoreOf 2 M)) :
    x * zv S * (x * zv S) = x * x := by
  calc x * zv S * (x * zv S) = x * (zv S * x) * zv S := by simp only [mul_assoc]
    _ = x * (x * zv S) * zv S := by rw [← mul_zv_comm S x]
    _ = x * x * (zv S * zv S) := by simp only [mul_assoc]
    _ = x * x := by rw [zv_mul_zv, mul_one]

private theorem zv_mul_mul_zv (S : Setting G M θ z π) (b c : ↥(CFSG.Open.pCoreOf 2 M)) :
    zv S * b * (zv S * c) = b * c := by
  calc zv S * b * (zv S * c) = zv S * (b * zv S) * c := by simp only [mul_assoc]
    _ = zv S * (zv S * b) * c := by rw [mul_zv_comm S b]
    _ = zv S * zv S * b * c := by simp only [mul_assoc]
    _ = b * c := by rw [zv_mul_zv, one_mul]

private theorem mul_zv_three (S : Setting G M θ z π) (q a b : ↥(CFSG.Open.pCoreOf 2 M)) :
    q * zv S * (a * zv S) * (b * zv S) = q * a * b * zv S := by
  calc q * zv S * (a * zv S) * (b * zv S) = q * (zv S * a) * zv S * (b * zv S) := by
        simp only [mul_assoc]
    _ = q * (a * zv S) * zv S * (b * zv S) := by rw [← mul_zv_comm S a]
    _ = q * a * (zv S * zv S) * (b * zv S) := by simp only [mul_assoc]
    _ = q * a * b * zv S := by rw [zv_mul_zv, mul_one]; simp only [mul_assoc]

private theorem π_eq_one_iff' (S : Setting G M θ z π) (q : ↥(CFSG.Open.pCoreOf 2 M)) :
    π q = 1 ↔ q = 1 ∨ q = zv S := by
  rw [S.π_eq_one_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  · rintro (h | h)
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)

private theorem class_eq_zero_iff (S : Setting G M θ z π) (q : ↥(CFSG.Open.pCoreOf 2 M)) :
    Multiplicative.toAdd (π q) = 0 ↔ q = 1 ∨ q = zv S :=
  toAdd_eq_zero.trans (π_eq_one_iff' S q)

private theorem sq_mem (S : Setting G M θ z π) (q : ↥(CFSG.Open.pCoreOf 2 M)) :
    q * q = 1 ∨ q * q = zv S :=
  (class_eq_zero_iff S _).mp (class_sq_zero q)

private theorem eq_or_eq_mul_zv (S : Setting G M θ z π) {x y : ↥(CFSG.Open.pCoreOf 2 M)}
    (h : π x = π y) : y = x ∨ y = x * zv S := by
  have h1 : π (x⁻¹ * y) = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
  rcases (π_eq_one_iff' S _).mp h1 with h2 | h2
  · exact Or.inl (inv_mul_eq_one.mp h2).symm
  · exact Or.inr (inv_mul_eq_iff_eq_mul.mp h2)

private theorem exists_class (S : Setting G M θ z π) (u : altHeart 6) :
    ∃ x : ↥(CFSG.Open.pCoreOf 2 M), Multiplicative.toAdd (π x) = u := by
  obtain ⟨x, hx⟩ := S.surj_π (Multiplicative.ofAdd u)
  exact ⟨x, by simp [hx]⟩

private def cj (S : Setting G M θ z π) (m : ↥M) (q : ↥(CFSG.Open.pCoreOf 2 M)) :
    ↥(CFSG.Open.pCoreOf 2 M) :=
  ⟨m * q * m⁻¹, S.conj_mem m.2 q.2⟩

private theorem coe_cj (S : Setting G M θ z π) (m : ↥M) (q : ↥(CFSG.Open.pCoreOf 2 M)) :
    ((cj S m q : ↥(CFSG.Open.pCoreOf 2 M)) : G) = (m : G) * q * (m : G)⁻¹ := rfl

private theorem cj_mul_left (S : Setting G M θ z π) (m m' : ↥M) (q : ↥(CFSG.Open.pCoreOf 2 M)) :
    cj S (m * m') q = cj S m (cj S m' q) :=
  Subtype.ext (by simp [coe_cj, mul_assoc])

private theorem cj_mul (S : Setting G M θ z π) (m : ↥M) (q q' : ↥(CFSG.Open.pCoreOf 2 M)) :
    cj S m (q * q') = cj S m q * cj S m q' :=
  Subtype.ext (by simp [coe_cj, mul_assoc])

private theorem cj_one (S : Setting G M θ z π) (m : ↥M) : cj S m 1 = 1 :=
  Subtype.ext (by simp [coe_cj])

private theorem cj_zv (S : Setting G M θ z π) (m : ↥M) : cj S m (zv S) = zv S :=
  Subtype.ext (S.conj_z m.2)

private theorem cj_eq_of_one_or_zv (S : Setting G M θ z π) (m : ↥M)
    {g : ↥(CFSG.Open.pCoreOf 2 M)} (h : g = 1 ∨ g = zv S) : cj S m g = g := by
  rcases h with rfl | rfl
  · exact cj_one S m
  · exact cj_zv S m

private theorem class_cj (S : Setting G M θ z π) (m : ↥M) (q : ↥(CFSG.Open.pCoreOf 2 M)) :
    Multiplicative.toAdd (π (cj S m q)) = altAct (θ m) (Multiplicative.toAdd (π q)) :=
  S.π_conj m q

private theorem sq_eq_of_ne_zero (S : Setting G M θ z π) (F : Facts)
    {q q' : ↥(CFSG.Open.pCoreOf 2 M)} (hq : Multiplicative.toAdd (π q) ≠ 0)
    (hq' : Multiplicative.toAdd (π q') ≠ 0) : q' * q' = q * q := by
  obtain ⟨σ, hσ⟩ := F.trans _ _ hq hq'
  obtain ⟨m, rfl⟩ := S.surj_θ σ
  have h1 : π (cj S m q) = π q' :=
    Multiplicative.toAdd.injective ((class_cj S m q).trans hσ)
  have h2 : cj S m q * cj S m q = q * q := by
    rw [← cj_mul, cj_eq_of_one_or_zv S m (sq_mem S q)]
  rw [← h2]
  rcases eq_or_eq_mul_zv S h1.symm with h3 | h3
  · rw [h3]
  · rw [h3, mul_zv_sq S]

private theorem sq_eq_one (S : Setting G M θ z π) (F : Facts) (q : ↥(CFSG.Open.pCoreOf 2 M)) :
    q * q = 1 := by
  by_contra hne
  have hq : q * q = zv S := (sq_mem S q).resolve_left hne
  have hq0 : Multiplicative.toAdd (π q) ≠ 0 := by
    intro h0
    rcases (class_eq_zero_iff S q).mp h0 with rfl | rfl
    · exact hne (one_mul 1)
    · exact hne (zv_mul_zv S)
  have hall : ∀ x : ↥(CFSG.Open.pCoreOf 2 M), Multiplicative.toAdd (π x) ≠ 0 → x * x = zv S :=
    fun x hx => (sq_eq_of_ne_zero S F hq0 hx).trans hq
  obtain ⟨u, v, w, hu, hv, hw, huv, huw, hvw, huvw⟩ := F.indep
  obtain ⟨a, ha⟩ := exists_class S u
  obtain ⟨b, hb⟩ := exists_class S v
  obtain ⟨c, hc⟩ := exists_class S w
  have hzc : ∀ x : ↥(CFSG.Open.pCoreOf 2 M), x * zv S = zv S * x := mul_zv_comm S
  have hsa : a * a = zv S := hall a (by rw [ha]; exact hu)
  have hsb : b * b = zv S := hall b (by rw [hb]; exact hv)
  have hsc : c * c = zv S := hall c (by rw [hc]; exact hw)
  have hsbc : b * c * (b * c) = zv S := hall (b * c) (by rw [class_mul, hb, hc]; exact hvw)
  have e1 : a * b * a⁻¹ = zv S * b :=
    conj_eq_of_sq hzc (zv_mul_zv S) hsa hsb (hall (a * b) (by rw [class_mul, ha, hb]; exact huv))
  have e2 : a * c * a⁻¹ = zv S * c :=
    conj_eq_of_sq hzc (zv_mul_zv S) hsa hsc (hall (a * c) (by rw [class_mul, ha, hc]; exact huw))
  have e3 : a * (b * c) * a⁻¹ = zv S * (b * c) :=
    conj_eq_of_sq hzc (zv_mul_zv S) hsa hsbc
      (hall (a * (b * c)) (by rw [class_mul, class_mul, ha, hb, hc, ← add_assoc]; exact huvw))
  have e4 : a * (b * c) * a⁻¹ = b * c := by
    calc a * (b * c) * a⁻¹ = (a * b * a⁻¹) * (a * c * a⁻¹) := by group
      _ = zv S * b * (zv S * c) := by rw [e1, e2]
      _ = b * c := zv_mul_mul_zv S b c
  exact zv_ne_one S (mul_eq_right.mp (e3.symm.trans e4))

private theorem mul_comm_V (S : Setting G M θ z π) (F : Facts)
    (x y : ↥(CFSG.Open.pCoreOf 2 M)) : x * y = y * x := by
  have hx : x⁻¹ = x := inv_eq_of_mul_eq_one_right (sq_eq_one S F x)
  have hy : y⁻¹ = y := inv_eq_of_mul_eq_one_right (sq_eq_one S F y)
  calc x * y = (x * y)⁻¹ := (inv_eq_of_mul_eq_one_right (sq_eq_one S F (x * y))).symm
    _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
    _ = y * x := by rw [hx, hy]

theorem isElemAbelian (S : Setting G M θ z π) (F : Facts) :
    CFSG.Open.IsElemAbelian 2 (CFSG.Open.pCoreOf 2 M) := by
  unfold CFSG.Open.IsElemAbelian
  refine ⟨IsMulCommutative.of_comm (mul_comm_V S F), fun x hx => ?_⟩
  rw [pow_two]
  exact congrArg Subtype.val (sq_eq_one S F ⟨x, hx⟩)

private theorem cj_eq_of_θ_eq (S : Setting G M θ z π) (F : Facts) {m m' : ↥M}
    (h : θ m = θ m') (q : ↥(CFSG.Open.pCoreOf 2 M)) : cj S m q = cj S m' q := by
  have h1 : θ (m⁻¹ * m') = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
  have h2 : ((m⁻¹ * m' : ↥M) : G) ∈ CFSG.Open.pCoreOf 2 M := (S.θ_eq_one_iff _).mp h1
  have h3 : cj S (m⁻¹ * m') q = q := by
    have h4 := congrArg Subtype.val
      (mul_comm_V S F ⟨((m⁻¹ * m' : ↥M) : G), h2⟩ q)
    apply Subtype.ext
    rw [coe_cj]
    exact mul_inv_eq_iff_eq_mul.mpr h4
  calc cj S m q = cj S m (cj S (m⁻¹ * m') q) := by rw [h3]
    _ = cj S (m * (m⁻¹ * m')) q := (cj_mul_left S m _ q).symm
    _ = cj S m' q := by rw [mul_inv_cancel_left]

private theorem cj_eq_of_pres (S : Setting G M θ z π) (F : Facts) {i j k : Fin 6} (hij : i ≠ j)
    (hjk : j ≠ k) (hik : i ≠ k) {q : ↥(CFSG.Open.pCoreOf 2 M)}
    (hq : Multiplicative.toAdd (π q) = pc i j) {τ : ↥M} (hP : Pres (θ τ) i j)
    (hk : θ τ k = k) : cj S τ q = q := by
  have hτq : π (cj S τ q) = π q := by
    apply Multiplicative.toAdd.injective
    rw [class_cj, hq]
    exact (F.fixed_pc_iff _ i j hij).mpr hP
  rcases eq_or_eq_mul_zv S hτq.symm with h | h
  · exact h
  exfalso
  obtain ⟨c, hc⟩ := S.surj_θ (cyc i j k)
  have hcyc := F.cyc_conj i j k hij hjk hik (θ τ) hP hk
  have hw2 : Multiplicative.toAdd (π (cj S c q)) = altAct (cyc i j k) (pc i j) := by
    rw [class_cj, hc, hq]
  have hw3 : Multiplicative.toAdd (π (cj S c⁻¹ q)) = altAct (cyc i j k)⁻¹ (pc i j) := by
    rw [class_cj, map_inv, hc, hq]
  have hs0 : Multiplicative.toAdd (π (q * cj S c q * cj S c⁻¹ q)) = 0 := by
    rw [class_mul, class_mul, hq, hw2, hw3]
    exact F.cyc_sum i j k hij hjk hik
  have hs : cj S τ (q * cj S c q * cj S c⁻¹ q) = q * cj S c q * cj S c⁻¹ q :=
    cj_eq_of_one_or_zv S τ ((class_eq_zero_iff S _).mp hs0)
  have twist : ∀ n : ↥M, θ (n * τ) = θ (τ * c) →
      cj S τ (cj S c q) = cj S n (q * zv S) ∧ cj S τ (cj S c⁻¹ q) = cj S n⁻¹ (q * zv S) := by
    intro n hn
    refine ⟨?_, ?_⟩
    · calc cj S τ (cj S c q) = cj S (τ * c) q := (cj_mul_left S τ c q).symm
        _ = cj S (n * τ) q := cj_eq_of_θ_eq S F hn.symm q
        _ = cj S n (cj S τ q) := cj_mul_left S n τ q
        _ = cj S n (q * zv S) := by rw [h]
    · have h2 : θ (τ * c⁻¹) = θ (n⁻¹ * τ) := by
        simp only [map_mul, map_inv] at hn ⊢
        calc θ τ * (θ c)⁻¹ = (θ n)⁻¹ * (θ n * θ τ) * (θ c)⁻¹ := by group
          _ = (θ n)⁻¹ * (θ τ * θ c) * (θ c)⁻¹ := by rw [hn]
          _ = (θ n)⁻¹ * θ τ := by group
      calc cj S τ (cj S c⁻¹ q) = cj S (τ * c⁻¹) q := (cj_mul_left S τ c⁻¹ q).symm
        _ = cj S (n⁻¹ * τ) q := cj_eq_of_θ_eq S F h2 q
        _ = cj S n⁻¹ (cj S τ q) := cj_mul_left S n⁻¹ τ q
        _ = cj S n⁻¹ (q * zv S) := by rw [h]
  have hτs := hs
  rw [cj_mul, cj_mul, h] at hτs
  rcases hcyc with h1 | h1
  · have hn : θ (c * τ) = θ (τ * c) := by
      rw [map_mul, map_mul, hc]
      calc cyc i j k * θ τ = θ τ * cyc i j k * (θ τ)⁻¹ * θ τ := by rw [h1]
        _ = θ τ * cyc i j k := by group
    obtain ⟨t2, t3⟩ := twist c hn
    rw [t2, t3, cj_mul, cj_mul, cj_zv, cj_zv, mul_zv_three S] at hτs
    exact zv_ne_one S (mul_eq_left.mp hτs)
  · have hn : θ (c⁻¹ * τ) = θ (τ * c) := by
      rw [map_mul, map_mul, map_inv, hc]
      calc (cyc i j k)⁻¹ * θ τ = θ τ * cyc i j k * (θ τ)⁻¹ * θ τ := by rw [h1]
        _ = θ τ * cyc i j k := by group
    obtain ⟨t2, t3⟩ := twist c⁻¹ hn
    rw [t2, t3, inv_inv, cj_mul, cj_mul, cj_zv, cj_zv, mul_zv_three S] at hτs
    have hswap : q * cj S c⁻¹ q * cj S c q = q * cj S c q * cj S c⁻¹ q := by
      rw [mul_assoc, mul_comm_V S F (cj S c⁻¹ q) (cj S c q), ← mul_assoc]
    rw [hswap] at hτs
    exact zv_ne_one S (mul_eq_left.mp hτs)

private theorem cj_eq_self (S : Setting G M θ z π) (F : Facts) (m : ↥M)
    (q : ↥(CFSG.Open.pCoreOf 2 M))
    (h : altAct (θ m) (Multiplicative.toAdd (π q)) = Multiplicative.toAdd (π q)) :
    cj S m q = q := by
  by_cases h0 : Multiplicative.toAdd (π q) = 0
  · exact cj_eq_of_one_or_zv S m ((class_eq_zero_iff S q).mp h0)
  obtain ⟨i, j, hij, hqij⟩ := F.exists_pc _ h0
  have hP : Pres (θ m) i j := (F.fixed_pc_iff _ i j hij).mp (by rw [← hqij]; exact h)
  obtain ⟨σ₁, σ₂, hσ, hP₁, hP₂, ⟨k₁, hk₁i, hk₁j, hk₁⟩, ⟨k₂, hk₂i, hk₂j, hk₂⟩⟩ :=
    F.decomp i j hij _ hP
  obtain ⟨m₁, hm₁⟩ := S.surj_θ σ₁
  have hm₂ : θ (m₁⁻¹ * m) = σ₂ := by
    rw [map_mul, map_inv, hm₁, hσ, inv_mul_cancel_left]
  have e₁ : cj S m₁ q = q :=
    cj_eq_of_pres S F hij hk₁j.symm hk₁i.symm hqij (by rw [hm₁]; exact hP₁)
      (by rw [hm₁]; exact hk₁)
  have e₂ : cj S (m₁⁻¹ * m) q = q :=
    cj_eq_of_pres S F hij hk₂j.symm hk₂i.symm hqij (by rw [hm₂]; exact hP₂)
      (by rw [hm₂]; exact hk₂)
  calc cj S m q = cj S (m₁ * (m₁⁻¹ * m)) q := by rw [mul_inv_cancel_left]
    _ = cj S m₁ (cj S (m₁⁻¹ * m) q) := cj_mul_left S _ _ q
    _ = q := by rw [e₂, e₁]

theorem conj_eq_self (S : Setting G M θ z π) (F : Facts) (m : ↥M)
    (q : ↥(CFSG.Open.pCoreOf 2 M))
    (h : altAct (θ m) (Multiplicative.toAdd (π q)) = Multiplicative.toAdd (π q)) :
    (m : G) * q * (m : G)⁻¹ = q :=
  congrArg Subtype.val (cj_eq_self S F m q h)

end Setting

end CFSG.CGT.Hall82.TheoremA
