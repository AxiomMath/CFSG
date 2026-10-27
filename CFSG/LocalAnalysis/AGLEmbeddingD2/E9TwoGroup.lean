module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Wielandt
public import CFSG.LocalAnalysis.SignalizerFunctor.Coprime

public section

namespace CFSG.AGLEmbeddingD2.E9TwoGroup

open CFSG.Wielandt CFSG.SignalizerFunctor.Helpers

section Elements

variable {A : Type*} [Group A]

theorem zpowers_eq_of_mem_of_mem {u v x : A} (hu : orderOf u = 3) (hv : orderOf v = 3)
    (hx : x ≠ 1) (hxu : x ∈ Subgroup.zpowers u) (hxv : x ∈ Subgroup.zpowers v) :
    Subgroup.zpowers u = Subgroup.zpowers v := by
  have key : ∀ {w : A}, orderOf w = 3 → x ∈ Subgroup.zpowers w →
      Subgroup.zpowers x = Subgroup.zpowers w := by
    intro w hw hxw
    have hle : Subgroup.zpowers x ≤ Subgroup.zpowers w := Subgroup.zpowers_le.mpr hxw
    have hfin : Finite (Subgroup.zpowers w) :=
      Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers, hw]; norm_num)
    have hdvd : Nat.card (Subgroup.zpowers x) ∣ 3 := by
      rw [← hw, ← Nat.card_zpowers w]
      exact Subgroup.card_dvd_of_le hle
    rw [Nat.card_zpowers] at hdvd
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact absurd (orderOf_eq_one_iff.mp h1) hx
    · exact Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, h3, hw])
  rw [← key hu hxu, key hv hxv]

end Elements

section Internal

variable {A J : Type} [Group A] [Finite A] [Group J] [Finite J] [MulDistribMulAction A J]

@[expose] noncomputable def fixCard (B : Subgroup A) : ℕ :=
  letI : MulDistribMulAction B J := MulDistribMulAction.compHom J B.subtype
  Nat.card (fixedPointSubgroup B J)

omit [Finite A] [Finite J] in
theorem fixCard_bot : fixCard (J := J) (⊥ : Subgroup A) = Nat.card J := by
  let : MulDistribMulAction (⊥ : Subgroup A) J :=
    MulDistribMulAction.compHom J (⊥ : Subgroup A).subtype
  have htop : fixedPointSubgroup (⊥ : Subgroup A) J = ⊤ := by
    rw [eq_top_iff]
    intro x _ g
    have hg : (g : A) = 1 := Subgroup.mem_bot.mp g.2
    change (g : A) • x = x
    rw [hg, one_smul]
  unfold fixCard
  rw [htop, Subgroup.card_top]

variable {a b : A}

omit [Finite A] in
theorem inf_zpowers_eq_bot (hb : orderOf b = 3) (hab : b ∉ Subgroup.zpowers a) :
    Subgroup.zpowers a ⊓ Subgroup.zpowers b = ⊥ := by
  have hfin : Finite (Subgroup.zpowers b) :=
    Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers, hb]; norm_num)
  have hdvd : Nat.card (Subgroup.zpowers a ⊓ Subgroup.zpowers b : Subgroup A) ∣ 3 := by
    rw [← hb, ← Nat.card_zpowers b]
    exact Subgroup.card_dvd_of_le inf_le_right
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
  · exact Subgroup.eq_bot_of_card_eq _ h1
  · exfalso
    have heq : Subgroup.zpowers a ⊓ Subgroup.zpowers b = Subgroup.zpowers b :=
      Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h3, Nat.card_zpowers, hb])
    exact hab (heq ▸ Subgroup.mem_zpowers b |>.1)

omit [Finite A] in
theorem pow_mul_pow_injective (ha : orderOf a = 3) (hb : orderOf b = 3)
    (hab : b ∉ Subgroup.zpowers a) :
    Function.Injective fun ij : Fin 3 × Fin 3 => a ^ (ij.1 : ℕ) * b ^ (ij.2 : ℕ) := by
  rintro ⟨i, j⟩ ⟨k, l⟩ h
  simp only at h
  have hmem : (a ^ (k : ℕ))⁻¹ * a ^ (i : ℕ) ∈
      Subgroup.zpowers a ⊓ Subgroup.zpowers b := by
    refine ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.npow_mem_zpowers a _))
      (Subgroup.npow_mem_zpowers a _), ?_⟩
    have : (a ^ (k : ℕ))⁻¹ * a ^ (i : ℕ) = b ^ (l : ℕ) * (b ^ (j : ℕ))⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h, mul_inv_cancel_right]
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.npow_mem_zpowers b _)
      (Subgroup.inv_mem _ (Subgroup.npow_mem_zpowers b _))
  rw [inf_zpowers_eq_bot hb hab, Subgroup.mem_bot, inv_mul_eq_one] at hmem
  have hj : b ^ (j : ℕ) = b ^ (l : ℕ) := by
    rw [hmem] at h
    exact mul_left_cancel h
  have hik : (k : ℕ) = i := pow_injOn_Iio_orderOf (by rw [ha]; exact k.2) (by rw [ha]; exact i.2)
    hmem
  have hjl : (j : ℕ) = l := pow_injOn_Iio_orderOf (by rw [hb]; exact j.2) (by rw [hb]; exact l.2)
    hj
  rw [Prod.mk.injEq]
  exact ⟨Fin.ext hik.symm, Fin.ext hjl⟩

theorem exists_pow_mul_pow (ha : orderOf a = 3) (hb : orderOf b = 3)
    (hab : b ∉ Subgroup.zpowers a) (hA : Nat.card A = 9) (g : A) :
    ∃ i j : Fin 3, g = a ^ (i : ℕ) * b ^ (j : ℕ) := by
  have hbij := (pow_mul_pow_injective ha hb hab).bijective_of_nat_card_le
    (by rw [hA, Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_fin])
  obtain ⟨⟨i, j⟩, hij⟩ := hbij.2 g
  exact ⟨i, j, hij.symm⟩

omit [Finite A] in
theorem orderOf_mul (ha : orderOf a = 3) (hb : orderOf b = 3) (hab : b ∉ Subgroup.zpowers a)
    (hc : Commute a b) : orderOf (a * b) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  apply orderOf_eq_prime
  · have ha3 : a ^ 3 = 1 := ha ▸ pow_orderOf_eq_one a
    have hb3 : b ^ 3 = 1 := hb ▸ pow_orderOf_eq_one b
    rw [hc.mul_pow, ha3, hb3, one_mul]
  · intro h
    apply hab
    rw [eq_inv_of_mul_eq_one_right h]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers a)

omit [Finite A] in
theorem orderOf_mul_inv (ha : orderOf a = 3) (hb : orderOf b = 3) (hab : b ∉ Subgroup.zpowers a)
    (hc : Commute a b) : orderOf (a * b⁻¹) = 3 := by
  have hb' : orderOf b⁻¹ = 3 := by rw [orderOf_inv, hb]
  have hab' : b⁻¹ ∉ Subgroup.zpowers a := fun h => hab (by simpa using Subgroup.inv_mem _ h)
  exact orderOf_mul ha hb' hab' hc.inv_right

omit [Finite A] in
theorem lines_ne (ha : orderOf a = 3) (hb : orderOf b = 3) (hab : b ∉ Subgroup.zpowers a)
    (hc : Commute a b) :
    Subgroup.zpowers a ≠ Subgroup.zpowers b ∧ Subgroup.zpowers a ≠ Subgroup.zpowers (a * b) ∧
      Subgroup.zpowers a ≠ Subgroup.zpowers (a * b⁻¹) ∧
      Subgroup.zpowers b ≠ Subgroup.zpowers (a * b) ∧
      Subgroup.zpowers b ≠ Subgroup.zpowers (a * b⁻¹) ∧
      Subgroup.zpowers (a * b) ≠ Subgroup.zpowers (a * b⁻¹) := by
  have ha1 : a ≠ 1 := fun h => by rw [h, orderOf_one] at ha; norm_num at ha
  have hnab : ∀ {u : A}, orderOf u = 3 → a ∈ Subgroup.zpowers u → u = b → False := by
    intro u hu hau hub
    subst hub
    exact hab (zpowers_eq_of_mem_of_mem ha hu ha1 (Subgroup.mem_zpowers a) hau ▸
      Subgroup.mem_zpowers u)
  have h12 : Subgroup.zpowers a ≠ Subgroup.zpowers b := fun h =>
    hab (h ▸ Subgroup.mem_zpowers b)
  have h13 : Subgroup.zpowers a ≠ Subgroup.zpowers (a * b) := fun h => by
    apply hab
    have hmem : a * b ∈ Subgroup.zpowers a := h ▸ Subgroup.mem_zpowers (a * b)
    simpa using Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers a)) hmem
  have h14 : Subgroup.zpowers a ≠ Subgroup.zpowers (a * b⁻¹) := fun h => by
    apply hab
    have hmem : a * b⁻¹ ∈ Subgroup.zpowers a := h ▸ Subgroup.mem_zpowers (a * b⁻¹)
    have : b⁻¹ ∈ Subgroup.zpowers a := by
      simpa using Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers a)) hmem
    simpa using Subgroup.inv_mem _ this
  have h23 : Subgroup.zpowers b ≠ Subgroup.zpowers (a * b) := fun h => by
    have hmem : a * b ∈ Subgroup.zpowers b := h ▸ Subgroup.mem_zpowers (a * b)
    have : a ∈ Subgroup.zpowers b := by
      simpa using Subgroup.mul_mem _ hmem (Subgroup.inv_mem _ (Subgroup.mem_zpowers b))
    exact hnab hb this rfl
  have h24 : Subgroup.zpowers b ≠ Subgroup.zpowers (a * b⁻¹) := fun h => by
    have hmem : a * b⁻¹ ∈ Subgroup.zpowers b := h ▸ Subgroup.mem_zpowers (a * b⁻¹)
    have : a ∈ Subgroup.zpowers b := by
      simpa using Subgroup.mul_mem _ hmem (Subgroup.mem_zpowers b)
    exact hnab hb this rfl
  have h34 : Subgroup.zpowers (a * b) ≠ Subgroup.zpowers (a * b⁻¹) := fun h => by
    have hmem : a * b⁻¹ ∈ Subgroup.zpowers (a * b) := h ▸ Subgroup.mem_zpowers (a * b⁻¹)
    have hb3 : b ^ 3 = 1 := hb ▸ pow_orderOf_eq_one b
    have hsq : b ^ 2 ∈ Subgroup.zpowers (a * b) := by
      have h1 := Subgroup.mul_mem _ (Subgroup.mem_zpowers (a * b)) (Subgroup.inv_mem _ hmem)
      have h2 : a * b * (a * b⁻¹)⁻¹ = b ^ 2 := by
        rw [mul_inv_rev, inv_inv, pow_two, show a * b * (b * a⁻¹) = a * (b * b) * a⁻¹ by group]
        exact (hc.mul_right hc).mul_inv_cancel
      rwa [h2] at h1
    have hbmem : b ∈ Subgroup.zpowers (a * b) := by
      have h4 := Subgroup.pow_mem _ hsq 2
      rwa [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_succ, hb3, one_mul] at h4
    have hamem : a ∈ Subgroup.zpowers (a * b) := by
      simpa using Subgroup.mul_mem _ (Subgroup.mem_zpowers (a * b)) (Subgroup.inv_mem _ hbmem)
    exact h13 (zpowers_eq_of_mem_of_mem ha (orderOf_mul ha hb hab hc) ha1
      (Subgroup.mem_zpowers a) hamem)
  exact ⟨h12, h13, h14, h23, h24, h34⟩

theorem mem_lines (ha : orderOf a = 3) (hb : orderOf b = 3) (hab : b ∉ Subgroup.zpowers a)
    (hc : Commute a b) (hA : Nat.card A = 9) {g : A} (hg : g ≠ 1) :
    g ∈ Subgroup.zpowers a ∨ g ∈ Subgroup.zpowers b ∨ g ∈ Subgroup.zpowers (a * b) ∨
      g ∈ Subgroup.zpowers (a * b⁻¹) := by
  obtain ⟨i, j, rfl⟩ := exists_pow_mul_pow ha hb hab hA g
  have hb3 : b ^ 3 = 1 := hb ▸ pow_orderOf_eq_one b
  have hb2 : b ^ 2 = b⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_succ, hb3])
  fin_cases i <;> fin_cases j
  · simp at hg
  · right; left
    show a ^ 0 * b ^ 1 ∈ _
    rw [pow_zero, one_mul, pow_one]
    exact Subgroup.mem_zpowers b
  · right; left
    show a ^ 0 * b ^ 2 ∈ _
    rw [pow_zero, one_mul]
    exact Subgroup.npow_mem_zpowers b 2
  · left
    show a ^ 1 * b ^ 0 ∈ _
    rw [pow_zero, mul_one, pow_one]
    exact Subgroup.mem_zpowers a
  · right; right; left
    show a ^ 1 * b ^ 1 ∈ _
    rw [pow_one, pow_one]
    exact Subgroup.mem_zpowers _
  · right; right; right
    show a ^ 1 * b ^ 2 ∈ _
    rw [pow_one, hb2]
    exact Subgroup.mem_zpowers _
  · left
    show a ^ 2 * b ^ 0 ∈ _
    rw [pow_zero, mul_one]
    exact Subgroup.npow_mem_zpowers a 2
  · right; right; right
    show a ^ 2 * b ^ 1 ∈ _
    have : a ^ 2 * b ^ 1 = (a * b⁻¹) ^ 2 := by
      rw [hc.inv_right.mul_pow, inv_pow, hb2, inv_inv, pow_one]
    rw [this]
    exact Subgroup.npow_mem_zpowers _ 2
  · right; right; left
    show a ^ 2 * b ^ 2 ∈ _
    rw [← hc.mul_pow]
    exact Subgroup.npow_mem_zpowers _ 2

theorem mem_lines_unique (ha : orderOf a = 3) (hb : orderOf b = 3)
    (hab : b ∉ Subgroup.zpowers a) (hc : Commute a b) (hA : Nat.card A = 9) {g : A}
    (hg : g ≠ 1) :
    (g ∈ Subgroup.zpowers a ∧ g ∉ Subgroup.zpowers b ∧ g ∉ Subgroup.zpowers (a * b) ∧
        g ∉ Subgroup.zpowers (a * b⁻¹)) ∨
      (g ∉ Subgroup.zpowers a ∧ g ∈ Subgroup.zpowers b ∧ g ∉ Subgroup.zpowers (a * b) ∧
        g ∉ Subgroup.zpowers (a * b⁻¹)) ∨
      (g ∉ Subgroup.zpowers a ∧ g ∉ Subgroup.zpowers b ∧ g ∈ Subgroup.zpowers (a * b) ∧
        g ∉ Subgroup.zpowers (a * b⁻¹)) ∨
      (g ∉ Subgroup.zpowers a ∧ g ∉ Subgroup.zpowers b ∧ g ∉ Subgroup.zpowers (a * b) ∧
        g ∈ Subgroup.zpowers (a * b⁻¹)) := by
  obtain ⟨h12, h13, h14, h23, h24, h34⟩ := lines_ne ha hb hab hc
  have hab3 := orderOf_mul ha hb hab hc
  have hai3 := orderOf_mul_inv ha hb hab hc
  have ex : ∀ {u v : A}, orderOf u = 3 → orderOf v = 3 → Subgroup.zpowers u ≠ Subgroup.zpowers v →
      g ∈ Subgroup.zpowers u → g ∉ Subgroup.zpowers v := fun hu hv huv hgu hgv =>
    huv (zpowers_eq_of_mem_of_mem hu hv hg hgu hgv)
  rcases mem_lines ha hb hab hc hA hg with h | h | h | h
  · exact Or.inl ⟨h, ex ha hb h12 h, ex ha hab3 h13 h, ex ha hai3 h14 h⟩
  · exact Or.inr (Or.inl ⟨ex hb ha (Ne.symm h12) h, h, ex hb hab3 h23 h, ex hb hai3 h24 h⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨ex hab3 ha (Ne.symm h13) h, ex hab3 hb (Ne.symm h23) h, h,
      ex hab3 hai3 h34 h⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ex hai3 ha (Ne.symm h14) h, ex hai3 hb (Ne.symm h24) h,
      ex hai3 hab3 (Ne.symm h34) h, h⟩))

theorem card_mul_fixCard_top_pow_three (hcop : Nat.Coprime (Nat.card J) (Nat.card A))
    (hsolv : Group.IsSolvable J) (ha : orderOf a = 3) (hb : orderOf b = 3)
    (hab : b ∉ Subgroup.zpowers a) (hc : Commute a b) (hA : Nat.card A = 9) :
    Nat.card J * fixCard (J := J) (⊤ : Subgroup A) ^ 3 =
      fixCard (J := J) (Subgroup.zpowers a) * fixCard (J := J) (Subgroup.zpowers b) *
        fixCard (J := J) (Subgroup.zpowers (a * b)) *
        fixCard (J := J) (Subgroup.zpowers (a * b⁻¹)) := by
  classical
  let B : Fin 6 → Subgroup A := ![⊥, ⊤, Subgroup.zpowers a, Subgroup.zpowers b,
    Subgroup.zpowers (a * b), Subgroup.zpowers (a * b⁻¹)]
  let m : Fin 6 → ℕ := ![3, 1, 0, 0, 0, 0]
  let n : Fin 6 → ℕ := ![0, 0, 1, 1, 1, 1]
  have hcoeff : ∀ g : A, (∑ i : Fin 6, if g ∈ B i then m i else 0) =
      ∑ i : Fin 6, if g ∈ B i then n i else 0 := by
    intro g
    by_cases hg : g = 1
    · subst hg
      simp [B, m, n, Fin.sum_univ_succ]
    · rcases mem_lines_unique ha hb hab hc hA hg with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ |
          ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ <;>
        simp [B, m, n, Fin.sum_univ_succ, hg, h1, h2, h3, h4]
  have hprod := fixedPointSubgroup_product_card_eq_of_coeff_sum_eq hcop hsolv B m n hcoeff
  change (∏ i : Fin 6, fixCard (J := J) (B i) ^ (m i * Nat.card (B i))) =
    ∏ i : Fin 6, fixCard (J := J) (B i) ^ (n i * Nat.card (B i)) at hprod
  have hcard3 : ∀ x : A, orderOf x = 3 → Nat.card (Subgroup.zpowers x) = 3 := fun x hx => by
    rw [Nat.card_zpowers, hx]
  simp only [B, m, n, Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Subgroup.card_bot, Subgroup.card_top, hA, hcard3 a ha, hcard3 b hb,
    hcard3 _ (orderOf_mul ha hb hab hc), hcard3 _ (orderOf_mul_inv ha hb hab hc), zero_mul,
    pow_zero, mul_one, one_mul, fixCard_bot] at hprod
  apply Nat.pow_left_injective (show 3 ≠ 0 by norm_num)
  simp only
  calc (Nat.card J * fixCard (J := J) (⊤ : Subgroup A) ^ 3) ^ 3
      = Nat.card J ^ 3 * fixCard (J := J) (⊤ : Subgroup A) ^ 9 := by ring
    _ = _ := hprod
    _ = _ := by ring

end Internal

section Ambient

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem fixCard_conj_eq (S A : Subgroup G) (hAS : A ≤ Subgroup.normalizer (S : Set G))
    (B : Subgroup A) :
    letI := conjugationAction A S hAS
    fixCard (J := S) B =
      Nat.card (S ⊓ Subgroup.centralizer ((B.map A.subtype : Subgroup G) : Set G) :
        Subgroup G) := by
  let := conjugationAction A S hAS
  let : MulDistribMulAction B S := MulDistribMulAction.compHom S B.subtype
  have heq : (fixedPointSubgroup B S).map S.subtype =
      S ⊓ Subgroup.centralizer ((B.map A.subtype : Subgroup G) : Set G) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.property, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro v hv
      obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hv
      have h := congrArg Subtype.val (hy (⟨w, hw⟩ : B))
      change ((w : A) : G) * (y : G) * ((w : A) : G)⁻¹ = y at h
      exact mul_inv_eq_iff_eq_mul.mp h
    · rintro ⟨hx, hc⟩
      refine ⟨⟨x, hx⟩, ?_, rfl⟩
      intro w
      apply Subtype.ext
      change (((w : B) : A) : G) * x * (((w : B) : A) : G)⁻¹ = x
      exact mul_inv_eq_iff_eq_mul.mpr (Subgroup.mem_centralizer_iff.mp hc _
        (Subgroup.mem_map_of_mem A.subtype w.property))
  unfold fixCard
  rw [← heq, Subgroup.card_map_of_injective S.subtype_injective]

theorem card_mul_card_inf_centralizer_pow_three (S A : Subgroup G)
    (hAS : A ≤ Subgroup.normalizer (S : Set G)) (hcop : Nat.Coprime (Nat.card S) 3)
    (hsolv : Group.IsSolvable S) (hA : Nat.card A = 9) {a b : G} (haA : a ∈ A) (hbA : b ∈ A)
    (ha : orderOf a = 3) (hb : orderOf b = 3) (hab : b ∉ Subgroup.zpowers a) :
    Nat.card S * Nat.card (S ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) ^ 3 =
      Nat.card (S ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) *
        Nat.card (S ⊓ Subgroup.centralizer ({b} : Set G) : Subgroup G) *
        Nat.card (S ⊓ Subgroup.centralizer ({a * b} : Set G) : Subgroup G) *
        Nat.card (S ⊓ Subgroup.centralizer ({a * b⁻¹} : Set G) : Subgroup G) := by
  let := conjugationAction A S hAS
  set a' : A := ⟨a, haA⟩
  set b' : A := ⟨b, hbA⟩
  have ha' : orderOf a' = 3 := by rw [← Subgroup.orderOf_coe]; exact ha
  have hb' : orderOf b' = 3 := by rw [← Subgroup.orderOf_coe]; exact hb
  have hab' : b' ∉ Subgroup.zpowers a' := fun h => by
    apply hab
    have := Subgroup.mem_map_of_mem A.subtype h
    rwa [MonoidHom.map_zpowers] at this
  have : IsMulCommutative A :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by rw [hA]; norm_num)
  have hc : Commute a' b' := this.is_comm.comm a' b'
  have hcop' : Nat.Coprime (Nat.card S) (Nat.card A) := by
    rw [hA, show (9 : ℕ) = 3 ^ 2 by norm_num]
    exact hcop.pow_right 2
  have h := card_mul_fixCard_top_pow_three hcop' hsolv ha' hb' hab' hc hA
  have hz : ∀ x : A, fixCard (J := S) (Subgroup.zpowers x) =
      Nat.card (S ⊓ Subgroup.centralizer ({(x : G)} : Set G) : Subgroup G) := by
    intro x
    rw [fixCard_conj_eq S A hAS, MonoidHom.map_zpowers, Subgroup.zpowers_eq_closure,
      Subgroup.centralizer_closure]
    rfl
  have htop : fixCard (J := S) (⊤ : Subgroup A) =
      Nat.card (S ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) := by
    rw [fixCard_conj_eq S A hAS, Subgroup.map_top, Subgroup.range_subtype]
  rw [htop, hz, hz, hz, hz] at h
  exact h

omit [Finite G] in
theorem card_inf_centralizer_conj (S : Subgroup G) {g : G}
    (hg : g ∈ Subgroup.normalizer (S : Set G)) (x : G) :
    Nat.card (S ⊓ Subgroup.centralizer ({g * x * g⁻¹} : Set G) : Subgroup G) =
      Nat.card (S ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) := by
  have hg' : g⁻¹ ∈ Subgroup.normalizer (S : Set G) := Subgroup.inv_mem _ hg
  refine Nat.card_congr
    { toFun := fun s => ⟨g⁻¹ * s * g, ⟨?_, ?_⟩⟩
      invFun := fun s => ⟨g * s * g⁻¹, ⟨?_, ?_⟩⟩
      left_inv := fun s => Subtype.ext (by simp [mul_assoc])
      right_inv := fun s => Subtype.ext (by simp [mul_assoc]) }
  · have := (Subgroup.mem_normalizer_iff.mp hg' s).mp (Subgroup.mem_inf.mp s.2).1
    simpa using this
  · show g⁻¹ * s * g ∈ Subgroup.centralizer ({x} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h : s * (g * x * g⁻¹) = g * x * g⁻¹ * s :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp s.2).2
    calc g⁻¹ * s * g * x = g⁻¹ * (s * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * x * g⁻¹ * s) * g := by rw [h]
      _ = x * (g⁻¹ * s * g) := by group
  · exact (Subgroup.mem_normalizer_iff.mp hg s).mp (Subgroup.mem_inf.mp s.2).1
  · show g * s * g⁻¹ ∈ Subgroup.centralizer ({g * x * g⁻¹} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h : s * x = x * s := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp s.2).2
    calc g * s * g⁻¹ * (g * x * g⁻¹) = g * (s * x) * g⁻¹ := by group
      _ = g * (x * s) * g⁻¹ := by rw [h]
      _ = g * x * g⁻¹ * (g * s * g⁻¹) := by group

theorem eight_add_le_of_pow (s u w : ℕ) (h : s + 3 * u = 4 * w) (huw : u < w)
    (h3 : 2 ^ w ≡ 2 ^ u [MOD 3]) : 8 + u ≤ s := by
  obtain ⟨k, rfl⟩ : ∃ k, w = u + k := ⟨w - u, by omega⟩
  have hk1 : k ≠ 1 := by
    rintro rfl
    have hr : 2 ^ u % 3 ≠ 0 := by
      intro h0
      have h3u : 3 ∣ 2 ^ u := Nat.dvd_of_mod_eq_zero h0
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3u
      omega
    have h' : 2 ^ u * 2 % 3 = 2 ^ u % 3 := by rw [← pow_succ]; exact h3
    rw [Nat.mul_mod] at h'
    have : 2 ^ u % 3 < 3 := Nat.mod_lt _ (by norm_num)
    omega
  omega

theorem two_pow_eight_mul_card_le (S A : Subgroup G) (hS : IsPGroup 2 S)
    (hAS : A ≤ Subgroup.normalizer (S : Set G)) (hA : Nat.card A = 9)
    (htrans : ∀ x ∈ A, x ≠ 1 → ∀ y ∈ A, y ≠ 1 →
      ∃ g ∈ Subgroup.normalizer (S : Set G), g * x * g⁻¹ = y)
    (hne : ¬ S ≤ Subgroup.centralizer (A : Set G)) :
    2 ^ 8 * Nat.card (S ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) ≤ Nat.card S := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := A) 3 (by rw [hA]; norm_num)
  set a : G := (y : G) with ha_def
  have hy3 : orderOf a = 3 := by rw [ha_def, Subgroup.orderOf_coe]; exact hy
  have hy1 : a ≠ 1 := fun h => by rw [h, orderOf_one] at hy3; norm_num at hy3
  have haA : a ∈ A := y.2
  have hord : ∀ x ∈ A, x ≠ 1 → orderOf x = 3 := by
    intro x hx hx1
    obtain ⟨g, -, hg⟩ := htrans x hx hx1 a haA hy1
    have h := MulEquiv.orderOf_eq (MulAut.conj g) x
    rw [MulAut.conj_apply, hg] at h
    rw [← h, hy3]
  obtain ⟨b, hbA, hab⟩ : ∃ b ∈ A, b ∉ Subgroup.zpowers a := by
    by_contra h
    push Not at h
    have := Subgroup.card_le_of_le (show A ≤ Subgroup.zpowers a from h)
    rw [hA, Nat.card_zpowers, hy3] at this
    norm_num at this
  have hb1 : b ≠ 1 := fun h => hab (h ▸ Subgroup.one_mem _)
  have hb3 := hord b hbA hb1
  have hAc : IsMulCommutative A :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by rw [hA]; norm_num)
  have hab' : Commute a b :=
    congrArg Subtype.val (hAc.is_comm.comm (⟨a, haA⟩ : A) ⟨b, hbA⟩)
  have hcop : Nat.Coprime (Nat.card S) 3 := by
    obtain ⟨n, hn⟩ := hS.exists_card_eq
    rw [hn]
    exact Nat.Coprime.pow_left n (by norm_num)
  have hsolv : Group.IsSolvable S := by
    have := hS.isNilpotent
    infer_instance
  have hid := card_mul_card_inf_centralizer_pow_three S A hAS hcop hsolv hA haA hbA hy3 hb3 hab
  have hsame : ∀ x ∈ A, x ≠ 1 → Nat.card (S ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) =
      Nat.card (S ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) := by
    intro x hx hx1
    obtain ⟨g, hg, rfl⟩ := htrans a haA hy1 x hx hx1
    exact card_inf_centralizer_conj S hg a
  have hab1 : a * b ≠ 1 := fun h => hab (by
    rw [eq_inv_of_mul_eq_one_right h]; exact Subgroup.inv_mem _ (Subgroup.mem_zpowers a))
  have habi1 : a * b⁻¹ ≠ 1 := fun h => hab (by
    rw [inv_injective (eq_inv_of_mul_eq_one_right h)]
    exact Subgroup.mem_zpowers a)
  rw [hsame b hbA hb1, hsame _ (A.mul_mem haA hbA) hab1,
    hsame _ (A.mul_mem haA (A.inv_mem hbA)) habi1] at hid
  have hCA : S ⊓ Subgroup.centralizer (A : Set G) = (S ⊓ Subgroup.centralizer ({a} : Set G)) ⊓
      Subgroup.centralizer ((Subgroup.zpowers b : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    apply le_antisymm
    · intro x hx
      obtain ⟨hxS, hxC⟩ := Subgroup.mem_inf.mp hx
      refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hxS, ?_⟩, ?_⟩
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_iff.mp hxC a haA).symm
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_iff.mp hxC b hbA).symm
    · intro x hx
      obtain ⟨hx1, hxb⟩ := Subgroup.mem_inf.mp hx
      obtain ⟨hxS, hxa⟩ := Subgroup.mem_inf.mp hx1
      refine Subgroup.mem_inf.mpr ⟨hxS, Subgroup.mem_centralizer_iff.mpr fun g hg => ?_⟩
      have hxa' : Commute a x := (Subgroup.mem_centralizer_singleton_iff.mp hxa).symm
      have hxb' : Commute b x := (Subgroup.mem_centralizer_singleton_iff.mp hxb).symm
      have hb' : orderOf (⟨b, hbA⟩ : A) = 3 := by rw [← Subgroup.orderOf_coe]; exact hb3
      have hab'' : (⟨b, hbA⟩ : A) ∉ Subgroup.zpowers (⟨a, haA⟩ : A) := fun h => by
        apply hab
        have := Subgroup.mem_map_of_mem A.subtype h
        rwa [MonoidHom.map_zpowers] at this
      have hy' : orderOf (⟨a, haA⟩ : A) = 3 := by rw [← Subgroup.orderOf_coe]; exact hy3
      obtain ⟨i, j, hij⟩ := exists_pow_mul_pow hy' hb' hab'' hA ⟨g, hg⟩
      have hgij : g = a ^ (i : ℕ) * b ^ (j : ℕ) := congrArg Subtype.val hij
      rw [hgij]
      exact ((hxa'.pow_left _).mul_left (hxb'.pow_left _)).eq
  have hmod : Nat.card (S ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) ≡
      Nat.card (S ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) [MOD 3] := by
    have hnorm : Subgroup.zpowers b ≤ Subgroup.normalizer
        ((S ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) : Set G) := by
      rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        obtain ⟨hxS, hxa⟩ := Subgroup.mem_inf.mp hx
        refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp (hAS hbA) x).mp hxS, ?_⟩
        rw [Subgroup.mem_centralizer_singleton_iff] at hxa ⊢
        exact ((hab'.mul_right (show Commute x a from hxa).symm).mul_right hab'.inv_right).eq.symm
      · intro hx
        obtain ⟨hxS, hxa⟩ := Subgroup.mem_inf.mp hx
        refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp (hAS hbA) x).mpr hxS, ?_⟩
        rw [Subgroup.mem_centralizer_singleton_iff] at hxa ⊢
        have hx' : x = b⁻¹ * (b * x * b⁻¹) * b := by group
        rw [hx']
        exact ((hab'.inv_right.mul_right (show Commute (b * x * b⁻¹) a from hxa).symm).mul_right
          hab').eq.symm
    have hbp : IsPGroup 3 (Subgroup.zpowers b) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hb3, pow_one])
    have := centralizer_card_modEq 3 Nat.prime_three (Subgroup.zpowers b)
      (S ⊓ Subgroup.centralizer ({a} : Set G)) hbp hnorm
    rwa [← hCA] at this
  obtain ⟨s, hs⟩ := hS.exists_card_eq
  obtain ⟨w, hw⟩ := (hS.to_le
    (inf_le_left : S ⊓ Subgroup.centralizer ({a} : Set G) ≤ S)).exists_card_eq
  obtain ⟨u, hu⟩ := (hS.to_le
    (inf_le_left : S ⊓ Subgroup.centralizer (A : Set G) ≤ S)).exists_card_eq
  have hle : u ≤ w := by
    have hdvd := Subgroup.card_dvd_of_le
      (show S ⊓ Subgroup.centralizer (A : Set G) ≤ S ⊓ Subgroup.centralizer ({a} : Set G) by
        rw [hCA]; exact inf_le_left)
    rw [hu, hw] at hdvd
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hdvd
  rw [hs, hu, hw] at hid
  rw [hu, hw] at hmod
  have hexp : s + 3 * u = 4 * w := by
    have h1 : 2 ^ (s + 3 * u) = 2 ^ (4 * w) := by
      rw [pow_add, show 3 * u = u * 3 by ring, pow_mul,
        show 4 * w = w + w + w + w by ring, pow_add, pow_add, pow_add]
      exact hid
    exact Nat.pow_right_injective (le_refl 2) h1
  have hlt : u < w := by
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · exfalso
      subst h
      have hsu : s = u := by omega
      apply hne
      have heq : S ⊓ Subgroup.centralizer (A : Set G) = S :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hs, hu, hsu])
      rw [← heq]
      exact inf_le_right
  have h8 := eight_add_le_of_pow s u w hexp hlt hmod
  rw [hs, hu, ← pow_add]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

end Ambient

end CFSG.AGLEmbeddingD2.E9TwoGroup
