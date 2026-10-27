module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.FreeGroup.Basic

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PcSylow

open Subgroup

section Card

variable {Q : Type*} [Group Q] {n : ℕ}

@[expose] def pcSub (q : Fin n → Q) (i : ℕ) : Subgroup Q :=
  Subgroup.closure {x | ∃ k : Fin n, i ≤ k.val ∧ q k = x}

theorem pcSub_mono (q : Fin n → Q) {i j : ℕ} (h : i ≤ j) : pcSub q j ≤ pcSub q i :=
  Subgroup.closure_mono fun _ ⟨k, hk, e⟩ => ⟨k, h.trans hk, e⟩

theorem pcSub_n (q : Fin n → Q) : pcSub q n = ⊥ := by
  unfold pcSub
  rw [eq_bot_iff, Subgroup.closure_le]
  rintro _ ⟨k, hk, -⟩
  exact absurd k.isLt (by omega)

theorem pcSub_card_step {p : ℕ} (hp : 0 < p) (q : Fin n → Q) (i : Fin n)
    (hAfin : Finite (pcSub q (i.val + 1)))
    (hpow : q i ^ p ∈ pcSub q (i.val + 1))
    (hconj : ∀ j : Fin n, i < j → q i * q j * (q i)⁻¹ ∈ pcSub q (i.val + 1)) :
    Finite (pcSub q i.val) ∧
      Nat.card (pcSub q i.val) ≤ p * Nat.card (pcSub q (i.val + 1)) := by
  set A := pcSub q (i.val + 1) with hA
  set B := pcSub q i.val with hB
  set g := q i with hg
  have hAB : A ≤ B := pcSub_mono q (Nat.le_succ _)
  have hgB : g ∈ B := Subgroup.subset_closure ⟨i, le_rfl, rfl⟩
  have hgA : ∀ x ∈ A, g * x * g⁻¹ ∈ A := by
    intro x hx
    refine Subgroup.closure_induction (p := fun x _ => g * x * g⁻¹ ∈ A) ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨k, hk, rfl⟩
      exact hconj k (by
        rw [Fin.lt_def]
        exact hk)
    · simp
    · intro x y _ _ hx hy
      have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
      rw [this]
      exact A.mul_mem hx hy
    · intro x _ hx
      have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
      rw [this]
      exact A.inv_mem hx
  have hgA' : ∀ x ∈ A, g⁻¹ * x * g ∈ A := by
    have := hAfin
    have hinj : Function.Injective fun x : A => (⟨g * x * g⁻¹, hgA x x.2⟩ : A) := by
      intro x y h
      have := congrArg Subtype.val h
      simp only [mul_left_inj, mul_right_inj] at this
      exact Subtype.ext this
    have hsurj := Finite.injective_iff_surjective.1 hinj
    intro y hy
    obtain ⟨x, hx⟩ := hsurj ⟨y, hy⟩
    have : g * (x : Q) * g⁻¹ = y := congrArg Subtype.val hx
    have : g⁻¹ * y * g = x := by rw [← this]; group
    rw [this]
    exact x.2
  have hnorm : ∀ b ∈ B, ∀ a ∈ A, b * a * b⁻¹ ∈ A ∧ b⁻¹ * a * b ∈ A := by
    intro b hb
    refine Subgroup.closure_induction
      (p := fun b _ => ∀ a ∈ A, b * a * b⁻¹ ∈ A ∧ b⁻¹ * a * b ∈ A) ?_ ?_ ?_ ?_ hb
    · rintro _ ⟨k, hk, rfl⟩ a ha
      by_cases hki : k = i
      · subst hki
        exact ⟨hgA a ha, hgA' a ha⟩
      · have hk' : i.val + 1 ≤ k.val := by
          have : i.val ≠ k.val := fun h => hki (Fin.ext h.symm)
          omega
        have hkA : q k ∈ A := Subgroup.subset_closure ⟨k, hk', rfl⟩
        refine ⟨?_, ?_⟩
        · exact A.mul_mem (A.mul_mem hkA ha) (A.inv_mem hkA)
        · exact A.mul_mem (A.mul_mem (A.inv_mem hkA) ha) hkA
    · intro a ha
      simpa using ha
    · intro x y _ _ hx hy a ha
      obtain ⟨h1, h2⟩ := hy a ha
      obtain ⟨h3, h4⟩ := hx _ h1
      obtain ⟨h5, h6⟩ := hx a ha
      obtain ⟨h7, h8⟩ := hy _ h6
      refine ⟨?_, ?_⟩
      · have : x * y * a * (x * y)⁻¹ = x * (y * a * y⁻¹) * x⁻¹ := by group
        rw [this]
        exact h3
      · have : (x * y)⁻¹ * a * (x * y) = y⁻¹ * (x⁻¹ * a * x) * y := by group
        rw [this]
        exact h8
    · intro x _ hx a ha
      obtain ⟨h1, h2⟩ := hx a ha
      refine ⟨?_, ?_⟩
      · simpa using h2
      · simpa using h1
  have : (A.subgroupOf B).Normal := ⟨fun x hx b => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    simpa using (hnorm b b.2 x hx).1⟩
  set gb : B := ⟨g, hgB⟩ with hgb
  set gq : B ⧸ A.subgroupOf B := QuotientGroup.mk gb with hgqq
  have hgen : ∀ x : B, (QuotientGroup.mk x : B ⧸ A.subgroupOf B) ∈ Subgroup.zpowers gq := by
    rintro ⟨x, hx⟩
    refine Subgroup.closure_induction
      (p := fun x hx => (QuotientGroup.mk (⟨x, hx⟩ : B) : B ⧸ A.subgroupOf B) ∈
        Subgroup.zpowers gq) ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨k, hk, rfl⟩
      by_cases hki : k = i
      · subst hki
        exact Subgroup.mem_zpowers _
      · have hk' : i.val + 1 ≤ k.val := by
          have : i.val ≠ k.val := fun h => hki (Fin.ext h.symm)
          omega
        have hkA : q k ∈ A := Subgroup.subset_closure ⟨k, hk', rfl⟩
        have : (QuotientGroup.mk (⟨q k, Subgroup.subset_closure ⟨k, hk, rfl⟩⟩ : B) :
            B ⧸ A.subgroupOf B) = 1 := by
          rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
          exact hkA
        rw [this]
        exact one_mem _
    · have : (QuotientGroup.mk (⟨1, B.one_mem⟩ : B) : B ⧸ A.subgroupOf B) = 1 := rfl
      simp only [this]
      exact one_mem _
    · intro x y hx hy ihx ihy
      have : (QuotientGroup.mk (⟨x * y, B.mul_mem hx hy⟩ : B) : B ⧸ A.subgroupOf B) =
          QuotientGroup.mk ⟨x, hx⟩ * QuotientGroup.mk ⟨y, hy⟩ := rfl
      rw [this]
      exact mul_mem ihx ihy
    · intro x hx ih
      have : (QuotientGroup.mk (⟨x⁻¹, B.inv_mem hx⟩ : B) : B ⧸ A.subgroupOf B) =
          (QuotientGroup.mk ⟨x, hx⟩)⁻¹ := rfl
      rw [this]
      exact inv_mem ih
  have hgqp : gq ^ p = 1 := by
    rw [hgqq, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hpow
  have hquot : Nat.card (B ⧸ A.subgroupOf B) ≤ p := by
    have h1 : Nat.card (B ⧸ A.subgroupOf B) = Nat.card (Subgroup.zpowers gq) := by
      refine Nat.card_congr (Equiv.symm (Equiv.ofBijective (fun x : Subgroup.zpowers gq => x.1)
        ⟨Subtype.val_injective, fun y => ⟨⟨y, ?_⟩, rfl⟩⟩))
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
      exact hgen x
    rw [h1, Nat.card_zpowers]
    exact Nat.le_of_dvd hp (orderOf_dvd_of_pow_eq_one hgqp)
  have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup (A.subgroupOf B)
  have hAeq : Nat.card (A.subgroupOf B) = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAB).toEquiv
  rw [hAeq] at hmul
  refine ⟨?_, ?_⟩
  · have : Finite A := hAfin
    have : Finite (A.subgroupOf B) :=
      Finite.of_equiv A (Subgroup.subgroupOfEquivOfLe hAB).toEquiv.symm
    have : Finite (B ⧸ A.subgroupOf B) := by
      have : Finite (Subgroup.zpowers gq) := by
        rw [finite_zpowers]
        exact (isOfFinOrder_iff_pow_eq_one.2 ⟨p, hp, hgqp⟩)
      exact Finite.of_surjective (fun x : Subgroup.zpowers gq => (x : B ⧸ A.subgroupOf B))
        (fun y => ⟨⟨y, by
          obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
          exact hgen x⟩, rfl⟩)
    have : Finite B :=
      Finite.of_equiv _ (Subgroup.groupEquivQuotientProdSubgroup (s := A.subgroupOf B)).symm
    exact this
  · rw [hmul]
    exact Nat.mul_le_mul_right _ hquot

theorem pc_card_le {p : ℕ} (hp : 0 < p) (q : Fin n → Q)
    (hgen : Subgroup.closure (Set.range q) = ⊤)
    (hpow : ∀ i : Fin n, q i ^ p ∈ pcSub q (i.val + 1))
    (hconj : ∀ i j : Fin n, i < j → q i * q j * (q i)⁻¹ ∈ pcSub q (i.val + 1)) :
    Finite Q ∧ Nat.card Q ≤ p ^ n := by
  have key : ∀ m : ℕ, m ≤ n →
      Finite (pcSub q (n - m)) ∧ Nat.card (pcSub q (n - m)) ≤ p ^ m := by
    intro m
    induction m with
    | zero =>
      intro _
      simp only [Nat.sub_zero, pcSub_n, pow_zero]
      refine ⟨inferInstance, ?_⟩
      simp
    | succ m ih =>
      intro hm
      obtain ⟨hf, hc⟩ := ih (by omega)
      have hi : n - (m + 1) < n := by omega
      have e : (n - (m + 1)) + 1 = n - m := by omega
      have hf' : Finite (pcSub q (n - (m + 1) + 1)) := by rw [e]; exact hf
      have h := pcSub_card_step hp q ⟨n - (m + 1), hi⟩ hf' (hpow ⟨n - (m + 1), hi⟩)
        (fun j hj => hconj ⟨n - (m + 1), hi⟩ j hj)
      have h2 : Nat.card (pcSub q (n - (m + 1))) ≤ p * Nat.card (pcSub q (n - m)) := by
        have h3 : Nat.card (pcSub q (n - (m + 1))) ≤
            p * Nat.card (pcSub q (n - (m + 1) + 1)) := h.2
        rw [e] at h3
        exact h3
      refine ⟨h.1, ?_⟩
      calc Nat.card (pcSub q (n - (m + 1))) ≤ p * Nat.card (pcSub q (n - m)) := h2
        _ ≤ p * p ^ m := Nat.mul_le_mul_left _ hc
        _ = p ^ (m + 1) := by ring
  obtain ⟨hf, h0⟩ := key n le_rfl
  have : pcSub q (n - n) = ⊤ := by
    rw [Nat.sub_self, ← hgen]
    unfold pcSub
    congr 1
    ext x
    simp
  rw [this] at hf h0
  have : Finite (⊤ : Subgroup Q) := hf
  refine ⟨Finite.of_equiv _ (Subgroup.topEquiv (G := Q)).toEquiv, ?_⟩
  simpa using h0

end Card

section Hom

variable {n : ℕ}

@[expose] def relSet (p : ℕ) (pw : Fin n → FreeGroup (Fin n))
    (cw : Fin n → Fin n → FreeGroup (Fin n)) : Set (FreeGroup (Fin n)) :=
  {r | (∃ i, r = FreeGroup.of i ^ p * (pw i)⁻¹) ∨
    ∃ i j, i < j ∧ r = FreeGroup.of i * FreeGroup.of j * (FreeGroup.of i)⁻¹ * (cw i j)⁻¹}

@[expose] def freeSub (n : ℕ) (i : ℕ) : Subgroup (FreeGroup (Fin n)) :=
  Subgroup.closure {x | ∃ k : Fin n, i ≤ k.val ∧ FreeGroup.of k = x}

theorem exists_hom_of_pc {p : ℕ} (hp : 0 < p) (pw : Fin n → FreeGroup (Fin n))
    (cw : Fin n → Fin n → FreeGroup (Fin n))
    (hpw : ∀ i : Fin n, pw i ∈ freeSub n (i.val + 1))
    (hcw : ∀ i j : Fin n, i < j → cw i j ∈ freeSub n (i.val + 1))
    {P₀ Gm : Type*} [Group P₀] [Group Gm] [Finite P₀] (σ : Fin n → P₀) (g : Fin n → Gm)
    (hσgen : Subgroup.closure (Set.range σ) = ⊤) (hcard : Nat.card P₀ = p ^ n)
    (hσ : ∀ r ∈ relSet p pw cw, FreeGroup.lift σ r = 1)
    (hg : ∀ r ∈ relSet p pw cw, FreeGroup.lift g r = 1) :
    ∃ ψ : P₀ →* Gm, ∀ i, ψ (σ i) = g i := by
  set N : Subgroup (FreeGroup (Fin n)) := Subgroup.normalClosure (relSet p pw cw) with hN
  have hNσ : N ≤ (FreeGroup.lift σ).ker := by
    refine Subgroup.normalClosure_le_normal fun r hr => ?_
    exact (MonoidHom.mem_ker).2 (hσ r hr)
  have hNg : N ≤ (FreeGroup.lift g).ker := by
    refine Subgroup.normalClosure_le_normal fun r hr => ?_
    exact (MonoidHom.mem_ker).2 (hg r hr)
  set π : FreeGroup (Fin n) →* FreeGroup (Fin n) ⧸ N := QuotientGroup.mk' N with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective N
  set q : Fin n → FreeGroup (Fin n) ⧸ N := fun i => π (FreeGroup.of i) with hq
  have hrelN : ∀ r ∈ relSet p pw cw, π r = 1 := fun r hr =>
    (QuotientGroup.eq_one_iff r).2 (Subgroup.subset_normalClosure hr)
  have hmapfree : ∀ i : ℕ, (freeSub n i).map π ≤ pcSub q i := by
    intro i
    rw [freeSub, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    exact Subgroup.subset_closure ⟨k, hk, rfl⟩
  have hqgen : Subgroup.closure (Set.range q) = ⊤ := by
    have h1 : (⊤ : Subgroup (FreeGroup (Fin n))).map π = ⊤ := Subgroup.map_top_of_surjective _ hπs
    rw [← FreeGroup.closure_range_of (Fin n), MonoidHom.map_closure] at h1
    rw [← h1]
    congr 1
    ext x
    simp [hq]
  have hqpow : ∀ i : Fin n, q i ^ p ∈ pcSub q (i.val + 1) := by
    intro i
    have h1 : π (FreeGroup.of i ^ p * (pw i)⁻¹) = 1 := hrelN _ (Or.inl ⟨i, rfl⟩)
    rw [map_mul, map_inv, mul_inv_eq_one, map_pow] at h1
    show π (FreeGroup.of i) ^ p ∈ _
    rw [h1]
    exact hmapfree _ (Subgroup.mem_map.2 ⟨pw i, hpw i, rfl⟩)
  have hqconj : ∀ i j : Fin n, i < j → q i * q j * (q i)⁻¹ ∈ pcSub q (i.val + 1) := by
    intro i j hij
    have h1 : π (FreeGroup.of i * FreeGroup.of j * (FreeGroup.of i)⁻¹ * (cw i j)⁻¹) = 1 :=
      hrelN _ (Or.inr ⟨i, j, hij, rfl⟩)
    rw [map_mul, map_inv, mul_inv_eq_one] at h1
    show π (FreeGroup.of i) * π (FreeGroup.of j) * (π (FreeGroup.of i))⁻¹ ∈ _
    rw [← map_mul, ← map_inv, ← map_mul, h1]
    exact hmapfree _ (Subgroup.mem_map.2 ⟨cw i j, hcw i j hij, rfl⟩)
  obtain ⟨hFfin, hFcard⟩ := pc_card_le hp q hqgen hqpow hqconj
  set φ : FreeGroup (Fin n) ⧸ N →* P₀ := QuotientGroup.lift N (FreeGroup.lift σ) hNσ with hφ
  have hφs : Function.Surjective φ := by
    intro x
    have hx : x ∈ Subgroup.closure (Set.range σ) := by rw [hσgen]; trivial
    have hle : Subgroup.closure (Set.range σ) ≤ (FreeGroup.lift σ).range := by
      rw [Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      exact ⟨FreeGroup.of i, by simp⟩
    obtain ⟨y, rfl⟩ := hle hx
    exact ⟨π y, rfl⟩
  have hbij : Function.Bijective φ := by
    have := hFfin
    rw [Nat.bijective_iff_surjective_and_card]
    refine ⟨hφs, le_antisymm ?_ ?_⟩
    · exact hFcard.trans hcard.ge
    · exact Nat.card_le_card_of_surjective _ hφs
  let e : FreeGroup (Fin n) ⧸ N ≃* P₀ := MulEquiv.ofBijective φ hbij
  set ψ' : FreeGroup (Fin n) ⧸ N →* Gm := QuotientGroup.lift N (FreeGroup.lift g) hNg with hψ'
  refine ⟨ψ'.comp e.symm.toMonoidHom, fun i => ?_⟩
  have : σ i = e (q i) := by
    show σ i = φ (π (FreeGroup.of i))
    simp [hφ, hπ]
  rw [this]
  simp [hψ', hq, hπ]

end Hom

section Inj

variable {P₀ Gm : Type*} [Group P₀] [Finite P₀] [Group Gm]

theorem exists_mem_center_of_normal {p : ℕ} (hp : p.Prime) (hP : IsPGroup p P₀)
    (K : Subgroup P₀) [K.Normal] (hK : K ≠ ⊥) : ∃ k ∈ K, k ∈ Subgroup.center P₀ ∧ k ≠ 1 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let : MulAction P₀ K :=
    { smul := fun g k => ⟨g * k * g⁻¹, Subgroup.Normal.conj_mem inferInstance (k : P₀) k.2 g⟩
      one_smul := fun k => Subtype.ext (by
        show (1 : P₀) * (k : P₀) * (1 : P₀)⁻¹ = k
        simp)
      mul_smul := fun a b k => Subtype.ext (by
        show (a * b) * (k : P₀) * (a * b)⁻¹ = a * (b * (k : P₀) * b⁻¹) * a⁻¹
        group) }
  have hmod := hP.card_modEq_card_fixedPoints K
  have hKp : IsPGroup p K := hP.to_subgroup K
  obtain ⟨m, hm, hKc⟩ := (hKp.nontrivial_iff_card).1 (by
    rw [Subgroup.nontrivial_iff_ne_bot]; exact hK)
  have hdvd : p ∣ Nat.card K := by
    rw [hKc]
    exact dvd_pow_self p hm.ne'
  have hdvd2 : p ∣ Nat.card (MulAction.fixedPoints P₀ K) :=
    (Nat.modEq_zero_iff_dvd.1 (hmod.symm.trans (Nat.modEq_zero_iff_dvd.2 hdvd)))
  have h1fix : (1 : K) ∈ MulAction.fixedPoints P₀ K := fun g => Subtype.ext (by
    show g * (1 : P₀) * g⁻¹ = 1
    simp)
  have hpos : 0 < Nat.card (MulAction.fixedPoints P₀ K) :=
    Nat.card_pos_iff.2 ⟨⟨⟨1, h1fix⟩⟩, inferInstance⟩
  have h2 : 1 < Nat.card (MulAction.fixedPoints P₀ K) :=
    lt_of_lt_of_le hp.one_lt (Nat.le_of_dvd hpos hdvd2)
  have : Nontrivial (MulAction.fixedPoints P₀ K) := Finite.one_lt_card_iff_nontrivial.1 h2
  obtain ⟨⟨k, hk⟩, hne⟩ := exists_ne (⟨1, h1fix⟩ : MulAction.fixedPoints P₀ K)
  refine ⟨k, k.2, ?_, fun h => hne (Subtype.ext (Subtype.ext h))⟩
  rw [Subgroup.mem_center_iff]
  intro g
  have e : g * (k : P₀) * g⁻¹ = k := congrArg Subtype.val (hk g)
  calc g * (k : P₀) = (g * k * g⁻¹) * g := by group
    _ = k * g := by rw [e]

theorem injective_of_center {p : ℕ} (hp : p.Prime) (hP : IsPGroup p P₀) (ψ : P₀ →* Gm)
    (hz : ∀ c ∈ Subgroup.center P₀, c ≠ 1 → ψ c ≠ 1) : Function.Injective ψ := by
  rw [← MonoidHom.ker_eq_bot_iff]
  by_contra hK
  obtain ⟨k, hk, hkc, hk1⟩ := exists_mem_center_of_normal hp hP ψ.ker hK
  exact hz k hkc hk1 (MonoidHom.mem_ker.1 hk)

omit [Finite P₀] in
theorem exists_conj_into_range [Finite Gm] {p : ℕ} (hp : p.Prime) (ψ : P₀ →* Gm)
    (hψ : Function.Injective ψ) {e m : ℕ} (hP : Nat.card P₀ = p ^ e)
    (hG : Nat.card Gm = p ^ e * m) (hm : ¬ p ∣ m) {s : Gm} (hs : orderOf s = p) :
    ∃ g : Gm, g⁻¹ * s * g ∈ ψ.range := by
  have : Fact p.Prime := ⟨hp⟩
  have hcardR : Nat.card ψ.range = p ^ e := by
    rw [← hP]
    exact (Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv).symm
  have hfac : (Nat.card Gm).factorization p = e := by
    rw [hG, Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) (by
      rintro rfl
      exact hm (dvd_zero p)), hp.factorization_pow]
    simp [Nat.factorization_eq_zero_of_not_dvd hm]
  let Sy : Sylow p Gm := Sylow.ofCard ψ.range (by rw [hfac]; exact hcardR)
  have hspow : IsPGroup p (Subgroup.zpowers s) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hs, pow_one]
  obtain ⟨Q, hQ⟩ := hspow.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Gm Sy Q
  have hsQ : s ∈ (Q : Subgroup Gm) := hQ (Subgroup.mem_zpowers s)
  refine ⟨g, ?_⟩
  rw [← hg, Sylow.coe_subgroup_smul] at hsQ
  rw [Subgroup.mem_smul_pointwise_iff_exists] at hsQ
  obtain ⟨t, ht, e⟩ := hsQ
  have : g⁻¹ * s * g = t := by
    rw [← e]
    simp [MulAut.conj_apply]
    group
  rw [this]
  exact ht

end Inj

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PcSylow
