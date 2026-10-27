module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SmallRankOneData

public section

namespace CFSG.AGLEmbedding.KFactProofs.NonUnitary

open CFSG.Open

variable {K : Type} [Group K] {p : ℕ}

theorem mem_of_conj_mem (hp : p.Prime) (T : Sylow p K) (hZ : Subgroup.center K = ⊥)
    (Y : Subgroup (MulAut K)) (hY : IsPGroup p Y)
    (hYN : ∀ b ∈ Subgroup.normalizer ((T : Subgroup K) : Set K), ∀ α ∈ Y,
      MulAut.conj b * α * (MulAut.conj b)⁻¹ ∈ Y) {c : K} (hc : MulAut.conj c ∈ Y) :
    c ∈ (T : Subgroup K) := by
  have : Fact p.Prime := ⟨hp⟩
  have hinj := conj_injective_of_center_trivial hZ
  set C : Subgroup K := Y.comap (MulAut.conj : K →* MulAut K) with hC
  have hCp : IsPGroup p C := by
    intro c
    obtain ⟨k, hk⟩ := hY ⟨MulAut.conj (c : K), c.2⟩
    refine ⟨k, Subtype.ext (hinj ?_)⟩
    have := congrArg Subtype.val hk
    simpa using this
  have hCN : ∀ b ∈ Subgroup.normalizer ((T : Subgroup K) : Set K), ∀ c ∈ C, b * c * b⁻¹ ∈ C := by
    intro b hb c hc
    show MulAut.conj (b * c * b⁻¹) ∈ Y
    have := hYN b hb _ hc
    simpa [map_mul, map_inv] using this
  have hTN : (T : Subgroup K) ≤ Subgroup.normalizer (C : Set K) := by
    intro t ht
    have htB : t ∈ Subgroup.normalizer ((T : Subgroup K) : Set K) := Subgroup.le_normalizer ht
    have htB' : t⁻¹ ∈ Subgroup.normalizer ((T : Subgroup K) : Set K) := inv_mem htB
    rw [Subgroup.mem_normalizer_iff]
    intro c
    constructor
    · intro hc
      exact hCN t htB c hc
    · intro hc
      have := hCN t⁻¹ htB' _ hc
      have e : t⁻¹ * (t * c * t⁻¹) * t⁻¹⁻¹ = c := by group
      rwa [e] at this
  have hsup : IsPGroup p ↥(C ⊔ (T : Subgroup K)) := hCp.to_sup_of_normal_left' T.2 hTN
  have hCT : C ≤ (T : Subgroup K) := by
    have := T.is_maximal' hsup le_sup_right
    exact le_sup_left.trans this.le
  exact hCT hc

theorem mul_apply_inv_mem (hp : p.Prime) (T : Sylow p K) (hZ : Subgroup.center K = ⊥)
    (Y : Subgroup (MulAut K)) (hY : IsPGroup p Y)
    (hYN : ∀ b ∈ Subgroup.normalizer ((T : Subgroup K) : Set K), ∀ α ∈ Y,
      MulAut.conj b * α * (MulAut.conj b)⁻¹ ∈ Y) {y : MulAut K} (hy : y ∈ Y) {b : K}
    (hb : b ∈ Subgroup.normalizer ((T : Subgroup K) : Set K)) :
    b * (y b)⁻¹ ∈ (T : Subgroup K) := by
  refine mem_of_conj_mem hp T hZ Y hY hYN ?_
  have h1 := Y.mul_mem (hYN b hb y hy) (Y.inv_mem hy)
  have h2 : MulAut.conj b * y * (MulAut.conj b)⁻¹ * y⁻¹ = MulAut.conj (b * (y b)⁻¹) := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rwa [h2] at h1

theorem apply_mem (hp : p.Prime) (T : Sylow p K) (hZ : Subgroup.center K = ⊥)
    (Y : Subgroup (MulAut K)) (hY : IsPGroup p Y)
    (hYN : ∀ b ∈ Subgroup.normalizer ((T : Subgroup K) : Set K), ∀ α ∈ Y,
      MulAut.conj b * α * (MulAut.conj b)⁻¹ ∈ Y) {y : MulAut K} (hy : y ∈ Y) {t : K}
    (ht : t ∈ (T : Subgroup K)) : y t ∈ (T : Subgroup K) := by
  have h := mul_apply_inv_mem hp T hZ Y hY hYN hy (Subgroup.le_normalizer ht)
  have e : y t = (t * (y t)⁻¹)⁻¹ * t := by group
  rw [e]
  exact (T : Subgroup K).mul_mem ((T : Subgroup K).inv_mem h) ht

theorem pLe_of_scalar_torus [Finite K] (hp : p.Prime) (T : Sylow p K)
    (hZ : Subgroup.center K = ⊥) {F : Type} [Field F] [CharP F p]
    (ψ : Multiplicative F →* K) (hψ : Function.Injective ψ)
    (hVT : ∀ a : Multiplicative F, ψ a ∈ (T : Subgroup K) ∧
      ∀ t ∈ (T : Subgroup K), ψ a * t = t * ψ a)
    (hVinv : ∀ f : MulAut K, (∀ t ∈ (T : Subgroup K), f t ∈ (T : Subgroup K)) →
      ∀ a : Multiplicative F, ∃ b : Multiplicative F, f (ψ a) = ψ b)
    (S : Set F) (hS : ∀ x : F, ∃ r s : F, (r = 0 ∨ r ∈ S) ∧ (s = 0 ∨ s ∈ S) ∧ x = r - s)
    (hsc : ∀ μ ∈ S, ∃ c ∈ Subgroup.normalizer ((T : Subgroup K) : Set K),
      ∀ a : Multiplicative F, c * ψ a * c⁻¹ = ψ (Multiplicative.ofAdd (μ * Multiplicative.toAdd a)))
    (hinner : ∀ f : MulAut K, (∀ a : Multiplicative F, f (ψ a) = ψ a) →
      ∃ u ∈ (T : Subgroup K), f = MulAut.conj u)
    (Y : Subgroup (MulAut K)) (hY : IsPGroup p Y)
    (hYN : ∀ b ∈ Subgroup.normalizer ((T : Subgroup K) : Set K), ∀ α ∈ Y,
      MulAut.conj b * α * (MulAut.conj b)⁻¹ ∈ Y) :
    ∀ α ∈ Y, ∃ u ∈ (T : Subgroup K), α = MulAut.conj u := by
  intro y hy
  have : Fact p.Prime := ⟨hp⟩
  have hyT : ∀ t ∈ (T : Subgroup K), y t ∈ (T : Subgroup K) := fun t ht =>
    apply_mem hp T hZ Y hY hYN hy ht
  choose g hg using hVinv y hyT
  let α : F → F := fun a => Multiplicative.toAdd (g (Multiplicative.ofAdd a))
  have hψα : ∀ a : F, y (ψ (Multiplicative.ofAdd a)) = ψ (Multiplicative.ofAdd (α a)) :=
    fun a => hg _
  have hαadd : ∀ a b : F, α (a + b) = α a + α b := by
    intro a b
    apply Multiplicative.ofAdd.injective
    apply hψ
    have h1 := hψα (a + b)
    rw [ofAdd_add, map_mul, map_mul, hψα, hψα] at h1
    rw [ofAdd_add, map_mul]
    exact h1.symm
  have hα0 : α 0 = 0 := by
    have h := hαadd 0 0
    rw [add_zero] at h
    linear_combination -h
  have hαneg : ∀ a : F, α (-a) = -α a := by
    intro a
    have := hαadd a (-a)
    rw [add_neg_cancel, hα0] at this
    exact (neg_eq_of_add_eq_zero_right this.symm).symm
  have hαsub : ∀ a b : F, α (a - b) = α a - α b := by
    intro a b
    rw [sub_eq_add_neg, hαadd, hαneg, ← sub_eq_add_neg]
  have hαS : ∀ μ ∈ S, ∀ a : F, α (μ * a) = μ * α a := by
    intro μ hμ a
    obtain ⟨c, hcN, hc⟩ := hsc μ hμ
    have hτ := mul_apply_inv_mem hp T hZ Y hY hYN hy hcN
    set τ : K := c * (y c)⁻¹ with hτdef
    have hyc : y c = τ⁻¹ * c := by rw [hτdef]; group
    have hcomm : ∀ b : Multiplicative F, τ⁻¹ * (c * ψ b * c⁻¹) * τ = c * ψ b * c⁻¹ := by
      intro b
      rw [hc b]
      obtain ⟨-, hcen⟩ := hVT (Multiplicative.ofAdd (μ * Multiplicative.toAdd b))
      have := hcen τ⁻¹ ((T : Subgroup K).inv_mem hτ)
      calc τ⁻¹ * ψ (Multiplicative.ofAdd (μ * Multiplicative.toAdd b)) * τ
          = ψ (Multiplicative.ofAdd (μ * Multiplicative.toAdd b)) * τ⁻¹ * τ := by rw [← this]
        _ = ψ (Multiplicative.ofAdd (μ * Multiplicative.toAdd b)) := by group
    have h1 : y (ψ (Multiplicative.ofAdd (μ * a))) =
        ψ (Multiplicative.ofAdd (μ * α a)) := by
      have e1 : ψ (Multiplicative.ofAdd (μ * a)) =
          c * ψ (Multiplicative.ofAdd a) * c⁻¹ := (hc (Multiplicative.ofAdd a)).symm
      rw [e1, map_mul, map_mul, map_inv, hψα, hyc]
      have e2 := hcomm (Multiplicative.ofAdd (α a))
      have e3 := hc (Multiplicative.ofAdd (α a))
      rw [toAdd_ofAdd] at e3
      rw [← e3, ← e2]
      group
    rw [hψα] at h1
    exact Multiplicative.ofAdd.injective (hψ h1)
  have hαlin : ∀ x a : F, α (x * a) = x * α a := by
    intro x a
    obtain ⟨r, s, hr, hs, rfl⟩ := hS x
    have key : ∀ t : F, (t = 0 ∨ t ∈ S) → α (t * a) = t * α a := by
      rintro t (rfl | ht)
      · rw [zero_mul, hα0, zero_mul]
      · exact hαS t ht a
    rw [sub_mul, hαsub, key r hr, key s hs, sub_mul]
  set c₀ : F := α 1 with hc₀
  have hαc : ∀ a : F, α a = c₀ * a := by
    intro a
    have := hαlin a 1
    rw [mul_one] at this
    rw [this, hc₀]
    ring
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hY ⟨y, hy⟩
  have hykpow : y ^ p ^ k = 1 := by
    have := pow_orderOf_eq_one (⟨y, hy⟩ : Y)
    rw [hk] at this
    exact congrArg Subtype.val this
  have hpow : ∀ (n : ℕ) (a : F),
      (y ^ n) (ψ (Multiplicative.ofAdd a)) = ψ (Multiplicative.ofAdd (c₀ ^ n * a)) := by
    intro n
    induction n with
    | zero => intro a; simp
    | succ n ih =>
      intro a
      rw [pow_succ', MulAut.mul_apply, ih, hψα, hαc]
      congr 2
      ring
  have hc₀pow : c₀ ^ p ^ k = 1 := by
    have h1 := hpow (p ^ k) 1
    rw [hykpow, MulAut.one_apply, mul_one] at h1
    have := Multiplicative.ofAdd.injective (hψ h1)
    exact this.symm
  have hc₀1 : c₀ = 1 := by
    have h1 : (c₀ - 1) ^ p ^ k = 0 := by
      rw [sub_pow_char_pow, hc₀pow, one_pow, sub_self]
    exact sub_eq_zero.mp ((pow_eq_zero_iff (pow_ne_zero k hp.ne_zero)).mp h1)
  apply hinner y
  intro z
  have h := hψα (Multiplicative.toAdd z)
  rw [hαc, hc₀1, one_mul] at h
  simpa using h

theorem apply_mem_center_of_stabilizes [Finite K] {T : Subgroup K} (f : MulAut K)
    (hf : ∀ t ∈ T, f t ∈ T) {z : K} (hzT : z ∈ T) (hz : ∀ t ∈ T, z * t = t * z) :
    f z ∈ T ∧ ∀ t ∈ T, f z * t = t * f z := by
  refine ⟨hf z hzT, fun t ht => ?_⟩
  have hinj : Function.Injective (fun x : T => (⟨f x, hf x x.2⟩ : T)) := fun x y hxy =>
    Subtype.ext (f.injective (congrArg Subtype.val hxy))
  obtain ⟨⟨t', ht'⟩, ht'e⟩ := Finite.injective_iff_surjective.mp hinj ⟨t, ht⟩
  have h : f t' = t := congrArg Subtype.val ht'e
  rw [← h, ← map_mul, ← map_mul, hz t' ht']

theorem range_le_of_invariant [Finite K] (hp : p.Prime) (T : Sylow p K) {F : Type} [Field F]
    (ψ : Multiplicative F →* K)
    (hcen : ∀ z ∈ (T : Subgroup K), (∀ t ∈ (T : Subgroup K), z * t = t * z) →
      ∃ a : Multiplicative F, ψ a = z)
    (hsc : ∀ μ : Fˣ, ∃ c ∈ Subgroup.normalizer ((T : Subgroup K) : Set K),
      ∀ a : Multiplicative F, c * ψ a * c⁻¹ = ψ (Multiplicative.ofAdd (μ * Multiplicative.toAdd a)))
    (V : Subgroup K) (hVT' : V ≤ (T : Subgroup K)) (hV : V ≠ ⊥)
    (hVN : Subgroup.normalizer ((T : Subgroup K) : Set K) ≤ Subgroup.normalizer (V : Set K)) :
    ∀ a : Multiplicative F, ψ a ∈ V := by
  have : Fact p.Prime := ⟨hp⟩
  have hnil : Group.IsNilpotent (T : Subgroup K) := T.2.isNilpotent
  have hnorm : (V.subgroupOf (T : Subgroup K)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVT').2 (Subgroup.le_normalizer.trans hVN)
  have hne : V.subgroupOf (T : Subgroup K) ≠ ⊥ := by
    intro h
    apply hV
    rw [eq_bot_iff]
    intro v hv
    have : (⟨v, hVT' hv⟩ : (T : Subgroup K)) ∈ V.subgroupOf (T : Subgroup K) := hv
    rw [h, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.2 (congrArg Subtype.val this)
  obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  obtain ⟨hyV, hyZ⟩ := Subgroup.mem_inf.1 hy
  set x : K := (y : K) with hxdef
  have hxT : x ∈ (T : Subgroup K) := y.2
  have hx1 : x ≠ 1 := fun h => hy1 (Subtype.ext (Subtype.ext h))
  have hxV' : x ∈ V := hyV
  have hxc : ∀ t ∈ (T : Subgroup K), x * t = t * x := fun t ht =>
    congrArg Subtype.val (Subgroup.mem_center_iff.1 hyZ ⟨t, ht⟩).symm
  obtain ⟨w, hw⟩ := hcen x hxT hxc
  have hw0 : Multiplicative.toAdd w ≠ 0 := by
    intro h0
    apply hx1
    have : w = 1 := Multiplicative.toAdd.injective (by simpa using h0)
    rw [← hw, this, map_one]
  intro a
  by_cases ha : Multiplicative.toAdd a = 0
  · have : a = 1 := Multiplicative.toAdd.injective (by simpa using ha)
    rw [this, map_one]
    exact V.one_mem
  · obtain ⟨c, hcN, hc⟩ := hsc (Units.mk0 (Multiplicative.toAdd a / Multiplicative.toAdd w)
      (div_ne_zero ha hw0))
    have h1 := (Subgroup.mem_normalizer_iff.1 (hVN hcN) x).1 hxV'
    have h2 : c * x * c⁻¹ = ψ a := by
      rw [← hw, hc]
      congr 1
      apply Multiplicative.toAdd.injective
      simp only [Units.val_mk0, toAdd_ofAdd]
      field_simp
    rwa [h2] at h1

end CFSG.AGLEmbedding.KFactProofs.NonUnitary
