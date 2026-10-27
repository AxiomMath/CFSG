module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.Fischer

variable {G : Type*} [Group G]

@[expose] def OutTwo (G : Type*) [Group G] : Prop :=
  ∀ β : MulAut G, ∃ k : ℕ, ∃ g : G, β ^ (2 ^ k) = MulAut.conj g

@[expose] def innerAut (G : Type*) [Group G] : Subgroup (MulAut G) :=
  (MulAut.conj : G →* MulAut G).range

theorem mem_innerAut {β : MulAut G} : β ∈ innerAut G ↔ ∃ g : G, MulAut.conj g = β := Iff.rfl

theorem innerAut_normal : (innerAut G).Normal := by
  constructor
  rintro _ ⟨g, rfl⟩ β
  refine ⟨β g, ?_⟩
  ext x
  simp [MulAut.conj_apply]

@[expose] def fixAut (t : G) : Subgroup (MulAut G) where
  carrier := {α | α t = t}
  one_mem' := rfl
  mul_mem' {α β} hα hβ := by
    show α (β t) = t
    rw [show β t = t from hβ, show α t = t from hα]
  inv_mem' {α} hα := by
    show α.symm t = t
    rw [MulEquiv.symm_apply_eq]
    exact (show α t = t from hα).symm

theorem mem_fixAut {t : G} {α : MulAut G} : α ∈ fixAut t ↔ α t = t := Iff.rfl

theorem map_mem_centralizer {t : G} (α : fixAut t) {x : G}
    (hx : x ∈ Subgroup.centralizer {t}) : (α : MulAut G) x ∈ Subgroup.centralizer {t} := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
  have ht : (α : MulAut G) t = t := α.2
  calc (α : MulAut G) x * t = (α : MulAut G) x * (α : MulAut G) t := by rw [ht]
    _ = (α : MulAut G) (x * t) := (map_mul _ _ _).symm
    _ = (α : MulAut G) (t * x) := by rw [hx]
    _ = t * (α : MulAut G) x := by rw [map_mul, ht]

@[expose] noncomputable def restrictCent (t : G) :
    fixAut t →* MulAut (Subgroup.centralizer {t}) where
  toFun α :=
    { toFun := fun x => ⟨(α : MulAut G) x, map_mem_centralizer α x.2⟩
      invFun := fun x => ⟨((α⁻¹ : fixAut t) : MulAut G) x, map_mem_centralizer α⁻¹ x.2⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun x => Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp) }
  map_one' := by ext x; rfl
  map_mul' α β := by ext x; rfl

theorem restrictCent_apply (t : G) (α : fixAut t) (x : Subgroup.centralizer {t}) :
    ((restrictCent t α x : Subgroup.centralizer {t}) : G) = (α : MulAut G) x := rfl

theorem eq_one_of_trivial_sup {A B : Subgroup G} (hAB : A ⊔ B = ⊤) {γ : MulAut G}
    (hA : ∀ x ∈ A, γ x = x) (hB : ∀ x ∈ B, γ x = x) : γ = 1 := by
  let F : Subgroup G :=
    { carrier := {x | γ x = x}
      one_mem' := map_one γ
      mul_mem' := fun {x y} hx hy => by
        show γ (x * y) = x * y
        rw [map_mul, show γ x = x from hx, show γ y = y from hy]
      inv_mem' := fun {x} hx => by
        show γ x⁻¹ = x⁻¹
        rw [map_inv, show γ x = x from hx] }
  have hF : A ⊔ B ≤ F := sup_le (fun x hx => hA x hx) (fun x hx => hB x hx)
  ext x
  exact hF (hAB ▸ Subgroup.mem_top x)

theorem pow_mem_of_eq_mul {H : Type*} [Group H] {N : Subgroup H} [N.Normal] {a b c : H}
    (hc : c ∈ N) (hab : a = c * b) {n : ℕ} (hb : b ^ n ∈ N) : a ^ n ∈ N := by
  have h1 : (QuotientGroup.mk a : H ⧸ N) = QuotientGroup.mk b := by
    rw [hab, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff c).2 hc, one_mul]
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, h1, ← QuotientGroup.mk_pow,
    QuotientGroup.eq_one_iff]
  exact hb

theorem pow_two_pow_mem {H : Type*} [Group H] {N : Subgroup H} {a : H} {k m : ℕ}
    (h : (a ^ (2 ^ k)) ^ (2 ^ m) ∈ N) : a ^ (2 ^ (k + m)) ∈ N := by
  rwa [pow_add, pow_mul]

theorem restrict_pow_apply (t : G) (α : fixAut t) (n : ℕ) (x : Subgroup.centralizer {t}) :
    ((restrictCent t α ^ n) x : G) = ((α : MulAut G) ^ n) (x : G) := by
  rw [← map_pow, restrictCent_apply, Subgroup.coe_pow]

theorem pow_mem_innerAut_of_centralizers {t t₁ : G} {α : MulAut G}
    (hα : ∃ g : G, α t = g * t * g⁻¹)
    (hH : OutTwo (Subgroup.centralizer {t})) (hH₁ : OutTwo (Subgroup.centralizer {t₁}))
    (ht₁ : t₁ ∈ Subgroup.centralizer {t})
    (hgen : Subgroup.centralizer {t} ⊔ Subgroup.centralizer {t₁} = ⊤)
    (hC : ∀ y ∈ Subgroup.centralizer {t₁}, (∀ x ∈ Subgroup.centralizer {t},
      x ∈ Subgroup.centralizer {t₁} → y * x = x * y) → ∃ r : ℕ, y ^ (2 ^ r) = 1) :
    ∃ k : ℕ, α ^ (2 ^ k) ∈ innerAut G := by
  have hN := innerAut_normal (G := G)
  obtain ⟨g, hg⟩ := hα
  set α' := MulAut.conj g⁻¹ * α with hα'def
  have hα' : α' t = t := by
    rw [hα'def, MulAut.mul_apply, hg, MulAut.conj_apply]
    group
  suffices h : ∃ k, α' ^ (2 ^ k) ∈ innerAut G by
    obtain ⟨k, hk⟩ := h
    refine ⟨k, pow_mem_of_eq_mul (mem_innerAut.2 ⟨g, rfl⟩) ?_ hk⟩
    rw [hα'def, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  obtain ⟨k, h, hk⟩ := hH (restrictCent t ⟨α', hα'⟩)
  set α₁ : MulAut G := MulAut.conj (h : G)⁻¹ * α' ^ (2 ^ k) with hα₁def
  have hpow : ∀ x ∈ Subgroup.centralizer {t}, (α' ^ (2 ^ k)) x = h * x * (h : G)⁻¹ := by
    intro x hx
    have := congrArg (fun β : MulAut _ => ((β ⟨x, hx⟩ : Subgroup.centralizer {t}) : G)) hk
    rw [restrict_pow_apply] at this
    rw [this, MulAut.conj_apply]
    rfl
  have hα₁H : ∀ x ∈ Subgroup.centralizer {t}, α₁ x = x := by
    intro x hx
    rw [hα₁def, MulAut.mul_apply, hpow x hx, MulAut.conj_apply]
    group
  have hα₁Hpow : ∀ n : ℕ, ∀ x ∈ Subgroup.centralizer {t}, (α₁ ^ n) x = x := by
    intro n
    induction n with
    | zero => intro x _; rfl
    | succ n ih =>
      intro x hx
      rw [pow_succ, MulAut.mul_apply, hα₁H x hx, ih x hx]
  have hα₁t₁ : α₁ t₁ = t₁ := hα₁H t₁ ht₁
  obtain ⟨m, y, hm⟩ := hH₁ (restrictCent t₁ ⟨α₁, hα₁t₁⟩)
  have hy : ∀ x ∈ Subgroup.centralizer {t}, x ∈ Subgroup.centralizer {t₁} →
      (y : G) * x = x * y := by
    intro x hx hx₁
    have := congrArg (fun β : MulAut _ => ((β ⟨x, hx₁⟩ : Subgroup.centralizer {t₁}) : G)) hm
    rw [restrict_pow_apply, hα₁Hpow _ x hx, MulAut.conj_apply] at this
    have e : x = y * x * (y : G)⁻¹ := this
    calc (y : G) * x = y * x * (y : G)⁻¹ * y := by group
      _ = x * y := by rw [← e]
  obtain ⟨r, hr⟩ := hC y y.2 hy
  have hα₁one : α₁ ^ (2 ^ (m + r)) = 1 := by
    apply eq_one_of_trivial_sup hgen
    · exact fun x hx => hα₁Hpow _ x hx
    · intro x hx₁
      have h1 : restrictCent t₁ ⟨α₁, hα₁t₁⟩ ^ (2 ^ (m + r)) = 1 := by
        rw [pow_add, pow_mul, hm, ← map_pow]
        have : y ^ (2 ^ r) = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hr)
        rw [this, map_one]
      have := congrArg (fun β : MulAut _ => ((β ⟨x, hx₁⟩ : Subgroup.centralizer {t₁}) : G)) h1
      rw [restrict_pow_apply] at this
      exact this
  refine ⟨k + (m + r), ?_⟩
  rw [pow_add, pow_mul]
  refine pow_mem_of_eq_mul (N := innerAut G) (mem_innerAut.2 ⟨(h : G), rfl⟩) ?_
    (by rw [hα₁one]; exact (innerAut G).one_mem)
  rw [hα₁def, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]

theorem outTwo_of_centralizers {t t₁ : G}
    (hcls : ∀ α : MulAut G, ∃ g : G, α t = g * t * g⁻¹)
    (hH : OutTwo (Subgroup.centralizer {t})) (hH₁ : OutTwo (Subgroup.centralizer {t₁}))
    (ht₁ : t₁ ∈ Subgroup.centralizer {t})
    (hgen : Subgroup.centralizer {t} ⊔ Subgroup.centralizer {t₁} = ⊤)
    (hC : ∀ y ∈ Subgroup.centralizer {t₁}, (∀ x ∈ Subgroup.centralizer {t},
      x ∈ Subgroup.centralizer {t₁} → y * x = x * y) → ∃ r : ℕ, y ^ (2 ^ r) = 1) :
    ∀ α : MulAut G, ∃ k : ℕ, α ^ (2 ^ k) ∈ innerAut G :=
  fun α => pow_mem_innerAut_of_centralizers (hcls α) hH hH₁ ht₁ hgen hC

theorem finite_mulAut [Finite G] : Finite (MulAut G) :=
  Finite.of_injective (fun f : MulAut G => (f : G → G)) fun _ _ h => MulEquiv.ext (congrFun h)

theorem isConj_map_mulAut (β : MulAut G) {a b : G} (h : IsConj a b) : IsConj (β a) (β b) :=
  (β : G →* G).map_isConj h

theorem isConj_of_mem_innerAut {β : MulAut G} (hβ : β ∈ innerAut G) (a : G) : IsConj (β a) a := by
  obtain ⟨g, rfl⟩ := hβ
  exact (isConj_iff.2 ⟨g, by rw [MulAut.conj_apply]⟩).symm

theorem pow_mem_innerAut_of_two_classes [Finite G] {t t₂ t₁ : G} (ht : t * t = 1) (ht1 : t ≠ 1)
    (hinv : ∀ s : G, s * s = 1 → s ≠ 1 → IsConj s t ∨ IsConj s t₂)
    (hH : OutTwo (Subgroup.centralizer {t})) (hH₁ : OutTwo (Subgroup.centralizer {t₁}))
    (ht₁ : t₁ ∈ Subgroup.centralizer {t})
    (hgen : Subgroup.centralizer {t} ⊔ Subgroup.centralizer {t₁} = ⊤)
    (hC : ∀ y ∈ Subgroup.centralizer {t₁}, (∀ x ∈ Subgroup.centralizer {t},
      x ∈ Subgroup.centralizer {t₁} → y * x = x * y) → ∃ r : ℕ, y ^ (2 ^ r) = 1)
    (α : MulAut G) : ∃ k : ℕ, α ^ (2 ^ k) ∈ innerAut G := by
  have := finite_mulAut (G := G)
  have hN := innerAut_normal (G := G)
  set q : MulAut G ⧸ innerAut G := QuotientGroup.mk α
  have hn : orderOf q ≠ 0 := (orderOf_pos q).ne'
  obtain ⟨a, m, hm, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn 2 (by norm_num)
  set β := α ^ (2 ^ a) with hβdef
  have hβm : β ^ m ∈ innerAut G := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hβdef, QuotientGroup.mk_pow, ← pow_mul,
      ← hnm, pow_orderOf_eq_one]
  have hinvol : ∀ (γ : MulAut G) (s : G), s * s = 1 → s ≠ 1 → γ s * γ s = 1 ∧ γ s ≠ 1 :=
    fun γ s hs hs1 => ⟨by rw [← map_mul, hs, map_one], fun h => hs1 (by
      rw [← map_one γ] at h; exact γ.injective h)⟩
  have hβt : IsConj (β t) t := by
    by_contra hc
    have h1 : IsConj (β t) t₂ :=
      (hinv _ (hinvol β t ht ht1).1 (hinvol β t ht ht1).2).resolve_left hc
    have hnt : ¬ IsConj t t₂ := fun h => hc (h1.trans h.symm)
    have ht₂ : t₂ * t₂ = 1 ∧ t₂ ≠ 1 := by
      obtain ⟨c, hc'⟩ := isConj_iff.1 h1
      have hb := hinvol β t ht ht1
      rw [← hc']
      constructor
      · calc c * β t * c⁻¹ * (c * β t * c⁻¹) = c * (β t * β t) * c⁻¹ := by group
          _ = 1 := by rw [hb.1]; group
      · intro h
        apply hb.2
        calc β t = c⁻¹ * (c * β t * c⁻¹) * c := by group
          _ = 1 := by rw [h]; group
    have h2 : IsConj (β t₂) t := by
      rcases hinv _ (hinvol β t₂ ht₂.1 ht₂.2).1 (hinvol β t₂ ht₂.1 ht₂.2).2 with h | h
      · exact h
      · exfalso
        apply hnt
        have := isConj_map_mulAut β⁻¹ (h1.trans h.symm)
        simpa using this
    have hswap : ∀ j : ℕ, (IsConj ((β ^ (2 * j)) t) t) ∧ IsConj ((β ^ (2 * j + 1)) t) t₂ := by
      intro j
      induction j with
      | zero => exact ⟨by rw [mul_zero, pow_zero]; exact IsConj.refl t,
          by rw [mul_zero, zero_add, pow_one]; exact h1⟩
      | succ j ih =>
        have e1 : β ^ (2 * (j + 1)) = β * β ^ (2 * j + 1) := by
          rw [← pow_succ']; ring_nf
        have e2 : β ^ (2 * (j + 1) + 1) = β * β ^ (2 * (j + 1)) := by
          rw [← pow_succ']
        have hA : IsConj ((β ^ (2 * (j + 1))) t) t := by
          rw [e1, MulAut.mul_apply]
          exact (isConj_map_mulAut β ih.2).trans h2
        refine ⟨hA, ?_⟩
        rw [e2, MulAut.mul_apply]
        exact (isConj_map_mulAut β hA).trans h1
    obtain ⟨j, hj⟩ : ∃ j, m = 2 * j + 1 := by
      have : m % 2 = 1 := by omega
      exact ⟨m / 2, by omega⟩
    have := (hswap j).2
    rw [← hj] at this
    exact hnt ((isConj_of_mem_innerAut hβm t).symm.trans this)
  obtain ⟨g, hg⟩ := isConj_iff.1 hβt.symm
  obtain ⟨k, hk⟩ := pow_mem_innerAut_of_centralizers (α := β) ⟨g, hg.symm⟩ hH hH₁ ht₁ hgen hC
  refine ⟨a + k, ?_⟩
  rw [pow_add, pow_mul]
  exact hk

theorem eq_top_of_outTwo [Finite G] (hout : ∀ α : MulAut G, ∃ k : ℕ, α ^ (2 ^ k) ∈ innerAut G)
    {R : Subgroup (MulAut G)} (hR : innerAut G ≤ R)
    (hNR : Subgroup.normalizer (R : Set (MulAut G)) = R) : R = ⊤ := by
  have := finite_mulAut (G := G)
  have hN := innerAut_normal (G := G)
  have hp : IsPGroup 2 (MulAut G ⧸ innerAut G) := by
    intro q
    obtain ⟨α, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, hk⟩ := hout α
    exact ⟨k, by rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact hk⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnil := hp.isNilpotent
  have hcond := (normalizerCondition_iff_only_full_group_self_normalizing).1
    (Group.normalizerCondition_of_isNilpotent (G := MulAut G ⧸ innerAut G))
  set R' := R.map (QuotientGroup.mk' (innerAut G))
  have hR' : Subgroup.normalizer (R' : Set (MulAut G ⧸ innerAut G)) = R' := by
    apply le_antisymm _ Subgroup.le_normalizer
    intro q hq
    obtain ⟨β, rfl⟩ := QuotientGroup.mk_surjective q
    have hβ : β ∈ Subgroup.normalizer (R : Set (MulAut G)) := by
      rw [Subgroup.mem_normalizer_iff]
      intro r
      constructor
      · intro hr
        have h1 : (QuotientGroup.mk (β * r * β⁻¹) : MulAut G ⧸ innerAut G) ∈ R' := by
          rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
          exact (Subgroup.mem_normalizer_iff.1 hq _).1 ⟨r, hr, rfl⟩
        obtain ⟨r', hr', e⟩ := h1
        have : (r')⁻¹ * (β * r * β⁻¹) ∈ innerAut G := QuotientGroup.eq.1 e
        have := R.mul_mem hr' (hR this)
        simpa using this
      · intro hr
        have h1 : (QuotientGroup.mk r : MulAut G ⧸ innerAut G) ∈ R' := by
          have h2 := (Subgroup.mem_normalizer_iff.1 hq (QuotientGroup.mk r)).2
          apply h2
          rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
          exact ⟨_, hr, rfl⟩
        obtain ⟨r', hr', e⟩ := h1
        have : (r')⁻¹ * r ∈ innerAut G := QuotientGroup.eq.1 e
        have := R.mul_mem hr' (hR this)
        simpa using this
    rw [hNR] at hβ
    exact ⟨β, hβ, rfl⟩
  have htop := hcond R' hR'
  rw [eq_top_iff]
  intro β _
  have : (QuotientGroup.mk β : MulAut G ⧸ innerAut G) ∈ R' := by rw [htop]; trivial
  obtain ⟨r, hr, e⟩ := this
  have : r⁻¹ * β ∈ innerAut G := QuotientGroup.eq.1 e
  have := R.mul_mem hr (hR this)
  simpa using this

end CFSG.Fischer
