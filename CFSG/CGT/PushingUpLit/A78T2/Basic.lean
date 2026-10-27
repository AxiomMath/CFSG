module

public import CFSG.CGT.PushingUpLit.A78T2.Data
public import CFSG.CGT.PushingUpLit.A78Sp4.F410

public section

namespace CFSG.CGT.PushingUpLit.A78T2

open CFSG.Assembly CFSG.ABGLocalTools
open CFSG.CGT.PushingUpLit.A78Sp4 (cj ElemAb2 mul_mem_cj mul_mem_cj_iff mem_cj_iff
  mem_normalizer_of_cj cj_eq_of_normalizes)
open scoped commutatorElement

variable {G : Type} [Group G]

theorem mem_normalizer_of_conj_mem [Finite G] {H : Subgroup G} {x : G}
    (h : ∀ y ∈ H, x * y * x⁻¹ ∈ H) : x ∈ Subgroup.normalizer (H : Set G) := by
  have hle : cj x H ≤ H := by
    intro y hy
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hy
    exact h w hw
  have heq : cj x H = H := Subgroup.eq_of_le_of_card_ge hle
    (by rw [CFSG.CGT.PushingUpLit.A78Sp4.card_cj])
  exact mem_normalizer_of_cj heq

section Heis

variable {J V V₂ Z : Subgroup G} {F : Type} [Field F] {a b c : G → F}

theorem T2Heis.a_one (h : T2Heis G J V V₂ Z F a b c) : a 1 = 0 := by
  have := h.add_a 1 J.one_mem 1 J.one_mem
  simpa using this

theorem T2Heis.b_one (h : T2Heis G J V V₂ Z F a b c) : b 1 = 0 := by
  have := h.add_b 1 J.one_mem 1 J.one_mem
  simpa using this

theorem T2Heis.c_one (h : T2Heis G J V V₂ Z F a b c) : c 1 = 0 := by
  have := h.add_c 1 Z.one_mem 1 Z.one_mem
  simpa using this

theorem T2Heis.a_inv (h : T2Heis G J V V₂ Z F a b c) {x : G} (hx : x ∈ J) : a x⁻¹ = -a x := by
  have := h.add_a x hx x⁻¹ (J.inv_mem hx)
  rw [mul_inv_cancel, h.a_one] at this
  linear_combination -this

theorem T2Heis.b_inv (h : T2Heis G J V V₂ Z F a b c) {x : G} (hx : x ∈ J) : b x⁻¹ = -b x := by
  have := h.add_b x hx x⁻¹ (J.inv_mem hx)
  rw [mul_inv_cancel, h.b_one] at this
  linear_combination -this

theorem T2Heis.mem_Z (h : T2Heis G J V V₂ Z F a b c) (hinf : V ⊓ V₂ = Z) {x : G} (hx : x ∈ J)
    (ha : a x = 0) (hb : b x = 0) : x ∈ Z := by
  rw [← hinf]
  exact ⟨(h.ker_b x hx).2 hb, (h.ker_a x hx).2 ha⟩

theorem T2Heis.a_Z (h : T2Heis G J V V₂ Z F a b c) (hinf : V ⊓ V₂ = Z) (hZJ : Z ≤ J) {z : G}
    (hz : z ∈ Z) : a z = 0 := by
  rw [← hinf] at hz
  exact (h.ker_a z (hZJ (hinf ▸ hz))).1 hz.2

theorem T2Heis.b_Z (h : T2Heis G J V V₂ Z F a b c) (hinf : V ⊓ V₂ = Z) (hZJ : Z ≤ J) {z : G}
    (hz : z ∈ Z) : b z = 0 := by
  rw [← hinf] at hz
  exact (h.ker_b z (hZJ (hinf ▸ hz))).1 hz.1

theorem T2Heis.central (h : T2Heis G J V V₂ Z F a b c) (hinf : V ⊓ V₂ = Z) (hZJ : Z ≤ J)
    (hcomm : ∀ x ∈ J, ∀ y ∈ J, ⁅x, y⁆ ∈ Z) {z : G} (hz : z ∈ Z) {x : G} (hx : x ∈ J) :
    z * x = x * z := by
  have h1 := h.comm z (hZJ hz) x hx
  rw [h.a_Z hinf hZJ hz, h.b_Z hinf hZJ hz, zero_mul, mul_zero, add_zero] at h1
  have h2 : ⁅z, x⁆ = 1 := h.inj_c _ (hcomm z (hZJ hz) x hx) 1 Z.one_mem (by rw [h1, h.c_one])
  exact commutatorElement_eq_one_iff_mul_comm.1 h2

theorem T2Heis.inv_mul_mem_Z (h : T2Heis G J V V₂ Z F a b c) (hinf : V ⊓ V₂ = Z) {x y : G}
    (hx : x ∈ J) (hy : y ∈ J) (ha : a x = a y) (hb : b x = b y) : x⁻¹ * y ∈ Z := by
  refine h.mem_Z hinf (J.mul_mem (J.inv_mem hx) hy) ?_ ?_
  · rw [h.add_a _ (J.inv_mem hx) _ hy, h.a_inv hx, ha, neg_add_cancel]
  · rw [h.add_b _ (J.inv_mem hx) _ hy, h.b_inv hx, hb, neg_add_cancel]

end Heis

variable {L L₂ V V₂ Z J T S M M₂ : Subgroup G} {e : ℕ}

theorem T2Base.Z_le_V (h : T2Base G V V₂ Z J T S M M₂ e) : Z ≤ V := h.inf ▸ inf_le_left
theorem T2Base.Z_le_V₂ (h : T2Base G V V₂ Z J T S M M₂ e) : Z ≤ V₂ := h.inf ▸ inf_le_right
theorem T2Base.V_le_J (h : T2Base G V V₂ Z J T S M M₂ e) : V ≤ J := h.sup ▸ le_sup_left
theorem T2Base.V₂_le_J (h : T2Base G V V₂ Z J T S M M₂ e) : V₂ ≤ J := h.sup ▸ le_sup_right
theorem T2Base.Z_le_J (h : T2Base G V V₂ Z J T S M M₂ e) : Z ≤ J := h.Z_le_V.trans h.V_le_J
theorem T2Base.J_le_S (h : T2Base G V V₂ Z J T S M M₂ e) : J ≤ S := h.J_le.trans h.T_le

theorem T2Base.conj_J (h : T2Base G V V₂ Z J T S M M₂ e) {s : G} (hs : s ∈ S) {x : G}
    (hx : x ∈ J) : s * x * s⁻¹ ∈ J := by
  have := h.normal_J.conj_mem ⟨x, h.J_le_S hx⟩ (Subgroup.mem_subgroupOf.2 hx) ⟨s, hs⟩
  exact Subgroup.mem_subgroupOf.1 this

theorem T2Base.conj_Z (h : T2Base G V V₂ Z J T S M M₂ e) {s : G} (hs : s ∈ S) {x : G}
    (hx : x ∈ Z) : s * x * s⁻¹ ∈ Z := by
  rw [← h.inf] at hx ⊢
  by_cases hsT : s ∈ T
  · obtain ⟨h1, h2⟩ := h.T_norm s hsT
    refine ⟨?_, ?_⟩
    · rw [← h1]; exact mul_mem_cj s hx.1
    · rw [← h2]; exact mul_mem_cj s hx.2
  · obtain ⟨h1, h2⟩ := h.swap s hs hsT
    refine ⟨?_, ?_⟩
    · rw [← h2]; exact mul_mem_cj s hx.2
    · rw [← h1]; exact mul_mem_cj s hx.1

theorem T2Base.S_le_normalizer_Z [Finite G] (h : T2Base G V V₂ Z J T S M M₂ e) :
    S ≤ Subgroup.normalizer (Z : Set G) := fun _ hs =>
  mem_normalizer_of_conj_mem fun _ hx => h.conj_Z hs hx

theorem T2Base.isPGroup_S [Finite G] (h : T2Base G V V₂ Z J T S M M₂ e) : IsPGroup 2 S := by
  obtain ⟨Q, hQ⟩ := h.sylow
  have : IsPGroup 2 ((Q : Subgroup (⊤ : Subgroup G)).map (⊤ : Subgroup G).subtype) :=
    Q.isPGroup'.map _
  rwa [hQ] at this

theorem T2Base.one_lt_card_Z (h : T2Base G V V₂ Z J T S M M₂ e) : 1 < Nat.card Z := by
  rw [h.card_Z]
  exact Nat.one_lt_two_pow (by have := h.two_le; omega)

theorem T2Base.exists_ne_one_Z (h : T2Base G V V₂ Z J T S M M₂ e) : ∃ z ∈ Z, z ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have : Z = ⊥ := (Subgroup.eq_bot_iff_forall Z).2 hcon
  have h1 := h.one_lt_card_Z
  rw [this, Subgroup.card_bot] at h1
  exact lt_irrefl _ h1

theorem T2Base.not_V_le_Z [Finite G] (h : T2Base G V V₂ Z J T S M M₂ e) : ¬ V ≤ Z := by
  intro hle
  have := Subgroup.card_le_of_le hle
  rw [h.card_V, h.card_Z] at this
  have h2 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 this
  have := h.two_le
  omega

theorem T2Base.not_V₂_le_Z [Finite G] (h : T2Base G V V₂ Z J T S M M₂ e) : ¬ V₂ ≤ Z := by
  intro hle
  have := Subgroup.card_le_of_le hle
  rw [h.card_V₂, h.card_Z] at this
  have h2 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 this
  have := h.two_le
  omega

theorem T2Side.conj_mem_L (hs : T2Side G L V Z J T M e) {m x : G} (hm : m ∈ M) (hx : x ∈ L) :
    m * x * m⁻¹ ∈ L := by
  have h2 := hs.normal_L.conj_mem ⟨x, hs.L_le_M hx⟩ (Subgroup.mem_subgroupOf.2 hx) ⟨m, hm⟩
  exact Subgroup.mem_subgroupOf.1 h2

theorem T2Side.mem_normalizer_J [Finite G] (hs : T2Side G L V Z J T M e) {z₀ : G} (hz₀ : z₀ ∈ Z)
    (hz₀1 : z₀ ≠ 1) {m : G} (hm : m ∈ M) (hmZ : m ∈ Subgroup.normalizer (Z : Set G)) :
    m ∈ Subgroup.normalizer (J : Set G) := by
  refine mem_normalizer_of_conj_mem fun x hx => ?_
  have hz' : m * z₀ * m⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.1 hmZ z₀).1 hz₀
  have hz'1 : m * z₀ * m⁻¹ ≠ 1 := fun h1 => hz₀1 (by
    have : z₀ = m⁻¹ * (m * z₀ * m⁻¹) * m := by group
    rw [this, h1]; group)
  have hxJ : x ∈ L ⊓ Subgroup.centralizer ({z₀} : Set G) := by rw [hs.cent_L z₀ hz₀ hz₀1]; exact hx
  rw [← hs.cent_L _ hz' hz'1]
  have h1 : x * z₀ = z₀ * x := Subgroup.mem_centralizer_singleton_iff.1 hxJ.2
  refine ⟨hs.conj_mem_L hm hxJ.1, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
  calc m * x * m⁻¹ * (m * z₀ * m⁻¹) = m * (x * z₀) * m⁻¹ := by group
    _ = m * (z₀ * x) * m⁻¹ := by rw [h1]
    _ = m * z₀ * m⁻¹ * (m * x * m⁻¹) := by group

theorem exists_pow_four_ne {K : Type*} [Field K] [Finite K] (hK : 4 < Nat.card K) :
    ∃ τ : K, τ ^ 4 ≠ τ := by
  classical
  have hp0 : (Polynomial.X ^ 4 - Polynomial.X : Polynomial K) ≠ 0 :=
    FiniteField.X_pow_card_sub_X_ne_zero K (by norm_num)
  have hdeg : (Polynomial.X ^ 4 - Polynomial.X : Polynomial K).natDegree = 4 :=
    FiniteField.X_pow_card_sub_X_natDegree_eq K (by norm_num)
  obtain ⟨τ, hτ⟩ := CFSG.CGT.PushingUpLit.A78Sp4.exists_avoid
    (Polynomial.X ^ 4 - Polynomial.X : Polynomial K).roots.toFinset (by
      calc _ ≤ (Polynomial.X ^ 4 - Polynomial.X : Polynomial K).roots.card :=
            Multiset.toFinset_card_le _
        _ ≤ (Polynomial.X ^ 4 - Polynomial.X : Polynomial K).natDegree :=
            Polynomial.card_roots' _
        _ < Nat.card K := by rw [hdeg]; exact hK)
  refine ⟨τ, fun h4 => hτ ?_⟩
  rw [Multiset.mem_toFinset, Polynomial.mem_roots hp0]
  simp [h4]

theorem sum_inv_ne_zero {K : Type*} [Field K] [CharP K 2] {τ : K} (hτ : τ ^ 4 ≠ τ) :
    τ ≠ 0 ∧ 1 + τ ≠ 0 ∧ 1 + τ⁻¹ + (1 + τ)⁻¹ ≠ 0 := by
  have h2 : (2 : K) = 0 := CFSG.CGT.PushingUpLit.A78Sp4.charTwo_two_eq_zero
  have hτ0 : τ ≠ 0 := by rintro rfl; simp at hτ
  have hτ1 : 1 + τ ≠ 0 := by
    intro h0
    apply hτ
    have : τ = 1 := by linear_combination h0 - h2
    rw [this]; ring
  refine ⟨hτ0, hτ1, fun h0 => hτ ?_⟩
  have key : (1 + τ⁻¹ + (1 + τ)⁻¹) * (τ * (1 + τ)) = τ ^ 2 + τ + 1 + 2 * τ := by
    field_simp
    ring
  rw [h0, zero_mul] at key
  have hq : τ ^ 2 + τ + 1 = 0 := by linear_combination -key - τ * h2
  linear_combination (τ ^ 2 + τ) * hq - (τ + τ ^ 2 + τ ^ 3) * h2

section Torus

variable [Finite G] {a b c : G → GaloisField 2 e}

theorem T2Loc.torus_cases (h : T2Loc G L L₂ V V₂ Z J T S M M₂ e)
    (hH : T2Heis G J V V₂ Z (GaloisField 2 e) a b c)
    (hT : T2Tori G J Z L L₂ (GaloisField 2 e) a b c) {W : Subgroup G} (hZW : Z ≤ W)
    (hWJ : W ≤ J)
    (hinv : ∀ x : G, (∀ j ∈ J, x * j * x⁻¹ ∈ J) → (∀ z ∈ Z, x * z * x⁻¹ ∈ Z) →
      ∀ w ∈ W, x * w * x⁻¹ ∈ W) :
    W = Z ∨ W = V ∨ W = V₂ ∨ W = J := by
  have hinf := h.base.inf
  have h2 : (2 : GaloisField 2 e) = 0 := CFSG.CGT.PushingUpLit.A78Sp4.charTwo_two_eq_zero
  have htor : ∀ t : GaloisField 2 e, t ≠ 0 → ∀ w ∈ W,
      ∃ w' ∈ W, a w' = t⁻¹ * a w ∧ b w' = t ^ 2 * b w := by
    intro t ht w hw
    obtain ⟨x, -, hxJ, hxab, hxZ⟩ := hT.torus₁ t ht
    exact ⟨x * w * x⁻¹, hinv x hxJ (fun z hz => (hxZ z hz).1) w hw, (hxab w (hWJ hw)).1,
      (hxab w (hWJ hw)).2⟩
  have hcrit : ∀ j ∈ J, ∀ w ∈ W, a w = a j → b w = b j → j ∈ W := by
    intro j hj w hw ha hb
    have := hZW (hH.inv_mul_mem_Z hinf (hWJ hw) hj ha hb)
    have e1 : j = w * (w⁻¹ * j) := by group
    rw [e1]
    exact W.mul_mem hw this
  have hV : (∃ w ∈ W, a w ≠ 0 ∧ b w = 0) → V ≤ W := by
    rintro ⟨w₀, hw₀, ha₀, hb₀⟩ v hv
    have hvJ := h.base.V_le_J hv
    have hbv : b v = 0 := (hH.ker_b v hvJ).1 hv
    by_cases hav : a v = 0
    · exact hZW (hH.mem_Z hinf hvJ hav hbv)
    · obtain ⟨w', hw', ha', hb'⟩ := htor (a w₀ / a v) (div_ne_zero ha₀ hav) w₀ hw₀
      refine hcrit v hvJ w' hw' ?_ ?_
      · rw [ha']; field_simp
      · rw [hb', hb₀, hbv, mul_zero]
  have hV₂ : (∃ w ∈ W, a w = 0 ∧ b w ≠ 0) → V₂ ≤ W := by
    rintro ⟨w₀, hw₀, ha₀, hb₀⟩ v hv
    have hvJ := h.base.V₂_le_J hv
    have hav : a v = 0 := (hH.ker_a v hvJ).1 hv
    by_cases hbv : b v = 0
    · exact hZW (hH.mem_Z hinf hvJ hav hbv)
    · obtain ⟨t, ht⟩ := CFSG.CGT.PushingUpLit.A78Sp4.exists_sq_eq (b v / b w₀)
      have ht0 : t ≠ 0 := by
        rintro rfl
        rw [zero_pow two_ne_zero] at ht
        exact (div_ne_zero hbv hb₀) ht.symm
      obtain ⟨w', hw', ha', hb'⟩ := htor t ht0 w₀ hw₀
      refine hcrit v hvJ w' hw' ?_ ?_
      · rw [ha', ha₀, hav, mul_zero]
      · rw [hb', ht]; field_simp
  have hboth : (∃ w ∈ W, a w ≠ 0 ∧ b w ≠ 0) → J ≤ W := by
    rintro ⟨w, hw, haw, hbw⟩
    have hcard : 4 < Nat.card (GaloisField 2 e) := by
      rw [GaloisField.card 2 e (by have := h.three_le; omega)]
      calc 4 < 2 ^ 3 := by norm_num
        _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) h.three_le
    obtain ⟨τ, hτ⟩ := exists_pow_four_ne hcard
    obtain ⟨hτ0, hτ1, hsum⟩ := sum_inv_ne_zero hτ
    obtain ⟨w₁, hw₁, ha₁, hb₁⟩ := htor τ hτ0 w hw
    obtain ⟨w₂, hw₂, ha₂, hb₂⟩ := htor (1 + τ) hτ1 w hw
    have hwJ := hWJ hw
    have hw₁J := hWJ hw₁
    have hw₂J := hWJ hw₂
    have hm : w * w₁ * w₂ ∈ W := W.mul_mem (W.mul_mem hw hw₁) hw₂
    have hmJ : w * w₁ ∈ J := J.mul_mem hwJ hw₁J
    have ham : a (w * w₁ * w₂) = a w * (1 + τ⁻¹ + (1 + τ)⁻¹) := by
      rw [hH.add_a _ hmJ _ hw₂J, hH.add_a _ hwJ _ hw₁J, ha₁, ha₂]
      ring
    have hbm : b (w * w₁ * w₂) = 0 := by
      rw [hH.add_b _ hmJ _ hw₂J, hH.add_b _ hwJ _ hw₁J, hb₁, hb₂]
      linear_combination (b w * (1 + τ + τ ^ 2)) * h2
    have hVW := hV ⟨_, hm, by rw [ham]; exact mul_ne_zero haw hsum, hbm⟩
    obtain ⟨v, hvJ, hav, hbv⟩ := hH.surj_ab (a w) 0
    have hv : v ∈ V := (hH.ker_b v hvJ).2 hbv
    have hvw : v⁻¹ * w ∈ W := W.mul_mem (W.inv_mem (hVW hv)) hw
    have ha3 : a (v⁻¹ * w) = 0 := by
      rw [hH.add_a _ (J.inv_mem hvJ) _ hwJ, hH.a_inv hvJ, hav, neg_add_cancel]
    have hb3 : b (v⁻¹ * w) ≠ 0 := by
      rw [hH.add_b _ (J.inv_mem hvJ) _ hwJ, hH.b_inv hvJ, hbv, neg_zero, zero_add]
      exact hbw
    have hV₂W := hV₂ ⟨_, hvw, ha3, hb3⟩
    rw [← h.base.sup]
    exact sup_le hVW hV₂W
  by_cases h1 : ∃ w ∈ W, a w ≠ 0 ∧ b w ≠ 0
  · exact Or.inr (Or.inr (Or.inr (le_antisymm hWJ (hboth h1))))
  push Not at h1
  by_cases h3 : ∃ w ∈ W, a w ≠ 0
  · obtain ⟨w₁, hw₁, ha₁⟩ := h3
    have hb₁ := h1 w₁ hw₁ ha₁
    have hb0 : ∀ w ∈ W, b w = 0 := by
      intro w hw
      by_contra hbw
      have haw : a w = 0 := by
        by_contra haw'
        exact hbw (h1 w hw haw')
      have hm : w₁ * w ∈ W := W.mul_mem hw₁ hw
      have := h1 _ hm (by rw [hH.add_a _ (hWJ hw₁) _ (hWJ hw), haw, add_zero]; exact ha₁)
      rw [hH.add_b _ (hWJ hw₁) _ (hWJ hw), hb₁, zero_add] at this
      exact hbw this
    refine Or.inr (Or.inl (le_antisymm (fun w hw => (hH.ker_b w (hWJ hw)).2 (hb0 w hw))
      (hV ⟨w₁, hw₁, ha₁, hb₁⟩)))
  · push Not at h3
    by_cases h4 : ∃ w ∈ W, b w ≠ 0
    · obtain ⟨w₂, hw₂, hb₂⟩ := h4
      refine Or.inr (Or.inr (Or.inl (le_antisymm (fun w hw => (hH.ker_a w (hWJ hw)).2 (h3 w hw))
        (hV₂ ⟨w₂, hw₂, h3 w₂ hw₂, hb₂⟩))))
    · push Not at h4
      exact Or.inl (le_antisymm (fun w hw => hH.mem_Z hinf (hWJ hw) (h3 w hw) (h4 w hw)) hZW)

end Torus

end CFSG.CGT.PushingUpLit.A78T2
