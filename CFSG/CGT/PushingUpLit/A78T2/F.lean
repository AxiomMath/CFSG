module

public import CFSG.CGT.PushingUpLit.A78T2.M

public section

namespace CFSG.CGT.PushingUpLit.A78T2

open CFSG.Assembly CFSG.ABGLocalTools
open CFSG.CGT.PushingUpLit.A78Sp4 (cj ElemAb2 mul_mem_cj mem_normalizer_of_cj elemAb2_cj card_cj
  cj_mono mem_cj_iff cj_cj exists_conj_le_of_isSylowOf exists_isSylowOf_ge
  exists_eq_cj_of_isSylowOf isSylowOf_cj cj_eq_of_normalizes exists_fully_centralized
  card_le_card_centralizer_sq exists_fixed_ne_one cj_centralizer_singleton)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L L₂ V V₂ Z J T S M M₂ : Subgroup G} {e : ℕ}

theorem T2Loc.inf_V_eq_bot (h : T2Loc G L L₂ V V₂ Z J T S M M₂ e) {f : G} (hfT : f ∈ T)
    (hfJ : f ∉ J) (hf2 : f * f = 1) {Q : Subgroup G} (hQp : IsPGroup 2 Q)
    (hQn : ∀ c ∈ Subgroup.centralizer ({f} : Set G), ∀ q ∈ Q, c * q * c⁻¹ ∈ Q) :
    ∀ x ∈ Q, x ∈ V → x ∈ Subgroup.centralizer ({f} : Set G) → x = 1 := by
  set C := Subgroup.centralizer ({f} : Set G) with hC
  have hc₁ := h.field.cent_L f hfT hfJ hf2
  have hc₂ := h.field.cent_L₂ f hfT hfJ hf2
  have hnorm : ((Q ⊓ (L₂ ⊓ C)).subgroupOf (L₂ ⊓ C)).Normal := by
    refine ⟨fun n hn k => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    refine ⟨?_, (L₂ ⊓ C).mul_mem ((L₂ ⊓ C).mul_mem k.2 n.2) ((L₂ ⊓ C).inv_mem k.2)⟩
    exact hQn k k.2.2 n hn.1
  have hP₂ := hc₂.O2 (Q ⊓ (L₂ ⊓ C)) inf_le_right (hQp.to_le inf_le_left) hnorm
  have hinv : ∀ k ∈ L ⊓ C, cj k (Q ⊓ (V ⊓ C)) = Q ⊓ (V ⊓ C) := by
    intro k hk
    have hkV : k ∈ Subgroup.normalizer (V : Set G) := by
      rw [← h.side₁.M_eq]; exact h.side₁.L_le_M hk.1
    have hone : ∀ k' ∈ L ⊓ C, ∀ x ∈ Q ⊓ (V ⊓ C), k' * x * k'⁻¹ ∈ Q ⊓ (V ⊓ C) := by
      intro k' hk' x hx
      have hk'V : k' ∈ Subgroup.normalizer (V : Set G) := by
        rw [← h.side₁.M_eq]; exact h.side₁.L_le_M hk'.1
      exact ⟨hQn k' hk'.2 x hx.1, (Subgroup.mem_normalizer_iff.1 hk'V x).1 hx.2.1,
        C.mul_mem (C.mul_mem hk'.2 hx.2.2) (C.inv_mem hk'.2)⟩
    have _ := hkV
    exact cj_eq_of_normalizes (hone k hk) fun x hx => by
      simpa using hone k⁻¹ ((L ⊓ C).inv_mem hk) x hx
  rcases hc₁.irred (Q ⊓ (V ⊓ C)) inf_le_right hinv with hbot | htop
  · intro x hxQ hxV hxC
    have : x ∈ Q ⊓ (V ⊓ C) := ⟨hxQ, hxV, hxC⟩
    rw [hbot] at this
    exact Subgroup.mem_bot.1 this
  · exfalso
    have hle : V ⊓ C ≤ Z ⊓ C := by
      intro x hx
      have hxQ : x ∈ Q ⊓ (V ⊓ C) := by rw [htop]; exact hx
      have hxV₂ : x ∈ V₂ := hP₂ ⟨hxQ.1, h.side₂.J_le_L (h.base.V_le_J hx.1), hx.2⟩
      rw [← h.base.inf]
      exact ⟨⟨hx.1, hxV₂⟩, hx.2⟩
    have h1 := Subgroup.card_le_of_le hle
    have h2 : 2 ^ e ≤ Nat.card ↥(V ⊓ C) := hc₁.card_CV
    have h3 : Nat.card ↥(Z ⊓ C) < 2 ^ e := hc₁.card_CZ
    omega

theorem T2Loc.no_fixed_point (h : T2Loc G L L₂ V V₂ Z J T S M M₂ e) {f : G} (hfT : f ∈ T)
    (hfJ : f ∉ J) (hf2 : f * f = 1) {Q : Subgroup G} (hQp : IsPGroup 2 Q)
    (hQn : ∀ c ∈ Subgroup.centralizer ({f} : Set G), ∀ q ∈ Q, c * q * c⁻¹ ∈ Q) :
    ∀ x ∈ Q, x ∈ J → x ∈ Subgroup.centralizer ({f} : Set G) → x = 1 := by
  set C := Subgroup.centralizer ({f} : Set G) with hC
  have hc₁ := h.field.cent_L f hfT hfJ hf2
  have hnorm : ((Q ⊓ (L ⊓ C)).subgroupOf (L ⊓ C)).Normal := by
    refine ⟨fun n hn k => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    refine ⟨?_, (L ⊓ C).mul_mem ((L ⊓ C).mul_mem k.2 n.2) ((L ⊓ C).inv_mem k.2)⟩
    exact hQn k k.2.2 n hn.1
  have hP₁ := hc₁.O2 (Q ⊓ (L ⊓ C)) inf_le_right (hQp.to_le inf_le_left) hnorm
  intro x hxQ hxJ hxC
  exact h.inf_V_eq_bot hfT hfJ hf2 hQp hQn x hxQ
    (hP₁ ⟨hxQ, h.side₁.J_le_L hxJ, hxC⟩) hxC

omit [Finite G] in
theorem card_le_two_mul_of_coset [Finite G] {A B : Subgroup G} (_hBA : B ≤ A)
    (hcos : ∀ x ∈ A, ∀ y ∈ A, x ∉ B → y ∉ B → x⁻¹ * y ∈ B) : Nat.card A ≤ 2 * Nat.card B := by
  classical
  by_cases hAB : A ≤ B
  · have := Subgroup.card_le_of_le hAB
    omega
  obtain ⟨x₀, hx₀A, hx₀B⟩ := Set.not_subset.1 hAB
  let f : A → B × Bool := fun y =>
    if hy : (y : G) ∈ B then (⟨y, hy⟩, false)
    else (⟨x₀⁻¹ * y, hcos x₀ hx₀A y y.2 hx₀B hy⟩, true)
  have hinj : Function.Injective f := by
    intro y y' hyy
    simp only [f] at hyy
    by_cases hy : (y : G) ∈ B <;> by_cases hy' : (y' : G) ∈ B
    · simp only [hy, hy', ↓reduceDIte] at hyy
      have h3 := congrArg (fun p : B => (p : G)) (Prod.mk.inj hyy).1
      exact Subtype.ext h3
    · simp only [hy, hy', ↓reduceDIte] at hyy
      exact absurd (Prod.mk.inj hyy).2 (by decide)
    · simp only [hy, hy', ↓reduceDIte] at hyy
      exact absurd (Prod.mk.inj hyy).2 (by decide)
    · simp only [hy, hy', ↓reduceDIte] at hyy
      have h3 := congrArg (fun p : B => (p : G)) (Prod.mk.inj hyy).1
      exact Subtype.ext (mul_left_cancel h3)
  have := Nat.card_le_card_of_injective f hinj
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at this
  linarith

omit [Finite G] in
theorem exists_elemAb2_ext [Finite G] {H : Subgroup G} (hH : ElemAb2 H) {a : G} (ha : a * a = 1)
    (hcomm : ∀ h ∈ H, a * h = h * a) (haH : a ∉ H) :
    ∃ W : Subgroup G, ElemAb2 W ∧ H ≤ W ∧ a ∈ W ∧ Nat.card W = 2 * Nat.card H := by
  have hinv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hmul : ∀ v ∈ H, ∀ w ∈ H, v * a * (w * a) = v * w := by
    intro v _ w hw
    calc v * a * (w * a) = v * (a * w) * a := by group
      _ = v * (w * a) * a := by rw [hcomm w hw]
      _ = v * w * (a * a) := by group
      _ = v * w := by rw [ha, mul_one]
  have hmulR : ∀ v ∈ H, ∀ y ∈ H, v * a * y = v * y * a := by
    intro v _ y hy
    rw [mul_assoc, hcomm y hy, ← mul_assoc]
  let W : Subgroup G :=
    { carrier := {x | x ∈ H ∨ ∃ v ∈ H, x = v * a}
      mul_mem' := by
        rintro x y (hx | ⟨v, hv, rfl⟩) (hy | ⟨w, hw, rfl⟩)
        · exact Or.inl (H.mul_mem hx hy)
        · exact Or.inr ⟨x * w, H.mul_mem hx hw, by rw [mul_assoc]⟩
        · exact Or.inr ⟨v * y, H.mul_mem hv hy, hmulR v hv y hy⟩
        · exact Or.inl (by rw [hmul v hv w hw]; exact H.mul_mem hv hw)
      one_mem' := Or.inl H.one_mem
      inv_mem' := by
        rintro x (hx | ⟨v, hv, rfl⟩)
        · exact Or.inl (H.inv_mem hx)
        · refine Or.inr ⟨v⁻¹, H.inv_mem hv, ?_⟩
          rw [mul_inv_rev, hinv]
          exact hcomm v⁻¹ (H.inv_mem hv) }
  have hW : ElemAb2 W := by
    rintro x (hx | ⟨v, hv, rfl⟩) y (hy | ⟨w, hw, rfl⟩)
    · exact hH x hx y hy
    · refine ⟨?_, (hH x hx x hx).2⟩
      calc x * (w * a) = x * w * a := (mul_assoc _ _ _).symm
        _ = w * x * a := by rw [(hH x hx w hw).1]
        _ = w * a * x := (hmulR w hw x hx).symm
    · refine ⟨?_, by rw [hmul v hv v hv]; exact (hH v hv v hv).2⟩
      calc v * a * y = v * y * a := hmulR v hv y hy
        _ = y * v * a := by rw [(hH v hv y hy).1]
        _ = y * (v * a) := mul_assoc _ _ _
    · refine ⟨?_, by rw [hmul v hv v hv]; exact (hH v hv v hv).2⟩
      rw [hmul v hv w hw, hmul w hw v hv]
      exact (hH v hv w hw).1
  have hle : H ≤ W := fun x hx => Or.inl hx
  have haW : a ∈ W := Or.inr ⟨1, H.one_mem, by simp⟩
  have hidx : H.relIndex W = 2 := by
    rw [Subgroup.relIndex_eq_two_iff]
    refine ⟨a, haW, ?_⟩
    rintro b (hb | ⟨v, hv, rfl⟩)
    · refine Or.inr ⟨hb, fun hba => haH ?_⟩
      have : a = b⁻¹ * (b * a) := by group
      rw [this]
      exact H.mul_mem (H.inv_mem hb) hba
    · refine Or.inl ⟨?_, fun hva => haH ?_⟩
      · rw [show v * a * a = v by rw [mul_assoc, ha, mul_one]]
        exact hv
      · have : a = v⁻¹ * (v * a) := by group
        rw [this]
        exact H.mul_mem (H.inv_mem hv) hva
  have hcard := Subgroup.relIndex_mul_card (H := H) (K := W)
  rw [hidx, inf_eq_left.2 hle] at hcard
  exact ⟨W, hW, hle, haW, hcard.symm⟩

theorem T2Loc.inv_mul_mem_J (h : T2Loc G L L₂ V V₂ Z J T S M M₂ e) {f : G} (hfT : f ∈ T)
    (hfJ : f ∉ J) (hf2 : f * f = 1) {x y : G} (hxT : x ∈ T) (hxJ : x ∉ J) (hx2 : x * x = 1)
    (hyT : y ∈ T) (hyJ : y ∉ J) (hy2 : y * y = 1) : x⁻¹ * y ∈ J := by
  obtain ⟨j₁, hj₁, hx⟩ := h.field.inv_conj f hfT hfJ hf2 x hxT hxJ hx2
  obtain ⟨j₂, hj₂, hy⟩ := h.field.inv_conj f hfT hfJ hf2 y hyT hyJ hy2
  have hfS := h.base.T_le hfT
  have h1 : f⁻¹ * (j₁ * j₂⁻¹) * f⁻¹⁻¹ ∈ J :=
    h.base.conj_J (S.inv_mem hfS) (J.mul_mem hj₁ (J.inv_mem hj₂))
  have e1 : x⁻¹ * y = j₁⁻¹ * (f⁻¹ * (j₁ * j₂⁻¹) * f⁻¹⁻¹) * j₂ := by rw [← hx, ← hy]; group
  rw [e1]
  exact J.mul_mem (J.mul_mem (J.inv_mem hj₁) h1) hj₂

theorem T2Loc.relIndex_le_cent (h : T2Loc G L L₂ V V₂ Z J T S M M₂ e) {f : G} (hfT : f ∈ T)
    (hfJ : f ∉ J) (hf2 : f * f = 1) :
    J.relIndex T ≤ J.relIndex (T ⊓ Subgroup.centralizer ({f} : Set G)) := by
  set K := T ⊓ Subgroup.centralizer ({f} : Set G) with hK
  have hKT : K ≤ T := inf_le_left
  have hJTn : (J.subgroupOf T).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using h.base.conj_J (h.base.T_le g.2) hn⟩
  have hJKn : (J.subgroupOf K).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using h.base.conj_J (h.base.T_le (hKT g.2)) hn⟩
  have hmap : J.subgroupOf K ≤ (J.subgroupOf T).comap (Subgroup.inclusion hKT) := by
    intro x hx
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    exact hx
  let φ := QuotientGroup.map (J.subgroupOf K) (J.subgroupOf T) (Subgroup.inclusion hKT) hmap
  have hsurj : Function.Surjective φ := by
    intro q
    obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective q
    have htT : (t : G) ∈ T := t.2
    have hfS := h.base.T_le hfT
    have h1 : (t : G)⁻¹ * f * t ∈ T := T.mul_mem (T.mul_mem (T.inv_mem htT) hfT) htT
    have h2 : (t : G)⁻¹ * f * t ∉ J := fun hJ => hfJ (by
      have := h.base.conj_J (h.base.T_le htT) hJ
      simpa [mul_assoc] using this)
    have h3 : ((t : G)⁻¹ * f * t) * ((t : G)⁻¹ * f * t) = 1 := by
      calc ((t : G)⁻¹ * f * t) * ((t : G)⁻¹ * f * t) = (t : G)⁻¹ * (f * f) * t := by group
        _ = 1 := by rw [hf2]; group
    obtain ⟨j, hj, hjf⟩ := h.field.inv_conj f hfT hfJ hf2 _ h1 h2 h3
    have hkK : (t : G) * j⁻¹ ∈ K := by
      refine ⟨T.mul_mem htT (h.base.J_le (J.inv_mem hj)),
        Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      have e1 : f = (t : G) * (j⁻¹ * f * j) * (t : G)⁻¹ := by rw [hjf]; group
      calc (t : G) * j⁻¹ * f = (t : G) * (j⁻¹ * f * j) * (t : G)⁻¹ * ((t : G) * j⁻¹) := by group
        _ = f * ((t : G) * j⁻¹) := by rw [← e1]
    refine ⟨QuotientGroup.mk ⟨_, hkK⟩, ?_⟩
    rw [QuotientGroup.map_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have e2 : ((t : G) * j⁻¹)⁻¹ * t = j := by group
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion]
    rw [e2]
    exact hj
  exact Nat.card_le_card_of_surjective _ hsurj

theorem T2Loc.mem_T_of_fully (h : T2Loc G L L₂ V V₂ Z J T S M M₂ e) (hTJ : T ≠ J) {f : G}
    (hfT : f ∈ T) (hfJ : f ∉ J) (hf2 : f * f = 1) {g : G} (hgS : g⁻¹ * f * g ∈ S)
    (hR : IsSylowOf 2 (S ⊓ Subgroup.centralizer ({g⁻¹ * f * g} : Set G))
      (Subgroup.centralizer ({g⁻¹ * f * g} : Set G))) : g⁻¹ * f * g ∈ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set f' := g⁻¹ * f * g with hf'
  have hf'2 : f' * f' = 1 := by
    calc f' * f' = g⁻¹ * (f * f) * g := by rw [hf']; group
      _ = 1 := by rw [hf2]; group
  by_contra hf'T
  have he := h.field.even_e hTJ
  have he3 := h.three_le
  have hJT : J ≤ T := h.base.J_le
  have hconj : ∀ X₀ : Subgroup G, X₀ ≤ Subgroup.centralizer ({f} : Set G) → IsPGroup 2 X₀ →
      ∃ X : Subgroup G, X ≤ S ⊓ Subgroup.centralizer ({f'} : Set G) ∧
        Nat.card X = Nat.card X₀ ∧ ∃ m : G, X = cj m X₀ := by
    intro X₀ hX₀ hX₀p
    have hle : cj g⁻¹ X₀ ≤ Subgroup.centralizer ({f'} : Set G) := by
      have := cj_mono g⁻¹ hX₀
      rw [cj_centralizer_singleton] at this
      rwa [show g⁻¹ * f * g⁻¹⁻¹ = f' by rw [hf']; group] at this
    obtain ⟨c, -, hc⟩ := exists_conj_le_of_isSylowOf hR hle (hX₀p.map _)
    refine ⟨cj c (cj g⁻¹ X₀), hc, by rw [card_cj, card_cj], c * g⁻¹, by rw [cj_cj]⟩
  rcases h.field.types f' hgS hf'T hf'2 with hL₂ | ⟨hinvo, hcard⟩
  ·
    set K := T ⊓ Subgroup.centralizer ({f} : Set G) with hK
    obtain ⟨X, hXle, hXcard, -, -⟩ := hconj K inf_le_right
      (h.base.isPGroup_S.to_le (inf_le_left.trans h.base.T_le))
    have hXR : Nat.card X ≤ Nat.card ↥(S ⊓ Subgroup.centralizer ({f'} : Set G)) :=
      Subgroup.card_le_of_le hXle
    have hR1 := Subgroup.relIndex_mul_card (H := J) (K := S ⊓ Subgroup.centralizer ({f'} : Set G))
    have hR2 : J.relIndex (S ⊓ Subgroup.centralizer ({f'} : Set G)) ≤ J.relIndex S :=
      Subgroup.relIndex_le_of_le_right inf_le_left Subgroup.index_ne_zero_of_finite
    have hR3 : J ⊓ (S ⊓ Subgroup.centralizer ({f'} : Set G)) ≤ Z := by
      intro x hx
      have : x ∈ J ⊓ Subgroup.centralizer ({f'} : Set G) := ⟨hx.1, hx.2.2⟩
      rw [hL₂] at this
      exact this
    have hR4 := Subgroup.card_le_of_le hR3
    rw [h.base.card_Z] at hR4
    have hR5 : J.relIndex S = J.relIndex T * T.relIndex S :=
      (Subgroup.relIndex_mul_relIndex J T S hJT h.base.T_le).symm
    have hR6 : T.relIndex S ≤ 2 := h.base.index
    have hK1 := Subgroup.relIndex_mul_card (H := J) (K := K)
    have hK2 := h.relIndex_le_cent hfT hfJ hf2
    have hK3 : J ⊓ K = J ⊓ Subgroup.centralizer ({f} : Set G) := by
      rw [hK, ← inf_assoc, inf_eq_left.2 hJT]
    have hK4 : 2 ^ (e + e / 2) ≤ Nat.card ↥(J ⊓ K) := by
      rw [hK3]; exact h.field.card_CJf f hfT hfJ hf2
    have hpos : 0 < J.relIndex T := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    have key : J.relIndex T * 2 ^ (e + e / 2) ≤ J.relIndex T * 2 ^ (e + 1) := by
      calc J.relIndex T * 2 ^ (e + e / 2) ≤ J.relIndex K * Nat.card ↥(J ⊓ K) :=
            Nat.mul_le_mul hK2 hK4
        _ = Nat.card K := hK1
        _ = Nat.card X := hXcard.symm
        _ ≤ Nat.card ↥(S ⊓ Subgroup.centralizer ({f'} : Set G)) := hXR
        _ = J.relIndex (S ⊓ Subgroup.centralizer ({f'} : Set G)) *
            Nat.card ↥(J ⊓ (S ⊓ Subgroup.centralizer ({f'} : Set G))) := hR1.symm
        _ ≤ J.relIndex S * 2 ^ e := Nat.mul_le_mul hR2 hR4
        _ ≤ (J.relIndex T * 2) * 2 ^ e := by
            rw [hR5]; exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hR6)
        _ = J.relIndex T * 2 ^ (e + 1) := by rw [pow_succ]; ring
    have h5 := Nat.le_of_mul_le_mul_left key hpos
    have h6 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h5
    obtain ⟨k, hk⟩ := he
    omega
  ·
    have hCV : ElemAb2 (V ⊓ Subgroup.centralizer ({f} : Set G)) :=
      CFSG.CGT.PushingUpLit.A78Sp4.ElemAb2.mono h.base.elem_V inf_le_left
    obtain ⟨E, hEel, hCVE, hfE, hEcard⟩ := exists_elemAb2_ext hCV hf2
      (fun x hx => (Subgroup.mem_centralizer_singleton_iff.1 hx.2).symm)
      (fun hf => hfJ (h.base.V_le_J hf.1))
    have hEC : E ≤ Subgroup.centralizer ({f} : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hEel x hx f hfE).1
    obtain ⟨X, hXle, hXcard, m, hXm⟩ := hconj E hEC hEel.isPGroup
    have hXel : ElemAb2 X := by rw [hXm]; exact elemAb2_cj hEel m
    have hXS : X ≤ S := fun x hx => (hXle hx).1
    have h1 : Nat.card X ≤ 2 * Nat.card ↥(X ⊓ T) :=
      card_le_two_mul_of_coset inf_le_left fun x hx y hy hxT hyT =>
        ⟨X.mul_mem (X.inv_mem hx) hy,
          h.base.inv_mul_mem_T (hXS hx) (hXS hy) (fun h' => hxT ⟨hx, h'⟩) (fun h' => hyT ⟨hy, h'⟩)⟩
    have h2 : Nat.card ↥(X ⊓ T) ≤ 2 * Nat.card ↥(X ⊓ J) := by
      have hle : X ⊓ J ≤ X ⊓ T := inf_le_inf_left _ hJT
      have := card_le_two_mul_of_coset hle fun x hx y hy hxJ hyJ =>
        ⟨X.mul_mem (X.inv_mem hx.1) hy.1,
          h.inv_mul_mem_J hfT hfJ hf2 hx.2 (fun h' => hxJ ⟨hx.1, h'⟩) (hXel x hx.1 x hx.1).2
            hy.2 (fun h' => hyJ ⟨hy.1, h'⟩) (hXel y hy.1 y hy.1).2⟩
      exact this
    have hXJ : X ⊓ J ≤ Z ⊓ Subgroup.centralizer ({f'} : Set G) := fun x hx =>
      ⟨hinvo x ⟨hx.2, (hXle hx.1).2⟩ (hXel x hx.1 x hx.1).2, (hXle hx.1).2⟩
    have h3 := (Subgroup.card_le_of_le hXJ).trans hcard
    have h4 : 2 ^ e ≤ Nat.card ↥(V ⊓ Subgroup.centralizer ({f} : Set G)) :=
      (h.field.cent_L f hfT hfJ hf2).card_CV
    have h5 : 2 ^ (e + 1) ≤ 2 ^ (e / 2 + 2) := by
      rw [pow_succ, show e / 2 + 2 = (e / 2 + 1) + 1 by ring, pow_succ, pow_succ]
      calc 2 ^ e * 2 ≤ Nat.card E := by rw [hEcard]; linarith
        _ = Nat.card X := hXcard.symm
        _ ≤ 2 ^ (e / 2) * 2 * 2 := by linarith
    have h6 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h5
    obtain ⟨k, hk⟩ := he
    omega

theorem T2Loc.T_eq_J (h : T2Loc G L L₂ V V₂ Z J T S M M₂ e) : T = J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hTJ
  obtain ⟨f₀, hf₀T, hf₀J, hf₀2⟩ := h.field.exists_inv hTJ
  obtain ⟨g, hfS, hR⟩ := exists_fully_centralized h.base.sylow (h.base.T_le hf₀T)
  have hfT : g⁻¹ * f₀ * g ∈ T := h.mem_T_of_fully hTJ hf₀T hf₀J hf₀2 hfS hR
  set f := g⁻¹ * f₀ * g with hf
  have hf2 : f * f = 1 := by
    calc f * f = g⁻¹ * (f₀ * f₀) * g := by rw [hf]; group
      _ = 1 := by rw [hf₀2]; group
  have hfJ : f ∉ J := fun hJ => hf₀J (h.strongClosure (h.base.T_le hf₀T) hf₀2 (by
    rw [← hf]; exact hJ))
  have hf1 : f ≠ 1 := fun h1 => hfJ (h1 ▸ J.one_mem)
  set C := Subgroup.centralizer ({f} : Set G) with hC
  set Q := CFSG.Open.pCoreOf 2 C with hQ
  have hQp : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 C
  have hQn : ∀ c ∈ C, ∀ q ∈ Q, c * q * c⁻¹ ∈ Q := fun c hc q hq =>
    (Subgroup.mem_normalizer_iff.1 (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 C hc) q).1 hq
  have hZel : ElemAb2 Z := CFSG.CGT.PushingUpLit.A78Sp4.ElemAb2.mono h.base.elem_V h.base.Z_le_V
  have hYel : ElemAb2 (Z ⊓ C) := CFSG.CGT.PushingUpLit.A78Sp4.ElemAb2.mono hZel inf_le_left
  have hYne : Z ⊓ C ≠ ⊥ := by
    intro hbot
    have h1 := card_le_card_centralizer_sq hZel hf2 fun x hx => h.base.conj_Z hfS hx
    rw [← hC, hbot, Subgroup.card_bot, one_pow, h.base.card_Z] at h1
    have := Nat.one_lt_two_pow (n := e) (by have := h.base.two_le; omega)
    omega
  have hRY : ∀ t ∈ S ⊓ C, cj t (Z ⊓ C) = Z ⊓ C := by
    intro t ht
    rw [CFSG.CGT.PushingUpLit.A78Sp4.cj_inf_eq,
      CFSG.CGT.PushingUpLit.A78Sp4.cj_eq_of_mem_normalizer_set (h.base.S_le_normalizer_Z ht.1),
      CFSG.CGT.PushingUpLit.A78Sp4.cj_eq_self_of_mem ht.2]
  obtain ⟨z, hzY, hz1, hzfix⟩ := exists_fixed_ne_one (h.base.isPGroup_S.to_le inf_le_left) hYel
    hYne hRY
  have hzQ : z ∈ Q := by
    have hcent : z ∈ Subgroup.centralizer (Q : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      have hqR : q ∈ S ⊓ C := CFSG.CGT.PushingUpLit.A78Sp4.pCoreOf_le_of_isSylowOf hR hq
      have h1 := hzfix q hqR
      calc q * z = q * z * q⁻¹ * q := by group
        _ = z * q := by rw [h1]
    exact CFSG.CGT.PushingUpLit.A78Sp4.cent_le_pCoreOf h.charTwo hf2 hf1 ⟨hzY.2, hcent⟩
  exact hz1 (h.no_fixed_point hfT hfJ hf2 hQp hQn z hzQ (h.base.Z_le_J hzY.1) hzY.2)

end CFSG.CGT.PushingUpLit.A78T2
