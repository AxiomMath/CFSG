module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixSigns
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434CharThreeL2Tools

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12.KbarE27

open Subgroup

theorem exists_fixed_of_involutive (f : Fin 3 → Fin 3) (hf : ∀ k, f (f k) = k) :
    ∃ p, f p = p ∧ ((∀ k, f k = k) ∨ ∀ q, f q = q → q = p) := by
  have key : ∀ a b c : Fin 3, (∀ k, ![a, b, c] (![a, b, c] k) = k) →
      ∃ p, ![a, b, c] p = p ∧ ((∀ k, ![a, b, c] k = k) ∨ ∀ q, ![a, b, c] q = q → q = p) := by
    decide
  have hfe : f = ![f 0, f 1, f 2] := by
    funext k
    fin_cases k <;> rfl
  rw [hfe] at hf ⊢
  exact key _ _ _ hf

theorem exists_common_fixed (f g h : Fin 3 → Fin 3) (hf : ∀ k, f (f k) = k)
    (hg : ∀ k, g (g k) = k) (hh : ∀ k, h (h k) = k) (hfg : ∀ k, f (g k) = g (f k))
    (hfh : ∀ k, f (h k) = h (f k)) (hgh : ∀ k, g (h k) = h (g k)) :
    ∃ k, f k = k ∧ g k = k ∧ h k = k := by
  have hmove : ∀ u v : Fin 3 → Fin 3, (∀ k, u (v k) = v (u k)) → ∀ p, u p = p → u (v p) = v p :=
    fun u v huv p hp => by rw [huv, hp]
  obtain ⟨p, hp, hp1 | hpu⟩ := exists_fixed_of_involutive f hf
  · obtain ⟨q, hq, hq1 | hqu⟩ := exists_fixed_of_involutive g hg
    · obtain ⟨r, hr, -⟩ := exists_fixed_of_involutive h hh
      exact ⟨r, hp1 r, hq1 r, hr⟩
    · refine ⟨q, hp1 q, hq, ?_⟩
      exact hqu _ (hmove g h hgh q hq)
  · refine ⟨p, hp, hpu _ (hmove f g hfg p hp), hpu _ (hmove f h hfh p hp)⟩

variable {G₀ : Type} [Group G₀]

@[expose] def baseB (z : Fin 3 → G₀) : Subgroup G₀ :=
  zpowers (z 0) ⊔ zpowers (z 1) ⊔ zpowers (z 2)

theorem z_mem_baseB (z : Fin 3 → G₀) (k : Fin 3) : z k ∈ baseB z := by
  fin_cases k
  · exact mem_sup_left (mem_sup_left (mem_zpowers _))
  · exact mem_sup_left (mem_sup_right (mem_zpowers _))
  · exact mem_sup_right (mem_zpowers _)

structure E27Kit (Y₀ : Subgroup G₀) (z : Fin 3 → G₀) (P : G₀ → Prop) : Prop where
  conj : ∀ V : Subgroup G₀, CFSG.Open.IsElemAbelian 3 V → Nat.card V = 27 →
    ∃ σ : G₀, V = (baseB z).map (MulAut.conj σ).toMonoidHom
  P_conj : ∀ σ x : G₀, P x → P (σ * x * σ⁻¹)
  P_base : ∀ x ∈ baseB z, P x → ∃ k, x = z k ∨ x = (z k)⁻¹
  P_z : ∀ k, P (z k)
  distinct : ∀ k m : Fin 3, (z k = z m ∨ z k = (z m)⁻¹) → k = m
  cube : ∀ k, z k ^ 3 = 1
  ne_one : ∀ k, z k ≠ 1
  normal : Y₀.Normal
  five : ∀ k : Fin 3, ∃ (j l : Fin 3) (c : G₀), c ∈ Y₀ ∧ c ^ 2 = 1 ∧ c * z k = z k * c ∧
    (z j * (c * z l * c⁻¹)) ^ 5 = 1 ∧ z j * (c * z l * c⁻¹) ≠ 1

variable {Y₀ : Subgroup G₀} {z : Fin 3 → G₀} {P : G₀ → Prop}

def IsLine (z : Fin 3 → G₀) (σ : G₀) (k : Fin 3) (x : G₀) : Prop :=
  x = σ * z k * σ⁻¹ ∨ x = (σ * z k * σ⁻¹)⁻¹

theorem isLine_self (σ : G₀) (k : Fin 3) : IsLine z σ k (σ * z k * σ⁻¹) :=
  Or.inl rfl

theorem eq_of_isLine (hK : E27Kit Y₀ z P) {σ : G₀} {k m : Fin 3} {x : G₀}
    (hk : IsLine z σ k x) (hm : IsLine z σ m x) : k = m := by
  have key : ∀ k m : Fin 3, (σ * z k * σ⁻¹ = σ * z m * σ⁻¹ ∨
      σ * z k * σ⁻¹ = (σ * z m * σ⁻¹)⁻¹) → k = m := by
    intro k m h
    apply hK.distinct
    rcases h with h | h
    · left
      have := congrArg (fun y => σ⁻¹ * y * σ) h
      simpa [mul_assoc] using this
    · right
      have := congrArg (fun y => σ⁻¹ * y * σ) h
      simpa [mul_assoc] using this
  rcases hk with rfl | rfl <;> rcases hm with h | h
  · exact key k m (Or.inl h)
  · exact key k m (Or.inr h)
  · exact key k m (Or.inr (by rw [← h, inv_inv]))
  · exact key k m (Or.inl (inv_injective h))

theorem isLine_conj {σ t : G₀} {l m : Fin 3} {x : G₀}
    (ht : IsLine z σ m (t * (σ * z l * σ⁻¹) * t⁻¹)) (hx : IsLine z σ l x) :
    IsLine z σ m (t * x * t⁻¹) := by
  rcases hx with rfl | rfl
  · exact ht
  · have e : t * (σ * z l * σ⁻¹)⁻¹ * t⁻¹ = (t * (σ * z l * σ⁻¹) * t⁻¹)⁻¹ := by group
    rw [e]
    rcases ht with h | h
    · exact Or.inr (by rw [h])
    · exact Or.inl (by rw [h, inv_inv])

theorem five_dvd_card_of_kit [Finite G₀] (hK : E27Kit Y₀ z P) {V W₁ W₂ W₃ J : Subgroup G₀}
    {t₁ t₂ t₃ : G₀} (hc : IsE27InvConfig V W₁ W₂ W₃ t₁ t₂ t₃) (hVJ : V ≤ J)
    (hN₁ : ∀ y ∈ Y₀, y ^ 2 = 1 → (∀ w ∈ W₁, w * y = y * w) → y ∈ normalizer (J : Set G₀))
    (hN₂ : ∀ y ∈ Y₀, y ^ 2 = 1 → (∀ w ∈ W₂, w * y = y * w) → y ∈ normalizer (J : Set G₀))
    (hN₃ : ∀ y ∈ Y₀, y ^ 2 = 1 → (∀ w ∈ W₃, w * y = y * w) → y ∈ normalizer (J : Set G₀)) :
    5 ∣ Nat.card J := by
  obtain ⟨σ, hσ⟩ := hK.conj V hc.elem hc.card
  have ha_mem : ∀ k, σ * z k * σ⁻¹ ∈ V := fun k => by
    rw [hσ]
    exact ⟨z k, z_mem_baseB z k, by simp [MulAut.conj_apply]⟩
  have hline : ∀ x ∈ V, P x → ∃ k, IsLine z σ k x := by
    intro x hx hPx
    rw [hσ] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hconj : (MulAut.conj σ).toMonoidHom y = σ * y * σ⁻¹ := by
      simp [MulAut.conj_apply]
    rw [hconj] at hPx ⊢
    have hPy : P y := by
      have := hK.P_conj σ⁻¹ _ hPx
      simpa [mul_assoc] using this
    obtain ⟨k, hk | hk⟩ := hK.P_base y hy hPy
    · exact ⟨k, Or.inl (by rw [hk])⟩
    · exact ⟨k, Or.inr (by rw [hk]; group)⟩
  have hperm : ∀ t ∈ tripleNormalizer W₁ W₂ W₃, ∀ k, ∃ l,
      IsLine z σ l (t * (σ * z k * σ⁻¹) * t⁻¹) := by
    intro t ht k
    have hmem : t * (σ * z k * σ⁻¹) * t⁻¹ ∈ V :=
      (mem_normalizer_iff.1 (hc.tripleNormalizer_le_normalizer ht) _).1 (ha_mem k)
    exact hline _ hmem (hK.P_conj t _ (hK.P_conj σ _ (hK.P_z k)))
  have ht₁ := hc.t₁_mem_tripleNormalizer
  have ht₂ := hc.t₂_mem_tripleNormalizer
  have ht₃ := hc.t₃_mem_tripleNormalizer
  choose f₁ hf₁ using hperm t₁ ht₁
  choose f₂ hf₂ using hperm t₂ ht₂
  choose f₃ hf₃ using hperm t₃ ht₃
  have hinvol : ∀ t ∈ tripleNormalizer W₁ W₂ W₃, ∀ f : Fin 3 → Fin 3,
      (∀ k, IsLine z σ (f k) (t * (σ * z k * σ⁻¹) * t⁻¹)) → ∀ k, f (f k) = k := by
    intro t ht f hf k
    have hsq := mem_centralizer_iff.1 (hc.sq_mem_centralizer ht) _ (ha_mem k)
    have h1 : t * (t * (σ * z k * σ⁻¹) * t⁻¹) * t⁻¹ = σ * z k * σ⁻¹ := by
      calc t * (t * (σ * z k * σ⁻¹) * t⁻¹) * t⁻¹
          = t ^ 2 * (σ * z k * σ⁻¹) * (t ^ 2)⁻¹ := by rw [sq]; group
        _ = σ * z k * σ⁻¹ * t ^ 2 * (t ^ 2)⁻¹ := by rw [← hsq]
        _ = σ * z k * σ⁻¹ := by rw [mul_inv_cancel_right]
    have h2 := isLine_conj (hf (f k)) (hf k)
    rw [h1] at h2
    exact (eq_of_isLine hK (isLine_self σ k) h2).symm
  have hcomm : ∀ t ∈ tripleNormalizer W₁ W₂ W₃, ∀ t' ∈ tripleNormalizer W₁ W₂ W₃,
      ∀ f f' : Fin 3 → Fin 3, (∀ k, IsLine z σ (f k) (t * (σ * z k * σ⁻¹) * t⁻¹)) →
        (∀ k, IsLine z σ (f' k) (t' * (σ * z k * σ⁻¹) * t'⁻¹)) → ∀ k, f (f' k) = f' (f k) := by
    intro t ht t' ht' f f' hf hf' k
    have hNt := hc.tripleNormalizer_le_normalizer ht
    have hNt' := hc.tripleNormalizer_le_normalizer ht'
    have hbV : t' * (t * (σ * z k * σ⁻¹) * t⁻¹) * t'⁻¹ ∈ V :=
      (mem_normalizer_iff.1 hNt' _).1 ((mem_normalizer_iff.1 hNt _).1 (ha_mem k))
    have hcm := mem_centralizer_iff.1 (hc.commutator_mem_centralizer ht ht') _ hbV
    have h1 : t * (t' * (σ * z k * σ⁻¹) * t'⁻¹) * t⁻¹ =
        t' * (t * (σ * z k * σ⁻¹) * t⁻¹) * t'⁻¹ := by
      calc t * (t' * (σ * z k * σ⁻¹) * t'⁻¹) * t⁻¹
          = (t * t' * t⁻¹ * t'⁻¹) * (t' * (t * (σ * z k * σ⁻¹) * t⁻¹) * t'⁻¹) *
              (t * t' * t⁻¹ * t'⁻¹)⁻¹ := by group
        _ = t' * (t * (σ * z k * σ⁻¹) * t⁻¹) * t'⁻¹ * (t * t' * t⁻¹ * t'⁻¹) *
              (t * t' * t⁻¹ * t'⁻¹)⁻¹ := by rw [← hcm]
        _ = t' * (t * (σ * z k * σ⁻¹) * t⁻¹) * t'⁻¹ := by group
    have h2 := isLine_conj (hf (f' k)) (hf' k)
    have h3 := isLine_conj (hf' (f k)) (hf k)
    rw [h1] at h2
    exact eq_of_isLine hK h2 h3
  obtain ⟨k, hk₁, hk₂, hk₃⟩ := exists_common_fixed f₁ f₂ f₃ (hinvol t₁ ht₁ f₁ hf₁)
    (hinvol t₂ ht₂ f₂ hf₂) (hinvol t₃ ht₃ f₃ hf₃) (hcomm t₁ ht₁ t₂ ht₂ f₁ f₂ hf₁ hf₂)
    (hcomm t₁ ht₁ t₃ ht₃ f₁ f₃ hf₁ hf₃) (hcomm t₂ ht₂ t₃ ht₃ f₂ f₃ hf₂ hf₃)
  set a : G₀ := σ * z k * σ⁻¹ with ha
  have hDV : zpowers a ≤ V := zpowers_le.2 (ha_mem k)
  have ha1 : a ≠ 1 := fun h => hK.ne_one k (by
    have := congrArg (fun y => σ⁻¹ * y * σ) h
    simpa [ha, mul_assoc] using this)
  have ha3 : a ^ 3 = 1 := by rw [ha, conj_pow, hK.cube k]; group
  have hD3 : Nat.card (zpowers a) = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime ha3 ha1
  have hDne : zpowers a ≠ ⊥ := by
    intro h
    have := mem_zpowers a
    rw [h, mem_bot] at this
    exact ha1 this
  have hfix : ∀ (t : G₀) (f : Fin 3 → Fin 3),
      (∀ k, IsLine z σ (f k) (t * (σ * z k * σ⁻¹) * t⁻¹)) → f k = k →
      t * a * t⁻¹ ∈ zpowers a := by
    intro t f hf hfk
    have h := hf k
    rw [hfk] at h
    rcases h with h | h
    · rw [ha, h]
      exact mem_zpowers _
    · rw [ha, h]
      exact inv_mem (mem_zpowers _)
  have hDt : ∀ t ∈ ({t₁, t₂, t₃} : Set G₀), ∀ x ∈ zpowers a, t * x * t⁻¹ ∈ zpowers a := by
    intro t ht x hx
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hx
    have e : t * a ^ m * t⁻¹ = (t * a * t⁻¹) ^ m := (conj_zpow).symm
    rw [e]
    apply zpow_mem
    rcases ht with rfl | rfl | rfl
    · exact hfix t f₁ hf₁ hk₁
    · exact hfix t f₂ hf₂ hk₂
    · exact hfix t f₃ hf₃ hk₃
  have key : ∀ W : Subgroup G₀, W = zpowers a →
      (∀ y ∈ Y₀, y ^ 2 = 1 → (∀ w ∈ W, w * y = y * w) → y ∈ normalizer (J : Set G₀)) →
        5 ∣ Nat.card J := by
    intro W hW hN
    obtain ⟨j, l, c₀, hc₀, hc₀2, hc₀k, h5, h51⟩ := hK.five k
    have hcY : σ * c₀ * σ⁻¹ ∈ Y₀ := hK.normal.conj_mem c₀ hc₀ σ
    have hac : Commute a (σ * c₀ * σ⁻¹) := by
      show a * (σ * c₀ * σ⁻¹) = σ * c₀ * σ⁻¹ * a
      calc a * (σ * c₀ * σ⁻¹) = σ * (z k * c₀) * σ⁻¹ := by rw [ha]; group
        _ = σ * (c₀ * z k) * σ⁻¹ := by rw [hc₀k]
        _ = σ * c₀ * σ⁻¹ * a := by rw [ha]; group
    have hcN := hN _ hcY (by rw [conj_pow, hc₀2]; group) (by
      intro w hw
      rw [hW] at hw
      obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hw
      exact (hac.zpow_left m).eq)
    have hx : σ * z j * σ⁻¹ * ((σ * c₀ * σ⁻¹) * (σ * z l * σ⁻¹) * (σ * c₀ * σ⁻¹)⁻¹) ∈ J :=
      J.mul_mem (hVJ (ha_mem j)) ((mem_normalizer_iff.1 hcN _).1 (hVJ (ha_mem l)))
    have hxe : σ * z j * σ⁻¹ * ((σ * c₀ * σ⁻¹) * (σ * z l * σ⁻¹) * (σ * c₀ * σ⁻¹)⁻¹) =
        σ * (z j * (c₀ * z l * c₀⁻¹)) * σ⁻¹ := by group
    have hord : orderOf (σ * z j * σ⁻¹ *
        ((σ * c₀ * σ⁻¹) * (σ * z l * σ⁻¹) * (σ * c₀ * σ⁻¹)⁻¹)) = 5 := by
      have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
      rw [hxe]
      refine orderOf_eq_prime ?_ ?_
      · rw [conj_pow, h5]
        group
      · intro h
        apply h51
        have := congrArg (fun y => σ⁻¹ * y * σ) h
        simpa [mul_assoc] using this
    have hdvd := orderOf_dvd_natCard (⟨_, hx⟩ : J)
    rwa [Subgroup.orderOf_mk, hord] at hdvd
  rcases hc.exists_le_of_invariant hDV hDne hDt with hW | hW | hW
  · exact key W₁ (Subgroup.eq_of_le_of_card_ge hW (by rw [hD3, hc.card₁])) hN₁
  · exact key W₂ (Subgroup.eq_of_le_of_card_ge hW (by rw [hD3, hc.card₂])) hN₂
  · exact key W₃ (Subgroup.eq_of_le_of_card_ge hW (by rw [hD3, hc.card₃])) hN₃

theorem isE27InvConfig_map {G H : Type} [Group G] [Group H] {V W₁ W₂ W₃ : Subgroup G}
    {t₁ t₂ t₃ : G} (hc : IsE27InvConfig V W₁ W₂ W₃ t₁ t₂ t₃) (f : G →* H)
    (hf : ∀ v ∈ V, f v = 1 → v = 1) :
    IsE27InvConfig (V.map f) (W₁.map f) (W₂.map f) (W₃.map f) (f t₁) (f t₂) (f t₃) := by
  have hinj : Function.Injective (f.comp V.subtype) := by
    rw [injective_iff_map_eq_one]
    intro v hv
    exact Subtype.ext (hf v v.2 hv)
  have hcard : ∀ W : Subgroup G, W ≤ V → Nat.card (W.map f) = Nat.card W := by
    intro W hW
    have h1 : (W.subgroupOf V).map (f.comp V.subtype) = W.map f := by
      rw [← Subgroup.map_map, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hW]
    rw [← h1, Subgroup.card_map_of_injective hinj]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW).toEquiv
  have hW₁ : W₁ ≤ V := by rw [hc.join]; exact le_sup_left.trans le_sup_left
  have hW₂ : W₂ ≤ V := by rw [hc.join]; exact le_sup_right.trans le_sup_left
  have hW₃ : W₃ ≤ V := by rw [hc.join]; exact le_sup_right
  refine
    { card₁ := by rw [hcard W₁ hW₁, hc.card₁]
      card₂ := by rw [hcard W₂ hW₂, hc.card₂]
      card₃ := by rw [hcard W₃ hW₃, hc.card₃]
      join := by rw [hc.join, Subgroup.map_sup, Subgroup.map_sup]
      elem := hc.elem.map f
      card := by rw [hcard V le_rfl, hc.card]
      inv₁ := ?_
      inv₂ := ?_
      inv₃ := ?_
      comm₁ := ?_
      comm₂ := ?_
      comm₃ := ?_ }
  · rintro _ ⟨w, hw, rfl⟩
    rw [← map_mul, ← map_inv, ← map_mul, hc.inv₁ w hw, map_inv]
  · rintro _ ⟨w, hw, rfl⟩
    rw [← map_mul, ← map_inv, ← map_mul, hc.inv₂ w hw, map_inv]
  · rintro _ ⟨w, hw, rfl⟩
    rw [← map_mul, ← map_inv, ← map_mul, hc.inv₃ w hw, map_inv]
  · intro w hw
    rw [← Subgroup.map_sup] at hw
    obtain ⟨w, hw, rfl⟩ := hw
    rw [← map_mul, ← map_mul, hc.comm₁ w hw]
  · intro w hw
    rw [← Subgroup.map_sup] at hw
    obtain ⟨w, hw, rfl⟩ := hw
    rw [← map_mul, ← map_mul, hc.comm₂ w hw]
  · intro w hw
    rw [← Subgroup.map_sup] at hw
    obtain ⟨w, hw, rfl⟩ := hw
    rw [← map_mul, ← map_mul, hc.comm₃ w hw]

theorem isE27InvConfig_subgroupOf {G : Type} [Group G] {H V W₁ W₂ W₃ : Subgroup G}
    {t₁ t₂ t₃ : G} (hc : IsE27InvConfig V W₁ W₂ W₃ t₁ t₂ t₃) (hVH : V ≤ H) (ht₁ : t₁ ∈ H)
    (ht₂ : t₂ ∈ H) (ht₃ : t₃ ∈ H) :
    IsE27InvConfig (V.subgroupOf H) (W₁.subgroupOf H) (W₂.subgroupOf H) (W₃.subgroupOf H)
      ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩ ⟨t₃, ht₃⟩ := by
  have hcard : ∀ W : Subgroup G, W ≤ H → Nat.card (W.subgroupOf H) = Nat.card W :=
    fun W hW => Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW).toEquiv
  have h₁ : W₁ ≤ H := by rw [hc.join] at hVH; exact le_sup_left.trans (le_sup_left.trans hVH)
  have h₂ : W₂ ≤ H := by rw [hc.join] at hVH; exact le_sup_right.trans (le_sup_left.trans hVH)
  have h₃ : W₃ ≤ H := by rw [hc.join] at hVH; exact le_sup_right.trans hVH
  refine
    { card₁ := by rw [hcard W₁ h₁, hc.card₁]
      card₂ := by rw [hcard W₂ h₂, hc.card₂]
      card₃ := by rw [hcard W₃ h₃, hc.card₃]
      join := by
        rw [hc.join, Subgroup.subgroupOf_sup (sup_le h₁ h₂) h₃, Subgroup.subgroupOf_sup h₁ h₂]
      elem := hc.elem.subgroupOf H
      card := by rw [hcard V hVH, hc.card]
      inv₁ := fun w hw => Subtype.ext (hc.inv₁ w hw)
      inv₂ := fun w hw => Subtype.ext (hc.inv₂ w hw)
      inv₃ := fun w hw => Subtype.ext (hc.inv₃ w hw)
      comm₁ := ?_
      comm₂ := ?_
      comm₃ := ?_ }
  · intro w hw
    rw [← Subgroup.subgroupOf_sup h₂ h₃] at hw
    exact Subtype.ext (hc.comm₁ w hw)
  · intro w hw
    rw [← Subgroup.subgroupOf_sup h₁ h₃] at hw
    exact Subtype.ext (hc.comm₂ w hw)
  · intro w hw
    rw [← Subgroup.subgroupOf_sup h₁ h₂] at hw
    exact Subtype.ext (hc.comm₃ w hw)

theorem five_dvd_card_of_kit_aut [Finite G₀] {Y : Type} [Group Y] (Θ : MulAut Y ≃* G₀)
    (hK : E27Kit Y₀ z P) (hY₀ : ∀ c ∈ Y₀, ∃ y : Y, Θ (MulAut.conj y) = c)
    (hinj : Function.Injective (MulAut.conj : Y →* MulAut Y))
    {V W₁ W₂ W₃ J : Subgroup (MulAut Y)} {t₁ t₂ t₃ : MulAut Y}
    (hc : IsE27InvConfig V W₁ W₂ W₃ t₁ t₂ t₃) (hVJ : V ≤ J)
    (hN₁ : ∀ y : Y, y ^ 2 = 1 → (∀ w ∈ W₁, w y = y) →
      MulAut.conj y ∈ normalizer (J : Set (MulAut Y)))
    (hN₂ : ∀ y : Y, y ^ 2 = 1 → (∀ w ∈ W₂, w y = y) →
      MulAut.conj y ∈ normalizer (J : Set (MulAut Y)))
    (hN₃ : ∀ y : Y, y ^ 2 = 1 → (∀ w ∈ W₃, w y = y) →
      MulAut.conj y ∈ normalizer (J : Set (MulAut Y))) :
    5 ∣ Nat.card J := by
  have hc' := isE27InvConfig_map hc Θ.toMonoidHom
    (fun v _ hv => Θ.injective (by rw [MulEquiv.coe_toMonoidHom] at hv; rw [hv, map_one]))
  have hN : ∀ W : Subgroup (MulAut Y),
      (∀ y : Y, y ^ 2 = 1 → (∀ w ∈ W, w y = y) →
        MulAut.conj y ∈ normalizer (J : Set (MulAut Y))) →
      ∀ c ∈ Y₀, c ^ 2 = 1 → (∀ w ∈ W.map Θ.toMonoidHom, w * c = c * w) →
        c ∈ normalizer ((J.map Θ.toMonoidHom : Subgroup G₀) : Set G₀) := by
    intro W hNW c hcY hc2 hcomm
    obtain ⟨y, rfl⟩ := hY₀ c hcY
    have hy2 : y ^ 2 = 1 := by
      apply hinj
      apply Θ.injective
      rw [map_pow, map_pow, hc2, map_one, map_one]
    have hfix : ∀ w ∈ W, w y = y := by
      intro w hw
      have h1 : Θ w * Θ (MulAut.conj y) = Θ (MulAut.conj y) * Θ w :=
        hcomm (Θ w) ⟨w, hw, rfl⟩
      rw [← map_mul, ← map_mul] at h1
      have h2 : w * MulAut.conj y = MulAut.conj y * w := Θ.injective h1
      have h3 : MulAut.conj (w y) = MulAut.conj y := by
        rw [← CFSG.RankThree.PartTwo.Sec4.Item434CharThree.mul_conj_mul_inv, h2,
          mul_inv_cancel_right]
      exact hinj h3
    have hmem := hNW y hy2 hfix
    rw [← Subgroup.map_equiv_normalizer_eq]
    exact ⟨MulAut.conj y, hmem, rfl⟩
  have h5 := five_dvd_card_of_kit hK hc' (Subgroup.map_mono hVJ) (hN W₁ hN₁) (hN W₂ hN₂)
    (hN W₃ hN₃)
  rwa [Subgroup.card_map_of_injective Θ.injective] at h5

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12.KbarE27
