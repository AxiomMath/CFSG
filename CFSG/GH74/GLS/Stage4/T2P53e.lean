module

public import CFSG.GH74.GLS.Stage4.T2P53d
public import CFSG.GH74.GLS.Stage4.T2Ctx

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage4.Rest.T2

section Split

variable {G : Type} [Group G]

theorem t2P53_split {C₁ F : Subgroup G} (hFn : F ≤ normalizer (C₁ : Set G)) {y : G}
    (hy : y ∈ C₁ ⊔ F) : ∃ c ∈ C₁, ∃ f ∈ F, y = c * f := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left C₁ F hFn] at hy
  obtain ⟨c, hc, f, hf, rfl⟩ := hy
  exact ⟨c, hc, f, hf, rfl⟩

end Split

section Facts

variable {G : Type} [Group G] [Finite G] {Gs : Type} [Group Gs] {q₁ q₂ : ℕ} {z t : G}
  {K₁ K₂ S : Subgroup G} {F₁ F₂ : Type} [Field F₁] [Field F₂]

theorem t2P53_F_normC₁ (ctx : T2Ctx z K₁ K₂ S) {F : Subgroup G} (hFz : ∀ f ∈ F, f * z = z * f) :
    F ≤ normalizer ((K₁ ⊔ K₂ ⊔ S : Subgroup G) : Set G) := by
  intro f hf
  have hfC : f ∈ centralizer ({z} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 (hFz f hf)
  apply Subgroup.mem_normalizer_fintype
  intro x hx
  rw [ctx.KS] at hx ⊢
  exact ctx.C₁norm f hfC x hx

theorem t2P53_Cnorm (hSet : Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂) (hRem : Ch6Rem z K₁ K₂ F₁ F₂ t)
    (ctx : T2Ctx z K₁ K₂ S) {F : Subgroup G}
    (hCle : centralizer ({z} : Set G) ≤ K₁ ⊔ K₂ ⊔ S ⊔ F) (hFodd : ∀ f ∈ F, Odd (orderOf f))
    (hFz : ∀ f ∈ F, f * z = z * f) {c : G} (hc : c * z = z * c) :
    (∀ x ∈ K₁, c * x * c⁻¹ ∈ K₁) ∧ (∀ x ∈ K₂, c * x * c⁻¹ ∈ K₂) := by
  have hcC : c ∈ centralizer ({z} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 hc
  obtain ⟨c₁, hc₁, f, hf, rfl⟩ := t2P53_split (t2P53_F_normC₁ ctx hFz) (hCle hcC)
  have hc₁' : c₁ ∈ oPrimeResidualOf 2 (centralizer ({z} : Set G)) := by rw [← ctx.KS]; exact hc₁
  obtain ⟨hn₁, hn₂⟩ := t2C_C₁_normalizes hRem hSet.comm
  obtain ⟨hf₁, hf₂⟩ := t2Ctx_odd_normK ctx (hFz f hf) (hFodd f hf)
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · have := hn₁ c₁ hc₁' _ (hf₁ x hx)
    simpa [mul_assoc] using this
  · have := hn₂ c₁ hc₁' _ (hf₂ x hx)
    simpa [mul_assoc] using this

omit [Finite G] in
theorem t2P53_invK {K : Subgroup G} {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F))
    (e : ↥K ≃* SL2 F) (hzK : z ∈ K) (hze : e ⟨z, hzK⟩ = negOne F) :
    ∀ x ∈ K, x * x = 1 → x = 1 ∨ x = z := by
  intro x hx hx2
  by_cases hx1 : x = 1
  · exact Or.inl hx1
  · right
    have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card hodd
    have hne : e ⟨x, hx⟩ ≠ 1 := by
      intro h
      apply hx1
      have : (⟨x, hx⟩ : ↥K) = 1 := e.injective (by rw [h, map_one])
      simpa using congrArg Subtype.val this
    have hmul : e ⟨x, hx⟩ * e ⟨x, hx⟩ = 1 := by
      rw [← map_mul]
      have : (⟨x, hx⟩ : ↥K) * ⟨x, hx⟩ = 1 := Subtype.ext (by simpa using hx2)
      rw [this, map_one]
    have h3 := eq_negOne_of_involution h2 hmul hne
    have : (⟨x, hx⟩ : ↥K) = ⟨z, hzK⟩ := e.injective (by rw [h3, hze])
    simpa using congrArg Subtype.val this

theorem t2P53_hnc (hSet : Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂) (hRem : Ch6Rem z K₁ K₂ F₁ F₂ t)
    (ctx : T2Ctx z K₁ K₂ S) {F : Subgroup G}
    (hCle : centralizer ({z} : Set G) ≤ K₁ ⊔ K₂ ⊔ S ⊔ F) (hFodd : ∀ f ∈ F, Odd (orderOf f))
    (hFz : ∀ f ∈ F, f * z = z * f) (hFK : F ⊓ (K₁ ⊔ K₂) = ⊥)
    (hK₂inv : ∀ x ∈ K₂, x * x = 1 → x = 1 ∨ x = z) {u g : G} (hg : g⁻¹ * z * g = u)
    (hzu : z * u = u * z) (hzu_ne : z ≠ u) :
    ∃ x ∈ K₁, (g * z * g⁻¹) * x * (g * z * g⁻¹)⁻¹ ≠ x := by
  by_contra hcon
  push Not at hcon
  set y : G := g * z * g⁻¹ with hy
  have hz : z⁻¹ = z := inv_eq_of_mul_eq_one_right ctx.zz
  have hyz : y * z = z * y := by
    have hz' : z = g * u * g⁻¹ := by rw [← hg]; group
    calc y * z = g * z * g⁻¹ * (g * u * g⁻¹) := by rw [← hz']
      _ = g * (z * u) * g⁻¹ := by group
      _ = g * (u * z) * g⁻¹ := by rw [hzu]
      _ = (g * u * g⁻¹) * (g * z * g⁻¹) := by group
      _ = z * y := by rw [← hz']
  have hy2 : y * y = 1 := by
    calc y * y = g * (z * z) * g⁻¹ := by rw [hy]; group
      _ = 1 := by rw [ctx.zz]; group
  have hyz1 : y ≠ z := by
    intro h
    apply hzu_ne
    have : g * z = z * g := by
      calc g * z = (g * z * g⁻¹) * g := by group
        _ = z * g := by rw [← hy, h]
    calc z = g⁻¹ * (g * z) * 1 := by group
      _ = g⁻¹ * (z * g) := by rw [this]; group
      _ = u := by rw [← hg]; group
  have hy1 : y ≠ 1 := by
    intro h
    apply ctx.z_ne
    have : g * z * g⁻¹ = 1 := h
    calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
      _ = 1 := by rw [this]; group
  have hyC : y ∈ centralizer ({z} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 hyz
  have hFn := t2P53_F_normC₁ ctx hFz
  obtain ⟨c, hc, f, hf, hycf⟩ := t2P53_split hFn (hCle hyC)
  have hf2 : f * f = 1 := by
    have h1 : c * (f * c * f⁻¹) * (f * f) = 1 := by
      calc c * (f * c * f⁻¹) * (f * f) = (c * f) * (c * f) := by group
        _ = y * y := by rw [← hycf]
        _ = 1 := hy2
    have hcf : f * c * f⁻¹ ∈ K₁ ⊔ K₂ ⊔ S :=
      (Subgroup.mem_normalizer_iff.1 (hFn hf) c).1 hc
    have hmem : f * f ∈ K₁ ⊔ K₂ ⊔ S := by
      have : f * f = (c * (f * c * f⁻¹))⁻¹ := eq_inv_of_mul_eq_one_right h1
      rw [this]
      exact Subgroup.inv_mem _ (Subgroup.mul_mem _ hc hcf)
    have hmem' : f * f ∈ oPrimeResidualOf 2 (centralizer ({z} : Set G)) := by
      rw [← ctx.KS]; exact hmem
    have hodd : Odd (orderOf (f * f)) := by
      have : orderOf (f * f) ∣ orderOf f := by
        rw [← pow_two]; exact orderOf_pow_dvd 2
      exact Odd.of_dvd_nat (hFodd f hf) this
    have hK : f * f ∈ K₁ ⊔ K₂ := t2C_odd_mem_of_index_two hSet.index_two hmem' hodd
    have : f * f ∈ F ⊓ (K₁ ⊔ K₂) := ⟨F.mul_mem hf hf, hK⟩
    rw [hFK, Subgroup.mem_bot] at this
    exact this
  have hf1 : f = 1 := t2P53_odd_sq (hFodd f hf) hf2
  subst hf1
  rw [mul_one] at hycf
  have hyC₁ : y ∈ oPrimeResidualOf 2 (centralizer ({z} : Set G)) := by rw [← ctx.KS, hycf]; exact hc
  by_cases hyK : y ∈ K₁ ⊔ K₂
  ·
    obtain ⟨a, ha, b, hb, hab⟩ := (mem_sup_iff_of_comm hSet.comm y).1 hyK
    have haz : a ∈ Subgroup.zpowers z := by
      refine ctx.C.Z₁ a ha (fun k hk => ?_)
      have h1 := hcon k hk
      have h1' : y * k = k * y := by
        have : y * k * y⁻¹ = k := h1
        calc y * k = (y * k * y⁻¹) * y := by group
          _ = k * y := by rw [this]
      rw [hab] at h1'
      have h2 : k * b = b * k := hSet.comm k hk b hb
      have : a * k * b = k * a * b := by
        calc a * k * b = a * (k * b) := by group
          _ = a * (b * k) := by rw [h2]
          _ = a * b * k := by group
          _ = k * (a * b) := h1'
          _ = k * a * b := by group
      exact mul_right_cancel this
    have ha1 : a * a = 1 := by
      rcases t2C_zpowers_cases ctx.zz haz with h | h
      · rw [h]; simp
      · rw [h]; exact ctx.zz
    have hbb : b * b = 1 := by
      have hba : a * b = b * a := hSet.comm a ha b hb
      have : (a * b) * (a * b) = (a * a) * (b * b) := by
        calc (a * b) * (a * b) = a * (b * a) * b := by group
          _ = a * (a * b) * b := by rw [← hba]
          _ = (a * a) * (b * b) := by group
      have hy2' := hy2
      rw [hab] at hy2'
      rw [this, ha1, one_mul] at hy2'
      exact hy2'
    rcases t2C_zpowers_cases ctx.zz haz with ha' | ha' <;> rcases hK₂inv b hb hbb with hb' | hb'
    · exact hy1 (by rw [hab, ha', hb']; simp)
    · exact hyz1 (by rw [hab, ha', hb']; simp)
    · exact hyz1 (by rw [hab, ha', hb']; simp)
    · exact hy1 (by rw [hab, ha', hb']; exact ctx.zz)
  · exact t2C_not_cent_K₁ hSet hRem ctx.C hyC₁ hyK (fun x hx => by
      have h1 := hcon x hx
      calc y * x = (y * x * y⁻¹) * y := by group
        _ = x * y := by rw [h1])

end Facts

end CFSG.GH74.GLS.Stage4.Rest
