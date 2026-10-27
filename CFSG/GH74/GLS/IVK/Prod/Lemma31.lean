module

public import CFSG.GH74.GLS.IVK.Prod.Basic

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.GorensteinWalter
open CFSG.Semidihedral

section Lemma31

variable {H : Type} [Group H] {K₁ K₂ : Subgroup H} {F₁ F₂ : Type} [Field F₁] [Field F₂]

namespace ProdSL2

theorem invol_coset (h : ProdSL2 H K₁ K₂ F₁ F₂) {z : H} (hz : z ∈ K₁ ⊓ K₂) (hz1 : z ≠ 1) {t : H}
    (ht2 : t * t = 1) (hK : K₁.map (MulAut.conj t).toMonoidHom = K₂) {a b : H} (ha : a ∈ K₁)
    (hb : b ∈ K₂) (hx : (a * b * t) * (a * b * t) = 1) :
    (a * b * t = a * t * a⁻¹) ∨ (a * b * t = a * (z * t) * a⁻¹) := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hzt : t * z * t⁻¹ = z := h.t_comm_z hz hz1 ht2 hK
  have hzt' : t * z = z * t := by
    have : t * z * t⁻¹ * t = z * t := by rw [hzt]
    simpa [mul_assoc] using this
  set a' := t * a * t⁻¹ with ha'
  set b' := t * b * t⁻¹ with hb'
  have ha'K : a' ∈ K₂ := swap_mem₁ hK ha
  have hb'K : b' ∈ K₁ := swap_mem₂ ht2 hK hb
  have h1 : a * b * a' * b' = 1 := by
    have : (a * b * t) * (a * b * t) = a * b * a' * b' * (t * t) := by
      simp only [ha', hb']
      group
    rw [this, ht2, mul_one] at hx
    exact hx
  have hcomm : (b * a') * b' = b' * (b * a') := (h.comm b' hb'K (b * a') (K₂.mul_mem hb ha'K)).symm
  have h2 : (a * b') * (b * a') = 1 := by
    calc (a * b') * (b * a') = a * (b' * (b * a')) := by group
      _ = a * ((b * a') * b') := by rw [hcomm]
      _ = a * b * a' * b' := by group
      _ = 1 := h1
  have hab'K₂ : a * b' ∈ K₂ := by
    have : a * b' = (b * a')⁻¹ := eq_inv_of_mul_eq_one_left h2
    rw [this]
    exact K₂.inv_mem (K₂.mul_mem hb ha'K)
  have hwK : a * b' ∈ K₁ ⊓ K₂ := ⟨K₁.mul_mem ha hb'K, hab'K₂⟩
  have hb'eq : b' = a⁻¹ * (a * b') := by group
  set w := a * b' with hw
  have hwa : a * w = w * a := h.comm a ha w hwK.2
  have hwcases := h.inter_cases hz hz1 w hwK
  have htw : t * w * t⁻¹ = w := by
    rcases hwcases with h0 | h0
    · rw [h0]; group
    · rw [h0]; exact hzt
  have htw' : t * w = w * t := by
    have : t * w * t⁻¹ * t = w * t := by rw [htw]
    simpa [mul_assoc] using this
  have hbeq : b = a'⁻¹ * w := by
    have h3 : b = t * b' * t⁻¹ := by
      simp only [hb']
      calc b = (t * t) * b * (t⁻¹ * t⁻¹) := by rw [ht2, hti, ht2]; group
        _ = t * (t * b * t⁻¹) * t⁻¹ := by group
    rw [h3, hb'eq]
    simp only [ha']
    have : t * (a⁻¹ * w) * t⁻¹ = (t * a * t⁻¹)⁻¹ * (t * w * t⁻¹) := by group
    rw [this, htw]
  have hawinv : a⁻¹ * w = w * a⁻¹ := by
    calc a⁻¹ * w = a⁻¹ * (w * a) * a⁻¹ := by group
      _ = a⁻¹ * (a * w) * a⁻¹ := by rw [hwa]
      _ = w * a⁻¹ := by group
  have htwt : t⁻¹ * w * t = w := by
    rw [hti]
    calc t * w * t = (w * t) * t := by rw [htw']
      _ = w * (t * t) := by group
      _ = w := by rw [ht2, mul_one]
  have hx_eq : a * b * t = a * (w * t) * a⁻¹ := by
    rw [hbeq]
    simp only [ha']
    calc a * ((t * a * t⁻¹)⁻¹ * w) * t = a * t * a⁻¹ * (t⁻¹ * w * t) := by group
      _ = a * t * a⁻¹ * w := by rw [htwt]
      _ = a * t * (a⁻¹ * w) := by group
      _ = a * t * (w * a⁻¹) := by rw [hawinv]
      _ = a * (t * w) * a⁻¹ := by group
      _ = a * (w * t) * a⁻¹ := by rw [htw']
  rcases hwcases with h0 | h0
  · left
    rw [hx_eq, h0]
    group
  · right
    rw [hx_eq, h0]


@[expose] noncomputable def normHom (h : ProdSL2 H K₁ K₂ F₁ F₂) (t : H)
    (hK : K₁.map (MulAut.conj t).toMonoidHom = K₂) : ↥K₁ →* H where
  toFun a := (a : H) * (t * a * t⁻¹)
  map_one' := by simp
  map_mul' a a' := by
    have hc : (a' : H) * (t * a * t⁻¹) = (t * a * t⁻¹) * a' :=
      h.comm a' a'.2 _ (swap_mem₁ hK a.2)
    calc ((a * a' : ↥K₁) : H) * (t * ((a * a' : ↥K₁) : H) * t⁻¹)
        = (a : H) * ((a' : H) * (t * a * t⁻¹)) * (t * a' * t⁻¹) := by
          simp only [Subgroup.coe_mul]; group
      _ = (a : H) * ((t * a * t⁻¹) * a') * (t * a' * t⁻¹) := by rw [hc]
      _ = ((a : H) * (t * a * t⁻¹)) * ((a' : H) * (t * a' * t⁻¹)) := by group

theorem normHom_apply (h : ProdSL2 H K₁ K₂ F₁ F₂) (t : H)
    (hK : K₁.map (MulAut.conj t).toMonoidHom = K₂) (a : ↥K₁) :
    h.normHom t hK a = (a : H) * (t * a * t⁻¹) := rfl


@[expose] noncomputable def zHom (z : H) (hzo : orderOf z = 2) : Multiplicative (ZMod 2) →* H :=
  MonoidHom.mk' (fun ε => z ^ (Multiplicative.toAdd ε).val) (by
    intro a b
    have h1 : (Multiplicative.toAdd (a * b)).val =
        ((Multiplicative.toAdd a).val + (Multiplicative.toAdd b).val) % 2 := by
      show (Multiplicative.toAdd a + Multiplicative.toAdd b).val = _
      rw [ZMod.val_add]
    have hp := pow_mod_orderOf z ((Multiplicative.toAdd a).val + (Multiplicative.toAdd b).val)
    rw [hzo] at hp
    rw [h1, ← pow_add]
    exact hp)

theorem zHom_apply (z : H) (hzo : orderOf z = 2) (ε : Multiplicative (ZMod 2)) :
    zHom z hzo ε = z ^ (Multiplicative.toAdd ε).val := rfl

theorem zHom_eq_one_iff (z : H) (hz1 : z ≠ 1) (hzo : orderOf z = 2) (ε : Multiplicative (ZMod 2)) :
    zHom z hzo ε = 1 ↔ ε = 1 := by
  rw [zHom_apply]
  constructor
  · intro h1
    have hlt : (Multiplicative.toAdd ε).val < 2 := ZMod.val_lt _
    have h0 : (Multiplicative.toAdd ε).val = 0 := by
      by_contra hne
      have : (Multiplicative.toAdd ε).val = 1 := by omega
      rw [this, pow_one] at h1
      exact hz1 h1
    have : Multiplicative.toAdd ε = 0 := (ZMod.val_eq_zero _).1 h0
    exact this
  · intro h1
    rw [h1]
    simp


theorem centralizer_equiv (h : ProdSL2 H K₁ K₂ F₁ F₂) {z : H} (hz : z ∈ K₁ ⊓ K₂) (hz1 : z ≠ 1)
    {t : H} (ht2 : t * t = 1) (hK : K₁.map (MulAut.conj t).toMonoidHom = K₂) :
    Nonempty (↥(centralizer ({t} : Set H) ⊓ (K₁ ⊔ K₂)) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) F₁ × Multiplicative (ZMod 2)) := by
  obtain ⟨hint, hzo⟩ := h.inter_eq hz hz1
  have hz2 : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hzo, pow_two] at this
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hzt : t * z * t⁻¹ = z := h.t_comm_z hz hz1 ht2 hK
  have hcases := h.inter_cases hz hz1
  obtain ⟨ζ, hζ⟩ : ∃ ζ : Multiplicative (ZMod 2) →* H, ∀ ε, ζ ε = z ^ (Multiplicative.toAdd ε).val :=
    ⟨zHom z hzo, fun _ => rfl⟩
  have hzK : ∀ x ∈ K₁ ⊔ K₂, Commute x z := fun x hx => (h.z_comm hz hx).symm
  have hNmem : ∀ a : ↥K₁, h.normHom t hK a ∈ K₁ ⊔ K₂ := fun a =>
    Subgroup.mul_mem_sup a.2 (swap_mem₁ hK a.2)
  have hzpow : ∀ k : ℕ, z ^ k ∈ K₁ ⊔ K₂ := fun k =>
    pow_mem (Subgroup.mem_sup_left hz.1) k
  have hcomm : ∀ (a : ↥K₁) (ε : Multiplicative (ZMod 2)), Commute (h.normHom t hK a) (ζ ε) := by
    intro a ε
    rw [hζ]
    exact (hzK _ (hNmem a)).pow_right _
  let Φ : ↥K₁ × Multiplicative (ZMod 2) →* H := (h.normHom t hK).noncommCoprod ζ hcomm
  have hΦ : ∀ p, Φ p = h.normHom t hK p.1 * ζ p.2 := fun p => rfl
  have hconj_Φ : ∀ p, t * Φ p * t⁻¹ = Φ p := by
    rintro ⟨a, ε⟩
    rw [hΦ]
    simp only [normHom_apply, hζ]
    set k := (Multiplicative.toAdd ε).val
    have e1 : t * ((a : H) * (t * a * t⁻¹) * z ^ k) * t⁻¹ =
        (t * a * t⁻¹) * (t * (t * a * t⁻¹) * t⁻¹) * (t * z ^ k * t⁻¹) := by group
    have e2 : t * (t * (a : H) * t⁻¹) * t⁻¹ = a := by
      calc t * (t * (a : H) * t⁻¹) * t⁻¹ = (t * t) * a * (t⁻¹ * t⁻¹) := by group
        _ = a := by rw [← mul_inv_rev, ht2]; group
    have e3 : t * z ^ k * t⁻¹ = z ^ k := by
      rw [← conj_pow, hzt]
    rw [e1, e2, e3, ← h.comm a a.2 _ (swap_mem₁ hK a.2)]
  have hmem : ∀ p, Φ p ∈ centralizer ({t} : Set H) ⊓ (K₁ ⊔ K₂) := by
    intro p
    refine ⟨?_, ?_⟩
    · show Φ p ∈ centralizer ({t} : Set H)
      rw [Subgroup.mem_centralizer_singleton_iff]
      have := hconj_Φ p
      calc Φ p * t = t * Φ p * t⁻¹ * t := by rw [this]
        _ = t * Φ p := by group
    · rw [hΦ, hζ]
      exact Subgroup.mul_mem _ (hNmem p.1) (hzpow _)
  let G₀ : Subgroup H := centralizer ({t} : Set H) ⊓ (K₁ ⊔ K₂)
  let Φ' : ↥K₁ × Multiplicative (ZMod 2) →* ↥G₀ := Φ.codRestrict G₀ hmem
  have hΦ'val : ∀ p, ((Φ' p : ↥G₀) : H) = Φ p := fun p => rfl
  have hsurj : Function.Surjective Φ' := by
    rintro ⟨x, hxC, hxK⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := (h.mem_sup_iff x).1 hxK
    have hxt : t * (a * b) * t⁻¹ = a * b := by
      have : (a * b) * t = t * (a * b) := Subgroup.mem_centralizer_singleton_iff.1 hxC
      calc t * (a * b) * t⁻¹ = (a * b) * t * t⁻¹ := by rw [this]
        _ = a * b := by group
    set a' := t * a * t⁻¹ with ha'
    set b' := t * b * t⁻¹ with hb'
    have ha'K : a' ∈ K₂ := swap_mem₁ hK ha
    have hb'K : b' ∈ K₁ := swap_mem₂ ht2 hK hb
    have hexp : t * (a * b) * t⁻¹ = a' * b' := by simp only [ha', hb']; group
    have hc' : a' * b' = b' * a' := (h.comm b' hb'K a' ha'K).symm
    have hab : a * b = b' * a' := by rw [← hxt, hexp, hc']
    set w := b'⁻¹ * a with hw
    have hwK₁ : w ∈ K₁ := K₁.mul_mem (K₁.inv_mem hb'K) ha
    have hwb : w * b = a' := by
      calc b'⁻¹ * a * b = b'⁻¹ * (a * b) := by group
        _ = b'⁻¹ * (b' * a') := by rw [hab]
        _ = a' := by group
    have hwK₂ : w ∈ K₂ := by
      have : w = a' * b⁻¹ := by
        calc w = w * b * b⁻¹ := by group
          _ = a' * b⁻¹ := by rw [hwb]
      rw [this]
      exact K₂.mul_mem ha'K (K₂.inv_mem hb)
    have hwcase := hcases w ⟨hwK₁, hwK₂⟩
    have hbeq : b = w⁻¹ * a' := by
      calc b = w⁻¹ * (w * b) := by group
        _ = w⁻¹ * a' := by rw [hwb]
    have hwinv : w⁻¹ = w := by
      rcases hwcase with h0 | h0
      · rw [h0]; simp
      · rw [h0]; exact inv_eq_of_mul_eq_one_right hz2
    have hwa' : w * a' = a' * w := by
      rcases hwcase with h0 | h0
      · rw [h0]; simp
      · rw [h0]; exact h.z_comm hz (Subgroup.mem_sup_right ha'K)
    have hx_eq : a * b = (a * a') * w := by
      calc a * b = a * (w⁻¹ * a') := by rw [← hbeq]
        _ = a * (w * a') := by rw [hwinv]
        _ = a * (a' * w) := by rw [hwa']
        _ = (a * a') * w := by group
    rcases hwcase with h0 | h0
    · refine ⟨(⟨a, ha⟩, 1), Subtype.ext ?_⟩
      rw [hΦ'val, hΦ]
      show (a : H) * (t * a * t⁻¹) * ζ 1 = a * b
      rw [map_one, mul_one, hx_eq, h0, mul_one]
    · refine ⟨(⟨a, ha⟩, Multiplicative.ofAdd 1), Subtype.ext ?_⟩
      rw [hΦ'val, hΦ]
      show (a : H) * (t * a * t⁻¹) * ζ (Multiplicative.ofAdd 1) = a * b
      rw [hζ, hx_eq, h0]
      have : (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 2))).val = 1 := by decide
      rw [this, pow_one]
  let π : ↥K₁ →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F₁ :=
    (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F₁))).comp
      h.slEquiv₁.toMonoidHom
  let Θ : ↥K₁ × Multiplicative (ZMod 2) →*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) F₁ × Multiplicative (ZMod 2) :=
    π.prodMap (MonoidHom.id _)
  have hΘsurj : Function.Surjective Θ := by
    rintro ⟨g, ε⟩
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective g
    exact ⟨(h.slEquiv₁.symm s, ε), by simp [Θ, π]⟩
  obtain ⟨h2, hφz⟩ := h.z_data₁ hz hz1
  have hcenter : ∀ a : ↥K₁, π a = 1 ↔ a = 1 ∨ a = ⟨z, hz.1⟩ := by
    intro a
    show (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F₁)))
      (h.slEquiv₁ a) = 1 ↔ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      ProjectiveSL2Cover.mem_center_iff_eq_one_or_minusIdentity,
      ProjectiveSL2Cover.minusIdentity_eq_neg_one]
    constructor
    · rintro (h1 | h1)
      · left; exact h.slEquiv₁.injective (by rw [h1, map_one])
      · right; exact h.slEquiv₁.injective (by rw [h1, hφz]; rfl)
    · rintro (h1 | h1)
      · left; rw [h1, map_one]
      · right; rw [h1, hφz]; rfl
  have hker : Φ'.ker = Θ.ker := by
    ext ⟨a, ε⟩
    simp only [MonoidHom.mem_ker]
    constructor
    · intro h1
      have h1' : Φ (a, ε) = 1 := congrArg Subtype.val h1
      rw [hΦ] at h1'
      simp only [normHom_apply, hζ] at h1'
      set k := (Multiplicative.toAdd ε).val with hk
      have haK₂ : (a : H) ∈ K₂ := by
        have : (a : H) = ((t * a * t⁻¹) * z ^ k)⁻¹ := by
          apply eq_inv_of_mul_eq_one_left
          rw [← mul_assoc]
          exact h1'
        rw [this]
        exact K₂.inv_mem (K₂.mul_mem (swap_mem₁ hK a.2) (pow_mem hz.2 k))
      have hacase := hcases a ⟨a.2, haK₂⟩
      have hε : ε = 1 := by
        rw [← zHom_eq_one_iff z hz1 hzo ε]
        show z ^ k = 1
        rcases hacase with h0 | h0
        · rw [h0] at h1'
          simpa using h1'
        · rw [h0, hzt] at h1'
          calc z ^ k = z * z * z ^ k := by rw [hz2, one_mul]
            _ = 1 := h1'
      refine Prod.ext ?_ hε
      show π a = 1
      rw [hcenter]
      rcases hacase with h0 | h0
      · left; exact Subtype.ext h0
      · right; exact Subtype.ext h0
    · intro h1
      have h1' : π a = 1 ∧ ε = 1 := ⟨congrArg Prod.fst h1, congrArg Prod.snd h1⟩
      obtain ⟨h1a, h1ε⟩ := h1'
      apply Subtype.ext
      rw [hΦ'val, hΦ]
      show h.normHom t hK a * ζ ε = 1
      rw [h1ε, map_one, mul_one]
      rcases (hcenter a).1 h1a with h0 | h0
      · rw [h0, map_one]
      · rw [h0, normHom_apply]
        show z * (t * z * t⁻¹) = 1
        rw [hzt, hz2]
  have e1 := QuotientGroup.quotientKerEquivOfSurjective Φ' hsurj
  have e2 := QuotientGroup.quotientKerEquivOfSurjective Θ hΘsurj
  have e3 := QuotientGroup.quotientMulEquivOfEq hker
  exact ⟨e1.symm.trans (e3.trans e2)⟩


end ProdSL2

end Lemma31

theorem ivk_3_1a : IVK_3_1a := by
  intro F₁ F₂ _ _ H _ _ K₁ K₂ h z hz hz1 x y hx hy hx2 hy2 hxz hyz
  obtain ⟨-, hzo⟩ := h.inter_eq hz hz1
  have hz2 : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hzo, pow_two] at this
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hint' : ∀ w ∈ K₁ ⊓ K₂, w = 1 ∨ w = z := h.inter_cases hz hz1
  have key : ∀ a ∈ K₁, ∀ b ∈ K₂, orderOf (a * b) = 2 → a * b ≠ z → a * a = z ∧ b * b = z := by
    intro a ha b hb hab2 habz
    have hsq : (a * b) * (a * b) = 1 := by
      have := pow_orderOf_eq_one (a * b)
      rwa [hab2, pow_two] at this
    have hc : a * b = b * a := h.comm a ha b hb
    have hab : (a * a) * (b * b) = 1 := by
      calc a * a * (b * b) = a * (a * b) * b := by group
        _ = a * (b * a) * b := by rw [← hc]
        _ = (a * b) * (a * b) := by group
        _ = 1 := hsq
    have haaK₂ : a * a ∈ K₂ := by
      have : a * a = (b * b)⁻¹ := eq_inv_of_mul_eq_one_left hab
      rw [this]
      exact K₂.inv_mem (K₂.mul_mem hb hb)
    rcases hint' (a * a) ⟨K₁.mul_mem ha ha, haaK₂⟩ with h1 | h1
    · exfalso
      have hbb : b * b = 1 := by rw [h1, one_mul] at hab; exact hab
      rcases h.eq_one_or_eq_z₁ hz hz1 ha h1 with ha1 | ha1 <;>
        rcases h.symm.eq_one_or_eq_z₁ (z := z) ⟨hz.2, hz.1⟩ hz1 hb hbb with hb1 | hb1
      · apply hab2.symm.not_gt
        rw [ha1, hb1, one_mul, orderOf_one]; omega
      · apply habz; rw [ha1, hb1, one_mul]
      · apply habz; rw [ha1, hb1, mul_one]
      · rw [ha1, hb1, hz2, orderOf_one] at hab2; omega
    · refine ⟨h1, ?_⟩
      rw [h1] at hab
      have : b * b = z⁻¹ := eq_inv_of_mul_eq_one_right hab
      rw [this, hzinv]
  obtain ⟨a, ha, b, hb, rfl⟩ := (h.mem_sup_iff x).1 hx
  obtain ⟨a', ha', b', hb', rfl⟩ := (h.mem_sup_iff y).1 hy
  obtain ⟨haz, hbz⟩ := key a ha b hb hx2 hxz
  obtain ⟨ha'z, hb'z⟩ := key a' ha' b' hb' hy2 hyz
  obtain ⟨g₁, hg₁, hg₁a⟩ := h.exists_conj₁ hz hz1 ha ha' haz ha'z
  obtain ⟨g₂, hg₂, hg₂b⟩ := h.symm.exists_conj₁ (z := z) ⟨hz.2, hz.1⟩ hz1 hb hb' hbz hb'z
  refine ⟨g₁ * g₂, Subgroup.mul_mem_sup hg₁ hg₂, ?_⟩
  have c1 : g₂ * a = a * g₂ := (h.comm a ha g₂ hg₂).symm
  have c2 : (g₂ * b * g₂⁻¹) * g₁⁻¹ = g₁⁻¹ * (g₂ * b * g₂⁻¹) :=
    (h.comm g₁⁻¹ (K₁.inv_mem hg₁) _ (K₂.mul_mem (K₂.mul_mem hg₂ hb) (K₂.inv_mem hg₂))).symm
  calc g₁ * g₂ * (a * b) * (g₁ * g₂)⁻¹ = g₁ * (g₂ * a) * b * g₂⁻¹ * g₁⁻¹ := by group
    _ = g₁ * (a * g₂) * b * g₂⁻¹ * g₁⁻¹ := by rw [c1]
    _ = g₁ * a * ((g₂ * b * g₂⁻¹) * g₁⁻¹) := by group
    _ = g₁ * a * (g₁⁻¹ * (g₂ * b * g₂⁻¹)) := by rw [c2]
    _ = (g₁ * a * g₁⁻¹) * (g₂ * b * g₂⁻¹) := by group
    _ = a' * b' := by rw [hg₁a, hg₂b]


theorem ivk_3_1b : IVK_3_1b := by
  intro F₁ F₂ _ _ H _ _ K₁ K₂ h z hz hz1 T t ht ht2 hK
  have ht2' : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht2, pow_two] at this
  refine ⟨?_, ?_⟩
  · rintro x ⟨p, hp, rfl⟩ hx2
    obtain ⟨a, ha, b, hb, rfl⟩ := (h.mem_sup_iff p).1 hp.2
    have hx : (a * b * t) * (a * b * t) = 1 := by
      have := pow_orderOf_eq_one (a * b * t)
      rwa [hx2, pow_two] at this
    have ha' : a⁻¹ ∈ K₁ ⊔ K₂ := Subgroup.mem_sup_left (K₁.inv_mem ha)
    rcases h.invol_coset hz hz1 ht2' hK ha hb hx with h1 | h1
    · left
      exact ⟨a⁻¹, ha', by rw [h1]; group⟩
    · right
      exact ⟨a⁻¹, ha', by rw [h1]; group⟩
  · obtain ⟨e⟩ := h.centralizer_equiv hz hz1 ht2' hK
    exact ⟨e.trans (MulEquiv.prodCongr (L2.equivPSL F₁).symm (MulEquiv.refl _))⟩


end CFSG.GH74.GLS.IVK
