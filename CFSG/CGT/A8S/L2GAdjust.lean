module

public import CFSG.CGT.A8S.L2GModel
public import CFSG.CGT.T75JM.L2GAdjust

public section

namespace CFSG.CGT.A8S.L2

open CFSG.Open CFSG.CGT.Timmesfeld75 CFSG.CGT.T75JM

variable {G H : Type*} [Group G] [Group H]

theorem exists_conj_b0 {T T₁ : Subgroup G} (h : TCtx T T₁) (M : T1ModelA8 H)
    {E : OntoEmb H (Subgroup.normalizer (T : Set G))} (hE : ∀ x, x ∈ M.T0 ↔ E.Φ x ∈ T)
    {b : G} (hb : b ∈ normIn T₁ T) (hb1 : b ≠ 1) :
    ∃ E₁ : OntoEmb H (Subgroup.normalizer (T : Set G)),
      (∀ x, x ∈ M.T0 ↔ E₁.Φ x ∈ T) ∧ E₁.Φ M.b0 = b := by
  have hbT₁ : b ∈ T₁ := (mem_normIn.1 hb).1
  have hbN : b ∈ Subgroup.normalizer (T : Set G) := (mem_normIn.1 hb).2
  have hbT : b ∉ T := fun hbT => hb1 (by
    have : b ∈ T ⊓ T₁ := ⟨hbT, hbT₁⟩
    rw [h.inf_bot, Subgroup.mem_bot] at this
    exact this)
  obtain ⟨b', hb'⟩ := E.surj b hbN
  have hb'2 : b' * b' = 1 := E.inj (by
    rw [map_mul, hb', map_one]
    exact elemAbelian_mul_self h.elemAbelian₁ hbT₁)
  have hb'T : b' ∉ M.T0 := fun hm => hbT (hb' ▸ (hE b').1 hm)
  have hinner : ∀ (E₀ : OntoEmb H (Subgroup.normalizer (T : Set G))),
      (∀ x, x ∈ M.T0 ↔ E₀.Φ x ∈ T) → ∀ n : H, E₀.Φ (n * M.b0 * n⁻¹) = b →
      ∃ E₁ : OntoEmb H (Subgroup.normalizer (T : Set G)),
        (∀ x, x ∈ M.T0 ↔ E₁.Φ x ∈ T) ∧ E₁.Φ M.b0 = b := by
    intro E₀ hE₀ n hn
    refine ⟨E₀.comp (MulAut.conj n), fun x => ?_, ?_⟩
    · have hΦ : (E₀.comp (MulAut.conj n)).Φ x = E₀.Φ n * E₀.Φ x * (E₀.Φ n)⁻¹ := by
        simp [MulAut.conj_apply]
      rw [hΦ, hE₀ x]
      exact Subgroup.mem_normalizer_iff.1 (E₀.mem n) (E₀.Φ x)
    · simpa [MulAut.conj_apply] using hn
  obtain ⟨n, hn | hn⟩ := M.inv_class b' hb'2 hb'T
  · exact hinner E hE n (by rw [hn, hb'])
  · refine hinner (E.comp M.alpha) (fun x => ?_) (M.alpha n) ?_
    · rw [OntoEmb.comp_Φ_apply, ← hE, ← M.alpha_T]
    · have e : M.alpha (M.alpha n * M.b0 * (M.alpha n)⁻¹) = n * M.alpha M.b0 * n⁻¹ := by
        rw [map_mul M.alpha, map_mul M.alpha, map_inv M.alpha, M.alpha_alpha]
      rw [OntoEmb.comp_Φ_apply, e, hn, hb']

theorem exists_adjustA8 {T T₁ : Subgroup G} (h : TCtx T T₁) (M : T1ModelA8 H)
    {E : OntoEmb H (Subgroup.normalizer (T : Set G))} (hE : ∀ x, x ∈ M.T0 ↔ E.Φ x ∈ T) :
    ∃ E' : OntoEmb H (Subgroup.normalizer (T : Set G)),
      (∀ x, x ∈ M.T0 ↔ E'.Φ x ∈ T) ∧ ∀ x, x ∈ M.B0 ↔ E'.Φ x ∈ T₁ := by
  classical
  obtain ⟨b, hb, hb1⟩ := exists_ne_one_of_one_lt_card (K := normIn T₁ T)
    (by rw [h.norm2]; norm_num)
  have hbT₁ : b ∈ T₁ := (mem_normIn.1 hb).1
  obtain ⟨E₁, hE₁, hb0⟩ := exists_conj_b0 h M hE hb hb1
  set B'' : Subgroup H := T₁.comap E₁.Φ with hB''
  have hmemB : ∀ x, x ∈ B'' ↔ E₁.Φ x ∈ T₁ := fun x => Subgroup.mem_comap
  have hb0B : M.b0 ∈ B'' := by rw [hmemB, hb0]; exact hbT₁
  have hexpB : ∀ x ∈ B'', x * x = 1 := by
    intro x hx
    apply E₁.inj
    rw [map_mul, map_one]
    exact elemAbelian_mul_self h.elemAbelian₁ ((hmemB x).1 hx)
  have hcardB : Nat.card B'' = 4 := by
    rw [← h.norm2]
    refine Nat.card_congr (Equiv.ofBijective
      (fun x : B'' => (⟨E₁.Φ x, mem_normIn.2 ⟨(hmemB x).1 x.2, E₁.mem x⟩⟩ : normIn T₁ T)) ⟨?_, ?_⟩)
    · intro x y hxy
      exact Subtype.ext (E₁.inj (congrArg Subtype.val hxy))
    · rintro ⟨y, hy⟩
      obtain ⟨hyT₁, hyN⟩ := mem_normIn.1 hy
      obtain ⟨z, hz⟩ := E₁.surj y hyN
      exact ⟨⟨z, (hmemB z).2 (hz ▸ hyT₁)⟩, Subtype.ext hz⟩
  have hbotB : B'' ⊓ M.T0 = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have h1 : E₁.Φ x ∈ T ⊓ T₁ := ⟨(hE₁ x).1 hx.2, (hmemB x).1 hx.1⟩
    rw [h.inf_bot, Subgroup.mem_bot] at h1
    exact E₁.inj (h1.trans (map_one E₁.Φ).symm)
  have hnormB : ∀ x, x ∈ Subgroup.normalizer (B'' : Set H) ↔
      E₁.Φ x ∈ Subgroup.normalizer (T₁ : Set G) := fun x => h.mem_normalizer_comap_iff E₁ x
  have hcentB : ∀ c ∈ B'', c ≠ 1 → ∀ y : H, y * c = c * y →
      y ∈ Subgroup.normalizer (B'' : Set H) := by
    intro c hc hc1 y hy
    have hcT₁ : E₁.Φ c ∈ T₁ := (hmemB c).1 hc
    have hc1' : E₁.Φ c ≠ 1 := fun h1 => hc1 (E₁.inj (h1.trans (map_one E₁.Φ).symm))
    have hyc : E₁.Φ y * E₁.Φ c = E₁.Φ c * E₁.Φ y := by rw [← map_mul, ← map_mul, hy]
    refine (hnormB y).2 (h.wc₁.centralizer_le_normalizer hcT₁ hc1' ?_)
    exact Subgroup.mem_centralizer_singleton_iff.2 hyc
  have hB0 := M.klein_eq B'' hb0B hexpB hcardB hbotB hcentB
  refine ⟨E₁, hE₁, fun x => ?_⟩
  rw [← hB0]
  exact hmemB x

end CFSG.CGT.A8S.L2
