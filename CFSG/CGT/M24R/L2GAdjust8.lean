module

public import CFSG.CGT.M24R.L2GModel8
public import CFSG.CGT.T75JM.L2GAdjust

public section

namespace CFSG.CGT.M24R

open CFSG.Open CFSG.CGT.Timmesfeld75 CFSG.CGT.T75JM

variable {G H : Type*} [Group G] [Group H]

theorem card_comap_normIn {T T₁ : Subgroup G} (h : TCtx T T₁)
    (E : OntoEmb H (Subgroup.normalizer (T : Set G))) :
    Nat.card ((normIn T T₁).comap E.Φ) = 4 := by
  rw [← h.norm1]
  refine Nat.card_congr (Equiv.ofBijective
    (fun x : (normIn T T₁).comap E.Φ => (⟨E.Φ x, x.2⟩ : normIn T T₁)) ⟨?_, ?_⟩)
  · intro x y hxy
    exact Subtype.ext (E.inj (congrArg Subtype.val hxy))
  · rintro ⟨y, hy⟩
    obtain ⟨z, hz⟩ := E.surj y (Subgroup.le_normalizer (mem_normIn.1 hy).1)
    refine ⟨⟨z, ?_⟩, Subtype.ext hz⟩
    show E.Φ z ∈ normIn T T₁
    rw [hz]
    exact hy

theorem exists_adjust8 {T T₁ : Subgroup G} (h : TCtx T T₁)
    {E : OntoEmb H (Subgroup.normalizer (T : Set G))} {n : ℕ} (M : T1Model8 H n)
    (hE : ∀ x, x ∈ M.T0 ↔ E.Φ x ∈ T) :
    ∃ E' : OntoEmb H (Subgroup.normalizer (T : Set G)),
      (∀ x, x ∈ M.T0 ↔ E'.Φ x ∈ T) ∧ ∀ x, x ∈ M.B0 ↔ E'.Φ x ∈ T₁ := by
  classical
  obtain ⟨b, hb, hb1⟩ := exists_ne_one_of_one_lt_card (K := normIn T₁ T)
    (by rw [h.norm2]; norm_num)
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
  have hcentA : ∀ t ∈ M.T0, t * b' = b' * t → t ∈ (normIn T T₁).comap E.Φ := by
    intro t ht htb
    have h1 : E.Φ t ∈ Subgroup.centralizer ({b} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff, ← hb', ← map_mul, ← map_mul, htb]
    exact mem_normIn.2 ⟨(hE t).1 ht, h.wc₁.centralizer_le_normalizer hbT₁ hb1 h1⟩
  obtain ⟨n, hn⟩ := M.inv_class b' hb'2 hb'T _ (card_comap_normIn h E).le hcentA
  set E₁ : OntoEmb H (Subgroup.normalizer (T : Set G)) := E.comp (MulAut.conj n) with hE₁def
  have hΦ₁ : ∀ x, E₁.Φ x = E.Φ n * E.Φ x * (E.Φ n)⁻¹ := by
    intro x
    simp [E₁, MulAut.conj_apply]
  have hE₁ : ∀ x, x ∈ M.T0 ↔ E₁.Φ x ∈ T := by
    intro x
    rw [hΦ₁, hE x]
    exact Subgroup.mem_normalizer_iff.1 (E.mem n) (E.Φ x)
  have hb0 : E₁.Φ M.b0 = b := by
    rw [hΦ₁, ← map_inv, ← map_mul, ← map_mul, hn, hb']
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
  have hcardA : Nat.card ↥(M.T0 ⊓ Subgroup.normalizer (B'' : Set H)) = 4 := by
    rw [← h.norm1]
    refine Nat.card_congr (Equiv.ofBijective
      (fun x : ↥(M.T0 ⊓ Subgroup.normalizer (B'' : Set H)) =>
        (⟨E₁.Φ x, mem_normIn.2 ⟨(hE₁ x).1 x.2.1, (hnormB x).1 x.2.2⟩⟩ : normIn T T₁)) ⟨?_, ?_⟩)
    · intro x y hxy
      exact Subtype.ext (E₁.inj (congrArg Subtype.val hxy))
    · rintro ⟨y, hy⟩
      obtain ⟨hyT, hyN₁⟩ := mem_normIn.1 hy
      obtain ⟨z, hz⟩ := E₁.surj y (Subgroup.le_normalizer hyT)
      exact ⟨⟨z, Subgroup.mem_inf.2 ⟨(hE₁ z).2 (hz ▸ hyT), (hnormB z).2 (hz ▸ hyN₁)⟩⟩,
        Subtype.ext hz⟩
  have hcommB : ∀ a ∈ M.T0 ⊓ Subgroup.normalizer (B'' : Set H), ∀ x ∈ B'', a * x = x * a := by
    intro a ha x hx
    apply E₁.inj
    rw [map_mul, map_mul]
    exact h.comm_A_B (mem_normIn.2 ⟨(hE₁ a).1 ha.1, (hnormB a).1 ha.2⟩)
      (mem_normIn.2 ⟨(hmemB x).1 hx, E₁.mem x⟩)
  have hcentB : ∀ c ∈ B'', c ≠ 1 → ∀ y : H, y * c = c * y →
      y ∈ Subgroup.normalizer (B'' : Set H) := by
    intro c hc hc1 y hy
    have hcT₁ : E₁.Φ c ∈ T₁ := (hmemB c).1 hc
    have hc1' : E₁.Φ c ≠ 1 := fun h1 => hc1 (E₁.inj (h1.trans (map_one E₁.Φ).symm))
    have hyc : E₁.Φ y * E₁.Φ c = E₁.Φ c * E₁.Φ y := by rw [← map_mul, ← map_mul, hy]
    refine (hnormB y).2 (h.wc₁.centralizer_le_normalizer hcT₁ hc1' ?_)
    exact Subgroup.mem_centralizer_singleton_iff.2 hyc
  have hB0 := M.klein_eq B'' hb0B hexpB hcardB hbotB hcardA hcommB hcentB
  refine ⟨E₁, hE₁, fun x => ?_⟩
  rw [← hB0]
  exact hmemB x

end CFSG.CGT.M24R
