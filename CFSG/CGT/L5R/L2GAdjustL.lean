module

public import CFSG.CGT.L5R.L2GModelL

public section

namespace CFSG.CGT.L5R

open CFSG.Open CFSG.CGT.Timmesfeld75 CFSG.CGT.T75JM

variable {G H : Type*} [Group G] [Group H]

theorem isAdmL_comap {T T₁ : Subgroup G} (h : TCtxL T T₁)
    (E : OntoEmb H (Subgroup.normalizer (T : Set G))) {T0 : Subgroup H}
    (hE : ∀ x, x ∈ T0 ↔ E.Φ x ∈ T) : IsAdmL T0 (T₁.comap E.Φ) := by
  have hmemB : ∀ x, x ∈ T₁.comap E.Φ ↔ E.Φ x ∈ T₁ := fun x => Subgroup.mem_comap
  have hnormB : ∀ x, x ∈ Subgroup.normalizer ((T₁.comap E.Φ : Subgroup H) : Set H) ↔
      E.Φ x ∈ Subgroup.normalizer (T₁ : Set G) := fun x => h.mem_normalizer_comap_iff E x
  refine ⟨fun x hx => ?_, ?_, ?_, fun a ha x hx => ?_, fun c hc hc1 y hy => ?_⟩
  · apply E.inj
    rw [map_mul, map_one]
    exact elemAbelian_mul_self h.elemAbelian₁ ((hmemB x).1 hx)
  · rw [← h.norm2]
    refine Nat.card_congr (Equiv.ofBijective
      (fun x : T₁.comap E.Φ => (⟨E.Φ x, mem_normIn.2 ⟨(hmemB x).1 x.2, E.mem x⟩⟩ :
        normIn T₁ T)) ⟨?_, ?_⟩)
    · intro x y hxy
      exact Subtype.ext (E.inj (congrArg Subtype.val hxy))
    · rintro ⟨y, hy⟩
      obtain ⟨hyT₁, hyN⟩ := mem_normIn.1 hy
      obtain ⟨z, hz⟩ := E.surj y hyN
      exact ⟨⟨z, (hmemB z).2 (hz ▸ hyT₁)⟩, Subtype.ext hz⟩
  · rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have h1 : E.Φ x ∈ T ⊓ T₁ :=
      ⟨(hE x).1 (Subgroup.mem_inf.1 hx).2, (hmemB x).1 (Subgroup.mem_inf.1 hx).1⟩
    rw [h.inf_bot, Subgroup.mem_bot] at h1
    exact E.inj (h1.trans (map_one E.Φ).symm)
  · apply E.inj
    rw [map_mul, map_mul]
    exact h.comm_A_B (mem_normIn.2 ⟨(hE a).1 (Subgroup.mem_inf.1 ha).1,
      (hnormB a).1 (Subgroup.mem_inf.1 ha).2⟩) (mem_normIn.2 ⟨(hmemB x).1 hx, E.mem x⟩)
  · have hcT₁ : E.Φ c ∈ T₁ := (hmemB c).1 hc
    have hc1' : E.Φ c ≠ 1 := fun h1 => hc1 (E.inj (h1.trans (map_one E.Φ).symm))
    have hyc : E.Φ y * E.Φ c = E.Φ c * E.Φ y := by rw [← map_mul, ← map_mul, hy]
    exact (hnormB y).2 (h.wc₁.centralizer_le_normalizer hcT₁ hc1'
      (Subgroup.mem_centralizer_singleton_iff.2 hyc))

theorem exists_conjB {T T₁ : Subgroup G} (h : TCtxL T T₁)
    {E : OntoEmb H (Subgroup.normalizer (T : Set G))} (M : T1ModelL H)
    (hE : ∀ x, x ∈ M.T0 ↔ E.Φ x ∈ T) :
    ∃ n : H, ∀ x, x ∈ M.B0 ↔ E.Φ (n * x * n⁻¹) ∈ T₁ := by
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
  have hcard8 : Nat.card ↥(M.T0 ⊓ Subgroup.centralizer ({b'} : Set H)) = 8 := by
    rw [card_inf_centralizer_comap E hE, hb', h.inf_centralizer_eq hb hb1, h.norm1]
  have key : ∀ (n : H) (p : H), n * p * n⁻¹ = b' →
      p ∈ (T₁.comap (E.comp (MulAut.conj n)).Φ) := by
    intro n p hp
    show E.Φ (MulAut.conj n p) ∈ T₁
    rw [MulAut.conj_apply, hp, hb']
    exact hbT₁
  have hE₁ : ∀ n : H, ∀ x, x ∈ M.T0 ↔ (E.comp (MulAut.conj n)).Φ x ∈ T := by
    intro n x
    simp only [OntoEmb.comp_Φ_apply, MulAut.conj_apply, map_mul, map_inv]
    rw [hE x]
    exact Subgroup.mem_normalizer_iff.1 (E.mem n) (E.Φ x)
  rcases M.inv_class b' hb'2 hb'T hcard8 with ⟨n, hn⟩ | ⟨n, hn⟩
  · have hB0 := M.klein_eq _ (key n M.b0 hn) (isAdmL_comap h _ (hE₁ n))
    refine ⟨n, fun x => ?_⟩
    rw [← hB0]
    show E.Φ (MulAut.conj n x) ∈ T₁ ↔ _
    rw [MulAut.conj_apply]
  · exact (M.klein_none _ (key n M.c0 hn) (isAdmL_comap h _ (hE₁ n))).elim

end CFSG.CGT.L5R
