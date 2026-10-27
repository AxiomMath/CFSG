module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.CentreTypeTwo
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.SixLie
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding CFSG.AGLEmbeddingD2

theorem isFiveList_cases {X : Type} [Group X] (h : IsFiveList X) :
    StatedClassicalModel X .PSp 3 2 1 ∨ StatedClassicalModel X .PSp 4 2 1 ∨
      StatedClassicalModel X .POmegaMinus 4 2 1 ∨ StatedClassicalModel X .PSU 4 2 1 ∨
      StatedClassicalModel X .PSU 5 2 1 := by
  obtain ⟨d, ⟨q, hq, hd⟩, ⟨e⟩⟩ := h
  obtain ⟨d1, hv⟩ := d
  simp only at hd
  obtain ⟨hp, hf⟩ := primePower_card_two' hq
  rcases hd with rfl | rfl | rfl | rfl | rfl
  · have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even 3 q hv hp
      (by norm_num) e
    rw [hp, hf] at h
    exact Or.inl h
  · have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even 4 q hv hp
      (by norm_num) e
    rw [hp, hf] at h
    exact Or.inr (Or.inl h)
  · have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even 4 q hv hp e
    rw [hp, hf] at h
    exact Or.inr (Or.inr (Or.inl h))
  · have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 3 q hv e
    rw [hp, hf] at h
    exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 4 q hv e
    rw [hp, hf] at h
    exact Or.inr (Or.inr (Or.inr (Or.inr h)))

theorem three_coprime_center_of_isFiveList (hG : GriessAllModelsStatement) {X₀ : Type} [Group X₀]
    [Finite X₀] (hperf : Group.IsPerfect X₀) (h : IsFiveList (X₀ ⧸ Subgroup.center X₀)) :
    Nat.Coprime 3 (Nat.card (Subgroup.center X₀)) := by
  rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
  intro h3
  have hdvd := card_center_dvd_card_griessHopfMultiplier hperf (MulEquiv.refl _)
  obtain ⟨d, ⟨q, hq, hd⟩, ⟨e⟩⟩ := h
  have hq' : q.p ^ q.exponent = 2 := by rw [← TauCeti.PrimePower.card_def]; exact hq
  have hcl : IsClassicalOrG2IndexTwo d.1 := by
    rcases hd with h | h | h | h | h <;> simp [IsClassicalOrG2IndexTwo, h, hq']
  obtain ⟨r, q', hr, -, h3r⟩ :=
    three_dvd_multiplier_classicalIndexTwo hG d hcl e (h3.trans hdvd)
  rcases hd with h | h | h | h | h <;> rw [h] at hr
  · cases hr
  · cases hr
  · cases hr
  · have := (TauCeti.LieTypeIndex.twistedA.inj hr).1
    subst this
    omega
  · have := (TauCeti.LieTypeIndex.twistedA.inj hr).1
    subst this
    omega

theorem isElemAbelian_of_map {A B : Type*} [Group A] [Group B] (f : A →* B) {p : ℕ}
    {V : Subgroup A} (hinj : ∀ x ∈ V, f x = 1 → x = 1) (h : IsElemAbelian p (V.map f)) :
    IsElemAbelian p V := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun v hv => ?_⟩
  · obtain ⟨v, hv⟩ := a
    obtain ⟨w, hw⟩ := b
    have hc := h.1.is_comm.comm ⟨f v, v, hv, rfl⟩ ⟨f w, w, hw, rfl⟩
    have h1 : f ((v * w)⁻¹ * (w * v)) = 1 := by
      have := congrArg Subtype.val hc
      simp only [Subgroup.coe_mul] at this
      rw [map_mul, map_inv, map_mul, map_mul, this, inv_mul_cancel]
    have h2 := hinj _ (V.mul_mem (V.inv_mem (V.mul_mem hv hw)) (V.mul_mem hw hv)) h1
    exact Subtype.ext (inv_mul_eq_one.mp h2)
  · have h1 := h.2 (f v) ⟨v, hv, rfl⟩
    rw [← map_pow] at h1
    exact hinj _ (V.pow_mem hv p) h1

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
