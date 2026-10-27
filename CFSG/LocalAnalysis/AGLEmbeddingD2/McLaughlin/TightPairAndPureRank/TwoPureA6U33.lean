module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.PairTRFrontier
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.RowFixed

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.Quasithin
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def shear3k {k : ℕ} (v : Fin k → ZMod 3) : Equiv.Perm (Fin k × ZMod 3) :=
  Equiv.prodShear (Equiv.refl _) fun i => Equiv.addRight (v i)

theorem shear3k_apply {k : ℕ} (v : Fin k → ZMod 3) (x : Fin k × ZMod 3) :
    shear3k v x = (x.1, x.2 + v x.1) :=
  rfl

@[expose] def shearHomK (k m : ℕ) :
    Multiplicative (Fin k → ZMod 3) →* Equiv.Perm ((Fin k × ZMod 3) ⊕ Fin m) where
  toFun v := Equiv.sumCongr (shear3k (Multiplicative.toAdd v)) (Equiv.refl _)
  map_one' := by
    ext x
    rcases x with x | x <;> simp [shear3k_apply]
  map_mul' v w := by
    ext x
    rcases x with x | x
    · simp only [Equiv.sumCongr_apply, Sum.map_inl, Equiv.Perm.coe_mul, Function.comp_apply,
        shear3k_apply, toAdd_mul, Pi.add_apply]
      congr 2
      ring
    · simp

theorem shearHomK_injective (k m : ℕ) : Function.Injective (shearHomK k m) := by
  rw [injective_iff_map_eq_one]
  intro v hv
  have hv' : ∀ i : Fin k, Multiplicative.toAdd v i = 0 := by
    intro i
    have h := congrArg (fun σ : Equiv.Perm ((Fin k × ZMod 3) ⊕ Fin m) => σ (Sum.inl (i, 0))) hv
    simp only [shearHomK, MonoidHom.coe_mk, OneHom.coe_mk, Equiv.sumCongr_apply, Sum.map_inl,
      shear3k_apply, zero_add, Equiv.Perm.coe_one, id_eq, Sum.inl.injEq, Prod.mk.injEq,
      true_and] at h
    exact h
  have : Multiplicative.toAdd v = 0 := funext hv'
  exact this

theorem sign_eq_one_of_pow_three_k {α : Type*} [DecidableEq α] [Fintype α] {σ : Equiv.Perm α}
    (hσ : σ ^ 3 = 1) : Equiv.Perm.sign σ = 1 := by
  have h := congrArg Equiv.Perm.sign hσ
  rw [map_pow, map_one] at h
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1
  · exact h1
  · rw [h1] at h
    exact absurd h (by decide)

theorem le_pRank_alternatingGroup_three {N k : ℕ} (hN : 3 * k ≤ N) :
    k ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥(alternatingGroup (Fin N))) := by
  set m := N - 3 * k with hm
  let e : (Fin k × ZMod 3) ⊕ Fin m ≃ Fin N :=
    ((Equiv.sumCongr (finProdFinEquiv : Fin k × Fin 3 ≃ Fin (k * 3)) (Equiv.refl _)).trans
      finSumFinEquiv).trans (finCongr (by omega))
  set φ : Multiplicative (Fin k → ZMod 3) →* Equiv.Perm (Fin N) :=
    (e.permCongrHom).toMonoidHom.comp (shearHomK k m) with hφ
  have hφinj : Function.Injective φ :=
    (e.permCongrHom.injective).comp (shearHomK_injective k m)
  have h3 : ∀ x : ZMod 3, 3 • x = 0 := by decide
  have hpow : ∀ v : Multiplicative (Fin k → ZMod 3), v ^ 3 = 1 := by
    intro v
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one]
    funext i
    exact h3 _
  have hcomm : ∀ v w : Multiplicative (Fin k → ZMod 3), v * w = w * v := fun v w => mul_comm v w
  have hle : k ≤ CFSG.Open.pRank 3 (alternatingGroup (Fin N)) := by
    refine CFSG.SectionRank.le_pRank_of_injective (by norm_num) hcomm hpow ?_ φ hφinj ?_
    · rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, Fintype.card_fun,
        ZMod.card, Fintype.card_fin]
    · rintro _ ⟨v, rfl⟩
      rw [Equiv.Perm.mem_alternatingGroup]
      exact sign_eq_one_of_pow_three_k (by rw [← map_pow, hpow, map_one])
  rwa [CFSG.SectionRank.pRank_eq_pRank_top_subgroup] at hle

theorem two_le_pRank_alternatingGroup_six :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥(alternatingGroup (Fin 6))) :=
  le_pRank_alternatingGroup_three (k := 2) (by norm_num)

@[expose] def U33Facts : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsUThreeThree X →
    Subgroup.center X = ⊥ ∧ 2 ≤ Open.pRank 3 (⊤ : Subgroup X)

theorem IsUThreeThree.quot_of_center_bot {X : Type} [Group X] (hZ : Subgroup.center X = ⊥)
    (h : IsUThreeThree X) : IsUThreeThree (X ⧸ Subgroup.center X) := by
  obtain ⟨d, hd, ⟨e⟩⟩ := h
  exact ⟨d, hd, ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans
    (QuotientGroup.quotientBot (G := X))).trans e⟩⟩

section Pure

variable {G : Type} [Group G] [Finite G]

theorem center_barM_eq_bot (hU : U33Facts) {M L : Subgroup G}
    (h : IsA6OrU33 ↥(barM M L)) : Subgroup.center ↥(barM M L) = ⊥ := by
  rcases h with he | h
  · obtain ⟨e⟩ := he
    exact center_eq_bot_of_alt (by norm_num) e
  · exact (hU _ h).1

omit [Finite G] in
theorem not_alt_eight_of_card {X : Type} [Group X] (hc : Subgroup.center X = ⊥)
    (hn : Nat.card X ≠ 20160) :
    ¬ Nonempty (X ⧸ Subgroup.center X ≃* alternatingGroup (Fin 8)) := by
  rintro ⟨f⟩
  have h1 : Nat.card (X ⧸ Subgroup.center X) = Nat.card X :=
    Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hc).trans
      (QuotientGroup.quotientBot (G := X))).toEquiv
  have h2 : Nat.card (X ⧸ Subgroup.center X) = 20160 := by
    rw [Nat.card_congr f.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    decide
  exact hn (h1 ▸ h2)

theorem tightRow_of_isA6OrU33 (hat : U33Atlas) (hU : U33Facts) {M L : Subgroup G}
    (h : IsA6OrU33 ↥(barM M L)) :
    TightRow M L ∧ ¬ Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃*
      alternatingGroup (Fin 8)) := by
  have hc := center_barM_eq_bot hU h
  rcases h with he | h
  · obtain ⟨e⟩ := he
    refine ⟨Or.inl (quotCenterEquivAlt (by norm_num) e), not_alt_eight_of_card hc ?_⟩
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    decide
  · refine ⟨Or.inr (Or.inr (Or.inr (IsUThreeThree.quot_of_center_bot hc h))),
      not_alt_eight_of_card hc ?_⟩
    rw [(hat _ h).1]
    norm_num

end Pure

end CFSG.AGLEmbeddingD2.McLaughlin
