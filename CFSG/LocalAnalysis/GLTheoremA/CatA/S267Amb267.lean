module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267Conc267

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA

section Amb

variable {G : Type} [Group G] [Finite G]

theorem coversMod_map_inj {A : Type} [Group A] [Finite A] {p : ℕ} (hp : p.Prime) (π : A →* G)
    (hπ : Function.Injective π) {U₀ J₀ : Subgroup A}
    (hcov : CoversMod p (Subgroup.normalizer (U₀ : Set A)) J₀) :
    CoversMod p (Subgroup.normalizer ((U₀.map π : Subgroup G) : Set G)) (J₀.map π) := by
  have hker : ¬ p ∣ Nat.card π.ker := by
    rw [(MonoidHom.ker_eq_bot_iff π).2 hπ, Subgroup.card_bot]
    exact hp.not_dvd_one
  have hOJ : (GLAPPrimeCoreOf p J₀).map π = GLAPPrimeCoreOf p (J₀.map π) :=
    map_glaPPrimeCoreOf hp π hker _
  have h1 := congrArg (Subgroup.map π) hcov
  unfold CoversMod at hcov ⊢
  rw [Subgroup.map_sup, hOJ] at h1
  refine le_antisymm (sup_le inf_le_right (Subgroup.map_subtype_le _)) ?_
  refine h1.symm.le.trans (sup_le ?_ le_sup_right)
  exact ((Subgroup.map_inf_le _ _ _).trans (inf_le_inf_right _
    (Subgroup.le_normalizer_map _))).trans le_sup_left

theorem coversMod_inf_of_le {p : ℕ} {X N J : Subgroup G} (hJ : J ≤ X) (h : CoversMod p N J) :
    CoversMod p (X ⊓ N) J := by
  unfold CoversMod at h ⊢
  have : X ⊓ N ⊓ J = N ⊓ J := by
    ext x; constructor
    · rintro ⟨⟨_, hN⟩, hJx⟩; exact ⟨hN, hJx⟩
    · rintro ⟨hN, hJx⟩; exact ⟨⟨hJ hJx, hN⟩, hJx⟩
  rw [this]; exact h

theorem gConcA12_of_amb {p : ℕ} (hp : p.Prime) {X : Subgroup G} (H : Subgroup G) (hHX : H ≤ X)
    (K₀ B₀ : Subgroup ↥H) (h : S267ConcA12 p K₀ B₀) :
    ∃ B' D J : Subgroup G, IsElemAbelian p B' ∧ B' ≤ X ∧ InD p B' 1 (K₀.map H.subtype) D J ∧
      (B' = (B₀.map H.subtype) ∨ (Nat.card (B₀.map H.subtype) ≤ Nat.card B' ∧ ∃ T : Subgroup G, T ≤ X ∧ T ≠ ⊥ ∧ IsPGroup 2 T ∧
        B' ≤ Subgroup.normalizer (T : Set G))) ∧
      Nat.card ↥(B' ⊓ centModSubgroup p (K₀.map H.subtype)) = p := by
  classical
  have hinj : Function.Injective H.subtype := H.subtype_injective
  have hc : ∀ P : Subgroup ↥H, Nat.card (P.map H.subtype) = Nat.card P := fun P =>
    Subgroup.card_map_of_injective hinj
  have hle : ∀ P : Subgroup ↥H, P.map H.subtype ≤ X := fun P =>
    (Subgroup.map_subtype_le P).trans hHX
  obtain ⟨B', D, J, hBel, hIn, hcase, hcard⟩ := h
  refine ⟨B'.map H.subtype, D.map H.subtype, J.map H.subtype,
    CFSG.SectionRank.isElemAbelian_map hBel _, hle B', inD_map_inj hp H.subtype hinj hIn, ?_, ?_⟩
  · rcases hcase with rfl | ⟨hle', T, hT0, hT2, hTn⟩
    · exact Or.inl rfl
    · refine Or.inr ⟨by rw [hc, hc]; exact hle', T.map H.subtype, hle T,
        fun h => hT0 ((Subgroup.map_eq_bot_iff_of_injective T hinj).1 h), hT2.map _, ?_⟩
      exact (Subgroup.map_mono hTn).trans (Subgroup.le_normalizer_map _)
  · have hmapcm : (B' ⊓ centModSubgroup p K₀).map H.subtype =
        B'.map H.subtype ⊓ centModSubgroup p (K₀.map H.subtype) := by
      apply le_antisymm
      · rintro _ ⟨x, ⟨hxB, hxC⟩, rfl⟩
        exact ⟨⟨x, hxB, rfl⟩, (mem_centModSubgroup_map_iff_inj hp H.subtype hinj).1 hxC⟩
      · rintro _ ⟨⟨x, hxB, rfl⟩, hyC⟩
        exact ⟨x, ⟨hxB, (mem_centModSubgroup_map_iff_inj hp H.subtype hinj).2 hyC⟩, rfl⟩
    rw [← hmapcm, hc]; exact hcard

theorem gConcACov_of_amb {p : ℕ} (hp : p.Prime) {X : Subgroup G} (H : Subgroup G) (hHX : H ≤ X)
    (K₀ B₀ : Subgroup ↥H) (h : S267ConcACov p K₀ B₀) :
    ∃ B' D J : Subgroup G, IsElemAbelian p B' ∧ B' ≤ X ∧ InD p B' 1 (K₀.map H.subtype) D J ∧
      (B' = (B₀.map H.subtype) ∨ (Nat.card (B₀.map H.subtype) ≤ Nat.card B' ∧ ∃ T : Subgroup G, T ≤ X ∧ T ≠ ⊥ ∧ IsPGroup 2 T ∧
        B' ≤ Subgroup.normalizer (T : Set G))) ∧
      Nat.card ↥(B' ⊓ centModSubgroup p (K₀.map H.subtype)) = p ∧
      ∃ T : Subgroup G, T ≤ X ∧ T ≠ ⊥ ∧ IsPGroup 2 T ∧ D ≤ Subgroup.normalizer (T : Set G) ∧
        CoversMod p (X ⊓ Subgroup.normalizer (T : Set G)) J := by
  classical
  have hinj : Function.Injective H.subtype := H.subtype_injective
  have hle : ∀ P : Subgroup ↥H, P.map H.subtype ≤ X := fun P =>
    (Subgroup.map_subtype_le P).trans hHX
  obtain ⟨B', D, J, hBel, hIn, hcase, hcard, T, hT0, hT2, hDT, hcov⟩ := h
  have hc : ∀ P : Subgroup ↥H, Nat.card (P.map H.subtype) = Nat.card P := fun P =>
    Subgroup.card_map_of_injective hinj
  refine ⟨B'.map H.subtype, D.map H.subtype, J.map H.subtype,
    CFSG.SectionRank.isElemAbelian_map hBel _, hle B', inD_map_inj hp H.subtype hinj hIn, ?_, ?_, ?_⟩
  · rcases hcase with rfl | ⟨hle', T₁, hT₁0, hT₁2, hT₁n⟩
    · exact Or.inl rfl
    · refine Or.inr ⟨by rw [hc, hc]; exact hle', T₁.map H.subtype, hle T₁,
        fun h => hT₁0 ((Subgroup.map_eq_bot_iff_of_injective T₁ hinj).1 h), hT₁2.map _, ?_⟩
      exact (Subgroup.map_mono hT₁n).trans (Subgroup.le_normalizer_map _)
  · have hmapcm : (B' ⊓ centModSubgroup p K₀).map H.subtype =
        B'.map H.subtype ⊓ centModSubgroup p (K₀.map H.subtype) := by
      apply le_antisymm
      · rintro _ ⟨x, ⟨hxB, hxC⟩, rfl⟩
        exact ⟨⟨x, hxB, rfl⟩, (mem_centModSubgroup_map_iff_inj hp H.subtype hinj).1 hxC⟩
      · rintro _ ⟨⟨x, hxB, rfl⟩, hyC⟩
        exact ⟨x, ⟨hxB, (mem_centModSubgroup_map_iff_inj hp H.subtype hinj).2 hyC⟩, rfl⟩
    rw [← hmapcm, hc]; exact hcard
  · refine ⟨T.map H.subtype, hle T, fun h => hT0 ((Subgroup.map_eq_bot_iff_of_injective T hinj).1 h),
      hT2.map _, (Subgroup.map_mono hDT).trans (Subgroup.le_normalizer_map _), ?_⟩
    exact coversMod_inf_of_le (hle J) (coversMod_map_inj hp H.subtype hinj hcov)

theorem gConcBCDE_of_amb {p q : ℕ} (hp : p.Prime) (H : Subgroup G) (K₀ B₀ : Subgroup ↥H)
    (h : S267ConcBCDE p q K₀ B₀) :
    S267ConcBCDE p q (K₀.map H.subtype) (B₀.map H.subtype) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hinj : Function.Injective H.subtype := H.subtype_injective
  have hc : ∀ P : Subgroup ↥H, Nat.card (P.map H.subtype) = Nat.card P := fun P =>
    Subgroup.card_map_of_injective hinj
  obtain ⟨e₀⟩ := nonempty_pQuot_equiv_map hp (show ¬ p ∣ Nat.card H.subtype.ker by
    rw [(MonoidHom.ker_eq_bot_iff H.subtype).2 hinj, Subgroup.card_bot]; exact hp.not_dvd_one) K₀
  let e₁ : PSimple p K₀ ≃* PSimple p (K₀.map H.subtype) :=
    QuotientGroup.congr _ _ e₀ (Subgroup.map_center_eq e₀)
  have hLie : ∀ d, pSimpleIsLie p K₀ d → pSimpleIsLie p (K₀.map H.subtype) d := fun d hd =>
    (catalogIs_congr e₁).1 hd
  have hcen : Subgroup.center (PQuot p K₀) = ⊥ → Subgroup.center (PQuot p (K₀.map H.subtype)) = ⊥ := by
    intro hcz
    have := Subgroup.map_center_eq e₀
    rw [hcz, Subgroup.map_bot] at this
    exact this.symm
  have hmapcm : (B₀ ⊓ centModSubgroup p K₀).map H.subtype =
      B₀.map H.subtype ⊓ centModSubgroup p (K₀.map H.subtype) := by
    apply le_antisymm
    · rintro _ ⟨x, ⟨hxB, hxC⟩, rfl⟩
      exact ⟨⟨x, hxB, rfl⟩, (mem_centModSubgroup_map_iff_inj hp H.subtype hinj).1 hxC⟩
    · rintro _ ⟨⟨x, hxB, rfl⟩, hyC⟩
      exact ⟨x, ⟨hxB, (mem_centModSubgroup_map_iff_inj hp H.subtype hinj).2 hyC⟩, rfl⟩
  have hmapK : (B₀ ⊓ K₀).map H.subtype = B₀.map H.subtype ⊓ K₀.map H.subtype := by
    apply le_antisymm (Subgroup.map_inf_le _ _ _)
    rintro _ ⟨⟨x, hxB, rfl⟩, ⟨y, hyK, hyx⟩⟩
    have : y = x := hinj hyx
    subst this
    exact ⟨y, ⟨hxB, hyK⟩, rfl⟩
  have hsup : B₀ = (B₀ ⊓ centModSubgroup p K₀) ⊔ (B₀ ⊓ K₀) →
      B₀.map H.subtype = (B₀.map H.subtype ⊓ centModSubgroup p (K₀.map H.subtype)) ⊔
        (B₀.map H.subtype ⊓ K₀.map H.subtype) := by
    intro hs
    conv_lhs => rw [hs]
    rw [Subgroup.map_sup, hmapcm, hmapK]
  have hinf : (B₀ ⊓ centModSubgroup p K₀) ⊓ (B₀ ⊓ K₀) = ⊥ →
      (B₀.map H.subtype ⊓ centModSubgroup p (K₀.map H.subtype)) ⊓
        (B₀.map H.subtype ⊓ K₀.map H.subtype) = ⊥ := by
    intro hb
    have h1 : ((B₀ ⊓ centModSubgroup p K₀) ⊓ (B₀ ⊓ K₀)).map H.subtype =
        (B₀.map H.subtype ⊓ centModSubgroup p (K₀.map H.subtype)) ⊓
          (B₀.map H.subtype ⊓ K₀.map H.subtype) := by
      apply le_antisymm (by
        refine (Subgroup.map_inf_le _ _ _).trans ?_
        rw [hmapcm, hmapK])
      rintro _ ⟨⟨hy1, hy2⟩, ⟨hy3, hy4⟩⟩
      have hy1' := hy1
      obtain ⟨x, hxB, rfl⟩ := hy1'
      have hx1 : x ∈ B₀ ⊓ centModSubgroup p K₀ := by
        rw [← Subgroup.mem_map_iff_mem hinj, hmapcm]; exact ⟨hy1, hy2⟩
      have hx2 : x ∈ B₀ ⊓ K₀ := by
        rw [← Subgroup.mem_map_iff_mem hinj, hmapK]; exact ⟨hy3, hy4⟩
      exact ⟨x, ⟨hx1, hx2⟩, rfl⟩
    rw [← h1, hb, Subgroup.map_bot]
  rcases h with ⟨h4, h3, Q, hQq, hQ⟩ | ⟨h4, hsb, hib, hcb, Q, hQq, hQ⟩ | ⟨h4, hsb, hib, hcb, Q, hQq, hQ, hdiv⟩ |
    ⟨h4, h4', hcb, Q, hQq, hQ, hdiv⟩
  · refine Or.inl ⟨by rw [hc]; exact h4, h3, Q, hQq, ?_⟩
    rcases hQ with ⟨hQ, hd⟩ | ⟨hQ, hd⟩
    · exact Or.inl ⟨hLie _ hQ, hd⟩
    · exact Or.inr ⟨hLie _ hQ, hd⟩
  · refine Or.inr (Or.inl ⟨by rw [hc]; exact h4, hsup hsb, hinf hib, hcen hcb, Q, hQq, ?_⟩)
    rcases hQ with ⟨hQ, hd⟩ | ⟨hQ, hd⟩
    · exact Or.inl ⟨hLie _ hQ, hd⟩
    · exact Or.inr ⟨hLie _ hQ, hd⟩
  · refine Or.inr (Or.inr (Or.inl ⟨by rw [hc]; exact h4, hsup hsb, hinf hib, hcen hcb, Q, hQq, ?_, hdiv⟩))
    rcases hQ with hQ | hQ
    · exact Or.inl (hLie _ hQ)
    · exact Or.inr (hLie _ hQ)
  · refine Or.inr (Or.inr (Or.inr ⟨?_, by rw [← hmapK, hc]; exact h4', hcen hcb, Q, hQq, hLie _ hQ, hdiv⟩))
    rcases h4 with h | h
    · exact Or.inl (by rw [hc]; exact h)
    · exact Or.inr (by rw [hc]; exact h)

end Amb

end CFSG.LocalAnalysis.GLTheoremA.S267

end
