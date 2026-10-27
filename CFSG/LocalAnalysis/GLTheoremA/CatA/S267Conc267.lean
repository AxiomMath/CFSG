module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267Trans
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267Cover
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267Omega268

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA

@[expose] def S267ConcACov (p : ℕ) {A : Type} [Group A] [Finite A] (K B : Subgroup A) : Prop :=
  ∃ B' D J : Subgroup A, IsElemAbelian p B' ∧ InD p B' 1 K D J ∧
    (B' = B ∨ (Nat.card B ≤ Nat.card B' ∧ ∃ T : Subgroup A, T ≠ ⊥ ∧ IsPGroup 2 T ∧
      B' ≤ Subgroup.normalizer (T : Set A))) ∧
    Nat.card ↥(B' ⊓ centModSubgroup p K) = p ∧
    ∃ T : Subgroup A, T ≠ ⊥ ∧ IsPGroup 2 T ∧ D ≤ Subgroup.normalizer (T : Set A) ∧
      CoversMod p (Subgroup.normalizer (T : Set A)) J

section Core

variable {A : Type} [Group A] [Finite A]

theorem conc267_core {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (N : Subgroup A) [N.Normal]
    (hN : ¬ p ∣ Nat.card N) (K₀ B₀ : Subgroup A) (hK₀n : K₀.Normal) (hB₀ : IsElemAbelian p B₀)
    {B' D' J' : Subgroup (A ⧸ N)} (hBel : IsElemAbelian p B') (hIn : InD p B' 1 (K₀.map (QuotientGroup.mk' N)) D' J')
    (hcase : B' = B₀.map (QuotientGroup.mk' N) ∨
      (Nat.card (B₀.map (QuotientGroup.mk' N)) ≤ Nat.card B' ∧ ∃ T : Subgroup (A ⧸ N), T ≠ ⊥ ∧
        IsPGroup 2 T ∧ B' ≤ Subgroup.normalizer (T : Set (A ⧸ N))))
    (hcard : Nat.card ↥(B' ⊓ centModSubgroup p (K₀.map (QuotientGroup.mk' N))) = p) :
    ∃ B₁ D₁ J₁ : Subgroup A, IsElemAbelian p B₁ ∧ B₁.map (QuotientGroup.mk' N) = B' ∧
      D₁.map (QuotientGroup.mk' N) = D' ∧ J₁.map (QuotientGroup.mk' N) = J' ∧
      InD p B₁ 1 K₀ D₁ J₁ ∧
      (B₁ = B₀ ∨ (Nat.card B₀ ≤ Nat.card B₁ ∧ ∃ T : Subgroup A, T ≠ ⊥ ∧ IsPGroup 2 T ∧
        B₁ ≤ Subgroup.normalizer (T : Set A))) ∧
      Nat.card ↥(B₁ ⊓ centModSubgroup p K₀) = p := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set π : A →* A ⧸ N := QuotientGroup.mk' N with hπ
  have hker : ¬ p ∣ Nat.card π.ker := by rw [hπ, QuotientGroup.ker_mk']; exact hN
  have hB₀p : IsPGroup p B₀ := isPGroup_of_isElemAbelian hB₀
  have hcB₀ : Nat.card (B₀.map π) = Nat.card B₀ := card_map_of_isPGroup hp π hker hB₀p
  obtain ⟨B₁, hB₁el, hB₁map, hB₁card, hB₁B₀⟩ : ∃ B₁ : Subgroup A, IsElemAbelian p B₁ ∧ B₁.map π = B' ∧
      Nat.card B₁ = Nat.card B' ∧ (B' = B₀.map π → B₁ = B₀) := by
    by_cases hBB : B' = B₀.map π
    · exact ⟨B₀, hB₀, hBB.symm, by rw [hBB, hcB₀], fun _ => rfl⟩
    · obtain ⟨B₁, hel, hmap, hc⟩ := exists_elemAbelian_lift N hN hBel
      exact ⟨B₁, hel, hmap, hc, fun h => absurd h hBB⟩
  have hB₁K : B₁ ≤ Subgroup.normalizer (K₀ : Set A) := by
    intro g _; rw [Subgroup.normalizer_eq_top_iff.2 hK₀n]; exact Subgroup.mem_top _
  have hIn' : InD p (B₁.map π) 1 (K₀.map π) D' J' := by rw [hB₁map]; exact hIn
  obtain ⟨J₁, hJ₁map, hInD⟩ := inD_of_quot hp π hker hB₁el hB₁K hIn'
  have hDmap : (B₁ ⊓ D'.comap π).map π = D' := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩; exact hx.2
    · intro y hy
      obtain ⟨b, hb, rfl⟩ : y ∈ B₁.map π := by rw [hB₁map]; exact hIn.1.1 hy
      exact ⟨b, ⟨hb, hy⟩, rfl⟩
  refine ⟨B₁, B₁ ⊓ D'.comap π, J₁, hB₁el, hB₁map, hDmap, hJ₁map, hInD, ?_, ?_⟩
  · rcases hcase with hBB | ⟨hle, T, hT0, hT2, hTn⟩
    · exact Or.inl (hB₁B₀ hBB)
    · refine Or.inr ⟨by rw [← hcB₀, hB₁card]; exact hle, ?_⟩
      obtain ⟨T₁, hT₁2, hBT, hTmap, -, -⟩ := exists_twoGroup_lift hp hp2 N hN hT2
        (isPGroup_of_isElemAbelian hB₁el) (by rw [hB₁map]; exact hTn)
      exact ⟨T₁, fun h => hT0 (by rw [← hTmap, h, Subgroup.map_bot]), hT₁2, hBT⟩
  ·
    have hmapcm : (B₁ ⊓ centModSubgroup p K₀).map π = B' ⊓ centModSubgroup p (K₀.map π) := by
      apply le_antisymm
      · rintro _ ⟨x, ⟨hxB, hxC⟩, rfl⟩
        refine ⟨by rw [← hB₁map]; exact ⟨x, hxB, rfl⟩, ?_⟩
        exact (mem_centModSubgroup_map_iff hp π hker (hB₁K hxB)).1 hxC
      · rintro y ⟨hyB, hyC⟩
        obtain ⟨x, hxB, rfl⟩ : y ∈ B₁.map π := by rw [hB₁map]; exact hyB
        exact ⟨x, ⟨hxB, (mem_centModSubgroup_map_iff hp π hker (hB₁K hxB)).2 hyC⟩, rfl⟩
    have h1 := card_map_of_isPGroup hp π hker
      ((isPGroup_of_isElemAbelian hB₁el).to_le (inf_le_left : B₁ ⊓ centModSubgroup p K₀ ≤ B₁))
    rw [← h1, hmapcm]
    exact hcard

theorem conc267A12_of_quot {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (N : Subgroup A) [N.Normal]
    (hN : ¬ p ∣ Nat.card N) (K₀ B₀ : Subgroup A) (hK₀n : K₀.Normal) (hB₀ : IsElemAbelian p B₀)
    (h : S267ConcA12 p (K₀.map (QuotientGroup.mk' N)) (B₀.map (QuotientGroup.mk' N))) :
    S267ConcA12 p K₀ B₀ := by
  obtain ⟨B', D', J', hBel, hIn, hcase, hcard⟩ := h
  obtain ⟨B₁, D₁, J₁, hB₁el, -, -, -, hInD, hcase₁, hcard₁⟩ :=
    conc267_core hp hp2 N hN K₀ B₀ hK₀n hB₀ hBel hIn hcase hcard
  exact ⟨B₁, D₁, J₁, hB₁el, hInD, hcase₁, hcard₁⟩

theorem conc267ACov_of_quot {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (N : Subgroup A) [N.Normal]
    (hN : ¬ p ∣ Nat.card N) (K₀ B₀ : Subgroup A) (hNK : N ≤ K₀) (hK₀n : K₀.Normal)
    (hB₀ : IsElemAbelian p B₀)
    (h : S267ConcA p (K₀.map (QuotientGroup.mk' N)) (B₀.map (QuotientGroup.mk' N))) :
    S267ConcACov p K₀ B₀ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨B', D', J', hBel, hIn, hcase, hcard, t, ht1, ht2, htD, htJ⟩ := h
  obtain ⟨B₁, D₁, J₁, hB₁el, hB₁map, hD₁map, hJ₁map, hInD, hcase₁, hcard₁⟩ :=
    conc267_core hp hp2 N hN K₀ B₀ hK₀n hB₀ hBel hIn hcase hcard
  set π : A →* A ⧸ N := QuotientGroup.mk' N with hπ
  have hD₁p : IsPGroup p D₁ := (isPGroup_of_isElemAbelian hB₁el).to_le hInD.1.1
  have ht2' : IsPGroup 2 (Subgroup.zpowers t) :=
    isPGroup_of_isElemAbelian (CFSG.HardMathSupport.Solomon.Coordinator.i1020_isElemAbelian_zpowers ht2)
  have hDnorm : D₁.map π ≤ Subgroup.normalizer ((Subgroup.zpowers t : Subgroup (A ⧸ N)) : Set (A ⧸ N)) := by
    rw [hD₁map]
    intro d hd
    exact mem_normalizer_zpowers_of_comm (htD d hd)
  have hJnorm : J₁.map π ≤ Subgroup.normalizer ((Subgroup.zpowers t : Subgroup (A ⧸ N)) : Set (A ⧸ N)) := by
    rw [hJ₁map]
    intro j hj
    exact mem_normalizer_zpowers_of_comm (htJ j hj)
  obtain ⟨T, hT2, hTmap, hDT, hcov⟩ := covers_of_lift hp hp2 N hN ht2' (M := K₀) (D := D₁) (J := J₁)
    hNK hD₁p hInD.2.1.1 hDnorm hJnorm
  refine ⟨B₁, D₁, J₁, hB₁el, hInD, hcase₁, hcard₁, T, ?_, hT2, hDT, hcov⟩
  intro h
  rw [h, Subgroup.map_bot] at hTmap
  exact ht1 (Subgroup.zpowers_eq_bot.1 hTmap.symm)

end Core

section BCDE

variable {A : Type} [Group A] [Finite A]

theorem map_inf_of_ker_le {Ω : Type*} [Group Ω] (π : A →* Ω) {M : Subgroup A} (hM : π.ker ≤ M)
    (B₀ : Subgroup A) : (B₀ ⊓ M).map π = B₀.map π ⊓ M.map π := by
  apply le_antisymm (Subgroup.map_inf_le _ _ _)
  rintro y ⟨⟨b, hb, rfl⟩, ⟨k, hk, hky⟩⟩
  refine ⟨b, ⟨hb, ?_⟩, rfl⟩
  have h1 : k⁻¹ * b ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hky, inv_mul_cancel]
  have := M.mul_mem hk (hM h1)
  simpa using this

theorem concBCDE_of_quot {p q : ℕ} (hp : p.Prime) (N : Subgroup A) [N.Normal]
    (hN : ¬ p ∣ Nat.card N) (K₀ B₀ : Subgroup A) (hNK : N ≤ K₀) (hK₀n : K₀.Normal)
    (hB₀ : IsElemAbelian p B₀)
    (h : S267ConcBCDE p q (K₀.map (QuotientGroup.mk' N)) (B₀.map (QuotientGroup.mk' N))) :
    S267ConcBCDE p q K₀ B₀ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set π : A →* A ⧸ N := QuotientGroup.mk' N with hπ
  have hker : ¬ p ∣ Nat.card π.ker := by rw [hπ, QuotientGroup.ker_mk']; exact hN
  have hker' : π.ker ≤ K₀ := by rw [hπ, QuotientGroup.ker_mk']; exact hNK
  have hB₀p : IsPGroup p B₀ := isPGroup_of_isElemAbelian hB₀
  obtain ⟨e₀⟩ := nonempty_pQuot_equiv_map hp hker K₀
  let e₁ : PSimple p K₀ ≃* PSimple p (K₀.map π) := QuotientGroup.congr _ _ e₀ (Subgroup.map_center_eq e₀)
  have hcB : Nat.card B₀ = Nat.card (B₀.map π) := (card_map_of_isPGroup hp π hker hB₀p).symm
  have hLie : ∀ d, pSimpleIsLie p (K₀.map π) d → pSimpleIsLie p K₀ d := fun d hd =>
    (catalogIs_congr e₁).2 hd
  have hcen : Subgroup.center (PQuot p (K₀.map π)) = ⊥ → Subgroup.center (PQuot p K₀) = ⊥ := by
    intro hc
    have := Subgroup.map_center_eq e₀
    rw [hc] at this
    exact (Subgroup.map_eq_bot_iff_of_injective _ e₀.injective).1 this
  have hKN : B₀ ⊓ K₀ ≤ B₀ := inf_le_left
  have hBK : Nat.card ↥(B₀ ⊓ K₀) = Nat.card ↥(B₀.map π ⊓ K₀.map π) := by
    rw [← map_inf_of_ker_le π hker' B₀]
    exact (card_map_of_isPGroup hp π hker (hB₀p.to_le hKN)).symm
  have hB₀K : B₀ ≤ Subgroup.normalizer (K₀ : Set A) := by
    intro g _; rw [Subgroup.normalizer_eq_top_iff.2 hK₀n]; exact Subgroup.mem_top _
  have hmapcm : (B₀ ⊓ centModSubgroup p K₀).map π = B₀.map π ⊓ centModSubgroup p (K₀.map π) := by
    apply le_antisymm
    · rintro _ ⟨x, ⟨hxB, hxC⟩, rfl⟩
      exact ⟨⟨x, hxB, rfl⟩, (mem_centModSubgroup_map_iff hp π hker (hB₀K hxB)).1 hxC⟩
    · rintro y ⟨⟨x, hxB, rfl⟩, hyC⟩
      exact ⟨x, ⟨hxB, (mem_centModSubgroup_map_iff hp π hker (hB₀K hxB)).2 hyC⟩, rfl⟩
  have hsup : B₀.map π = (B₀.map π ⊓ centModSubgroup p (K₀.map π)) ⊔ (B₀.map π ⊓ K₀.map π) →
      B₀ = (B₀ ⊓ centModSubgroup p K₀) ⊔ (B₀ ⊓ K₀) := by
    intro hs
    have hle : (B₀ ⊓ centModSubgroup p K₀) ⊔ (B₀ ⊓ K₀) ≤ B₀ := sup_le inf_le_left inf_le_left
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    have h1 := card_map_of_isPGroup hp π hker (hB₀p.to_le hle)
    rw [← h1, Subgroup.map_sup, hmapcm, map_inf_of_ker_le π hker' B₀, ← hs, ← hcB]
  have hinf : (B₀.map π ⊓ centModSubgroup p (K₀.map π)) ⊓ (B₀.map π ⊓ K₀.map π) = ⊥ →
      (B₀ ⊓ centModSubgroup p K₀) ⊓ (B₀ ⊓ K₀) = ⊥ := by
    intro hb
    have hle : (B₀ ⊓ centModSubgroup p K₀) ⊓ (B₀ ⊓ K₀) ≤ B₀ := inf_le_left.trans inf_le_left
    have h1 := card_map_of_isPGroup hp π hker (hB₀p.to_le hle)
    have h2 : ((B₀ ⊓ centModSubgroup p K₀) ⊓ (B₀ ⊓ K₀)).map π = ⊥ := by
      refine le_bot_iff.1 ((Subgroup.map_inf_le _ _ _).trans ?_)
      rw [hmapcm, map_inf_of_ker_le π hker' B₀, hb]
    rw [h2, Subgroup.card_bot] at h1
    exact Subgroup.eq_bot_of_card_eq _ h1.symm
  rcases h with ⟨h4, h3, Q, hQq, hQ⟩ | ⟨h4, hsb, hib, hcb, Q, hQq, hQ⟩ | ⟨h4, hsb, hib, hcb, Q, hQq, hQ, hdiv⟩ |
    ⟨h4, h4', hcb, Q, hQq, hQ, hdiv⟩
  · refine Or.inl ⟨by rw [hcB]; exact h4, h3, Q, hQq, ?_⟩
    rcases hQ with ⟨hQ, hd⟩ | ⟨hQ, hd⟩
    · exact Or.inl ⟨hLie _ hQ, hd⟩
    · exact Or.inr ⟨hLie _ hQ, hd⟩
  · refine Or.inr (Or.inl ⟨by rw [hcB]; exact h4, hsup hsb, hinf hib, hcen hcb, Q, hQq, ?_⟩)
    rcases hQ with ⟨hQ, hd⟩ | ⟨hQ, hd⟩
    · exact Or.inl ⟨hLie _ hQ, hd⟩
    · exact Or.inr ⟨hLie _ hQ, hd⟩
  · refine Or.inr (Or.inr (Or.inl ⟨by rw [hcB]; exact h4, hsup hsb, hinf hib, hcen hcb, Q, hQq, ?_, hdiv⟩))
    rcases hQ with hQ | hQ
    · exact Or.inl (hLie _ hQ)
    · exact Or.inr (hLie _ hQ)
  · refine Or.inr (Or.inr (Or.inr ⟨?_, by rw [hBK]; exact h4', hcen hcb, Q, hQq, hLie _ hQ, hdiv⟩))
    rcases h4 with h | h
    · exact Or.inl (by rw [hcB]; exact h)
    · exact Or.inr (by rw [hcB]; exact h)

end BCDE

end CFSG.LocalAnalysis.GLTheoremA.S267

end
