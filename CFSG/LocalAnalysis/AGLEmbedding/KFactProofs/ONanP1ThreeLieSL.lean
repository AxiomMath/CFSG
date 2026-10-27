module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanP1ThreeLieWeakCore
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanP1ThreeLieDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCharPGenSL

public section

namespace CFSG.AGLEmbedding.P1Lie

open CFSG.Open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.PreuniquenessRankFour.Helpers

section SL

open CFSG.LieType.Universal.SpecialLinear CFSG.LieType.Steinberg.SL

@[expose] def ind (m a b : ℕ) : Fin m → ℤ := fun k => if a ≤ k.val ∧ k.val < b then 1 else 0

theorem toStd_ind {m a b : ℕ} (hab : a < b) (hb : b ≤ m) :
    toStd m (ind m a b) = Pi.single (⟨a, by omega⟩ : Fin (m + 1)) 1 -
      Pi.single (⟨b, by omega⟩ : Fin (m + 1)) 1 := by
  funext x
  simp only [toStd, ind, Pi.sub_apply, Pi.single_apply, Fin.ext_iff]
  split_ifs <;> omega

theorem ind_mem_roots {m a b : ℕ} (hab : a < b) (hb : b ≤ m) :
    ind m a b ∈ roots (isFiniteType_A m) ∅ := by
  rw [roots_eq]
  exact ⟨⟨a, by omega⟩, ⟨b, by omega⟩, by simp [Fin.ext_iff]; omega, toStd_ind hab hb⟩

theorem pairOf_ind {m a b : ℕ} (hab : a < b) (hb : b ≤ m) :
    pairOf m (ind m a b) = (⟨a, by omega⟩, ⟨b, by omega⟩) :=
  pairOf_eq (by simp [Fin.ext_iff]; omega) (toStd_ind hab hb)


variable {m : ℕ} {F : Type} [Field F]

theorem ind_inj {a b c d : ℕ} (hab : a < b) (hb : b ≤ m) (hcd : c < d) (hd : d ≤ m)
    (h : ind m a b = ind m c d) : a = c ∧ b = d := by
  have := congrArg (pairOf m) h
  rw [pairOf_ind hab hb, pairOf_ind hcd hd] at this
  simp only [Prod.mk.injEq, Fin.mk.injEq] at this
  exact this

theorem commRoots_ind {a b c d : ℕ} (hab : a < b) (hb : b ≤ m) (hcd : c < d) (hd : d ≤ m)
    (hbc : b ≠ c) (hda : d ≠ a) (hne : (a, b) ≠ (c, d)) :
    CommRoots (rootDatum m F) (ind m a b) (ind m c d) := by
  have hα := ind_mem_roots hab hb
  have hβ := ind_mem_roots hcd hd
  have hαβ : ind m a b + ind m c d ≠ 0 := by
    intro h
    have h1 := congrFun h ⟨a, by omega⟩
    simp only [Pi.add_apply, ind, Pi.zero_apply] at h1
    split_ifs at h1 <;> omega
  constructor
  · by_contra h
    rcases eq_or_eq_neg_of_not_linIndepPair (isFiniteType_A m) rfl hα hβ h with h1 | h1
    · exact hne (by
        obtain ⟨e1, e2⟩ := ind_inj hcd hd hab hb h1
        rw [e1, e2])
    · have h2 : toStd m (ind m c d) = Pi.single (⟨b, by omega⟩ : Fin (m + 1)) 1 -
          Pi.single (⟨a, by omega⟩ : Fin (m + 1)) 1 := by
        rw [h1, toStd_neg, toStd_ind hab hb, neg_sub]
      have h3 := pairOf_eq (by simp [Fin.ext_iff]; omega) h2
      rw [pairOf_ind hcd hd] at h3
      simp only [Prod.mk.injEq, Fin.mk.injEq] at h3
      omega
  · ext ε
    simp only [openCone, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨hε, a', b', ha, hb', rfl⟩
    have hmem : (a', b') ∈ expPairs (Φ (m := m) (F := F)) (ind m a b) (ind m c d) :=
      ⟨ha, hb', hε⟩
    rw [mem_expPairs_iff hα hβ hαβ] at hmem
    obtain ⟨-, hchain⟩ := hmem
    rw [Chain, pairOf_ind hab hb, pairOf_ind hcd hd] at hchain
    rcases hchain with h | h
    · exact hbc (by simpa [Fin.ext_iff] using h)
    · exact hda (by simpa [Fin.ext_iff] using h)

theorem ind_mem_posExcept {a b : ℕ} (hab : a < b) (hb : b ≤ m) (i : Fin m)
    (hi : a ≠ i.val ∨ a + 2 ≤ b) :
    ind m a b ∈ (Φ (m := m) (F := F)).posExcept i := by
  by_cases h : a = i.val
  · have h2 : a + 2 ≤ b := hi.resolve_left (by omega)
    refine (Φ (m := m) (F := F)).mem_posExcept_of_pos (j := ⟨a + 1, by omega⟩)
      (ind_mem_roots hab hb) ?_ ?_
    · simp [Fin.ext_iff]; omega
    · simp [ind]; omega
  · refine (Φ (m := m) (F := F)).mem_posExcept_of_pos (j := ⟨a, by omega⟩)
      (ind_mem_roots hab hb) ?_ ?_
    · simp [Fin.ext_iff]; omega
    · simp [ind]; omega

theorem ind_ne_two_smul {a b : ℕ} (hab : a < b) (hb : b ≤ m) :
    ∀ δ ∈ (rootDatum m F).roots, ind m a b ≠ 2 • δ := fun _ hδ e =>
  two_smul_notMem_roots (isFiniteType_A m) rfl hδ (e ▸ ind_mem_roots hab hb)


theorem weakCore_sl_of_commuting {p : ℕ} (hp : p.Prime) [Finite F] (hrank : 2 ≤ m)
    (w : (Fin m → ℤ) → ℕ)
    (hroot : ∀ γ ∈ (rootDatum m F).roots, ∃ E ≤ (rootDatum m F).rootGroup γ,
      IsElemAbelian p E ∧ p ^ w γ ≤ Nat.card E)
    (hS : ∀ i : Fin m, ∃ S : Finset (Fin m → ℤ),
      (∀ γ ∈ S, γ ∈ (Φ (m := m) (F := F)).posExcept i ∧
        ∀ δ ∈ (rootDatum m F).roots, γ ≠ 2 • δ) ∧
      (∀ γ ∈ S, ∀ δ ∈ S, γ ≠ δ → CommRoots (rootDatum m F) γ δ) ∧ 3 ≤ ∑ γ ∈ S, w γ) :
    GLBWeakCore p (posUnipotent (rootDatum m F)) = ⊤ :=
  weakCore_posUnipotent_eq_top_of_commuting (isCTGroupDatum m F) (steinbergExtras m F) hp hrank w
    hroot hS

theorem weakCore_sl {p f : ℕ} (hp : p.Prime) [CharP F p] [Finite F] (hF : Nat.card F = p ^ f)
    (hm : 3 ≤ m ∨ (m = 2 ∧ 2 ≤ f)) :
    GLBWeakCore p (posUnipotent (rootDatum m F)) = ⊤ := by
  classical
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · have h1 : Nat.card F = 1 := by simpa using hF
      have h2 : 1 < Nat.card F := Finite.one_lt_card
      omega
    · exact h
  have hrank : 2 ≤ m := by omega
  refine weakCore_sl_of_commuting hp hrank (fun _ => f) ?_ ?_
  · intro γ hγ
    obtain ⟨hE, hcard⟩ := isElemAbelian_card_of_isParametrization (p := p) isParametrization hγ
    exact ⟨_, le_rfl, hE, by rw [hcard, hF]⟩
  · intro i
    rcases hm with hm | ⟨rfl, hf⟩
    · refine ⟨({ind m 0 2, ind m 0 3, ind m 1 3} : Finset (Fin m → ℤ)), ?_, ?_, ?_⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton]
        rintro γ (rfl | rfl | rfl)
        · exact ⟨ind_mem_posExcept (by omega) (by omega) i (Or.inr (by omega)),
            ind_ne_two_smul (by omega) (by omega)⟩
        · exact ⟨ind_mem_posExcept (by omega) (by omega) i (Or.inr (by omega)),
            ind_ne_two_smul (by omega) (by omega)⟩
        · exact ⟨ind_mem_posExcept (by omega) (by omega) i (Or.inr (by omega)),
            ind_ne_two_smul (by omega) (by omega)⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton]
        rintro γ (rfl | rfl | rfl) δ (rfl | rfl | rfl) hne
        · exact absurd rfl hne
        · exact commRoots_ind (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            (by simp)
        · exact commRoots_ind (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            (by simp)
        · exact commRoots_ind (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            (by simp)
        · exact absurd rfl hne
        · exact commRoots_ind (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            (by simp)
        · exact commRoots_ind (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            (by simp)
        · exact commRoots_ind (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            (by simp)
        · exact absurd rfl hne
      · have h1 : ind m 0 2 ∉ ({ind m 0 3, ind m 1 3} : Finset (Fin m → ℤ)) := by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨fun h => by have := ind_inj (by omega) (by omega) (by omega) (by omega) h; omega,
            fun h => by have := ind_inj (by omega) (by omega) (by omega) (by omega) h; omega⟩
        have h2 : ind m 0 3 ∉ ({ind m 1 3} : Finset (Fin m → ℤ)) := by
          simp only [Finset.mem_singleton]
          exact fun h => by have := ind_inj (by omega) (by omega) (by omega) (by omega) h; omega
        rw [Finset.sum_insert h1, Finset.sum_insert h2, Finset.sum_singleton]
        omega
    · have hi : i.val = 0 ∨ i.val = 1 := by have := i.isLt; omega
      rcases hi with hi | hi
      · refine ⟨({ind 2 1 2, ind 2 0 2} : Finset (Fin 2 → ℤ)), ?_, ?_, ?_⟩
        · simp only [Finset.mem_insert, Finset.mem_singleton]
          rintro γ (rfl | rfl)
          · exact ⟨ind_mem_posExcept (by omega) (by omega) i (Or.inl (by omega)),
              ind_ne_two_smul (by omega) (by omega)⟩
          · exact ⟨ind_mem_posExcept (by omega) (by omega) i (Or.inr (by omega)),
              ind_ne_two_smul (by omega) (by omega)⟩
        · simp only [Finset.mem_insert, Finset.mem_singleton]
          rintro γ (rfl | rfl) δ (rfl | rfl) hne
          · exact absurd rfl hne
          · exact commRoots_ind (by omega) (by omega) (by omega) (by omega) (by omega)
              (by omega) (by simp)
          · exact commRoots_ind (by omega) (by omega) (by omega) (by omega) (by omega)
              (by omega) (by simp)
          · exact absurd rfl hne
        · have h1 : ind 2 1 2 ∉ ({ind 2 0 2} : Finset (Fin 2 → ℤ)) := by
            simp only [Finset.mem_singleton]
            exact fun h => by have := ind_inj (by omega) (by omega) (by omega) (by omega) h; omega
          rw [Finset.sum_insert h1, Finset.sum_singleton]
          omega
      · refine ⟨({ind 2 0 1, ind 2 0 2} : Finset (Fin 2 → ℤ)), ?_, ?_, ?_⟩
        · simp only [Finset.mem_insert, Finset.mem_singleton]
          rintro γ (rfl | rfl)
          · exact ⟨ind_mem_posExcept (by omega) (by omega) i (Or.inl (by omega)),
              ind_ne_two_smul (by omega) (by omega)⟩
          · exact ⟨ind_mem_posExcept (by omega) (by omega) i (Or.inr (by omega)),
              ind_ne_two_smul (by omega) (by omega)⟩
        · simp only [Finset.mem_insert, Finset.mem_singleton]
          rintro γ (rfl | rfl) δ (rfl | rfl) hne
          · exact absurd rfl hne
          · exact commRoots_ind (by omega) (by omega) (by omega) (by omega) (by omega)
              (by omega) (by simp)
          · exact commRoots_ind (by omega) (by omega) (by omega) (by omega) (by omega)
              (by omega) (by simp)
          · exact absurd rfl hne
        · have h1 : ind 2 0 1 ∉ ({ind 2 0 2} : Finset (Fin 2 → ℤ)) := by
            simp only [Finset.mem_singleton]
            exact fun h => by have := ind_inj (by omega) (by omega) (by omega) (by omega) h; omega
          rw [Finset.sum_insert h1, Finset.sum_singleton]
          omega

end SL

section SLGroup

open CFSG.AGLEmbedding.CharPGen CFSG.LieType.Universal.SpecialLinear

theorem exists_pGroup_weakCore_sl {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F]
    {p f : ℕ} [Fact p.Prime] [CharP F p] (hF : Nat.card F = p ^ f) {r : ℕ}
    (hr : 3 ≤ r ∨ (r = 2 ∧ 2 ≤ f))
    (e : G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin (r + 1)) F) :
    ∃ P : Subgroup G, IsPGroup p P ∧ GLBWeakCore p P = ⊤ := by
  have hext := steinbergExtras r F
  have hX : ∀ γ ∈ (rootDatum r F).roots, IsPGroup p ((rootDatum r F).rootGroup γ) := fun γ hγ =>
    isPGroup_of_isParametrization SL.isParametrization hγ
  have hU : IsPGroup p (posUnipotent (rootDatum r F)) := isPGroup_iSup_pos hext hX
  let π : Matrix.SpecialLinearGroup (Fin (r + 1)) F →* G :=
    e.symm.toMonoidHom.comp (QuotientGroup.mk' _)
  have hπ : Function.Surjective π := e.symm.surjective.comp (QuotientGroup.mk'_surjective _)
  have hinj : ∀ x ∈ posUnipotent (rootDatum r F), π x = 1 → x = 1 := by
    intro x hx hx1
    have hmk : (QuotientGroup.mk' _ x : Matrix.ProjectiveSpecialLinearGroup (Fin (r + 1)) F) = 1 :=
      e.symm.injective (by rw [map_one]; exact hx1)
    obtain ⟨k, hk⟩ := hU ⟨x, hx⟩
    exact eq_one_of_mem_center_of_pow ((QuotientGroup.eq_one_iff x).1 hmk)
      (congrArg Subtype.val hk)
  exact ⟨(posUnipotent (rootDatum r F)).map π, hU.map π,
    weakCore_map_eq_top Fact.out π hπ hinj (weakCore_sl Fact.out hF hr)⟩

end SLGroup

end CFSG.AGLEmbedding.P1Lie

namespace CFSG.AGLEmbedding

open CFSG.Open

@[expose] def IsWeakSLIndex (d : TauCeti.ValidLieTypeIndex) : Prop :=
  ∃ (r : ℕ) (q : TauCeti.PrimePower), 2 ≤ r ∧ d.1 = .A r q ∧ (3 ≤ r ∨ 2 ≤ q.exponent)

theorem weakCharPGenAt_sl : WeakCharPGenAt IsWeakSLIndex := by
  intro K _ _ _ _ d ⟨r, q, hr, hd, hcond⟩ ⟨e⟩ p hp hp2 hchar hrank T
  obtain ⟨⟨d, hv⟩, rfl⟩ : ∃ d' : {d : TauCeti.LieTypeIndex // d.Valid}, d' = d := ⟨d, rfl⟩
  simp only at hd hchar
  subst hd
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hpq : p = q.p := by simpa using hchar
  subst hpq
  have hcond' : 3 ≤ r ∨ (r = 2 ∧ 2 ≤ q.exponent) := by
    by_cases h3 : 3 ≤ r
    · exact Or.inl h3
    · exact Or.inr ⟨by omega, hcond.resolve_left h3⟩
  obtain ⟨P, hP, hcore⟩ := P1Lie.exists_pGroup_weakCore_sl
    (GaloisField.card q.p q.exponent q.exponent_pos.ne') hcond'
    (e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r q hv))
  exact P1Lie.weakCore_eq_top_of_pGroup hp hP hcore T

end CFSG.AGLEmbedding
