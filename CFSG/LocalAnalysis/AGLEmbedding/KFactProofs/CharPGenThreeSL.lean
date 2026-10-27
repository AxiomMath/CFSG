module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CharPGenThree
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanP1ThreeLieSL

public section

namespace CFSG.AGLEmbedding.CharPGenThree

open CFSG.Open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.AGLEmbedding.P1Lie

section SL

open CFSG.LieType.Universal.SpecialLinear CFSG.LieType.Steinberg.SL

private theorem three_le_pRank_sl_triple {F : Type} [Field F] {m p : ℕ} (hp : p.Prime)
    [CharP F p] [Finite F] (hm : 3 ≤ m) (i : Fin m) :
    3 ≤ CFSG.Open.pRank p (posUnipotentExcept (SpecialLinear.rootDatum m F) i) := by
  have hext := steinbergExtras m F
  have hX : ∀ γ ∈ (SpecialLinear.rootDatum m F).roots,
      IsPGroup p ((SpecialLinear.rootDatum m F).rootGroup γ) := fun γ hγ =>
    isPGroup_of_isParametrization isParametrization hγ
  have hr : ∀ γ ∈ ({ind m 0 2, ind m 0 3, ind m 1 3} : Finset (Fin m → ℤ)),
      γ ∈ (SpecialLinear.rootDatum m F).roots ∧
        (∃ j₁ j₂ : Fin m, j₁ ≠ j₂ ∧ 0 < γ j₁ ∧ 0 < γ j₂) ∧
        ∀ δ ∈ (SpecialLinear.rootDatum m F).roots, γ ≠ 2 • δ := by
    intro γ hγ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hγ
    rcases hγ with rfl | rfl | rfl
    · exact ⟨ind_mem_roots (by omega) (by omega),
        ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp [Fin.ext_iff], by simp [ind], by simp [ind]⟩,
        ind_ne_two_smul (by omega) (by omega)⟩
    · exact ⟨ind_mem_roots (by omega) (by omega),
        ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp [Fin.ext_iff], by simp [ind], by simp [ind]⟩,
        ind_ne_two_smul (by omega) (by omega)⟩
    · exact ⟨ind_mem_roots (by omega) (by omega),
        ⟨⟨1, by omega⟩, ⟨2, by omega⟩, by simp [Fin.ext_iff], by simp [ind], by simp [ind]⟩,
        ind_ne_two_smul (by omega) (by omega)⟩
  have h12 : ind m 0 2 ≠ ind m 0 3 := fun h => by
    have := (ind_inj (a := 0) (b := 2) (c := 0) (d := 3) (by omega) (by omega) (by omega)
      (by omega) h).2
    omega
  have h13 : ind m 0 2 ≠ ind m 1 3 := fun h => by
    have := (ind_inj (a := 0) (b := 2) (c := 1) (d := 3) (by omega) (by omega) (by omega)
      (by omega) h).1
    omega
  have h23 : ind m 0 3 ≠ ind m 1 3 := fun h => by
    have := (ind_inj (a := 0) (b := 3) (c := 1) (d := 3) (by omega) (by omega) (by omega)
      (by omega) h).1
    omega
  have c12 : CommRoots (SpecialLinear.rootDatum m F) (ind m 0 2) (ind m 0 3) :=
    commRoots_ind (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by simp)
  have c13 : CommRoots (SpecialLinear.rootDatum m F) (ind m 0 2) (ind m 1 3) :=
    commRoots_ind (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by simp)
  have c23 : CommRoots (SpecialLinear.rootDatum m F) (ind m 0 3) (ind m 1 3) :=
    commRoots_ind (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by simp)
  exact three_le_pRank_of_triple (D := SpecialLinear.rootDatum m F) hext hp hX
    (γ₁ := ind m 0 2) (γ₂ := ind m 0 3) (γ₃ := ind m 1 3) hr h12 h13 h23 c12 c13 c23 i

private theorem three_le_pRank_sl_pair {F : Type} [Field F] {p f : ℕ} (hp : p.Prime)
    [CharP F p] [Finite F] (hF : Nat.card F = p ^ f) (hf : 2 ≤ f)
    (i : Fin (SpecialLinear.rootDatum 2 F).rank) :
    3 ≤ CFSG.Open.pRank p (posUnipotentExcept (SpecialLinear.rootDatum 2 F) i) := by
  classical
  have hext := steinbergExtras 2 F
  have hrank : (SpecialLinear.rootDatum 2 F).rank = 2 := rfl
  have hroot : ∀ γ ∈ (SpecialLinear.rootDatum 2 F).roots,
      ∃ E ≤ (SpecialLinear.rootDatum 2 F).rootGroup γ, IsElemAbelian p E ∧
        p ^ f ≤ Nat.card E := by
    intro γ hγ
    obtain ⟨hE, hcard⟩ := isElemAbelian_card_of_isParametrization (p := p) isParametrization hγ
    exact ⟨_, le_rfl, hE, by rw [hcard, hF]⟩
  have hi : i.val = 0 ∨ i.val = 1 := by have := i.isLt; omega
  rcases hi with hi | hi
  · have h12 : ind (SpecialLinear.rootDatum 2 F).rank 1 2 ≠
        ind (SpecialLinear.rootDatum 2 F).rank 0 2 := fun h => by
      have := (ind_inj (a := 1) (b := 2) (c := 0) (d := 2) (by omega) (by omega) (by omega)
        (by omega) h).1
      omega
    have key := sum_le_pRank_posUnipotentExcept (D := SpecialLinear.rootDatum 2 F) hext hp
      (fun _ => f) hroot (i := i)
      ({ind (SpecialLinear.rootDatum 2 F).rank 1 2,
        ind (SpecialLinear.rootDatum 2 F).rank 0 2} :
        Finset (Fin (SpecialLinear.rootDatum 2 F).rank → ℤ))
      (fun γ hγ => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hγ
        rcases hγ with rfl | rfl
        · exact ⟨ind_mem_posExcept (by omega) (by omega) i (Or.inl (by omega)),
            ind_ne_two_smul (by omega) (by omega)⟩
        · exact ⟨ind_mem_posExcept (by omega) (by omega) i (Or.inr (by omega)),
            ind_ne_two_smul (by omega) (by omega)⟩)
      (fun γ hγ δ hδ hne => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hγ hδ
        rcases hγ with rfl | rfl <;> rcases hδ with rfl | rfl
        · exact absurd rfl hne
        · exact commRoots_ind (by omega) (by omega) (by omega) (by omega) (by omega)
            (by omega) (by simp)
        · exact commRoots_ind (by omega) (by omega) (by omega) (by omega) (by omega)
            (by omega) (by simp)
        · exact absurd rfl hne)
    rw [Finset.sum_const, Finset.card_pair h12, smul_eq_mul] at key
    omega
  · have h12 : ind (SpecialLinear.rootDatum 2 F).rank 0 1 ≠
        ind (SpecialLinear.rootDatum 2 F).rank 0 2 := fun h => by
      have := (ind_inj (a := 0) (b := 1) (c := 0) (d := 2) (by omega) (by omega) (by omega)
        (by omega) h).2
      omega
    have key := sum_le_pRank_posUnipotentExcept (D := SpecialLinear.rootDatum 2 F) hext hp
      (fun _ => f) hroot (i := i)
      ({ind (SpecialLinear.rootDatum 2 F).rank 0 1,
        ind (SpecialLinear.rootDatum 2 F).rank 0 2} :
        Finset (Fin (SpecialLinear.rootDatum 2 F).rank → ℤ))
      (fun γ hγ => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hγ
        rcases hγ with rfl | rfl
        · exact ⟨ind_mem_posExcept (by omega) (by omega) i (Or.inl (by omega)),
            ind_ne_two_smul (by omega) (by omega)⟩
        · exact ⟨ind_mem_posExcept (by omega) (by omega) i (Or.inr (by omega)),
            ind_ne_two_smul (by omega) (by omega)⟩)
      (fun γ hγ δ hδ hne => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hγ hδ
        rcases hγ with rfl | rfl <;> rcases hδ with rfl | rfl
        · exact absurd rfl hne
        · exact commRoots_ind (by omega) (by omega) (by omega) (by omega) (by omega)
            (by omega) (by simp)
        · exact commRoots_ind (by omega) (by omega) (by omega) (by omega) (by omega)
            (by omega) (by simp)
        · exact absurd rfl hne)
    rw [Finset.sum_const, Finset.card_pair h12, smul_eq_mul] at key
    omega

theorem three_le_pRank_posUnipotentExcept_sl {F : Type} [Field F] {m p f : ℕ} (hp : p.Prime)
    [CharP F p] [Finite F] (hF : Nat.card F = p ^ f)
    (hm : 3 ≤ m ∨ (m = 2 ∧ 2 ≤ f)) (i : Fin m) :
    3 ≤ CFSG.Open.pRank p (posUnipotentExcept (SpecialLinear.rootDatum m F) i) := by
  rcases hm with hm | ⟨rfl, hf⟩
  · exact three_le_pRank_sl_triple hp hm i
  · exact three_le_pRank_sl_pair hp hF hf i

theorem exists_pGroup_glbCore3_sl {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F]
    {p f : ℕ} [Fact p.Prime] [CharP F p] (hF : Nat.card F = p ^ f) {r : ℕ}
    (hr : 3 ≤ r ∨ (r = 2 ∧ 2 ≤ f))
    (e : G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin (r + 1)) F) :
    ∃ P : Subgroup G, IsPGroup p P ∧ GLBCore p 3 P = ⊤ := by
  have hext := steinbergExtras r F
  have hct := isCTGroupDatum r F
  have hX : ∀ γ ∈ (rootDatum r F).roots, IsPGroup p ((rootDatum r F).rootGroup γ) := fun γ hγ =>
    isPGroup_of_isParametrization isParametrization hγ
  have hU : IsPGroup p (posUnipotent (rootDatum r F)) := isPGroup_iSup_pos hext hX
  let π : Matrix.SpecialLinearGroup (Fin (r + 1)) F →* G :=
    e.symm.toMonoidHom.comp (QuotientGroup.mk' _)
  have hπ : Function.Surjective π := e.symm.surjective.comp (QuotientGroup.mk'_surjective _)
  have hinj : ∀ x ∈ posUnipotent (rootDatum r F), π x = 1 → x = 1 := by
    intro x hx hx1
    have hmk : (QuotientGroup.mk' _ x : Matrix.ProjectiveSpecialLinearGroup (Fin (r + 1)) F) = 1 :=
      e.symm.injective (by rw [map_one]; exact hx1)
    obtain ⟨k, hk⟩ := hU ⟨x, hx⟩
    exact CFSG.AGLEmbedding.CharPGen.eq_one_of_mem_center_of_pow
      ((QuotientGroup.eq_one_iff x).1 hmk) (congrArg Subtype.val hk)
  exact ⟨(posUnipotent (rootDatum r F)).map π, hU.map π,
    CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Fact2314.glbCore_map_eq_top_of_injOn Fact.out π hπ
      hinj
      (glbCore_posUnipotent_eq_top_of_le_pRank (D := rootDatum r F) hct Fact.out
        (by change 0 < r; omega)
        (fun i => three_le_pRank_posUnipotentExcept_sl (F := F) (m := r) (p := p) (f := f)
          Fact.out hF hr i))⟩

end SL

end CFSG.AGLEmbedding.CharPGenThree

namespace CFSG.AGLEmbedding

open CFSG.Open

theorem charPGen3At_sl : CharPGen3At IsWeakSLIndex := by
  refine charPGen3At_of_pGroup ?_
  intro K _ _ _ d ⟨r, q, hr, hd, hcond⟩ e p hp hp2 hchar hrank
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
  exact CFSG.AGLEmbedding.CharPGenThree.exists_pGroup_glbCore3_sl
    (F := GaloisField q.p q.exponent) (p := q.p) (f := q.exponent)
    (GaloisField.card q.p q.exponent q.exponent_pos.ne') hcond'
    (e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r q hv))

end CFSG.AGLEmbedding
