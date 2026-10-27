module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3.Transitive
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3.Dual
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.OvergroupDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.L3Leaves
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.QuasisimpleSolvableNormal
public import CFSG.Adapters.LinearCatalog
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupA5
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3

open Matrix CFSG.LargeExtraspecial.A2Mod CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.L3Leaves

variable {F : Type} [Field F]

theorem overgroupOddIndex_of_mulEquiv {K G : Type} [Group K] [Finite K] [Group G] [Finite G]
    (e : K ≃* G) (h : OvergroupOddIndex G) : OvergroupOddIndex K := by
  intro hK hcyc A W hA hNW hW h16
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hG : IsSimpleGroup G := by
    have := hK
    exact e.symm.isSimpleGroup
  have hcycG : ∀ X : Subgroup G, IsPGroup 3 X → IsCyclic X := by
    intro X hX
    set e' := X.equivMapOfInjective e.symm.toMonoidHom e.symm.injective
    have h1 : IsPGroup 3 ↥(X.map e.symm.toMonoidHom) := hX.map _
    have h2 := hcyc _ h1
    exact isCyclic_of_surjective e'.symm.toMonoidHom e'.symm.surjective
  have hcard : Nat.card (A.map e.toMonoidHom) = 3 := by
    rw [Subgroup.card_map_of_injective e.injective, hA]
  have hN : Subgroup.normalizer ((A.map e.toMonoidHom : Subgroup G) : Set G) ≤
      W.map e.toMonoidHom := by
    rw [← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hNW
  have hW' : ¬ CFSG.HallHigman.IsPSolvable 3 ↥(W.map e.toMonoidHom) := fun hs =>
    hW (OrdinaryProofs.QuasisimpleSolvableNormal.isPSolvable_of_mulEquiv
      (W.equivMapOfInjective e.toMonoidHom e.injective).symm hs)
  have hidx : (W.map e.toMonoidHom).index = W.index := Subgroup.index_map_equiv W e
  have h16' : ¬ 16 ∣ (W.map e.toMonoidHom).index := by rwa [hidx]
  have := h hG hcycG _ _ hcard hN hW' h16'
  rwa [hidx] at this

theorem orderOf_cGL : orderOf (cGL (F := F)) = 3 :=
  orderOf_eq_prime cGL_pow_three cGL_ne_one

theorem card_A0 : Nat.card (A0 : Subgroup (SL3 F)) = 3 := by
  rw [Nat.card_zpowers, orderOf_injective lev lev_injective, orderOf_cGL]

variable [Finite F]

theorem three_ne_zero_of_mod (hq : Nat.card F % 3 = 2) : (3 : F) ≠ 0 := by
  have h := sq_add_self_add_one_ne_zero hq 1
  norm_num at h
  exact h

theorem exists_cube (hq : Nat.card F % 3 = 2) (x : F) : ∃ y : F, y ^ 3 = x :=
  (cube_bijective hq).2 x

theorem exists_pow_six_ne_one (hq : Nat.card F % 3 = 2) (h5 : 5 ≤ Nat.card F) :
    ∃ μ : F, μ ≠ 0 ∧ μ ^ 6 ≠ 1 := by
  classical
  have := Fintype.ofFinite F
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hord : orderOf g = Nat.card F - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units]
  refine ⟨g, g.ne_zero, fun h => ?_⟩
  have h6 : g ^ 6 = 1 := Units.ext (by simpa using h)
  have hdvd := orderOf_dvd_of_pow_eq_one h6
  rw [hord] at hdvd
  have hle := Nat.le_of_dvd (by norm_num) hdvd
  interval_cases hc : Nat.card F - 1 <;> omega

theorem sixteen_dvd_sq_of_even (h5 : 5 ≤ Nat.card F) (heven : 2 ∣ Nat.card F) :
    16 ∣ Nat.card F ^ 2 := by
  classical
  have := Fintype.ofFinite F
  obtain ⟨p, -, n, hp, hcard⟩ := FiniteField.card' F
  rw [Nat.card_eq_fintype_card, hcard] at h5 heven ⊢
  have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp
    (Nat.prime_two.dvd_of_dvd_pow heven) |>.symm
  subst hp2
  have hn : 2 ≤ (n : ℕ) := by
    by_contra h
    push Not at h
    interval_cases hn : (n : ℕ)
    · simp at h5
    · simp at h5
  obtain ⟨m, hm⟩ : ∃ m, (n : ℕ) = m + 2 := ⟨(n : ℕ) - 2, by omega⟩
  rw [hm]
  exact ⟨2 ^ (2 * m), by ring⟩

theorem index_cases_SL3 (hq : Nat.card F % 3 = 2) (h5 : 5 ≤ Nat.card F)
    (hmax : GL2NonsplitMax F) {W : Subgroup (SL3 F)}
    (hNW : Subgroup.normalizer ((A0 : Subgroup (SL3 F)) : Set (SL3 F)) ≤ W)
    (hW : ¬ Group.IsSolvable W) :
    W = ⊤ ∨ W.index = Nat.card F ^ 2 ∨ W.index = Nat.card F ^ 2 + Nat.card F + 1 ∨
      W.index = Nat.card F ^ 2 * (Nat.card F ^ 2 + Nat.card F + 1) := by
  have hroot := sq_add_self_add_one_ne_zero hq
  have hcube := exists_cube hq
  have h3 := three_ne_zero_of_mod hq
  obtain ⟨μ, hμ0, hμ6⟩ := exists_pow_six_ne_one hq h5
  have hlev : ∀ X : GL (Fin 2) F,
      (X : Matrix (Fin 2) (Fin 2) F) * cMat = cMat * (X : Matrix (Fin 2) (Fin 2) F) → lev X ∈ W :=
    fun X hX => hNW (lev_mem_normalizer_A0 (mem_Nt_of_comm hX))
  rcases le_P1_or_le_P2_or_transitive hroot hcube hlev with h | h | h
  · rcases index_of_le_P1 hroot hcube h3 hmax h hNW hW with h' | h'
    · exact Or.inr (Or.inr (Or.inl h'))
    · exact Or.inr (Or.inr (Or.inr h'))
  · rcases index_of_le_P2 hroot hcube h3 hmax h hNW hW with h' | h'
    · exact Or.inr (Or.inr (Or.inl h'))
    · exact Or.inr (Or.inr (Or.inr h'))
  · rcases eq_top_or_index_of_transitive hroot hcube h3 hmax hμ0 hμ6 hNW h with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')

theorem overgroupOddIndex_SL3 (hq : Nat.card F % 3 = 2) (h5 : 5 ≤ Nat.card F)
    (hmax : GL2NonsplitMax F) : OvergroupOddIndex (SL3 F) := by
  intro _ hcyc A W hA hNW hW h16
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := exists_conj_eq_of_card_eq_three hcyc hA card_A0
  set W' := W.map (MulAut.conj g).toMonoidHom
  have hNW' : Subgroup.normalizer ((A0 : Subgroup (SL3 F)) : Set (SL3 F)) ≤ W' := by
    rw [hg, ← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hNW
  have hW' : ¬ Group.IsSolvable W' := by
    intro hs
    apply hW
    have hWs : Group.IsSolvable W := by
      set e := W.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
      exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    exact S3AmalgamBound.OvergroupA5.isPSolvable_of_isSolvable Nat.prime_three hWs
  have hidx : W'.index = W.index := Subgroup.index_map_equiv W (MulAut.conj g)
  have hodd : Odd (Nat.card F ^ 2 + Nat.card F + 1) := by
    have : Even (Nat.card F ^ 2 + Nat.card F) := by
      rw [show Nat.card F ^ 2 + Nat.card F = Nat.card F * (Nat.card F + 1) by ring]
      exact Nat.even_mul_succ_self _
    exact this.add_one
  rw [← hidx] at h16 ⊢
  rcases Nat.even_or_odd (Nat.card F) with he | ho
  · have h16q := sixteen_dvd_sq_of_even h5 (even_iff_two_dvd.mp he)
    rcases index_cases_SL3 hq h5 hmax hNW' hW' with h | h | h | h
    · rw [h, Subgroup.index_top]
      exact odd_one
    · exact absurd (h ▸ h16q) h16
    · rw [h]
      exact hodd
    · exact absurd (h ▸ h16q.mul_right _) h16
  · rcases index_cases_SL3 hq h5 hmax hNW' hW' with h | h | h | h
    · rw [h, Subgroup.index_top]
      exact odd_one
    · rw [h]
      exact ho.pow
    · rw [h]
      exact hodd
    · rw [h]
      exact ho.pow.mul hodd

@[expose] noncomputable def pslEquivSL3 (hq : Nat.card F % 3 = 2) :
    Matrix.ProjectiveSpecialLinearGroup (Fin 3) F ≃* SL3 F :=
  (QuotientGroup.quotientMulEquivOfEq (by
    rw [eq_bot_iff]
    intro A hA
    obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
    rw [Fintype.card_fin] at hr
    have h1 := cube_eq_one_imp hq hr
    rw [Subgroup.mem_bot]
    refine Subtype.ext ?_
    rw [← hrA, h1]
    simp)).trans QuotientGroup.quotientBot

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811

open L3

theorem kFactOvergroupL3_of_max
    (hmax : ∀ (F : Type) [Field F] [Finite F], Nat.card F % 3 = 2 → 5 ≤ Nat.card F →
      GL2NonsplitMax F) : KFactOvergroupL3 := by
  intro K _ _ d q hq hd ⟨e⟩
  obtain ⟨d, hv⟩ := d
  simp only at hd
  subst hd
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  set F := GaloisField q.p q.exponent
  have hF : Nat.card F = q.card := by
    rw [GaloisField.card q.p q.exponent q.exponent_pos.ne', ← TauCeti.PrimePower.card_def]
  have hqF : Nat.card F % 3 = 2 := by rw [hF]; exact hq
  have h5 : 5 ≤ Nat.card F := by
    rw [hF]
    have hdup := ((TauCeti.LieTypeIndex.valid_iff _).mp hv).2
    rw [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff] at hdup
    have h2 : 2 ≤ q.card := by
      rw [TauCeti.PrimePower.card_def]
      exact (Nat.one_lt_pow q.exponent_pos.ne' q.prime_p.one_lt)
    omega
  exact overgroupOddIndex_of_mulEquiv
    ((e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 q hv)).trans
      (pslEquivSL3 hqF))
    (overgroupOddIndex_SL3 hqF h5 (hmax F hqF h5))

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811
