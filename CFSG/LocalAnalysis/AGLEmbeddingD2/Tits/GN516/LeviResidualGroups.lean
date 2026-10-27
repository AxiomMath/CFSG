module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.LeviResidual
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParSuzuki
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParTwoMap

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516

open CFSG.Open CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar
  CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGen

structure TwoParSolv (S : Type) [Group S] (T P₁ P₂ : Subgroup S) : Prop where
  tp : TwoPar S T P₁ P₂
  s₁ : Group.IsSolvable ↥P₁
  s₂ : Group.IsSolvable ↥P₂

section TwoParSolv

variable {S S' : Type} [Group S] [Group S']

theorem TwoParSolv.map (e : S ≃* S') {T P₁ P₂ : Subgroup S} (h : TwoParSolv S T P₁ P₂) :
    TwoParSolv S' (T.map e.toMonoidHom) (P₁.map e.toMonoidHom) (P₂.map e.toMonoidHom) :=
  ⟨h.tp.map e,
    by
      have := h.s₁
      exact Group.isSolvable_of_isSolvable_injective (f := (e.subgroupMap P₁).symm.toMonoidHom)
        (e.subgroupMap P₁).symm.injective,
    by
      have := h.s₂
      exact Group.isSolvable_of_isSolvable_injective (f := (e.subgroupMap P₂).symm.toMonoidHom)
        (e.subgroupMap P₂).symm.injective⟩

theorem TwoParSolv.exists_of_equiv [Finite S'] (e : S ≃* S') {T P₁ P₂ : Subgroup S}
    (h : TwoParSolv S T P₁ P₂) {T' : Subgroup S'} (hT' : IsSylowTwoOf T' ⊤) :
    ∃ P₁' P₂' : Subgroup S', TwoParSolv S' T' P₁' P₂' := by
  have h1 := h.map e
  obtain ⟨g, hg⟩ := exists_conj_of_sylowTwo h1.tp.sylow hT'
  rw [← hg]
  exact ⟨_, _, h1.map (MulAut.conj g)⟩

theorem minLevi_of_twoParSolv {Y : Type} [Group Y] [Finite Y] (e : Y ≃* S)
    (h : ∃ T P₁ P₂ : Subgroup S, TwoParSolv S T P₁ P₂) : MinLevi Y := by
  intro _ T Q hT hQ hne
  obtain ⟨T₀, P₁, P₂, h⟩ := h
  obtain ⟨P₁', P₂', h'⟩ := TwoParSolv.exists_of_equiv e.symm h hT
  have hNQ : Subgroup.normalizer (T : Set Y) ≤ Q := by simpa using hQ.2.1.le
  rcases h'.tp.hover Q hNQ with e1 | e1 | e1 | e1
  · exact absurd hQ.2.1 (by rw [top_inf_eq, e1]; exact lt_irrefl _)
  · rw [e1]
    have := h'.s₁
    exact leviAlt_pElement_of_solvable this
  · rw [e1]
    have := h'.s₂
    exact leviAlt_pElement_of_solvable this
  · exact absurd e1 hne

end TwoParSolv

theorem minLevi_suzuki {Y : Type} [Group Y] [Finite Y] (m : ℕ)
    (hv : (TauCeti.LieTypeIndex.suzuki m).Valid)
    (e : Y ≃* (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.suzuki m, hv⟩).Group) :
    MinLevi Y := by
  intro _ T Q hT hQ hne
  exact absurd ((suzuki_cat m hv e hT).2.coatom.2 Q (by simpa using hQ.2.1)) hne

theorem natCard_dvd_factorial_index {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    {Q : Subgroup G} (hQ : Q ≠ ⊤) : Nat.card G ∣ (Q.index).factorial := by
  have := Fintype.ofFinite G
  classical
  let φ : G →* Equiv.Perm (G ⧸ Q) := MulAction.toPermHom G (G ⧸ Q)
  have hker : φ.ker = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with h | h
    · exact h
    · exfalso
      apply hQ
      rw [eq_top_iff]
      intro g _
      have h1 : g ∈ φ.ker := h ▸ Subgroup.mem_top g
      have h2 : g • ((1 : G) : G ⧸ Q) = ((1 : G) : G ⧸ Q) := by
        simpa [φ] using DFunLike.congr_fun (MonoidHom.mem_ker.1 h1) ((1 : G) : G ⧸ Q)
      have h3 : ((g * 1 : G) : G ⧸ Q) = ((1 : G) : G ⧸ Q) := h2
      have h4 := QuotientGroup.eq.1 h3
      simpa using h4
  have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).1 hker
  have hd := Subgroup.card_dvd_of_injective φ hinj
  rwa [Nat.card_perm] at hd

theorem natCard_sylowTwo_of_card_360 {Y : Type} [Group Y] [Finite Y] (hY : Nat.card Y = 360)
    {T : Subgroup Y} (hT : IsSylowTwoOf T ⊤) : Nat.card T = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).1 hT.2.1
  have hodd : ¬ 2 ∣ T.index := by
    have h := hT.2.2
    rwa [show (T.subgroupOf ⊤).index = T.index from Subgroup.relIndex_top_right T] at h
  have hmul := Subgroup.card_mul_index T
  rw [hk, hY] at hmul
  have hk8 : k ≤ 8 := by
    by_contra h
    have : 2 ^ 9 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    have := Nat.le_of_dvd (by norm_num) (Dvd.intro _ hmul)
    omega
  rw [hk]
  interval_cases k <;> omega

theorem solvable_of_proper_overSylow_360 {Y : Type} [Group Y] [Finite Y] [IsSimpleGroup Y]
    (hY : Nat.card Y = 360) {T Q : Subgroup Y} (hT : IsSylowTwoOf T ⊤) (hTQ : T ≤ Q)
    (hQ : Q ≠ ⊤) : Group.IsSolvable ↥Q := by
  have hT8 := natCard_sylowTwo_of_card_360 hY hT
  have h8 : 8 ∣ Nat.card Q := hT8 ▸ Subgroup.card_dvd_of_le hTQ
  have hmul := Subgroup.card_mul_index Q
  rw [hY] at hmul
  have hfac := natCard_dvd_factorial_index hQ
  rw [hY] at hfac
  have hi1 : Q.index ≠ 1 := fun h => hQ (Subgroup.index_eq_one.1 h)
  have hi0 : 0 < Q.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hi6 : 6 ≤ Q.index := by
    by_contra h
    have : Q.index ∈ ({2, 3, 4, 5} : Finset ℕ) := by simp; omega
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h | h | h | h <;> rw [h] at hfac <;> revert hfac <;> decide
  obtain ⟨c', hc'⟩ := h8
  have hdvd : Q.index ∣ 45 := by
    refine ⟨c', ?_⟩
    rw [hc'] at hmul
    linarith
  have hmem : Q.index ∈ Nat.divisors 45 := Nat.mem_divisors.2 ⟨hdvd, by norm_num⟩
  have hdiv45 : Nat.divisors 45 = {1, 3, 5, 9, 15, 45} := by decide
  rw [hdiv45] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h | h | h
  · omega
  · omega
  · omega
  · rw [h] at hmul
    have : Nat.card Q = 8 * 5 := by omega
    exact isSolvable_of_natCard_eq (p := 2) (q := 5) (a := 3) (b := 1) Nat.prime_two (by norm_num)
      (by norm_num) (by rw [this]; norm_num)
  · rw [h] at hmul
    have : Nat.card Q = 8 * 3 := by omega
    exact isSolvable_of_natCard_eq (p := 2) (q := 3) (a := 3) (b := 1) Nat.prime_two (by norm_num)
      (by norm_num) (by rw [this]; norm_num)
  · rw [h] at hmul
    have : Nat.card Q = 8 := by omega
    exact isSolvable_of_natCard_eq (p := 2) (q := 3) (a := 3) (b := 0) Nat.prime_two (by norm_num)
      (by norm_num) (by rw [this]; norm_num)

theorem minLevi_alt_six {Y : Type} [Group Y] [Finite Y] (e : Y ≃* ↥(alternatingGroup (Fin 6))) :
    MinLevi Y := by
  intro hs T Q hT hQ hne
  have hY : Nat.card Y = 360 := by
    rw [Nat.card_congr e.toEquiv]
    have h := two_mul_nat_card_alternatingGroup (α := Fin 6)
    have h1 : Nat.card (Fin 6) = 6 := by simp
    rw [Nat.card_perm, h1] at h
    rw [show Nat.factorial 6 = 720 from rfl] at h
    omega
  have hTQ : T ≤ Q := Subgroup.le_normalizer.trans (by simpa using hQ.2.1.le)
  exact leviAlt_pElement_of_solvable (solvable_of_proper_overSylow_360 hY hT hTQ hne)

end CFSG.AGLEmbeddingD2.Tits.GN516
