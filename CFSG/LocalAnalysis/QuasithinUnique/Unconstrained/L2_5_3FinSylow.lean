module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_3FinShape
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_3FinRadical
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.QuasithinUnique.Fin253

open CFSG.Open CFSG.Quasithin

section SylowRadical

variable {G : Type} [Group G] [Finite G]

@[expose] def SylowRadical (M L : Subgroup G) : Prop :=
  IsSylowTwoOf (pCoreOf 2 (M ⊓ L)) L

theorem sylowRadical_of_isBorelIn {M L : Subgroup G} (h : IsBorelIn (M ⊓ L) L) :
    SylowRadical M L := by
  obtain ⟨P, hP, hB⟩ := h
  have hPB : P ≤ M ⊓ L := by
    rw [hB]
    exact le_inf hP.le Subgroup.le_normalizer
  have hn : M ⊓ L ≤ Subgroup.normalizer (P : Set G) := by
    rw [hB]
    exact inf_le_right
  have h1 : P ≤ pCoreOf 2 (M ⊓ L) := le_pCoreOf_of_normal_pGroup hPB hn hP.isPGroup
  have h2 : pCoreOf 2 (M ⊓ L) ≤ L :=
    (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 _).trans inf_le_right
  have h3 : pCoreOf 2 (M ⊓ L) = P :=
    hP.eq_of_le h1 h2 (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 _)
  unfold SylowRadical
  rw [h3]
  exact hP

omit [Finite G] in
theorem sylowRadical_of_inf_eq {M S L : Subgroup G} (hS : IsPGroup 2 S) (hMS : M ⊓ L = S ⊓ L)
    (hsyl : IsSylowTwoOf (S ⊓ L) L) : SylowRadical M L := by
  have h2 : IsPGroup 2 ↥(S ⊓ L) := hS.to_le inf_le_left
  have h3 : pCoreOf 2 (S ⊓ L) = S ⊓ L :=
    le_antisymm (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 _)
      (le_pCoreOf_of_normal_pGroup le_rfl Subgroup.le_normalizer h2)
  unfold SylowRadical
  rw [hMS, h3]
  exact hsyl

theorem sylowRadical_conjugate {M L : Subgroup G} (h : SylowRadical M L) {s : G} (hs : s ∈ M) :
    SylowRadical M (CFSG.conjugate L s) := by
  have hM : M.map (MulAut.conj s⁻¹).toMonoidHom = M :=
    Unc25G2.map_conj_eq_of_mem_normalizer' (Subgroup.le_normalizer (M.inv_mem hs))
  have hinf : (M ⊓ L).map (MulAut.conj s⁻¹).toMonoidHom = M ⊓ CFSG.conjugate L s := by
    rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj s⁻¹).injective, hM]
    rfl
  have h1 := IsSylowTwoOf.map_equiv (MulAut.conj s⁻¹) h
  unfold SylowRadical
  rw [← hinf, pCoreOf_map_equiv 2 (MulAut.conj s⁻¹)]
  exact h1

theorem isSylowTwoOf_sup_of_commute {A B P P' : Subgroup G}
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hP : IsSylowTwoOf P A) (hP' : IsSylowTwoOf P' B)
    (hAB : IsPGroup 2 ↥(A ⊓ B)) : IsSylowTwoOf (P ⊔ P') (A ⊔ B) := by
  have hAcent : A ≤ Subgroup.centralizer (B : Set G) := fun a ha =>
    Subgroup.mem_centralizer_iff.mpr fun b hb => (hc a ha b hb).symm
  have hBcent : B ≤ Subgroup.centralizer (A : Set G) := fun b hb =>
    Subgroup.mem_centralizer_iff.mpr fun a ha => hc a ha b hb
  have hsubB : ((A ⊓ B : Subgroup G) : Set G) ⊆ (B : Set G) := fun x hx => hx.2
  have hsubA : ((A ⊓ B : Subgroup G) : Set G) ⊆ (A : Set G) := fun x hx => hx.1
  have hAnorm : A ≤ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) :=
    hAcent.trans ((Subgroup.centralizer_le hsubB).trans (Subgroup.centralizer_le_normalizer _))
  have hBnorm : B ≤ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) :=
    hBcent.trans ((Subgroup.centralizer_le hsubA).trans (Subgroup.centralizer_le_normalizer _))
  have hABP : A ⊓ B ≤ P := hP.le_of_normalizes inf_le_left hAnorm hAB
  have hABP' : A ⊓ B ≤ P' := hP'.le_of_normalizes inf_le_right hBnorm hAB
  have hPP' : P ⊓ P' = A ⊓ B :=
    le_antisymm (inf_le_inf hP.le hP'.le) (le_inf hABP hABP')
  have hc' : ∀ x ∈ P, ∀ y ∈ P', x * y = y * x := fun x hx y hy => hc x (hP.le hx) y (hP'.le hy)
  obtain ⟨h1, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A B hc
  obtain ⟨h2, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute P P' hc'
  rw [hPP'] at h2
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hAB
  have hP'cent : P' ≤ Subgroup.centralizer (P : Set G) := fun y hy =>
    Subgroup.mem_centralizer_iff.mpr fun x hx => hc' x hx y hy
  have hP'norm : P' ≤ Subgroup.normalizer (P : Set G) :=
    hP'cent.trans (Subgroup.centralizer_le_normalizer _)
  have hPP2 : IsPGroup 2 ↥(P ⊔ P') := hP.isPGroup.to_sup_of_normal_left' hP'.isPGroup hP'norm
  refine isSylowTwoOf_of_card_eq (sup_le_sup hP.le hP'.le) hPP2 ?_
  have hA0 : Nat.card ↥A ≠ 0 := Nat.card_pos.ne'
  have hB0 : Nat.card ↥B ≠ 0 := Nat.card_pos.ne'
  have hD0 : Nat.card ↥(A ⊔ B) ≠ 0 := Nat.card_pos.ne'
  have hv : (Nat.card ↥(A ⊔ B)).factorization 2 + k =
      (Nat.card ↥A).factorization 2 + (Nat.card ↥B).factorization 2 := by
    rw [hk] at h1
    have h1' : (Nat.card ↥(A ⊔ B) * 2 ^ k).factorization 2 =
        (Nat.card ↥A * Nat.card ↥B).factorization 2 := by rw [h1]
    rw [Nat.factorization_mul hD0 (by positivity), Nat.factorization_mul hA0 hB0,
      Finsupp.add_apply, Finsupp.add_apply, Nat.factorization_pow, Finsupp.smul_apply,
      Nat.Prime.factorization_self Nat.prime_two] at h1'
    simpa using h1'
  have hcard : Nat.card ↥(P ⊔ P') * 2 ^ k = twoPart A * twoPart B := by
    rw [← hk, h2, hP.card_eq, hP'.card_eq]
  have htwo : twoPart (A ⊔ B) * 2 ^ k = twoPart A * twoPart B := by
    unfold twoPart
    rw [← pow_add, ← pow_add, hv]
  exact Nat.eq_of_mul_eq_mul_right (by positivity) (hcard.trans htwo.symm)

theorem isSylowTwoOf_pCoreOf_inf_sup {M A B : Subgroup G}
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hA : SylowRadical M A) (hB : SylowRadical M B)
    (hAB : IsPGroup 2 ↥(A ⊓ B)) : IsSylowTwoOf (pCoreOf 2 (M ⊓ (A ⊔ B))) (A ⊔ B) := by
  have hsyl := isSylowTwoOf_sup_of_commute hc hA hB hAB
  have hAcent : A ≤ Subgroup.centralizer (B : Set G) := fun a ha =>
    Subgroup.mem_centralizer_iff.mpr fun b hb => (hc a ha b hb).symm
  have hBcent : B ≤ Subgroup.centralizer (A : Set G) := fun b hb =>
    Subgroup.mem_centralizer_iff.mpr fun a ha => hc a ha b hb
  have hAn : A ⊔ B ≤ Subgroup.normalizer (A : Set G) :=
    sup_le Subgroup.le_normalizer (hBcent.trans (Subgroup.centralizer_le_normalizer _))
  have hBn : A ⊔ B ≤ Subgroup.normalizer (B : Set G) :=
    sup_le (hAcent.trans (Subgroup.centralizer_le_normalizer _)) Subgroup.le_normalizer
  have hXA : M ⊓ (A ⊔ B) ≤ Subgroup.normalizer (pCoreOf 2 (M ⊓ A) : Set G) :=
    (CFSG.RankThreeCoreUniqueness.Helpers.common_normalizer_le_normalizer_inf _ M A
      (inf_le_left.trans Subgroup.le_normalizer) (inf_le_right.trans hAn)).trans
      (CFSG.RankThreeCoreUniqueness.Helpers.normalizer_localGroup_le_normalizer_pCoreOf 2 _)
  have hXB : M ⊓ (A ⊔ B) ≤ Subgroup.normalizer (pCoreOf 2 (M ⊓ B) : Set G) :=
    (CFSG.RankThreeCoreUniqueness.Helpers.common_normalizer_le_normalizer_inf _ M B
      (inf_le_left.trans Subgroup.le_normalizer) (inf_le_right.trans hBn)).trans
      (CFSG.RankThreeCoreUniqueness.Helpers.normalizer_localGroup_le_normalizer_pCoreOf 2 _)
  have hPPX : pCoreOf 2 (M ⊓ A) ⊔ pCoreOf 2 (M ⊓ B) ≤ M ⊓ (A ⊔ B) :=
    sup_le ((CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 _).trans
      (inf_le_inf_left M le_sup_left))
      ((CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 _).trans
        (inf_le_inf_left M le_sup_right))
  have hle : pCoreOf 2 (M ⊓ A) ⊔ pCoreOf 2 (M ⊓ B) ≤ pCoreOf 2 (M ⊓ (A ⊔ B)) :=
    le_pCoreOf_of_normal_pGroup hPPX (le_normalizer_sup hXA hXB) hsyl.isPGroup
  have heq : pCoreOf 2 (M ⊓ (A ⊔ B)) = pCoreOf 2 (M ⊓ A) ⊔ pCoreOf 2 (M ⊓ B) :=
    hsyl.eq_of_le hle ((CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 _).trans inf_le_right)
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 _)
  rw [heq]
  exact hsyl

end SylowRadical

section Shape

variable {G : Type} [Group G] [Finite G] {T M H S : Subgroup G} {z : G}

theorem shape (hs : UnconstrainedSetting G T M) (ht : Tuple25 T M H S z)
    (hinn : ∀ L : Subgroup G, IsComponentIn L H → Ch1.InducesInner z L) {K : Subgroup G}
    (hK : IsComponentIn K H) :
    conjJoin H K = K ∨ ∃ s ∈ S, CFSG.conjugate K s ≠ K ∧ IsComponentIn (CFSG.conjugate K s) H ∧
      ⁅K, CFSG.conjugate K s⁆ = ⊥ ∧ conjJoin H K = K ⊔ CFSG.conjugate K s := by
  by_cases hall : ∀ g ∈ H, CFSG.conjugate K g = K
  · left
    refine le_antisymm (iSup_le fun g => ?_) (le_conjJoin_self H K)
    have := hall (g : G)⁻¹ (H.inv_mem g.2)
    simp only [CFSG.conjugate, inv_inv] at this
    exact this.le
  · right
    push Not at hall
    obtain ⟨g₀, hg₀, h₀⟩ := hall
    obtain ⟨s, hsS, hs'⟩ := exists_mem_conjugate_ne ht hg₀ h₀
      (conjugate_dichotomy hs ht hinn hK hg₀ h₀)
    have hsH : s ∈ H := ht.le_H hsS
    have hd := conjugate_dichotomy hs ht hinn hK hsH hs'
    have hK'c : IsComponentIn (CFSG.conjugate K s) H := Unc25G2.isComponentIn_conjugate hK hsH
    have hcomm : ⁅K, CFSG.conjugate K s⁆ = ⊥ :=
      (BenderBranch.eq_or_commute_of_isComponentIn hK hK'c).resolve_left fun h => hs' h.symm
    refine ⟨s, hsS, hs', hK'c, hcomm, ?_⟩
    refine le_antisymm (iSup_le fun g => ?_) (sup_le (le_conjJoin_self H K) ?_)
    · have := hd (g : G)⁻¹ (H.inv_mem g.2)
      simp only [CFSG.conjugate, inv_inv] at this ⊢
      rcases this with h | h
      · exact h.le.trans le_sup_left
      · exact h.le.trans le_sup_right
    · exact map_conj_le_conjJoin H K ⟨s⁻¹, H.inv_mem hsH⟩

theorem isSylowTwoOf_radicalOf (hs : UnconstrainedSetting G T M) (ht : Tuple25 T M H S z)
    (hinn : ∀ L : Subgroup G, IsComponentIn L H → Ch1.InducesInner z L) {K : Subgroup G}
    (hK : IsComponentIn K H) (hsyl : SylowRadical M K) :
    IsSylowTwoOf (radicalOf M H K) (conjJoin H K) := by
  rcases shape hs ht hinn hK with hD | ⟨s, hsS, -, -, hcomm, hD⟩
  · unfold radicalOf
    rw [hD]
    exact hsyl
  · have hc : ∀ a ∈ K, ∀ b ∈ CFSG.conjugate K s, a * b = b * a := fun a ha b hb =>
      BenderBranch.commute_of_commutator_eq_bot hcomm ha hb
    have hcen : Unc25G2.CentreTwo K := ht.centreTwo hs hK (hinn K hK)
    have hAB : IsPGroup 2 ↥(K ⊓ CFSG.conjugate K s) := by
      rintro ⟨x, hxK, hxK'⟩
      obtain ⟨k, hk⟩ := hcen x hxK fun w hw => hc w hw x hxK'
      exact ⟨k, Subtype.ext hk⟩
    unfold radicalOf
    rw [hD]
    exact isSylowTwoOf_pCoreOf_inf_sup hc hsyl (sylowRadical_conjugate hsyl (ht.le_M hsS)) hAB

@[expose] def InCase3 (M : Subgroup G) (z : G) (K : Subgroup G) : Prop :=
  (StatedClassicalModel ↥K .PSL 3 3 1 ∨
      Nonempty (↥K ≃* CFSG.Blueprint.NativeSporadic.Carrier .M11)) ∧
    ∃ zL : G, IsProjectionOn z zL K ∧ M ⊓ K = K ⊓ Subgroup.centralizer ({zL} : Set G)

theorem sylowRadical_or_case3 (ht : Tuple25 T M H S z) {K : Subgroup G} (hK : IsComponentIn K H)
    (hBe : ¬ fusionIsBenderGroup ↥K) (hcl : ComponentList M S z K) :
    SylowRadical M K ∨ InCase3 M z K := by
  obtain ⟨-, -, -, -, hcase⟩ := hcl
  rcases hcase with h1 | h2 | h3 | h4
  · exact absurd h1.1 hBe
  · exact Or.inl (sylowRadical_of_isBorelIn h2.2.2)
  · exact Or.inr h3
  · exact Or.inl (sylowRadical_of_inf_eq ht.sylow.isPGroup h4.2
      (RankOneRecog.isSylowTwoOf_inf_of_subnormal ht.sylow hK.1 hK.2.2))

end Shape

end CFSG.QuasithinUnique.Fin253
