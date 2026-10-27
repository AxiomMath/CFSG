module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42TypeListAux
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57SL
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57Sp4
public import CFSG.Quasithin.Background.A3Structure312Iso

public section

namespace CFSG.QuasithinUnique.Bridge

open CFSG.Quasithin CFSG.Assembly.LowTwoRank

@[expose] def B42Types (L : Type) [Group L] : Prop :=
  (∃ (K : Type) (_ : Field K) (_ : Finite K) (n : ℕ), 2 ≤ n ∧ Nat.card K = 2 ^ n ∧
      Nonempty (L ≃* ↥(StatedSL 2 K))) ∨
  (∃ n : ℕ, 1 ≤ n ∧ IsSL3 (2 ^ n) L) ∨
  (∃ (K : Type) (_ : Field K) (_ : Finite K) (n : ℕ), 2 ≤ n ∧ Nat.card K = 2 ^ n ∧
      Nonempty (L ≃* ↥(StatedSp 2 K))) ∨
  (∃ (K : Type) (_ : Field K) (_ : Finite K) (n : ℕ), 2 ≤ n ∧ Nat.card K = 2 ^ n ∧
      Nonempty (L ≃* ↥(CFSG.Open.quasithinG2 K))) ∨
  (∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ∧
      ∃ N : Subgroup ↥(CFSG.Open.quasithinG2 K), N.Normal ∧ Nonempty (L ≃* ↥N)) ∨
  (∃ m : ℕ, (m = 5 ∨ m = 6 ∨ m = 7) ∧ IsAlt m L) ∨
  IsHat L (alternatingGroup (Fin 6)) ∨
  (∃ (K : Type) (_ : Field K) (_ : Finite K) (n : ℕ), Nat.card K = 2 ∧ (n = 4 ∨ n = 5) ∧
      Nonempty (L ≃* ↥(StatedSL n K)))

namespace TypeList

section Cases

variable {V : Type} [CommGroup V] [Finite V] {G L A : Subgroup (MulAut V)}

theorem one_le_of_card_eq_pow {K : Type} [Field K] [Finite K] {n : ℕ} (h : Nat.card K = 2 ^ n) :
    1 ≤ n := by
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · exfalso
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    rw [h0, pow_zero] at h
    omega
  · exact h0

theorem typeOf_case1 (hq : CFSG.IsQuasisimple ↥L) (h : B42Case1 G L A) : B42Types ↥L := by
  obtain ⟨-, ⟨n, hn⟩, -, -⟩ := h
  obtain ⟨K, hK, hKfin, hcard, ⟨e⟩⟩ := BinaryNaturalSL.exists_equiv hn
  refine Or.inl ⟨K, hK, hKfin, n, ?_, hcard, ⟨e.symm⟩⟩
  by_contra hlt
  have h1 : n = 1 := by
    have := one_le_of_card_eq_pow hcard
    omega
  subst h1
  have hK2 : Nat.card K = 2 := by simpa using hcard
  have h1 : Nat.card ↥L = Nat.card K * (Nat.card K ^ 2 - 1) := by
    rw [← Nat.card_congr e.toEquiv,
      ← Nat.card_congr (specialLinearGroupEquivStatedSL 2 K).toEquiv]
    exact CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two K
  have h6 : Nat.card ↥L = 6 := by simp [h1, hK2]
  exact commutator_ne_top_of_card_six h6 hq.1.commutator_eq_top

theorem typeOf_case2 (h : B42Case2 G L) : B42Types ↥L := by
  obtain ⟨-, ⟨n, hn⟩, -⟩ := h
  obtain ⟨K, hK, hKfin, hcard, ⟨e⟩⟩ := BinaryNaturalSL.exists_equiv hn
  exact Or.inr (Or.inl ⟨n, one_le_of_card_eq_pow hcard, K, hK, hKfin, hcard, ⟨e.symm⟩⟩)

theorem typeOf_case3 (hq : CFSG.IsQuasisimple ↥L) (hLJ : L ≤ ffJ G)
    (hnorm : (L.subgroupOf (ffJ G)).Normal) (h : B42Case3 G L) : B42Types ↥L := by
  obtain ⟨⟨n, hn, hn2⟩, -⟩ := h
  obtain ⟨K, hK, hKfin, hcard, ⟨e⟩⟩ := BinaryNaturalSp4.exists_equiv hn
  have hn1 := one_le_of_card_eq_pow hcard
  rcases Nat.lt_or_ge n 2 with hlt | hge
  · have h1 : n = 1 := by omega
    subst h1
    have : Fintype K := Fintype.ofFinite K
    have hK2 : Fintype.card K = 2 := by
      rw [← Nat.card_eq_fintype_card]
      simpa using hcard
    let π : Equiv.Perm (Fin 6) →* ↥(ffJ G) :=
      e.toMonoidHom.comp (Alt57Model.spEquivPerm K hK2).symm.toMonoidHom
    have hπ : Function.Surjective π :=
      e.surjective.comp (Alt57Model.spEquivPerm K hK2).symm.surjective
    have hq' : CFSG.IsQuasisimple ↥(L.subgroupOf (ffJ G)) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLJ).symm hq
    obtain ⟨f⟩ := perm_perfect_normal_equiv (n := 6) (by norm_num) π hπ _ hnorm
      hq'.1.commutator_eq_top (exists_noncomm_of_quasisimple hq')
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨6, Or.inr (Or.inl rfl),
      ⟨(Subgroup.subgroupOfEquivOfLe hLJ).symm.trans f.symm⟩⟩)))))
  · have heq : ffJ G = L := hn2 hge
    exact Or.inr (Or.inr (Or.inl ⟨K, hK, hKfin, n, hge, hcard,
      ⟨(e.trans (MulEquiv.subgroupCongr heq)).symm⟩⟩))

theorem typeOf_case4 (hLJ : L ≤ ffJ G) (hnorm : (L.subgroupOf (ffJ G)).Normal)
    (h : B42Case4 G L A) : B42Types ↥L := by
  obtain ⟨⟨n, hn, -, hn2⟩, -⟩ := h
  obtain ⟨K, hK, hKfin, hcard, ⟨e⟩⟩ := exists_equiv_of_g2Natural hn
  have hn1 := one_le_of_card_eq_pow hcard
  rcases Nat.lt_or_ge n 2 with hlt | hge
  · have h1 : n = 1 := by omega
    subst h1
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨K, hK, hKfin, by simpa using hcard,
      (L.subgroupOf (ffJ G)).map e.symm.toMonoidHom,
      Subgroup.Normal.map hnorm e.symm.toMonoidHom e.symm.surjective, ?_⟩))))
    exact ⟨(Subgroup.subgroupOfEquivOfLe hLJ).symm.trans
      (e.symm.subgroupMap (L.subgroupOf (ffJ G)))⟩
  · have heq : ffJ G = L := hn2 hge
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨K, hK, hKfin, n, hge, hcard,
      ⟨(e.trans (MulEquiv.subgroupCongr heq)).symm⟩⟩)))

theorem typeOf_case5 (hq : CFSG.IsQuasisimple ↥L) (hLJ : L ≤ ffJ G)
    (hnorm : (L.subgroupOf (ffJ G)).Normal) (h : B42Case5 G A) : B42Types ↥L := by
  obtain ⟨⟨n, hn, π, hπ, -⟩, -⟩ := h
  have hn5 : 5 ≤ n := by rcases hn with rfl | rfl <;> omega
  have hq' : CFSG.IsQuasisimple ↥(L.subgroupOf (ffJ G)) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLJ).symm hq
  obtain ⟨f⟩ := perm_perfect_normal_equiv hn5 π hπ.1 _ hnorm hq'.1.commutator_eq_top
    (exists_noncomm_of_quasisimple hq')
  refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, ?_,
    ⟨(Subgroup.subgroupOfEquivOfLe hLJ).symm.trans f.symm⟩⟩)))))
  rcases hn with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inr rfl)

theorem typeOf_case6 (hq : CFSG.IsQuasisimple ↥L) (h : B42Case6 G L A) : B42Types ↥L := by
  obtain ⟨-, ⟨π, hπ⟩, -⟩ := h
  have : IsSimpleGroup (alternatingGroup (Fin 6)) := alt_isSimple (by norm_num)
  have : Nontrivial ↥L := CFSG.LocalCores.isQuasisimple_nontrivial hq
  obtain ⟨e⟩ := exists_mulEquiv_of_surjective_of_simple (Γ := alternatingGroup (Fin 6))
    (H := ↥L) π hπ.1
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨6, Or.inr (Or.inl rfl),
    ⟨e.symm⟩⟩)))))

theorem typeOf_case7 (hq : CFSG.IsQuasisimple ↥L) (h : B42Case7 G L A) : B42Types ↥L := by
  obtain ⟨-, -, ⟨α, π, hπ⟩, -⟩ := h
  have : IsSimpleGroup (alternatingGroup (Fin 7)) := alt_isSimple (by norm_num)
  have : Nontrivial ↥L := CFSG.LocalCores.isQuasisimple_nontrivial hq
  obtain ⟨e⟩ := exists_mulEquiv_of_surjective_of_simple (Γ := alternatingGroup (Fin 7))
    (H := ↥L) π hπ.1
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨7, Or.inr (Or.inr rfl),
    ⟨e.symm⟩⟩)))))

theorem typeOf_case8 (h : B42Case8 G L A) : B42Types ↥L := by
  obtain ⟨-, -, -, K, hK, hKfin, Γ₀, -, -, hHat, -, π, hπ, -⟩ := h
  have hinj : Function.Injective π := hπ.injective_of_faithful (FFModel.nat_faithful _)
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    (IsHat.of_mulEquiv (MulEquiv.ofBijective π ⟨hinj, hπ.1⟩) hHat)))))))

theorem typeOf_case9 (h : B42Case9 G L) : B42Types ↥L := by
  obtain ⟨-, n, hn, hnat, -⟩ := h
  obtain ⟨K, hK, hKfin, hcard, ⟨e⟩⟩ := BinaryNaturalSL.exists_equiv hnat
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    ⟨K, hK, hKfin, n, by simpa using hcard, hn, ⟨e.symm⟩⟩))))))

omit [Finite V] in
theorem typeOf_sl_two (hq : CFSG.IsQuasisimple ↥L) {n : ℕ} (hn : 3 ≤ n) (hn45 : n = 4 ∨ n = 5)
    (π : ↥(StatedSL n (ZMod 2)) →* ↥L) (hπ : Function.Surjective π) : B42Types ↥L := by
  have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) := isSimple_sl_zmod2 n hn
  have : IsSimpleGroup ↥(StatedSL n (ZMod 2)) :=
    (specialLinearGroupEquivStatedSL n (ZMod 2)).symm.isSimpleGroup
  have : Nontrivial ↥L := CFSG.LocalCores.isQuasisimple_nontrivial hq
  obtain ⟨e⟩ := exists_mulEquiv_of_surjective_of_simple (Γ := ↥(StatedSL n (ZMod 2)))
    (H := ↥L) π hπ
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    ⟨ZMod 2, inferInstance, inferInstance, n, by simp, hn45, ⟨e.symm⟩⟩))))))

end Cases

end TypeList

open TypeList in
theorem asB42Types_of_asB42With {KP : ∀ (Y : Type) [Group Y], Prop} (h : AsB42With KP) :
    ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
      ∀ G L : Subgroup (MulAut V), B4HypWith KP G L → (∃ A, IsFFStarOffender G A) →
        B42Types ↥L := by
  intro V _ _ hV G L hHyp hex
  obtain ⟨A, hA⟩ := hex
  have hconc := h V hV G L hHyp A hA
  have hL := hHyp.2.1
  have hq : CFSG.IsQuasisimple ↥L := hHyp.2.2.1
  have hLJ : L ≤ ffJ G := le_ffJ_of_b4Hyp hV hHyp hA
  have hnorm : (L.subgroupOf (ffJ G)).Normal := ⟨fun l hl g => by
    rw [Subgroup.mem_subgroupOf] at hl ⊢
    have h1 := CFSG.Quasithin.le_normalizer_quasithinGenFitting G (ffJ_le_self G g.2)
    rw [← hL] at h1
    exact (Subgroup.mem_normalizer_iff.1 h1 _).1 hl⟩
  rcases hconc with c1 | c2 | c3 | c4 | c5 | c6 | c7 | c8 | c9 | c10 | c11
  · exact typeOf_case1 hq c1
  · exact typeOf_case2 c2
  · exact typeOf_case3 hq hLJ hnorm c3
  · exact typeOf_case4 hLJ hnorm c4
  · exact typeOf_case5 hq hLJ hnorm c5
  · exact typeOf_case6 hq c6
  · exact typeOf_case7 hq c7
  · exact typeOf_case8 c8
  · exact typeOf_case9 c9
  · obtain ⟨⟨π, hπ⟩, -⟩ := c10
    exact typeOf_sl_two hq (n := 4) (by norm_num) (Or.inl rfl) π hπ.1
  · obtain ⟨-, -, -, -, π, hπ, -⟩ := c11
    exact typeOf_sl_two hq (n := 5) (by norm_num) (Or.inr rfl) π hπ.1

end CFSG.QuasithinUnique.Bridge
