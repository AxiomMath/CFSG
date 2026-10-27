module

public import CFSG.LargeExtraspecial.S12InspFamOMinus
public import CFSG.LargeExtraspecial.O62Basic
public import CFSG.LargeExtraspecial.S12InspXFis

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module Matrix CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner equivalence)

namespace S12Insp4P

theorem false_of_dvd {X : Type} [Group X] (h20 : 20160 ∣ Nat.card X * Nat.card (Outer X))
    {a b : ℕ} (ha : Nat.card X ∣ a) (hb : Nat.card (Outer X) ∣ b) (hab : ¬ 20160 ∣ a * b) :
    False :=
  hab (h20.trans (Nat.mul_dvd_mul ha hb))

theorem false_of_two_pow_eight_dvd {K : Type*} [Group K] [Finite K]
    (hP : ∀ P : Subgroup K, IsPGroup 2 P → Nat.card P ≤ 2 ^ 7) (hdvd : 2 ^ 8 ∣ Nat.card K) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP8⟩ := Sylow.exists_subgroup_card_pow_prime 2 hdvd
  have h := hP P (IsPGroup.of_card hP8)
  rw [hP8] at h
  norm_num at h

theorem psl_cases {X : Type} [Group X] [Finite X] {n f : ℕ} (hn : 3 ≤ n) (hf : 1 ≤ f)
    (h : LieModel X .PSL n 2 f) (h2 : ∀ k, 2 ^ k ∣ Nat.card X → k ≤ 7)
    (h20 : 20160 ∣ Nat.card X * Nat.card (Outer X)) : (n = 3 ∧ f = 2) ∨ (n = 4 ∧ f = 1) := by
  have hcl := LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h
  have hc := (CFSG.Timmesfeld.card_statedClassicalModel_two hcl).1 rfl
  have hout := (CFSG.RankThree.OuterOrder.higher_linear_unitary_outer_order_determinant_bound
    (Or.inl rfl) hn Nat.prime_two hf hcl).1
  have hk := h2 _ (S12Insp4.two_pow_mul_dvd
    (show (2 ^ f) ^ ((n - 1) * (n - 1 + 1) / 2) ∣ Nat.card X by
      rw [hc]; exact S12Insp4.pow_dvd_ordA (by omega)))
  have hn4 : n ≤ 4 := by
    by_contra hlt
    have h20' : 4 * 5 ≤ (n - 1) * (n - 1 + 1) :=
      Nat.mul_le_mul (by omega : 4 ≤ n - 1) (by omega : 5 ≤ n - 1 + 1)
    have := Nat.le_mul_of_pos_left ((n - 1) * (n - 1 + 1) / 2) hf
    omega
  simp only [CFSG.RankThree.OuterOrder.determinantParameter] at hout
  interval_cases n
  · have hf2 : f ≤ 2 := by norm_num at hk; omega
    interval_cases f
    · exact (false_of_dvd h20 (a := 168) (b := 2) (by rw [hc]; decide)
        (by norm_num at hout; exact hout) (by decide)).elim
    · exact Or.inl ⟨rfl, rfl⟩
  · have hf1 : f = 1 := by norm_num at hk; omega
    exact Or.inr ⟨rfl, hf1⟩

theorem outcome_cases {X : Type} [Group X] [Finite X] (hX : CFSG.Timmesfeld.Outcome X)
    (h2 : ∀ k, 2 ^ k ∣ Nat.card X → k ≤ 7) (h20 : 20160 ∣ Nat.card X * Nat.card (Outer X)) :
    LieModel X .PSL 3 2 2 ∨ LieModel X .PSL 4 2 1 ∨ NativeSporadic.IsSporadic X .J2 := by
  rcases hX with ⟨n, f, hn, hf, h⟩ | ⟨n, f, hn, hf, h⟩ | ⟨n, f, hn, hf, h | h⟩ | ⟨f, hf, h⟩ |
    ⟨f, hf, τ, hτ, h⟩ | h | he | hJ
  · rcases psl_cases hn hf h h2 h20 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · have hcl := LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h
    have hc := (CFSG.Timmesfeld.card_statedClassicalModel_two hcl).2.2.1 rfl
    have h9 : 3 * 3 ≤ n * n := Nat.mul_le_mul hn hn
    have := Nat.le_mul_of_pos_left (n * n) hf
    exact (S12Insp4.false_of_two_pow_dvd h2 (a := f * (n * n)) (by omega)
      (S12Insp4.two_pow_mul_dvd (by rw [hc]; exact S12Insp4.pow_dvd_ordBC (by omega)))).elim
  · have hcl := LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h
    have hc := (CFSG.Timmesfeld.card_statedClassicalModel_two hcl).2.2.2.1 rfl
    have h12 : 4 * 3 ≤ n * (n - 1) := Nat.mul_le_mul hn (by omega)
    have := Nat.le_mul_of_pos_left (n * (n - 1)) hf
    exact (S12Insp4.false_of_two_pow_dvd h2 (a := f * (n * (n - 1))) (by omega)
      (S12Insp4.two_pow_mul_dvd (by rw [hc]; exact S12Insp4.pow_dvd_ordD _ _))).elim
  · have hcl := LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h
    have hc := (CFSG.Timmesfeld.card_statedClassicalModel_two hcl).2.2.2.2 rfl
    have h12 : 4 * 3 ≤ n * (n - 1) := Nat.mul_le_mul hn (by omega)
    have := Nat.le_mul_of_pos_left (n * (n - 1)) hf
    exact (S12Insp4.false_of_two_pow_dvd h2 (a := f * (n * (n - 1))) (by omega)
      (S12Insp4.two_pow_mul_dvd (by rw [hc]; exact S12Insp4.pow_dvd_ordTwistedD _ _))).elim
  · exact (S12Insp4.false_of_exceptional (by omega) (by decide) (fun _ => hf) h h2).elim
  · exact (S12Insp4.false_of_exceptional hf (by revert hτ; cases τ <;> decide)
      (fun hG => by subst hG; exact absurd hτ (by decide)) h h2).elim
  · obtain ⟨e⟩ := CFSG.Timmesfeld.nonempty_mulEquiv_PSU3_of_lieModel h
    have hcl := LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h
    have hout := (CFSG.RankThree.OuterOrder.higher_linear_unitary_outer_order_determinant_bound
      (Or.inr rfl) le_rfl Nat.prime_three le_rfl hcl).1
    simp only [CFSG.RankThree.OuterOrder.determinantParameter] at hout
    exact (false_of_dvd h20 (a := 6048) (b := 2)
      (by rw [Nat.card_congr e.toEquiv]; exact CFSG.Quasithin.H13.A7.nat_card_psu331_dvd)
      (by norm_num at hout; exact hout) (by decide)).elim
  · obtain ⟨e⟩ := he
    have hcX : Nat.card X = 360 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin]
      rfl
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (DW.isPGroup_outer_alt6 e)
    have h7 : 7 ∣ 360 * 2 ^ k := by
      rw [← hcX, ← hk]
      exact (by norm_num : 7 ∣ 20160).trans h20
    have hcop : Nat.Coprime 7 (2 ^ k) := Nat.Coprime.pow_right _ (by decide)
    exact absurd (hcop.dvd_of_dvd_mul_right h7) (by decide)
  · exact Or.inr (Or.inr hJ)

theorem false_of_perm_three_five {X : Type} [Group X] {m : ℕ} (hm : m = 3 ∨ m = 5)
    (φ : X ≃* Equiv.Perm (Fin m)) (h20 : 20160 ∣ Nat.card X * Nat.card (Outer X)) : False := by
  have hO : Nat.card (Outer X) = 1 := by
    rw [Nat.card_congr (equivalence φ).toEquiv]
    refine S12Insp4.card_outer_eq_one fun ψ => ?_
    rcases hm with rfl | rfl
    · obtain ⟨g, hg⟩ := CFSG.Quasithin.G11.G118.g118_perm_three_aut_inner ψ
      exact ⟨g, MulEquiv.ext fun x => (hg x).trans (MulAut.conj_apply g x).symm⟩
    · obtain ⟨g, hg⟩ := CFSG.Monster.B.TwoA.sym5_conj_surjective ψ
      exact ⟨g, hg.symm⟩
  rw [hO, S12Insp4.card_of_perm φ] at h20
  rcases hm with rfl | rfl <;> exact absurd h20 (by decide)

theorem card_eq_card_orthogonalGroup_of_model {X : Type} [Group X] {D : Set X} {m : ℕ}
    {Q : QuadraticForm (ZMod 2) (Fin (2 * m) → ZMod 2)}
    (hmod : fischerLinearModel D (fischerMatrixGroup fun A => ∀ x, Q (A *ᵥ x) = Q x)
      (fischerTransvections (QuadraticMap.polar Q) fun v => Q v = 1)) :
    Nat.card X = Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) := by
  obtain ⟨φ, -⟩ := hmod
  have hcl : (fischerMatrixGroup fun A : Matrix (Fin (2 * m)) (Fin (2 * m)) (ZMod 2) =>
      ∀ x, Q (A *ᵥ x) = Q x) = (TauCeti.QuadraticMap.orthogonalGroup Q).comap
        (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin (2 * m)) (ZMod 2)).toMonoidHom :=
    CFSG.ClassicalGroups.Orthogonal.closure_isometries_eq_comap rfl
  have hcm : (TauCeti.QuadraticMap.orthogonalGroup Q).comap
      (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin (2 * m)) (ZMod 2)).toMonoidHom =
        (TauCeti.QuadraticMap.orthogonalGroup Q).map
          (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin (2 * m)) (ZMod 2)).symm.toMonoidHom :=
    Subgroup.comap_equiv_eq_map_symm
      (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin (2 * m)) (ZMod 2))
      (TauCeti.QuadraticMap.orthogonalGroup Q)
  rw [Nat.card_congr φ.toEquiv, hcl, hcm, Subgroup.card_map_of_injective (MulEquiv.injective _)]

theorem setOf_eq_zero_eq_compl {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (Q : QuadraticForm (ZMod 2) V) : {v | Q v = 0} = {v | Q v = 1}ᶜ := by
  ext v
  simp only [Set.mem_ofPred_eq, Set.mem_compl_iff]
  rcases O62.zmod2_eq_zero_or_eq_one (Q v) with h | h <;> simp [h]

theorem card_orthogonalGroup_minus_four {Q : QuadraticForm (ZMod 2) (Fin (2 * 2) → ZMod 2)}
    (hnd : ∀ x, (∀ y, QuadraticMap.polar Q x y = 0) → x = 0)
    (hmin : ¬ ∃ W : Submodule (ZMod 2) (Fin (2 * 2) → ZMod 2),
      finrank (ZMod 2) W = 2 ∧ ∀ w ∈ W, Q w = 0) :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) = 120 := by
  have hprod := S12DW.card_orthogonalGroup_mul_ncard_eq (O62.nondegenerate_of_forall hnd)
    (m := 2) (by rw [Module.finrank_fin_fun])
  have h10 := S12Insp5.ncard_eq_ten_of_minus hnd hmin
  have hsum := Set.ncard_add_ncard_compl {v : Fin (2 * 2) → ZMod 2 | Q v = 1}
  have hcard : Nat.card (Fin (2 * 2) → ZMod 2) = 16 := by
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num
  rw [← setOf_eq_zero_eq_compl, hcard, h10] at hsum
  have h720 : 2 ^ (2 ^ 2) * ∏ j ∈ Finset.Icc 1 2, (2 ^ (2 * j) - 1) = 720 := by decide
  rw [h720, show {v : Fin (2 * 2) → ZMod 2 | Q v = 0}.ncard = 6 by omega] at hprod
  omega

theorem card_orthogonalGroup_six {Q : QuadraticForm (ZMod 2) (Fin (2 * 3) → ZMod 2)}
    (hnd : ∀ x, (∀ y, QuadraticMap.polar Q x y = 0) → x = 0) :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) = 40320 ∨
      Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) = 51840 :=
  O62.card_orthogonalGroup (by rw [Module.finrank_fin_fun]) (O62.nondegenerate_of_forall hnd)

theorem isPlus_of_card_orthogonalGroup {Q : QuadraticForm (ZMod 2) (Fin (2 * 3) → ZMod 2)}
    (hnd : ∀ x, (∀ y, QuadraticMap.polar Q x y = 0) → x = 0)
    (hc : Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) = 40320) : O62.IsPlus Q := by
  have hprod := S12DW.card_orthogonalGroup_mul_ncard_eq (O62.nondegenerate_of_forall hnd)
    (m := 3) (by rw [Module.finrank_fin_fun])
  have h1451520 : 2 ^ (3 ^ 2) * ∏ j ∈ Finset.Icc 1 3, (2 ^ (2 * j) - 1) = 1451520 := by decide
  rw [h1451520, hc] at hprod
  have hsum := Set.ncard_add_ncard_compl {v : Fin (2 * 3) → ZMod 2 | Q v = 1}
  have hcard : Nat.card (Fin (2 * 3) → ZMod 2) = 64 := by
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num
  rw [← setOf_eq_zero_eq_compl, hcard] at hsum
  have h28 : {v : Fin (2 * 3) → ZMod 2 | Q v = 1}.ncard = 28 := by omega
  obtain ⟨L, hL⟩ := CFSG.Fischer.Classification.exists_linearEquiv_of_ncard_eq Q O62.qPlus hnd
    O62.polar_qPlus_nondeg rfl (by rw [h28, O62.ncard_qPlus])
  exact O62.isPlus_of_qPlus L hL

end S12Insp4P

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem dvd_card_Mbar_of_section
    (hsec : ∀ N : Subgroup S.Mbar, N.Normal → 20160 ∣ Nat.card N ∨ 20160 ∣ N.index) :
    20160 ∣ Nat.card S.Mbar := by
  rcases hsec ⊥ inferInstance with h | h
  · rw [card_bot] at h
    norm_num at h
  · rwa [index_bot] at h

theorem dvd_card_Xbar12_mul_card_outer_of_section {g : G} {t : S.O} (hS : S.S12Standing g t)
    (hsec : ∀ N : Subgroup S.Mbar, N.Normal → 20160 ∣ Nat.card N ∨ 20160 ∣ N.index) :
    20160 ∣ Nat.card (S.Xbar12 g) * Nat.card (Outer (S.Xbar12 g)) :=
  (dvd_card_Mbar_of_section hsec).trans (card_Mbar_dvd_card_Xbar12_mul_card_outer hS)

theorem dvd_card_Xbar12_or_dvd_relIndex {g : G}
    (hsec : ∀ N : Subgroup S.Mbar, N.Normal → 20160 ∣ Nat.card N ∨ 20160 ∣ N.index) :
    20160 ∣ Nat.card (S.Xbar12 g) ∨ 20160 ∣ (S.Xbar12 g).relIndex S.Mbar := by
  have hN : ((S.Xbar12 g).subgroupOf S.Mbar).Normal := ⟨fun n hn m => by
    rw [mem_subgroupOf] at hn ⊢
    have := (mem_normalizer_iff.mp (Mbar_le_normalizer_Xbar12 m.2) (n : S.O)).mp hn
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using this⟩
  have e : Nat.card ((S.Xbar12 g).subgroupOf S.Mbar) = Nat.card (S.Xbar12 g) :=
    Nat.card_congr (subgroupOfEquivOfLe (Xbar12_le_Mbar (S := S) (g := g))).toEquiv
  rcases hsec _ hN with h | h
  · exact Or.inl (h.trans (dvd_of_eq e))
  · exact Or.inr h

theorem false_of_section {g : G} (hP : ∀ P : Subgroup S.Mbar, IsPGroup 2 P → Nat.card P ≤ 2 ^ 7)
    (hsec : ∀ N : Subgroup S.Mbar, N.Normal → 20160 ∣ Nat.card N ∨ 20160 ∣ N.index)
    (h4 : 4 ∣ Nat.card (S.Xbar12 g)) (h20 : ¬ 20160 ∣ Nat.card (S.Xbar12 g)) : False := by
  rcases dvd_card_Xbar12_or_dvd_relIndex (g := g) hsec with h | h
  · exact h20 h
  · have e : Nat.card ((S.Xbar12 g).subgroupOf S.Mbar) = Nat.card (S.Xbar12 g) :=
      Nat.card_congr (subgroupOfEquivOfLe (Xbar12_le_Mbar (S := S) (g := g))).toEquiv
    have hM : Nat.card (S.Xbar12 g) * (S.Xbar12 g).relIndex S.Mbar = Nat.card S.Mbar :=
      (congrArg (· * (S.Xbar12 g).relIndex S.Mbar) e.symm).trans
        (card_mul_index (H := (S.Xbar12 g).subgroupOf S.Mbar))
    refine S12Insp4P.false_of_two_pow_eight_dvd hP ?_
    rw [← hM]
    exact (show 2 ^ 8 ∣ 4 * 20160 by norm_num).trans (Nat.mul_dvd_mul h4 h)

end Setting

end CFSG.LargeExtraspecial
