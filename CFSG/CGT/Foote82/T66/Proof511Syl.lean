module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCat81E6A8Gen4
public import CFSG.GH74.GLS.Gen4Exclusions
public import CFSG.GH74.GLS.C3.Layer1.Th2AModelSucc
public import CFSG.CGT.T75P.A8ExclE16
public import Certificates.Certificate919201
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.GH73.S8Facts

public section

namespace CFSG.CGT.Foote82.Proof511

open Subgroup Equiv Equiv.Perm CFSG.ComponentClassification.GSThmB.Cat81A8

theorem card_subtype_mem_filter {α : Type*} [DecidableEq α] (L : List α) (hL : L.Nodup)
    (p : α → Prop) [DecidablePred p] :
    Nat.card {y // y ∈ L ∧ p y} = (L.filter fun y => decide (p y)).length := by
  have h1 : Nat.card {y // y ∈ L ∧ p y} =
      Nat.card ↥(L.filter fun y => decide (p y)).toFinset :=
    Nat.card_congr (Equiv.subtypeEquivRight fun y => by simp [List.mem_filter])
  rw [h1, Nat.card_eq_finsetCard, List.toFinset_card_of_nodup (hL.filter _)]

theorem card_sqOne_congr {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    Nat.card {x : A // x ^ 2 = 1} = Nat.card {y : B // y ^ 2 = 1} :=
  Nat.card_congr (e.toEquiv.subtypeEquiv fun x => by
    change x ^ 2 = 1 ↔ e x ^ 2 = 1
    rw [← map_pow, MulEquiv.map_eq_one_iff])

@[expose] def IsA10Type (P : Type*) [Group P] : Prop :=
  Nonempty (P ≃* ↥T8)

theorem sqOne_count_holds :
    (TList.filter fun y => decide (y * y = 1)).length = 44 :=
  Certificates.certificate919201

theorem sqOne_card_T8 :
    Nat.card {x : ↥T8 // x ^ 2 = 1} = 44 := by
  classical
  have h1 : Nat.card {x : ↥T8 // x ^ 2 = 1} =
      Nat.card {y : Perm (Fin 8) // y ∈ TList ∧ y * y = 1} :=
    Nat.card_congr
      { toFun := fun x => ⟨x.1, mem_T8_iff.mp x.1.2, by
          have h := congrArg Subtype.val x.2
          simpa [sq] using h⟩
        invFun := fun y => ⟨⟨y.1, mem_T8_iff.mpr y.2.1⟩, Subtype.ext (by simpa [sq] using y.2.2)⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
  rw [h1, card_subtype_mem_filter TList (bfs_nodup gensT 8) (fun y => y * y = 1)]
  exact sqOne_count_holds

theorem swap02_mem : (swap 0 2 : Perm (Fin 8)) ∈ T8 := by
  have h : (swap 0 2 : Perm (Fin 8)) = ts := by decide
  rw [h]
  exact mem_T8_of_mem_gensT (by simp [gensT])

theorem swap13_mem : (swap 1 3 : Perm (Fin 8)) ∈ T8 := by
  have h : (swap 1 3 : Perm (Fin 8)) = tr * ts * tr⁻¹ := by decide
  rw [h]
  have hr : tr ∈ T8 := mem_T8_of_mem_gensT (by simp [gensT])
  have hs : ts ∈ T8 := mem_T8_of_mem_gensT (by simp [gensT])
  exact mul_mem (mul_mem hr hs) (inv_mem hr)

theorem swap46_mem : (swap 4 6 : Perm (Fin 8)) ∈ T8 := by
  have h : (swap 4 6 : Perm (Fin 8)) = tw * ts * tw⁻¹ := by decide
  rw [h]
  have hw : tw ∈ T8 := mem_T8_of_mem_gensT (by simp [gensT])
  have hs : ts ∈ T8 := mem_T8_of_mem_gensT (by simp [gensT])
  exact mul_mem (mul_mem hw hs) (inv_mem hw)

theorem swap57_mem : (swap 5 7 : Perm (Fin 8)) ∈ T8 := by
  have h : (swap 5 7 : Perm (Fin 8)) = tw * swap 1 3 * tw⁻¹ := by decide
  rw [h]
  have hw : tw ∈ T8 := mem_T8_of_mem_gensT (by simp [gensT])
  exact mul_mem (mul_mem hw swap13_mem) (inv_mem hw)

@[expose] noncomputable def e16gen : Fin 4 → ↥T8
  | 0 => ⟨swap 0 2, swap02_mem⟩
  | 1 => ⟨swap 1 3, swap13_mem⟩
  | 2 => ⟨swap 4 6, swap46_mem⟩
  | 3 => ⟨swap 5 7, swap57_mem⟩

theorem exists_e16_T8 : ∃ E : Subgroup ↥T8, Nat.card E = 16 ∧ ∀ x ∈ E, x ^ 2 = 1 := by
  refine CFSG.CGT.T75P.a8x_exists_E16 e16gen ?_ ?_ ?_
  · intro i
    apply Subtype.ext
    fin_cases i <;> decide
  · intro i j
    apply Subtype.ext
    fin_cases i <;> fin_cases j <;> decide
  · intro a ha h
    have hdec : ∀ a : Fin 4 → Fin 2, a ≠ 0 →
        (swap 0 2 : Perm (Fin 8)) ^ (a 0 : ℕ) * ((swap 1 3) ^ (a 1 : ℕ) *
          ((swap 4 6) ^ (a 2 : ℕ) * (swap 5 7) ^ (a 3 : ℕ))) ≠ 1 := by decide
    apply hdec a ha
    have h' := congrArg Subtype.val h
    rw [CFSG.CGT.T75P.a8x_prod_four] at h'
    simpa [e16gen] using h'


@[expose] def unitsToPerm2 : ℤˣ →* Perm (Fin 2) where
  toFun u := if u = 1 then 1 else swap 0 1
  map_one' := if_pos rfl
  map_mul' := by decide

theorem sign_unitsToPerm2 (u : ℤˣ) : sign (unitsToPerm2 u) = u := by
  rcases Int.units_eq_one_or u with rfl | rfl <;> decide

@[expose] def toPerm10 : Perm (Fin 8) →* Perm (Fin 10) :=
  (finSumFinEquiv.permCongrHom : Perm (Fin 8 ⊕ Fin 2) ≃* Perm (Fin (8 + 2))).toMonoidHom.comp
    ((sumCongrHom (Fin 8) (Fin 2)).comp ((MonoidHom.id _).prod (unitsToPerm2.comp sign)))

theorem sign_toPerm10 (σ : Perm (Fin 8)) : sign (toPerm10 σ) = 1 := by
  change sign (finSumFinEquiv.permCongr (Equiv.Perm.sumCongr σ (unitsToPerm2 (sign σ)))) = 1
  rw [sign_permCongr, sign_sumCongr, sign_unitsToPerm2, Int.units_mul_self]

theorem toPerm10_injective : Function.Injective toPerm10 := by
  intro σ τ h
  have h1 := (finSumFinEquiv.permCongrHom : Perm (Fin 8 ⊕ Fin 2) ≃* Perm (Fin (8 + 2))).injective h
  have h2 := sumCongrHom_injective h1
  exact congrArg Prod.fst h2

@[expose] def toAlt10 : Perm (Fin 8) →* alternatingGroup (Fin 10) :=
  toPerm10.codRestrict (alternatingGroup (Fin 10)) fun σ =>
    mem_alternatingGroup.mpr (sign_toPerm10 σ)

theorem toAlt10_injective : Function.Injective toAlt10 := fun _ _ h =>
  toPerm10_injective (congrArg Subtype.val h)

theorem isA10Type_of_map {X : Type*} [Group X] [Finite X]
    (φ : Perm (Fin 8) →* X) (hφ : Function.Injective φ) (m : ℕ) (hX : Nat.card X = 128 * m)
    (hm : ¬ 2 ∣ m) (Q : Sylow 2 X) : IsA10Type ↥(Q : Subgroup X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : Nat.card (T8.map φ) = 128 := by rw [card_map_of_injective hφ, card_T8]
  let S₀ : Sylow 2 X := IsPGroup.toSylow (P := T8.map φ)
    (IsPGroup.of_card (n := 7) (by rw [hc]; norm_num)) (by
      have h := (T8.map φ).card_mul_index
      rw [hc, hX] at h
      have hi : (T8.map φ).index = m := by
        have h128 : (0 : ℕ) < 128 := by norm_num
        exact Nat.eq_of_mul_eq_mul_left h128 h
      rw [hi]
      exact hm)
  exact ⟨(Sylow.equiv Q S₀).trans (T8.equivMapOfInjective φ hφ).symm⟩

theorem isA10Type_of_alt10
    (Q : Sylow 2 ↥(alternatingGroup (Fin 10))) :
    IsA10Type ↥(Q : Subgroup ↥(alternatingGroup (Fin 10))) :=
  isA10Type_of_map toAlt10 toAlt10_injective 14175
    (by rw [nat_card_alternatingGroup, Nat.card_fin]; decide) (by decide) Q

theorem isA10Type_of_perm8 (Q : Sylow 2 (Perm (Fin 8))) :
    IsA10Type ↥(Q : Subgroup (Perm (Fin 8))) :=
  isA10Type_of_map (MonoidHom.id _) Function.injective_id 315
    (by rw [Nat.card_perm, Nat.card_fin]; decide) (by decide) Q

theorem isA10Type_of_perm9 (Q : Sylow 2 (Perm (Fin 9))) :
    IsA10Type ↥(Q : Subgroup (Perm (Fin 9))) :=
  isA10Type_of_map (CFSG.GH74.GLS.C3.Layer1.Bk.extendLastPerm 8)
    CFSG.GH74.GLS.C3.Layer1.Bk.extendLastPerm_injective 2835
    (by rw [Nat.card_perm, Nat.card_fin]; decide) (by decide) Q

theorem isA8Type_of_alt9 (Q : Sylow 2 ↥(alternatingGroup (Fin 9))) :
    CFSG.GH74.Uniqueness.SU.SU5.IsA8Type ↥(Q : Subgroup ↥(alternatingGroup (Fin 9))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q₈⟩ := (inferInstance : Nonempty (Sylow 2 ↥(alternatingGroup (Fin 8))))
  have h64 : Nat.card ↥(Q₈ : Subgroup ↥(alternatingGroup (Fin 8))) = 64 :=
    CFSG.EvenSporadicStandard.HNRecog.GH73.IsA8Type.card_eq ⟨Q₈, ⟨MulEquiv.refl _⟩⟩
  let ι := CFSG.GH74.GLS.C3.Layer1.Bk.extendLastAlt 8
  have hι : Function.Injective ι := CFSG.GH74.GLS.C3.Layer1.Bk.extendLastAlt_injective
  have hc : Nat.card ((Q₈ : Subgroup ↥(alternatingGroup (Fin 8))).map ι) = 64 := by rw [card_map_of_injective hι, h64]
  let S₀ : Sylow 2 ↥(alternatingGroup (Fin 9)) := IsPGroup.toSylow (P := (Q₈ : Subgroup ↥(alternatingGroup (Fin 8))).map ι)
    (IsPGroup.of_card (n := 6) (by rw [hc]; norm_num)) (by
      have h := ((Q₈ : Subgroup ↥(alternatingGroup (Fin 8))).map ι).card_mul_index
      have hA : Nat.card ↥(alternatingGroup (Fin 9)) = 64 * 2835 := by
        rw [nat_card_alternatingGroup, Nat.card_fin]; decide
      rw [hc, hA] at h
      have hi : ((Q₈ : Subgroup ↥(alternatingGroup (Fin 8))).map ι).index = 2835 :=
        Nat.eq_of_mul_eq_mul_left (by norm_num : (0 : ℕ) < 64) h
      rw [hi]
      decide)
  exact ⟨Q₈, ⟨(Sylow.equiv Q S₀).trans ((Q₈ : Subgroup ↥(alternatingGroup (Fin 8))).equivMapOfInjective ι hι).symm⟩⟩

structure A10SylowData (X : Type) [Group X] : Prop where
  card_eq : ∃ j : ℕ, Nat.card X = 128 * (2 * j + 1)
  sqOne : ∀ T : Sylow 2 X, Nat.card {x : ↥(T : Subgroup X) // x ^ 2 = 1} = 44
  exists_e16 : ∃ E : Subgroup X, Nat.card E = 16 ∧ ∀ x ∈ E, x ^ 2 = 1
  gen_four : ∀ P : Subgroup X, IsPGroup 2 P →
    ∃ s : Finset X, s.card ≤ 4 ∧ Subgroup.closure (s : Set X) = P

theorem A10SylowData.of_sylow
    {X : Type} [Group X] [Finite X] (S : Sylow 2 X) (h : IsA10Type ↥(S : Subgroup X)) :
    A10SylowData X := by
  classical
  haveI : Finite (Sylow 2 X) := Sylow.finite_of_finiteIndex S
  have hT : ∀ T : Sylow 2 X, IsA10Type ↥(T : Subgroup X) := by
    intro T
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X S T
    obtain ⟨e⟩ := h
    rw [← hg]
    exact ⟨(S.equivSMul g).symm.trans e⟩
  obtain ⟨e⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨j, hj⟩ :=
      (Nat.not_even_iff_odd.mp fun he => S.not_dvd_index (even_iff_two_dvd.mp he) : Odd S.index)
    refine ⟨j, ?_⟩
    rw [← Subgroup.card_mul_index (S : Subgroup X), Nat.card_congr e.toEquiv, card_T8, hj]
  · intro T
    obtain ⟨eT⟩ := hT T
    rw [card_sqOne_congr eT, sqOne_card_T8]
  · obtain ⟨E, hEcard, hEsq⟩ := exists_e16_T8
    refine ⟨(E.map e.symm.toMonoidHom).map (S : Subgroup X).subtype, ?_, ?_⟩
    · rw [card_map_of_injective (S : Subgroup X).subtype_injective,
        card_map_of_injective e.symm.injective, hEcard]
    · intro y hy
      obtain ⟨u, hu, rfl⟩ := mem_map.mp hy
      obtain ⟨v, hv, rfl⟩ := mem_map.mp hu
      have h1 := hEsq v hv
      have h2 : (e.symm.toMonoidHom v) ^ 2 = 1 := by rw [← map_pow, h1, map_one]
      have h3 := congrArg (S : Subgroup X).subtype h2
      rwa [map_pow, map_one] at h3
  · exact CFSG.GH74.SectionalTwoRankLE.of_sylow S
      (CFSG.GH74.SectionalTwoRankLE.of_mulEquiv e.symm gen4_T8)

end CFSG.CGT.Foote82.Proof511
