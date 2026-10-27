module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.KFactsAbs
public import CFSG.LocalAnalysis.GLTheoremA.CatB.YS09StdSubFSp6
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVSp82

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.KFacts

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 TauCeti
open CFSG.LocalAnalysis.GLTheoremA.CatB.StdSp6 (Pm Pm_add)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence)

theorem lieIndex_isSp8two {S : Type} [Group S] (h : catalogIs S S8.L84.isSp82) :
    ∃ (q : PrimePower) (hv : (LieTypeIndex.B 4 q).Valid), q.card = 2 ∧
      Nonempty (S ≃* ValidLieTypeIndex.Group ⟨.B 4 q, hv⟩) := by
  obtain ⟨d, hv, hP, ⟨e⟩⟩ := exists_lieIndex h
  cases d with
  | B r q =>
    rcases r with _ | _ | _ | _ | _ | r
    · exact hP.elim
    · exact hP.elim
    · exact hP.elim
    · exact hP.elim
    · exact ⟨q, hv, hP, ⟨e⟩⟩
    · exact hP.elim
  | _ => exact hP.elim

theorem bridge_sp8two {S : Type} [Group S] (h : catalogIs S S8.L84.isSp82) :
    Nonempty (S ≃* StatedSp 4 (ZMod 2)) := by
  obtain ⟨q, hv, hq, ⟨e⟩⟩ := lieIndex_isSp8two h
  obtain ⟨h1, h2⟩ := primePower_eq_of_card_eq Nat.prime_two (s := 1) (by norm_num)
    (hq.trans (by norm_num))
  rcases CFSG.Models.lieModel_B 4 q hv e with hm | hm
  · rw [h1, h2] at hm
    obtain ⟨-, K, _, _, hK, ⟨e'⟩⟩ := hm.statedClassicalModel (by decide)
    obtain ⟨φ⟩ := exists_ringEquiv_zmod_two (K := K) (by rw [hK]; norm_num)
    exact ⟨e'.trans (statedProjEquivZMod2 φ
      (CFSG.Adapters.RankTwoModelTransports.glCongr_statedSp φ 4))⟩
  · rw [h1, h2] at hm
    exact absurd hm.admissible.2.2.2 (by norm_num)

theorem nonempty_sp82_equiv :
    Nonempty (StatedSp 4 (ZMod 2) ≃* CFSG.PGLModel.projSp 4 (GaloisField 2 1)) := by
  haveI : Nat.card (GaloisField 2 1) = 2 := by
    rw [GaloisField.card 2 1 one_ne_zero]; norm_num
  obtain ⟨φ⟩ := exists_ringEquiv_zmod_two (K := GaloisField 2 1) this
  exact ⟨(statedProjEquivZMod2 φ
    (CFSG.Adapters.RankTwoModelTransports.glCongr_statedSp φ 4)).symm.trans
    (CFSG.RankThree.PartTwo.Sec4.projSpEquivStatedProj 4 (GaloisField 2 1)).symm⟩

theorem card3_sp82 : (Nat.card (StatedSp 4 (ZMod 2))).factorization 3 = 5 := by
  obtain ⟨e⟩ := nonempty_sp82_equiv
  rw [Nat.card_congr e.toEquiv]
  exact CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIV.factorization_card_projSp_four_two

theorem outer_sp82 : ¬ 3 ∣ Nat.card (Outer (StatedSp 4 (ZMod 2))) := by
  obtain ⟨e⟩ := nonempty_sp82_equiv
  rw [Nat.card_congr (equivalence e).toEquiv]
  exact CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIV.not_three_dvd_card_outer_projSp_four_two

@[expose] def blk (v : Fin 4 → ZMod 3) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2) :=
  pb fun i => Pm (v i)

theorem vec4_eq (v : Fin 4 → ZMod 3) : v = ![v 0, v 1, v 2, v 3] := by
  funext i
  fin_cases i <;> rfl

theorem blk_eq (v : Fin 4 → ZMod 3) : blk v = pb ![Pm (v 0), Pm (v 1), Pm (v 2), Pm (v 3)] := by
  unfold blk
  congr 1
  funext i
  fin_cases i <;> rfl

theorem Pm_zero : Pm 0 = 1 := by simp [Pm]

theorem blk_mul_neg (v : Fin 4 → ZMod 3) : blk v * blk (-v) = 1 := by
  have h : (fun i => Pm (v i) * Pm ((-v) i)) = fun _ => (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) := by
    funext i
    rw [← Pm_add, Pi.neg_apply, add_neg_cancel, Pm_zero]
  unfold blk
  rw [pb_mul, h, pb_one]

theorem blk_symp_aux : ∀ a b c d : ZMod 3,
    (pb ![Pm a, Pm b, Pm c, Pm d]).transpose *
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2)) *
      pb ![Pm a, Pm b, Pm c, Pm d] = Matrix.fromBlocks 0 1 (-1) 0 := by
  decide +kernel

theorem blk_symp (v : Fin 4 → ZMod 3) :
    (blk v).transpose *
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2)) * blk v =
      Matrix.fromBlocks 0 1 (-1) 0 := by
  rw [blk_eq]
  exact blk_symp_aux _ _ _ _

@[expose] def tauM (v : Fin 4 → ZMod 3) : StatedSp 4 (ZMod 2) :=
  mkSpG (blk v) (blk (-v)) (blk_mul_neg v) (by simpa using blk_mul_neg (-v)) (blk_symp v)

theorem tauM_add (x y : Fin 4 → ZMod 3) : tauM (x + y) = tauM x * tauM y :=
  Subtype.ext (Units.ext (by
    show blk (x + y) = blk x * blk y
    unfold blk
    rw [pb_mul]
    congr 1
    funext i
    exact Pm_add _ _))

@[expose] def tau : Multiplicative (Fin 4 → ZMod 3) →* StatedSp 4 (ZMod 2) :=
  MonoidHom.mk' (fun v => tauM v.toAdd) fun x y => tauM_add x.toAdd y.toAdd

theorem blk_key : ∀ a b c d : ZMod 3, pb ![Pm a, Pm b, Pm c, Pm d] = 1 →
    (a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0) := by
  decide +kernel

theorem tau_injective : Function.Injective tau := by
  rw [injective_iff_map_eq_one]
  intro v hv
  have hm : blk v.toAdd = 1 := congrArg (fun g : StatedSp 4 (ZMod 2) =>
    (((g : GL (Fin 4 ⊕ Fin 4) (ZMod 2))).val : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2))) hv
  rw [blk_eq] at hm
  obtain ⟨h0, h1, h2, h3⟩ := blk_key _ _ _ _ hm
  apply Multiplicative.toAdd.injective
  rw [vec4_eq v.toAdd, h0, h1, h2, h3]
  funext i
  fin_cases i <;> rfl

theorem card_F1 : Nat.card tau.range = 3 ^ 4 := card_range_three tau tau_injective

@[expose] def rho : Fin 4 ⊕ Fin 4 → Fin 4 ⊕ Fin 4 := Sum.map ![1, 2, 0, 3] ![1, 2, 0, 3]

@[expose] def rhoInv : Fin 4 ⊕ Fin 4 → Fin 4 ⊕ Fin 4 := Sum.map ![2, 0, 1, 3] ![2, 0, 1, 3]

@[expose] def sigM : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2) :=
  Matrix.of fun x y => if x = rho y then 1 else 0

@[expose] def sigMInv : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2) :=
  Matrix.of fun x y => if x = rhoInv y then 1 else 0

theorem sig_symp : sigM.transpose *
    (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2)) * sigM =
      Matrix.fromBlocks 0 1 (-1) 0 := by
  decide +kernel

@[expose] def sigEl : StatedSp 4 (ZMod 2) :=
  mkSpG sigM sigMInv (by decide +kernel) (by decide +kernel) sig_symp

theorem sig_cube : sigM * sigM * sigM = 1 := by decide +kernel

theorem sigEl_cube : sigEl ^ 3 = 1 := by
  have h : sigEl ^ 3 = sigEl * sigEl * sigEl := by rw [pow_succ, pow_two]
  rw [h]
  exact Subtype.ext (Units.ext sig_cube)

theorem sig_conj : ∀ a b c d : ZMod 3, sigM * pb ![Pm a, Pm b, Pm c, Pm d] * sigMInv =
    pb ![Pm c, Pm a, Pm b, Pm d] := by
  decide +kernel

theorem sigEl_conj (v : Fin 4 → ZMod 3) :
    sigEl * tauM v * sigEl⁻¹ = tauM ![v 2, v 0, v 1, v 3] :=
  Subtype.ext (Units.ext (by
    show sigM * blk v * sigMInv = blk ![v 2, v 0, v 1, v 3]
    rw [blk_eq, blk_eq]
    exact sig_conj _ _ _ _))

theorem tauM_ne : tauM ![0, 1, 0, 0] ≠ tauM ![1, 0, 0, 0] := fun h =>
  absurd (Multiplicative.toAdd.injective (tau_injective (a₁ := Multiplicative.ofAdd ![0, 1, 0, 0])
    (a₂ := Multiplicative.ofAdd ![1, 0, 0, 0]) h) ▸ rfl : (![0, 1, 0, 0] : Fin 4 → ZMod 3) =
      ![1, 0, 0, 0]) (by decide)

theorem sigEl_mem_normalizer :
    sigEl ∈ Subgroup.normalizer (tau.range : Set (StatedSp 4 (ZMod 2))) := by
  apply mem_normalizer_of_forall_conj_mem
  rintro _ ⟨v, rfl⟩
  exact ⟨Multiplicative.ofAdd ![v.toAdd 2, v.toAdd 0, v.toAdd 1, v.toAdd 3],
    (sigEl_conj v.toAdd).symm⟩

theorem sigEl_not_mem_centralizer :
    sigEl ∉ Subgroup.centralizer (tau.range : Set (StatedSp 4 (ZMod 2))) := by
  intro h
  have hc := Subgroup.mem_centralizer_iff.1 h (tauM ![1, 0, 0, 0])
    ⟨Multiplicative.ofAdd ![1, 0, 0, 0], rfl⟩
  apply tauM_ne
  have := sigEl_conj ![1, 0, 0, 0]
  rw [← hc] at this
  simpa using this.symm

@[expose] def tM : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2) :=
  pb ![1, 1, 1, !![1, 1; 0, 1]]

theorem tM_sq : tM * tM = 1 := by unfold tM; decide +kernel

theorem tM_symp : tM.transpose *
    (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2)) * tM =
      Matrix.fromBlocks 0 1 (-1) 0 := by
  unfold tM; decide +kernel

theorem tM_ne : tM ≠ 1 := by unfold tM; decide +kernel

@[expose] def tEl : StatedSp 4 (ZMod 2) := mkSpG tM tM tM_sq tM_sq tM_symp

theorem tEl_sq : tEl ^ 2 = 1 := by
  rw [pow_two]
  exact Subtype.ext (Units.ext tM_sq)

theorem tEl_ne : tEl ≠ 1 := fun h => tM_ne (congrArg (fun g : StatedSp 4 (ZMod 2) =>
  (((g : GL (Fin 4 ⊕ Fin 4) (ZMod 2))).val : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2))) h)

theorem isPGroup_zpowers_tEl : IsPGroup 2 (Subgroup.zpowers tEl) :=
  IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, orderOf_eq_prime tEl_sq tEl_ne, pow_one])

@[expose] def emb34 : Multiplicative (Fin 3 → ZMod 3) →* Multiplicative (Fin 4 → ZMod 3) :=
  MonoidHom.mk' (fun v => Multiplicative.ofAdd ![v.toAdd 0, v.toAdd 1, v.toAdd 2, 0]) fun x y => by
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i <;> simp

theorem emb34_injective : Function.Injective emb34 := by
  intro x y h
  have h' := congrArg Multiplicative.toAdd h
  apply Multiplicative.toAdd.injective
  funext i
  fin_cases i
  · exact congrFun h' 0
  · exact congrFun h' 1
  · exact congrFun h' 2

@[expose] def tau3 : Multiplicative (Fin 3 → ZMod 3) →* StatedSp 4 (ZMod 2) := tau.comp emb34

theorem tau3_injective : Function.Injective tau3 := tau_injective.comp emb34_injective

theorem tM_comm : ∀ a b c : ZMod 3,
    pb ![Pm a, Pm b, Pm c, Pm 0] * tM = tM * pb ![Pm a, Pm b, Pm c, Pm 0] := by
  unfold tM; decide +kernel

theorem tau3_comm (v : Multiplicative (Fin 3 → ZMod 3)) : tau3 v * tEl = tEl * tau3 v :=
  Subtype.ext (Units.ext (by
    show blk ![v.toAdd 0, v.toAdd 1, v.toAdd 2, 0] * tM =
      tM * blk ![v.toAdd 0, v.toAdd 1, v.toAdd 2, 0]
    rw [blk_eq]
    exact tM_comm _ _ _))

theorem tau3_le_normalizer :
    tau3.range ≤
      Subgroup.normalizer ((Subgroup.zpowers tEl : Subgroup _) : Set (StatedSp 4 (ZMod 2))) := by
  rintro _ ⟨v, rfl⟩
  apply mem_normalizer_of_forall_conj_mem
  intro y hy
  have hc : Commute (tau3 v) tEl := tau3_comm v
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  rw [((hc.zpow_right n).eq)]
  simp only [mul_inv_cancel_right]
  exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) n

theorem kProfile_sp82 : KProfile (StatedSp 4 (ZMod 2)) where
  card3 := card3_sp82
  outer := outer_sp82
  nonab := exists_nonab_of_normalizing card3_sp82
    (isElemAbelian_range_three tau) card_F1
    sigEl_mem_normalizer ⟨1, by simpa using sigEl_cube⟩ sigEl_not_mem_centralizer
  e27 := ⟨tau3.range, Subgroup.zpowers tEl,
    isElemAbelian_range_three tau3, card_range_three tau3 tau3_injective,
    isPGroup_zpowers_tEl, fun h => tEl_ne (Subgroup.zpowers_eq_bot.1 h),
    tau3_le_normalizer⟩

end CFSG.LocalAnalysis.GLTheoremA.CatB.KFacts
