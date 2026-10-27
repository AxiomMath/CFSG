module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.FStdDiagDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ExcRankMain
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ExcOrdMain
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ClsExcOut
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ClsLabel
public import CFSG.LocalAnalysis.GLTheoremA.CatB.List93RkTits

public section

namespace CFSG.LocalAnalysis.GLTheoremA.FStdDiag

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 TauCeti
open CFSG.HardMathSupport.Solomon.Coordinator renaming fixSubgroup → coordFix
open CFSG.LocalAnalysis.GLTheoremA.Y10GField (InnDiagKind FamLin FamUni FamSymp FamOrth FamExc
  fam_cover)
open CFSG.LocalAnalysis.GLTheoremA.HStdExcl (SmallOrd)
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)
open CFSG.ComponentClassification.OuterAutomorphisms renaming inner → innerAut
open CFSG.HardMathSupport.Solomon.Coordinator.I1420 (lieOrderFormula)

theorem fstd_cq_dvd_card {S : Type} [Group S] [Finite S] (I : Subgroup S) :
    Nat.card (↥I ⧸ Subgroup.center ↥I) ∣ Nat.card S :=
  (Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_subgroup_dvd_card I)

theorem fstd_not_smallOrd_of_card {S : Type} [Group S] [Finite S] (I : Subgroup S)
    (h1 : ¬ 25920 ∣ Nat.card S) (h2 : ¬ 360 ∣ Nat.card S) : ¬ SmallOrd I := by
  rintro (h | h) <;> [exact h1 (h ▸ fstd_cq_dvd_card I); exact h2 (h ▸ fstd_cq_dvd_card I)]

theorem fstd_three_dvd_of_smallOrd {S : Type} [Group S] [Finite S] {I : Subgroup S}
    (h : SmallOrd I) : 3 ∣ Nat.card S := by
  rcases h with h | h <;> exact dvd_trans (by norm_num) (h ▸ fstd_cq_dvd_card I)

theorem fstd_eq_one_of_card_360 {S : Type} [Group S] [Finite S] (hS : Nat.card S = 360)
    {α : MulAut S} {I : Subgroup S} (hI : CFSG.Open.IsComponentOf I (coordFix α))
    (h : SmallOrd I) : α = 1 := by
  have hle : Nat.card (↥I ⧸ Subgroup.center ↥I) ≤ Nat.card ↥I :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)
  have hIS : Nat.card ↥I ≤ 360 :=
    hS ▸ Nat.le_of_dvd Nat.card_pos (Subgroup.card_subgroup_dvd_card I)
  have hI360 : Nat.card ↥I = Nat.card S := by
    rcases h with h | h <;> omega
  have htop : I = ⊤ := Subgroup.eq_top_of_card_eq I hI360
  ext s
  have hs : s ∈ coordFix α := hI.1 (htop ▸ Subgroup.mem_top s)
  have hs' : α s = s := hs
  rw [hs', MulAut.one_apply]

theorem fstd_exists_elemAbelian_of_le_inner {S : Type} [Group S] [Finite S]
    (hZ : Subgroup.center S = ⊥) {A : Subgroup (MulAut S)}
    (hA : CFSG.Assembly.IsElemAbelian 3 A) (hAi : A ≤ innerAut S) :
    ∃ F : Subgroup S, CFSG.Assembly.IsElemAbelian 3 F ∧ Nat.card ↥F = Nat.card ↥A := by
  have hinj : Function.Injective (MulAut.conj : S →* MulAut S) := by
    intro a b hab
    have hc : a⁻¹ * b ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h1 := DFunLike.congr_fun hab g
      simp only [MulAut.conj_apply] at h1
      calc g * (a⁻¹ * b) = a⁻¹ * (a * g * a⁻¹) * b := by group
        _ = a⁻¹ * (b * g * b⁻¹) * b := by rw [h1]
        _ = a⁻¹ * b * g := by group
    rw [hZ, Subgroup.mem_bot] at hc
    calc a = a * (a⁻¹ * b) := by rw [hc, mul_one]
      _ = b := by group
  refine ⟨A.comap MulAut.conj, ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
  · apply Subtype.ext
    apply hinj
    have h := hA.1.is_comm.comm (⟨MulAut.conj (x : S), x.2⟩ : ↥A) ⟨MulAut.conj (y : S), y.2⟩
    have h' := congrArg Subtype.val h
    simp only [Subgroup.coe_mul] at h' ⊢
    rw [map_mul, map_mul]
    exact h'
  · apply hinj
    rw [map_pow, hA.2 _ hx, map_one]
  · have hmap : (A.comap MulAut.conj).map MulAut.conj = A :=
      Subgroup.map_comap_eq_self (fun β hβ => hAi hβ)
    rw [← Subgroup.card_map_of_injective hinj, hmap]

theorem fstd_27_dvd_of_elemAbelian {G : Type} [Group G] [Finite G] {A : Subgroup G}
    (hA : CFSG.Assembly.IsElemAbelian 3 A) (hc : 27 ≤ Nat.card ↥A) : 27 ∣ Nat.card ↥A := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 ↥A := fun g => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (by rw [Subgroup.coe_pow, hA.2 _ g.2, Subgroup.coe_one])⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hp
  rw [hk] at hc ⊢
  have hk3 : 3 ≤ k := by
    by_contra hlt
    have : 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  exact (Nat.pow_dvd_pow 3 hk3)

theorem fstd_card_lt_of_alt8 {S : Type} [Group S] [Finite S]
    (e : S ≃* alternatingGroup (Fin 8)) {A : Subgroup (MulAut S)}
    (hA : CFSG.Assembly.IsElemAbelian 3 A) : Nat.card ↥A < 27 := by
  by_contra hlt
  have hge : 27 ≤ Nat.card ↥A := by omega
  have h27 := fstd_27_dvd_of_elemAbelian hA hge
  obtain ⟨hinj, hsurj⟩ := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 8
    (by norm_num) (by norm_num)
  let φ : Equiv.Perm (Fin 8) ≃* MulAut (alternatingGroup (Fin 8)) := MulEquiv.ofBijective _
    ⟨hinj, hsurj⟩
  let ψ : ↥A →* Equiv.Perm (Fin 8) :=
    (φ.symm.toMonoidHom.comp (MulAut.congr e).toMonoidHom).comp A.subtype
  have hψ : Function.Injective ψ := by
    intro a b hab
    exact Subtype.ext ((MulAut.congr e).injective (φ.symm.injective hab))
  have hdvd := Subgroup.card_dvd_of_injective ψ hψ
  have h8 : Nat.card (Fin 8) = 8 := by simp
  rw [Nat.card_perm, h8] at hdvd
  have := h27.trans hdvd
  norm_num [Nat.factorial] at this

section Dispatch


theorem fstd_false_of_ambiguous {S : Type} [Group S] [Finite S]
    (hamb : catalogIs S (ambiguousChev 2)) {A : Subgroup (MulAut S)}
    (hA : CFSG.Assembly.IsElemAbelian 3 A) (hAc : 27 ≤ Nat.card ↥A) {α : MulAut S} (hα1 : α ≠ 1)
    {I : Subgroup S} (hI : CFSG.Open.IsComponentOf I (coordFix α)) (hsm : SmallOrd I) :
    False := by
  obtain ⟨i, hi, ⟨e⟩⟩ := hamb
  cases i with
  | cyclic p hp => exact hi.elim
  | sporadic n => exact hi.elim
  | alternating n hn =>
    have hn' : n = 5 ∨ n = 6 ∨ n = 8 := by
      simp only [ambiguousChev] at hi
      omega
    have e' : S ≃* alternatingGroup (Fin n) := e
    haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
    have hcard : Nat.card S = n.factorial / 2 := by
      rw [Nat.card_congr e'.toEquiv, nat_card_alternatingGroup]
      simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
    rcases hn' with rfl | rfl | rfl
    · exact fstd_not_smallOrd_of_card I (by rw [hcard]; decide) (by rw [hcard]; decide) hsm
    · exact hα1 (fstd_eq_one_of_card_360 (by rw [hcard]; decide) hI hsm)
    · have := fstd_card_lt_of_alt8 e' hA
      omega
  | lie dl =>
    obtain ⟨d, hv⟩ := dl
    have hcard := CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds ⟨d, hv⟩ S ⟨e⟩
    cases d with
    | A r q =>
      rcases r with _ | _ | r
      · exact hi.elim
      · have hq : q.card = 7 := by
          simp only [ambiguousChev] at hi
          omega
        refine fstd_not_smallOrd_of_card I ?_ ?_ hsm <;> rw [hcard] <;>
          simp only [lieOrderFormula, hq] <;> decide +kernel
      · exact hi.elim
    | twistedA r q =>
      rcases r with _ | _ | _ | r
      · exact hi.elim
      · exact hi.elim
      · have hq : q.card = 3 := by
          simp only [ambiguousChev] at hi
          omega
        refine fstd_not_smallOrd_of_card I ?_ ?_ hsm <;> rw [hcard] <;>
          simp only [lieOrderFormula, hq] <;> decide +kernel
      · rcases r with _ | r
        · exact absurd hi.2 (by norm_num)
        · exact hi.elim
    | _ => exact hi.elim

theorem fstd_false_of_famExc (hExc : SmallExcRes) {S : Type} [Group S] [Finite S]
    (hs : IsSimpleGroup S) (hnab : ∃ a b : S, a * b ≠ b * a) (hch : IsChevSimple 2 S)
    {labK : GLALabel} (hE : FamExc labK) {A : Subgroup (MulAut S)}
    (hA : CFSG.Assembly.IsElemAbelian 3 A) (hAc : 27 ≤ Nat.card ↥A)
    (hAk : ∀ β ∈ A, InnDiagKind S labK β) {α : MulAut S} (hαA : α ∈ A) (hα1 : α ≠ 1)
    {I : Subgroup S} (hI : CFSG.Open.IsComponentOf I (coordFix α)) (hsm : SmallOrd I) :
    False := by
  have hcen : Subgroup.center S = ⊥ :=
    CFSG.SignalizerFunctorTheorem.CatalogBridge.center_eq_bot_of_isSimpleGroup_of_noncomm hs hnab
  have hα3 : α ^ 3 = 1 := hA.2 α hαA
  have hin := hAk α hαA
  rcases hch with ⟨i, hi, ⟨e⟩⟩ | hamb
  · cases i with
    | cyclic _ _ => exact hi.elim
    | alternating _ _ => exact hi.elim
    | sporadic _ => exact hi.elim
    | lie dl =>
      obtain ⟨d, hv⟩ := dl
      have hc : d.characteristic = 2 := hi
      have hcls : ¬ CFSG.LocalAnalysis.GLTheoremA.K1419.I1419ClassLie d := by
        intro hcl
        obtain ⟨eZ⟩ := CFSG.LocalAnalysis.GLTheoremA.K1419E.nonempty_quotCenter_equiv_of_bot hcen
        exact CFSG.LocalAnalysis.GLTheoremA.K1419.k1419ClsExcOut_of_rigid
          CFSG.StandardType.ggLabelRigidInput_holds
          CFSG.LocalAnalysis.GLTheoremA.K1419.k1419ClsClassLabel_holds S labK
          (CFSG.LocalAnalysis.GLTheoremA.K144I.openQuasisimple_of_simple hs hnab)
          (CFSG.StandardType.Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.1) hin)
          ⟨.lie ⟨d, hv⟩, ⟨hc, hcl⟩, ⟨eZ.trans e⟩⟩ hE
      have hrk : ∀ (hd : CFSG.LocalAnalysis.GLTheoremA.K1419E.ExcIdx d)
          (hd' : CFSG.HardMathSupport.Dickson.Sec6.FamG2 d ∨
            CFSG.HardMathSupport.Dickson.Sec6.FamTriD4 d ∨
            CFSG.HardMathSupport.Dickson.Sec6.FamReeF4 d)
          (hct : CFSG.HardMathSupport.Solomon.Coordinator.IsCharTwoLieIndex d), False := by
        intro hd hd' hct
        obtain ⟨hinn, hrank⟩ := CFSG.LocalAnalysis.GLTheoremA.K1419E.l3u3Rank_exc ⟨d, hv⟩ hd' hct e
        have hAinn : A ≤ innerAut S := fun β hβ => hinn
          (CFSG.LocalAnalysis.GLTheoremA.K1419E.mem_innAutDerived_of_exc hs hnab (d := ⟨d, hv⟩)
            hd hc e (hAk β hβ))
        obtain ⟨F, hF, hFc⟩ := fstd_exists_elemAbelian_of_le_inner hcen hA hAinn
        have := hrank F hF
        omega
      have hexc : ∀ (hd : CFSG.LocalAnalysis.GLTheoremA.K1419E.ExcIdx d)
          (hd' : CFSG.HardMathSupport.Dickson.Sec6.FamF4 d ∨
            CFSG.HardMathSupport.Dickson.Sec6.FamE6 d ∨
            CFSG.HardMathSupport.Dickson.Sec6.FamTwE6 d ∨
            CFSG.HardMathSupport.Dickson.Sec6.FamE7 d ∨
            CFSG.HardMathSupport.Dickson.Sec6.FamE8 d), False := fun hd hd' =>
        hExc S ⟨d, hv⟩ hd' hc e α
          (CFSG.LocalAnalysis.GLTheoremA.K1419E.mem_innAutDerived_of_exc hs hnab (d := ⟨d, hv⟩)
            hd hc e hin) hα3 hα1 I hI hsm
      cases d with
      | A r q => exact hcls trivial
      | twistedA r q => exact hcls trivial
      | B r q => exact hcls trivial
      | C r q => exact hcls trivial
      | D r q => exact hcls trivial
      | twistedD r q => exact hcls trivial
      | G2 q =>
        exact hrk (Or.inl trivial) (Or.inl trivial)
          ((LieTypeIndex.characteristic_G2 q).symm.trans hc)
      | trialityD4 q =>
        exact hrk (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl trivial)))))))
          (Or.inr (Or.inl trivial)) ((LieTypeIndex.characteristic_trialityD4 q).symm.trans hc)
      | reeF4 m =>
        exact hrk (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr trivial)))))))
          (Or.inr (Or.inr trivial)) trivial
      | F4 q => exact hexc (Or.inr (Or.inl trivial)) (Or.inl trivial)
      | E6 q => exact hexc (Or.inr (Or.inr (Or.inl trivial))) (Or.inr (Or.inl trivial))
      | twistedE6 q =>
        exact hexc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl trivial))))))
          (Or.inr (Or.inr (Or.inl trivial)))
      | E7 q =>
        exact hexc (Or.inr (Or.inr (Or.inr (Or.inl trivial))))
          (Or.inr (Or.inr (Or.inr (Or.inl trivial))))
      | E8 q =>
        exact hexc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl trivial)))))
          (Or.inr (Or.inr (Or.inr (Or.inr trivial))))
      | suzuki m =>
        have hcard := CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds ⟨_, hv⟩ S ⟨e⟩
        apply CFSG.LocalAnalysis.GLTheoremA.K1419E.l3u3Ord_not_three_dvd_orderSuzuki m
        have h3 := fstd_three_dvd_of_smallOrd hsm
        rwa [hcard] at h3
      | tits =>
        have hlt := ((List93.tits_holds S ⟨.lie ⟨_, hv⟩, rfl, ⟨e⟩⟩).1 A hA)
        omega
      | reeG2 m =>
        have h3 : (LieTypeIndex.reeG2 m).characteristic = 3 := LieTypeIndex.characteristic_reeG2 m
        omega
  · exact fstd_false_of_ambiguous hamb hA hAc hα1 hI hsm

theorem smallCentreS_of_res (hLin : SmallFam FamLin) (hUni : SmallFam FamUni)
    (hSymp : SmallFam FamSymp) (hOrth : SmallFam FamOrth) (hExc : SmallExcRes) :
    SmallCentreS := by
  intro S _ _ hs hnab hch labK A hA hAc hAk α hαA hα1 I hI hsm
  have hcen : Subgroup.center S = ⊥ :=
    CFSG.SignalizerFunctorTheorem.CatalogBridge.center_eq_bot_of_isSimpleGroup_of_noncomm hs hnab
  have hα3 : α ^ 3 = 1 := hA.2 α hαA
  have hin := hAk α hαA
  rcases fam_cover labK with hL | hU | hSp | hO | hE
  · exact hLin S labK α I hL hcen hα3 hα1 hin hI hsm
  · exact hUni S labK α I hU hcen hα3 hα1 hin hI hsm
  · exact hSymp S labK α I hSp hcen hα3 hα1 hin hI hsm
  · exact hOrth S labK α I hO hcen hα3 hα1 hin hI hsm
  · exact (fstd_false_of_famExc hExc hs hnab hch hE hA hAc hAk hαA hα1 hI hsm).elim

end Dispatch

end CFSG.LocalAnalysis.GLTheoremA.FStdDiag

end
