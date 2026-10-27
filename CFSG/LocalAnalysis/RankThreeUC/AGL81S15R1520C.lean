module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RowStmts
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsLie
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1515A
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankBase
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankCases
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15LiftBasic
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1512C
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1517A
import CFSG.RankThree.PartOne.N143.Inspect613Even

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open Subgroup KFactsPair

section Centre

open scoped commutatorElement

theorem centre_barO2_eq_bot_of_pRank_three_aux_quot {D : Type*} [Group D]
    (hP : commutator (D ⧸ Subgroup.center D) = ⊤) :
    Subgroup.center (D ⧸ Subgroup.center D) = ⊥ := by
  have hsup : commutator D ⊔ Subgroup.center D = ⊤ := by
    have h1 : (commutator D).map (QuotientGroup.mk' (Subgroup.center D)) = ⊤ := by
      rw [← hP, _root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
    rw [eq_top_iff]
    intro x _
    have hx : QuotientGroup.mk' (Subgroup.center D) x ∈
        (commutator D).map (QuotientGroup.mk' (Subgroup.center D)) := by
      rw [h1]
      exact Subgroup.mem_top _
    obtain ⟨y, hy, hxy⟩ := hx
    have hyx : y⁻¹ * x ∈ Subgroup.center D := by
      rw [← QuotientGroup.ker_mk' (Subgroup.center D), MonoidHom.mem_ker, map_mul, map_inv, hxy]
      simp
    have hx' : x = y * (y⁻¹ * x) := by group
    rw [hx']
    exact Subgroup.mul_mem_sup hy hyx
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective z
  have hcomm : ∀ x : D, ⁅d, x⁆ ∈ Subgroup.center D := by
    intro x
    rw [← QuotientGroup.ker_mk' (Subgroup.center D), MonoidHom.mem_ker]
    have := Subgroup.mem_center_iff.1 hz (QuotientGroup.mk x)
    change (QuotientGroup.mk' (Subgroup.center D)) ⁅d, x⁆ = 1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact this.symm
  let g : D →* Subgroup.center D :=
    { toFun := fun x => ⟨⁅d, x⁆, hcomm x⟩
      map_one' := by ext; simp
      map_mul' := by
        intro x y
        refine Subtype.ext ?_
        show ⁅d, x * y⁆ = ⁅d, x⁆ * ⁅d, y⁆
        have h1 : ⁅d, x * y⁆ = ⁅d, x⁆ * (x * ⁅d, y⁆ * x⁻¹) := by
          simp [commutatorElement_def]; group
        have h2 : x * ⁅d, y⁆ * x⁻¹ = ⁅d, y⁆ := by
          have := Subgroup.mem_center_iff.1 (hcomm y) x
          rw [this]; simp
        rw [h1, h2] }
  have hker : commutator D ⊔ Subgroup.center D ≤ g.ker := by
    refine sup_le ?_ ?_
    · rw [_root_.commutator_def, Subgroup.commutator_le]
      intro a _ b _
      rw [MonoidHom.mem_ker]
      rw [map_commutatorElement g a b]
      refine Subtype.ext ?_
      show ⁅(g a : D), (g b : D)⁆ = 1
      exact commutatorElement_eq_one_iff_mul_comm.2
        (Subgroup.mem_center_iff.1 (g a).2 (g b : D)).symm
    · intro c hc
      rw [MonoidHom.mem_ker]
      ext
      change ⁅d, c⁆ = 1
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact Subgroup.mem_center_iff.1 hc d
  rw [hsup] at hker
  have hd : d ∈ Subgroup.center D := by
    rw [Subgroup.mem_center_iff]
    intro x
    have h := hker (Subgroup.mem_top x)
    rw [MonoidHom.mem_ker] at h
    have h' : ⁅d, x⁆ = 1 := congrArg Subtype.val h
    rw [commutatorElement_eq_one_iff_mul_comm] at h'
    exact h'.symm
  rw [Subgroup.mem_bot]
  exact (QuotientGroup.eq_one_iff d).2 hd

theorem centre_barO2_eq_bot_of_pRank_three_aux_centre {S : Type} [Group S] (hS : commutator S = ⊤)
    {d : TauCeti.ValidLieTypeIndex} (e : S ≃* (TauCeti.CFSGIndex.lie d).Group) :
    Subgroup.center S = ⊥ := by
  haveI : Group.IsPerfect S := ⟨hS⟩
  haveI : Group.IsPerfect (TauCeti.CFSGIndex.lie d).Group :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hc : Subgroup.center (TauCeti.CFSGIndex.lie d).Group = ⊥ :=
    centre_barO2_eq_bot_of_pRank_three_aux_quot
      (D := ↥(commutator ↥(TauCeti.fixedSubgroup d.steinberg)))
      Group.IsPerfect.commutator_eq_top
  rw [eq_bot_iff]
  intro z hz
  have hz' : e z ∈ Subgroup.center (TauCeti.CFSGIndex.lie d).Group := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨s, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz s]
  rw [hc, Subgroup.mem_bot] at hz'
  rw [Subgroup.mem_bot]
  exact e.injective (by simpa using hz')

theorem centre_barO2_eq_bot_of_pRank_three_aux_quotEquiv {S : Type} [Group S]
    (hS : commutator S = ⊤) {d : TauCeti.ValidLieTypeIndex}
    (e : S ≃* (TauCeti.CFSGIndex.lie d).Group) :
    Nonempty ((S ⧸ Subgroup.center S) ≃* (TauCeti.CFSGIndex.lie d).Group) :=
  ⟨(QuotientGroup.quotientMulEquivOfEq (centre_barO2_eq_bot_of_pRank_three_aux_centre hS e)).trans
    (QuotientGroup.quotientBot.trans e)⟩

theorem centre_barO2_eq_bot_of_pRank_three_aux_over {S : Type} [Group S] (hS : commutator S = ⊤)
    {f : TauCeti.PrimePower → TauCeti.LieTypeIndex} {c : ℕ → Prop} (h : IsLieIdxOver S f c) :
    ∃ (Q : TauCeti.PrimePower) (d : TauCeti.ValidLieTypeIndex), Q.p = 2 ∧ c Q.card ∧ d.1 = f Q ∧
      Nonempty ((S ⧸ Subgroup.center S) ≃* (TauCeti.CFSGIndex.lie d).Group) := by
  obtain ⟨Q, hQ2, hc, d, hd, ⟨e⟩⟩ := h
  exact ⟨Q, d, hQ2, hc, hd, centre_barO2_eq_bot_of_pRank_three_aux_quotEquiv hS e⟩

theorem centre_barO2_eq_bot_of_pRank_three_aux_classical {d : TauCeti.LieTypeIndex}
    (h : IsRankTwoPlus d) : IsClassicalOrG2Index d := by
  cases d <;> first | exact h.1 | exact h | exact h.elim

theorem centre_barO2_eq_bot_of_pRank_three_aux_ne {d : TauCeti.LieTypeIndex} (h : RankThreeList d) :
    (∀ Q, d ≠ .A 2 Q) ∧ (∀ Q, d ≠ .twistedA 4 Q) := by
  refine ⟨fun Q hd => ?_, fun Q hd => ?_⟩ <;> subst hd <;> simp [RankThreeList] at h

theorem centre_barO2_eq_bot_of_pRank_three_aux_sl3 {S : Type} [Group S] {n : ℕ} (hn : 2 ≤ n)
    (e : S ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 n)) :
    ∃ (d : TauCeti.ValidLieTypeIndex) (Q : TauCeti.PrimePower), Q.p = 2 ∧ Q.exponent = n ∧
      d.1 = .A 2 Q ∧ Nonempty ((S ⧸ Subgroup.center S) ≃* (TauCeti.CFSGIndex.lie d).Group) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let eP : (S ⧸ Subgroup.center S) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) (GaloisField 2 n) :=
    QuotientGroup.congr (Subgroup.center S)
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 n))) e
      (Subgroup.map_center_eq e)
  let Q : TauCeti.PrimePower := ⟨2, n, Nat.prime_two, by omega⟩
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hv : (TauCeti.LieTypeIndex.A 2 Q).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    refine ⟨⟨by norm_num, fun h => by omega⟩, ?_⟩
    have hc : Q.card = 2 ^ n := by rw [TauCeti.PrimePower.card_def]
    rintro (⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩)
    · omega
    · omega
    · omega
  obtain ⟨-, K, hF, hfin, hK, ⟨eK⟩⟩ :=
    CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv
      (MulEquiv.refl (TauCeti.CFSGIndex.lie ⟨.A 2 Q, hv⟩).Group)
  exact ⟨⟨_, hv⟩, Q, rfl, rfl, rfl, ⟨eP.trans
    ((CFSG.ClassicalModels.statedLinearModelEquivGaloisPSL K 3 2 n (by omega) hK).symm.trans
      eK.symm)⟩⟩

theorem centre_barO2_eq_bot_of_pRank_three_aux_sl2 {S : Type} [Group S]
    (e : S ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 1)) :
    ∃ (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower), q.card = 7 ∧ d.1 = .A 1 q ∧
      Nonempty ((S ⧸ Subgroup.center S) ≃* (TauCeti.CFSGIndex.lie d).Group) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  let eP : (S ⧸ Subgroup.center S) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) (GaloisField 2 1) :=
    QuotientGroup.congr (Subgroup.center S)
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 1))) e
      (Subgroup.map_center_eq e)
  let q : TauCeti.PrimePower := ⟨7, 1, Nat.prime_seven, Nat.one_pos⟩
  have hc : q.card = 7 := by rw [TauCeti.PrimePower.card_def]; norm_num
  have hv : (TauCeti.LieTypeIndex.A 1 q).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    refine ⟨⟨le_rfl, fun _ => by omega⟩, ?_⟩
    rintro (⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩) <;> omega
  obtain ⟨-, K, hF, hfin, hK, ⟨eK⟩⟩ :=
    CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv
      (MulEquiv.refl (TauCeti.CFSGIndex.lie ⟨.A 1 q, hv⟩).Group)
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = Fintype.card (ZMod 7) := by
    rw [ZMod.card, ← Nat.card_eq_fintype_card, hK]
    exact (TauCeti.PrimePower.card_def q).symm.trans hc
  let φ : K ≃+* ZMod 7 := FiniteField.ringEquivOfCardEq hcard
  let φ₁ : GaloisField 2 1 ≃+* ZMod 2 :=
    (CFSG.ClassicalModels.finiteFieldEquivGaloisField (ZMod 2) 2 1 Nat.one_pos
      (by rw [Nat.card_zmod]; norm_num)).symm
  let e₂ : Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) ≃*
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
    (QuotientGroup.quotientMulEquivOfEq
      CFSG.LocalAnalysis.ComponentInitial.center_SL_three_zmod_two_eq_bot).trans
      QuotientGroup.quotientBot
  let e₃ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) ≃* GL (Fin 3) (ZMod 2) :=
    MulEquiv.ofBijective _ CFSG.LocalAnalysis.ComponentInitial.bijective_toGL_three_zmod_two
  obtain ⟨e₄⟩ := CFSG.LocalAnalysis.ComponentInitial.nonempty_GL_three_two_equiv_PSL_two_seven
  exact ⟨⟨_, hv⟩, q, hc, rfl, ⟨eP.trans
    ((CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv φ₁ (Fin 3)).trans
      (e₂.trans (e₃.trans (e₄.trans
        ((CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv φ.symm (Fin 2)).trans
          ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).trans
            eK.symm))))))⟩⟩

end Centre

section CommutingRank

variable {X : Type} [Group X] [Finite X]

theorem pRank_three_lt_of_exists_aux_bot {Y : Type} [Group Y] [Finite Y] {q : ℕ} (hq : q.Prime) :
    CFSG.Open.pRank q (⊥ : Subgroup Y) = 0 := by
  refine Nat.le_zero.1 (CFSG.SectionRank.pRank_le hq.one_lt fun E hE _ => ?_)
  rw [le_bot_iff.1 hE]
  simp

theorem pRank_three_lt_of_exists {L : Subgroup X} (hL : IsC2 L)
    (hZ3 : CFSG.Open.pRank 3 L = 3 → Subgroup.center ↥(barO2 L) = ⊥)
    (hX3 : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 3) {I : Subgroup X} (hI : I ≤ cMHat L)
    (h3I : 1 ≤ CFSG.Open.pRank 3 I) : CFSG.Open.pRank 3 L < 3 := by
  have _ := hL
  by_contra hcon
  have hmono : ∀ U : Subgroup X, CFSG.Open.pRank 3 U ≤ 3 := fun U =>
    (CFSG.SectionRank.pRank_mono Nat.prime_three.one_lt le_top).trans hX3
  have hL3 : CFSG.Open.pRank 3 L = 3 := by have := hmono L; omega
  have hZ := hZ3 hL3
  have hc : ∀ a ∈ barO2 L, ∀ b ∈ barO2 I, a * b = b * a := by
    intro a ha b hb
    obtain ⟨y, hy, rfl⟩ := hb
    have h1 : y ∈ cMHat L := hI hy
    have h2 : (QuotientGroup.mk' (CFSG.pCore 2 X)) y ∈ cMBar L := h1
    exact (Subgroup.mem_centralizer_iff.1 h2) a ha
  have hinf : barO2 L ⊓ barO2 I = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxz : (⟨x, hx.1⟩ : ↥(barO2 L)) ∈ Subgroup.center ↥(barO2 L) := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hc g g.2 x hx.2)
    rw [hZ, Subgroup.mem_bot] at hxz
    exact (Subgroup.mem_bot).2 (congrArg Subtype.val hxz)
  have hmain := pRank_add_le_pRank_sup_add_pRank_inf hc Nat.prime_three
  rw [hinf, pRank_three_lt_of_exists_aux_bot Nat.prime_three, add_zero] at hmain
  have e1 : CFSG.Open.pRank 3 (barO2 L) = CFSG.Open.pRank 3 L :=
    (pRank_barO2_eq_aux_eq L Nat.prime_three (by norm_num)).symm
  have e2 : CFSG.Open.pRank 3 (barO2 I) = CFSG.Open.pRank 3 I :=
    (pRank_barO2_eq_aux_eq I Nat.prime_three (by norm_num)).symm
  have e3 : CFSG.Open.pRank 3 (barO2 L ⊔ barO2 I) = CFSG.Open.pRank 3 (L ⊔ I) := by
    rw [← Subgroup.map_sup]
    exact (pRank_barO2_eq_aux_eq _ Nat.prime_three (by norm_num)).symm
  have h4 := hmono (L ⊔ I)
  omega

end CommutingRank

section ExcludedGroups

variable {X : Type} [Group X] [Finite X]

theorem pRank_lift_eq_three_of_excluded_aux_chev (hRank : LieOddRankChev) {T L : Subgroup X}
    {Ls : Subgroup (X ⧸ gnC T)} (hX : GNSetting X T) (hLs : IsComponentOf Ls ⊤) (hL : LiftOf T L Ls)
    {d : TauCeti.ValidLieTypeIndex} (hd : IsClassicalOrG2Index d.1)
    (e : Nonempty ((↥Ls ⧸ Subgroup.center ↥Ls) ≃* (TauCeti.CFSGIndex.lie d).Group)) :
    CFSG.Open.pRank 3 L = mRankChev d.1 3 (Nat.card (Subgroup.center ↥(barO2 L))) := by
  obtain ⟨⟨eQ⟩, -, -⟩ := centre_of_lift hX hLs hL
  obtain ⟨e'⟩ := e
  have hK : CFSG.Open.IsQuasisimple ↥(barO2 L) := hL.1.component.2.2
  exact (pRank_barO2_eq hL.1 Nat.prime_three (by norm_num)).trans
    ((CFSG.SectionRank.pRank_eq_pRank_top_subgroup (barO2 L)).trans
      (hRank _ hK d hd ⟨eQ.trans e'⟩ 3 Nat.prime_three (by norm_num)))

theorem pRank_lift_eq_three_of_excluded_aux_even {Q : TauCeti.PrimePower} (hQ : Q.p = 2)
    (hc : ¬ 3 ∣ Q.card + 1) : Even Q.exponent := by
  by_contra hn
  obtain ⟨k, hk⟩ := Nat.not_even_iff_odd.1 hn
  apply hc
  rw [TauCeti.PrimePower.card_def, hQ, hk, pow_succ, pow_mul]
  have h : (2 ^ 2) ^ k % 3 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  omega

theorem pRank_lift_eq_three_of_excluded_aux_odd {Q : TauCeti.PrimePower} (hQ : Q.p = 2)
    (hc : ¬ 3 ∣ Q.card - 1) : Odd Q.exponent := by
  by_contra hn
  obtain ⟨k, hk⟩ := Nat.not_odd_iff_even.1 hn
  apply hc
  rw [TauCeti.PrimePower.card_def, hQ, hk, ← two_mul, pow_mul]
  have h : (2 ^ 2) ^ k % 3 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  have hpos : 0 < (2 ^ 2) ^ k := by positivity
  omega

theorem pRank_lift_eq_three_of_excluded_aux_rank3 (hRank : LieOddRankChev) {T L : Subgroup X}
    {Ls : Subgroup (X ⧸ gnC T)} (hX : GNSetting X T) (hLs : IsComponentOf Ls ⊤) (hL : LiftOf T L Ls)
    {d : TauCeti.ValidLieTypeIndex} (hdr : IsRankTwoPlus d.1) (hR : RankThreeList d.1)
    (e : Ls ≃* (TauCeti.CFSGIndex.lie d).Group) : CFSG.Open.pRank 3 L = 3 := by
  obtain ⟨e'⟩ := centre_barO2_eq_bot_of_pRank_three_aux_quotEquiv hLs.2.2.1 e
  rw [pRank_lift_eq_three_of_excluded_aux_chev hRank hX hLs hL
    (centre_barO2_eq_bot_of_pRank_three_aux_classical hdr) ⟨e'⟩]
  exact ((mRank3_cases hdr _).2.2.1).2 hR

theorem pRank_lift_eq_three_of_excluded_aux_alt (hAlt : LieOddRankAlt) {T L : Subgroup X}
    {Ls : Subgroup (X ⧸ gnC T)} (hX : GNSetting X T) (hLs : IsComponentOf Ls ⊤) (hL : LiftOf T L Ls)
    (e : Ls ≃* alternatingGroup (Fin 10)) : CFSG.Open.pRank 3 L = 3 := by
  obtain ⟨-, ⟨e'⟩⟩ := quotCenter_equiv_alt (n := 10) (by norm_num) e
  obtain ⟨⟨eQ⟩, -, -⟩ := centre_of_lift hX hLs hL
  have hK : CFSG.Open.IsQuasisimple ↥(barO2 L) := hL.1.component.2.2
  rw [(pRank_barO2_eq hL.1 Nat.prime_three (by norm_num)).trans
    (CFSG.SectionRank.pRank_eq_pRank_top_subgroup (barO2 L)),
    hAlt _ hK 10 (by norm_num) ⟨eQ.trans e'⟩ 3 Nat.prime_three (by norm_num)]

theorem pRank_lift_eq_three_of_excluded (hRank : LieOddRankChev) (hAlt : LieOddRankAlt) {T L : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)}
    (hX : GNSetting X T) (hLs : IsComponentOf Ls ⊤) (hL : LiftOf T L Ls)
    (h : IsSpSix (fun _ => True) ↥Ls ∨ IsOmegaEightMinus (fun _ => True) ↥Ls ∨ IsLinTwo 6 ↥Ls ∨
      IsLinTwo 7 ↥Ls ∨ Nonempty (↥Ls ≃* alternatingGroup (Fin 10)) ∨
      IsLFour (fun Q => ¬ 3 ∣ Q + 1) ↥Ls ∨ IsUFour (fun Q => ¬ 3 ∣ Q - 1) ↥Ls) :
    CFSG.Open.pRank 3 L = 3 := by
  rcases h with h | h | h | h | h | h | h
  · obtain ⟨Q, hQ, -, d, hd, he⟩ := h
    exact pRank_lift_three_of_bad hRank hX hLs hL (p := Q.card + 1)
      (Or.inr (Or.inl ⟨Q, hQ, dvd_refl _, d, hd, he⟩))
  · obtain ⟨Q, hQ, -, d, hd, he⟩ := h
    exact pRank_lift_three_of_bad hRank hX hLs hL (p := Q.card + 1)
      (Or.inr (Or.inr ⟨Q, hQ, dvd_refl _, d, hd, he⟩))
  · exact pRank_lift_three_of_bad hRank hX hLs hL (p := 7) (Or.inl ⟨Or.inl h, rfl⟩)
  · exact pRank_lift_three_of_bad hRank hX hLs hL (p := 7) (Or.inl ⟨Or.inr h, rfl⟩)
  · obtain ⟨e⟩ := h
    exact pRank_lift_eq_three_of_excluded_aux_alt hAlt hX hLs hL e
  · rcases h with ⟨Q, hQ, hc, d, hd, ⟨e⟩⟩ | ⟨hc2, -⟩
    · exact pRank_lift_eq_three_of_excluded_aux_rank3 hRank hX hLs hL
        (by rw [hd]; exact ⟨hQ, by norm_num⟩)
        (by rw [hd]; exact pRank_lift_eq_three_of_excluded_aux_even hQ hc) e
    · exact absurd (by norm_num : 3 ∣ 2 + 1) hc2
  · obtain ⟨Q, hQ, hc, d, hd, ⟨e⟩⟩ := h
    exact pRank_lift_eq_three_of_excluded_aux_rank3 hRank hX hLs hL
      (by rw [hd]; exact ⟨hQ, le_refl 3⟩)
      (by rw [hd]; exact pRank_lift_eq_three_of_excluded_aux_odd hQ hc) e

end ExcludedGroups

section ListCentre

variable {X : Type} [Group X] [Finite X]

theorem centre_barO2_eq_bot_of_pRank_three_aux_lie (hRank : LieOddRankChev) (hKSMOdd : KSMOdd)
    (hKSMU4 : KSMU4) {T L : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)} (hX : GNSetting X T)
    (hLs : IsComponentOf Ls ⊤) (hL : LiftOf T L Ls) {d : TauCeti.ValidLieTypeIndex}
    (hdr : IsRankTwoPlus d.1) (hd : In1512 d.1)
    (e : Nonempty ((↥Ls ⧸ Subgroup.center ↥Ls) ≃* (TauCeti.CFSGIndex.lie d).Group))
    (h3 : CFSG.Open.pRank 3 L = 3) : Subgroup.center ↥(barO2 L) = ⊥ := by
  obtain ⟨⟨eQ⟩, -, -⟩ := centre_of_lift hX hLs hL
  obtain ⟨e'⟩ := e
  have hK : CFSG.Open.IsQuasisimple ↥(barO2 L) := hL.1.component.2.2
  have h1 := pRank_lift_eq_three_of_excluded_aux_chev hRank hX hLs hL
    (centre_barO2_eq_bot_of_pRank_three_aux_classical hdr) ⟨e'⟩
  have hR : RankThreeList d.1 := ((mRank3_cases hdr _).2.2.1).1 (h1.symm.trans h3)
  obtain ⟨h2, h4⟩ := centre_barO2_eq_bot_of_pRank_three_aux_ne hR
  exact centre_eq_bot_of_in1512 hKSMOdd hKSMU4 hK hd h2 h4 ⟨eQ.trans e'⟩ (centre_barO2_odd hL.1)

theorem centre_barO2_eq_bot_of_pRank_three (hT : LieOddRankTable) (hKSMOdd : KSMOdd) (hKSMU4 : KSMU4)
    (hKSMAlt : KSMAlt) {T T₁ T₂ L : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)} (hX : GNSetting X T)
    (hshape : GNShape T T₁ T₂) (hLs : GNYComponent T T₁ T₂ Ls) (hL : LiftOf T L Ls)
    (hlist : IsGroupOf1512 ↥Ls) (h3 : CFSG.Open.pRank 3 L = 3) :
    Subgroup.center ↥(barO2 L) = ⊥ := by
  have _ := hshape
  have hLs' : IsComponentOf Ls ⊤ := hLs.1
  have hS : commutator ↥Ls = ⊤ := hLs'.2.2.1
  obtain ⟨⟨eQ⟩, -, -⟩ := centre_of_lift hX hLs' hL
  have hK : CFSG.Open.IsQuasisimple ↥(barO2 L) := hL.1.component.2.2
  have hodd := centre_barO2_odd hL.1
  have hr : CFSG.Open.pRank 3 L = CFSG.Open.pRank 3 (⊤ : Subgroup ↥(barO2 L)) :=
    (pRank_barO2_eq hL.1 Nat.prime_three (by norm_num)).trans
      (CFSG.SectionRank.pRank_eq_pRank_top_subgroup (barO2 L))
  have lie : ∀ {d : TauCeti.ValidLieTypeIndex}, IsRankTwoPlus d.1 → In1512 d.1 →
      Nonempty ((↥Ls ⧸ Subgroup.center ↥Ls) ≃* (TauCeti.CFSGIndex.lie d).Group) →
      Subgroup.center ↥(barO2 L) = ⊥ := fun hdr hd e =>
    centre_barO2_eq_bot_of_pRank_three_aux_lie hT.chev hKSMOdd hKSMU4 hX hLs' hL hdr hd e h3
  have lieIdx : ∀ {f : TauCeti.PrimePower → TauCeti.LieTypeIndex} {c : ℕ → Prop},
      IsLieIdxOver ↥Ls f c →
      (∀ Q : TauCeti.PrimePower, Q.p = 2 → c Q.card → IsRankTwoPlus (f Q) ∧ In1512 (f Q)) →
      Subgroup.center ↥(barO2 L) = ⊥ := fun h hf => by
    obtain ⟨Q, d, hQ2, hc, hd, e⟩ := centre_barO2_eq_bot_of_pRank_three_aux_over hS h
    obtain ⟨hdr, hd1⟩ := hf Q hQ2 hc
    exact lie (by rw [hd]; exact hdr) (by rw [hd]; exact hd1) e
  have alt : ∀ {n : ℕ}, 5 ≤ n →
      Nonempty ((↥Ls ⧸ Subgroup.center ↥Ls) ≃* alternatingGroup (Fin n)) →
      CFSG.Open.pRank 3 L = n / 3 := fun hn ⟨e⟩ => by
    rw [hr]
    exact hT.alt _ hK _ hn ⟨eQ.trans e⟩ 3 Nat.prime_three (by norm_num)
  have altS : ∀ {n : ℕ}, 5 ≤ n → Nonempty (↥Ls ≃* alternatingGroup (Fin n)) →
      CFSG.Open.pRank 3 L = n / 3 := fun hn ⟨e⟩ =>
    alt hn (quotCenter_equiv_alt (by omega) e).2
  rcases hlist with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exfalso
    have := alt (n := 6) (by norm_num) h.2.2
    omega
  · exfalso
    have := altS (n := 7) (by norm_num) h
    omega
  · obtain ⟨e⟩ := h
    obtain ⟨-, ⟨e'⟩⟩ := quotCenter_equiv_alt (n := 10) (by norm_num) e
    exact Subgroup.eq_bot_of_card_eq _ ((hKSMAlt _ hK 10 ⟨eQ.trans e'⟩ hodd).2 (by norm_num))
  · rcases h with h | ⟨-, d, ⟨q, hq3, hd⟩, ⟨e⟩⟩
    · exact lieIdx h (fun Q hQ _ => ⟨hQ, hQ⟩)
    · exfalso
      obtain ⟨e'⟩ := centre_barO2_eq_bot_of_pRank_three_aux_quotEquiv hS e
      have := (hT.small _ hK 3 Nat.prime_three (by norm_num)).2 ⟨q, d, hq3, hd, ⟨eQ.trans e'⟩⟩
      rw [← hr] at this
      simp at this
      omega
  · obtain ⟨n, hn, -, ⟨e⟩⟩ := h
    rcases Nat.lt_or_ge n 2 with hlt | hge
    · obtain rfl : n = 1 := by omega
      exfalso
      obtain ⟨d, q, hq7, hd, ⟨e'⟩⟩ := centre_barO2_eq_bot_of_pRank_three_aux_sl2 e
      have := (hT.small _ hK 3 Nat.prime_three (by norm_num)).1 ⟨q, d, hq7, hd, ⟨eQ.trans e'⟩⟩
      rw [← hr] at this
      simp at this
      omega
    · obtain ⟨d, Q, hQ2, -, hd, e'⟩ := centre_barO2_eq_bot_of_pRank_three_aux_sl3 hge e
      exact lie (by rw [hd]; exact ⟨hQ2, le_refl 2⟩) (by rw [hd]; exact hQ2) e'
  · rcases h with h | ⟨-, e⟩
    · exact lieIdx h (fun Q hQ _ => ⟨⟨hQ, by norm_num⟩, hQ⟩)
    · exfalso
      have := altS (n := 8) (by norm_num) e
      omega
  · exact lieIdx h (fun Q hQ _ => ⟨⟨hQ, le_refl 3⟩, hQ⟩)
  · rcases h with h | ⟨-, e⟩
    · exact lieIdx h (fun Q hQ _ => ⟨⟨hQ, le_refl 2⟩, hQ⟩)
    · exfalso
      have := altS (n := 6) (by norm_num) e
      omega
  · exact lieIdx h (fun Q hQ _ => ⟨⟨hQ, by norm_num⟩, hQ⟩)
  · exact lieIdx h (fun Q hQ _ => ⟨⟨hQ, le_refl 4⟩, hQ⟩)
  · exact lieIdx h (fun Q hQ hc => ⟨⟨hQ, by norm_num⟩, hc⟩)
  · exact lieIdx h (fun Q hQ hc => ⟨⟨hQ, by norm_num⟩, hc⟩)
  · exact lieIdx h (fun Q hQ hc => ⟨⟨hQ, by norm_num⟩, hc⟩)
  · exact lieIdx h (fun Q hQ hc => ⟨⟨hQ, by norm_num⟩, hc⟩)

end ListCentre

end CFSG.LocalAnalysis.RankThreeUC.S15
