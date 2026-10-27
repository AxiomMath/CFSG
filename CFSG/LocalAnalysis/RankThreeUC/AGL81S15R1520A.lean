module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1517Defs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsLie
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1512H
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1515C
import CFSG.RankThree.PartOne.N143.Inspect613Even

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open Subgroup KFactsPair

variable {X : Type} [Group X] [Finite X]

section CentreLemmas

theorem not_dvd_centre_barO2_of_row1512_aux0 {P : Type*} [Group P]
    (h : commutator (P ⧸ Subgroup.center P) = ⊤) :
    Subgroup.center (P ⧸ Subgroup.center P) = ⊥ := by
  set Z := Subgroup.center P with hZ
  set π : P →* P ⧸ Z := QuotientGroup.mk' Z with hπ
  set N : Subgroup P := (Subgroup.center (P ⧸ Z)).comap π with hN
  have hNZ : ⁅N, (⊤ : Subgroup P)⁆ ≤ Z := by
    rw [Subgroup.commutator_le]
    intro n hn g _
    rw [← QuotientGroup.ker_mk' Z, MonoidHom.mem_ker, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    exact ((Subgroup.mem_center_iff.1 hn) (π g)).symm
  have h1 : ⁅⁅N, (⊤ : Subgroup P)⁆, (⊤ : Subgroup P)⁆ = ⊥ := by
    refine le_bot_iff.1 ((Subgroup.commutator_mono hNZ le_rfl).trans ?_)
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer.2 (by
      rw [Subgroup.coe_top, Subgroup.centralizer_univ])).le
  have h2 : ⁅⁅(⊤ : Subgroup P), (⊤ : Subgroup P)⁆, N⁆ = ⊥ :=
    Subgroup.commutator_commutator_eq_bot_of_rotate
      (by rw [Subgroup.commutator_comm (⊤ : Subgroup P) N]; exact h1) h1
  have hcomm : ∀ c ∈ commutator P, ∀ x ∈ N, c * x = x * c := by
    intro c hc x hx
    have := (Subgroup.commutator_eq_bot_iff_le_centralizer.1 h2) hc
    exact ((Subgroup.mem_centralizer_iff.1 this) x hx).symm
  have hdec : ∀ y : P, ∃ c ∈ commutator P, ∃ z ∈ Z, y = c * z := by
    intro y
    have hmem : π y ∈ (commutator P).map π := by
      have : (commutator P).map π = commutator (P ⧸ Z) := by
        rw [map_commutator_eq, MonoidHom.range_eq_top_of_surjective π
          (QuotientGroup.mk'_surjective Z), ← _root_.commutator_def]
      rw [this, h]
      exact Subgroup.mem_top _
    obtain ⟨c, hc, hcy⟩ := hmem
    have h3 : π (c⁻¹ * y) = 1 := by rw [map_mul, map_inv, hcy, inv_mul_cancel]
    exact ⟨c, hc, c⁻¹ * y, (QuotientGroup.eq_one_iff _).1 h3, by group⟩
  rw [Subgroup.eq_bot_iff_forall]
  intro g hg
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
  have hxN : x ∈ N := hg
  have hxZ : x ∈ Z := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨c, hc, z, hz, rfl⟩ := hdec y
    calc c * z * x = c * (z * x) := mul_assoc _ _ _
      _ = c * (x * z) := by rw [(Subgroup.mem_center_iff.1 hz) x]
      _ = (c * x) * z := (mul_assoc _ _ _).symm
      _ = (x * c) * z := by rw [hcomm c hc x hxN]
      _ = x * (c * z) := mul_assoc _ _ _
  exact (QuotientGroup.eq_one_iff x).2 hxZ

theorem not_dvd_centre_barO2_of_row1512_aux1 {S : Type} [Group S] (hS : commutator S = ⊤)
    {d : TauCeti.ValidLieTypeIndex} (e : S ≃* (TauCeti.CFSGIndex.lie d).Group) :
    Subgroup.center S = ⊥ := by
  haveI : Group.IsPerfect S := ⟨hS⟩
  haveI : Group.IsPerfect (TauCeti.CFSGIndex.lie d).Group :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hG : commutator (TauCeti.CFSGIndex.lie d).Group = ⊤ := Group.IsPerfect.commutator_eq_top
  have hc : Subgroup.center (TauCeti.CFSGIndex.lie d).Group = ⊥ :=
    not_dvd_centre_barO2_of_row1512_aux0
      (P := ↥(commutator ↥(TauCeti.fixedSubgroup d.steinberg))) hG
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  have hz' : e z ∈ Subgroup.center (TauCeti.CFSGIndex.lie d).Group := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨s, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz s]
  rw [hc, Subgroup.mem_bot] at hz'
  exact e.injective (by simpa using hz')

theorem not_dvd_centre_barO2_of_row1512_aux2 {S : Type} [Group S] (hS : commutator S = ⊤)
    {d : TauCeti.ValidLieTypeIndex} (e : S ≃* (TauCeti.CFSGIndex.lie d).Group) :
    Nonempty ((S ⧸ Subgroup.center S) ≃* (TauCeti.CFSGIndex.lie d).Group) :=
  ⟨(QuotientGroup.quotientMulEquivOfEq (not_dvd_centre_barO2_of_row1512_aux1 hS e)).trans
    (QuotientGroup.quotientBot.trans e)⟩

theorem not_dvd_centre_barO2_of_row1512_aux3 (hKSMAlt : KSMAlt) {K : Type} [Group K] [Finite K]
    (hK : CFSG.Open.IsQuasisimple K) (hodd : Odd (Nat.card (Subgroup.center K))) {n : ℕ}
    (hn : 6 ≤ n) (e : Nonempty ((K ⧸ Subgroup.center K) ≃* alternatingGroup (Fin n))) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) : ¬ p ∣ Nat.card (Subgroup.center K) := by
  intro hpz
  obtain ⟨h67, h8⟩ := hKSMAlt K hK n e hodd
  by_cases h : n = 6 ∨ n = 7
  · have := Nat.le_of_dvd (by norm_num) (hpz.trans (h67 h))
    omega
  · have h1 := h8 (by omega)
    rw [h1] at hpz
    exact hp.one_lt.ne' (Nat.dvd_one.1 hpz)

theorem not_dvd_centre_barO2_of_row1512_aux4 {S : Type} [Group S] (hS : commutator S = ⊤)
    {f : TauCeti.PrimePower → TauCeti.LieTypeIndex} {c : ℕ → Prop} (h : IsLieIdxOver S f c) :
    ∃ (Q : TauCeti.PrimePower) (d : TauCeti.ValidLieTypeIndex), Q.p = 2 ∧ c Q.card ∧ d.1 = f Q ∧
      Nonempty ((S ⧸ Subgroup.center S) ≃* (TauCeti.CFSGIndex.lie d).Group) := by
  obtain ⟨Q, hQ2, hc, d, hd, ⟨e⟩⟩ := h
  exact ⟨Q, d, hQ2, hc, hd, not_dvd_centre_barO2_of_row1512_aux2 hS e⟩

theorem not_dvd_centre_barO2_of_row1512_aux5 {S : Type} [Group S] {n : ℕ} (hn : 2 ≤ n)
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
  obtain ⟨-, K, hF, hfin, hK, ⟨eK⟩⟩ := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv
    (MulEquiv.refl (TauCeti.CFSGIndex.lie ⟨.A 2 Q, hv⟩).Group)
  exact ⟨⟨_, hv⟩, Q, rfl, rfl, rfl, ⟨eP.trans
    ((CFSG.ClassicalModels.statedLinearModelEquivGaloisPSL K 3 2 n (by omega) hK).symm.trans
      eK.symm)⟩⟩

theorem not_dvd_centre_barO2_of_row1512_aux6 {S : Type} [Group S]
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
  obtain ⟨-, K, hF, hfin, hK, ⟨eK⟩⟩ := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv
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

end CentreLemmas

theorem not_dvd_centre_barO2_of_row1512 (hKSMOdd : KSMOdd) (hKSMU4 : KSMU4) (hKSML3 : KSML3)
    (hKSMAlt : KSMAlt) {T L : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)} (hX : GNSetting X T)
    (hLs : IsComponentOf Ls ⊤) (hL : LiftOf T L Ls) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hlist : IsGroupOf1512 ↥Ls) (hU5 : IsUFiveFour ↥Ls → p ≠ 5) :
    ¬ p ∣ Nat.card (Subgroup.center ↥(barO2 L)) := by
  obtain ⟨⟨eQ⟩, -, -⟩ := centre_of_lift hX hLs hL
  have hK : CFSG.Open.IsQuasisimple ↥(barO2 L) := hL.1.component.2.2
  have hodd := centre_barO2_odd hL.1
  have hS : commutator ↥Ls = ⊤ := hLs.2.2.1
  have lie : ∀ {d : TauCeti.ValidLieTypeIndex}, In1512 d.1 → (∀ Q, d.1 = .twistedA 4 Q → p ≠ 5) →
      Nonempty ((↥Ls ⧸ Subgroup.center ↥Ls) ≃* (TauCeti.CFSGIndex.lie d).Group) →
      ¬ p ∣ Nat.card (Subgroup.center ↥(barO2 L)) := fun hd h5 ⟨e⟩ =>
    not_dvd_card_centre_of_in1512 hKSMOdd hKSMU4 hKSML3 hK hodd hd ⟨eQ.trans e⟩ hp hp5 h5
  have alt : ∀ {n : ℕ}, 6 ≤ n →
      Nonempty ((↥Ls ⧸ Subgroup.center ↥Ls) ≃* alternatingGroup (Fin n)) →
      ¬ p ∣ Nat.card (Subgroup.center ↥(barO2 L)) := fun hn ⟨e⟩ =>
    not_dvd_centre_barO2_of_row1512_aux3 hKSMAlt hK hodd hn ⟨eQ.trans e⟩ hp hp5
  have altS : ∀ {n : ℕ}, 6 ≤ n → Nonempty (↥Ls ≃* alternatingGroup (Fin n)) →
      ¬ p ∣ Nat.card (Subgroup.center ↥(barO2 L)) := fun hn ⟨e⟩ =>
    alt hn (quotCenter_equiv_alt (by omega) e).2
  have lieIdx : ∀ {f : TauCeti.PrimePower → TauCeti.LieTypeIndex} {c : ℕ → Prop},
      IsLieIdxOver ↥Ls f c → (∀ Q : TauCeti.PrimePower, Q.p = 2 → c Q.card → In1512 (f Q)) →
      (∀ Q Q' : TauCeti.PrimePower, f Q ≠ .twistedA 4 Q') →
      ¬ p ∣ Nat.card (Subgroup.center ↥(barO2 L)) := fun h hin hne => by
    obtain ⟨Q, d, hQ2, hc, hd, e⟩ := not_dvd_centre_barO2_of_row1512_aux4 hS h
    exact lie (by rw [hd]; exact hin Q hQ2 hc) (fun Q' h' => (hne Q Q' (hd.symm.trans h')).elim) e
  rcases hlist with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact alt (by norm_num) h.2.2
  · exact altS (by norm_num) h
  · exact altS (by norm_num) h
  · rcases h with h | ⟨-, d, ⟨q, hq3, hd⟩, ⟨e⟩⟩
    · exact lieIdx h (fun Q hQ _ => hQ) (fun Q Q' h' => by cases h')
    · obtain ⟨e'⟩ := not_dvd_centre_barO2_of_row1512_aux2 hS e
      have h1 := hKSMOdd.2 ↥(barO2 L) hK d ⟨q, hq3, hd⟩ ⟨eQ.trans e'⟩ hodd
      rw [h1]
      exact fun h => hp.one_lt.ne' (Nat.dvd_one.1 h)
  · obtain ⟨n, hn, -, ⟨e⟩⟩ := h
    rcases Nat.lt_or_ge n 2 with hlt | hge
    · obtain rfl : n = 1 := by omega
      obtain ⟨d, q, hq7, hd, ⟨e'⟩⟩ := not_dvd_centre_barO2_of_row1512_aux6 e
      have h1 := (hKSML3 ↥(barO2 L) hK d ⟨eQ.trans e'⟩ hodd).1 (Or.inr ⟨q, hq7, hd⟩)
      rw [h1]
      exact fun h => hp.one_lt.ne' (Nat.dvd_one.1 h)
    · obtain ⟨d, Q, hQ2, -, hd, e'⟩ := not_dvd_centre_barO2_of_row1512_aux5 hge e
      exact lie (by rw [hd]; exact hQ2) (fun Q' h' => by rw [hd] at h'; cases h') e'
  · rcases h with h | ⟨-, e⟩
    · exact lieIdx h (fun Q hQ _ => hQ) (fun Q Q' h' => by cases h')
    · exact altS (by norm_num) e
  · exact lieIdx h (fun Q hQ _ => hQ) (fun Q Q' h' => by cases h')
  · rcases h with h | ⟨-, e⟩
    · exact lieIdx h (fun Q hQ _ => hQ) (fun Q Q' h' => by cases h')
    · exact altS (by norm_num) e
  · exact lieIdx h (fun Q hQ _ => hQ) (fun Q Q' h' => by cases h')
  · exact lieIdx h (fun Q hQ _ => hQ) (fun Q Q' h' => by cases h')
  · exact lieIdx h (fun Q _ hc => hc) (fun Q Q' h' => by cases h')
  · exact lieIdx h (fun Q _ hc => hc) (fun Q Q' h' => by cases h')
  · exact lieIdx h (fun Q _ hc => hc) (fun Q Q' h' => by cases h')
  · obtain ⟨Q, d, hQ2, hc, hd, e⟩ := not_dvd_centre_barO2_of_row1512_aux4 hS h
    exact lie (by rw [hd]; exact hc) (fun Q' _ => hU5 h) e

theorem outTwoGroup_of_isAltSixCoverThree (hKOut : KOut) {S : Type} [Group S] [Finite S]
    (h : IsAltSixCoverThree S) : OutTwoGroup S := by
  obtain ⟨hq, -, ⟨e⟩⟩ := h
  haveI : Group.IsPerfect S := ⟨hq.1⟩
  intro φ
  set π := CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom S with hπ
  have hlist : IsOutTwoGroupList (S ⧸ Subgroup.center S) := Or.inl ⟨e⟩
  obtain ⟨k, y, hy⟩ := hKOut (S ⧸ Subgroup.center S) hlist (π φ)
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
  have hconj : π (MulAut.conj g) = MulAut.conj (QuotientGroup.mk g : S ⧸ Subgroup.center S) := by
    ext z
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective z
    have h1 := CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_apply_mk
      (MulAut.conj g) z
    simp only [QuotientGroup.mk'_apply] at h1
    simp [hπ, CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom, h1,
      MulAut.conj_apply]
  refine ⟨k, g, ?_⟩
  apply CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective S
  rw [← hπ, hconj, map_pow]
  exact hy

section CentralProd

theorem isAltSixCoverThree_of_centralProd_aux0 {J : Type} [Group J] {K₁ K₂ : Subgroup J}
    (hsup : K₁ ⊔ K₂ = ⊤) (hc : K₂ ≤ Subgroup.centralizer (K₁ : Set J)) : K₁.Normal := by
  have h : K₁ ⊔ K₂ ≤ Subgroup.normalizer (K₁ : Set J) :=
    sup_le Subgroup.le_normalizer (hc.trans (Subgroup.centralizer_le_normalizer _))
  rw [hsup] at h
  exact Subgroup.normalizer_eq_top_iff.1 (top_le_iff.1 h)

theorem isAltSixCoverThree_of_centralProd_aux1 {Y : Type} [Group Y] [Finite Y] {J : Subgroup Y}
    (hJ : J.Normal) {K₁ K₂ : Subgroup ↥J} (h₁ : CFSG.Open.IsQuasisimple ↥K₁)
    (h₂ : CFSG.Open.IsQuasisimple ↥K₂) (hsup : K₁ ⊔ K₂ = ⊤)
    (hc : K₁ ≤ Subgroup.centralizer (K₂ : Set ↥J)) {C : Subgroup Y}
    (hC : CFSG.Open.IsComponentOf C ⊤) (hCJ : C ≤ J) :
    C = K₁.map J.subtype ∨ C = K₂.map J.subtype := by
  have hc' : K₂ ≤ Subgroup.centralizer (K₁ : Set ↥J) := fun y hy =>
    Subgroup.mem_centralizer_iff.2 fun x hx => ((Subgroup.mem_centralizer_iff.1 (hc hx)) y hy).symm
  have hn₁ : K₁.Normal := isAltSixCoverThree_of_centralProd_aux0 hsup hc'
  have hn₂ : K₂.Normal := isAltSixCoverThree_of_centralProd_aux0 (by rw [sup_comm]; exact hsup) hc
  have hJsub : CFSG.Open.IsSubnormal J (⊤ : Subgroup Y) :=
    CFSG.Open.IsSubnormal.step le_top (Subgroup.Normal.subgroupOf hJ ⊤) (CFSG.Open.IsSubnormal.refl ⊤)
  have hcomp : ∀ {K : Subgroup ↥J}, K.Normal → CFSG.Open.IsQuasisimple ↥K →
      CFSG.Open.IsComponentOf (K.map J.subtype) ⊤ := fun hn hq =>
    CFSG.ComponentClassification.LocalComponents.of_subnormal_subgroup J hJsub _
      ⟨le_top, CFSG.Open.IsSubnormal.step le_top (Subgroup.Normal.subgroupOf hn ⊤)
        (CFSG.Open.IsSubnormal.refl ⊤), hq⟩
  have hA₁ := hcomp hn₁ h₁
  have hA₂ := hcomp hn₂ h₂
  rcases CFSG.ComponentClassification.LocalComponents.subnormal_contains_or_commutes C _ hC
    hA₁.2.1 with h1 | h1
  · exact Or.inl (CFSG.ComponentClassification.LocalComponents.eq_of_le C _ hC hA₁ h1)
  rcases CFSG.ComponentClassification.LocalComponents.subnormal_contains_or_commutes C _ hC
    hA₂.2.1 with h2 | h2
  · exact Or.inr (CFSG.ComponentClassification.LocalComponents.eq_of_le C _ hC hA₂ h2)
  exfalso
  have e1 : K₁.map J.subtype ≤ Subgroup.centralizer (C : Set Y) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 (by rw [Subgroup.commutator_comm]; exact h1)
  have e2 : K₂.map J.subtype ≤ Subgroup.centralizer (C : Set Y) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 (by rw [Subgroup.commutator_comm]; exact h2)
  have hJeq : K₁.map J.subtype ⊔ K₂.map J.subtype = J := by
    rw [← Subgroup.map_sup, hsup, Subgroup.map_top, Subgroup.range_subtype]
  have hCC : C ≤ Subgroup.centralizer (C : Set Y) := by
    rw [← hJeq] at hCJ
    exact hCJ.trans (sup_le e1 e2)
  exact liftOf_unique_aux1 hC (Subgroup.commutator_eq_bot_iff_le_centralizer.2 hCC)

end CentralProd

theorem isAltSixCoverThree_of_centralProd {L : Subgroup X} (hL : IsC2 L)
    (hJ : IsCentralProdA6Z3 ↥(barO2 (Subgroup.normalClosure (L : Set X)))) :
    IsAltSixCoverThree ↥(barO2 L) ∧
      Set.ncard {L' : Subgroup X | IsC2 L' ∧ L' ≤ Subgroup.normalClosure (L : Set X)} ≤ 2 := by
  obtain ⟨K₁, K₂, h₁, h₂, hsup, hc, -, -⟩ := hJ
  have hJn : (barO2 (Subgroup.normalClosure (L : Set X))).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  have key : ∀ {L' : Subgroup X}, IsC2 L' → L' ≤ Subgroup.normalClosure (L : Set X) →
      barO2 L' = K₁.map (barO2 (Subgroup.normalClosure (L : Set X))).subtype ∨
        barO2 L' = K₂.map (barO2 (Subgroup.normalClosure (L : Set X))).subtype :=
    fun hL' hle => isAltSixCoverThree_of_centralProd_aux1 hJn h₁.1 h₂.1 hsup hc hL'.component
      (Subgroup.map_mono hle)
  refine ⟨?_, ?_⟩
  · rcases key hL Subgroup.le_normalClosure with h | h
    · exact isAltSixCoverThree_of_mulEquiv ((MulEquiv.subgroupCongr h).trans
        (K₁.equivMapOfInjective _ (Subgroup.subtype_injective _)).symm) h₁
    · exact isAltSixCoverThree_of_mulEquiv ((MulEquiv.subgroupCongr h).trans
        (K₂.equivMapOfInjective _ (Subgroup.subtype_injective _)).symm) h₂
  · have hpair : ({K₁.map (barO2 (Subgroup.normalClosure (L : Set X))).subtype,
        K₂.map (barO2 (Subgroup.normalClosure (L : Set X))).subtype} :
          Set (Subgroup (X ⧸ CFSG.pCore 2 X))).ncard ≤ 2 :=
      (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])
    refine le_trans (Set.ncard_le_ncard_of_injOn barO2 ?_ ?_ (Set.toFinite _)) hpair
    · intro L' hL'
      exact key hL'.1 hL'.2
    · intro a ha b hb hab
      exact isC2_eq_of_barO2_eq ha.1 hb.1 hab

end CFSG.LocalAnalysis.RankThreeUC.S15
