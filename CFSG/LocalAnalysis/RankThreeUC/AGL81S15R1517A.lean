module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1517Defs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KOutLin
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsLie
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1512B
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1512E
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankCases
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15LiftBasic
import CFSG.Adapters.LieModelSimple
import CFSG.RankThree.PartOne.N143.Inspect613Even
import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge
import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDBridge

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open Subgroup
open scoped commutatorElement

section BadIndex

theorem bad1517_iff_aux_cases {p : ℕ} {d : TauCeti.LieTypeIndex} (h : BadIdx1517 p d) :
    (∃ Q : TauCeti.PrimePower, d = .B 3 Q ∧ Q.p = 2 ∧ p ∣ Q.card + 1) ∨
    (∃ Q : TauCeti.PrimePower, d = .twistedD 4 Q ∧ Q.p = 2 ∧ p ∣ Q.card + 1) ∨
    (∃ Q : TauCeti.PrimePower, d = .A 5 Q ∧ Q.card = 2 ∧ p = 7) ∨
    (∃ Q : TauCeti.PrimePower, d = .A 6 Q ∧ Q.card = 2 ∧ p = 7) := by
  unfold BadIdx1517 at h
  split at h
  · exact Or.inl ⟨_, rfl, h⟩
  · exact Or.inr (Or.inl ⟨_, rfl, h⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨_, rfl, h⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨_, rfl, h⟩))
  · exact h.elim

theorem bad1517_iff {p : ℕ} {S : Type} [Group S] :
    Bad1517 p S ↔ ∃ d : TauCeti.ValidLieTypeIndex, BadIdx1517 p d.1 ∧
      Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group) := by
  constructor
  · rintro (⟨hlin, hp7⟩ | ⟨Q, hQ2, hdvd, d, hd, he⟩ | ⟨Q, hQ2, hdvd, d, hd, he⟩)
    · rcases hlin with ⟨Q, hQ2, hQc, d, hd, he⟩ | ⟨Q, hQ2, hQc, d, hd, he⟩
      · refine ⟨d, ?_, he⟩
        rw [hd]
        exact ⟨hQc, hp7⟩
      · refine ⟨d, ?_, he⟩
        rw [hd]
        exact ⟨hQc, hp7⟩
    · refine ⟨d, ?_, he⟩
      rw [hd]
      exact ⟨hQ2, hdvd⟩
    · refine ⟨d, ?_, he⟩
      rw [hd]
      exact ⟨hQ2, hdvd⟩
  · rintro ⟨⟨d1, hv⟩, hd, he⟩
    rcases bad1517_iff_aux_cases hd with ⟨Q, rfl, hQ, hdvd⟩ | ⟨Q, rfl, hQ, hdvd⟩ |
      ⟨Q, rfl, hQc, hp7⟩ | ⟨Q, rfl, hQc, hp7⟩
    · exact Or.inr (Or.inl ⟨Q, hQ, hdvd, ⟨.B 3 Q, hv⟩, rfl, he⟩)
    · exact Or.inr (Or.inr ⟨Q, hQ, hdvd, ⟨.twistedD 4 Q, hv⟩, rfl, he⟩)
    · exact Or.inl ⟨Or.inl ⟨Q, (KOutLin_aux_card_two hQc).1, hQc, ⟨.A 5 Q, hv⟩, rfl, he⟩, hp7⟩
    · exact Or.inl ⟨Or.inr ⟨Q, (KOutLin_aux_card_two hQc).1, hQc, ⟨.A 6 Q, hv⟩, rfl, he⟩, hp7⟩

theorem bad1517_of_equiv {p : ℕ} {S S' : Type} [Group S] [Group S'] (e : S ≃* S')
    (h : Bad1517 p S) : Bad1517 p S' := by
  obtain ⟨d, hd, ⟨f⟩⟩ := bad1517_iff.1 h
  exact bad1517_iff.2 ⟨d, hd, ⟨e.symm.trans f⟩⟩

theorem isLinTwo_of_equiv {m : ℕ} {S S' : Type} [Group S] [Group S'] (e : S ≃* S')
    (h : IsLinTwo m S) : IsLinTwo m S' := by
  obtain ⟨Q, hQ2, hQc, d, hd, ⟨f⟩⟩ := h
  exact ⟨Q, hQ2, hQc, d, hd, ⟨e.symm.trans f⟩⟩

theorem isClassicalTwoOrG2_of_bad {p : ℕ} {S : Type} [Group S] (h : Bad1517 p S)
    (hZ : Subgroup.center S = ⊥) : IsClassicalTwoOrG2 (S ⧸ Subgroup.center S) := by
  obtain ⟨d, hd, ⟨e⟩⟩ := bad1517_iff.1 h
  refine Or.inl ⟨d, ?_, ⟨(QuotientGroup.quotientMulEquivOfEq hZ).trans
    (QuotientGroup.quotientBot.trans e)⟩⟩
  rcases bad1517_iff_aux_cases hd with ⟨Q, hd', hQ, -⟩ | ⟨Q, hd', hQ, -⟩ | ⟨Q, hd', hQc, -⟩ |
    ⟨Q, hd', hQc, -⟩
  · rw [hd']; exact hQ
  · rw [hd']; exact hQ
  · rw [hd']; exact (KOutLin_aux_card_two hQc).1
  · rw [hd']; exact (KOutLin_aux_card_two hQc).1

end BadIndex

section BadSimple

theorem bad1517_aux_center_eq_bot {S : Type} [Group S] [IsSimpleGroup S]
    (h : ∃ a b : S, a * b ≠ b * a) : Subgroup.center S = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with hb | ht
  · exact hb
  · exfalso
    obtain ⟨a, b, hab⟩ := h
    have ha : a ∈ Subgroup.center S := by
      rw [ht]
      exact Subgroup.mem_top a
    exact hab (Subgroup.mem_center_iff.1 ha b).symm

theorem bad1517_aux_isQuasisimple {S : Type} [Group S] [IsSimpleGroup S]
    (h : ∃ a b : S, a * b ≠ b * a) : CFSG.Open.IsQuasisimple S := by
  have hc := bad1517_aux_center_eq_bot h
  refine ⟨?_, ?_⟩
  · rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator S) with hb | ht
    · exfalso
      obtain ⟨a, b, hab⟩ := h
      have hmem : ⁅a, b⁆ ∈ commutator S :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [hb, Subgroup.mem_bot, commutatorElement_def, mul_inv_eq_one,
        mul_inv_eq_iff_eq_mul] at hmem
      exact hab hmem
    · exact ht
  · exact ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).isSimpleGroup

theorem bad1517_aux_transfer {S P : Type} [Group S] [Group P] (f : S ≃* P) [IsSimpleGroup P]
    (h : ∃ a b : P, a * b ≠ b * a) : IsSimpleGroup S ∧ ∃ a b : S, a * b ≠ b * a := by
  refine ⟨f.isSimpleGroup, ?_⟩
  obtain ⟨a, b, hab⟩ := h
  exact ⟨f.symm a, f.symm b, fun hc => hab (by simpa using congrArg f hc)⟩

theorem bad1517_aux_field {K : Type} [Field K] [Finite K] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) : (∃ s : Finset K, s.card = 4) ∨ Nat.card K = 2 := by
  by_cases h2 : Nat.card K = 2
  · exact Or.inr h2
  · left
    have h4 : 4 ≤ Nat.card K := by
      rcases Nat.lt_or_ge f 2 with hlt | hge
      · have : f = 1 := by omega
        subst this
        simp at hK
        exact absurd hK h2
      · calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hge
          _ = Nat.card K := hK.symm
    haveI : Fintype K := Fintype.ofFinite K
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset K)) (n := 4)
      (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact h4)
    exact ⟨s, hs⟩

theorem bad1517_aux_nonabelian_of_perfect {G : Type} [Group G] [Nontrivial G]
    (h : Group.IsPerfect G) : ∃ a b : G, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  exact Group.IsPerfect.not_isSolvable (G := G) (Group.isSolvable_of_comm hcon)

theorem bad1517_aux_typeA {S : Type} [Group S] {r : ℕ} {Q : TauCeti.PrimePower} (hr : 2 ≤ r)
    (hv : (TauCeti.LieTypeIndex.A r Q).Valid)
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨.A r Q, hv⟩).Group) :
    IsSimpleGroup S ∧ ∃ a b : S, a * b ≠ b * a := by
  have hmod := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
  haveI hsS := CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel hmod
  obtain ⟨-, K, hF, hfin, -, ⟨eK⟩⟩ := hmod
  let f : S ≃* Matrix.ProjectiveSpecialLinearGroup (Fin (r + 1)) K :=
    eK.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj (r + 1) K).symm
  haveI := CFSG.LinearGroups.linear_projective_perfect (K := K) (n := r + 1) (by omega)
    (Or.inl (by omega))
  haveI : Group.IsPerfect S :=
    Group.IsPerfect.ofSurjective (f := f.symm.toMonoidHom) f.symm.surjective
  exact ⟨hsS, bad1517_aux_nonabelian_of_perfect inferInstance⟩

theorem bad1517_aux_simple_nonabelian {p : ℕ} {S : Type} [Group S] (h : Bad1517 p S) :
    IsSimpleGroup S ∧ ∃ a b : S, a * b ≠ b * a := by
  obtain ⟨⟨d1, hv⟩, hd, ⟨e⟩⟩ := bad1517_iff.1 h
  rcases bad1517_iff_aux_cases hd with ⟨Q, rfl, hQ, -⟩ | ⟨Q, rfl, hQ, -⟩ | ⟨Q, rfl, hQc, -⟩ |
    ⟨Q, rfl, hQc, -⟩
  · have hmod := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even 3 Q hv hQ le_rfl
      (MulEquiv.refl _)
    have hsL := CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel hmod
    obtain ⟨-, K, hF, hfin, hK, ⟨eK⟩⟩ := hmod
    haveI := hsL
    haveI : IsSimpleGroup (StatedProj (StatedSp 3 K)) := eK.symm.isSimpleGroup
    have hcond : (∃ s : Finset K, s.card = 4) ∨ (Nat.card K = 3 ∧ 2 ≤ 3) ∨
        (Nat.card K = 2 ∧ 3 ≤ 3) := by
      rcases bad1517_aux_field (K := K) Q.exponent_pos (by rw [hK, hQ]) with h4 | h2
      · exact Or.inl h4
      · exact Or.inr (Or.inr ⟨h2, le_rfl⟩)
    haveI := CFSG.ClassicalGroups.Symplectic.isPerfect_statedSp 3 K hcond
    exact bad1517_aux_transfer (e.trans eK)
      (CFSG.LieType.Universal.Spin.exists_mul_ne_mul_statedProj (H := StatedSp 3 K))
  · have hmod := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even 4 Q hv hQ
      (MulEquiv.refl _)
    have hsL := CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel hmod
    obtain ⟨-, K, hF, hfin, -, b, c, hirr, ⟨eK⟩⟩ := hmod
    haveI := hsL
    haveI : IsSimpleGroup (StatedProj (StatedOmega (StatedQuadMinus 4 K b c))) :=
      eK.symm.isSimpleGroup
    haveI := CFSG.LieType.Universal.Spin.isPerfect_statedOmega_quadMinus (K := K) (b := b) (c := c)
      (n := 4) le_rfl hirr
    exact bad1517_aux_transfer (e.trans eK)
      (CFSG.LieType.Universal.Spin.exists_mul_ne_mul_statedProj
        (H := StatedOmega (StatedQuadMinus 4 K b c)))
  · exact bad1517_aux_typeA (by norm_num) hv e
  · exact bad1517_aux_typeA (by norm_num) hv e

end BadSimple

section LiftLevel

variable {X : Type} [Group X] [Finite X]

theorem lift_centre_trivial_of_bad_aux1 {K S : Type*} [Group K] [Group S] (f : K →* S)
    (hf : Function.Surjective f) (hker : f.ker ≤ Subgroup.center K)
    (hS : Subgroup.center S = ⊥) : f.ker = Subgroup.center K := by
  refine le_antisymm hker ?_
  intro z hz
  rw [MonoidHom.mem_ker]
  have h : f z ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro s
    obtain ⟨k, rfl⟩ := hf s
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz k]
  rw [hS, Subgroup.mem_bot] at h
  exact h

theorem lift_centre_trivial_of_bad_aux2 {p : ℕ} {d : TauCeti.LieTypeIndex} (h : BadIdx1517 p d) :
    In1512 d ∧ (∀ Q, d ≠ .A 2 Q) ∧ (∀ Q, d ≠ .twistedA 3 Q) ∧ (∀ Q, d ≠ .twistedA 4 Q) := by
  rcases bad1517_iff_aux_cases h with ⟨Q, rfl, hQ, -⟩ | ⟨Q, rfl, hQ, -⟩ | ⟨Q, rfl, hQc, -⟩ |
    ⟨Q, rfl, hQc, -⟩
  · exact ⟨hQ, fun _ h' => by simp at h', fun _ h' => by simp at h', fun _ h' => by simp at h'⟩
  · exact ⟨hQ, fun _ h' => by simp at h', fun _ h' => by simp at h', fun _ h' => by simp at h'⟩
  · exact ⟨hQc, fun _ h' => by simp at h', fun _ h' => by simp at h', fun _ h' => by simp at h'⟩
  · exact ⟨hQc, fun _ h' => by simp at h', fun _ h' => by simp at h', fun _ h' => by simp at h'⟩

theorem lift_centre_trivial_of_bad (hKSM : KSMOdd) {T L : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)}
    {p : ℕ} (hX : GNSetting X T) (hLs : IsComponentOf Ls ⊤) (hL : LiftOf T L Ls)
    (hbad : Bad1517 p ↥Ls) :
    Subgroup.center ↥(barO2 L) = ⊥ ∧ Nonempty (↥(barO2 L) ≃* ↥Ls) := by
  obtain ⟨d, hd, ⟨e⟩⟩ := bad1517_iff.1 hbad
  obtain ⟨hsimple, hnab⟩ := bad1517_aux_simple_nonabelian hbad
  haveI := hsimple
  have hZLs : Subgroup.center ↥Ls = ⊥ := bad1517_aux_center_eq_bot hnab
  obtain ⟨f, hf, hker⟩ := barO2_centralExt hX hLs hL
  have hK : CFSG.Open.IsQuasisimple ↥(barO2 L) := hL.1.component.2.2
  have hker_eq : f.ker = Subgroup.center ↥(barO2 L) :=
    lift_centre_trivial_of_bad_aux1 f hf hker hZLs
  let eK : (↥(barO2 L) ⧸ Subgroup.center ↥(barO2 L)) ≃* (TauCeti.CFSGIndex.lie d).Group :=
    ((QuotientGroup.quotientMulEquivOfEq hker_eq.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)).trans e
  obtain ⟨h1512, hA2, hTA3, hTA4⟩ := lift_centre_trivial_of_bad_aux2 hd
  have hcard : Nat.card (Subgroup.center ↥(barO2 L)) = 1 :=
    (hKSM.1 ↥(barO2 L) hK d h1512 hA2 hTA3 ⟨eK⟩ (centre_barO2_odd hL.1)).2 hTA4
  have hbot : Subgroup.center ↥(barO2 L) = ⊥ := Subgroup.eq_bot_of_card_eq _ hcard
  exact ⟨hbot, ⟨MulEquiv.ofBijective f ⟨(MonoidHom.ker_eq_bot_iff f).1 (hker_eq.trans hbot), hf⟩⟩⟩

theorem pRank_lift_three_of_bad_aux1 {p : ℕ} {d : TauCeti.LieTypeIndex} (h : BadIdx1517 p d) :
    IsClassicalOrG2Index d ∧ IsRankTwoPlus d ∧ RankThreeList d := by
  rcases bad1517_iff_aux_cases h with ⟨Q, rfl, hQ, -⟩ | ⟨Q, rfl, hQ, -⟩ | ⟨Q, rfl, hQc, -⟩ |
    ⟨Q, rfl, hQc, -⟩
  · exact ⟨hQ, ⟨hQ, by norm_num⟩, trivial⟩
  · exact ⟨hQ, ⟨hQ, by norm_num⟩, trivial⟩
  · obtain ⟨hp2, he⟩ := KOutLin_aux_card_two hQc
    exact ⟨hp2, ⟨hp2, by norm_num⟩, by show Odd Q.exponent; rw [he]; exact odd_one⟩
  · obtain ⟨hp2, he⟩ := KOutLin_aux_card_two hQc
    exact ⟨hp2, ⟨hp2, by norm_num⟩, by show Odd Q.exponent; rw [he]; exact odd_one⟩

theorem pRank_lift_three_of_bad (hRank : LieOddRankChev) {T L : Subgroup X}
    {Ls : Subgroup (X ⧸ gnC T)} {p : ℕ} (hX : GNSetting X T) (hLs : IsComponentOf Ls ⊤)
    (hL : LiftOf T L Ls) (hbad : Bad1517 p ↥Ls) : CFSG.Open.pRank 3 L = 3 := by
  obtain ⟨d, hd, ⟨e⟩⟩ := bad1517_iff.1 hbad
  obtain ⟨hcl, hrk2, hlist⟩ := pRank_lift_three_of_bad_aux1 hd
  obtain ⟨hsimple, hnab⟩ := bad1517_aux_simple_nonabelian hbad
  haveI := hsimple
  have hZLs : Subgroup.center ↥Ls = ⊥ := bad1517_aux_center_eq_bot hnab
  obtain ⟨⟨eQ⟩, -, -⟩ := centre_of_lift hX hLs hL
  have hK : CFSG.Open.IsQuasisimple ↥(barO2 L) := hL.1.component.2.2
  let eQ' : (↥Ls ⧸ Subgroup.center ↥Ls) ≃* (TauCeti.CFSGIndex.lie d).Group :=
    (QuotientGroup.quotientMulEquivOfEq hZLs).trans (QuotientGroup.quotientBot.trans e)
  have h1 := (pRank_barO2_eq hL.1 Nat.prime_three (by norm_num)).trans
    (CFSG.SectionRank.pRank_eq_pRank_top_subgroup (barO2 L))
  have h2 := hRank _ hK d hcl ⟨eQ.trans eQ'⟩ 3 Nat.prime_three (by norm_num)
  have h3 := ((mRank3_cases hrk2 (Nat.card (Subgroup.center ↥(barO2 L)))).2.2.1).2 hlist
  rw [h1, h2, h3]

theorem lift_normal_of_pRank_three {L : Subgroup X} (hL : IsC2 L)
    (hZ : Subgroup.center ↥(barO2 L) = ⊥) (h3 : CFSG.Open.pRank 3 L = 3)
    (hX : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 3) : L.Normal := by
  refine ⟨fun n hn g => ?_⟩
  by_contra hcon
  have hC2 : IsC2 (L.map (MulAut.conj g).toMonoidHom) := liftOf_conj_aux4 hL g
  have hne : L ≠ L.map (MulAut.conj g).toMonoidHom := by
    intro h
    apply hcon
    have hmem : g * n * g⁻¹ ∈ L.map (MulAut.conj g).toMonoidHom :=
      ⟨n, hn, by simp [MulAut.conj_apply]⟩
    rw [← h] at hmem
    exact hmem
  have hs : CFSG.Open.pRank 3 ((Subgroup.center ↥(barO2 L)).map (barO2 L).subtype) ≤ 0 := by
    by_contra hlt
    push Not at hlt
    have h1 := (one_le_pRank_iff_dvd _ Nat.prime_three).1 hlt
    rw [Subgroup.card_map_of_injective (barO2 L).subtype_injective, hZ, Subgroup.card_bot] at h1
    omega
  have hsum := pRank_add_le_pRank_sup hL hC2 hne Nat.prime_three (by norm_num) hs
  have hmono : CFSG.Open.pRank 3 L ≤ CFSG.Open.pRank 3 (L.map (MulAut.conj g).toMonoidHom) :=
    CFSG.SectionRank.pRank_le_map Nat.prime_three.one_lt _
      (fun a b h => (MulAut.conj g).injective h) L
  have hle : CFSG.Open.pRank 3 (L ⊔ L.map (MulAut.conj g).toMonoidHom) ≤ 3 :=
    (CFSG.SectionRank.pRank_mono Nat.prime_three.one_lt le_top).trans hX
  omega

end LiftLevel

section OutOrRank

theorem bad_pRank_or_out_aux1 {Q : TauCeti.PrimePower} {p : ℕ} (hQ : Q.p = 2)
    (hd : p ∣ Q.card + 1) : p ≠ 2 := by
  rintro rfl
  rw [TauCeti.PrimePower.card_def, hQ] at hd
  have h2 : 2 ∣ 2 ^ Q.exponent := dvd_pow_self 2 Q.exponent_pos.ne'
  have := (Nat.dvd_add_right h2).1 hd
  omega

theorem bad_pRank_or_out_aux2 {Q p : ℕ} (hd : p ∣ Q + 1) : eS Q p = 1 ∧ eP Q p ∣ 2 := by
  have h : ((Q + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hd
  rw [Nat.cast_add, Nat.cast_one] at h
  have h' : (Q : ZMod p) = -1 := eq_neg_of_add_eq_zero_left h
  refine ⟨?_, ?_⟩
  · unfold eS
    rw [h']
    simp
  · unfold eP
    rw [h']
    exact orderOf_dvd_of_pow_eq_one (by simp)

theorem bad_pRank_or_out_aux3 (hRank : LieOddRankChev) {S : Type} [Group S] [Finite S] {p : ℕ}
    (hp : p.Prime) (hbad : Bad1517 p S) {Q : TauCeti.PrimePower} (hQ : Q.p = 2)
    (hdvd : p ∣ Q.card + 1) {d : TauCeti.ValidLieTypeIndex}
    (hd : d.1 = .B 3 Q ∨ d.1 = .twistedD 4 Q) (e : S ≃* (TauCeti.CFSGIndex.lie d).Group) :
    CFSG.Open.pRank p (⊤ : Subgroup S) = 3 := by
  obtain ⟨hsimple, hnab⟩ := bad1517_aux_simple_nonabelian hbad
  haveI := hsimple
  have hq := bad1517_aux_isQuasisimple hnab
  have hZ := bad1517_aux_center_eq_bot hnab
  have hp2 : p ≠ 2 := bad_pRank_or_out_aux1 hQ hdvd
  have hcl : IsClassicalOrG2Index d.1 := by
    rcases hd with hd | hd <;> (rw [hd]; exact hQ)
  let eQ : (S ⧸ Subgroup.center S) ≃* (TauCeti.CFSGIndex.lie d).Group :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans (QuotientGroup.quotientBot.trans e)
  have h1 := hRank S hq d hcl ⟨eQ⟩ p hp hp2
  rw [hZ, Subgroup.card_bot] at h1
  obtain ⟨hS1, hP2⟩ := bad_pRank_or_out_aux2 hdvd
  rw [h1]
  rcases hd with hd | hd
  · rw [hd]
    show rkSp 3 Q.card p = 3
    unfold rkSp
    rw [hS1]
  · rw [hd]
    show rkOmMinus 4 Q.card p = 3
    unfold rkOmMinus
    rw [hS1, if_pos (hP2.trans (by norm_num))]

theorem bad_pRank_or_out (hRank : LieOddRankChev) (hOut : KOutLin) {S : Type} [Group S] [Finite S]
    {p : ℕ} (hp : p.Prime) (hbad : Bad1517 p S) :
    CFSG.Open.pRank p (⊤ : Subgroup S) = 3 ∨
      ∀ φ : MulAut S, ∃ k : ℕ, φ ^ (2 ^ k) ∈ (MulAut.conj : S →* MulAut S).range := by
  rcases id hbad with ⟨hlin, -⟩ | ⟨Q, hQ, hdvd, d, hd, ⟨e⟩⟩ | ⟨Q, hQ, hdvd, d, hd, ⟨e⟩⟩
  · exact Or.inr (fun φ => hOut S hlin φ)
  · exact Or.inl (bad_pRank_or_out_aux3 hRank hp hbad hQ hdvd (Or.inl hd) e)
  · exact Or.inl (bad_pRank_or_out_aux3 hRank hp hbad hQ hdvd (Or.inr hd) e)

end OutOrRank

end CFSG.LocalAnalysis.RankThreeUC.S15
