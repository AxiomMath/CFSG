module

public import CFSG.LocalAnalysis.StandardType.ChevTwoLieModel
public import CFSG.LocalAnalysis.StandardType.GGReverseMarking
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinDict
public import CFSG.LocalAnalysis.GLTheoremA.CatA.CentQChar2Index
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieIdx
public import CFSG.Adapters.TauCetiLieModels
public import CFSG.Adapters.LinearSmallCatalog
public import CFSG.Adapters.StatedClassicalOrders
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264Parts
public import CFSG.LocalAnalysis.GLTheoremA.S4S.I145GW
public import CFSG.LocalAnalysis.GLTheoremA.S4S.KData
public import CFSG.Milestones.CL_LIT_Gorenstein_Walter_L_balance

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CanonSubcomp

open CFSG.Open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley TauCeti CFSG.Assembly.LowTwoRank
open CFSG.StandardType (markTag markRank markChar markDeg GGLabelRigidInput)

open CFSG.LocalAnalysis.GLTheoremA.Y10F (HasLabel hasLabel_isQuasisimple)


theorem canonLabel_n_eq_markDeg {lab : GLALabel} (hlab : LargeEvenInLambda2 lab)
    (hc : markChar lab = 2) : (canonLabel lab).n = markDeg lab := by
  obtain ⟨t, r, n⟩ := lab
  cases t
  case twF4der =>
    obtain ⟨-, -, h1⟩ := hlab
    simp only [canonLabel, markDeg]
    exact h1.symm
  case B2der => simp [markChar] at hc
  case G2der => simp [markChar] at hc
  case D =>
    simp only [canonLabel, markDeg]
    split_ifs <;> rfl
  case twD =>
    simp only [canonLabel, markDeg]
    split_ifs <;> first | rfl | omega
  all_goals rfl

theorem markChar_eq_two_of_two_le {lab : GLALabel} (hlab : LargeEvenInLambda2 lab)
    (hn : 2 ≤ lab.n) : markChar lab = 2 := by
  obtain ⟨t, r, n⟩ := lab
  change 2 ≤ n at hn
  cases t
  case B2der =>
    obtain ⟨-, -, h1⟩ := hlab
    have h1' : n = 1 := h1
    omega
  case G2der =>
    obtain ⟨-, -, h1⟩ := hlab
    have h1' : n = 1 := h1
    omega
  all_goals rfl

theorem n_dvd_canonLabel_n {lab : GLALabel} (hlab : LargeEvenInLambda2 lab) :
    lab.n ∣ (canonLabel lab).n := by
  obtain ⟨t, r, n⟩ := lab
  cases t
  case B2der =>
    obtain ⟨-, -, h1⟩ := hlab
    subst h1
    exact one_dvd _
  case G2der =>
    obtain ⟨-, -, h1⟩ := hlab
    subst h1
    exact one_dvd _
  case twF4der =>
    obtain ⟨-, -, h1⟩ := hlab
    subst h1
    exact one_dvd _
  case D =>
    simp only [canonLabel]
    split_ifs <;> exact dvd_rfl
  case twD =>
    simp only [canonLabel]
    split_ifs
    · exact dvd_rfl
    · exact dvd_mul_left n 2
    · exact dvd_rfl
  all_goals exact dvd_rfl

theorem canonLabel_n_eq_self {lab : GLALabel} (hlab : LargeEvenInLambda2 lab)
    (h : lab.tag = .twD → 3 ≤ lab.rank) : (canonLabel lab).n = lab.n := by
  obtain ⟨t, r, n⟩ := lab
  cases t
  case B2der =>
    obtain ⟨-, -, h1⟩ := hlab
    simp only [canonLabel]
    exact h1.symm
  case G2der =>
    obtain ⟨-, -, h1⟩ := hlab
    simp only [canonLabel]
    exact h1.symm
  case twF4der =>
    obtain ⟨-, -, h1⟩ := hlab
    simp only [canonLabel]
    exact h1.symm
  case D =>
    simp only [canonLabel]
    split_ifs <;> rfl
  case twD =>
    have h3 : 3 ≤ r := h rfl
    simp only [canonLabel]
    split_ifs <;> first | rfl | omega
  all_goals rfl

theorem lambda2_of_hasLabel {X : Type} [Group X] {lab : GLALabel} (h : HasLabel X (· = lab)) :
    LargeEvenInLambda2 lab := by
  obtain ⟨-, lab', hlam, hraw⟩ := h
  obtain ⟨_, _, _, _, -, -, -, rfl⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  exact hlam

section Marked


theorem markedModel_of_hasLabel {X : Type} [Group X] {lab : GLALabel} (h : HasLabel X (· = lab)) :
    CFSG.StandardType.MarkedModel lab (X ⧸ Subgroup.center X) := by
  obtain ⟨-, lab', -, R, _, I, F, θ, -, -, ⟨rfl, hm⟩⟩ :=
    CFSG.StandardType.Canonical.largeEvenMarking_exists
      (CFSG.StandardType.Canonical.largeEvenMarking_markedModel h)
  exact CFSG.StandardType.MarkedModel.of_mulEquiv θ.symm hm

end Marked

section Certs


theorem exists_lieModel_two_fieldSize {S : Type} [Group S] (d : ValidLieTypeIndex)
    (hd : d.1.characteristic = 2) (e : S ≃* d.Group) :
    ∃ (t : StatedLieTag) (n f : ℕ), CFSG.Blueprint.LieModel S t n 2 f ∧
      KD264Lie.fieldSize d.1 = 2 ^ f := by
  have hB := CFSG.TauCetiBridge.Even.chevalleyBridgesAll
  obtain ⟨d, hv⟩ := d
  have hr := (LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1
  cases d with
  | A r q =>
    have hp : q.p = 2 := by simpa using hd
    have h := CFSG.Models.lieModel_A r q hv e
    rw [hp] at h
    exact ⟨_, _, _, CFSG.StandardType.ChevTwo.blueprintLieModel_of_modelsLieModel
      (by simp [classicalTags]) h, by show q.card = _; rw [PrimePower.card_def, hp]⟩
  | twistedA r q =>
    have hp : q.p = 2 := by simpa using hd
    have h := CFSG.Models.lieModel_twistedA r q hv e
    have hc : ValidLieTypeIndex.characteristic ⟨.twistedA r q, hv⟩ = 2 := hd
    rw [hc] at h
    exact ⟨_, _, _, CFSG.StandardType.ChevTwo.blueprintLieModel_of_modelsLieModel
      (by simp [classicalTags]) h, by
        show q.card = _
        rw [PrimePower.card_def, hp, ValidLieTypeIndex.fieldExponent,
          LieTypeIndex.fieldExponent_twistedA]⟩
  | B r q =>
    have hp : q.p = 2 := by simpa using hd
    rcases CFSG.Models.lieModel_B r q hv e with h | h
    · rw [hp] at h
      exact ⟨_, _, _, CFSG.StandardType.ChevTwo.blueprintLieModel_of_modelsLieModel
        (by simp [classicalTags]) h, by show q.card = _; rw [PrimePower.card_def, hp]⟩
    · rw [hp] at h
      exact absurd h.1.2.2.2 (by simp)
  | C r q =>
    have hp : q.p = 2 := by simpa using hd
    exact absurd hp hr.2
  | D r q =>
    have hp : q.p = 2 := by simpa using hd
    have h := CFSG.Models.lieModel_D r q hv e
    rw [hp] at h
    exact ⟨_, _, _, CFSG.StandardType.ChevTwo.blueprintLieModel_of_modelsLieModel
      (by simp [classicalTags]) h, by show q.card = _; rw [PrimePower.card_def, hp]⟩
  | twistedD r q =>
    have hp : q.p = 2 := by simpa using hd
    have h := CFSG.Models.lieModel_twistedD r q hv e
    rw [hp] at h
    exact ⟨_, _, _, CFSG.StandardType.ChevTwo.blueprintLieModel_of_modelsLieModel
      (by simp [classicalTags]) h, by show q.card = _; rw [PrimePower.card_def, hp]⟩
  | E6 q =>
    have hp : q.p = 2 := by simpa using hd
    exact ⟨.E6, 0, q.exponent, .inr (.inl ⟨rfl, by simp [chevalleyExceptionalTags],
      ⟨Nat.prime_two, q.exponent_pos, rfl⟩,
      CFSG.StandardType.ChevTwo.untwistedChevalleyModel_of_bridge hB.e6 q hv hp e⟩),
      by show q.card = _; rw [PrimePower.card_def, hp]⟩
  | E7 q =>
    have hp : q.p = 2 := by simpa using hd
    exact ⟨.E7, 0, q.exponent, .inr (.inl ⟨rfl, by simp [chevalleyExceptionalTags],
      ⟨Nat.prime_two, q.exponent_pos, rfl⟩,
      CFSG.StandardType.ChevTwo.untwistedChevalleyModel_of_bridge hB.e7 q hv hp e⟩),
      by show q.card = _; rw [PrimePower.card_def, hp]⟩
  | E8 q =>
    have hp : q.p = 2 := by simpa using hd
    exact ⟨.E8, 0, q.exponent, .inr (.inl ⟨rfl, by simp [chevalleyExceptionalTags],
      ⟨Nat.prime_two, q.exponent_pos, rfl⟩,
      CFSG.StandardType.ChevTwo.untwistedChevalleyModel_of_bridge hB.e8 q hv hp e⟩),
      by show q.card = _; rw [PrimePower.card_def, hp]⟩
  | F4 q =>
    have hp : q.p = 2 := by simpa using hd
    exact ⟨.F4, 0, q.exponent, .inr (.inl ⟨rfl, by simp [chevalleyExceptionalTags],
      ⟨Nat.prime_two, q.exponent_pos, rfl⟩,
      CFSG.StandardType.ChevTwo.untwistedChevalleyModel_of_bridge hB.f4 q hv hp e⟩),
      by show q.card = _; rw [PrimePower.card_def, hp]⟩
  | G2 q =>
    have hp : q.p = 2 := by simpa using hd
    have h3 : 3 ≤ 2 ^ q.exponent := by
      have h3 : 3 ≤ q.card := hr
      rwa [PrimePower.card_def, hp] at h3
    exact ⟨.G2, 0, q.exponent, .inr (.inl ⟨rfl, by simp [chevalleyExceptionalTags],
      ⟨Nat.prime_two, q.exponent_pos, rfl, h3⟩,
      CFSG.StandardType.ChevTwo.untwistedChevalleyModel_of_bridge hB.g2 q hv hp e⟩),
      by show q.card = _; rw [PrimePower.card_def, hp]⟩
  | twistedE6 q =>
    have hp : q.p = 2 := by simpa using hd
    exact ⟨.twistedE6, 0, q.exponent, .inr (.inl ⟨rfl, by simp [chevalleyExceptionalTags],
      ⟨Nat.prime_two, q.exponent_pos, rfl⟩,
      CFSG.StandardType.ChevTwo.twistedChevalleyModel_of_bridge hB.twistedE6 q hv hp e⟩),
      by show q.card = _; rw [PrimePower.card_def, hp]⟩
  | trialityD4 q =>
    have hp : q.p = 2 := by simpa using hd
    exact ⟨.trialityD4, 0, q.exponent, .inr (.inl ⟨rfl, by simp [chevalleyExceptionalTags],
      ⟨Nat.prime_two, q.exponent_pos, rfl⟩,
      CFSG.StandardType.ChevTwo.twistedChevalleyModel_of_bridge hB.trialityD4 q hv hp e⟩),
      by show q.card = _; rw [PrimePower.card_def, hp]⟩
  | suzuki m =>
    exact ⟨.twistedB2, 0, 2 * m + 1, .inr (.inr (.inr ⟨rfl, rfl,
      CFSG.StandardType.ChevTwo.suzukiModel_of_valid m hv e⟩)), rfl⟩
  | reeG2 m =>
    exact absurd hd (by simp)
  | reeF4 a =>
    exact ⟨.twistedF4, 0, 2 * a + 1, .inr (.inr (.inl ⟨rfl, by simp [reeTitsTags],
      CFSG.StandardType.ChevTwo.reeTitsModel_of_reeF4 a hv e⟩)), rfl⟩
  | tits =>
    exact ⟨.Tits, 0, 1, .inr (.inr (.inl ⟨rfl, by simp [reeTitsTags],
      CFSG.StandardType.ChevTwo.reeTitsModel_of_tits hv e⟩)), (pow_one 2).symm⟩

theorem exists_index_or_small_of_lieModel_two {S : Type} [Group S] {t : StatedLieTag} {n f : ℕ}
    (h : CFSG.Blueprint.LieModel S t n 2 f) :
    (∃ d : ValidLieTypeIndex, d.1.characteristic = 2 ∧ Nonempty (S ≃* (CFSGIndex.lie d).Group)) ∨
      Nat.card S = 60 ∨ f = 1 := by
  rcases h with ⟨-, hm⟩ | ⟨-, ht, hm⟩ | ⟨-, ht, hm⟩ | ⟨-, -, hm⟩
  · rcases classical_two_cases hm with hd | ⟨rfl, rfl, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩
    · exact Or.inl hd
    · refine Or.inr (Or.inl ?_)
      rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl (by norm_num) hm]
      decide
    · exact Or.inr (Or.inr rfl)
    · exact Or.inr (Or.inr rfl)
  · exact Or.inl (index_of_chevalleyExceptional ht hm)
  · have ht' : t = .twistedF4 ∨ t = .Tits := by
      simp only [reeTitsTags, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl
      · exact absurd hm.1.2.2.2.1 (by norm_num)
      · exact Or.inl rfl
      · exact Or.inr rfl
    exact Or.inl (index_of_reeTits_two ht' hm)
  · exact Or.inl (index_of_suzuki hm)

end Certs

section Dict


theorem two_pow_canonLabel_n_of_lie (hRig : GGLabelRigidInput) {X : Type} [Group X]
    {lab : GLALabel} (hX : HasLabel X (· = lab)) (d : ValidLieTypeIndex)
    (hd : d.1.characteristic = 2) (φ : X ⧸ Subgroup.center X ≃* d.Group) :
    2 ^ (canonLabel lab).n = KD264Lie.fieldSize d.1 := by
  obtain ⟨t, n, f, hLM, hfs⟩ := exists_lieModel_two_fieldSize d hd φ
  have hq := hasLabel_isQuasisimple hX
  obtain ⟨hX', lab', hlam', hraw'⟩ :=
    CFSG.StandardType.Canonical.largeEvenMarking_of_lieModel_centerQuot hq.1 hLM
  obtain ⟨_, _, _, _, _, _, _, _, _, hc, hf⟩ :=
    CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw'
  have hX'' : HasLabel X (· = lab') :=
    ⟨hX', lab', hlam', CFSG.StandardType.Canonical.largeEvenRawDatum_mono
      (fun _ _ _ _ ⟨hs, hna, θ, _⟩ => ⟨hs, hna, θ, rfl⟩) hraw'⟩
  obtain ⟨hlab, -, hg⟩ := Y10GInnLin.ggHasLabel_of_hasLabel hX
  obtain ⟨hlab'', -, hg'⟩ := Y10GInnLin.ggHasLabel_of_hasLabel hX''
  rw [Y10GInnLin.canonLabel_eq_of_ggLabelIso (hRig lab lab' _ hlab hlab'' hg hg'),
    canonLabel_n_eq_markDeg hlam' hc, hf, hfs]

theorem dvd_canonLabel_n_of_compRelC (hRig : GGLabelRigidInput)
    {X : Type} [Group X] [Finite X] {lab : GLALabel} (hX : HasLabel X (· = lab))
    {d : LieTypeIndex} (hd : d.characteristic = 2) {m : ℕ} (hm : KD264Lie.fieldSize d = 2 ^ m)
    {i : CFSGIndex} (φ : X ⧸ Subgroup.center X ≃* i.Group) (h : KD264Lie.compRelC d i) :
    m ∣ (canonLabel lab).n := by
  have hm1 : ∀ k, 2 ^ m = 2 ^ k → m = k := fun k h => Nat.pow_right_injective le_rfl h
  have hodd : ∀ r, r % 2 = 1 → 3 ≤ r → 2 ^ m ≠ r := by
    intro r hr h3 h
    rcases m with _ | m
    · simp at h
      omega
    · rw [pow_succ] at h
      omega
  have hone : KD264Lie.fieldSize d = 2 → m ∣ (canonLabel lab).n := fun h2 => by
    rw [hm1 1 (hm.symm.trans (h2.trans (pow_one 2).symm))]
    exact one_dvd _
  cases i with
  | cyclic p hp => exact h.elim
  | sporadic s => exact h.elim
  | lie e =>
    rcases h with ⟨hch, ⟨j, -, hfs⟩, -⟩ | ⟨h2, -⟩ | ⟨h3, -⟩
    · have hD := two_pow_canonLabel_n_of_lie hRig hX e (hch.trans hd) φ
      rw [hfs, hm, ← pow_mul] at hD
      exact ⟨j, Nat.pow_right_injective le_rfl hD⟩
    · exact hone h2
    · exact absurd (hm.symm.trans h3) (hodd 3 rfl le_rfl)
  | alternating n hn =>
    rcases h with ⟨rfl, h2 | h4 | h5⟩ | ⟨rfl, h2 | h3 | h9⟩ | ⟨rfl, h2⟩
    · exact hone h2
    · have hm2 : m = 2 := hm1 2 ((hm.symm.trans h4).trans (by norm_num))
      subst hm2
      have hE : Nat.card (GaloisField 2 2) = 2 ^ 2 :=
        CFSG.StandardType.ChevTwo.card_galoisField_two (by norm_num)
      obtain ⟨ψ⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five
        (GaloisField 2 2) (Or.inl (by rw [hE]; norm_num))
      have hcan := Y10GInnLin.linLabelDict_of_ggLabelRigidInput hRig X lab 2 2 (GaloisField 2 2)
        le_rfl hE hX ⟨φ.trans ψ.symm⟩
      rw [hcan]
    · exact absurd (hm.symm.trans h5) (hodd 5 rfl (by norm_num))
    · exact hone h2
    · exact absurd (hm.symm.trans h3) (hodd 3 rfl le_rfl)
    · exact absurd (hm.symm.trans h9) (hodd 9 rfl (by norm_num))
    · exact hone h2

end Dict

end CFSG.LocalAnalysis.GLTheoremA.CanonSubcomp

end
