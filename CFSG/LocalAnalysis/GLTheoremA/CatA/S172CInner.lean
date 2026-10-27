module

public import CFSG.LocalAnalysis.GLTheoremA.S12.Inputs123
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172InnerConj
import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTCompU6
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Label
import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDBridge

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S172C

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open scoped commutatorElement

private theorem model_centerQuot_of_catalogIs {Ω : Type} [Group Ω] [Finite Ω]
    {S : Subgroup Ω} {p n k : ℕ} (hqs : CFSG.Open.IsQuasisimple ↥S) (hn : 4 ≤ n)
    (hS : catalogIs (PSimple p S) (isOmMA n (2 ^ k))) :
    StatedClassicalModel (↥S ⧸ Subgroup.center ↥S) .POmegaMinus n 2 k := by
  obtain ⟨i0, hi0, ⟨eCat⟩⟩ := hS
  let P : TauCeti.LieTypeIndex → Prop :=
    fun d => ∃ hv : d.Valid, isOmM n (2 ^ k) (.lie ⟨d, hv⟩)
  have hS_onLie : catalogIs (PSimple p S) (onLie P) := by
    refine ⟨i0, ?_, ⟨eCat⟩⟩
    rcases hi0 with h1 | ⟨hn3, -⟩
    · cases i0 with
      | cyclic a b => simp [isOmM, onLie] at h1
      | alternating a b => simp [isOmM, onLie] at h1
      | sporadic s => simp [isOmM, onLie] at h1
      | lie idx => exact ⟨idx.2, h1⟩
    · omega
  have hmodel : StatedClassicalModel (PSimple p S) .POmegaMinus n 2 k := by
    obtain ⟨d, hv, hPd, ⟨e0⟩⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.CatB.exists_lieIndex hS_onLie
    cases d with
    | twistedD r q =>
      obtain ⟨hv', hPd'⟩ := hPd
      have hrq : r = n ∧ q.card = 2 ^ k := by simpa [isOmM, onLie] using hPd'
      obtain ⟨hr, hqc⟩ := hrq
      have hcard2 : 2 ≤ q.card := q.isPrimePow_card.two_le
      have hkpos : k ≠ 0 := by
        intro hk
        subst hk
        rw [pow_zero] at hqc
        omega
      have hpow : q.p ^ q.exponent = 2 ^ k := by
        rw [← TauCeti.PrimePower.card_def, hqc]
      obtain ⟨hq2, hqexp⟩ :=
        Nat.Prime.pow_inj' q.prime_p Nat.prime_two (Nat.ne_of_gt q.exponent_pos) hkpos hpow
      have hM :=
        CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even r q hv hq2 e0
      simpa [hr, hq2, hqexp] using hM
    | _ => simp [P, isOmM, onLie] at hPd
  have hnt : Nontrivial (PSimple p S) :=
    (CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_of_statedClassicalModel_POmegaMinus
      (PSimple p S) n 2 k hmodel).1
  obtain ⟨ePZ⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.HSubT.psimple_nonempty_equiv_quotCenter p S hqs hnt
  exact CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv ePZ hmodel

private theorem eq_of_ggLabelIso_twD {n k : ℕ} (hn : 4 ≤ n) :
    ∀ lab : CFSG.Assembly.LargeEvenLabel,
      CFSG.StandardType.GGLabelIso lab ⟨.twD, n, k⟩ → lab = ⟨.twD, n, k⟩ := by
  intro lab h
  obtain ⟨t, r, m⟩ := lab
  unfold CFSG.StandardType.GGLabelIso at h
  rcases h with h | h | h | h | h | h | h | h <;> simp_all

theorem mem_sup_centralizer_of_innerDiagMarking (hRig : CFSG.StandardType.GGLabelRigidInput)
    {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω} {p n k : ℕ}
    (hqs : CFSG.Open.IsQuasisimple ↥S) (hn : 4 ≤ n)
    (hS : catalogIs (PSimple p S) (isOmMA n (2 ^ k))) (hid : InnerDiagMarking B S) :
    ∀ b ∈ B, b ∈ S ⊔ Subgroup.centralizer (S : Set Ω) := by
  have hmodelZ := model_centerQuot_of_catalogIs hqs hn hS
  have hqs' : CFSG.IsQuasisimple ↥S :=
    CFSG.LocalAnalysis.GLTheoremA.S172X.isQuasisimple_of_open hqs
  have hHasTarget : CFSG.LocalAnalysis.GLTheoremA.Y10F.HasLabel ↥S (· = ⟨.twD, n, k⟩) :=
    CFSG.LocalAnalysis.GLTheoremA.Y10F.hasLabel_of_statedClassicalModel_POmegaMinus hqs' hmodelZ
  obtain ⟨hperf, hraw⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.S172X.innerDiagMarking_rawDatum_of_hasLabel hRig hqs'
      hHasTarget (eq_of_ggLabelIso_twD (n := n) (k := k) hn) hid
  intro b hb
  have hr2 : n ≠ 2 := by omega
  have hr3 : n ≠ 3 := by omega
  have htag : (⟨.twD, n, k⟩ : CFSG.Assembly.LargeEvenLabel).tag = .twD := rfl
  have hrank : (⟨.twD, n, k⟩ : CFSG.Assembly.LargeEvenLabel).rank = n := rfl
  unfold CFSG.Assembly.LargeEvenRawDatum at hraw
  simp only [htag, hrank, hr2, hr3, ↓reduceIte] at hraw
  unfold CFSG.Assembly.LargeEvenRecipeOmegaMinus at hraw
  obtain ⟨K, hKf, hKfin, hcardK, bK, cK, hbcK, hQ'⟩ := hraw
  obtain ⟨-, -, θ, hN, hall⟩ := hQ'
  obtain ⟨φ, hφmem, hφ⟩ := hall b hb
  simp only [CFSG.Assembly.LargeEvenInnSet] at hφmem
  obtain ⟨r, rfl⟩ := hφmem
  exact CFSG.LocalAnalysis.GLTheoremA.S172X.mem_sup_centralizer_of_largeEvenInduces_conj
    θ hperf (hN hb) hφ

end CFSG.LocalAnalysis.GLTheoremA.S172C

end