module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GClsLinRecipe
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GField

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GField

open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA.Y10F CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.Open CFSG.Yardstones.Md0ec50421ce4
  CFSG.LocalAnalysis.GLTheoremB

theorem rawDatum_exists {lab : LargeEvenLabel} {Q : LargeEvenRawCont}
    (h : LargeEvenRawDatum lab Q) : ∃ (R : Type) (_ : Group R) (I F : Set (MulAut R)), Q R I F := by
  obtain ⟨tag, rank, n⟩ := lab
  cases tag <;> dsimp only [LargeEvenRawDatum] at h <;> (try split_ifs at h) <;>
    (repeat' (obtain ⟨_, h⟩ := h)) <;> exact ⟨_, _, _, _, h⟩

theorem charP_two_of_card_pow {K : Type} [Field K] [Finite K] {m : ℕ} (hK : Nat.card K = 2 ^ m) :
    CharP K 2 := by
  have := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime_pow (f := m) (by rw [← Nat.card_eq_fintype_card, hK])

theorem famLin_recipe {lab : LargeEvenLabel} (hΛ : LargeEvenInLambda2 lab) (hfam : FamLin lab) :
    ∃ (d m : ℕ), 2 ≤ d ∧ 1 ≤ m ∧
      ∀ Q : LargeEvenRawCont, LargeEvenRawDatum lab Q ↔ LargeEvenRecipeLinear d (2 ^ m) Q := by
  obtain ⟨tag, rank, n⟩ := lab
  obtain ⟨hn, hT⟩ := hΛ
  dsimp only at hn
  rcases hfam with h | ⟨h, hr⟩ | ⟨h, hr⟩
  · subst h
    dsimp only [LargeEvenInLambda2] at hT
    exact ⟨rank + 1, n, by omega, hn, fun Q => Iff.rfl⟩
  · subst h
    dsimp only at hr
    subst hr
    exact ⟨4, n, by norm_num, hn, fun Q => by simp [LargeEvenRawDatum]⟩
  · subst h
    dsimp only at hr
    subst hr
    exact ⟨2, n * 2, le_rfl, by omega, fun Q => by simp [LargeEvenRawDatum, pow_mul]⟩

theorem induces_unique {S : Type} [Group S] {R : Type} [Group R] {θ : S ⧸ Subgroup.center S ≃* R}
    {α : MulAut S} {u u' : MulAut R}
    (hu : LargeEvenInduces θ (fun s s' => s' = α s) u)
    (hu' : LargeEvenInduces θ (fun s s' => s' = α s) u') : u = u' := by
  ext r
  obtain ⟨q, rfl⟩ := θ.surjective r
  induction q using QuotientGroup.induction_on with
  | H s => rw [hu s (α s) rfl, hu' s (α s) rfl]

theorem ClsLin_holds : ClsLin := by
  intro S _ _ p α labK hfam hp hp2 _ hlab hα
  have hlab' : LargeEvenMarking S (fun lab _ _ _ _ _ => lab = labK) := hlab
  obtain ⟨hcomm, lab, hΛ, hraw⟩ := hlab'
  obtain ⟨_, _, _, _, hQ0⟩ := rawDatum_exists hraw
  obtain ⟨_, _, θ0, hlabEq⟩ := hQ0
  subst hlabEq
  obtain ⟨d, m, hd, _, hiff⟩ := famLin_recipe hΛ hfam
  obtain ⟨K, instF, instFin, hK, hQ⟩ := (hiff _).1 hraw
  obtain ⟨hsimple, hnonab, θ, -⟩ := hQ
  haveI : CharP K 2 := charP_two_of_card_pow hK
  have hodd : Odd p := hp.odd_of_ne_two hp2
  set φ : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin d) K)) :=
    MulAut.congr θ (centerQuotAut S α) with hφdef
  have hφp : φ ^ p = 1 := by
    rw [hφdef, ← map_pow, ← map_pow, hα, map_one, map_one]
  have hind : LargeEvenInduces θ (fun s s' => s' = α s) φ := by
    intro l l' hll'
    subst hll'
    simp [hφdef, MulAut.congr_apply, centerQuotAut_mk]
  have hrec : ∀ Q : LargeEvenRawCont,
      Q (LargeEvenProj (LargeEvenSLGroup (Fin d) K))
        (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ)
        (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K))) →
      LargeEvenRecipeLinear d (2 ^ m) Q := by
    intro Q hQK
    unfold LargeEvenRecipeLinear
    exact ⟨K, instF, instFin, hK, hQK⟩
  have hdich := recipe_dichotomy hd hodd φ hφp
  by_cases hI : φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ
  · left
    unfold InnDiagKind CFSG.Assembly.LargeEvenMarking
    exact ⟨hcomm, lab, hΛ, (hiff _).2 (hrec _
      ⟨hsimple, hnonab, θ, rfl, φ, hI, hind⟩)⟩
  · right
    obtain ⟨i, hi, f, hf, hφif⟩ := hdich.resolve_left hI
    have hnotI : ¬ ∃ i' ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ,
        LargeEvenInduces θ (fun s s' => s' = α s) i' := by
      rintro ⟨i', hi', hind'⟩
      apply hI
      rw [← induces_unique hind' hind]
      exact hi'
    have hindif : LargeEvenInduces θ (fun s s' => s' = α s) (i * f) := by
      rw [← hφif]
      exact hind
    unfold FieldKind CFSG.Assembly.LargeEvenMarking
    exact ⟨hcomm, lab, hΛ, (hiff _).2 (hrec _
      ⟨hsimple, hnonab, θ, rfl, ⟨i, hi, f, hf, hindif⟩, hnotI⟩)⟩

end CFSG.LocalAnalysis.GLTheoremA.Y10GField
