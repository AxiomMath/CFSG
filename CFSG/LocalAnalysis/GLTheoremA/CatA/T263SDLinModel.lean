module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263SDMark
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DSLin1
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154Fld
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263SDLift
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GClsLin

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263.SD.Lin

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
  CFSG.LocalAnalysis.GLTheoremA.Y10F CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LocalAnalysis.GLTheoremA.T263
  CFSG.LocalAnalysis.GLTheoremA.T263.SD CFSG.LocalAnalysis.GLTheoremA.K155X
open scoped commutatorElement

theorem sd_exists_psl_of_linHi {T : Type} [Group T] (h : catalogIs T t263GLinHi) :
    ∃ (a m : ℕ) (E : Type) (_ : Field E) (_ : Finite E), 3 ≤ a ∧ Nat.card E = 2 ^ m ∧
      Nonempty (T ≃* StatedProj (StatedSL a E)) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic p hp => simp [t263GLinHi, onLie] at hi
  | alternating n hn => simp [t263GLinHi, onLie] at hi
  | sporadic s => simp [t263GLinHi, onLie] at hi
  | lie d =>
    obtain ⟨t, hv⟩ := d
    cases t with
    | A r q =>
      have hq : q.p = 2 ∧ 2 ≤ r := by simpa [t263GLinHi, onLie] using hi
      haveI : Fact q.p.Prime := ⟨q.prime_p⟩
      haveI : NeZero q.exponent := ⟨Nat.pos_iff_ne_zero.1 q.exponent_pos⟩
      refine ⟨r + 1, q.exponent, GaloisField q.p q.exponent, inferInstance, inferInstance, by omega, ?_,
        ⟨(e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r q hv)).trans
          (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj (r + 1)
            (GaloisField q.p q.exponent))⟩⟩
      rw [GaloisField.card q.p q.exponent (Nat.pos_iff_ne_zero.1 q.exponent_pos), hq.1]
    | _ => simp [t263GLinHi, onLie] at hi

theorem sd_recipe_dim {lab : LargeEvenLabel} (hΛ : LargeEvenInLambda2 lab) {r m : ℕ}
    (hc : canonLabel lab = ⟨.A, r, m⟩) :
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ (m₀ = 1 → lab.n = 1) ∧
      ∀ Q : LargeEvenRawCont, LargeEvenRawDatum lab Q ↔ LargeEvenRecipeLinear (r + 1) (2 ^ m₀) Q := by
  obtain ⟨hn, -⟩ := hΛ
  obtain ⟨tag, rank, n⟩ := lab
  dsimp only at hn
  cases tag
  case A =>
    simp [canonLabel] at hc
    obtain ⟨rfl, -⟩ := hc
    exact ⟨n, hn, fun h => h, fun Q => Iff.rfl⟩
  case D =>
    by_cases h3 : rank = 3
    · simp [canonLabel, h3] at hc
      obtain ⟨rfl, -⟩ := hc
      exact ⟨n, hn, fun h => h, fun Q => by simp [LargeEvenRawDatum, h3]⟩
    · simp [canonLabel, h3] at hc
  case twD =>
    by_cases h3 : rank = 3
    · simp [canonLabel, h3] at hc
    · by_cases h2 : rank = 2
      · simp [canonLabel, h2] at hc
        obtain ⟨rfl, -⟩ := hc
        exact ⟨n * 2, by omega, fun h => by omega, fun Q => by simp [LargeEvenRawDatum, h2, pow_mul]⟩
      · simp [canonLabel, h3, h2] at hc
  all_goals simp [canonLabel] at hc

theorem sd_lin_model (hLD : Y10GInnLin.LinLabelDict) {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω]
    {S B₀ : Subgroup Ω} (hSp : GLAPPrimeCore p ↥S = ⊥) (hSq : CFSG.Open.IsQuasisimple ↥S)
    (hQ : catalogIs (↥S ⧸ Subgroup.center ↥S) t263GLinHi) (hInn : InnDiagOn p B₀ S) :
    ∃ (d : ℕ) (K : Type) (_ : Field K) (_ : Finite K)
      (θ : ↥S ⧸ Subgroup.center ↥S ≃* LargeEvenProj (StatedSL d K)),
      3 ≤ d ∧ (2 : K) = 0 ∧
      (∃ m : ℕ, 1 ≤ m ∧ Nat.card K = 2 ^ m ∧
        (m = 1 → GLAMarking (↥S) (fun lab _ _ _ _ _ => lab.n = 1))) ∧
      ∀ b ∈ B₀, ∃ φ : MulAut (LargeEvenProj (StatedSL d K)),
        (∃ A : GL (Fin d) K, ∀ h h' : ↥(StatedSL d K),
          (h' : GL (Fin d) K) = A * (h : GL (Fin d) K) * A⁻¹ →
            φ (LargeEvenProjMk (StatedSL d K) h) = LargeEvenProjMk (StatedSL d K) h') ∧
        LargeEvenInduces θ (fun s s' : ↥S => (s' : Ω) = b * s * b⁻¹) φ := by
  obtain ⟨lab, hΛ, hraw⟩ := sd_marking_on_S hSp hInn
  have hlab : HasLabel ↥S (fun l : GLALabel => l = lab) :=
    ⟨hSq.1, lab, hΛ, CFSG.StandardType.Canonical.largeEvenRawDatum_mono
      (fun R _ I F ⟨hs, hna, θ, _⟩ => ⟨hs, hna, θ, rfl⟩) hraw⟩
  obtain ⟨a, m, E, hEf, hEfin, ha, hE, ⟨e⟩⟩ := sd_exists_psl_of_linHi hQ
  have hcanon := hLD ↥S lab a m E (by omega) hE hlab ⟨e⟩
  obtain ⟨m₀, hm0, hm1, hiff⟩ := sd_recipe_dim hΛ hcanon
  obtain ⟨K, instF, instFin, hK, hs, hna, θ, hindb⟩ := (hiff _).1 hraw
  haveI : CharP K 2 := Y10GField.charP_two_of_card_pow hK
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  have key : ∀ H : Subgroup (GL (Fin (a - 1 + 1)) K), H = StatedSL (a - 1 + 1) K →
      ∀ θ : ↥S ⧸ Subgroup.center ↥S ≃* LargeEvenProj H,
        (∀ b ∈ B₀, ∃ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk H) Set.univ,
          LargeEvenInduces θ (fun s s' : ↥S => (s' : Ω) = b * s * b⁻¹) φ) →
        ∃ θ' : ↥S ⧸ Subgroup.center ↥S ≃* LargeEvenProj (StatedSL (a - 1 + 1) K),
          ∀ b ∈ B₀, ∃ φ : MulAut (LargeEvenProj (StatedSL (a - 1 + 1) K)),
            (∃ A : GL (Fin (a - 1 + 1)) K, ∀ h h' : ↥(StatedSL (a - 1 + 1) K),
              (h' : GL (Fin (a - 1 + 1)) K) = A * (h : GL (Fin (a - 1 + 1)) K) * A⁻¹ →
                φ (LargeEvenProjMk (StatedSL (a - 1 + 1) K) h) =
                  LargeEvenProjMk (StatedSL (a - 1 + 1) K) h') ∧
            LargeEvenInduces θ' (fun s s' : ↥S => (s' : Ω) = b * s * b⁻¹) φ := by
    intro H hH θ hind
    subst hH
    refine ⟨θ, fun b hb => ?_⟩
    obtain ⟨φ, ⟨A, -, hA⟩, hφ⟩ := hind b hb
    exact ⟨φ, ⟨A, hA⟩, hφ⟩
  obtain ⟨θ', hθ'⟩ := key _ (largeEvenSLGroup_eq_statedSL (a - 1 + 1)) θ (fun b hb => (hindb b hb))
  refine ⟨a - 1 + 1, K, instF, instFin, θ', by omega, h2, ⟨m₀, hm0, hK, fun h1 => ?_⟩, hθ'⟩
  exact ⟨hSq.1, lab, hΛ, CFSG.StandardType.Canonical.largeEvenRawDatum_mono
    (fun R _ I F ⟨hs, hna, θ, _⟩ => ⟨hs, hna, θ, hm1 h1⟩) hraw⟩

end CFSG.LocalAnalysis.GLTheoremA.T263.SD.Lin

end
