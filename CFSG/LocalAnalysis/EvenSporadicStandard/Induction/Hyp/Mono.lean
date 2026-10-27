module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.Link5a
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.Step
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.Adapters.GeneralizedFitting
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.QuasiAssembly
public import CFSG.LocalAnalysis.ComponentClassification.GSLitInputs
public import CFSG.LocalAnalysis.ComponentClassification.TBLitPropC
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.ClosingAt
public import CFSG.LocalAnalysis.EvenSporadicStandard.McLStd.Dichotomy
public import CFSG.LocalAnalysis.EvenSporadicStandard.McLStd.Input
public import CFSG.LocalAnalysis.OddStandard.SmallF3Interfaces
public import CFSG.LocalAnalysis.SectionRank.KGroupSectionClosure
public import CFSG.Permutation.AlternatingAutomorphism
public import CFSG.Sporadic.Bridge.LyData
public import CFSG.Sporadic.Bridge.TableSurj
public import CFSG.Sporadic.HN.LevelChainSpec
public import CFSG.Sporadic.Ly.ActionBase
public import CFSG.Sporadic.Ly.CertificateBase
public import CFSG.Sporadic.Ly.FaithSpec
public import CFSG.Sporadic.Ly.Simple
public import CFSG.Sporadic.LyBase
public import CFSG.Sporadic.Presentation.Ly
public import CFSG.Sporadic.Schreier.LyFixedSet
public import Certificates.Certificate3085Base

public section

namespace CFSG.EvenSporadicStandard.Induction.Hyp

open Subgroup Relation CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78

variable {H : Type} [Group H] [Finite H]

@[expose] noncomputable def cqCard (X : Subgroup H) : ℕ := Nat.card (↥X ⧸ center ↥X)

omit [Finite H] in
theorem cqCard_eq_of_cover {A B : Subgroup H} (hA : Group.IsPerfect ↥A) (π : ↥A →* ↥B)
    (hπ : Function.Surjective π) (hker : π.ker ≤ center ↥A) : cqCard A = cqCard B := by
  obtain ⟨e⟩ := cqEquiv_of_cover π hπ hker
  exact Nat.card_congr e.toEquiv

theorem cover_comp {A B C : Type*} [Group A] [Group B] [Group C] [Group.IsPerfect A]
    (π₁ : A →* B) (π₂ : B →* C) (h₁ : π₁.ker ≤ center A) (h₂ : π₂.ker ≤ center B) :
    (π₂.comp π₁).ker ≤ center A := fun x hx =>
  memCenter_of_cover π₁ h₁ (h₂ (by simpa using hx))

theorem chain_link5a_diag {M : Subgroup H} {m : ℕ} {L T : ℕ → Subgroup H} {s : ℕ → H}
    (hch : Sol78Chain23 H M m L T s) {i : ℕ} (hi : 1 ≤ i) (him : i ≤ m)
    (h5a : Sol78Link5a (L i) (L (i - 1)) (s i)) :
    ∃ π : ↥(L i) →* ↥(L (i - 1)), Function.Surjective π ∧ π.ker ≤ center ↥(L i) ∧
      ∀ a : ↥(L i), ((π a : ↥(L (i - 1))) : H) = (a : H) * (s i * (a : H) * (s i)⁻¹) := by
  obtain ⟨hTp, hLc⟩ := hch.comp i him
  obtain ⟨hsp, hsN, hs2, hLp⟩ := hch.elem i hi him
  obtain ⟨hincl, -⟩ := hch.incl i hi him
  have hA' : IsCompIn ((L i).map (MulAut.conj (s i)).toMonoidHom) (centralizer (T i : Set H)) :=
    isCompIn_map_conj_of_mem_normalizer hLc (mem_normalizer_centralizer_of_mem_normalizer hsN)
  refine exists_diag_cover_of_link5a hLc.isQuasisimple hLp.isQuasisimple
    (hLc.commute_of_ne hA' h5a.1) ?_ hincl ?_ h5a.2
  · exact mem_centralizer_iff.2 fun l hl => (mem_centralizer_iff.1 (hLc.1 hl) _ hs2).symm
  · exact mem_centralizer_iff.2 fun p hp =>
      (mem_centralizer_iff.1 (hLp.1 hp) (s i) (mem_sup_right (mem_zpowers _))).symm

theorem chain_link5a_cover {M : Subgroup H} {m : ℕ} {L T : ℕ → Subgroup H} {s : ℕ → H}
    (hch : Sol78Chain23 H M m L T s) {i : ℕ} (hi : 1 ≤ i) (him : i ≤ m)
    (h5a : Sol78Link5a (L i) (L (i - 1)) (s i)) :
    ∃ π : ↥(L i) →* ↥(L (i - 1)), Function.Surjective π ∧ π.ker ≤ center ↥(L i) := by
  obtain ⟨π, hπ, hk, -⟩ := chain_link5a_diag hch hi him h5a
  exact ⟨π, hπ, hk⟩

omit [Finite H] in
theorem chain_link5bData {M : Subgroup H} {m : ℕ} {L T : ℕ → Subgroup H} {s : ℕ → H}
    (hch : Sol78Chain23 H M m L T s) {i : ℕ} (hi : 1 ≤ i) (him : i ≤ m)
    (h5b : Sol78Link5b (L i) (L (i - 1)) (s i)) :
    Sol78Link5bData (L (i - 1)) (L i) (T i) (s i) := by
  obtain ⟨hTp, hLc⟩ := hch.comp i him
  obtain ⟨hsp, hsN, hs2, hKc⟩ := hch.elem i hi him
  obtain ⟨hincl, hincl2⟩ := hch.incl i hi him
  exact ⟨hTp, hLc, hsp, hsN, hs2, hKc, ⟨hincl, hincl2⟩, h5b⟩

theorem chain_link5b_lt {M : Subgroup H} {m : ℕ} {L T : ℕ → Subgroup H} {s : ℕ → H}
    (hch : Sol78Chain23 H M m L T s) {i : ℕ} (hi : 1 ≤ i) (him : i ≤ m)
    (h5b : Sol78Link5b (L i) (L (i - 1)) (s i)) : cqCard (L (i - 1)) < cqCard (L i) := by
  obtain ⟨hTp, hLc⟩ := hch.comp i him
  obtain ⟨hsp, hsN, hs2, hLp⟩ := hch.elem i hi him
  obtain ⟨hincl, -⟩ := hch.incl i hi him
  have hne : L (i - 1) ≠ L i := fun h => by
    have := hch.inj (i - 1) (by omega) i him h
    omega
  exact cqCard_lt_of_link5b hLc.isQuasisimple hLp.isQuasisimple hne hLc hs2 hLp hincl h5b

theorem chain_link_data {M : Subgroup H} {m : ℕ} {L T : ℕ → Subgroup H} {s : ℕ → H}
    (hch : Sol78Chain23 H M m L T s) {i : ℕ} (hi : 1 ≤ i) (him : i ≤ m) :
    (∃ π : ↥(L i) →* ↥(L (i - 1)), Function.Surjective π ∧ π.ker ≤ center ↥(L i)) ∨
      cqCard (L (i - 1)) < cqCard (L i) := by
  rcases hch.link i hi him with h5a | h5b
  · exact Or.inl (chain_link5a_cover hch hi him h5a)
  · exact Or.inr (chain_link5b_lt hch hi him h5b)

theorem chain_link_le {M : Subgroup H} {m : ℕ} {L T : ℕ → Subgroup H} {s : ℕ → H}
    (hch : Sol78Chain23 H M m L T s) {i : ℕ} (hi : 1 ≤ i) (him : i ≤ m) :
    cqCard (L (i - 1)) ≤ cqCard (L i) := by
  rcases chain_link_data hch hi him with ⟨π, hπ, hker⟩ | hlt
  · have : Group.IsPerfect ↥(L i) := (hch.comp i him).2.isQuasisimple.1
    exact (cqCard_eq_of_cover this π hπ hker).ge
  · exact hlt.le

theorem chain_link_cover {M : Subgroup H} {m : ℕ} {L T : ℕ → Subgroup H} {s : ℕ → H}
    (hch : Sol78Chain23 H M m L T s) {i : ℕ} (hi : 1 ≤ i) (him : i ≤ m)
    (heq : cqCard (L (i - 1)) = cqCard (L i)) :
    ∃ π : ↥(L i) →* ↥(L (i - 1)), Function.Surjective π ∧ π.ker ≤ center ↥(L i) := by
  rcases chain_link_data hch hi him with h | hlt
  · exact h
  · omega

theorem chain_zero_le {M : Subgroup H} {m : ℕ} {L T : ℕ → Subgroup H} {s : ℕ → H}
    (hch : Sol78Chain23 H M m L T s) : ∀ i, i ≤ m → cqCard (L 0) ≤ cqCard (L i) := by
  intro i
  induction i with
  | zero => exact fun _ => le_rfl
  | succ k ihk =>
    intro hk
    exact (ihk (by omega)).trans (chain_link_le hch (i := k + 1) (by omega) hk)

theorem chain_cover_of_eq {M : Subgroup H} {m : ℕ} {L T : ℕ → Subgroup H} {s : ℕ → H}
    (hch : Sol78Chain23 H M m L T s) :
    ∀ i, i ≤ m → cqCard (L 0) = cqCard (L i) →
      ∃ π : ↥(L i) →* ↥(L 0), Function.Surjective π ∧ π.ker ≤ center ↥(L i) := by
  intro i
  induction i with
  | zero => exact fun _ _ => ⟨MonoidHom.id _, Function.surjective_id, by simp⟩
  | succ k ihk =>
    intro hk heq
    have h1 : cqCard (L k) ≤ cqCard (L (k + 1)) := chain_link_le hch (i := k + 1) (by omega) hk
    have h0 := chain_zero_le hch k (by omega)
    obtain ⟨π₀, hπ₀, hk₀⟩ := ihk (by omega) (by omega)
    obtain ⟨π₁, hπ₁, hk₁⟩ : ∃ π : ↥(L (k + 1)) →* ↥(L k),
        Function.Surjective π ∧ π.ker ≤ center ↥(L (k + 1)) :=
      chain_link_cover hch (i := k + 1) (by omega) hk
        (by show cqCard (L k) = cqCard (L (k + 1)); omega)
    have : Group.IsPerfect ↥(L (k + 1)) := (hch.comp (k + 1) hk).2.isQuasisimple.1
    exact ⟨π₀.comp π₁, hπ₀.comp hπ₁, cover_comp π₁ π₀ hk₁ hk₀⟩

theorem lt_step_data (junction : JunctionStmtAt H)
    (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H) {N : Subgroup H}
    (hN : FStarSimple N) {A B : Subgroup H} (hLt : Lt A B) (hex : NotExc (↥A ⧸ center ↥A)) :
    cqCard A ≤ cqCard B ∧ (cqCard A = cqCard B →
      ∃ π : ↥B →* ↥A, Function.Surjective π ∧ π.ker ≤ center ↥B) := by
  by_cases hAB : A = B
  · subst hAB
    exact ⟨le_rfl, fun _ => ⟨MonoidHom.id _, Function.surjective_id, by simp⟩⟩
  obtain ⟨m, L, T, s, hm, hch, h0, hle⟩ :=
    junction hkp N hN A B (lt_inL_left hLt) (lt_inL_right hLt) hLt hAB hex.1 hex.2
  have hlast : L m = B := hch.last
  subst h0 hlast
  exact ⟨chain_zero_le hch m le_rfl, chain_cover_of_eq hch m le_rfl⟩

theorem reach_data (junction : JunctionStmtAt H)
    (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H) {N : Subgroup H}
    (hN : FStarSimple N) {K A : Subgroup H} (h : ReflTransGen Lt K A)
    (hex : ∀ B, ReflTransGen Lt K B → NotExc (↥B ⧸ center ↥B)) :
    cqCard K ≤ cqCard A ∧ (cqCard K = cqCard A →
      ∃ π : ↥A →* ↥K, Function.Surjective π ∧ π.ker ≤ center ↥A) := by
  induction h with
  | refl => exact ⟨le_rfl, fun _ => ⟨MonoidHom.id _, Function.surjective_id, by simp⟩⟩
  | tail hKB hBA ih =>
    rename_i B A
    obtain ⟨h1, h2⟩ := lt_step_data junction hkp hN hBA (hex B hKB)
    refine ⟨ih.1.trans h1, fun heq => ?_⟩
    obtain ⟨π₀, hπ₀, hk₀⟩ := ih.2 (by have := ih.1; omega)
    obtain ⟨π₁, hπ₁, hk₁⟩ := h2 (by have := ih.1; omega)
    have : Group.IsPerfect ↥A := (lt_inL_right hBA).isQuasisimple.1
    exact ⟨π₀.comp π₁, hπ₀.comp hπ₁, cover_comp π₁ π₀ hk₁ hk₀⟩

end CFSG.EvenSporadicStandard.Induction.Hyp
