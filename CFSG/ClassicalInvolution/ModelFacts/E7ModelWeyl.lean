module

public import CFSG.ClassicalInvolution.ModelFacts.E7ModelPair
public import CFSG.ClassicalInvolution.ModelFacts.E7ModelRoots
public import CFSG.ClassicalInvolution.RouteD.TypeEModel
public import CFSG.ClassicalInvolution.ModelFacts.StandardPair
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcOrthAdj
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121

public section

namespace CFSG.ClassicalInvolution.ModelFacts.E7Model

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.ClassicalInvolution.ModelFacts.Levi
  CFSG.ClassicalInvolution.ModelFacts CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Universal
  CFSG.ClassicalInvolution.Generic CFSG.LieType.CurtisTits

variable {F : Type} [Field F]

theorem rootTorusSL2_eq_thetaDiag {β : Fin (Tag.rank .E7) → ℤ} (hβ : IsRoot .E7 β) :
    rootTorusSL2 .E7 F β (-1) = rootDiagUnit .E7 (thetaDiag β (-1 : Fˣ)) := by
  obtain ⟨a, -, ha, -⟩ := exists_signTuple_of_isRoot (K := F) hβ
  rw [ha]
  congr 1
  funext i
  have h1 := rootChar_signTuple_eq (K := F) hβ (isRoot_single .E7 i) ha
  rw [CFSG.ClassicalInvolution.Balance.rootChar_single_eq] at h1
  rw [h1, iform_self_isRoot_E7 hβ]
  simp only [thetaDiag]
  congr 1
  omega

section PhaseZero

theorem phase_zero_step : ∀ γ ∈ rootFinset .E7, (∀ j, 0 ≤ γ j) →
    γ = thetaLit ∨ ∃ i : Fin 7, (∀ j, 0 ≤ reflect .E7 (e7Idx i) γ j) ∧
      ∑ j, γ j + 1 ≤ ∑ j, (reflect .E7 (e7Idx i) γ) j := by
  decide +kernel

theorem exists_word_to_theta (γ : V7) (hγ : IsRoot .E7 γ) :
    ∃ ω : List ℕ, wordAct ω γ = thetaLit ∨ wordAct ω γ = -thetaLit := by
  have hsign : ∀ γ ∈ rootFinset .E7, (∀ j, 0 ≤ γ j) ∨ (∀ j, γ j ≤ 0) := by decide +kernel
  have hpos : ∀ n : ℕ, ∀ γ : V7, IsRoot .E7 γ → (∀ j, 0 ≤ γ j) → (17 - ∑ j, γ j).toNat = n →
      ∃ ω : List ℕ, wordAct ω γ = thetaLit := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro γ hγ hp hn
      rcases phase_zero_step γ (mem_rootFinset.2 hγ) hp with rfl | ⟨i, hi, hht⟩
      · exact ⟨[], rfl⟩
      · have hγ' : IsRoot .E7 (reflect .E7 (e7Idx i) γ) := IsRoot.reflect _ hγ
        have h17 : ∀ γ ∈ rootFinset .E7, ∑ j, γ j ≤ 17 := by decide +kernel
        have hle := h17 _ (mem_rootFinset.2 hγ')
        obtain ⟨ω, hω⟩ := ih ((17 - ∑ j, reflect .E7 (e7Idx i) γ j).toNat) (by omega)
          (reflect .E7 (e7Idx i) γ) hγ' hi rfl
        exact ⟨i.val :: ω, by rw [wordAct_cons]; exact hω⟩
  rcases hsign γ (mem_rootFinset.2 hγ) with h | h
  · obtain ⟨ω, hω⟩ := hpos _ γ hγ h rfl
    exact ⟨ω, Or.inl hω⟩
  · have hneg : IsRoot .E7 (-γ) := CFSG.LieType.Chevalley.IsRoot.neg hγ
    obtain ⟨ω, hω⟩ := hpos _ (-γ) hneg (fun j => by have := h j; simp; omega) rfl
    refine ⟨ω, Or.inr ?_⟩
    rw [← neg_eq_iff_eq_neg, ← wordAct_neg, hω]

end PhaseZero

section Adjoint

variable [Finite F]

theorem exists_conj_rankOne_to_theta {β : Fin (Tag.rank .E7) → ℤ} (hβ : IsRoot .E7 β) :
    ∃ n ∈ adjointGroup .E7 F, (rootRankOneGroup .E7 F β).map (MulAut.conj n).toMonoidHom =
      rootRankOneGroup .E7 F thetaE7 := by
  obtain ⟨ω, hω⟩ := exists_word_to_theta β hβ
  obtain ⟨k, hk⟩ := exists_conj_stdRankOne_wordAct F ω
  refine ⟨εm F k, εm_mem k, ?_⟩
  have h1 := hk β hβ
  have h2 : stdRankOne (e7Datum F) (wordAct ω β) = stdRankOne (e7Datum F) thetaE7 := by
    rw [thetaE7_eq]
    rcases hω with h | h
    · rw [h]
    · rw [h, stdRankOne_neg]
  rw [h2] at h1
  have h3 := congrArg (fun S => S.map (εm F)) h1
  simp only [map_conjSub, map_stdRankOne_εm hβ, map_stdRankOne_εm isRoot_thetaE7] at h3
  exact h3

theorem map_conj_rootRankOneGroup_of_commute_gen (hF : ringChar F ≠ 2)
    (hodd : Odd (Nat.card F)) {β : Fin (Tag.rank .E7) → ℤ} (hβ : IsRoot .E7 β) {w : ModGL .E7 F}
    (hwG : w ∈ adjointGroup .E7 F)
    (hwd : w * rootTorusSL2 .E7 F β (-1) = rootTorusSL2 .E7 F β (-1) * w) :
    (rootRankOneGroup .E7 F β).map (MulAut.conj w).toMonoidHom = rootRankOneGroup .E7 F β := by
  obtain ⟨n, hnG, hn⟩ := exists_conj_rankOne_to_theta (F := F) hβ
  set d := rootTorusSL2 .E7 F β (-1) with hd
  have hdL : d ∈ rootRankOneGroup .E7 F β := ⟨HSL (-1), rfl⟩
  have hz : n * d * n⁻¹ ∈ rootRankOneGroup .E7 F thetaE7 := by
    rw [← hn]
    exact ⟨d, hdL, by simp [MulAut.conj_apply]⟩
  have hz2 : (n * d * n⁻¹) * (n * d * n⁻¹) = 1 := by
    calc (n * d * n⁻¹) * (n * d * n⁻¹) = n * (d * d) * n⁻¹ := by group
      _ = 1 := by rw [hd, rootTorusSL2_neg_one_mul_self]; group
  have hz1 : n * d * n⁻¹ ≠ 1 := by
    intro h
    apply rootTorusSL2_neg_one_ne_one hF β
    have : d = n⁻¹ * (n * d * n⁻¹) * n := by group
    rw [← hd, this, h]
    group
  have hzθ := eq_rootTorusSL2_neg_one_of_mul_self_eq_one hF hodd hz hz2 hz1
  rw [rootTorusSL2_thetaE7] at hzθ
  have hw'G : n * w * n⁻¹ ∈ adjointGroup .E7 F := mul_mem (mul_mem hnG hwG) (inv_mem hnG)
  have hw'd : (n * w * n⁻¹) * rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : Fˣ)) =
      rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : Fˣ)) * (n * w * n⁻¹) := by
    rw [← hzθ]
    calc n * w * n⁻¹ * (n * d * n⁻¹) = n * (w * d) * n⁻¹ := by group
      _ = n * (d * w) * n⁻¹ := by rw [hwd]
      _ = n * d * n⁻¹ * (n * w * n⁻¹) := by group
  have key := map_conj_rootRankOneGroup_of_commute hF hw'G hw'd
  change conjSub w (rootRankOneGroup .E7 F β) = rootRankOneGroup .E7 F β
  have hβθ : rootRankOneGroup .E7 F β = conjSub n⁻¹ (rootRankOneGroup .E7 F thetaE7) := by
    rw [← hn]
    exact (conjSub_inv_conjSub n _).symm
  have key' : conjSub (n * w * n⁻¹) (rootRankOneGroup .E7 F thetaE7) =
      rootRankOneGroup .E7 F thetaE7 := key
  calc conjSub w (rootRankOneGroup .E7 F β)
      = conjSub w (conjSub n⁻¹ (rootRankOneGroup .E7 F thetaE7)) := by rw [← hβθ]
    _ = conjSub n⁻¹ (conjSub (n * w * n⁻¹) (rootRankOneGroup .E7 F thetaE7)) := by
        rw [← conjSub_mul, ← conjSub_mul]
        congr 1
        group
    _ = rootRankOneGroup .E7 F β := by rw [key', hβθ]

end Adjoint

section PairL

theorem iform_reflect (i : Fin (Tag.rank .E7)) (u v : V7) :
    iform (reflect .E7 i u) (reflect .E7 i v) = iform u v := by
  rw [← CFSG.LieType.Chevalley.simple_smul, ← CFSG.LieType.Chevalley.simple_smul,
    iform_smul_smul]

theorem iform_wordAct (ω : List ℕ) (u v : V7) : iform (wordAct ω u) (wordAct ω v) = iform u v := by
  induction ω generalizing u v with
  | nil => rfl
  | cons i ω ih => rw [wordAct_cons, wordAct_cons, ih, iform_reflect]

theorem isRoot_wordAct (ω : List ℕ) {γ : V7} (hγ : IsRoot .E7 γ) : IsRoot .E7 (wordAct ω γ) := by
  induction ω generalizing γ with
  | nil => exact hγ
  | cons i ω ih => rw [wordAct_cons]; exact ih (IsRoot.reflect _ hγ)

theorem iform_neg_left' (u v : V7) : iform (-u) v = -iform u v := by
  rw [show (-u : V7) = (-1 : ℤ) • u by simp, iform_smul_left]
  ring

theorem e7Idx_zero : e7Idx 0 = (0 : Fin 7) := rfl

variable (F) [Finite F]

omit [Finite F] in
theorem exists_conj_theta_e0 {α β : V7} (hα : IsRoot .E7 α) (hβ : IsRoot .E7 β)
    (h : iform α β = 1 ∨ iform α β = -1) :
    ∃ k : ↥(e7Data_valid.minGroup F),
      conjSub k (stdRankOne (e7Datum F) α) = stdRankOne (e7Datum F) thetaE7 ∧
      conjSub k (stdRankOne (e7Datum F) β) = rankOne (e7Datum F).rootGroup (0 : Fin 7) := by
  obtain ⟨ω, hω⟩ := exists_word_to_theta α hα
  obtain ⟨k₀, hk₀⟩ := exists_conj_stdRankOne_wordAct F ω
  have hγ : IsRoot .E7 (wordAct ω β) := isRoot_wordAct ω hβ
  have hinv := iform_wordAct ω α β
  have hpair : iform thetaE7 (wordAct ω β) = 1 ∨ iform thetaE7 (wordAct ω β) = -1 := by
    rw [thetaE7_eq]
    rcases hω with h' | h'
    · rw [← h', hinv]
      exact h
    · have : thetaLit = -wordAct ω α := by rw [h', neg_neg]
      rw [this, iform_neg_left', hinv]
      omega
  have hk₀α : conjSub k₀ (stdRankOne (e7Datum F) α) = stdRankOne (e7Datum F) thetaE7 := by
    rw [hk₀ α hα, thetaE7_eq]
    rcases hω with h' | h'
    · rw [h']
    · rw [h', stdRankOne_neg]
  obtain ⟨k₁, hk₁, hk₁'⟩ := exists_conj_phase_one F hγ hpair
  rw [e7Idx_zero] at hk₁'
  refine ⟨k₁ * k₀, ?_, ?_⟩
  · rw [conjSub_mul, hk₀α, hk₁]
  · rw [conjSub_mul, hk₀ β hβ]
    exact hk₁'

theorem linearPair_of_roots {α β : V7} (hα : IsRoot .E7 α) (hβ : IsRoot .E7 β)
    (h : iform α β = 1 ∨ iform α β = -1) :
    ∃ W, CFSG.ClassicalInvolution.WeakCT.LinearBlockStandardPair F W
      (stdRankOne (e7Datum F) α) (stdRankOne (e7Datum F) β) := by
  obtain ⟨k, hk1, hk2⟩ := exists_conj_theta_e0 F hα hβ h
  obtain ⟨m, hm0, hm2⟩ := exists_conj_edge F (a := 0) (b := 2) (by decide)
  rw [e7Idx_fin] at hm0 hm2
  rw [e7Idx_zero] at hm2
  obtain ⟨W, hW⟩ := CFSG.ClassicalInvolution.RouteD.stdPair_edge_E7 (F := F) (i := 0) (j := 2)
    (by decide)
  have e1 : conjSub (k⁻¹ * m) (rankOne (e7Datum F).rootGroup (0 : Fin 7)) =
      stdRankOne (e7Datum F) α := by
    rw [conjSub_mul, hm0, ← hk1, conjSub_inv_conjSub]
  have e2 : conjSub (k⁻¹ * m) (rankOne (e7Datum F).rootGroup (2 : Fin 7)) =
      stdRankOne (e7Datum F) β := by
    rw [conjSub_mul, hm2, ← hk2, conjSub_inv_conjSub]
  have h3 := linearBlockStandardPair_map_conj hW (k⁻¹ * m)
  change CFSG.ClassicalInvolution.WeakCT.LinearBlockStandardPair F _ (conjSub _ _) (conjSub _ _)
    at h3
  rw [e1, e2] at h3
  exact ⟨_, h3⟩

end PairL

end CFSG.ClassicalInvolution.ModelFacts.E7Model
