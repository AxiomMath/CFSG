module

public import CFSG.ClassicalInvolution.ModelFacts.E8ExclHJ
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116

public section

namespace CFSG.ClassicalInvolution.ModelFacts.E7Model

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Universal
  CFSG.LieType.CurtisTits CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.ModelFacts.Levi CFSG.ClassicalInvolution.ModelFacts
  CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ClassicalInvolution.RouteD CFSG.Timmesfeld CFSG.LieType.RootSystem

section Words

theorem root_pos_or_neg : ∀ γ ∈ rootFinset .E7, (∀ j, 0 ≤ γ j) ∨ (∀ j, γ j ≤ 0) := by
  decide +kernel

theorem phase_D6_step : ∀ γ ∈ rootFinset .E7, γ (e7Idx 0) = 0 → (∀ j, 0 ≤ γ j) →
    (∃ j : Fin (Tag.rank .E7), j.val ≠ 0 ∧ γ = Pi.single j 1) ∨
      ∃ i : Fin 7, i.val ≠ 0 ∧ (∀ j, 0 ≤ reflect .E7 (e7Idx i) γ j) ∧
        ∑ j, (reflect .E7 (e7Idx i) γ) j + 1 = ∑ j, γ j := by
  decide +kernel

theorem simple_to_six (j : Fin 7) (hj : j.val ≠ 0) :
    ∃ ω : List ℕ, (∀ i ∈ ω, i % 7 ≠ 0) ∧
      wordAct ω (Pi.single (e7Idx j) 1) = Pi.single (e7Idx 6) 1 := by
  fin_cases j
  · exact absurd rfl hj
  · exact ⟨[3, 1, 4, 3, 5, 4, 6, 5], by decide, by decide +kernel⟩
  · exact ⟨[3, 2, 4, 3, 5, 4, 6, 5], by decide, by decide +kernel⟩
  · exact ⟨[4, 3, 5, 4, 6, 5], by decide, by decide +kernel⟩
  · exact ⟨[5, 4, 6, 5], by decide, by decide +kernel⟩
  · exact ⟨[6, 5], by decide, by decide +kernel⟩
  · exact ⟨[], by decide, by decide +kernel⟩

theorem exists_word_D6_pos (γ : V7) (hγ : IsRoot .E7 γ) (h0 : γ (e7Idx 0) = 0)
    (hpos : ∀ j, 0 ≤ γ j) :
    ∃ ω : List ℕ, (∀ i ∈ ω, i % 7 ≠ 0) ∧ wordAct ω γ = Pi.single (e7Idx 6) 1 := by
  suffices H : ∀ n : ℕ, ∀ γ : V7, IsRoot .E7 γ → γ (e7Idx 0) = 0 → (∀ j, 0 ≤ γ j) →
      (∑ j, γ j).toNat = n →
      ∃ ω : List ℕ, (∀ i ∈ ω, i % 7 ≠ 0) ∧ wordAct ω γ = Pi.single (e7Idx 6) 1 from
    H _ γ hγ h0 hpos rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro γ hγ h0 hpos hn
    rcases phase_D6_step γ (mem_rootFinset.2 hγ) h0 hpos with ⟨j, hj, rfl⟩ | ⟨i, hi, hpos', hht⟩
    · have e : e7Idx (j : ℕ) = j := e7Idx_fin j
      rw [← e]
      exact simple_to_six j hj
    · have hγ' : IsRoot .E7 (reflect .E7 (e7Idx i) γ) := IsRoot.reflect _ hγ
      have hi0 : e7Idx i ≠ e7Idx 0 := by
        intro he
        apply hi
        have := congrArg Fin.val he
        simp only [e7Idx] at this
        have h7 : i.val < 7 := i.2
        simpa [Nat.mod_eq_of_lt h7] using this
      have h' : reflect .E7 (e7Idx i) γ (e7Idx 0) = 0 := by
        rw [reflect_apply_eq_of_ne _ (Ne.symm hi0), h0]
      have hpos1 : 0 ≤ ∑ j, γ j := Finset.sum_nonneg fun j _ => hpos j
      have hr0 : 0 ≤ ∑ j, reflect .E7 (e7Idx i) γ j := Finset.sum_nonneg fun j _ => hpos' j
      obtain ⟨ω, hω, hact⟩ := ih ((∑ j, reflect .E7 (e7Idx i) γ j).toNat) (by omega)
        (reflect .E7 (e7Idx i) γ) hγ' h' hpos' rfl
      refine ⟨i.val :: ω, ?_, ?_⟩
      · intro k hk
        rcases List.mem_cons.1 hk with rfl | hk
        · have h7 : i.val < 7 := i.2
          rw [Nat.mod_eq_of_lt h7]
          exact hi
        · exact hω k hk
      · rw [wordAct_cons]
        exact hact

theorem exists_word_D6 (γ : V7) (hγ : IsRoot .E7 γ) (h0 : iform thetaE7 γ = 0) :
    ∃ ω : List ℕ, (∀ i ∈ ω, i % 7 ≠ 0) ∧
      (wordAct ω γ = Pi.single (e7Idx 6) 1 ∨ wordAct ω γ = -Pi.single (e7Idx 6) 1) := by
  rw [iform_thetaE7_eq_coord] at h0
  rcases root_pos_or_neg γ (mem_rootFinset.2 hγ) with hpos | hneg
  · obtain ⟨ω, hω, hact⟩ := exists_word_D6_pos γ hγ h0 hpos
    exact ⟨ω, hω, Or.inl hact⟩
  · have hγ' : IsRoot .E7 (-γ) := IsRoot.neg hγ
    have h0' : (-γ) (e7Idx 0) = 0 := by simp [h0]
    have hpos' : ∀ j, 0 ≤ (-γ) j := fun j => by simpa using hneg j
    obtain ⟨ω, hω, hact⟩ := exists_word_D6_pos (-γ) hγ' h0' hpos'
    refine ⟨ω, hω, Or.inr ?_⟩
    rw [wordAct_neg] at hact
    rw [← hact]
    simp

end Words

section Conj

variable {p f : ℕ} [Fact p.Prime]

local notation "D₇" => e7Datum (GaloisField p f)

theorem exists_mem_HJ_conj_wordAct (ω : List ℕ) (hω : ∀ i ∈ ω, i % 7 ≠ 0) :
    ∃ k ∈ HJ p f, ∀ γ : V7, IsRoot .E7 γ →
      conjSub k (stdRankOne D₇ γ) = stdRankOne D₇ (wordAct ω γ) := by
  induction ω with
  | nil =>
    refine ⟨1, one_mem _, fun γ _ => ?_⟩
    rw [wordAct_nil, conjSub_one]
  | cons i ω ih =>
    obtain ⟨k, hk, hkγ⟩ := ih (fun j hj => hω j (List.mem_cons_of_mem _ hj))
    have hi : i % 7 ≠ 0 := hω i (List.mem_cons_self ..)
    have hi7 : (e7Idx i).val ≠ 0 := by simpa [e7Idx] using hi
    have hnm : e7Data_valid.nm (GaloisField p f) (e7Idx i) ∈ HJ p f :=
      rankOne_le_HJ_of_ne_zero hi7 (e7Data_valid.nm_mem_rankOne (GaloisField p f) (e7Idx i))
    refine ⟨k * e7Data_valid.nm (GaloisField p f) (e7Idx i), mul_mem hk hnm, fun γ hγ => ?_⟩
    have hγr : γ ∈ (e7Datum (GaloisField p f)).roots :=
      (e7Data_valid.mem_minDatum_roots isFiniteType_cartan_E7 (GaloisField p f)).2 hγ
    have h1 := CFSG.LieType.Steinberg.map_conj_rootGroup
      (e7Datum_isCTGroupDatum (GaloisField p f)) (e7Idx i) hγr
    rw [refl_eq_reflect] at h1
    have h1' : ∀ δ : V7, IsRoot .E7 δ →
        conjSub (e7Data_valid.nm (GaloisField p f) (e7Idx i)) (stdRankOne D₇ δ) =
          stdRankOne D₇ (reflect .E7 (e7Idx i) δ) := by
      intro δ hδ
      have hδr : δ ∈ (e7Datum (GaloisField p f)).roots :=
        (e7Data_valid.mem_minDatum_roots isFiniteType_cartan_E7 (GaloisField p f)).2 hδ
      have h2 := CFSG.LieType.Steinberg.map_conj_rootGroup
        (e7Datum_isCTGroupDatum (GaloisField p f)) (e7Idx i) hδr
      have h3 := CFSG.LieType.Steinberg.map_conj_rootGroup
        (e7Datum_isCTGroupDatum (GaloisField p f)) (e7Idx i)
        ((e7Data_valid.mem_minDatum_roots isFiniteType_cartan_E7 (GaloisField p f)).2
          (CFSG.LieType.Chevalley.IsRoot.neg hδ))
      rw [refl_eq_reflect] at h2 h3
      unfold conjSub stdRankOne
      rw [Subgroup.map_sup, h2, h3, ← reflect_neg]
    rw [wordAct_cons, ← hkγ _ (IsRoot.reflect _ hγ), conjSub_mul, h1' γ hγ]

theorem exists_mem_HJ_conj_rankOne {γ : V7} (hγ : IsRoot .E7 γ) (h0 : iform thetaE7 γ = 0) :
    ∃ k ∈ HJ p f, conjSub k (stdRankOne D₇ γ) =
      rankOne (e7Datum (GaloisField p f)).rootGroup (e7Idx 6) := by
  obtain ⟨ω, hω, hact⟩ := exists_word_D6 γ hγ h0
  obtain ⟨k, hk, hkγ⟩ := exists_mem_HJ_conj_wordAct (p := p) (f := f) ω hω
  refine ⟨k, hk, ?_⟩
  rw [hkγ γ hγ]
  rcases hact with h | h
  · rw [h]
    rfl
  · rw [h, stdRankOne_neg]
    rfl

end Conj

end CFSG.ClassicalInvolution.ModelFacts.E7Model
