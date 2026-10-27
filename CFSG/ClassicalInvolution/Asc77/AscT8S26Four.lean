module

public import CFSG.ClassicalInvolution.Asc77.AscT7AExclude
public import CFSG.ClassicalInvolution.Asc77.AscP1SevenRep
public import CFSG.ClassicalInvolution.Asc77.AscP1SevenWire
public import CFSG.ClassicalInvolution.Asc77.WP2Thm8
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson

@[expose] def s26IsTransp (x : Equiv.Perm (Fin 4)) : Prop :=
  ∃ i j : Fin 4, i ≠ j ∧ x = Equiv.swap i j

instance (x : Equiv.Perm (Fin 4)) : Decidable (s26IsTransp x) := by
  unfold s26IsTransp
  infer_instance

theorem s26_perm4_sign : ∀ x : Equiv.Perm (Fin 4), x * x = 1 → ¬ s26IsTransp x →
    Equiv.Perm.sign x = 1 := by decide

theorem s26_perm4_conj : ∀ τ τ' : Equiv.Perm (Fin 4), s26IsTransp τ → s26IsTransp τ' →
    ∃ g : Equiv.Perm (Fin 4), g * τ * g⁻¹ = τ' := by decide

theorem s26_perm4_dbl : ∀ δ : Equiv.Perm (Fin 4), δ * δ = 1 → δ ≠ 1 → ¬ s26IsTransp δ →
    ∃ τ : Equiv.Perm (Fin 4), s26IsTransp τ ∧ ¬ (τ * δ = δ * τ ∨ (τ * δ) ^ 3 = 1) := by decide

theorem s26_perm4_comm : ∀ a b c : Equiv.Perm (Fin 4), s26IsTransp a → s26IsTransp b → a ≠ b →
    a * b = b * a → s26IsTransp c → c ≠ a → c ≠ b → c * a ≠ a * c ∧ c * b ≠ b * c := by decide

theorem s26_perm4_third : ∀ a b : Equiv.Perm (Fin 4), ∃ τ : Equiv.Perm (Fin 4),
    s26IsTransp τ ∧ τ ≠ a ∧ τ ≠ b := by decide

theorem s26_perm4_sign_swap : Equiv.Perm.sign (Equiv.swap (0 : Fin 4) 1) ≠ 1 := by decide

theorem s26_tt_iff {Δ : Set (Equiv.Perm (Fin 4))} (h : Star3T.IsTT Δ) (x : Equiv.Perm (Fin 4)) :
    x ∈ Δ ↔ s26IsTransp x := by
  have hex : ∃ τ ∈ Δ, s26IsTransp τ := by
    by_contra hno
    push Not at hno
    have hle : Subgroup.closure Δ ≤ (Equiv.Perm.sign : Equiv.Perm (Fin 4) →* ℤˣ).ker := by
      rw [Subgroup.closure_le]
      intro d hd
      exact (MonoidHom.mem_ker).mpr (s26_perm4_sign d (h.mul_self d hd) (hno d hd))
    rw [h.closure_eq_top] at hle
    exact s26_perm4_sign_swap ((MonoidHom.mem_ker).mp (hle (Subgroup.mem_top _)))
  obtain ⟨τ₀, hτ₀, hτ₀T⟩ := hex
  have hall : ∀ τ', s26IsTransp τ' → τ' ∈ Δ := by
    intro τ' hτ'
    obtain ⟨g, hg⟩ := s26_perm4_conj τ₀ τ' hτ₀T hτ'
    rw [← hg]
    exact h.conj_mem τ₀ hτ₀ g
  constructor
  · intro hx
    by_contra hxT
    obtain ⟨τ, hτT, hτ⟩ := s26_perm4_dbl x (h.mul_self x hx) (h.ne_one x hx) hxT
    exact hτ (h.comm_or_cube τ (hall τ hτT) x hx)
  · exact hall x

section Third

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

omit [Finite G] in
@[expose] noncomputable def s26Elt (ρ : Rep Ω W) : ↥(muGroup Ω W) :=
  ⟨ρ.img, piG_mem_muGroup (Subgroup.mem_sup_left (le_MGrp_of_mem_D ρ.hR ρ.hr))⟩

omit [Finite G] in
theorem s26Elt_mem (ρ : Rep Ω W) : s26Elt ρ ∈ muDelta Ω W :=
  ⟨ρ.R, ρ.hR, ρ.r, ρ.hr, ρ.hrW, rfl⟩

theorem s26Elt_eq_iff (c : Ctx p f Ω W) (ρ σ : Rep Ω W) : s26Elt ρ = s26Elt σ ↔ ρ.K = σ.K :=
  ⟨fun h => c.K_eq_of_img_eq ρ σ (congrArg Subtype.val h),
    fun h => Subtype.ext (c.img_eq_of_K_eq ρ σ h)⟩

theorem s26_exists_third {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}
    (hs : Std8 p f Ω K J S R T W z t) (φ : ↥(muGroup Ω W) ≃* Equiv.Perm (Fin 4)) :
    ∃ P ∈ DSet Ω W, ∃ M ∈ Ω, IsSylow2In P M ∧ M ≠ K ∧ M ≠ J ∧ M ∉ omegaNbr Ω J := by
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have hP : PartIHyp p f Ω := ⟨hp, hq, hΩ, hs.stand.aEmpty⟩
  have hW : W ∈ WSet Ω := hs.hW.1
  have c : Ctx p f Ω W := ⟨hp, hq, hΩ, hW, thompsonKey G Ω hP W hW, hs.stand.aEmpty⟩
  obtain ⟨hRΩ, hRK, hRS⟩ := hs.hR
  obtain ⟨hTΩ, hTJ, hTS⟩ := hs.hT
  have hJΩ : J ∈ Ω := hs.hJ.1
  have hSN : ∀ s ∈ (S : Subgroup G), s ∈ Subgroup.normalizer (W : Set G) := fun s hs' =>
    mem_normalizer_iff_conjSub_eq.mpr (hs.hW.2.2 s hs')
  have hRD : R ∈ DSet Ω W := ⟨hRΩ, fun x hx => hSN x (hRS hx)⟩
  have hTD : T ∈ DSet Ω W := ⟨hTΩ, fun x hx => hSN x (hTS hx)⟩
  have hRsyl : IsSylow2In R K := T3.isSylow2In_of_mem_RSet_of_le hp hΩ hK hRΩ hRK
  have hTsyl : IsSylow2In T J := T3.isSylow2In_of_mem_RSet_of_le hp hΩ hJΩ hTΩ hTJ
  obtain ⟨r, hr, hrW⟩ := exists_not_mem_of_mem_D hp hq hΩ hW hRD
  obtain ⟨t', ht', htW⟩ := exists_not_mem_of_mem_D hp hq hΩ hW hTD
  let ρ : Rep Ω W := ⟨K, R, r, hK, hRD, hRsyl, hr, hrW⟩
  let σ : Rep Ω W := ⟨J, T, t', hJΩ, hTD, hTsyl, ht', htW⟩
  have hTT := isTT_muDelta hp hq hΩ hW (thompsonCube G Ω hP W hW)
  have hTT' := T7A.isTT_map_equiv hTT φ
  have hρσ : s26Elt ρ ≠ s26Elt σ := fun h => hs.hJ.2.1 ((s26Elt_eq_iff c ρ σ).mp h).symm
  have hcomm : s26Elt ρ * s26Elt σ = s26Elt σ * s26Elt ρ :=
    Subtype.ext (c.comm_of_omega ρ σ hs.hJ)
  have hex : ∃ P ∈ DSet Ω W, ∃ M ∈ Ω, IsSylow2In P M ∧ M ≠ K ∧ M ≠ J := by
    by_contra hno
    push Not at hno
    have hsub : ∀ d ∈ muDelta Ω W, d = s26Elt ρ ∨ d = s26Elt σ := by
      rintro d ⟨R', hR', r', hr', hr'W, hd⟩
      obtain ⟨M, hM, hR'M⟩ := exists_isSylow2In_of_mem_RSet hR'.1
      let ρ' : Rep Ω W := ⟨M, R', r', hM, hR', hR'M, hr', hr'W⟩
      have hdρ' : d = s26Elt ρ' := Subtype.ext hd
      by_cases hMK : M = K
      · left
        rw [hdρ']
        exact (s26Elt_eq_iff c ρ' ρ).mpr hMK
      · right
        have hMJ : M = J := hno R' hR' M hM hR'M hMK
        rw [hdρ']
        exact (s26Elt_eq_iff c ρ' σ).mpr hMJ
    obtain ⟨τ, hτT, hτ1, hτ2⟩ := s26_perm4_third (φ (s26Elt ρ)) (φ (s26Elt σ))
    have hτΔ : τ ∈ φ '' muDelta Ω W := (s26_tt_iff hTT' τ).mpr hτT
    obtain ⟨d, hd, rfl⟩ := hτΔ
    rcases hsub d hd with rfl | rfl
    · exact hτ1 rfl
    · exact hτ2 rfl
  obtain ⟨P, hPD, M, hMΩ, hPM, hMK, hMJ⟩ := hex
  refine ⟨P, hPD, M, hMΩ, hPM, hMK, hMJ, fun hnbr => ?_⟩
  obtain ⟨rP, hrP, hrPW⟩ := exists_not_mem_of_mem_D hp hq hΩ hW hPD
  let ρP : Rep Ω W := ⟨M, P, rP, hMΩ, hPD, hPM, hrP, hrPW⟩
  have hcommP : s26Elt σ * s26Elt ρP = s26Elt ρP * s26Elt σ :=
    Subtype.ext (c.comm_of_omega σ ρP hnbr)
  have hPρ : s26Elt ρP ≠ s26Elt ρ := fun h => hMK ((s26Elt_eq_iff c ρP ρ).mp h)
  have hPσ : s26Elt ρP ≠ s26Elt σ := fun h => hMJ ((s26Elt_eq_iff c ρP σ).mp h)
  have hmem : ∀ ρ' : Rep Ω W, s26IsTransp (φ (s26Elt ρ')) := fun ρ' =>
    (s26_tt_iff hTT' (φ (s26Elt ρ'))).mp ⟨s26Elt ρ', s26Elt_mem ρ', rfl⟩
  have hρT := hmem ρ
  have hσT := hmem σ
  have hPT := hmem ρP
  have hρσ' : φ (s26Elt ρ) ≠ φ (s26Elt σ) := fun h => hρσ (φ.injective h)
  have hc' : φ (s26Elt ρ) * φ (s26Elt σ) = φ (s26Elt σ) * φ (s26Elt ρ) := by
    rw [← map_mul, ← map_mul, hcomm]
  have hPρ' : φ (s26Elt ρP) ≠ φ (s26Elt ρ) := fun h => hPρ (φ.injective h)
  have hPσ' : φ (s26Elt ρP) ≠ φ (s26Elt σ) := fun h => hPσ (φ.injective h)
  have := (s26_perm4_comm _ _ _ hρT (hσT) hρσ' hc' hPT hPρ' hPσ').2
  apply this
  rw [← map_mul, ← map_mul, ← hcommP]

end Third

variable (p f : ℕ) [Fact p.Prime]

@[expose] def C26_2_u : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8 p f Ω K J S R T W z t →
      ¬ DConnected Ω → MuIsoS4 Ω W →
        ∀ P ∈ DSet Ω W, ∀ M ∈ Ω, P ≤ M → M ≠ K → M ≠ J → ∀ u : G, IsUniqueInvolution M u →
          ∀ x ∈ T, x * u = u * x

variable {p f}

theorem c26_2_of_u (h : C26_2_u p f) : C26_2 p f := by
  intro G _ _ _ Ω K J S R T W z t hs hdisc hS4
  obtain ⟨φ⟩ := hS4
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hP : PartIHyp p f Ω := ⟨hp, hq, hΩ, hs.stand.aEmpty⟩
  have hW : W ∈ WSet Ω := hs.hW.1
  have c : Ctx p f Ω W := ⟨hp, hq, hΩ, hW, thompsonKey G Ω hP W hW, hs.stand.aEmpty⟩
  obtain ⟨P, hPD, M, hMΩ, hPM, hMK, hMJ, hnot⟩ := s26_exists_third hs φ
  obtain ⟨u, hu⟩ := hΩ.exists_uniqueInvolution hp hq hMΩ
  have hcent := h G Ω K J S R T W z t hs hdisc ⟨φ⟩ P hPD M hMΩ hPM.1 hMK hMJ u hu
  obtain ⟨hTΩ, hTJ, hTS⟩ := hs.hT
  have hJΩ : J ∈ Ω := hs.hJ.1
  have hSN : ∀ s ∈ (S : Subgroup G), s ∈ Subgroup.normalizer (W : Set G) := fun s hs' =>
    mem_normalizer_iff_conjSub_eq.mpr (hs.hW.2.2 s hs')
  have hTD : T ∈ DSet Ω W := ⟨hTΩ, fun x hx => hSN x (hTS hx)⟩
  have hTsyl : IsSylow2In T J := T3.isSylow2In_of_mem_RSet_of_le hp hΩ hJΩ hTΩ hTJ
  obtain ⟨t', ht', htW⟩ := exists_not_mem_of_mem_D hp hq hΩ hW hTD
  obtain ⟨rP, hrP, hrPW⟩ := exists_not_mem_of_mem_D hp hq hΩ hW hPD
  let σ : Rep Ω W := ⟨J, T, t', hJΩ, hTD, hTsyl, ht', htW⟩
  let ρP : Rep Ω W := ⟨M, P, rP, hMΩ, hPD, hPM, hrP, hrPW⟩
  have hrel : σ.r * u * σ.r⁻¹ = t * u :=
    c.conj_involution σ ρP (fun h => hMJ h.symm) hnot hs.ht hu
  have hcomm : σ.r * u = u * σ.r := hcent t' ht'
  have hcu : σ.r * u * σ.r⁻¹ = u := by
    rw [hcomm]
    group
  rw [hcu] at hrel
  apply hs.ht.ne_one
  have : t * u = 1 * u := by rw [← hrel, one_mul]
  exact mul_right_cancel this

end CFSG.ClassicalInvolution.Asc77
