module

public import CFSG.CGT.PushingUpLit.BHS7.OmegaProdA3

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.G6 CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ] {G T E : Subgroup Γ}

@[expose] def omegaThree (G T : Subgroup Γ) : Set (Subgroup Γ) :=
  {E | E ∈ omegaSet G T ∧ IsNaturalAltModule ↥E 1}

@[expose] def badThree (G T : Subgroup Γ) (y : Γ) : Set (Subgroup Γ) :=
  {E | E ∈ omegaThree G T ∧ y ∉ Subgroup.centralizer (pCoreOf 2 E : Set Γ)}

theorem exists_finset_mem_iff (S : Set (Subgroup Γ)) :
    ∃ s : Finset (Subgroup Γ), ∀ F, F ∈ s ↔ F ∈ S :=
  ⟨(Set.toFinite S).toFinset, fun _ => (Set.toFinite S).mem_toFinset⟩

omit [Finite Γ] in
theorem iSup_set_eq_finset (S : Set (Subgroup Γ)) (s : Finset (Subgroup Γ))
    (hs : ∀ F, F ∈ s ↔ F ∈ S) (f : Subgroup Γ → Subgroup Γ) :
    (⨆ F ∈ S, f F : Subgroup Γ) = ⨆ F ∈ s, f F :=
  le_antisymm (iSup₂_le fun F hF => le_iSup₂_of_le F ((hs F).2 hF) le_rfl)
    (iSup₂_le fun F hF => le_iSup₂_of_le F ((hs F).1 hF) le_rfl)

theorem mem_iSup_pCoreOf_of_centralizes (h : MinCex G T) (s : Finset (Subgroup Γ))
    (hs : ∀ F ∈ s, F ∈ omegaSet G T) :
    ∀ r ∈ (⨆ F ∈ s, F : Subgroup Γ),
      (∀ F ∈ s, r ∈ Subgroup.centralizer (pCoreOf 2 F : Set Γ)) →
        r ∈ (⨆ F ∈ s, pCoreOf 2 F : Subgroup Γ) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro r hr _
    simp only [Finset.notMem_empty, iSup_false, iSup_bot, Subgroup.mem_bot] at hr ⊢
    exact hr
  | insert E s hEs ih =>
    intro r hr hrc
    have hs' : ∀ F ∈ s, F ∈ omegaSet G T := fun F hF => hs F (Finset.mem_insert_of_mem hF)
    have hEΩ : E ∈ omegaSet G T := hs E (Finset.mem_insert_self E s)
    have hEb := omega_isBTBlock h hEΩ
    have hchar := charTwo_of_isBTBlock h.charTwo h.sylow hEb
    have hWE : pCoreOf 2 E ≤ E := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 E
    have hcomm : ∀ F ∈ s, ∀ f ∈ F, ∀ e ∈ E, f * e = e * f := fun F hF f hf e he =>
      omega_comm' h hEΩ (hs' F hF) (fun hFE => hEs (hFE ▸ hF)) f hf e he
    have hQE : ∀ q ∈ (⨆ F ∈ s, F : Subgroup Γ), ∀ e ∈ E, q * e = e * q := by
      intro q hq e he
      have hle : (⨆ F ∈ s, F : Subgroup Γ) ≤ Subgroup.centralizer (E : Set Γ) :=
        iSup₂_le fun F hF f hf => Subgroup.mem_centralizer_iff.mpr fun e he =>
          (hcomm F hF f hf e he).symm
      exact (Subgroup.mem_centralizer_iff.mp (hle hq) e he).symm
    rw [Finset.iSup_insert] at hr ⊢
    have hr2 : r ∈ (⨆ F ∈ s, F : Subgroup Γ) ⊔ E := by rwa [sup_comm]
    obtain ⟨q, hq, e, he, rfl⟩ := exists_mul_of_mem_sup' hQE hr2
    have hqW : q ∈ Subgroup.centralizer (pCoreOf 2 E : Set Γ) :=
      Subgroup.mem_centralizer_iff.mpr fun w hw => (hQE q hq w (hWE hw)).symm
    have heW : e ∈ Subgroup.centralizer (pCoreOf 2 E : Set Γ) := by
      have := (Subgroup.centralizer _).mul_mem ((Subgroup.centralizer _).inv_mem hqW)
        (hrc E (Finset.mem_insert_self E s))
      simpa using this
    have heWE : e ∈ pCoreOf 2 E := by
      have h1 : e ∈ E ⊓ Subgroup.centralizer (pCoreOf 2 E : Set Γ) := ⟨he, heW⟩
      rwa [inf_centralizer_pCoreOf_eq hchar hEb.elemAbelian.1] at h1
    have hqF : ∀ F ∈ s, q ∈ Subgroup.centralizer (pCoreOf 2 F : Set Γ) := by
      intro F hF
      have hWF : pCoreOf 2 F ≤ F := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 F
      have h1 : e ∈ Subgroup.centralizer (pCoreOf 2 F : Set Γ) :=
        Subgroup.mem_centralizer_iff.mpr fun w hw => hcomm F hF w (hWF hw) e he
      have := (Subgroup.centralizer _).mul_mem (hrc F (Finset.mem_insert_of_mem hF))
        ((Subgroup.centralizer _).inv_mem h1)
      simpa using this
    have hqs := ih hs' q hq hqF
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hqs) (Subgroup.mem_sup_left heWE)

theorem exists_act_of_mem_iSup (h : MinCex G T) {𝒮 : Set (Subgroup Γ)} (h𝒮 : 𝒮 ⊆ omegaSet G T)
    {E : Subgroup Γ} (hE : E ∈ 𝒮) {y : Γ} (hy : y ∈ (⨆ F ∈ 𝒮, F : Subgroup Γ)) :
    y ∈ Subgroup.normalizer (pCoreOf 2 E : Set Γ) ∧
      ∃ e ∈ E, ∀ w ∈ pCoreOf 2 E, y * w * y⁻¹ = e * w * e⁻¹ := by
  classical
  have hEW : E ≤ Subgroup.normalizer (pCoreOf 2 E : Set Γ) := le_normalizer_pCoreOf_self E
  have hnW : ∀ g ∈ E, ∀ w ∈ pCoreOf 2 E, g * w * g⁻¹ ∈ pCoreOf 2 E := fun g hg w hw =>
    (Subgroup.mem_normalizer_iff.mp (hEW hg) w).mp hw
  let N : Subgroup Γ :=
    { carrier := {y | y ∈ Subgroup.normalizer (pCoreOf 2 E : Set Γ) ∧
        ∃ e ∈ E, ∀ w ∈ pCoreOf 2 E, y * w * y⁻¹ = e * w * e⁻¹}
      mul_mem' := by
        rintro a b ⟨ha, e₁, he₁, h₁⟩ ⟨hb, e₂, he₂, h₂⟩
        refine ⟨(Subgroup.normalizer _).mul_mem ha hb, e₁ * e₂, E.mul_mem he₁ he₂, fun w hw => ?_⟩
        calc a * b * w * (a * b)⁻¹ = a * (b * w * b⁻¹) * a⁻¹ := by group
          _ = a * (e₂ * w * e₂⁻¹) * a⁻¹ := by rw [h₂ w hw]
          _ = e₁ * (e₂ * w * e₂⁻¹) * e₁⁻¹ := h₁ _ (hnW e₂ he₂ w hw)
          _ = e₁ * e₂ * w * (e₁ * e₂)⁻¹ := by group
      one_mem' := ⟨(Subgroup.normalizer _).one_mem, 1, E.one_mem, fun w hw => by group⟩
      inv_mem' := by
        rintro a ⟨ha, e, he, h1⟩
        refine ⟨(Subgroup.normalizer _).inv_mem ha, e⁻¹, E.inv_mem he, fun w hw => ?_⟩
        have hw' : e⁻¹ * w * e ∈ pCoreOf 2 E := by
          have := hnW e⁻¹ (E.inv_mem he) w hw
          simpa using this
        have h2 : a * (e⁻¹ * w * e) * a⁻¹ = w := by
          rw [h1 _ hw']
          group
        calc a⁻¹ * w * a⁻¹⁻¹ = a⁻¹ * (a * (e⁻¹ * w * e) * a⁻¹) * a := by rw [h2]; group
          _ = e⁻¹ * w * e⁻¹⁻¹ := by group }
  have hle : (⨆ F ∈ 𝒮, F : Subgroup Γ) ≤ N := by
    refine iSup₂_le fun F hF f hf => ?_
    by_cases hFE : F = E
    · subst hFE
      exact ⟨hEW hf, f, hf, fun w hw => rfl⟩
    · have hcomm := omega_comm' h (h𝒮 hE) (h𝒮 hF) hFE
      have hfc : f ∈ Subgroup.centralizer (pCoreOf 2 E : Set Γ) :=
        Subgroup.mem_centralizer_iff.mpr fun w hw =>
          (hcomm f hf w (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 E hw)).symm
      refine ⟨Subgroup.centralizer_le_normalizer _ hfc, 1, E.one_mem, fun w hw => ?_⟩
      have := Subgroup.mem_centralizer_iff.mp hfc w hw
      rw [mul_inv_eq_iff_eq_mul.mpr this.symm]
      group
  exact hle hy

theorem step_three (h : MinCex G T) {y : Γ} (hyC : y ∈ cStarIn G T)
    (hyG : y ∈ (⨆ E ∈ omegaThree G T, E : Subgroup Γ)) {Ek Ep : Subgroup Γ}
    (hk : Ek ∈ omegaThree G T) (hp : Ep ∈ badThree G T y) {b : Γ} (hb : b ∈ baum T)
    (hbk : b ∈ Subgroup.centralizer (pCoreOf 2 Ek : Set Γ))
    (hbp : b ∉ Subgroup.centralizer (pCoreOf 2 Ep : Set Γ)) :
    y * b * y⁻¹ * b⁻¹ ∈ cStarIn G T ∧
      y * b * y⁻¹ * b⁻¹ ∈ (⨆ E ∈ omegaThree G T, E : Subgroup Γ) ∧
      badThree G T (y * b * y⁻¹ * b⁻¹) ⊆ badThree G T y \ {Ek} ∧
      Ep ∈ badThree G T (y * b * y⁻¹ * b⁻¹) := by
  classical
  have hbC : b ∈ cStarIn G T := le_cStarIn_of_minCex h ((inf_le_left : baum T ≤ T) hb)
  have h3 : omegaThree G T ⊆ omegaSet G T := fun F hF => hF.1
  have hBN : ∀ K ∈ omegaThree G T, b ∈ Subgroup.normalizer (K : Set Γ) := fun K hK =>
    baum_le_normalizer_of_isBTBlock (omega_isBTBlock h hK.1) hb
  have hbG : b ∈ Subgroup.normalizer ((⨆ E ∈ omegaThree G T, E : Subgroup Γ) : Set Γ) :=
    mem_normalizer_biSup (𝒮 := omegaThree G T) (f := id) (fun K => rfl) (fun K => rfl)
      (fun K hK => by rw [BHS.conjSub_eq_of_mem_normalizer (hBN K hK)]; exact hK)
      (fun K hK => by
        rw [BHS.conjSub_eq_of_mem_normalizer ((Subgroup.normalizer _).inv_mem (hBN K hK))]
        exact hK)
  have hy'G : y * b * y⁻¹ * b⁻¹ ∈ (⨆ E ∈ omegaThree G T, E : Subgroup Γ) := by
    have h1 : b * y⁻¹ * b⁻¹ ∈ (⨆ E ∈ omegaThree G T, E : Subgroup Γ) :=
      (Subgroup.mem_normalizer_iff.mp hbG y⁻¹).mp (Subgroup.inv_mem _ hyG)
    have h2 : y * b * y⁻¹ * b⁻¹ = y * (b * y⁻¹ * b⁻¹) := by group
    rw [h2]
    exact Subgroup.mul_mem _ hyG h1
  refine ⟨(cStarIn G T).mul_mem ((cStarIn G T).mul_mem ((cStarIn G T).mul_mem hyC hbC)
    ((cStarIn G T).inv_mem hyC)) ((cStarIn G T).inv_mem hbC), hy'G, ?_, ?_⟩
  · rintro F ⟨hF, hFy'⟩
    have hyN := (exists_act_of_mem_iSup h h3 hF hyG).1
    have hbNF : b ∈ Subgroup.normalizer (pCoreOf 2 F : Set Γ) :=
      (baum_le_normalizer_of_isBTBlock (omega_isBTBlock h hF.1)).trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 F) hb
    refine ⟨⟨hF, fun hyc => hFy' (commutator_mem_centralizer hyN hbNF (Or.inl hyc))⟩, ?_⟩
    intro hFk
    rw [Set.mem_singleton_iff] at hFk
    subst hFk
    exact hFy' (commutator_mem_centralizer hyN hbNF (Or.inr hbk))
  · refine ⟨hp.1, fun hy'c => hp.2 ?_⟩
    obtain ⟨-, e, he, hact⟩ := exists_act_of_mem_iSup h h3 hp.1 hyG
    exact (a3_commutator_iff h hp.1.1 hp.1.2 hb hbp he hact).mp hy'c

theorem badThree_eq_empty (h : MinCex G T) :
    ∀ n : ℕ, ∀ y : Γ, y ∈ cStarIn G T →
      y ∈ (⨆ E ∈ omegaThree G T, E : Subgroup Γ) → (badThree G T y).ncard = n →
        badThree G T y = ∅ := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro y hyC hyG hn
    by_contra hne
    obtain ⟨E₀, hE₀⟩ := Set.nonempty_iff_ne_empty.mpr hne
    by_cases hmore : ∃ E₁ ∈ badThree G T y, E₁ ≠ E₀
    · obtain ⟨E₁, hE₁, hne₁⟩ := hmore
      obtain ⟨b, hb, hbiff⟩ := a3_distinct h hE₀.1.1 hE₁.1.1 hE₀.1.2 hE₁.1.2 hne₁
      have key : ∀ {Ek Ep : Subgroup Γ}, Ek ∈ badThree G T y → Ep ∈ badThree G T y →
          b ∈ Subgroup.centralizer (pCoreOf 2 Ek : Set Γ) →
          b ∉ Subgroup.centralizer (pCoreOf 2 Ep : Set Γ) → False := by
        intro Ek Ep hk hp hbk hbp
        obtain ⟨hC', hG', hsub, hEp'⟩ := step_three h hyC hyG hk.1 hp hb hbk hbp
        have hlt : (badThree G T (y * b * y⁻¹ * b⁻¹)).ncard < n := by
          rw [← hn]
          refine Set.ncard_lt_ncard ⟨fun F hF => (hsub hF).1, fun hsup => ?_⟩ (Set.toFinite _)
          have : Ek ∈ badThree G T (y * b * y⁻¹ * b⁻¹) := hsup hk
          exact (hsub this).2 rfl
        have h0 := ih _ hlt _ hC' hG' rfl
        rw [h0] at hEp'
        exact hEp'
      by_cases hb0 : b ∈ Subgroup.centralizer (pCoreOf 2 E₀ : Set Γ)
      · have hb1 : b ∉ Subgroup.centralizer (pCoreOf 2 E₁ : Set Γ) := fun hh =>
          hbiff ⟨fun _ => hh, fun _ => hb0⟩
        exact key hE₀ hE₁ hb0 hb1
      · have hb1 : b ∈ Subgroup.centralizer (pCoreOf 2 E₁ : Set Γ) := by
          by_contra hh
          exact hbiff ⟨fun h0 => absurd h0 hb0, fun h1 => absurd h1 hh⟩
        exact key hE₁ hE₀ hb1 hb0
    ·
      push Not at hmore
      obtain ⟨s₀, hs₀⟩ := exists_finset_mem_iff {F | F ∈ omegaThree G T ∧ F ≠ E₀}
      have hs₀Ω : ∀ F ∈ s₀, F ∈ omegaSet G T := fun F hF => ((hs₀ F).1 hF).1.1
      set R : Subgroup Γ := ⨆ F ∈ s₀, F with hR
      have hGle : (⨆ E ∈ omegaThree G T, E : Subgroup Γ) ≤ R ⊔ E₀ := by
        refine iSup₂_le fun F hF => ?_
        by_cases hFE : F = E₀
        · rw [hFE]
          exact le_sup_right
        · exact le_sup_of_le_left (le_iSup₂_of_le F ((hs₀ F).2 ⟨hF, hFE⟩) le_rfl)
      have hRE : ∀ r ∈ R, ∀ e ∈ E₀, r * e = e * r := by
        intro r hr e he
        have hle : R ≤ Subgroup.centralizer (E₀ : Set Γ) := by
          refine iSup₂_le fun F hF f hf => Subgroup.mem_centralizer_iff.mpr fun e he => ?_
          exact (omega_comm' h hE₀.1.1 ((hs₀ F).1 hF).1.1 ((hs₀ F).1 hF).2 f hf e he).symm
        exact (Subgroup.mem_centralizer_iff.mp (hle hr) e he).symm
      obtain ⟨r, hr, e, he, rfl⟩ := exists_mul_of_mem_sup' hRE (hGle hyG)
      have hWE₀ : pCoreOf 2 E₀ ≤ E₀ := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 E₀
      have hrc : ∀ F ∈ s₀, r ∈ Subgroup.centralizer (pCoreOf 2 F : Set Γ) := by
        intro F hF
        have hFΩ := (hs₀ F).1 hF
        have hFy : r * e ∈ Subgroup.centralizer (pCoreOf 2 F : Set Γ) := by
          by_contra hcon
          exact hFΩ.2 (hmore F ⟨hFΩ.1, hcon⟩)
        have hWF : pCoreOf 2 F ≤ F := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 F
        have he' : e ∈ Subgroup.centralizer (pCoreOf 2 F : Set Γ) :=
          Subgroup.mem_centralizer_iff.mpr fun w hw =>
            omega_comm' h hE₀.1.1 hFΩ.1.1 hFΩ.2 w (hWF hw) e he
        have := (Subgroup.centralizer _).mul_mem hFy ((Subgroup.centralizer _).inv_mem he')
        simpa using this
      have hrW := mem_iSup_pCoreOf_of_centralizes h s₀ hs₀Ω r hr hrc
      have hWT : ∀ F ∈ s₀, pCoreOf 2 F ≤ T := fun F hF =>
        pCoreOf_le_sylow h.charTwo h.sylow (omega_isBTBlock h (hs₀Ω F hF)) h.sylow
      have hrT : r ∈ T :=
        (iSup₂_le fun F hF => hWT F hF : (⨆ F ∈ s₀, pCoreOf 2 F : Subgroup Γ) ≤ T) hrW
      have hrC : r ∈ cStarIn G T := le_cStarIn_of_minCex h hrT
      have heC : e ∈ cStarIn G T := by
        have := (cStarIn G T).mul_mem ((cStarIn G T).inv_mem hrC) hyC
        simpa using this
      have heW : e ∈ pCoreOf 2 E₀ := by
        have := cStarIn_inf_eq_of_three h hE₀.1.1 hE₀.1.2
        rw [← this]
        exact ⟨heC, he⟩
      have hrE₀ : r ∈ Subgroup.centralizer (pCoreOf 2 E₀ : Set Γ) :=
        Subgroup.mem_centralizer_iff.mpr fun w hw => (hRE r hr w (hWE₀ hw)).symm
      have heE₀ : e ∈ Subgroup.centralizer (pCoreOf 2 E₀ : Set Γ) :=
        Subgroup.mem_centralizer_iff.mpr fun w hw =>
          (omega_isBTBlock h hE₀.1.1).elemAbelian.1 w hw e heW
      exact hE₀.2 ((Subgroup.centralizer _).mul_mem hrE₀ heE₀)

theorem omegaCStarProd_of_omegaMaxSwap (h : MinCex G T) (hms : OmegaMaxSwap G T) :
    OmegaCStarProd G T := by
  classical
  refine le_antisymm ?_ (iSup₂_le fun E hE => inf_le_inf_left _ (le_iSup₂_of_le E hE le_rfl))
  intro x hx
  obtain ⟨sna, hsna⟩ := exists_finset_mem_iff {F | F ∈ omegaSet G T ∧ ¬ IsNaturalAltModule ↥F 1}
  have hna : ∀ F ∈ sna, F ∈ omegaSet G T ∧ ¬ IsNaturalAltModule ↥F 1 := fun F hF =>
    (hsna F).1 hF
  have hsplit : (⨆ E ∈ omegaSet G T, E : Subgroup Γ) ≤
      (⨆ F ∈ sna, F : Subgroup Γ) ⊔ (⨆ E ∈ omegaThree G T, E : Subgroup Γ) := by
    refine iSup₂_le fun E hE => ?_
    by_cases hA : IsNaturalAltModule ↥E 1
    · exact le_sup_of_le_right (le_iSup₂_of_le E ⟨hE, hA⟩ le_rfl)
    · exact le_sup_of_le_left (le_iSup₂_of_le E ((hsna E).2 ⟨hE, hA⟩) le_rfl)
  have hG₃c : ∀ F ∈ sna, ∀ f ∈ F, ∀ r ∈ (⨆ E ∈ omegaThree G T, E : Subgroup Γ),
      r * f = f * r := by
    intro F hF f hf r hr
    have h2 : (⨆ E ∈ omegaThree G T, E : Subgroup Γ) ≤ Subgroup.centralizer ({f} : Set Γ) := by
      refine iSup₂_le fun E hE e he => ?_
      have hFE : F ≠ E := fun hh => (hna F hF).2 (hh ▸ hE.2)
      have := omega_comm' h hE.1 (hna F hF).1 hFE f hf e he
      refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact this
    exact (Subgroup.mem_centralizer_iff.mp (h2 hr) f (Set.mem_singleton f)).symm
  have hcomm : ∀ q ∈ (⨆ F ∈ sna, F : Subgroup Γ), ∀ r ∈ (⨆ E ∈ omegaThree G T, E : Subgroup Γ),
      q * r = r * q := by
    intro q hq r hr
    have h1 : (⨆ F ∈ sna, F : Subgroup Γ) ≤
        Subgroup.centralizer ((⨆ E ∈ omegaThree G T, E : Subgroup Γ) : Set Γ) := by
      refine iSup₂_le fun F hF f hf => Subgroup.mem_centralizer_iff.mpr fun r hr => ?_
      exact hG₃c F hF f hf r hr
    exact (Subgroup.mem_centralizer_iff.mp (h1 hq) r hr).symm
  obtain ⟨q, hq, r, hr, rfl⟩ := exists_mul_of_mem_sup' hcomm (hsplit hx.2)
  have hqC := mem_iSup_cStarIn_of_na h hms sna hna (q * r) hx.1 q hq r
    (fun F hF f hf => hG₃c F hF f hf r hr) rfl
  have hqC' : q ∈ cStarIn G T :=
    (iSup₂_le fun F _ => inf_le_left :
      (⨆ F ∈ sna, cStarIn G T ⊓ F : Subgroup Γ) ≤ cStarIn G T) hqC
  have hrC : r ∈ cStarIn G T := by
    have := (cStarIn G T).mul_mem ((cStarIn G T).inv_mem hqC') hx.1
    simpa using this
  have hr3 : r ∈ (⨆ E ∈ omegaThree G T, pCoreOf 2 E : Subgroup Γ) := by
    obtain ⟨s3, hs3⟩ := exists_finset_mem_iff (omegaThree G T)
    have hr3c : ∀ E ∈ omegaThree G T, r ∈ Subgroup.centralizer (pCoreOf 2 E : Set Γ) := by
      intro E hE
      by_contra hcon
      have h0 := badThree_eq_empty h _ r hrC hr rfl
      have : E ∈ badThree G T r := ⟨hE, hcon⟩
      rw [h0] at this
      exact this
    rw [iSup_set_eq_finset (omegaThree G T) s3 hs3 (fun E => pCoreOf 2 E)]
    refine mem_iSup_pCoreOf_of_centralizes h s3 (fun F hF => ((hs3 F).1 hF).1) r ?_ ?_
    · rw [← iSup_set_eq_finset (omegaThree G T) s3 hs3 (fun E => E)]
      exact hr
    · intro F hF
      exact hr3c F ((hs3 F).1 hF)
  have hq' : q ∈ (⨆ E ∈ omegaSet G T, cStarIn G T ⊓ E : Subgroup Γ) :=
    (iSup₂_le fun F hF => le_iSup₂_of_le F (hna F hF).1 le_rfl :
      (⨆ F ∈ sna, cStarIn G T ⊓ F : Subgroup Γ) ≤ ⨆ E ∈ omegaSet G T, cStarIn G T ⊓ E) hqC
  have hr' : r ∈ (⨆ E ∈ omegaSet G T, cStarIn G T ⊓ E : Subgroup Γ) :=
    (iSup₂_le fun E hE => le_iSup₂_of_le E hE.1 (cStarIn_inf_eq_of_three h hE.1 hE.2).ge :
      (⨆ E ∈ omegaThree G T, pCoreOf 2 E : Subgroup Γ) ≤
        ⨆ E ∈ omegaSet G T, cStarIn G T ⊓ E) hr3
  exact Subgroup.mul_mem _ hq' hr'

end CFSG.CGT.PushingUpLit.BHS7
