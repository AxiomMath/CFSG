module

public import CFSG.CGT.PushingUpLit.BHS7.OffenderTrick
public import CFSG.CGT.PushingUpLit.BHS7.OmegaProdNA

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.G6 CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement
open Equiv Equiv.Perm

variable {Γ : Type} [Group Γ] [Finite Γ] {G T E : Subgroup Γ}

theorem swap_conj_fin_three {n : ℕ} (hn : n = 3) :
    ∀ x y : Fin n, x ≠ y → ∀ c : Perm (Fin n), Perm.sign c = 1 →
      swap x y * c * (swap x y)⁻¹ = c⁻¹ := by
  subst hn
  decide

theorem eq_one_of_sq_fin_three {n : ℕ} (hn : n = 3) :
    ∀ c : Perm (Fin n), Perm.sign c = 1 → c * c = 1 → c = 1 := by
  subst hn
  decide

theorem eq_one_of_fix_fin_three {n : ℕ} (hn : n = 3) :
    ∀ (c : Perm (Fin n)) (p : Fin n), Perm.sign c = 1 → c p = p → c = 1 := by
  subst hn
  decide

theorem exists_altAct_three (h : MinCex G T) (hE : E ∈ omegaSet G T)
    (hA : IsNaturalAltModule ↥E 1) : ∃ A : AltAct G T E 1, A.k = 1 := by
  obtain ⟨A⟩ := nonempty_altAct h.charTwo h.sylow (omega_isBTBlock h hE) le_rfl hA
  exact ⟨A, by have h1 := A.one_le_k; have h2 := A.k_le; omega⟩

omit [Finite Γ] in
theorem AltAct.exists_swap_of_k_one (A : AltAct G T E 1) (hk : A.k = 1) :
    ∃ x y : Fin (2 * 1 + 1), x ≠ y ∧ ∀ b : ↥(E ⊔ baum T), (b : Γ) ∈ baum T →
      A.Φ b = 1 ∨ A.Φ b = swap x y := by
  obtain ⟨T₀, hsw, -, hcard, hY⟩ := A.baum_swap
  rw [hk] at hcard
  obtain ⟨t, rfl⟩ := Set.ncard_eq_one.mp hcard
  obtain ⟨x, y, hxy, rfl⟩ := hsw t (Set.mem_singleton t)
  refine ⟨x, y, hxy, fun b hb => ?_⟩
  have hbY : A.Φ b ∈ A.Y := A.mem_Y_of_mem_baum hb
  have hbY' : A.Φ b ∈ Subgroup.closure ({swap x y} : Set (Perm (Fin (2 * 1 + 1)))) := by
    rw [← hY]
    exact hbY
  obtain ⟨n, hn⟩ := Subgroup.mem_closure_singleton.mp hbY'
  have hsq : swap x y ^ (2 : ℤ) = 1 := by
    rw [zpow_two]
    exact swap_mul_self x y
  rcases Int.even_or_odd' n with ⟨k, rfl | rfl⟩
  · left
    rw [← hn, zpow_mul, hsq, one_zpow]
  · right
    rw [← hn, zpow_add_one, zpow_mul, hsq, one_zpow, one_mul]

theorem cStarIn_inf_eq_of_three (h : MinCex G T) (hE : E ∈ omegaSet G T)
    (hA : IsNaturalAltModule ↥E 1) : cStarIn G T ⊓ E = pCoreOf 2 E := by
  have hEb := omega_isBTBlock h hE
  have hS : IsSylowTwoOf (T ⊓ E) E :=
    isSylowTwoOf_inf_of_isSubnormal hE.2 (isSylowTwoOf_of_isSylowOf h.sylow)
  obtain ⟨A, hk⟩ := exists_altAct_three h hE hA
  obtain ⟨p₀, hp₀⟩ := A.exists_cStarIn_iff le_rfl hk h hEb hS (omega_not_le_cStarIn h hE)
  have hchar := charTwo_of_isBTBlock h.charTwo h.sylow hEb
  apply le_antisymm
  · intro e he
    have heH : e ∈ E ⊔ baum T := (le_sup_left : E ≤ E ⊔ baum T) he.2
    have h1 : A.Φ ⟨e, heH⟩ p₀ = p₀ := (hp₀ ⟨e, heH⟩).mp he.1
    have h2 : A.Φ ⟨e, heH⟩ = 1 :=
      eq_one_of_fix_fin_three (by norm_num) _ p₀
        (mem_alternatingGroup.mp (A.alt_of_mem _ he.2)) h1
    have h3 := (A.ker_iff _).mp h2
    have h4 : e ∈ E ⊓ Subgroup.centralizer (pCoreOf 2 E : Set Γ) := ⟨he.2, h3⟩
    rwa [inf_centralizer_pCoreOf_eq hchar hEb.elemAbelian.1] at h4
  · intro w hw
    have hWT : pCoreOf 2 E ≤ T := pCoreOf_le_sylow h.charTwo h.sylow hEb h.sylow
    exact ⟨le_cStarIn_of_minCex h (hWT hw),
      CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 E hw⟩

theorem a3_commutator_iff (h : MinCex G T) (hE : E ∈ omegaSet G T)
    (hA : IsNaturalAltModule ↥E 1) {b y e : Γ} (hb : b ∈ baum T)
    (hbW : b ∉ Subgroup.centralizer (pCoreOf 2 E : Set Γ)) (he : e ∈ E)
    (hy : ∀ w ∈ pCoreOf 2 E, y * w * y⁻¹ = e * w * e⁻¹) :
    y * b * y⁻¹ * b⁻¹ ∈ Subgroup.centralizer (pCoreOf 2 E : Set Γ) ↔
      y ∈ Subgroup.centralizer (pCoreOf 2 E : Set Γ) := by
  classical
  have hEb := omega_isBTBlock h hE
  obtain ⟨A, hk⟩ := exists_altAct_three h hE hA
  obtain ⟨x, x', hxx', hY⟩ := A.exists_swap_of_k_one hk
  have hEW : E ≤ Subgroup.normalizer (pCoreOf 2 E : Set Γ) := le_normalizer_pCoreOf_self E
  have hBE : baum T ≤ Subgroup.normalizer (E : Set Γ) := baum_le_normalizer_of_isBTBlock hEb
  have hBW : baum T ≤ Subgroup.normalizer (pCoreOf 2 E : Set Γ) :=
    hBE.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 E)
  have heH : e ∈ E ⊔ baum T := (le_sup_left : E ≤ E ⊔ baum T) he
  have hbH : b ∈ E ⊔ baum T := (le_sup_right : baum T ≤ E ⊔ baum T) hb
  have hΦb : A.Φ ⟨b, hbH⟩ = swap x x' := by
    rcases hY ⟨b, hbH⟩ hb with h1 | h1
    · exact absurd ((A.ker_iff _).mp h1) hbW
    · exact h1
  have hnW : ∀ g ∈ Subgroup.normalizer (pCoreOf 2 E : Set Γ), ∀ w ∈ pCoreOf 2 E,
      g * w * g⁻¹ ∈ pCoreOf 2 E := fun g hg w hw => (Subgroup.mem_normalizer_iff.mp hg w).mp hw
  have hnW' : ∀ g ∈ Subgroup.normalizer (pCoreOf 2 E : Set Γ), ∀ w ∈ pCoreOf 2 E,
      g⁻¹ * w * g ∈ pCoreOf 2 E := fun g hg w hw => by
    have := hnW g⁻¹ ((Subgroup.normalizer _).inv_mem hg) w hw
    simpa using this
  have heN : e ∈ Subgroup.normalizer (pCoreOf 2 E : Set Γ) := hEW he
  have hbN : b ∈ Subgroup.normalizer (pCoreOf 2 E : Set Γ) := hBW hb
  have hyinv : ∀ w ∈ pCoreOf 2 E, y⁻¹ * w * y = e⁻¹ * w * e := by
    intro w hw
    have h1 := hy _ (hnW' e heN w hw)
    have h2 : y * (e⁻¹ * w * e) * y⁻¹ = w := by
      rw [h1]
      group
    calc y⁻¹ * w * y = y⁻¹ * (y * (e⁻¹ * w * e) * y⁻¹) * y := by rw [h2]
      _ = e⁻¹ * w * e := by group
  have hconj : ∀ w ∈ pCoreOf 2 E, (y * b * y⁻¹ * b⁻¹) * w * (y * b * y⁻¹ * b⁻¹)⁻¹ =
      (e * b * e⁻¹ * b⁻¹) * w * (e * b * e⁻¹ * b⁻¹)⁻¹ := by
    intro w hw
    have hu := hnW' b hbN w hw
    have hv := hnW' e heN _ hu
    have hv' := hnW b hbN _ hv
    have c1 := hyinv _ hu
    have c2 := hy _ hv'
    calc (y * b * y⁻¹ * b⁻¹) * w * (y * b * y⁻¹ * b⁻¹)⁻¹
        = y * (b * (y⁻¹ * (b⁻¹ * w * b) * y) * b⁻¹) * y⁻¹ := by group
      _ = y * (b * (e⁻¹ * (b⁻¹ * w * b) * e) * b⁻¹) * y⁻¹ := by rw [c1]
      _ = e * (b * (e⁻¹ * (b⁻¹ * w * b) * e) * b⁻¹) * e⁻¹ := c2
      _ = (e * b * e⁻¹ * b⁻¹) * w * (e * b * e⁻¹ * b⁻¹)⁻¹ := by group
  have hcent : ∀ g : Γ, g ∈ Subgroup.centralizer (pCoreOf 2 E : Set Γ) ↔
      ∀ w ∈ pCoreOf 2 E, g * w * g⁻¹ = w := by
    intro g
    rw [Subgroup.mem_centralizer_iff]
    constructor
    · intro hg w hw
      rw [mul_inv_eq_iff_eq_mul]
      exact (hg w hw).symm
    · intro hg w hw
      have := hg w hw
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this.symm
  have hz : (e * b * e⁻¹ * b⁻¹) ∈ Subgroup.centralizer (pCoreOf 2 E : Set Γ) ↔
      e ∈ Subgroup.centralizer (pCoreOf 2 E : Set Γ) := by
    have hmem : e * b * e⁻¹ * b⁻¹ ∈ E ⊔ baum T :=
      (E ⊔ baum T).mul_mem ((E ⊔ baum T).mul_mem ((E ⊔ baum T).mul_mem heH hbH)
        ((E ⊔ baum T).inv_mem heH)) ((E ⊔ baum T).inv_mem hbH)
    have e1 : (⟨e * b * e⁻¹ * b⁻¹, hmem⟩ : ↥(E ⊔ baum T)) =
        ⟨e, heH⟩ * ⟨b, hbH⟩ * ⟨e, heH⟩⁻¹ * ⟨b, hbH⟩⁻¹ := rfl
    have hc : Perm.sign (A.Φ ⟨e, heH⟩) = 1 :=
      mem_alternatingGroup.mp (A.alt_of_mem _ he)
    have hc' : Perm.sign (A.Φ ⟨e, heH⟩)⁻¹ = 1 := by rw [map_inv, hc]; rfl
    have h3 : swap x x' * (A.Φ ⟨e, heH⟩)⁻¹ * (swap x x')⁻¹ = A.Φ ⟨e, heH⟩ := by
      have := swap_conj_fin_three (n := 2 * 1 + 1) (by norm_num) x x' hxx' _ hc'
      rw [this, inv_inv]
    have h4 : A.Φ ⟨e * b * e⁻¹ * b⁻¹, hmem⟩ = A.Φ ⟨e, heH⟩ * A.Φ ⟨e, heH⟩ := by
      rw [e1, map_mul, map_mul, map_mul, map_inv, map_inv, hΦb]
      calc A.Φ ⟨e, heH⟩ * swap x x' * (A.Φ ⟨e, heH⟩)⁻¹ * (swap x x')⁻¹
          = A.Φ ⟨e, heH⟩ * (swap x x' * (A.Φ ⟨e, heH⟩)⁻¹ * (swap x x')⁻¹) := by group
        _ = A.Φ ⟨e, heH⟩ * A.Φ ⟨e, heH⟩ := by rw [h3]
    rw [← A.ker_iff ⟨_, hmem⟩, ← A.ker_iff ⟨e, heH⟩, h4]
    constructor
    · intro h5
      exact eq_one_of_sq_fin_three (n := 2 * 1 + 1) (by norm_num) _ hc h5
    · intro h5
      rw [h5, one_mul]
  rw [hcent (y * b * y⁻¹ * b⁻¹), hcent y]
  constructor
  · intro H w hw
    have h1 : e * b * e⁻¹ * b⁻¹ ∈ Subgroup.centralizer (pCoreOf 2 E : Set Γ) := by
      rw [hcent]
      intro w' hw'
      rw [← hconj w' hw']
      exact H w' hw'
    have h2 := (hcent e).mp (hz.mp h1)
    rw [hy w hw]
    exact h2 w hw
  · intro H w hw
    have h1 : e ∈ Subgroup.centralizer (pCoreOf 2 E : Set Γ) := by
      rw [hcent]
      intro w' hw'
      rw [← hy w' hw']
      exact H w' hw'
    have h2 := (hcent _).mp (hz.mpr h1)
    rw [hconj w hw]
    exact h2 w hw

theorem a3_distinct (h : MinCex G T) {E E' : Subgroup Γ} (hE : E ∈ omegaSet G T)
    (hE' : E' ∈ omegaSet G T) (hA : IsNaturalAltModule ↥E 1) (hA' : IsNaturalAltModule ↥E' 1)
    (hne : E' ≠ E) :
    ∃ b ∈ baum T, ¬ (b ∈ Subgroup.centralizer (pCoreOf 2 E : Set Γ) ↔
      b ∈ Subgroup.centralizer (pCoreOf 2 E' : Set Γ)) := by
  classical
  by_contra hcon
  push Not at hcon
  have hEb := omega_isBTBlock h hE
  have hEb' := omega_isBTBlock h hE'
  obtain ⟨A, hk⟩ := exists_altAct_three h hE hA
  obtain ⟨A', hk'⟩ := exists_altAct_three h hE' hA'
  obtain ⟨x, y, hxy, hY⟩ := A.exists_swap_of_k_one hk
  obtain ⟨x', y', hxy', hY'⟩ := A'.exists_swap_of_k_one hk'
  have hWab := hEb.elemAbelian.1
  have hWab' := hEb'.elemAbelian.1
  have hW₁ : IsElemAbelian 2 (pCoreOf 2 E) := isElemAbelian_of_forall' hWab hEb.elemAbelian.2
  have hW₂ : IsElemAbelian 2 (pCoreOf 2 E') := isElemAbelian_of_forall' hWab' hEb'.elemAbelian.2
  have hWT : pCoreOf 2 E ≤ T := pCoreOf_le_sylow h.charTwo h.sylow hEb h.sylow
  have hWT' : pCoreOf 2 E' ≤ T := pCoreOf_le_sylow h.charTwo h.sylow hEb' h.sylow
  have hWE : pCoreOf 2 E ≤ E := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 E
  have hWE' : pCoreOf 2 E' ≤ E' := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 E'
  have hBE : baum T ≤ Subgroup.normalizer (E : Set Γ) := baum_le_normalizer_of_isBTBlock hEb
  have hBE' : baum T ≤ Subgroup.normalizer (E' : Set Γ) := baum_le_normalizer_of_isBTBlock hEb'
  have hBW : baum T ≤ Subgroup.normalizer (pCoreOf 2 E : Set Γ) :=
    hBE.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 E)
  have hBW' : baum T ≤ Subgroup.normalizer (pCoreOf 2 E' : Set Γ) :=
    hBE'.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 E')
  have hcomm : ∀ u ∈ E', ∀ v ∈ E, u * v = v * u := omega_comm' h hE hE' hne
  have h12 : ∀ u ∈ pCoreOf 2 E, ∀ v ∈ pCoreOf 2 E', u * v = v * u := fun u hu v hv =>
    (hcomm v (hWE' hv) u (hWE hu)).symm
  have hdisj : ∀ u ∈ pCoreOf 2 E, u ∈ pCoreOf 2 E' → u = 1 := by
    intro u hu hu'
    refine A.eq_one_of_centralizes le_rfl hu fun e he => ?_
    have := hcomm u (hWE' hu') e he
    rw [mul_inv_eq_iff_eq_mul]
    exact this.symm
  have hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (pCoreOf 2 E : Set Γ) := by
    intro hle
    apply six_four_d h.charTwo h.sylow hEb
    rw [blockW_eq_pCoreOf hEb, Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hle
  have hex : ∃ Am : Subgroup Γ, IsMaxElemAbelian T Am ∧
      ¬ Am ≤ Subgroup.centralizer (pCoreOf 2 E : Set Γ) := by
    by_contra hnone
    push Not at hnone
    exact hJ (iSup₂_le fun Am hAm => hnone Am hAm)
  obtain ⟨Am, hAm, hAmc⟩ := hex
  obtain ⟨a, haA, haW⟩ := IsConcreteLE.not_le_iff_exists.mp hAmc
  have haB : a ∈ baum T := B6.thompsonJ_le_baum T (B6.le_thompsonJ hAm haA)
  have haW' : a ∉ Subgroup.centralizer (pCoreOf 2 E' : Set Γ) := fun hh =>
    haW ((hcon a haB).mpr hh)
  have hmove : ∀ {W : Subgroup Γ}, a ∉ Subgroup.centralizer (W : Set Γ) →
      ∃ u ∈ W, a * u * a⁻¹ ≠ u := by
    intro W haW
    rw [Subgroup.mem_centralizer_iff] at haW
    push Not at haW
    obtain ⟨u, hu, hne'⟩ := haW
    refine ⟨u, hu, fun hh => hne' ?_⟩
    rw [mul_inv_eq_iff_eq_mul] at hh
    exact hh.symm
  obtain ⟨u₁, hu₁, hu₁a⟩ := hmove haW
  obtain ⟨u₂, hu₂, hu₂a⟩ := hmove haW'
  have hAmB : ∀ b ∈ Am, b ∈ baum T := fun b hb => B6.thompsonJ_le_baum T (B6.le_thompsonJ hAm hb)
  have hker : ∀ {E₀ : Subgroup Γ} (A₀ : AltAct G T E₀ 1) (x₀ y₀ : Fin (2 * 1 + 1)),
      (∀ b : ↥(E₀ ⊔ baum T), (b : Γ) ∈ baum T → A₀.Φ b = 1 ∨ A₀.Φ b = swap x₀ y₀) →
      ∀ b₁ ∈ baum T, ∀ b₂ ∈ baum T, b₁ ∉ Subgroup.centralizer (pCoreOf 2 E₀ : Set Γ) →
        b₂ ∉ Subgroup.centralizer (pCoreOf 2 E₀ : Set Γ) →
        b₁⁻¹ * b₂ ∈ Subgroup.centralizer (pCoreOf 2 E₀ : Set Γ) := by
    intro E₀ A₀ x₀ y₀ hY₀ b₁ hb₁ b₂ hb₂ h₁ h₂
    have hb₁H : b₁ ∈ E₀ ⊔ baum T := (le_sup_right : baum T ≤ E₀ ⊔ baum T) hb₁
    have hb₂H : b₂ ∈ E₀ ⊔ baum T := (le_sup_right : baum T ≤ E₀ ⊔ baum T) hb₂
    have e₁ : A₀.Φ ⟨b₁, hb₁H⟩ = swap x₀ y₀ := by
      rcases hY₀ ⟨b₁, hb₁H⟩ hb₁ with h1 | h1
      · exact absurd ((A₀.ker_iff _).mp h1) h₁
      · exact h1
    have e₂ : A₀.Φ ⟨b₂, hb₂H⟩ = swap x₀ y₀ := by
      rcases hY₀ ⟨b₂, hb₂H⟩ hb₂ with h1 | h1
      · exact absurd ((A₀.ker_iff _).mp h1) h₂
      · exact h1
    refine (A₀.ker_iff ⟨b₁⁻¹ * b₂, (E₀ ⊔ baum T).mul_mem ((E₀ ⊔ baum T).inv_mem hb₁H) hb₂H⟩).mp ?_
    have : (⟨b₁⁻¹ * b₂, (E₀ ⊔ baum T).mul_mem ((E₀ ⊔ baum T).inv_mem hb₁H) hb₂H⟩ :
        ↥(E₀ ⊔ baum T)) = ⟨b₁, hb₁H⟩⁻¹ * ⟨b₂, hb₂H⟩ := rfl
    rw [this, map_mul, map_inv, e₁, e₂, inv_mul_cancel]
  refine false_of_offender hAm hW₁ hW₂ hWT hWT' h12 hdisj
    (fun a' ha' w hw => (Subgroup.mem_normalizer_iff.mp (hBW (hAmB a' ha')) w).mp hw)
    (fun a' ha' w hw => (Subgroup.mem_normalizer_iff.mp (hBW' (hAmB a' ha')) w).mp hw)
    haA hu₁ hu₂ hu₁a hu₂a fun b hb => ?_
  by_cases hbW : b ∈ Subgroup.centralizer (pCoreOf 2 E : Set Γ)
  · exact Or.inl ⟨⟨hb, hbW⟩, (hcon b (hAmB b hb)).mp hbW⟩
  · have hbW' : b ∉ Subgroup.centralizer (pCoreOf 2 E' : Set Γ) := fun hh =>
      hbW ((hcon b (hAmB b hb)).mpr hh)
    right
    have hab : a⁻¹ * b ∈ Am := Am.mul_mem (Am.inv_mem haA) hb
    exact ⟨⟨hab, hker A x y hY a haB b (hAmB b hb) haW hbW⟩,
      hker A' x' y' hY' a haB b (hAmB b hb) haW' hbW'⟩

end CFSG.CGT.PushingUpLit.BHS7
