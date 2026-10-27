module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5QStepY

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS CFSG.OddStandard.Solomon75.AhatData

open scoped commutatorElement

theorem commutator_commutator_le_ker {G H : Type*} [Group G] [Group H] (f : G →* H)
    (Y₀ : Subgroup G) (Γ : Set H) (hΓ : ∀ y ∈ Y₀, f y ∈ Γ)
    (hcomm : ∀ a ∈ Γ, ∀ b ∈ Γ, ∀ c ∈ Γ, ∀ d ∈ Γ, ⁅⁅a, b⁆, ⁅c, d⁆⁆ = 1) :
    ⁅⁅Y₀, Y₀⁆, ⁅Y₀, Y₀⁆⁆ ≤ f.ker := by
  set T : Subgroup H := Y₀.map f with hT
  have hTΓ : ∀ t ∈ T, t ∈ Γ := by
    rintro _ ⟨y, hy, rfl⟩
    exact hΓ y hy
  have hN : ∀ a ∈ ⁅T, T⁆, ∀ b ∈ ⁅T, T⁆, a * b = b * a := by
    intro a ha
    rw [Subgroup.commutator_def] at ha
    induction ha using Subgroup.closure_induction with
    | mem a₀ ha₀ =>
      obtain ⟨t₁, ht₁, t₂, ht₂, rfl⟩ := ha₀
      intro b hb
      rw [Subgroup.commutator_def] at hb
      induction hb using Subgroup.closure_induction with
      | mem b₀ hb₀ =>
        obtain ⟨t₃, ht₃, t₄, ht₄, rfl⟩ := hb₀
        exact commutatorElement_eq_one_iff_mul_comm.1
          (hcomm _ (hTΓ _ ht₁) _ (hTΓ _ ht₂) _ (hTΓ _ ht₃) _ (hTΓ _ ht₄))
      | one => simp
      | mul b₁ b₂ _ _ ih₁ ih₂ =>
        calc ⁅t₁, t₂⁆ * (b₁ * b₂) = (⁅t₁, t₂⁆ * b₁) * b₂ := by group
          _ = (b₁ * ⁅t₁, t₂⁆) * b₂ := by rw [ih₁]
          _ = b₁ * (⁅t₁, t₂⁆ * b₂) := by group
          _ = b₁ * (b₂ * ⁅t₁, t₂⁆) := by rw [ih₂]
          _ = (b₁ * b₂) * ⁅t₁, t₂⁆ := by group
      | inv b₁ _ ih => exact (show Commute ⁅t₁, t₂⁆ b₁ from ih).inv_right.eq
    | one => intro b _; simp
    | mul a₁ a₂ _ _ ih₁ ih₂ =>
      intro b hb
      calc a₁ * a₂ * b = a₁ * (a₂ * b) := by group
        _ = a₁ * (b * a₂) := by rw [ih₂ b hb]
        _ = (a₁ * b) * a₂ := by group
        _ = (b * a₁) * a₂ := by rw [ih₁ b hb]
        _ = b * (a₁ * a₂) := by group
    | inv a₁ _ ih =>
      intro b hb
      exact (show Commute a₁ b from ih b hb).inv_left.eq
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [MonoidHom.mem_ker, map_commutatorElement]
  have ha' : f a ∈ ⁅T, T⁆ := by
    rw [hT, ← Subgroup.map_commutator]
    exact Subgroup.mem_map_of_mem f ha
  have hb' : f b ∈ ⁅T, T⁆ := by
    rw [hT, ← Subgroup.map_commutator]
    exact Subgroup.mem_map_of_mem f hb
  exact commutatorElement_eq_one_iff_mul_comm.2 (hN _ ha' _ hb')

namespace PairCtx

variable {X : Type} [Group X] [Finite X] {n : ℕ} {z s : X} {A A' : Subgroup X}
  {M : AhatModel X n A} {M' : AhatModel X n A'}

@[expose] def D (_ : PairCtx X n z s A A' M M') : Subgroup X :=
  centralizer ({z} : Set X) ⊓ centralizer ({s} : Set X)

@[expose] noncomputable def psiD (h : PairCtx X n z s A A' M M') : ↥h.D →* Perm (Fin n) :=
  h.psi.comp (Subgroup.inclusion inf_le_left)

@[expose] noncomputable def tauD (h : PairCtx X n z s A A' M M') : ↥h.D →* Perm (Fin n) :=
  h.swap.psi.comp (Subgroup.inclusion inf_le_right)

theorem psiD_apply (h : PairCtx X n z s A A' M M') (u : ↥h.D) : h.psiD u = M.permX u :=
  h.psi_apply ⟨u, u.2.1⟩

theorem tauD_apply (h : PairCtx X n z s A A' M M') (u : ↥h.D) : h.tauD u = M'.permX u :=
  h.swap.psi_apply ⟨u, u.2.2⟩

theorem mem_ker_psiD (h : PairCtx X n z s A A' M M') {u : ↥h.D} :
    u ∈ h.psiD.ker ↔ (u : X) ∈ h.P := by
  rw [MonoidHom.mem_ker, h.psiD_apply, M.permX_eq_one_iff h.hn (h.hNz u.2.1), h.mem_P_iff]
  exact ⟨fun hm => ⟨u.2.2, u.2.1, hm⟩, fun hm => hm.2.2⟩

theorem Y_mem_D (h : PairCtx X n z s A A' M M') {y : X} (hy : y ∈ h.Y) : y ∈ h.D :=
  ⟨hy.2, h.hAs hy.1⟩

theorem H0_liftY (h : PairCtx X n z s A A' M M') (hσ8' : (M'.permX z).support.card = 8) :
    ∀ g ∈ H0 (M'.permX z), ∃ u ∈ h.Y, M'.permX u = g := by
  intro g hg
  obtain ⟨u, hu, hzu, hug⟩ := h.swap.H0_lift hσ8' g hg
  exact ⟨u, ⟨hu, Subgroup.mem_centralizer_singleton_iff.2 hzu.symm⟩, hug⟩

theorem false_of_small [NeZero n] (h : PairCtx X n z s A A' M M') (hn10 : n ≤ 10)
    (hσ8' : (M'.permX z).support.card = 8) (hfco2 : FCO2 n (M'.permX z))
    (hY : ∀ y ∈ h.Y, M.permX y ^ 8 = 1) : False := by
  obtain ⟨ι, hι, hι2, hι1, hι4⟩ := hfco2
  simp only [Wn, hn10, ↓reduceIte] at hι
  have hcl : Subgroup.closure {g | g ∈ H0 (M'.permX z) ∧ Odd (orderOf g)} ≤ h.swap.Rbar := by
    rw [Subgroup.closure_le]
    rintro g ⟨hg, hgodd⟩
    obtain ⟨u, huY, hug⟩ := h.H0_liftY hσ8' g hg
    set u' : ↥h.D := ⟨u, h.Y_mem_D huY⟩ with hu'
    have hodd : Odd (orderOf (h.tauD u')) := by rw [h.tauD_apply]; exact hug ▸ hgodd
    obtain ⟨v, hv, hvodd, hvg⟩ := exists_odd_pow_lift h.tauD u' hodd
    have hvY : (v : X) ∈ h.Y := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
      have : ((u' ^ k : ↥h.D) : X) = u ^ k := by simp [hu']
      rw [this]
      exact Subgroup.zpow_mem _ huY k
    have hpsi : h.psiD v = 1 := by
      have h8 : orderOf (h.psiD v) ∣ 8 := by
        refine orderOf_dvd_of_pow_eq_one ?_
        rw [h.psiD_apply]
        exact hY _ hvY
      have hodd' : Odd (orderOf (h.psiD v)) := Odd.of_dvd_nat hvodd (orderOf_map_dvd _ _)
      have h8' : orderOf (h.psiD v) ∣ 2 ^ 3 := by simpa using h8
      obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h8'
      by_cases hi0 : i = 0
      · rw [hi0, pow_zero] at hi
        exact orderOf_eq_one_iff.1 hi
      · rw [hi] at hodd'
        exact absurd hodd' (by simp [Nat.not_odd_iff_even, Nat.even_pow, hi0])
    have hvP : (v : X) ∈ h.P := h.mem_ker_psiD.1 hpsi
    refine h.swap.mem_Rbar_iff.2 ⟨v, hvP, ?_⟩
    rw [← h.tauD_apply, hvg, h.tauD_apply, hug]
  exact absurd (h.swap.fixCount_le_of_involution_Rbar (hcl hι) hι2 hι1) (by omega)

theorem false_of_eleven [NeZero n] (h : PairCtx X n z s A A' M M') (hn11 : ¬ n ≤ 10)
    (hσ8' : (M'.permX z).support.card = 8) (hfco2 : FCO2 n (M'.permX z))
    (hY : ∀ y₁ ∈ h.Y, ∀ y₂ ∈ h.Y, ∀ y₃ ∈ h.Y, ∀ y₄ ∈ h.Y,
      ⁅⁅M.permX y₁, M.permX y₂⁆, ⁅M.permX y₃, M.permX y₄⁆⁆ = 1) : False := by
  obtain ⟨ι, hι, hι2, hι1, hι4⟩ := hfco2
  simp only [Wn, hn11, ↓reduceIte] at hι
  set YD : Subgroup ↥h.D := h.Y.subgroupOf h.D with hYD
  have hle : H0 (M'.permX z) ≤ YD.map h.tauD := by
    intro g hg
    obtain ⟨u, huY, hug⟩ := h.H0_liftY hσ8' g hg
    exact ⟨⟨u, h.Y_mem_D huY⟩, huY, by rw [h.tauD_apply, hug]⟩
  have hι' := Subgroup.commutator_mono (Subgroup.commutator_mono hle hle)
    (Subgroup.commutator_mono hle hle) hι
  rw [← Subgroup.map_commutator, ← Subgroup.map_commutator] at hι'
  obtain ⟨w, hw, hwι⟩ := hι'
  have hker := commutator_commutator_le_ker h.psiD YD {g | ∃ y ∈ h.Y, M.permX y = g}
    (fun y₀ hy₀ => ⟨(y₀ : X), hy₀, (h.psiD_apply y₀).symm⟩)
    (by
      rintro _ ⟨y₁, hy₁, rfl⟩ _ ⟨y₂, hy₂, rfl⟩ _ ⟨y₃, hy₃, rfl⟩ _ ⟨y₄, hy₄, rfl⟩
      exact hY y₁ hy₁ y₂ hy₂ y₃ hy₃ y₄ hy₄) hw
  have hwP : (w : X) ∈ h.P := h.mem_ker_psiD.1 hker
  have hmem : ι ∈ h.swap.Rbar := h.swap.mem_Rbar_iff.2 ⟨w, hwP, by rw [← h.tauD_apply, hwι]⟩
  exact absurd (h.swap.fixCount_le_of_involution_Rbar hmem hι2 hι1) (by omega)

end PairCtx

end CFSG.OddStandard.Solomon75
