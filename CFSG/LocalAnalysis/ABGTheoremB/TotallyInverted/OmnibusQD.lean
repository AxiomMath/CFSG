module

public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.DataConstructionQD
public import CFSG.LocalAnalysis.ABGTheoremB.IV6
public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.FinalAssembly
public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.InputsFourFusion
public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.NoDataBridge
public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.OmnibusWQ

public section

namespace CFSG.ABGTheoremB.TotallyInverted

open CFSG.ABGLocalTools CFSG.QuasiDihedralFusion Omnibus OmnibusW
open scoped Pointwise

namespace OmnibusQD

variable {G : Type} [Group G] [Finite G] {σ : Setting G} {r : ℕ}

private theorem nStructure_of_zero (Δ : Data σ r)
    (h0 : ∀ Z : Subgroup G, Z ≤ σ.N → Odd (Nat.card Z) →
      σ.C ≤ Subgroup.normalizer (Z : Set G) →
      ∃ P : Subgroup G, σ.C ≤ Subgroup.normalizer (P : Set G) ∧
        (Z : Set G) ⊆ (σ.C : Set G) * (P : Set G) ∧
        ∃ Y ∈ ({σ.Ps r 0, R Δ 0, Rs Δ 0} : Set (Subgroup G)),
          ∀ g ∈ P, (∃ k : ℕ, g ^ r ^ k = 1) → g ∈ Y) :
    ABG_II_4_11_Input Δ := by
  intro i Z hZN hZ hCZ
  set g : G := Δ.a ^ (i : ℕ) with hgdef
  have hgM : g ∈ σ.M := a_pow_mem_M Δ _
  have hgC : conjSub g σ.C = σ.C := conjSub_a_pow_C Δ _
  have hgN : conjSub g⁻¹ (σ.Ns i) = σ.N := by
    rw [hgdef, ← conjSub_a_pow_N Δ i, conjSub_inv_conjSub]
  have hZ'N : conjSub g⁻¹ Z ≤ σ.N := hgN ▸ conjSub_mono hZN
  have hZ'odd : Odd (Nat.card (conjSub g⁻¹ Z)) := by rw [card_conjSub]; exact hZ
  have hCZ' : σ.C ≤ Subgroup.normalizer ((conjSub g⁻¹ Z : Subgroup G) : Set G) :=
    le_normalizer_conjSub hCZ (σ.M.inv_mem hgM)
  obtain ⟨P, hCP, hZP, Y, hY, hPY⟩ := h0 _ hZ'N hZ'odd hCZ'
  have hconj : ∀ {X : Fin 3 → Subgroup G}, (∀ j, conjSub Δ.a (X j) = X (j + 1)) →
      conjSub g (X 0) = X i := fun hX => conjSub_a_pow_zero Δ hX i
  have hR : ∀ j, conjSub Δ.a (R Δ j) = R Δ (j + 1) := fun j => by
    rw [R, R, conjSub_sup, (Δ.Q_conj j).1, Δ.P_conj j]
  have hRs : ∀ j, conjSub Δ.a (Rs Δ j) = Rs Δ (j + 1) := fun j => by
    rw [Rs, Rs, conjSub_sup, (Δ.Q_conj j).2, Δ.P_conj j]
  refine ⟨conjSub g P, le_normalizer_conjSub hCP hgM, fun z hz => ?_, conjSub g Y, ?_,
    fun x hx hxr => ?_⟩
  · have hz' : g⁻¹ * z * g ∈ ((conjSub g⁻¹ Z : Subgroup G) : Set G) := by
      rw [SetLike.mem_coe, mem_conjSub, show g⁻¹⁻¹ * (g⁻¹ * z * g) * g⁻¹ = z by group]
      exact hz
    obtain ⟨c, hc, p, hp, he⟩ := hZP hz'
    refine ⟨g * c * g⁻¹, ?_, g * p * g⁻¹, conj_mem_conjSub hp, ?_⟩
    · rw [SetLike.mem_coe, ← hgC]
      exact conj_mem_conjSub hc
    · have he' : c * p = g⁻¹ * z * g := he
      change g * c * g⁻¹ * (g * p * g⁻¹) = z
      rw [show g * c * g⁻¹ * (g * p * g⁻¹) = g * (c * p) * g⁻¹ by group, he']
      group
  · rcases hY with h | h | h
    · rw [h, hconj Δ.P_conj]
      exact Or.inl rfl
    · rw [h, hconj hR]
      exact Or.inr (Or.inl rfl)
    · rw [Set.mem_singleton_iff] at h
      rw [h, hconj hRs]
      exact Or.inr (Or.inr rfl)
  · obtain ⟨k, hk⟩ := hxr
    rw [mem_conjSub] at hx ⊢
    refine hPY _ hx ⟨k, ?_⟩
    rw [show g⁻¹ * x * g = g⁻¹ * x * g⁻¹⁻¹ by group, conj_pow, hk]
    group

private theorem nStructure_zero_of_inf_eq_bot (hσ : σ.IsValid) (hT : σ.TIFacts) (Δ : Data σ r)
    (hJ₀ : Δ.J ⊓ σ.ON = ⊥) {Z : Subgroup G} (hZN : Z ≤ σ.N) (hZ : Odd (Nat.card Z))
    (hCZ : σ.C ≤ Subgroup.normalizer (Z : Set G)) :
    ∃ P : Subgroup G, σ.C ≤ Subgroup.normalizer (P : Set G) ∧
      (Z : Set G) ⊆ (σ.C : Set G) * (P : Set G) ∧
      ∃ Y ∈ ({σ.Ps r 0, R Δ 0, Rs Δ 0} : Set (Subgroup G)),
        ∀ g ∈ P, (∃ k : ℕ, g ^ r ^ k = 1) → g ∈ Y := by
  have hJ : σ.IsLayerComplement Δ.J := ⟨Δ.J_le, Δ.L₀_eq, hJ₀, Δ.J_normal, Δ.J_centralizes⟩
  obtain ⟨p', X, hp', hX, hZle⟩ :=
    hT.permutable_le Δ.J hJ Z hZN hZ (mul_comm_of_le_normalizer hCZ).symm
  obtain ⟨hXJ, hXp, hCX, hXC⟩ := hX
  have hXN : X ≤ σ.N := hXJ.trans (hJ.le.trans hσ.L₀_le_N)
  have hCON : σ.C ≤ Subgroup.normalizer (σ.ON : Set G) := σ.C_le_N.trans σ.N_le_normalizer_ON
  have hCP : σ.C ≤ Subgroup.normalizer ((X ⊔ σ.ON : Subgroup G) : Set G) :=
    fun c hc => mem_normalizer_sup (hCX hc) (hCON hc)
  have key : ∀ g ∈ X ⊔ σ.ON, ∀ k : ℕ, g ^ r ^ k = 1 →
      ∃ x ∈ X, ∃ o ∈ σ.Ps r 0, x ^ r ^ k = 1 ∧ x * o = g := by
    intro g hg k hk
    have hg' : g ∈ ((X ⊔ σ.ON : Subgroup G) : Set G) := hg
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _
      (hXN.trans σ.N_le_normalizer_ON)] at hg'
    obtain ⟨x, hx, o, ho, rfl⟩ := hg'
    have hcomm : Commute x o :=
      ((Subgroup.mem_centralizer_iff.mp (Δ.J_centralizes (hXJ hx))) o ho).symm
    have h1 : x ^ r ^ k * o ^ r ^ k = 1 := by rw [← hcomm.mul_pow]; exact hk
    have h2 : x ^ r ^ k = (o ^ r ^ k)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have h3 : x ^ r ^ k ∈ Δ.J ⊓ σ.ON := by
      refine ⟨Δ.J.pow_mem (hXJ hx) _, ?_⟩
      rw [h2]
      exact σ.ON.inv_mem (σ.ON.pow_mem ho _)
    rw [hJ.inf_eq, Subgroup.mem_bot] at h3
    have h4 : o ^ r ^ k = 1 := by rwa [h3, one_mul] at h1
    exact ⟨x, hx, o, mem_Ps_zero_of_mem_ON Δ ho h4, h3, rfl⟩
  refine ⟨X ⊔ σ.ON, hCP, fun z hz => ?_, ?_⟩
  · have hz' : z ∈ ((σ.C ⊔ (X ⊔ σ.ON) : Subgroup G) : Set G) := by
      rw [← sup_assoc]
      exact hZle hz
    rwa [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hCP] at hz'
  by_cases hXr : p' = r ∧ X ≠ ⊥
  · obtain ⟨hpr, hX1⟩ := hXr
    rw [hpr] at hXp
    obtain ⟨hδε, hrp⟩ :=
      hT.layer_signalizer Δ.J hJ r Δ.prime Δ.ne_two X ⟨hXJ, hXp, hCX, hXC⟩ hX1
    have hrq : r ∣ σ.q := by
      rw [Setting.q, hrp]
      exact dvd_pow_self _ (Nat.one_le_iff_ne_zero.mp hσ.one_le_f)
    obtain ⟨-, -, -, -, -, hcov, -⟩ := Δ.Q_cases ⟨hδε, hrq⟩ 0
    have hXJ0 : X ≤ conjSub (Δ.a ^ ((0 : Fin 3) : ℕ)) Δ.J := by simpa using hXJ
    rcases hcov X hXJ0 hXp hCX with hXQ | hXQ
    · refine ⟨R Δ 0, Or.inr (Or.inl rfl), fun g hg ⟨k, hk⟩ => ?_⟩
      obtain ⟨x, hx, o, ho, -, rfl⟩ := key g hg k hk
      exact Subgroup.mul_mem_sup (hXQ hx) ho
    · refine ⟨Rs Δ 0, Or.inr (Or.inr rfl), fun g hg ⟨k, hk⟩ => ?_⟩
      obtain ⟨x, hx, o, ho, -, rfl⟩ := key g hg k hk
      exact Subgroup.mul_mem_sup (hXQ hx) ho
  · refine ⟨σ.Ps r 0, Or.inl rfl, fun g hg ⟨k, hk⟩ => ?_⟩
    obtain ⟨x, hx, o, ho, hxk, rfl⟩ := key g hg k hk
    have hx1 : x = 1 := by
      by_cases hpr : p' = r
      · have hX1 : X = ⊥ := by
          by_contra h
          exact hXr ⟨hpr, h⟩
        rw [hX1] at hx
        exact Subgroup.mem_bot.mp hx
      · obtain ⟨m, hm⟩ := hXp ⟨x, hx⟩
        have hxm : x ^ p' ^ m = 1 := by simpa using congrArg Subtype.val hm
        have hcop : Nat.Coprime (p' ^ m) (r ^ k) :=
          Nat.Coprime.pow _ _ ((Nat.coprime_primes hp' Δ.prime).mpr hpr)
        rw [← orderOf_eq_one_iff]
        exact Nat.Coprime.eq_one_of_dvd
          (Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hxm) hcop)
          (orderOf_dvd_of_pow_eq_one hxk)
    rw [hx1, one_mul]
    exact ho

theorem nStructure_of_inf_eq_bot (hσ : σ.IsValid) (hT : σ.TIFacts) (Δ : Data σ r)
    (hJ : Δ.J ⊓ σ.ON = ⊥) : ABG_II_4_11_Input Δ :=
  nStructure_of_zero Δ fun _ hZN hZ hCZ => nStructure_zero_of_inf_eq_bot hσ hT Δ hJ hZN hZ hCZ

theorem nStructure_of_exceptionalLayer (hT9 : TIFactsQ9 σ) (Δ : Data σ r)
    (hJ : IsExceptionalLayer σ Δ.J) : ABG_II_4_11_Input Δ := by
  refine nStructure_of_zero Δ fun Z hZN hZ hCZ => ?_
  have hZle := hT9.permutable_le Δ.J hJ Z hZN hZ (mul_comm_of_le_normalizer hCZ).symm
  have hCON : σ.C ≤ Subgroup.normalizer (σ.ON : Set G) := σ.C_le_N.trans σ.N_le_normalizer_ON
  refine ⟨σ.ON, hCON, fun z hz => ?_, σ.Ps r 0, Or.inl rfl,
    fun g hg ⟨k, hk⟩ => mem_Ps_zero_of_mem_ON Δ hg hk⟩
  have hz' : z ∈ ((σ.C ⊔ σ.ON : Subgroup G) : Set G) := hZle hz
  rwa [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hCON] at hz'

theorem nStructure (hσ : σ.IsValid) (hT : σ.TIFacts) (hT9 : TIFactsQ9 σ) (Δ : Data σ r) :
    ABG_II_4_11_Input Δ := by
  by_cases hJ₀ : Δ.J ⊓ σ.ON = ⊥
  · exact nStructure_of_inf_eq_bot hσ hT Δ hJ₀
  · obtain ⟨hq, hh, hcard⟩ := Δ.J_inf.resolve_left hJ₀
    exact nStructure_of_exceptionalLayer hT9 Δ
      ⟨Δ.J_le, Δ.L₀_eq, Δ.J_centralizes, Δ.J_normal, hq, hh, hcard⟩

theorem qConjugacy_of_nStructure (hσ : σ.IsValid) (hII : σ.ChapterIIFacts)
    (hQC : σ.QCoverFact) (h31 : ABG_II_3_1_Input G) (Δ : Data σ r)
    (hN : ABG_II_4_11_Input Δ) : ABG_V_8_7_Q_Input σ r := by
  intro H hCH _ hHQ
  obtain ⟨i, hdec⟩ := exists_le_oddCoreIn_sup_inf_Ns hσ Δ h31 hCH hHQ
  set m : G := (Δ.a ^ (i : ℕ))⁻¹ with hmdef
  have hm : m ∈ Subgroup.normalizer (σ.T : Set G) :=
    Subgroup.inv_mem _ (Subgroup.pow_mem _ (a_mem_normalizer_T hσ Δ) _)
  have hmN : conjSub m (σ.Ns i) = σ.N := by
    rw [hmdef, ← conjSub_a_pow_N Δ i, conjSub_inv_conjSub]
  refine conjugate_of_conjSub hm (conjugate_of_le_sup_inf_N hσ hII hQC Δ hN ?_
    (IsQGroup.of_mulEquiv (conjSubEquiv m H) hHQ) ?_)
  · rw [← conjSub_C hm]
    exact conjSub_mono hCH
  · calc conjSub m H ≤ conjSub m (oddCoreIn H ⊔ H ⊓ σ.Ns i) := conjSub_mono hdec
      _ = oddCoreIn (conjSub m H) ⊔ conjSub m H ⊓ σ.N := by
        rw [conjSub_sup, conjSub_inf, hmN, oddCoreIn_conjSub]

end OmnibusQD

variable {G : Type} [Group G] [Finite G] {σ : Setting G}

theorem omnibusInputs_qd {r : ℕ} (hσ : σ.IsValid) (_hh : σ.height = 1)
    (hII : σ.ChapterIIFacts) (hT : σ.TIFacts) (hT9 : TIFactsQ9 σ) (hQC : σ.QCoverFact)
    (h31 : ABG_II_3_1_Input G) (h57 : ABG_II_5_7_Input σ) (h87 : ABG_V_8_7_D_Input σ r)
    (Δ : Data σ r) : OmnibusInputs Δ where
  nStructure := OmnibusQD.nStructure hσ hT hT9 Δ
  qCentralizer := h31
  dCentralizer := h57
  qConjugacy := OmnibusQD.qConjugacy_of_nStructure hσ hII hQC h31 Δ
    (OmnibusQD.nStructure hσ hT hT9 Δ)
  dConjugacy := h87

theorem not_totallyInverted_of_height_eq_one (hσ : σ.IsValid) (hh : σ.height = 1)
    (hII : σ.ChapterIIFacts) (hV : σ.CorollaryV61) (hT : σ.TIFacts) (hT9 : TIFactsQ9 σ)
    (hd : ∃ d ∈ σ.D, d * σ.x₂ * d⁻¹ = σ.x₃) (hF₀ : IsSylowOf 2 σ.F₀ σ.C)
    (hQC : σ.QCoverFact) (h57 : ABG_II_5_7_Input σ)
    (h87 : ∀ r : ℕ, r.Prime → r ≠ 2 → ABG_V_8_7_D_Input σ r)
    (hD : Sec10.DGroupFourFusion G) (hI : ∀ (r : ℕ) (Δ : Data σ r), Sec11.Inputs Δ) :
    ∀ r : ℕ, r.Prime → r ∣ Nat.card σ.ON → σ.Exceptional r → ¬ σ.TotallyInverted r := by
  intro r hr hdvd hexc hti
  obtain ⟨Δ⟩ := nonempty_data_qd hσ hh hd hF₀ hII.automizer_T hV hT hT9 hr hdvd hexc hti
  exact no_data_of_inputs hσ hII Δ
    (omnibusInputs_qd hσ hh hII hT hT9 hQC (Inputs.abg_II_3_1_input G) h57 (h87 r hr Δ.ne_two)
      Δ)
    (abg_IV_6_2_of_propIV62 (σ.propIV62 hσ hII) hr hdvd) (Inputs.qGroupFourFusion G) hD
    (hI r Δ)

end CFSG.ABGTheoremB.TotallyInverted
