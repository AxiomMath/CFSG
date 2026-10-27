module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81Fus1
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7S4c
public import CFSG.LocalAnalysis.ComponentInitial.OddLinearTwoAliases

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

theorem lieModel_of_isSec8JType {Y : Type} [Group Y] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (hJ : IsSec8JType Y p f) :
    ∃ p' f' : ℕ, p'.Prime ∧ p' ≠ 2 ∧ 1 ≤ f' ∧ Blueprint.LieModel Y .PSL 2 p' f' := by
  rcases hJ with hL | ⟨-, -, hA⟩
  · exact ⟨p, 2 * f, hp, hp2, by omega, hL⟩
  · exact ⟨3, 2, Nat.prime_three, by norm_num, by norm_num, Or.inl ⟨by decide,
      CFSG.LocalAnalysis.ComponentInitial.statedClassicalModel_psl_two_nine_of_alternating_six Y
        hA⟩⟩

namespace Hyp52

variable {X : Type} [Group X] [Finite X] (h : Hyp52 X)

theorem sec8_exists_sylow_Dbar : ∃ T : Sylow 2 (h.J ⧸ pPrimeCore 2 h.J),
    (T : Subgroup (h.J ⧸ pPrimeCore 2 h.J)) =
      (h.D.subgroupOf h.J).map (QuotientGroup.mk' (pPrimeCore 2 ↥h.J)) ∧
      Nat.card (T : Subgroup (h.J ⧸ pPrimeCore 2 h.J)) = Nat.card h.D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R, hR⟩ := h.sec8_D_sylow
  refine ⟨R.mapSurjective (QuotientGroup.mk'_surjective _), by rw [Sylow.coe_mapSurjective, hR],
    ?_⟩
  have hker : ¬ 2 ∣ Nat.card (QuotientGroup.mk' (pPrimeCore 2 ↥h.J)).ker := by
    rw [QuotientGroup.ker_mk']
    exact (Nat.prime_two.coprime_iff_not_dvd).mp (pPrimeCore_coprime_card (p := 2) (G := ↥h.J))
  rw [Sylow.coe_mapSurjective, Eight.card_map_of_isPGroup hker R.isPGroup', hR,
    Six.card_subgroupOf_eq, inf_eq_left.mpr inf_le_right]

variable {h}

theorem sec8_conj_mem_D {t e : X} (ht : t ∈ h.S) (he : e ∈ h.D) : t * e * t⁻¹ ∈ h.D :=
  mem_inf.mpr ⟨mul_mem (mul_mem ht (h.D_le_S he)) (inv_mem ht),
    (mem_normalizer_iff.mp (h.S_le_normalizer ht) e).mp (mem_inf.mp he).2⟩

theorem sec8_conj_mem_conjugate_P {g t e : X} (hg : g ∈ normalizer (h.S : Set X))
    (ht : t ∈ h.S) (he : e ∈ conjugate h.P g) : t * e * t⁻¹ ∈ conjugate h.P g := by
  rw [mem_conjugate_iff] at he ⊢
  have htg : g * t * g⁻¹ ∈ h.S := (mem_normalizer_iff.mp hg t).mp ht
  have := h.conj_mem_P' htg he
  rwa [show g * t * g⁻¹ * (g * e * g⁻¹) * (g * t * g⁻¹)⁻¹ = g * (t * e * t⁻¹) * g⁻¹ by group]
    at this

theorem sec8_conjugate_P_le_S {g : X} (hg : g ∈ normalizer (h.S : Set X)) :
    conjugate h.P g ≤ h.S := by
  intro e he
  rw [mem_conjugate_iff] at he
  have h1 := (mem_normalizer_iff.mp (inv_mem hg) _).mp (mem_inf.mp he).1
  rwa [show g⁻¹ * (g * e * g⁻¹) * g⁻¹⁻¹ = e by group] at h1

end Hyp52

namespace Hyp59

variable {H : Type} [Group H] [Finite H] {h : Hyp59 H}

namespace L81Hyp

theorem isSylowIn_S (H₁ : h.L81Hyp) : Seven.IsSylowIn h.S (centralizer ({h.a} : Set H)) :=
  ⟨fun _ hs => (mem_inf.mp (h.S_le hs)).1, H₁.S_sylow_C⟩

variable {H₁ : h.L81Hyp}

namespace Data

variable (d : Data H₁)

theorem not_conj_a_az (hC : CFL2C) (F : d.Facts) (c : H) :
    c⁻¹ * h.a * c ≠ h.a * d.z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hc
  have hz1 : d.z ≠ 1 := fun h1 => by
    have := d.z_ord
    rw [h1, orderOf_one] at this
    exact absurd this (by norm_num)
  have hSaz : h.S ≤ centralizer ({h.a * d.z} : Set H) := by
    intro w hw
    rw [mem_centralizer_singleton_iff]
    calc w * (h.a * d.z) = (w * h.a) * d.z := by group
      _ = (h.a * w) * d.z := by rw [h.toHyp52.comm_a hw]
      _ = h.a * (w * d.z) := by group
      _ = h.a * (d.z * w) := by rw [mem_centralizer_iff.mp d.z_S w hw]
      _ = h.a * d.z * w := by group
  obtain ⟨g', hg'N, hg'⟩ := Seven.exists_normalizer_conj_of_sylow H₁.isSylowIn_S hSaz hc
  have hC_eq := H₁.C_eq
  have hDP : h.D ⊓ h.P = ⊥ := h.toHyp52.D_inf_P_eq_bot H₁.center_J
  have hZ : ∀ w : H, (∀ t ∈ h.S, t * w = w * t) → g' * w * g'⁻¹ ∈ h.P → g' * w * g'⁻¹ = 1 ∨
      g' * w * g'⁻¹ = h.a := by
    intro w hwZ hwP
    have hpZ : ∀ t ∈ h.S, t * (g' * w * g'⁻¹) = g' * w * g'⁻¹ * t := by
      intro t ht
      have htg : g'⁻¹ * t * g' ∈ h.S := by
        have := (mem_normalizer_iff.mp (inv_mem hg'N) t).mp ht
        rwa [inv_inv] at this
      have h1 := hwZ _ htg
      calc t * (g' * w * g'⁻¹) = g' * ((g'⁻¹ * t * g') * w) * g'⁻¹ := by group
        _ = g' * (w * (g'⁻¹ * t * g')) * g'⁻¹ := by rw [h1]
        _ = g' * w * g'⁻¹ * t := by group
    have hv : g' * w * g'⁻¹ ∈ h.P ⊓ centralizer (h.S : Set H) :=
      mem_inf.mpr ⟨hwP, mem_centralizer_iff.mpr hpZ⟩
    rw [hC_eq] at hv
    exact mem_zpowers_two h.orderOf_a hv
  have hw_eq : ∀ w : H, g' * w * g'⁻¹ = h.a → w = h.a * d.z := fun w h1 => by
    calc w = g'⁻¹ * (g' * w * g'⁻¹) * g' := by group
      _ = h.a * d.z := by rw [h1, hg']
  have hDP' : h.D ⊓ conjugate h.P g' = ⊥ := by
    by_contra hne
    obtain ⟨w, hw, hw1, hwZ⟩ := Seven.exists_mem_center_of_normal h.toHyp52.isPGroup_S
      (inf_le_left.trans h.toHyp52.D_le_S)
      (fun t ht v hv => mem_inf.mpr ⟨h.toHyp52.sec8_conj_mem_D ht (mem_inf.mp hv).1,
        h.toHyp52.sec8_conj_mem_conjugate_P hg'N ht (mem_inf.mp hv).2⟩) hne
    obtain ⟨hwD, hwg⟩ := mem_inf.mp hw
    rw [mem_conjugate_iff] at hwg
    rcases hZ w hwZ hwg with h1 | h1
    · apply hw1
      calc w = g'⁻¹ * (g' * w * g'⁻¹) * g' := by group
        _ = 1 := by rw [h1]; group
    · have haD : h.a ∈ h.D := by
        have := mul_mem (hw_eq w h1 ▸ hwD) (inv_mem d.z_D)
        rwa [mul_inv_cancel_right] at this
      have := hDP ▸ mem_inf.mpr ⟨haD, h.toHyp52.a_mem_P⟩
      exact a_ne_one' (h := h) (mem_bot.mp this)
  have hPP' : h.P ⊓ conjugate h.P g' = ⊥ := by
    by_contra hne
    obtain ⟨w, hw, hw1, hwZ⟩ := Seven.exists_mem_center_of_normal h.toHyp52.isPGroup_S
      (inf_le_left.trans inf_le_left)
      (fun t ht v hv => mem_inf.mpr ⟨h.toHyp52.conj_mem_P' ht (mem_inf.mp hv).1,
        h.toHyp52.sec8_conj_mem_conjugate_P hg'N ht (mem_inf.mp hv).2⟩) hne
    obtain ⟨hwP, hwg⟩ := mem_inf.mp hw
    rw [mem_conjugate_iff] at hwg
    have hwa : w = h.a := by
      have hv : w ∈ h.P ⊓ centralizer (h.S : Set H) :=
        mem_inf.mpr ⟨hwP, mem_centralizer_iff.mpr fun t ht => (hwZ t ht)⟩
      rw [hC_eq] at hv
      rcases mem_zpowers_two h.orderOf_a hv with h1 | h1
      · exact absurd h1 hw1
      · exact h1
    rcases hZ w hwZ hwg with h1 | h1
    · apply hw1
      calc w = g'⁻¹ * (g' * w * g'⁻¹) * g' := by group
        _ = 1 := by rw [h1]; group
    · apply hz1
      have := hw_eq w h1
      rw [hwa] at this
      calc d.z = h.a⁻¹ * (h.a * d.z) := by group
        _ = 1 := by rw [← this, inv_mul_cancel]
  have hcomm : ∀ e ∈ h.D, ∀ q ∈ conjugate h.P g', e * q = q * e := by
    intro e he q hq
    have hqS : q ∈ h.S := h.toHyp52.sec8_conjugate_P_le_S hg'N hq
    have h1 : e * q * e⁻¹ * q⁻¹ ∈ h.D ⊓ conjugate h.P g' := by
      refine mem_inf.mpr ⟨?_, ?_⟩
      · rw [show e * q * e⁻¹ * q⁻¹ = e * (q * e⁻¹ * q⁻¹) by group]
        exact mul_mem he (h.toHyp52.sec8_conj_mem_D hqS (inv_mem he))
      · rw [show e * q * e⁻¹ * q⁻¹ = (e * q * e⁻¹) * q⁻¹ by group]
        exact mul_mem (h.toHyp52.sec8_conj_mem_conjugate_P hg'N (h.toHyp52.D_le_S he) hq)
          (inv_mem hq)
    rw [hDP', mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
    exact h1
  have hWN : conjugate h.P g' ≤ normalizer (h.J : Set H) :=
    (h.toHyp52.sec8_conjugate_P_le_S hg'N).trans h.toHyp52.S_le_normalizer
  have hW : conjugate h.P g' ⊓ coreActionKernel h.J = ⊥ := by
    rw [eq_bot_iff]
    intro e he
    obtain ⟨heP', heC⟩ := mem_inf.mp he
    have heP : e ∈ h.P := mem_inf.mpr ⟨h.toHyp52.sec8_conjugate_P_le_S hg'N heP', heC⟩
    rw [← hPP']
    exact mem_inf.mpr ⟨heP, heP'⟩
  obtain ⟨T, hT, hTD⟩ := h.toHyp52.sec8_exists_sylow_Dbar
  have hle : Seven.rhoImg h.J (conjugate h.P g') ≤
      centralizer (innOf (T : Subgroup (h.J ⧸ pPrimeCore 2 h.J)) :
        Set (MulAut (↥h.J ⧸ pPrimeCore 2 ↥h.J))) := by
    rw [hT, ← Seven.rhoImg_eq_innOf (inf_le_right : h.D ≤ h.J)]
    rintro _ ⟨⟨q, hqN⟩, hq, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨⟨e, heN⟩, he, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact hcomm e (mem_subgroupOf.mp he) q (mem_subgroupOf.mp hq)
  have hR2 : IsPGroup 2 (Seven.rhoImg h.J (conjugate h.P g')) := by
    have hW2 : IsPGroup 2 (conjugate h.P g') :=
      h.toHyp52.isPGroup_S.to_le (h.toHyp52.sec8_conjugate_P_le_S hg'N)
    exact (hW2.of_equiv (subgroupOfEquivOfLe hWN).symm).map _
  obtain ⟨-, p, f, hp, hp2, hf, -, hJ⟩ := Hyp52.Sec8Case.exists_params h.toHyp52 H₁.case8
  obtain ⟨p', f', hp', hp2', hf', hJL⟩ := lieModel_of_isSec8JType hp hp2 hf hJ
  have h8 : 8 ≤ Nat.card (T : Subgroup (h.J ⧸ pPrimeCore 2 h.J)) := hTD ▸ F.eight_le
  have h4 := hC _ p' f' hp' hp2' hf' hJL T h8 _ hR2 hle
  rw [Seven.card_rhoImg hWN hW le_rfl, Seven.card_conjugate] at h4
  have := H₁.eight_le
  omega

end Data

end L81Hyp

end Hyp59

end CFSG.ComponentClassification.GSThmB
