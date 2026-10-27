module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43Frame
public import Certificates.Certificate27601
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC3UExtBase

public section

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.PairNative CFSG.LieType.Multipliers.U43 CFSG.EvenSporadicStandard.Fin76b
  CFSG.EvenSporadicStandard.M24Std.CU43 CFSG.Sporadic.SmallOddCore

section Data

theorem rho_mul_self : rhoPerm * rhoPerm = 1 := by
  have h := Certificates.certificate27601.1
  simp only [rhoCheck, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨-, hsq⟩, -⟩, -⟩, -⟩ := h
  exact (eqA_iff (rep_compA rep_rhoArr rep_rhoArr) rep_idA).1 hsq

theorem rho_mem_coset : ∃ g ∈ P, rhoPerm = g * tP 5 := by
  have h := Certificates.certificate27601.1
  simp only [rhoCheck, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨-, -⟩, h5⟩, -⟩, -⟩ := h
  have := (inP_iff (rep_compA rep_rhoArr (rep_tArr_inv (by norm_num : 5 < 8)))).1 h5
  exact ⟨_, this, by group⟩

theorem phi_conj_seven : ∃ g ∈ P, fP * tP 7 * fP⁻¹ = g * tP 5 := by
  have h := Certificates.certificate27601.1
  simp only [rhoCheck, Bool.and_eq_true] at h
  obtain ⟨-, h75⟩ := h
  have := (inP_iff (rep_compA rep_fP (rep_compA (rep_tArr 7) (rep_compA rep_fP_inv
    (rep_tArr_inv (by norm_num : 5 < 8)))))).1 h75
  exact ⟨_, this, by group⟩

theorem order6_data : ∃ w ∈ P, w * rP 8 = rP 8 * w ∧ orderOf w = 6 := by
  have h := Certificates.certificate27601.2
  simp only [order6Check, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨hinv, hP⟩, hcomm⟩, h6⟩, h2⟩, h3⟩ := h
  have hrep := (rep_permOfArr hinv).1
  have hr8 : Rep 820 reps[8]! (rP 8) := rep_rP (by norm_num : 8 < 9)
  refine ⟨permOfArr 820 order6W, (inP_iff hrep).1 hP, ?_, ?_⟩
  · exact (eqA_iff (rep_compA hrep hr8) (rep_compA hr8 hrep)).1 hcomm
  · have e6 : permOfArr 820 order6W ^ 6 = 1 :=
      (eqA_iff (rep_powA hrep 6) rep_idA).1 h6
    have e2 : permOfArr 820 order6W ^ 2 ≠ 1 := fun h' =>
      absurd ((eqA_iff (rep_powA hrep 2) rep_idA).2 h') (by simp [h2])
    have e3 : permOfArr 820 order6W ^ 3 ≠ 1 := fun h' =>
      absurd ((eqA_iff (rep_powA hrep 3) rep_idA).2 h') (by simp [h3])
    have hd : orderOf (permOfArr 820 order6W) ∣ 6 := orderOf_dvd_of_pow_eq_one e6
    have hn2 : ¬ orderOf (permOfArr 820 order6W) ∣ 2 := fun hh =>
      e2 (orderOf_dvd_iff_pow_eq_one.1 hh)
    have hn3 : ¬ orderOf (permOfArr 820 order6W) ∣ 3 := fun hh =>
      e3 (orderOf_dvd_iff_pow_eq_one.1 hh)
    have hle : orderOf (permOfArr 820 order6W) ≤ 6 := Nat.le_of_dvd (by norm_num) hd
    generalize orderOf (permOfArr 820 order6W) = m at hd hn2 hn3 hle
    interval_cases m <;> simp_all <;> omega

end Data

section Cover

theorem cent_of_coset {β : Equiv.Perm (Fin 820)} (hβ : β ∈ R) (hβ2 : β * β = 1)
    {g : Equiv.Perm (Fin 820)} (hg : g ∈ P) {k : ℕ} (hk : k < 8) (hk0 : k ≠ 0)
    (hβg : β = g * tP k) :
    ∃ j, j < 9 ∧ repCoset[j]! = k ∧
      Nat.card ↥(P ⊓ centralizer ({β} : Set (Equiv.Perm (Fin 820)))) = repCent[j]! := by
  have hβ1 : β ≠ 1 := by
    intro h
    apply hk0
    have : tP k ∈ P := by
      have e : tP k = g⁻¹ * β := by rw [hβg]; group
      rw [e, h, mul_one]
      exact P.inv_mem hg
    exact (tP_mem_P_iff hk).1 this
  obtain ⟨j, hj, ⟨c, hc, hcj⟩, g₁, hg₁, hβ₁⟩ := involution_data hβ hβ2 hβ1
  have hak := repCoset_lt hj
  have hkk : repCoset[j]! = k := by
    by_contra hne
    apply tP_mul_inv_not_mem hak hk hne
    have e : tP repCoset[j]! * (tP k)⁻¹ = g₁⁻¹ * g := by
      have e1 : tP repCoset[j]! = g₁⁻¹ * β := by rw [hβ₁]; group
      rw [e1, hβg]
      group
    rw [e]
    exact P.mul_mem (P.inv_mem hg₁) hg
  refine ⟨j, hj, hkk, ?_⟩
  rw [hcj, card_inf_centralizer_conj hc, card_inf_centralizer_rP hj]

theorem exists_conj_rho {β : Equiv.Perm (Fin 820)} (hβ2 : β * β = 1) {g : Equiv.Perm (Fin 820)}
    (hg : g ∈ P) (hβg : β = g * tP 5) : ∃ c ∈ P, β = c * rhoPerm * c⁻¹ := by
  obtain ⟨g', hg', hρ⟩ := rho_mem_coset
  have hρR : rhoPerm ∈ R := mem_R_iff.2 ⟨g', hg', 5, by norm_num, hρ⟩
  have hβR : β ∈ R := mem_R_iff.2 ⟨g, hg, 5, by norm_num, hβg⟩
  have h5P : tP 5 ∉ P := fun h => absurd ((tP_mem_P_iff (by norm_num)).1 h) (by norm_num)
  have hρP : rhoPerm ∉ P := fun h => h5P (by
    have e : tP 5 = g'⁻¹ * rhoPerm := by rw [hρ]; group
    rw [e]
    exact P.mul_mem (P.inv_mem hg') h)
  have hcent : ∀ {γ : Equiv.Perm (Fin 820)}, γ ∈ R → γ * γ = 1 → ∀ {h : Equiv.Perm (Fin 820)},
      h ∈ P → γ = h * tP 5 →
        Nat.card ↥(P ⊓ centralizer ({γ} : Set (Equiv.Perm (Fin 820)))) = 720 := by
    intro γ hγR hγ2 h hh hγ
    obtain ⟨j, hj, hjk, hc⟩ := cent_of_coset hγR hγ2 hh (by norm_num) (by norm_num) hγ
    have : j = 5 := by
      revert hjk
      interval_cases j <;> simp [repCoset]
    subst this
    rw [hc]
    decide
  have hcos : β * rhoPerm⁻¹ ∈ P := by
    have e : β * rhoPerm⁻¹ = g * g'⁻¹ := by rw [hβg, hρ]; group
    rw [e]
    exact P.mul_mem hg (P.inv_mem hg')
  exact same_coset_conj hρR hρP rho_mul_self hβR hβ2 hcos (hcent hρR rho_mul_self hg' hρ)
    (hcent hβR hβ2 hg hβg)

theorem class_cases {zh : Equiv.Perm (Fin 820)} (hR : zh ∈ R) (hP : zh ∉ P) (h2 : zh * zh = 1)
    (h720 : Nat.card ↥(P ⊓ centralizer ({zh} : Set (Equiv.Perm (Fin 820)))) = 720) :
    (∃ r ∈ R, zh = r * rhoPerm * r⁻¹) ∨ (∃ c ∈ P, zh = c * rP 8 * c⁻¹) := by
  have hne : zh ≠ 1 := fun h => hP (h ▸ P.one_mem)
  obtain ⟨j, hj, ⟨c, hc, hcj⟩, g, hg, hgz⟩ := involution_data hR h2 hne
  have hrc : repCent[j]! = 720 := by
    rw [hcj, card_inf_centralizer_conj hc, card_inf_centralizer_rP hj] at h720
    exact h720
  have hj' : j = 4 ∨ j = 5 ∨ j = 8 := by
    revert hrc
    interval_cases j <;> simp [repCent]
  rcases hj' with rfl | rfl | rfl
  · left
    have hg7 : zh = g * tP 7 := by simpa [repCoset] using hgz
    obtain ⟨g₇, hg₇, hφ⟩ := phi_conj_seven
    have hfR : fP ∈ R := by
      have := tP_mem_R (k := 4) (by norm_num)
      rwa [tP_four] at this
    have hz' : fP * zh * fP⁻¹ = (fP * g * fP⁻¹ * g₇) * tP 5 := by
      calc fP * zh * fP⁻¹ = (fP * g * fP⁻¹) * (fP * tP 7 * fP⁻¹) := by rw [hg7]; group
        _ = (fP * g * fP⁻¹) * (g₇ * tP 5) := by rw [hφ]
        _ = (fP * g * fP⁻¹ * g₇) * tP 5 := by group
    have hgm : fP * g * fP⁻¹ ∈ P := conj_mem_P hfR hg
    have h2' : (fP * zh * fP⁻¹) * (fP * zh * fP⁻¹) = 1 := by
      calc (fP * zh * fP⁻¹) * (fP * zh * fP⁻¹) = fP * (zh * zh) * fP⁻¹ := by group
        _ = 1 := by rw [h2]; group
    obtain ⟨c', hc', hcc⟩ := exists_conj_rho h2' (P.mul_mem hgm hg₇) hz'
    refine ⟨fP⁻¹ * c', R.mul_mem (R.inv_mem hfR) (P_le_R hc'), ?_⟩
    calc zh = fP⁻¹ * (fP * zh * fP⁻¹) * fP := by group
      _ = fP⁻¹ * (c' * rhoPerm * c'⁻¹) * fP := by rw [hcc]
      _ = (fP⁻¹ * c') * rhoPerm * (fP⁻¹ * c')⁻¹ := by group
  · left
    have hg5 : zh = g * tP 5 := by simpa [repCoset] using hgz
    obtain ⟨c', hc', hcc⟩ := exists_conj_rho h2 hg hg5
    exact ⟨c', P_le_R hc', hcc⟩
  · right
    exact ⟨c, hc, hcj⟩

theorem u43_identification {K : Type} [Group K] [Finite K] (E : Subgroup K) [E.Normal]
    (θ : E ≃* ↥P) (hC : centralizer (E : Set K) = ⊥) {ζ : K} (hζ : ζ * ζ = 1)
    (hdvd : Nat.card ↥(centralizer ({ζ} : Set K)) ∣ 4320)
    (h6 : ∀ g ∈ E, g * ζ = ζ * g → orderOf g ≠ 6) :
    E.index = 2 ∧ Nonempty (K ≃* ↥U43Ext) := by
  have hnot := frame_not_mem E θ hC hζ hdvd
  have h720 := frame_card E θ hC hζ hdvd
  have hidx := frame_index E θ hC hζ hdvd
  refine ⟨hidx, ?_⟩
  have hz2 : emb E θ ζ * emb E θ ζ = 1 := emb_mul_self E θ hζ
  have hzR : emb E θ ζ ∈ R := emb_mem E θ ζ
  have hzP : emb E θ ζ ∉ P := fun h => hnot ((emb_mem_P_iff E θ hC).1 h)
  have hcent : Nat.card ↥(P ⊓ centralizer ({emb E θ ζ} : Set (Equiv.Perm (Fin 820)))) = 720 := by
    rw [← card_inf_centralizer_emb E θ hC]
    exact h720
  rcases class_cases hzR hzP hz2 hcent with ⟨r, hr, hrz⟩ | ⟨c, hc, hcz⟩
  ·
    have hPle : ∀ p ∈ P, r⁻¹ * p * r ∈ U43Ext := by
      intro p hp
      have h1 : r⁻¹ * p * r ∈ P := by
        have := conj_mem_P (R.inv_mem hr) hp
        simpa using this
      rw [P_eq_range] at h1
      obtain ⟨x, hx⟩ := h1
      rw [← hx]
      exact subset_closure (Or.inl ⟨x, rfl⟩)
    have hrange : (emb E θ).range = U43Ext.map (MulAut.conj r).toMonoidHom := by
      apply le_antisymm
      · rintro _ ⟨k, rfl⟩
        by_cases hk : k ∈ E
        · refine ⟨r⁻¹ * emb E θ k * r, hPle _ ((emb_mem_P_iff E θ hC).2 hk), ?_⟩
          show r * (r⁻¹ * emb E θ k * r) * r⁻¹ = emb E θ k
          group
        · have hkz : k * ζ ∈ E := by
            refine (Subgroup.mul_mem_iff_of_index_two hidx).2 ?_
            exact ⟨fun h => absurd h hk, fun h => absurd h hnot⟩
          have hkzP : emb E θ (k * ζ) ∈ P := (emb_mem_P_iff E θ hC).2 hkz
          refine ⟨(r⁻¹ * emb E θ (k * ζ) * r) * rhoPerm,
            mul_mem (hPle _ hkzP) (subset_closure (Or.inr rfl)), ?_⟩
          have hk' : k = (k * ζ) * ζ := by
            have : ζ * ζ = 1 := hζ
            calc k = k * (ζ * ζ) := by rw [this, mul_one]
              _ = (k * ζ) * ζ := by group
          show r * ((r⁻¹ * emb E θ (k * ζ) * r) * rhoPerm) * r⁻¹ = emb E θ k
          calc r * ((r⁻¹ * emb E θ (k * ζ) * r) * rhoPerm) * r⁻¹
              = emb E θ (k * ζ) * (r * rhoPerm * r⁻¹) := by group
            _ = emb E θ (k * ζ) * emb E θ ζ := by rw [hrz]
            _ = emb E θ k := by rw [← map_mul, ← hk']
      · rw [Subgroup.map_le_iff_le_comap]
        unfold U43Ext
        rw [Subgroup.closure_le]
        rintro _ (⟨x, rfl⟩ | rfl)
        · have hp : r * psi x * r⁻¹ ∈ P := by
            refine conj_mem_P hr ?_
            rw [P_eq_range]
            exact ⟨x, rfl⟩
          obtain ⟨c, -, hc⟩ := exists_emb_eq E θ hp
          exact ⟨c, hc⟩
        · exact ⟨ζ, by rw [hrz]; rfl⟩
    exact ⟨(MonoidHom.ofInjective (emb_injective E θ hC)).trans
      ((MulEquiv.subgroupCongr hrange).trans
        (U43Ext.equivMapOfInjective (MulAut.conj r).toMonoidHom (MulAut.conj r).injective).symm)⟩
  ·
    exfalso
    obtain ⟨w, hwP, hwc, hw6⟩ := order6_data
    have hcwP : c * w * c⁻¹ ∈ P := P.mul_mem (P.mul_mem hc hwP) (P.inv_mem hc)
    obtain ⟨g₀, hg₀E, hg₀⟩ := exists_emb_eq E θ hcwP
    refine h6 g₀ hg₀E ?_ ?_
    · apply emb_injective E θ hC
      rw [map_mul, map_mul, hg₀, hcz]
      calc c * w * c⁻¹ * (c * rP 8 * c⁻¹) = c * (w * rP 8) * c⁻¹ := by group
        _ = c * (rP 8 * w) * c⁻¹ := by rw [hwc]
        _ = c * rP 8 * c⁻¹ * (c * w * c⁻¹) := by group
    · rw [← orderOf_injective (emb E θ) (emb_injective E θ hC) g₀, hg₀]
      have := MulEquiv.orderOf_eq (MulAut.conj c) w
      rw [MulAut.conj_apply] at this
      rw [this, hw6]

end Cover

end CFSG.ComponentClassification.CatFC
