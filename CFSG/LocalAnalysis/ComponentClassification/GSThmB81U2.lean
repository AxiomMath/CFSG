module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81U
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81F8

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

namespace Hyp59

variable {H : Type} [Group H] [Finite H] {h : Hyp59 H}

namespace L81Hyp

variable {H₁ : h.L81Hyp}

namespace Data

variable {d : Data H₁} {v : H} (hv : d.IsV v)
include hv

omit hv in
theorem conj_a_cases (hSy : CFL2Sylow) (hB1 : ConjFixStatement) (hB6 : SylowKernelStatement)
    (hCF23 : CFProp23Fusion) (hCF24 : CFProp24c) (hCFc : CFProp23Center) (hCF1 : CFSec8Simple)
    (hCF2 : CFSec8InnerCentralizer) (hC : CFL2C) (F : d.Facts) {w : H}
    (hw : w ∈ normalizer (h.F32 : Set H)) :
    w⁻¹ * h.a * w = h.a ∨ w⁻¹ * h.a * w = d.z := by
  have haF := d.a_mem_commutator_F hSy hB1 hB6 hCF23 hCF24 hCFc hCF1 hCF2 F
  have hmem : w⁻¹ * h.a * w ∈ ⁅h.F32, h.F32⁆ := by
    have := conj_mem_commutator_of_mem_normalizer (inv_mem hw) haF
    rwa [inv_inv] at this
  have hSS : ⁅h.F32, h.F32⁆ ≤ ⁅h.S, h.S⁆ := commutator_mono h.F32_le_S h.F32_le_S
  have h2 : (w⁻¹ * h.a * w) * (w⁻¹ * h.a * w) = 1 := by
    rw [show w⁻¹ * h.a * w * (w⁻¹ * h.a * w) = w⁻¹ * (h.a * h.a) * w by group,
      Six.a_mul_a_self h.toHyp52]
    group
  have h1 : w⁻¹ * h.a * w ≠ 1 := fun h1 => a_ne_one' (h := h) (by
    calc h.a = w * (w⁻¹ * h.a * w) * w⁻¹ := by group
      _ = 1 := by rw [h1]; group)
  rcases d.inv_SS_cases (hSS hmem) h2 h1 with h3 | h3 | h3
  · exact Or.inl h3
  · exact Or.inr h3
  · exact absurd h3 (d.not_conj_a_az hC F w)

theorem le_S_of_le_U (hRk : CFL2Rank) {E : Subgroup H} (hEU : E ≤ h.U81 v)
    (hE2 : ∀ e ∈ E, e * e = 1) (hE32 : Nat.card E = 32) : E ≤ h.S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  obtain ⟨w, hwE, hwS⟩ := Set.not_subset.mp hne
  obtain ⟨s, hs, hsw⟩ := (mem_U_cases hv (hEU hwE)).resolve_left hwS
  have hwN : w ∈ normalizer (h.S : Set H) := hsw ▸ mul_mem (le_normalizer hs) hv.mem_N
  have hwa : w * h.a * w⁻¹ ≠ h.a := by
    intro h1
    have h2 : w⁻¹ * h.a * w = h.a := by
      calc w⁻¹ * h.a * w = w⁻¹ * (w * h.a * w⁻¹) * w := by rw [h1]
        _ = h.a := by group
    rw [hsw, show (s * v)⁻¹ * h.a * (s * v) = v⁻¹ * (s⁻¹ * h.a * s) * v by group,
      show s⁻¹ * h.a * s = h.a by rw [mul_assoc, ← h.toHyp52.comm_a hs, inv_mul_cancel_left],
      hv.conj_a] at h2
    exact d.z_ne_a h2
  have hPP : h.P ⊓ conjugate h.P w = ⊥ := by
    by_contra hne'
    obtain ⟨x, hx, hx1, hxZ⟩ := Seven.exists_mem_center_of_normal h.toHyp52.isPGroup_S
      (inf_le_left.trans inf_le_left)
      (fun t ht y hy => mem_inf.mpr ⟨h.toHyp52.conj_mem_P' ht (mem_inf.mp hy).1,
        h.toHyp52.sec8_conj_mem_conjugate_P hwN ht (mem_inf.mp hy).2⟩) hne'
    obtain ⟨hxP, hxw⟩ := mem_inf.mp hx
    rw [mem_conjugate_iff] at hxw
    have hxa : x = h.a := by
      have hv' : x ∈ h.P ⊓ centralizer (h.S : Set H) :=
        mem_inf.mpr ⟨hxP, mem_centralizer_iff.mpr fun t ht => hxZ t ht⟩
      rw [H₁.C_eq] at hv'
      exact (mem_zpowers_two h.orderOf_a hv').resolve_left hx1
    have hwxZ : w * x * w⁻¹ ∈ h.P ⊓ centralizer (h.S : Set H) := by
      refine mem_inf.mpr ⟨hxw, mem_centralizer_iff.mpr fun t ht => ?_⟩
      have htw : w⁻¹ * t * w ∈ h.S := by
        have := (mem_normalizer_iff.mp (inv_mem hwN) t).mp ht
        rwa [inv_inv] at this
      have h1 := hxZ _ htw
      calc t * (w * x * w⁻¹) = w * ((w⁻¹ * t * w) * x) * w⁻¹ := by group
        _ = w * (x * (w⁻¹ * t * w)) * w⁻¹ := by rw [h1]
        _ = w * x * w⁻¹ * t := by group
    rw [H₁.C_eq, hxa] at hwxZ
    rcases mem_zpowers_two h.orderOf_a hwxZ with h1 | h1
    · apply a_ne_one' (h := h)
      calc h.a = w⁻¹ * (w * h.a * w⁻¹) * w := by group
        _ = 1 := by rw [h1]; group
    · exact hwa h1
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    Eight.comm_of_mul_self hE2 hx hy
  set E' := E ⊓ h.S with hE'
  have hcw : ∀ x ∈ E', ∀ y ∈ zpowers w, x * y = y * x := by
    intro x hx y hy
    rcases eq_one_or_of_mem_zpowers_of_mul_self (hE2 w hwE) hy with h1 | h1
    · rw [h1, one_mul, mul_one]
    · rw [h1]; exact hEcomm x (mem_inf.mp hx).1 w hwE
  have hdw : E' ⊓ zpowers w = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨hy1, hy2⟩ := mem_inf.mp hy
    rcases eq_one_or_of_mem_zpowers_of_mul_self (hE2 w hwE) hy2 with h1 | h1
    · exact h1
    · exact absurd (h1 ▸ (mem_inf.mp hy1).2) hwS
  have hEle : E ≤ E' ⊔ zpowers w := by
    intro e he
    by_cases heS : e ∈ h.S
    · exact mem_sup_left (mem_inf.mpr ⟨he, heS⟩)
    · obtain ⟨s', hs', hs'e⟩ := (mem_U_cases hv (hEU he)).resolve_left heS
      have h1 : e * w⁻¹ ∈ E' := by
        refine mem_inf.mpr ⟨mul_mem he (inv_mem hwE), ?_⟩
        rw [hs'e, hsw, show s' * v * (s * v)⁻¹ = s' * s⁻¹ by group]
        exact mul_mem hs' (inv_mem hs)
      rw [show e = e * w⁻¹ * w by group]
      exact mul_mem (mem_sup_left h1) (mem_sup_right (mem_zpowers _))
  have hw1 : w ≠ 1 := fun h1 => hwS (h1 ▸ one_mem _)
  have hcw2 : Nat.card (zpowers w) = 2 := by
    rw [Nat.card_zpowers]; exact orderOf_eq_prime (by rw [pow_two]; exact hE2 w hwE) hw1
  have hcard := Seven.card_sup_of_commute hcw hdw
  rw [hcw2] at hcard
  have hc1 := card_le_of_le hEle
  rw [hcard, hE32] at hc1
  have hE'N : E' ≤ normalizer (h.J : Set H) := inf_le_right.trans h.toHyp52.S_le_normalizer
  have h1 := Seven.card_eq_card_rhoImg_mul hE'N
  have hker : E' ⊓ coreActionKernel h.J = ⊥ := by
    rw [eq_bot_iff, ← hPP]
    intro y hy
    obtain ⟨⟨hyE, hyS⟩, hyC⟩ := hy
    refine mem_inf.mpr ⟨mem_inf.mpr ⟨hyS, hyC⟩, ?_⟩
    rw [mem_conjugate_iff, hEcomm w hwE y hyE, mul_inv_cancel_right]
    exact mem_inf.mpr ⟨hyS, hyC⟩
  rw [hker, Subgroup.card_bot, mul_one] at h1
  obtain ⟨p', f', hp', hp2', hf', hJL⟩ := H₁.exists_lieModel_Jbar
  have hE'2 : ∀ x ∈ E', x * x = 1 := fun x hx => hE2 x (mem_inf.mp hx).1
  have h2 := hRk _ p' f' hp' hp2' hf' hJL (Seven.rhoImg h.J E') (rhoImg_mul_self hE'2)
  omega

theorem JeN_U_eq (hRk : CFL2Rank) : Eight.JeN 32 (h.U81 v) = h.F32 := by
  refine le_antisymm (Eight.JeN_le_of fun E hEU hE2 hE32 => ?_) (Eight.JeN_le_of fun E hES hE2
    hE32 => Eight.le_JeN (hES.trans le_sup_left) hE2 hE32)
  exact Eight.le_JeN (le_S_of_le_U hv hRk hEU hE2 hE32) hE2 hE32

theorem inf_normalizer_F_le (hSy : CFL2Sylow) (hB1 : ConjFixStatement)
    (hB6 : SylowKernelStatement) (hCF23 : CFProp23Fusion) (hCF24 : CFProp24c)
    (hCFc : CFProp23Center) (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) (hC : CFL2C)
    (F : d.Facts) {U' : Subgroup H} (hU'2 : IsPGroup 2 U') (hUU' : h.U81 v ≤ U') :
    U' ⊓ normalizer (h.F32 : Set H) ≤ h.U81 v := by
  have hCa : centralizer ({h.a} : Set H) ⊓ U' = h.S := by
    have hSle : h.S ≤ centralizer ({h.a} : Set H) ⊓ U' :=
      le_inf H₁.isSylowIn_S.1 (le_sup_left.trans hUU')
    exact eq_of_sylow_of_le H₁.isSylowIn_S.2 hSle inf_le_left (hU'2.to_le inf_le_right)
  intro w hw
  obtain ⟨hwU, hwN⟩ := mem_inf.mp hw
  rcases conj_a_cases hSy hB1 hB6 hCF23 hCF24 hCFc hCF1 hCF2 hC F hwN with h1 | h1
  · have : w ∈ centralizer ({h.a} : Set H) ⊓ U' := by
      refine mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr ?_, hwU⟩
      calc w * h.a = w * (w⁻¹ * h.a * w) := by rw [h1]
        _ = h.a * w := by group
    rw [hCa] at this
    exact mem_sup_left this
  · have hvU : v ∈ U' := hUU' (mem_sup_right (mem_zpowers _))
    have h2 : w * v⁻¹ ∈ centralizer ({h.a} : Set H) ⊓ U' := by
      refine mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr ?_, mul_mem hwU (inv_mem hvU)⟩
      have h3 : (w * v⁻¹)⁻¹ * h.a * (w * v⁻¹) = h.a := by
        rw [show (w * v⁻¹)⁻¹ * h.a * (w * v⁻¹) = v * (w⁻¹ * h.a * w) * v⁻¹ by group, h1,
          ← hv.conj_a]
        group
      calc w * v⁻¹ * h.a = w * v⁻¹ * ((w * v⁻¹)⁻¹ * h.a * (w * v⁻¹)) := by rw [h3]
        _ = h.a * (w * v⁻¹) := by group
    rw [hCa] at h2
    rw [show w = w * v⁻¹ * v by group]
    exact mul_mem (mem_sup_left h2) (mem_sup_right (mem_zpowers _))

theorem isSylow_U (hRk : CFL2Rank) (hSy : CFL2Sylow) (hB1 : ConjFixStatement)
    (hB6 : SylowKernelStatement) (hCF23 : CFProp23Fusion) (hCF24 : CFProp24c)
    (hCFc : CFProp23Center) (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) (hC : CFL2C)
    (F : d.Facts) : ∃ T : Sylow 2 H, (T : Subgroup H) = h.U81 v := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT⟩ := (isPGroup_U hv).exists_le_sylow
  refine ⟨T, ?_⟩
  by_contra hne
  obtain ⟨t, htT, htU, htN⟩ := Eight.exists_mem_normalizer_not_mem T.isPGroup' hT (Ne.symm hne)
  have htN' : t ∈ normalizer ((h.U81 v : Subgroup H) : Set H) := by
    have : t⁻¹ ∈ normalizer ((h.U81 v : Subgroup H) : Set H) :=
      Eight.mem_normalizer_of_conj_mem fun c hc => by rw [inv_inv]; exact htN c hc
    simpa using inv_mem this
  have htF : t ∈ normalizer (h.F32 : Set H) := by
    have := Eight.normalizer_le_normalizer_JeN 32 (h.U81 v) htN'
    rwa [JeN_U_eq hv hRk] at this
  exact htU (inf_normalizer_F_le hv hSy hB1 hB6 hCF23 hCF24 hCFc hCF1 hCF2 hC F T.isPGroup' hT
    (mem_inf.mpr ⟨htT, htF⟩))

end Data

end L81Hyp

end Hyp59

end CFSG.ComponentClassification.GSThmB
