module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecSwapSym
public import CFSG.LocalAnalysis.OddStandard.AltStdBalCentral
public import CFSG.LocalAnalysis.OddStandard.AltStdBalJ

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup Equiv Equiv.Perm CFSG.OddStandard.AltStdBal
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {Q : Subgroup G} {z : G}

@[expose] def IsSwapOn (e : L ≃* alternatingGroup (Fin n)) (hn : 8 ≤ n) (a : G) : Prop :=
  ∃ ha : a ∈ normalizer (L : Set G), (rho e hn ⟨a, ha⟩).IsSwap

@[expose] def CaseII (e : L ≃* alternatingGroup (Fin n)) (hn : 8 ≤ n) (S : Subgroup G) (z : G) :
    Prop :=
  ∀ a : G, a ∈ Partners z ↔ a ∈ S ∧ IsSwapOn e hn a

theorem shapeTwo_mul_z (d : Cyc L Q z) {u : G} (hu : u ∈ centralizer ({z} : Set G))
    (huL : u ∉ L ⊔ Q) (hu2 : u ^ 2 = 1) :
    u * z ∈ centralizer ({z} : Set G) ∧ u * z ∉ L ⊔ Q ∧ (u * z) ^ 2 = 1 := by
  have hcomm : u * z = z * u := mem_centralizer_singleton_iff.1 hu
  have hz2 : z ^ 2 = 1 := by rw [← d.order]; exact pow_orderOf_eq_one z
  refine ⟨mem_centralizer_singleton_iff.2 ?_, ?_, ?_⟩
  · calc u * z * z = (z * u) * z := by rw [hcomm]
      _ = z * (u * z) := mul_assoc _ _ _
  · intro hmem
    apply huL
    have hzQ : z ∈ L ⊔ Q := mem_sup_right d.mem
    have := mul_mem hmem (inv_mem hzQ)
    simpa [mul_assoc] using this
  · rw [(Commute.mul_pow hcomm 2), hu2, hz2, one_mul]

omit [Finite G] in
theorem mem_sup_zpowers_iff_of_mem_normalizer {u : G} (hu : u ∈ normalizer (L : Set G)) {c : G} :
    c ∈ L ⊔ zpowers u ↔ ∃ l ∈ L, ∃ w ∈ zpowers u, l * w = c := by
  have h := Subgroup.coe_mul_of_right_le_normalizer_left L (zpowers u) (zpowers_le.2 hu)
  have : c ∈ ((L ⊔ zpowers u : Subgroup G) : Set G) ↔
      c ∈ (L : Set G) * (zpowers u : Set G) := by rw [h]
  simpa [Set.mem_mul] using this

theorem eq_zpowers_of_card_eq_two_of_cyc (d : Cyc L Q z) (hQ2 : Nat.card Q = 2) :
    Q = zpowers z := by
  refine le_antisymm (fun q hq => ?_) (zpowers_le.2 d.mem)
  rcases eq_one_or_eq_of_card_eq_two d hQ2 hq with rfl | rfl
  · exact one_mem _
  · exact mem_zpowers _

theorem z_notMem_swapComplement (h : Setting G L n) (d : Cyc L Q z) {u : G}
    (hu : u ∈ centralizer ({z} : Set G)) (huL : u ∉ L ⊔ Q) (hu2 : u ^ 2 = 1) :
    z ∉ L ⊔ zpowers u := by
  obtain ⟨e⟩ := h.iso
  intro hz
  have huN : u ∈ normalizer (L : Set G) := AltStdBal.centralizer_le_normalizer h d hu
  obtain ⟨l, hl, w, hw, hlw⟩ := (mem_sup_zpowers_iff_of_mem_normalizer huN).1 hz
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hw
  have hw' : u ^ k = 1 ∨ u ^ k = u := by
    obtain ⟨j, rfl | rfl⟩ := Int.even_or_odd' k
    · left
      rw [zpow_mul]
      simp [hu2]
    · right
      rw [zpow_add, zpow_mul, zpow_one]
      simp [hu2]
  rcases hw' with hw1 | hwu
  · rw [hw1, mul_one] at hlw
    have hzL : z ∈ L := hlw ▸ hl
    have hz1 := eq_one_of_mem_of_mem_centralizer e (by have := h.hn; omega) hzL (d.le d.mem)
    have := d.order
    rw [hz1, orderOf_one] at this
    omega
  · rw [hwu] at hlw
    apply huL
    have : u = l⁻¹ * z := by rw [← hlw]; group
    rw [this]
    exact mul_mem (inv_mem (mem_sup_left hl)) (mem_sup_right d.mem)

theorem swapComplement_le_normalizer (h : Setting G L n) (d : Cyc L Q z) {u : G}
    (hu : u ∈ centralizer ({z} : Set G)) : L ⊔ zpowers u ≤ normalizer (L : Set G) :=
  sup_le Subgroup.le_normalizer (zpowers_le.2 (AltStdBal.centralizer_le_normalizer h d hu))

theorem zpowers_inf_swapComplement (h : Setting G L n) (d : Cyc L Q z) (hQ2 : Nat.card Q = 2)
    {u : G} (hu : u ∈ centralizer ({z} : Set G)) (huL : u ∉ L ⊔ Q) (hu2 : u ^ 2 = 1) :
    zpowers z ⊓ (L ⊔ zpowers u) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxz, hxS⟩
  have hxQ : x ∈ Q := by rw [eq_zpowers_of_card_eq_two_of_cyc d hQ2]; exact hxz
  rcases eq_one_or_eq_of_card_eq_two d hQ2 hxQ with rfl | rfl
  · exact one_mem _
  · exact absurd hxS (z_notMem_swapComplement h d hu huL hu2)

theorem centralizer_eq_swapComplement (h : Setting G L n) (d : Cyc L Q z) (hQ2 : Nat.card Q = 2)
    {u : G} (hu : u ∈ centralizer ({z} : Set G)) (huL : u ∉ L ⊔ Q) :
    centralizer ({z} : Set G) = zpowers z ⊔ (L ⊔ zpowers u) := by
  have hQz := eq_zpowers_of_card_eq_two_of_cyc d hQ2
  have hLQ : L ⊔ Q ≤ zpowers z ⊔ (L ⊔ zpowers u) := by
    rw [hQz]
    exact sup_le (le_sup_of_le_right le_sup_left) le_sup_left
  apply le_antisymm
  · intro c hc
    rcases mem_sup_or_inv_mul_mem_sup h d hu huL hc with hc1 | hc1
    · exact hLQ hc1
    · have : c = u * (u⁻¹ * c) := by group
      rw [this]
      exact mul_mem (mem_sup_right (mem_sup_right (mem_zpowers u))) (hLQ hc1)
  · exact sup_le (zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl))
      (sup_le (le_centralizer_single h d) (zpowers_le.2 hu))

@[expose] noncomputable def rhoSwap (h : Setting G L n) (d : Cyc L Q z) {u : G}
    (hu : u ∈ centralizer ({z} : Set G)) (e : L ≃* alternatingGroup (Fin n)) :
    (L ⊔ zpowers u : Subgroup G) →* Perm (Fin n) :=
  (rho e h.hn).comp (Subgroup.inclusion (swapComplement_le_normalizer h d hu))

theorem rhoSwap_apply (h : Setting G L n) (d : Cyc L Q z) {u : G}
    (hu : u ∈ centralizer ({z} : Set G)) (e : L ≃* alternatingGroup (Fin n))
    (s : (L ⊔ zpowers u : Subgroup G)) :
    rhoSwap h d hu e s = rho e h.hn ⟨s, swapComplement_le_normalizer h d hu s.2⟩ := rfl

theorem rhoSwap_bijective (h : Setting G L n) (d : Cyc L Q z) (hQ2 : Nat.card Q = 2) {u : G}
    (hu : u ∈ centralizer ({z} : Set G)) (huL : u ∉ L ⊔ Q) (hu2 : u ^ 2 = 1)
    (e : L ≃* alternatingGroup (Fin n)) : Function.Bijective (rhoSwap h d hu e) := by
  have hSN := swapComplement_le_normalizer h d hu
  have hdisj := zpowers_inf_swapComplement h d hQ2 hu huL hu2
  constructor
  · rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro s hs
    rw [MonoidHom.mem_ker, rhoSwap_apply] at hs
    have hK := (rho_eq_one_iff e h.hn ⟨s, hSN s.2⟩).1 hs
    have hC : (s : G) ∈ centralizer ({z} : Set G) :=
      (by rw [centralizer_eq_swapComplement h d hQ2 hu huL]; exact mem_sup_right s.2)
    have hQs : (s : G) ∈ Q := by
      rw [← cent_inf_eq h d]
      exact ⟨hK, hC⟩
    have : (s : G) ∈ zpowers z ⊓ (L ⊔ zpowers u) :=
      ⟨by rw [← eq_zpowers_of_card_eq_two_of_cyc d hQ2]; exact hQs, s.2⟩
    rw [hdisj] at this
    have h1 : (s : G) = 1 := this
    exact Subtype.ext h1
  · intro σ
    have hodd := signHom_eq_neg_one h d e hu huL
    have hodd' : Equiv.Perm.sign (rho e h.hn
        ⟨u, AltStdBal.centralizer_le_normalizer h d hu⟩) = -1 := hodd
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hσ | hσ
    · have hmem : σ ∈ alternatingGroup (Fin n) := mem_alternatingGroup.2 hσ
      let l : L := e.symm ⟨σ, hmem⟩
      refine ⟨⟨l, mem_sup_left l.2⟩, ?_⟩
      rw [rhoSwap_apply]
      have := rho_of_mem e h.hn l (Subgroup.le_normalizer l.2)
      rw [this]
      simp [l]
    · have hmem : σ * (rho e h.hn ⟨u, AltStdBal.centralizer_le_normalizer h d hu⟩)⁻¹ ∈
          alternatingGroup (Fin n) := by
        rw [mem_alternatingGroup, map_mul, map_inv, hσ, hodd']
        decide
      let l : L := e.symm ⟨σ * (rho e h.hn ⟨u, AltStdBal.centralizer_le_normalizer h d hu⟩)⁻¹,
        hmem⟩
      have hlN : (l : G) ∈ normalizer (L : Set G) := Subgroup.le_normalizer l.2
      have hρl : rho e h.hn ⟨l, hlN⟩ =
          σ * (rho e h.hn ⟨u, AltStdBal.centralizer_le_normalizer h d hu⟩)⁻¹ := by
        rw [rho_of_mem e h.hn l hlN]
        simp [l]
      refine ⟨⟨(l : G) * u, mul_mem (mem_sup_left l.2) (mem_sup_right (mem_zpowers u))⟩, ?_⟩
      rw [rhoSwap_apply]
      have : (⟨(l : G) * u, hSN (mul_mem (mem_sup_left l.2) (mem_sup_right (mem_zpowers u)))⟩ :
          normalizer (L : Set G)) =
          ⟨l, hlN⟩ * ⟨u, AltStdBal.centralizer_le_normalizer h d hu⟩ := rfl
      rw [this, map_mul, hρl, inv_mul_cancel_right]

theorem swapData_of_caseII (h : Setting G L n) (d : Cyc L Q z) (hQ2 : Nat.card Q = 2) {u : G}
    (hu : u ∈ centralizer ({z} : Set G)) (huL : u ∉ L ⊔ Q) (hu2 : u ^ 2 = 1)
    (e : L ≃* alternatingGroup (Fin n)) (hII : CaseII e h.hn (L ⊔ zpowers u) z) :
    Nonempty (SwapData z n) := by
  have hbij := rhoSwap_bijective h d hQ2 hu huL hu2 e
  have hSN := swapComplement_le_normalizer h d hu
  let ι : Perm (Fin n) ≃* (L ⊔ zpowers u : Subgroup G) :=
    (MulEquiv.ofBijective (rhoSwap h d hu e) hbij).symm
  have key : ∀ (x : (L ⊔ zpowers u : Subgroup G)) (τ : Perm (Fin n)),
      ι τ = x ↔ τ = rhoSwap h d hu e x := fun x τ => MulEquiv.symm_apply_eq _
  refine ⟨⟨L ⊔ zpowers u, ι, centralizer_eq_swapComplement h d hQ2 hu huL,
    zpowers_inf_swapComplement h d hQ2 hu huL hu2, ?_⟩⟩
  ext a
  rw [hII a]
  constructor
  · rintro ⟨haS, haN, hsw⟩
    refine ⟨rhoSwap h d hu e ⟨a, haS⟩, ?_, ?_⟩
    · rw [rhoSwap_apply]
      exact hsw
    · exact congrArg Subtype.val ((key ⟨a, haS⟩ _).2 rfl).symm
  · rintro ⟨τ, hτ, rfl⟩
    refine ⟨(ι τ).2, hSN (ι τ).2, ?_⟩
    have := (key (ι τ) τ).1 rfl
    rw [rhoSwap_apply] at this
    rw [← this]
    exact hτ

theorem false_of_caseII (h : Setting G L n) (d : Cyc L Q z) (hQ2 : Nat.card Q = 2) {u : G}
    (hu : u ∈ centralizer ({z} : Set G)) (huL : u ∉ L ⊔ Q) (hu2 : u ^ 2 = 1)
    (e : L ≃* alternatingGroup (Fin n)) (hII : CaseII e h.hn (L ⊔ zpowers u) z) : False := by
  obtain ⟨D⟩ := swapData_of_caseII h d hQ2 hu huL hu2 e hII
  have := h.std.simple
  exact false_of_swapData h.std.nonab h.hn d.order D

theorem false_of_caseII_or (h : Setting G L n) (d : Cyc L Q z) (hQ2 : Nat.card Q = 2) {u : G}
    (hu : u ∈ centralizer ({z} : Set G)) (huL : u ∉ L ⊔ Q) (hu2 : u ^ 2 = 1)
    (e : L ≃* alternatingGroup (Fin n))
    (hII : CaseII e h.hn (L ⊔ zpowers u) z ∨ CaseII e h.hn (L ⊔ zpowers (u * z)) z) : False := by
  rcases hII with h1 | h1
  · exact false_of_caseII h d hQ2 hu huL hu2 e h1
  · obtain ⟨hu', huL', hu2'⟩ := shapeTwo_mul_z d hu huL hu2
    exact false_of_caseII h d hQ2 hu' huL' hu2' e h1

end CFSG.OddStandard.AltStdSec
