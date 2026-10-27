module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62zDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62zH1Basic
import CFSG.HardMathSupport.Solomon.Coordinator.I18_3Family
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7ToolsA
import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma52

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.UniquenessMaximal
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {f : ℕ} {X Q : Subgroup G}

omit [Finite G] in
theorem k631m_conj_mem {H : Subgroup G} {g h : G} (hg : g ∈ normalizer (H : Set G)) (hh : h ∈ H) :
    g * h * g⁻¹ ∈ H :=
  (mem_normalizer_iff.mp hg h).mp hh

theorem k631m_two_dvd_card_of_perfect {J : Subgroup G} (hJ : ⁅J, J⁆ = J) (hJ1 : J ≠ ⊥) :
    2 ∣ Nat.card J := by
  by_contra h
  have hodd : Odd (Nat.card J) := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h)
  have hsolv : Group.IsSolvable J := CFSG.Milestones.odd_order_solvable hodd
  have : Group.IsPerfect J := Subgroup.isPerfect_iff.2 hJ
  have : Nontrivial J := (Subgroup.nontrivial_iff_ne_bot J).2 hJ1
  exact Group.IsPerfect.not_isSolvable J hsolv

omit [Finite G] in
theorem k631m_commutator_le_triv {O J W A : Subgroup G} (hWO : W ≤ normalizer (O : Set G))
    (hWJ : W ≤ normalizer (J : Set G)) (hA : A ≤ k631Triv O J) : ⁅W, A⁆ ≤ k631Triv O J := by
  rw [Subgroup.commutator_le]
  intro w hw a ha
  have haT := hA ha
  have hwa : w * a * w⁻¹ ∈ k631Triv O J := by
    obtain ⟨haO, haJ, ha'⟩ := haT
    refine ⟨?_, ?_, ?_⟩
    · exact mul_mem (mul_mem (hWO hw) haO) (inv_mem (hWO hw))
    · exact mul_mem (mul_mem (hWJ hw) haJ) (inv_mem (hWJ hw))
    · intro j hj
      have hj' : w⁻¹ * j * w ∈ J := by
        have := k631m_conj_mem (inv_mem (hWJ hw)) hj
        simpa using this
      have h1 := ha' _ hj'
      have e : ⁅w * a * w⁻¹, j⁆ = w * ⁅a, w⁻¹ * j * w⁆ * w⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact k631m_conj_mem (hWO hw) h1
  have e : ⁅w, a⁆ = (w * a * w⁻¹) * a⁻¹ := by simp only [commutatorElement_def]
  rw [e]
  exact mul_mem hwa (inv_mem haT)

theorem k631m_ne_bot {J : Subgroup G} (hJ : GLAPComponent f X J) : J ≠ ⊥ :=
  CFSG.HardMathSupport.Solomon.LocalBalance.glaPComponent_ne_bot hJ

theorem k631m_involution_centralized (hL : LayerHyp f X Q) {J : Subgroup G}
    (hJ : GLAPComponent f X J) {A : Subgroup G} (hAQ : A ≤ Q)
    (hA : A ≤ k631Triv (GLAPPrimeCoreOf f X) J) :
    ∃ t ∈ J, t ^ 2 = 1 ∧ t ≠ 1 ∧ ∀ a ∈ A, a * t = t * a := by
  have hf := hL.prime
  have : Fact f.Prime := ⟨hf⟩
  set O := GLAPPrimeCoreOf f X with hO
  have hOodd : Odd (Nat.card O) := hL.odd
  have hOf : ¬ f ∣ Nat.card O := not_dvd_card_glaPPrimeCoreOf hf X
  have hJX : J ≤ X := hJ.1
  have hXN : X ≤ normalizer (O : Set G) := le_normalizer_glaPPrimeCoreOf f X
  have h2 : 2 ∣ Nat.card J :=
    k631m_two_dvd_card_of_perfect (glaPComponent_perfect hJ) (k631m_ne_bot hJ)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := J) 2 h2
  have hxJ : (x : G) ∈ J := x.2
  have hxo : orderOf (x : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hx
  have hx2 : (x : G) ^ 2 = 1 := by rw [← hxo]; exact pow_orderOf_eq_one _
  have hxinv : (x : G)⁻¹ = x := by
    rw [inv_eq_iff_mul_eq_one, ← pow_two]; exact hx2
  have hAf : IsPGroup f A := hL.pgroup.to_le hAQ
  have hnorm : ∀ b ∈ A, ∀ y ∈ O ⊓ J, b * y * b⁻¹ ∈ O ⊓ J := fun b hb y hy =>
    ⟨k631m_conj_mem (hA hb).1 hy.1, k631m_conj_mem (hA hb).2.1 hy.2⟩
  have hcard : ¬ f ∣ Nat.card ↥(O ⊓ J) := fun h =>
    hOf (h.trans (Subgroup.card_dvd_of_le inf_le_left))
  have hcoset : ∀ b ∈ A, (x : G)⁻¹ * (b * x * b⁻¹) ∈ O ⊓ J := by
    intro b hb
    have hxJ' : (x : G)⁻¹ ∈ J := J.inv_mem hxJ
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have h1 := O.inv_mem ((hA hb).2.2 (x : G)⁻¹ hxJ')
      have e : (x : G)⁻¹ * (b * x * b⁻¹) = ⁅b, (x : G)⁻¹⁆⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [e]; exact h1
    · exact J.mul_mem hxJ' (k631m_conj_mem (hA hb).2.1 hxJ)
  obtain ⟨y, hy, hfix⟩ := exists_mul_mem_fixed_of_coset hAf hnorm hcard hcoset
  set c : G := x * y with hc
  have hcJ : c ∈ J := mul_mem hxJ hy.2
  have hcomm : ∀ a ∈ A, a * c = c * a := fun a ha => by
    have := hfix a ha
    calc a * c = (a * c * a⁻¹) * a := by group
      _ = c * a := by rw [hc, this]
  have hc2 : c ^ 2 ∈ O := by
    have e : c ^ 2 = ((x : G) * y * (x : G)⁻¹) * y := by
      rw [hc, pow_two, hxinv]
      group
    rw [e]
    exact mul_mem (k631m_conj_mem (hXN (hJX hxJ)) hy.1) hy.1
  have hkeven : 2 ∣ orderOf c := by
    by_contra hodd
    obtain ⟨m, hm⟩ : Odd (orderOf c) := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hodd)
    have hcO : c ∈ O := by
      have e : c = (c ^ 2) ^ (m + 1) := by
        rw [← pow_mul, show 2 * (m + 1) = orderOf c + 1 by omega, pow_succ, pow_orderOf_eq_one,
          one_mul]
      rw [e]; exact pow_mem hc2 _
    have hxO : (x : G) ∈ O := by
      have e : (x : G) = c * y⁻¹ := by rw [hc]; group
      rw [e]; exact mul_mem hcO (inv_mem hy.1)
    have h2dvd : orderOf (x : G) ∣ Nat.card O := Subgroup.orderOf_dvd_natCard O hxO
    rw [hxo] at h2dvd
    exact (Nat.not_even_iff_odd.mpr hOodd) (even_iff_two_dvd.mpr h2dvd)
  obtain ⟨m, hm⟩ := hkeven
  have hmpos : 0 < m := by have := orderOf_pos c; omega
  refine ⟨c ^ m, pow_mem hcJ m, ?_, ?_, fun a ha => ?_⟩
  · rw [← pow_mul, mul_comm, ← hm]; exact pow_orderOf_eq_one c
  · exact pow_ne_one_of_lt_orderOf hmpos.ne' (by omega)
  · exact (Commute.pow_right (show Commute a c from hcomm a ha) m).eq

theorem k631m_lift {p : ℕ} [Fact p.Prime] {O J W : Subgroup G} (hW : IsPGroup p W)
    (hWT : W ≤ k631Triv O J) (hO : ¬ p ∣ Nat.card O) :
    ∀ j ∈ J, ∃ c ∈ J ⊓ centralizer (W : Set G), c⁻¹ * j ∈ O ⊓ J := by
  intro j hj
  have hnorm : ∀ b ∈ W, ∀ y ∈ O ⊓ J, b * y * b⁻¹ ∈ O ⊓ J := fun b hb y hy =>
    Subgroup.mem_inf.mpr ⟨k631m_conj_mem (hWT hb).1 (Subgroup.mem_inf.mp hy).1,
      k631m_conj_mem (hWT hb).2.1 (Subgroup.mem_inf.mp hy).2⟩
  have hcard : ¬ p ∣ Nat.card ↥(O ⊓ J) := fun h =>
    hO (h.trans (Subgroup.card_dvd_of_le inf_le_left))
  have hcoset : ∀ b ∈ W, j⁻¹ * (b * j * b⁻¹) ∈ O ⊓ J := by
    intro b hb
    have hj' : j⁻¹ ∈ J := J.inv_mem hj
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have h1 := O.inv_mem ((hWT hb).2.2 j⁻¹ hj')
      have e : j⁻¹ * (b * j * b⁻¹) = ⁅b, j⁻¹⁆⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [e]; exact h1
    · exact J.mul_mem hj' (k631m_conj_mem (hWT hb).2.1 hj)
  obtain ⟨y, hy, hfix⟩ := exists_mul_mem_fixed_of_coset hW hnorm hcard hcoset
  refine ⟨j * y, Subgroup.mem_inf.mpr ⟨J.mul_mem hj (Subgroup.mem_inf.mp hy).2, ?_⟩, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have h := hfix b hb
    calc b * (j * y) = (b * (j * y) * b⁻¹) * b := by group
      _ = (j * y) * b := by rw [h]
  · have e : (j * y)⁻¹ * j = y⁻¹ := by group
    rw [e]
    exact (O ⊓ J).inv_mem hy

theorem k631m_relIndex_dvd {J C K : Subgroup G} (hCJ : C ≤ J) (hKJ : K ≤ J)
    (hKn : J ≤ normalizer (K : Set G)) (hJ : ∀ j ∈ J, ∃ c ∈ C, c⁻¹ * j ∈ K) :
    C.relIndex J ∣ Nat.card K := by
  have : (K.subgroupOf J).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKJ).2 hKn
  have hsup : C.subgroupOf J ⊔ K.subgroupOf J = ⊤ := by
    rw [eq_top_iff]
    intro j _
    obtain ⟨c, hc, hck⟩ := hJ (j : G) j.2
    have hc' : (⟨c, hCJ hc⟩ : J) ∈ C.subgroupOf J := hc
    have hk' : (⟨c⁻¹ * j, J.mul_mem (J.inv_mem (hCJ hc)) j.2⟩ : J) ∈ K.subgroupOf J := hck
    have e : j = (⟨c, hCJ hc⟩ : J) * ⟨c⁻¹ * j, J.mul_mem (J.inv_mem (hCJ hc)) j.2⟩ :=
      Subtype.ext (by simp)
    rw [e]
    exact Subgroup.mul_mem_sup hc' hk'
  have hr : (K.subgroupOf J).relIndex (C.subgroupOf J ⊔ K.subgroupOf J) =
      (K.subgroupOf J).relIndex (C.subgroupOf J) := Subgroup.relIndex_sup_right _ _
  rw [hsup, Subgroup.relIndex_top_right] at hr
  have h1 : (K.subgroupOf J).index * Nat.card (K.subgroupOf J) = Nat.card J :=
    Subgroup.index_mul_card _
  have h2 : Nat.card ((K.subgroupOf J).subgroupOf (C.subgroupOf J)) *
      (K.subgroupOf J).relIndex (C.subgroupOf J) = Nat.card (C.subgroupOf J) :=
    Subgroup.card_mul_index _
  have h3 : (C.subgroupOf J).index * Nat.card (C.subgroupOf J) = Nat.card J :=
    Subgroup.index_mul_card _
  have hrpos : 0 < (K.subgroupOf J).index :=
    Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have key : (C.subgroupOf J).index * Nat.card ((K.subgroupOf J).subgroupOf (C.subgroupOf J)) =
      Nat.card (K.subgroupOf J) := by
    apply Nat.eq_of_mul_eq_mul_right hrpos
    calc (C.subgroupOf J).index * Nat.card ((K.subgroupOf J).subgroupOf (C.subgroupOf J)) *
          (K.subgroupOf J).index
        = (C.subgroupOf J).index * (Nat.card ((K.subgroupOf J).subgroupOf (C.subgroupOf J)) *
          (K.subgroupOf J).relIndex (C.subgroupOf J)) := by rw [hr]; ring
      _ = (C.subgroupOf J).index * Nat.card (C.subgroupOf J) := by rw [h2]
      _ = Nat.card J := h3
      _ = Nat.card (K.subgroupOf J) * (K.subgroupOf J).index := by rw [← h1, mul_comm]
  have hcardK : Nat.card (K.subgroupOf J) = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKJ).toEquiv
  rw [← hcardK]
  exact Dvd.intro _ key

theorem k631m_centralizing_sylow (hL : LayerHyp f X Q) {J : Subgroup G}
    (hJ : GLAPComponent f X J) {W A : Subgroup G} (hW : IsPGroup 2 W) (hWL : W ≤ GLAPLayer f X)
    (hAQ : A ≤ Q) (hA : A ≤ k631Triv (GLAPPrimeCoreOf f X) J)
    (hAW : A ≤ normalizer (W : Set G)) (hWA : ⁅W, A⁆ = W) :
    ∃ D : Subgroup G, D ≤ J ⊓ centralizer (W : Set G) ∧ IsPGroup f D ∧
      ¬ f ∣ (D.subgroupOf J).index ∧ ∀ a ∈ A, ∀ d ∈ D, a * d = d * a := by
  have hf := hL.prime
  have : Fact f.Prime := ⟨hf⟩
  set O := GLAPPrimeCoreOf f X with hO
  have hOodd : Odd (Nat.card O) := hL.odd
  have hOf : ¬ f ∣ Nat.card O := not_dvd_card_glaPPrimeCoreOf hf X
  have hOcop : Nat.Coprime f (Nat.card O) := (Nat.Prime.coprime_iff_not_dvd hf).2 hOf
  have hO2 : ¬ 2 ∣ Nat.card O := fun h =>
    (Nat.not_even_iff_odd.mpr hOodd) (even_iff_two_dvd.mpr h)
  have hAf : IsPGroup f A := hL.pgroup.to_le hAQ
  have hJX : J ≤ X := hJ.1
  have hXN : X ≤ normalizer (O : Set G) := le_normalizer_glaPPrimeCoreOf f X
  have hWX : W ≤ X := hWL.trans (i183_glaPLayer_le f X)
  have hWJ : W ≤ normalizer (J : Set G) := hWL.trans (i183_glaPLayer_le_normalizer hf hJ)
  have hWT : W ≤ k631Triv O J := by
    have := k631m_commutator_le_triv (hWX.trans hXN) hWJ hA
    rwa [hWA] at this
  have hlift := k631m_lift (p := 2) hW hWT hO2
  set C : Subgroup G := J ⊓ centralizer (W : Set G) with hC
  have hCJ : C ≤ J := inf_le_left
  have hCnorm : ∀ a ∈ A, ∀ c ∈ C, a * c * a⁻¹ ∈ C := by
    intro a ha c hc
    refine Subgroup.mem_inf.mpr ⟨k631m_conj_mem (hA ha).2.1 (Subgroup.mem_inf.mp hc).1, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hw' : a⁻¹ * w * a ∈ W := by
      have := k631m_conj_mem (hAW (A.inv_mem ha)) hw
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc).2 _ hw'
    calc w * (a * c * a⁻¹) = a * ((a⁻¹ * w * a) * c) * a⁻¹ := by group
      _ = a * (c * (a⁻¹ * w * a)) * a⁻¹ := by rw [h1]
      _ = (a * c * a⁻¹) * w := by group
  have hAnormC : A ≤ normalizer (C : Set G) := fun a ha =>
    mem_normalizer_iff.mpr fun h => ⟨fun hh => hCnorm a ha h hh, fun hh => by
      have := hCnorm a⁻¹ (A.inv_mem ha) _ hh
      simpa [mul_assoc] using this⟩
  obtain ⟨D, hDC, hDp, hDidx, hDnorm⟩ :=
    k631a_exists_invariant_sylow (f := f) (r := f) hAf hAnormC (not_dvd_card_sylow f C)
  have hDJ : D ≤ J := hDC.trans hCJ
  have hDcomm : ∀ a ∈ A, ∀ d ∈ D, a * d = d * a := by
    intro a ha d hd
    have h1 : ⁅a, d⁆ ∈ O := (hA ha).2.2 d (hDJ hd)
    have h2 : ⁅a, d⁆ ∈ D := by
      have e : ⁅a, d⁆ = (a * d * a⁻¹) * d⁻¹ := by simp only [commutatorElement_def]
      rw [e]
      exact D.mul_mem (k631m_conj_mem (hDnorm ha) hd) (D.inv_mem hd)
    have h3 : ⁅a, d⁆ = 1 := k631a_eq_one_of_mem_inf hDp hOcop h2 h1
    exact commutatorElement_eq_one_iff_mul_comm.mp h3
  have hKn : J ≤ normalizer ((O ⊓ J : Subgroup G) : Set G) := fun j hj =>
    i183_mem_normalizer_inf (hXN (hJX hj)) (Subgroup.le_normalizer hj)
  have hdvd : C.relIndex J ∣ Nat.card ↥(O ⊓ J) :=
    k631m_relIndex_dvd hCJ inf_le_right hKn hlift
  have hidx : ¬ f ∣ (D.subgroupOf J).index := by
    have e : D.relIndex C * C.relIndex J = D.relIndex J :=
      Subgroup.relIndex_mul_relIndex D C J hDC hCJ
    intro h
    have h' : f ∣ D.relIndex C * C.relIndex J := by rw [e]; exact h
    rcases (Nat.Prime.dvd_mul hf).mp h' with h1 | h1
    · exact hDidx h1
    · exact hOf ((h1.trans hdvd).trans (Subgroup.card_dvd_of_le inf_le_left))
  exact ⟨D, hDC, hDp, hidx, hDcomm⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
