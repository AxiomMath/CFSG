module

public import CFSG.LocalAnalysis.ABGTheoremB.V4Basic
public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.TransitivityInputs
public import CFSG.GroupTheory.QuasiDihedralFusion.Transport
public import CFSG.LocalAnalysis.ABGTheoremB.V4Inputs

public section

namespace CFSG.ABGTheoremB.V4

open CFSG.QuasiDihedralFusion CFSG.ABGLocalTools CFSG.ABGTheoremB.TotallyInverted
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {σ : Setting G} {J W : Subgroup G}

theorem false_of_isQGroup_of_commutator_mem (hQF : Sec10.QGroupFourFusion G) {K T₁ : Subgroup G}
    (hK : IsQGroup K) (hT₁K : T₁ ≤ K) (hT₁ : IsKleinFour T₁)
    (hc : ∀ h ∈ K, ∀ t ∈ T₁, h * t * h⁻¹ * t⁻¹ ∈ oddCoreIn K) : False := by
  have := hT₁
  obtain ⟨z, hz, hz1, -, hconj⟩ := hQF K hK T₁ hT₁K hT₁
  have hz2 : orderOf z = 2 := kleinFour_orderOf hz hz1
  obtain ⟨t, ht, ht1, htz⟩ : ∃ t ∈ T₁, t ≠ 1 ∧ t ≠ z := by
    by_contra hcon
    push Not at hcon
    have hle : T₁ ≤ Subgroup.zpowers z := by
      intro t ht
      by_cases h1 : t = 1
      · rw [h1]; exact Subgroup.one_mem _
      · rw [hcon t ht h1]; exact Subgroup.mem_zpowers z
    have hcard := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, hz2, hT₁.card_four] at hcard
    omega
  obtain ⟨h, hh, hht⟩ := hconj t ht ht1 htz
  have hmem := hc h hh t ht
  have he : h * t * h⁻¹ * t⁻¹ = z := by
    rw [hht, mul_assoc, kleinFour_comm hz (T₁.inv_mem ht), ← mul_assoc, mul_inv_cancel, one_mul]
  rw [he] at hmem
  have hdvd : orderOf z ∣ Nat.card (oddCoreIn K) := Subgroup.orderOf_dvd_natCard _ hmem
  rw [hz2] at hdvd
  exact (Nat.not_even_iff_odd.mpr (odd_card_oddCoreIn K)) (even_iff_two_dvd.mpr hdvd)

theorem isQGroup_normalizer_of_le_oddCoreIn (hσ : σ.IsValid) (hII : σ.ChapterIIFacts)
    (hJ : σ.IsV21Layer J) (h31 : LemmaV31Input σ J) (hW : W ∈ σ.familyW J) (hW1 : W ≠ ⊥)
    {k : Fin 3} (hk : W ≤ oddCoreIn (σ.Ns k)) :
    IsQGroup (Subgroup.normalizer (W : Set G)) ∧
      ∀ h ∈ Subgroup.normalizer (W : Set G),
        h * σ.xs k * h⁻¹ * (σ.xs k)⁻¹ ∈ oddCoreIn (Subgroup.normalizer (W : Set G)) := by
  have : Fact σ.p.Prime := ⟨hσ.p_prime⟩
  obtain ⟨g, hgT, hgk⟩ := exists_conj_x_eq_xs hσ hII k
  set W' : Subgroup G := conjSub g⁻¹ W with hW'def
  have hW'ON : W' ≤ σ.ON := by
    rw [← DataConstruction.conjSub_inv_conjSub g σ.ON, conjSub_ON hgk]
    exact DataConstruction.conjSub_mono hk
  set Op := pCoreIn σ.p σ.N with hOp
  have hcop : Nat.Coprime (Nat.card W') (Nat.card Op) := by
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp (DataConstruction.isPGroup_pCoreIn σ.p σ.N)
    rw [DataConstruction.card_conjSub, ha]
    exact (Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hσ.p_prime).mpr
      (h31.coprime W hW))).symm
  have hOpsolv : Group.IsSolvable Op := by
    have := (DataConstruction.isPGroup_pCoreIn σ.p σ.N).isNilpotent
    infer_instance
  have hW'Op : W' ≤ Subgroup.normalizer (Op : Set G) :=
    (hW'ON.trans σ.ON_le_N).trans N_le_normalizer_pCore
  have hlift : ∀ y ∈ J, ∃ n ∈ Op, y * n ∈ Subgroup.centralizer (W' : Set G) := by
    intro y hy
    refine exists_mul_mem_centralizer_of_coprime hW'Op hOpsolv hcop (fun a ha => ?_)
    apply hJ.commutator_le
    have := Subgroup.commutator_mem_commutator (J.inv_mem hy) (hW'ON ha)
    rw [commutatorElement_def, inv_inv] at this
    simpa only [mul_assoc] using this
  set K : Subgroup G := Subgroup.normalizer (W' : Set G) with hKdef
  have hJON : J ≤ Subgroup.normalizer (σ.ON : Set G) := (J_le_N hσ hJ).trans σ.N_le_normalizer_ON
  have hcov : (σ.L₀ : Set G) ⊆ (K : Set G) * (σ.ON : Set G) := by
    intro l hl
    rw [SetLike.mem_coe, hJ.sup_eq] at hl
    obtain ⟨y, hy, o, ho, rfl⟩ := (mem_sup_iff_of_le_normalizer hJON).mp hl
    obtain ⟨n, hn, hyn⟩ := hlift y hy
    refine ⟨y * n, Subgroup.centralizer_le_normalizer _ hyn, n⁻¹ * o,
      σ.ON.mul_mem (σ.ON.inv_mem (pCore_N_le_ON hσ hn)) ho, ?_⟩
    simp only [mul_assoc, mul_inv_cancel_left]
  have hW'odd : Odd (Nat.card W') := by
    rw [DataConstruction.card_conjSub]
    exact odd_card_W hσ hJ hW
  have hW'K : W' ≤ oddCoreIn K := le_oddCoreIn Subgroup.le_normalizer le_rfl hW'odd
  have hOK : oddCoreIn K ≠ ⊥ := by
    intro h
    rw [h, le_bot_iff, hW'def, DataConstruction.conjSub_eq_bot_iff] at hW'K
    exact hW1 hW'K
  have hgT' : g⁻¹ ∈ Subgroup.normalizer (σ.T : Set G) := Subgroup.inv_mem _ hgT
  have hKeq : K = conjSub g⁻¹ (Subgroup.normalizer (W : Set G)) :=
    DataConstruction.normalizer_conjSub g⁻¹ W
  have hTK : σ.T ≤ K := by
    rw [hKeq, ← DataConstruction.conjSub_eq_self_of_mem hgT']
    exact DataConstruction.conjSub_mono (T_le_normalizer_W hσ hW)
  obtain ⟨hQ, hfac⟩ := hII.cover_qgroup K hTK hOK hcov
  have hKN : K ⊓ σ.N ≤ Subgroup.normalizer (oddCoreIn K : Set G) :=
    inf_le_left.trans (le_normalizer_oddCoreIn K)
  have hcK : ∀ h' ∈ K, h' * σ.x * h'⁻¹ * σ.x⁻¹ ∈ oddCoreIn K := by
    intro h' hh'
    rw [← hfac] at hh'
    obtain ⟨o, ho, c, hc, rfl⟩ := (mem_sup_iff_of_le_normalizer' hKN).mp hh'
    have hcx : c * σ.x = σ.x * c := (σ.mem_N_iff c).mp hc.2
    have hxO : σ.x * o⁻¹ * σ.x⁻¹ ∈ oddCoreIn K :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_oddCoreIn K (hTK σ.x_mem_T)) o⁻¹).mp
        ((oddCoreIn K).inv_mem ho)
    have e : o * c * σ.x * (o * c)⁻¹ * σ.x⁻¹ = o * (σ.x * o⁻¹ * σ.x⁻¹) := by
      calc o * c * σ.x * (o * c)⁻¹ * σ.x⁻¹ = o * (c * σ.x) * c⁻¹ * o⁻¹ * σ.x⁻¹ := by group
        _ = o * (σ.x * c) * c⁻¹ * o⁻¹ * σ.x⁻¹ := by rw [hcx]
        _ = o * (σ.x * o⁻¹ * σ.x⁻¹) := by group
    rw [e]
    exact (oddCoreIn K).mul_mem ho hxO
  refine ⟨?_, fun h hh => ?_⟩
  ·
    have hNW : Subgroup.normalizer (W : Set G) = conjSub g K := by
      rw [hKeq, DataConstruction.conjSub_conjSub_inv]
    rw [hNW]
    exact IsQGroup.of_mulEquiv
      (K.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective) hQ.1
  · have hh' : g⁻¹ * h * g ∈ K := by
      rw [hKeq, DataConstruction.mem_conjSub_iff, inv_inv]
      simpa [mul_assoc] using hh
    have hmem := hcK _ hh'
    rw [hKeq, ← DataConstruction.conjSub_oddCoreIn, DataConstruction.mem_conjSub_iff,
      inv_inv] at hmem
    rw [← hgk]
    convert hmem using 1
    group

theorem lemmaV41 (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) (hJ : σ.IsV21Layer J)
    (h31 : LemmaV31Input σ J) (hQF : Sec10.QGroupFourFusion G) (hW : W ∈ σ.familyW J)
    (hW1 : W ≠ ⊥) {i j : Fin 3} (hi : W ≤ oddCoreIn (σ.Ns i)) (hj : W ≤ oddCoreIn (σ.Ns j)) :
    i = j := by
  have h0 : ∀ k : Fin 3, W ≤ oddCoreIn (σ.Ns k) → k ≠ 0 := by
    rintro k hk rfl
    apply hW1
    rw [eq_bot_iff, ← W_inf_ON hJ hW]
    exact le_inf le_rfl hk
  by_contra hij
  obtain ⟨hQ, hci⟩ := isQGroup_normalizer_of_le_oddCoreIn hσ hII hJ h31 hW hW1 hi
  obtain ⟨-, hcj⟩ := isQGroup_normalizer_of_le_oddCoreIn hσ hII hJ h31 hW hW1 hj
  set K := Subgroup.normalizer (W : Set G)
  have hTK : σ.T ≤ K := T_le_normalizer_W hσ hW
  have hTO : σ.T ≤ Subgroup.normalizer (oddCoreIn K : Set G) :=
    hTK.trans (le_normalizer_oddCoreIn K)
  have h23 : (∀ h ∈ K, h * σ.x₂ * h⁻¹ * σ.x₂⁻¹ ∈ oddCoreIn K) ∧
      ∀ h ∈ K, h * σ.x₃ * h⁻¹ * σ.x₃⁻¹ ∈ oddCoreIn K := by
    have hi0 := h0 i hi
    have hj0 := h0 j hj
    fin_cases i <;> fin_cases j <;> simp_all <;> first
      | exact ⟨hci, hcj⟩ | exact ⟨hcj, hci⟩
  have hcT : ∀ h ∈ K, ∀ t ∈ σ.T, h * t * h⁻¹ * t⁻¹ ∈ oddCoreIn K := by
    intro h hh t ht
    rcases (DataConstruction.mem_T_iff hσ).mp ht with rfl | rfl | rfl | rfl
    · simp
    ·
      have hx : σ.x = σ.x₂ * σ.x₃ := (DataConstruction.x₂_mul_x₃ hσ).symm
      have h2 := h23.1 h hh
      have h3 := h23.2 h hh
      have hconj : σ.x₂ * (h * σ.x₃ * h⁻¹ * σ.x₃⁻¹) * σ.x₂⁻¹ ∈ oddCoreIn K :=
        (Subgroup.mem_normalizer_iff.mp (hTO σ.x₂_mem_T) _).mp h3
      have e : h * σ.x * h⁻¹ * σ.x⁻¹ =
          (h * σ.x₂ * h⁻¹ * σ.x₂⁻¹) * (σ.x₂ * (h * σ.x₃ * h⁻¹ * σ.x₃⁻¹) * σ.x₂⁻¹) := by
        rw [hx]; group
      rw [e]
      exact (oddCoreIn K).mul_mem h2 hconj
    · exact h23.1 h hh
    · exact h23.2 h hh
  exact false_of_isQGroup_of_commutator_mem hQF hQ hTK (Conjugacy.isKleinFour_T hσ) hcT

end CFSG.ABGTheoremB.V4
