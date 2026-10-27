module

public import CFSG.ClassicalInvolution.AschTight.Sec7KeyD

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem inf_W_of_mem_DSet (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω) (h611 : EtaMeets Ω)
    {W : Subgroup G} (hW : W ∈ WSet Ω) {R J : Subgroup G} (hR : R ∈ DSet Ω W) (hJ : J ∈ Ω)
    (hRJ : R ≤ J) :
    J ⊓ W = R ⊓ W ∧ R ⊓ W ∈ USet Ω ∧ Nat.card R = 2 * Nat.card ↥(R ⊓ W) ∧
      ∃ η ∈ etaG Ω, W = (⨆ U ∈ η, U) ∧ R ⊓ W ∈ η := by
  have hRsyl := isSylow2In_of_mem_RSet_of_le hp hΩ hR.1 hJ hRJ
  have h8 := hΩ.eight_le_of_mem_RSet hp hR.1
  obtain ⟨η, hη, hWη⟩ := id hW
  obtain ⟨S₁, hS₁⟩ := (IsPGroup.to_sup_of_normal_right' (isPGroup_of_mem_RSet hR.1)
    (isPGroup_of_mem_WSet hW) hR.2).exists_le_sylow
  have hJS₁ : 2 < Nat.card ↥(J ⊓ (S₁ : Subgroup G)) := by
    have := Subgroup.card_le_of_le (le_inf hRJ (le_sup_left.trans hS₁))
    omega
  have hU : J ⊓ W ∈ η := by
    have := h611 S₁ η hη (fun V hV => (hWη ▸ le_iSup₂_of_le (f := fun V (_ : V ∈ η) => V) V hV
      le_rfl : V ≤ W).trans (le_sup_right.trans hS₁)) J hJ hJS₁
    rwa [← hWη] at this
  have hJS : J ⊓ (S₁ : Subgroup G) = R :=
    hRsyl.eq_of_le (S₁.isPGroup'.to_le inf_le_right) inf_le_left
      (le_inf hRJ (le_sup_left.trans hS₁))
  have hJWR : J ⊓ W ≤ R := hJS ▸ inf_le_inf_left J (le_sup_right.trans hS₁)
  have heq : J ⊓ W = R ⊓ W := le_antisymm (le_inf hJWR inf_le_right) (inf_le_inf_right W hRJ)
  have hUU := mem_USet_of_mem_etaG hη hU
  rw [heq] at hU hUU
  exact ⟨heq, hUU, natCard_eq_two_mul_of_mem_USet hp hΩ hUU hJ hRsyl, η, hη, hWη, hU⟩

omit [Finite G] in
theorem sup_zpowers_le_centralizer {C : Subgroup G}
    (hC : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x) {g : G} (hg : ∀ x ∈ C, g * x = x * g) :
    C ⊔ Subgroup.zpowers g ≤ Subgroup.centralizer ((C ⊔ Subgroup.zpowers g : Subgroup G) :
      Set G) := by
  have h1 : C ⊔ Subgroup.zpowers g ≤ Subgroup.centralizer (C : Set G) := by
    refine sup_le (fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy => hC y hy x hx) ?_
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_centralizer_iff.mpr fun y hy => (hg y hy).symm
  have h2 : C ⊔ Subgroup.zpowers g ≤ Subgroup.centralizer ({g} : Set G) := by
    refine sup_le (fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr (hg x hx).symm) ?_
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  refine sup_le (fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy => ?_) ?_
  · exact ((Subgroup.mem_centralizer_iff.mp (h1 hy)) x hx).symm
  · rw [Subgroup.zpowers_le]
    exact Subgroup.mem_centralizer_iff.mpr fun y hy =>
      (Subgroup.mem_centralizer_singleton_iff.mp (h2 hy))

theorem mem_of_commute_of_index_two (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω) {R C : Subgroup G}
    (hR : R ∈ RSet Ω) (hCR : C ≤ R) (hC : IsCyclic ↥C) (hcard : Nat.card R = 2 * Nat.card C)
    {x : G} (hxR : x ∈ R) (hx : ∀ c ∈ C, x * c = c * x) : x ∈ C := by
  by_contra hxC
  have hle : C ⊔ Subgroup.zpowers x ≤ R := sup_le hCR (Subgroup.zpowers_le.mpr hxR)
  have hlt : C < C ⊔ Subgroup.zpowers x :=
    lt_of_le_of_ne le_sup_left fun h => hxC (h ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers x))
  have heq : C ⊔ Subgroup.zpowers x = R := by
    obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hlt.le
    have hk1 : k ≠ 1 := by
      rintro rfl
      rw [mul_one] at hk
      exact hlt.ne (Subgroup.eq_of_le_of_card_ge hlt.le hk.le)
    have hk0 : k ≠ 0 := by
      rintro rfl
      have := (Nat.card_pos (α := ↥(C ⊔ Subgroup.zpowers x))).ne'
      omega
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    calc Nat.card R = 2 * Nat.card C := hcard
      _ ≤ Nat.card C * k := by rw [mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
      _ = _ := hk.symm
  obtain ⟨a, ha, b, hb, hab⟩ := (hΩ.isQuatSub_of_mem_RSet hp hR).exists_not_commute
  rw [← heq] at ha hb
  have hcomm := sup_zpowers_le_centralizer (fun y hy w hw => commute_of_isCyclic hC hy hw) hx
  exact hab ((Subgroup.mem_centralizer_iff.mp (hcomm hb)) a ha)

omit [Finite G] in
theorem sup_OCW_le_centralizer {W : Subgroup G} (hWab : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) :
    W ⊔ OCW W ≤ Subgroup.centralizer (W : Set G) :=
  sup_le (fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy => hWab y hy x hx)
    (oddCoreOf_le_self _)

theorem mem_of_isPGroup_of_mem_sup_OCW {W : Subgroup G} (hW2 : IsPGroup 2 W) {g : G}
    (hg : g ∈ W ⊔ OCW W) (hg2 : IsPGroup 2 (Subgroup.zpowers g)) : g ∈ W := by
  have hXW : W ≤ Subgroup.normalizer ((OCW W : Subgroup G) : Set G) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_OCW W)
  have hg' : g ∈ ((W ⊔ OCW W : Subgroup G) : Set G) := hg
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hXW] at hg'
  obtain ⟨w, hw, x, hx, rfl⟩ := hg'
  show w * x ∈ W
  have hxw : w * x = x * w :=
    (Subgroup.mem_centralizer_iff.mp (oddCoreOf_le_self _ hx)) w hw
  obtain ⟨n, hn⟩ := hg2.exists_card_eq
  rw [Nat.card_zpowers] at hn
  have h1 : (w * x) ^ (2 ^ n) = 1 := by rw [← hn]; exact pow_orderOf_eq_one _
  have hc : Commute w x := hxw
  rw [hc.mul_pow] at h1
  have hxW : x ^ (2 ^ n) ∈ W := by
    have : x ^ (2 ^ n) = (w ^ (2 ^ n))⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [this]
    exact W.inv_mem (W.pow_mem hw _)
  have hxX : x ^ (2 ^ n) ∈ OCW W := (OCW W).pow_mem hx _
  have h2 : x ^ (2 ^ n) = 1 := eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard _) hxX
    (hW2.to_le (Subgroup.zpowers_le.mpr hxW))
  have h3 : x = 1 := by
    have hodd : Odd (orderOf x) :=
      (oddCoreOf_odd_natCard _).of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hx)
    have hdvd : orderOf x ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one h2
    have hc : Nat.Coprime (orderOf x) (2 ^ n) :=
      Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hodd)
    exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hc hdvd)
  rw [h3, mul_one]
  exact hw

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7
