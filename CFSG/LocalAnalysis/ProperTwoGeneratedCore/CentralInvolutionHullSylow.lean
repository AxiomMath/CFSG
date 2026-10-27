module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherEscapingRankTwo

public section

namespace CFSG.ProperTwoGeneratedCore.CentralInvolutionHull

open CFSG.Open CFSG.ProperTwoGeneratedCore CFSG.ProperTwoGeneratedCore.Assembly

variable {M : Type} [Group M] [Finite M]

theorem range_conj_normal (L : Type*) [Group L] :
    (MulAut.conj : L →* MulAut L).range.Normal := by
  constructor
  rintro _ ⟨l, rfl⟩ σ
  refine ⟨σ l, ?_⟩
  ext x
  simp [MulAut.conj_apply, map_mul, map_inv]

theorem card_eq_card_mul_relIndex {K L : Subgroup M} (hKL : K ≤ L) :
    Nat.card L = Nat.card K * K.relIndex L := by
  have h1 := Subgroup.card_mul_index K
  have h2 := Subgroup.card_mul_index L
  have h3 := Subgroup.relIndex_mul_index hKL
  have hpos : 0 < L.index := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
  have : Nat.card L * L.index = Nat.card K * K.relIndex L * L.index := by
    rw [h2, mul_assoc, h3, h1]
  exact Nat.eq_of_mul_eq_mul_right hpos this

omit [Finite M] in
theorem zpowers_normal_of_mem_center {u : M} (huZ : u ∈ Subgroup.center M) :
    (Subgroup.zpowers u).Normal :=
  Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr huZ)

omit [Finite M] in
theorem zpowers_inf_eq_bot {u : M} (hu : orderOf u = 2) (H : Subgroup M) (huH : u ∉ H) :
    Subgroup.zpowers u ⊓ H = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxu, hxH⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxu
  have hk : u ^ k = u ^ (k % 2) := by
    rw [← zpow_mod_orderOf, hu]; norm_cast
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · rw [hk, h, zpow_zero]; exact Subgroup.one_mem _
  · rw [hk, h, zpow_one] at hxH; exact absurd hxH huH

theorem card_zpowers_sup {u : M} (hu : orderOf u = 2) (huZ : u ∈ Subgroup.center M)
    (H : Subgroup M) (huH : u ∉ H) :
    Nat.card (Subgroup.zpowers u ⊔ H : Subgroup M) = 2 * Nat.card H := by
  have := zpowers_normal_of_mem_center huZ
  have h1 : (Subgroup.zpowers u).relIndex (Subgroup.zpowers u ⊔ H) = Nat.card H := by
    rw [Subgroup.relIndex_sup_left, ← Subgroup.inf_relIndex_right, zpowers_inf_eq_bot hu H huH,
      Subgroup.relIndex_bot_left]
  rw [card_eq_card_mul_relIndex (le_sup_left : Subgroup.zpowers u ≤ _), h1, Nat.card_zpowers, hu]

omit [Finite M] in
theorem conjNormal_eq_one_iff (L : Subgroup M) [L.Normal] (x : M) :
    MulAut.conjNormal (H := L) x = 1 ↔ x ∈ Subgroup.centralizer (L : Set M) := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro h l hl
    have := congrArg (fun σ : MulAut L => ((σ ⟨l, hl⟩ : L) : M)) h
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at this
    calc l * x = x * l * x⁻¹ * x := by rw [this]
      _ = x * l := by group
  · intro h
    ext ⟨l, hl⟩
    simp only [MulAut.conjNormal_apply, MulAut.one_apply]
    rw [← h l hl]
    group

theorem central_involution_hull_odd_outer_quotient_elementary_sylow
    (L : Subgroup M) [L.Normal] {u : M} (hu : orderOf u = 2) (huZ : u ∈ Subgroup.center M)
    (huL : u ∉ L) (hCL : Subgroup.centralizer (L : Set M) = Subgroup.zpowers u)
    (hOut : Odd (MulAut.conj : L →* MulAut L).range.index)
    (R : Subgroup M) (hRL : R ≤ L) (hRidx : ¬ 2 ∣ R.relIndex L)
    (hRelem : IsElemAbelian 2 R) :
    ∃ P : Sylow 2 M, (P : Subgroup M) = Subgroup.zpowers u ⊔ R ∧
      IsElemAbelian 2 (Subgroup.zpowers u ⊔ R) ∧ ∀ x : M, orderOf x ≠ 4 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let φ : M →* MulAut L := MulAut.conjNormal
  let Inn : Subgroup (MulAut L) := (MulAut.conj : L →* MulAut L).range
  have hInn : Inn.Normal := range_conj_normal L
  have hNodd : Odd (Inn.comap φ).index := by
    rw [Subgroup.index_comap]
    exact Odd.of_dvd_nat hOut (Subgroup.relIndex_dvd_index_of_normal Inn φ.range)
  set N' : Subgroup M := Subgroup.zpowers u ⊔ L with hN'
  have hNle : Inn.comap φ ≤ N' := by
    intro m hm
    obtain ⟨l, hl⟩ := Subgroup.mem_comap.mp hm
    have hker : φ (m * (l : M)⁻¹) = 1 := by
      rw [map_mul, map_inv, ← hl]
      change MulAut.conj l * (MulAut.conjNormal (H := L) (l : M))⁻¹ = 1
      rw [MulAut.conjNormal_val, mul_inv_cancel]
    have hc : m * (l : M)⁻¹ ∈ Subgroup.zpowers u := hCL ▸ (conjNormal_eq_one_iff L _).mp hker
    have : m = (m * (l : M)⁻¹) * l := by group
    rw [this]
    exact N'.mul_mem (le_sup_left (a := Subgroup.zpowers u) hc) (le_sup_right (b := L) l.property)
  have hN'odd : Odd N'.index := Odd.of_dvd_nat hNodd (Subgroup.index_dvd_of_le hNle)
  have huR : u ∉ R := fun h => huL (hRL h)
  have hcardN' := card_zpowers_sup hu huZ L huL
  have hcardP := card_zpowers_sup hu huZ R huR
  set P : Subgroup M := Subgroup.zpowers u ⊔ R with hP
  have hPN' : P ≤ N' := sup_le_sup_left hRL _
  have hrel : P.relIndex N' = R.relIndex L := by
    have h1 := card_eq_card_mul_relIndex hPN'
    have h2 := card_eq_card_mul_relIndex hRL
    rw [hcardN', hcardP, h2] at h1
    have hpos : 0 < 2 * Nat.card R := Nat.mul_pos (by norm_num) Nat.card_pos
    have : 2 * Nat.card R * R.relIndex L = 2 * Nat.card R * P.relIndex N' := by
      rw [← h1]; ring
    exact (Nat.eq_of_mul_eq_mul_left hpos this).symm
  have hPidx : ¬ 2 ∣ P.index := by
    rw [← Subgroup.relIndex_mul_index hPN', hrel]
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h with h | h
    · exact hRidx h
    · exact (Nat.not_even_iff_odd.mpr hN'odd) (even_iff_two_dvd.mpr h)
  have hPelem : IsElemAbelian 2 P := by
    refine commuting_elementary_sup _ _ (involution_zpowers_elementary u hu) hRelem ?_
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro r _
    exact (Subgroup.mem_center_iff.mp huZ r)
  have hPp : IsPGroup 2 P := isPGroup_of_isElemAbelian hPelem
  refine ⟨hPp.toSylow hPidx, hPp.toSylow_coe hPidx, hPelem, ?_⟩
  intro x hx
  have hxp : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hx]; norm_num)
  obtain ⟨g, hg⟩ := exists_conj_mem_sylow (hPp.toSylow hPidx) hxp
  have hgx : g⁻¹ * x * g ∈ P := by
    have := hg x (Subgroup.mem_zpowers x)
    rwa [hPp.toSylow_coe hPidx] at this
  have hsq : (g⁻¹ * x * g) ^ 2 = 1 := hPelem.2 _ hgx
  have hx2 : x ^ 2 = 1 := by
    have hc : (g⁻¹ * x * g⁻¹⁻¹) ^ 2 = g⁻¹ * x ^ 2 * g⁻¹⁻¹ := conj_pow
    rw [inv_inv] at hc
    rw [hc] at hsq
    have := congrArg (fun y => g * y * g⁻¹) hsq
    simpa [mul_assoc] using this
  have := orderOf_dvd_of_pow_eq_one hx2
  rw [hx] at this
  norm_num at this

end CFSG.ProperTwoGeneratedCore.CentralInvolutionHull
