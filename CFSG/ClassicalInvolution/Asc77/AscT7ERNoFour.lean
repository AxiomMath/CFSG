module

public import CFSG.ClassicalInvolution.Asc77.AscT7ERStar

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

namespace T7ER

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K K' : Subgroup G} {z : G}

omit [Finite G] in
theorem not_mem_twinSet_of_ne {J : Subgroup G} {a : G} (hz : IsUniqueInvolution K z)
    (ha : IsUniqueInvolution J a) (hne : a ≠ z) : J ∉ twinSet Ω K := by
  rintro ⟨-, z₀, hz₀, hJz₀⟩
  exact hne ((ha.eq hJz₀).trans (hz₀.eq hz))

theorem not_le_centralizer_of_mem_USet (hs : Hyp23Setting p f Ω K K' z) {W₀ : Subgroup G}
    (hW₀ : W₀ ∈ WSet Ω) (hE4 : MuIsoE4 Ω W₀) {J : Subgroup G} (hJ : J ∈ Ω)
    (hJt : J ∉ twinSet Ω K) {V : Subgroup G} (hV : V ∈ USet Ω) (hVJ : V ≤ J) :
    ¬ V ≤ Subgroup.centralizer ({z} : Set G) := by
  intro hVC
  have hst : AscStand p f Ω K := hs.stand
  have hp : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hK : K ∈ Ω := hst.mem
  have hKt : K ∈ twinSet Ω K := ⟨hK, z, hs.hz, hs.hz⟩
  have hKJ : K ≠ J := fun h => hJt (h ▸ hKt)
  have hV2 : IsPGroup 2 V := hΩ.isPGroup_of_mem_USet hp hV
  obtain ⟨-, -, -, -, -, -, -, -, hV4⟩ := hΩ.exists_data_of_mem_USet hp hV
  have hVN : V ≤ Subgroup.normalizer (K : Set G) :=
    hΩ.le_normalizer_of_le_centralizer hp hq hK hJ hKJ hs.hz hVJ hV2 (by omega) hVC
  have hstar : J ∈ omegaStarNbr Ω K := ⟨hJ, hKJ.symm, V, hV, hVJ, hVN⟩
  have hnbr := omegaStarNbr_subset_omegaNbr_of_E4 hst hW₀ hE4 hK hstar
  have hperp : J ∈ KPerp Ω K := Set.mem_insert_of_mem _ hnbr
  rw [hs.perp] at hperp
  rcases hperp with h | h
  · exact hKJ h.symm
  · exact hJt (h ▸ hs.hK')

theorem not_commute_of_orderOf_four (hs : Hyp23Setting p f Ω K K' z) {W₀ : Subgroup G}
    (hW₀ : W₀ ∈ WSet Ω) (hE4 : MuIsoE4 Ω W₀) {J : Subgroup G} (hJ : J ∈ Ω)
    (hJt : J ∉ twinSet Ω K) {x : G} (hx : x ∈ J) (hx4 : orderOf x = 4) : z * x ≠ x * z := by
  intro hxz
  have hst : AscStand p f Ω K := hs.stand
  have hp : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hK : K ∈ Ω := hst.mem
  obtain ⟨tJ, htJ⟩ := hΩ.exists_uniqueInvolution hp hq hJ
  have hxx : x * x = tJ := T7A.sq_eq_of_orderOf_four htJ hx hx4
  have hxC : x ∈ J ⊓ Subgroup.centralizer ({z} : Set G) :=
    ⟨hx, Subgroup.mem_centralizer_singleton_iff.mpr hxz.symm⟩
  have hx2 : IsPGroup 2 (Subgroup.zpowers x) := by
    refine IsPGroup.of_card (n := 2) ?_
    rw [Nat.card_zpowers, hx4]
    norm_num
  obtain ⟨V, hV, hxV⟩ := IsSylow2In.exists_ge hx2
    (Subgroup.zpowers_le.mpr hxC : Subgroup.zpowers x ≤ J ⊓ Subgroup.centralizer ({z} : Set G))
  have hxVm : x ∈ V := hxV (Subgroup.mem_zpowers x)
  have htV : tJ ∈ V := hxx ▸ V.mul_mem hxVm hxVm
  have hVJ : V ≤ J := hV.1.trans inf_le_left
  have hVC : V ≤ Subgroup.centralizer ({z} : Set G) := hV.1.trans inf_le_right
  have hnot2 : V ≠ Subgroup.zpowers tJ := by
    intro hVt
    rw [hVt] at hxVm
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxVm
    have h1 : x * x = 1 := by
      rw [← hk, ← zpow_add, ← two_mul, zpow_mul]
      have h2 : tJ ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact htJ.sq
      rw [h2, one_zpow]
    have h3 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h1)
    rw [hx4] at h3
    omega
  rcases l6_2 p f hp hq G Ω hΩ K hK z hs.hz J hJ hJt tJ htJ V hV htV with
    h | h | h | h
  · exact hnot2 h.1
  · exact hnot2 h.1
  · exact not_le_centralizer_of_mem_USet hs hW₀ hE4 hJ hJt h.1 hVJ hVC
  · have hVsyl : IsSylow2In V J := T7C.isSylow2In_of_mem_RSet_of_le hp hΩ hJ h.1 hVJ
    obtain ⟨U, hUV, hUc, hUcard⟩ := (hΩ.isQuatSub_of_mem_RSet hp h.1).exists_cyclic_index_two
    exact not_le_centralizer_of_mem_USet hs hW₀ hE4 hJ hJt
      (mem_USet_of_natCard hJ hVsyl hUV hUc hUcard) (hUV.trans hVJ) (hUV.trans hVC)

theorem not_commute_of_conj (hs : Hyp23Setting p f Ω K K' z) {W₀ : Subgroup G}
    (hW₀ : W₀ ∈ WSet Ω) (hE4 : MuIsoE4 Ω W₀) {J : Subgroup G} (hJ : J ∈ Ω) {a : G}
    (ha : IsUniqueInvolution J a) {y : G} (hya : y * z * y⁻¹ ≠ a) {x : G} (hx : x ∈ J)
    (hx4 : orderOf x = 4) : (y * z * y⁻¹) * x ≠ x * (y * z * y⁻¹) := by
  intro hc
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hJ' : conjSub y⁻¹ J ∈ Ω := hΩ.conjInvariant y⁻¹ J hJ
  have ha' : IsUniqueInvolution (conjSub y⁻¹ J) (y⁻¹ * a * y⁻¹⁻¹) := ha.conj y⁻¹
  have hne : y⁻¹ * a * y⁻¹⁻¹ ≠ z := by
    intro h
    apply hya
    have : a = y * z * y⁻¹ := by
      have h2 : y * (y⁻¹ * a * y⁻¹⁻¹) * y⁻¹ = a := by group
      rw [← h2, h]
    exact this.symm
  have hx' : y⁻¹ * x * y ∈ conjSub y⁻¹ J := by
    have := conj_mem_conjSub (n := y⁻¹) hx
    simpa [mul_assoc] using this
  have hord : orderOf (y⁻¹ * x * y) = 4 := by
    have h := MulEquiv.orderOf_eq (MulAut.conj y⁻¹) x
    simp only [MulAut.conj_apply, inv_inv] at h
    rw [h, hx4]
  have hcomm : z * (y⁻¹ * x * y) = (y⁻¹ * x * y) * z := by
    calc z * (y⁻¹ * x * y) = y⁻¹ * ((y * z * y⁻¹) * x) * y := by group
      _ = y⁻¹ * (x * (y * z * y⁻¹)) * y := by rw [hc]
      _ = (y⁻¹ * x * y) * z := by group
  exact not_commute_of_orderOf_four hs hW₀ hE4 hJ' (not_mem_twinSet_of_ne hs.hz ha' hne) hx'
    hord hcomm

end T7ER

end CFSG.ClassicalInvolution.Asc77
