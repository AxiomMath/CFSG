module

public import CFSG.ClassicalInvolution.Asc77.AscP1Nine3
public import CFSG.ClassicalInvolution.Asc77.AscL62Final
public import CFSG.ClassicalInvolution.Asc77.WP2Thompson

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77.AscP1Nine3

variable {G : Type} [Group G] {p f : ℕ} [Fact p.Prime]

namespace AscP1Nine3

theorem le_centralizer_of_uniqueInvolution {K : Subgroup G} {z : G} (hz : IsUniqueInvolution K z) :
    K ≤ Subgroup.centralizer ({z} : Set G) := by
  intro w hw
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (hz.commute_of_mem hw).symm

theorem conjSub_inf_eq (g : G) (A B : Subgroup G) :
    conjSub g (A ⊓ B) = conjSub g A ⊓ conjSub g B := by
  ext x
  simp only [mem_conjSub_iff, Subgroup.mem_inf]

end AscP1Nine3

theorem l9_3 : L9_3 p f := by
  intro G _ _ Ω hP K hK z hz S hS U hUS hU d hdU hd1 hΓ
  obtain ⟨hp, hq, hΩ, -⟩ := hP
  have h67 : L6_7 p f := l6_7_proved p f
  by_contra hno
  have hS2 : IsPGroup 2 S := hS.2.1
  set C : Subgroup G := Subgroup.centralizer ({z} : Set G) with hC
  have hKC : K ≤ C := le_centralizer_of_uniqueInvolution hz
  obtain ⟨z', hz'⟩ := hΩ.classical K hK
  have hz'z : z' = z := by
    have hsq : z' * z' = 1 := by
      have := pow_orderOf_eq_one z'
      rwa [hz'.orderOf_eq_two, pow_two] at this
    rcases hz.unique z' hz'.mem hsq with h | h
    · exfalso
      have := hz'.orderOf_eq_two
      rw [h, orderOf_one] at this
      omega
    · exact h
  have hsub : IsSubnormal K C := by
    have := hz'.subnormal
    rw [hz'z] at this
    exact this
  have hR : IsSylow2In (S ⊓ K) K := isSylow2In_inf_of_isSubnormal hS hsub
  set R : Subgroup G := S ⊓ K with hRdef
  have hRS : R ≤ S := inf_le_left
  have hRK : R ≤ K := inf_le_right
  have hRset : R ∈ RSet Ω := mem_RSet_of_isSylow2In hK hR
  have h8 : 8 ≤ Nat.card R := hΩ.eight_le_of_mem_RSet hp hRset
  have hR2 : IsPGroup 2 R := hS2.to_le hRS
  have hzR : z ∈ R := mem_of_uniqueInvolution_of_isPGroup hz hRK hR2 (by omega)
  set X : Subgroup G := S ⊓ ⨆ L ∈ twinSet Ω K, L with hX
  have hKtw : K ∈ twinSet Ω K := ⟨hK, z, hz, hz⟩
  have hRX : R ≤ X := le_inf hRS (hRK.trans (le_iSup₂_of_le K hKtw le_rfl))
  have hSC : ∀ a ∈ S, a ∈ C := fun a ha => hS.1 ha
  have hconjR : ∀ a ∈ S, conjSub a R ≤ X := by
    intro a ha
    refine le_inf ?_ ?_
    · have := conjSub_mono (n := a) hRS
      rwa [conjSub_eq_self_of_mem ha] at this
    · have hKa : conjSub a K ∈ twinSet Ω K := by
        refine ⟨hΩ.conjInvariant a K hK, z, hz, ?_⟩
        have h1 := hz.conj a
        have h2 : a * z * a⁻¹ = z := by
          have := Subgroup.mem_centralizer_singleton_iff.mp (hSC a ha)
          calc a * z * a⁻¹ = (z * a) * a⁻¹ := by rw [this]
            _ = z := by group
        rwa [h2] at h1
      exact (conjSub_mono (n := a) hRK).trans (le_iSup₂_of_le _ hKa le_rfl)
  have hΓ' : ∀ w ∈ U, w ≠ 1 → ∀ y ∈ X, y * w = w * y → y * d = d * y := by
    intro w hw hw1 y hy hyw
    have hmem : y ∈ gamma1 U X := inf_centralizer_le_gamma1 hw hw1
      ⟨hy, Subgroup.mem_centralizer_singleton_iff.mpr hyw⟩
    exact Subgroup.mem_centralizer_singleton_iff.mp (hΓ hmem)
  have hU2 : ∀ x ∈ U, x * x = 1 := hU.2
  have hUc : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x := by
    intro x hx y hy
    have h1 := hU2 _ (U.mul_mem hx hy)
    have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hU2 x hx)
    have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right (hU2 y hy)
    have h2 : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_right h1
    calc x * y = (x * y)⁻¹ := h2.symm
      _ = y * x := by rw [mul_inv_rev, hxi, hyi]
  obtain ⟨u, huU, hu1, hud⟩ : ∃ u ∈ U, u ≠ 1 ∧ u ≠ d := by
    by_contra hcon
    have hall : ∀ x ∈ U, x = 1 ∨ x = d := by
      intro x hx
      by_contra hx'
      exact hcon ⟨x, hx, fun h => hx' (Or.inl h), fun h => hx' (Or.inr h)⟩
    have := natCard_subgroup_le_two_of_subset hall
    have h4 := hU.1
    omega
  have hdu1 : d * u ≠ 1 := by
    intro h
    apply hud
    have := inv_eq_of_mul_eq_one_right h
    rw [inv_eq_of_mul_eq_one_right (hU2 d hdU)] at this
    exact this.symm
  have hdUS : d ∈ S := hUS hdU
  have huS : u ∈ S := hUS huU
  have hduU : d * u ∈ U := U.mul_mem hdU huU
  have hduS : d * u ∈ S := hUS hduU
  have hd2 := hU2 d hdU
  have hu2 := hU2 u huU
  have hdu : d * u = u * d := hUc d hdU u huU
  have hdu2 : (d * u) * (d * u) = 1 := hU2 _ hduU
  have hstar : ∀ w ∈ U, w ≠ 1 → ∀ x ∈ R, orderOf x = 4 → x * w = w * x → False := by
    intro w hw hw1 x hx hxo hxw
    exact hno ⟨x, hRK hx, hxo, hΓ' w hw hw1 x (hRX hx) hxw⟩
  have hfixR : ∀ w ∈ S, conjSub w K = K → conjSub w R = R := by
    intro w hw hwK
    rw [hRdef, conjSub_inf_eq, conjSub_eq_self_of_mem hw, hwK]
  by_cases hfd : conjSub d K = K
  · by_cases hfu : conjSub u K = K
    · obtain ⟨x, hx, hxo, hc⟩ := exists_centralizer_orderFour_of_normalizes hz hRK hRS hS2 hzR
        (by omega) hdUS huS (hfixR d hdUS hfd) (hfixR u huS hfu)
      rcases hc with h | h | h
      · exact hstar d hdU hd1 x hx hxo h
      · exact hstar u huU hu1 x hx hxo h
      · exact hstar (d * u) hduU hdu1 x hx hxo h
    ·
      obtain ⟨x, hx, hxo, hc⟩ := exists_centralizer_orderFour_stab2 h67 hp hq hΩ hK hR hRS hS2 hz
        (a := u) (b := d * u) (d := d) hdUS huS hd2 hu2 hdu rfl (hfixR d hdUS hfd) hfu
        (Or.inl rfl) hRX (hconjR u huS) (hconjR (d * u) hduS)
        (fun w hw y hy hyw => by
          have hw' : w = u ∨ w = d * u := by simpa using hw
          rcases hw' with h | h
          · rw [h] at hyw
            exact hΓ' u huU hu1 y hy hyw
          · rw [h] at hyw
            exact hΓ' (d * u) hduU hdu1 y hy hyw)
      exact hstar d hdU hd1 x hx hxo hc
  · by_cases hfu : conjSub u K = K
    ·
      have hud' : u * d = d * u := hdu.symm
      obtain ⟨x, hx, hxo, hc⟩ := exists_centralizer_orderFour_stab2 h67 hp hq hΩ hK hR hRS hS2 hz
        (a := d) (b := u * d) (d := d) huS hdUS hu2 hd2 hud' rfl (hfixR u huS hfu) hfd
        (Or.inr (Or.inl rfl)) hRX (hconjR d hdUS) (hconjR (u * d) (hUS (U.mul_mem huU hdU)))
        (fun w hw y hy hyw => by
          have hw' : w = d ∨ w = u * d := by simpa using hw
          rcases hw' with h | h
          · rw [h] at hyw
            exact hΓ' d hdU hd1 y hy hyw
          · rw [h] at hyw
            exact hΓ' (u * d) (U.mul_mem huU hdU) (by rw [hud']; exact hdu1) y hy hyw)
      exact hstar u huU hu1 x hx hxo hc
    · by_cases hfdu : conjSub (d * u) K = K
      ·
        have hvd : (d * u) * d = d * (d * u) := by
          calc (d * u) * d = d * (u * d) := by group
            _ = d * (d * u) := by rw [hdu]
        have hb : u = (d * u) * d := by
          calc u = (d * d) * u := by rw [hd2, one_mul]
            _ = d * (d * u) := by group
            _ = (d * u) * d := hvd.symm
        obtain ⟨x, hx, hxo, hc⟩ := exists_centralizer_orderFour_stab2 h67 hp hq hΩ hK hR hRS hS2 hz
          (v := d * u) (a := d) (b := u) (d := d) hduS hdUS hdu2 hd2 hvd hb
          (hfixR (d * u) hduS hfdu) hfd (Or.inr (Or.inl rfl)) hRX (hconjR d hdUS)
          (hconjR u huS)
          (fun w hw y hy hyw => by
            have hw' : w = d ∨ w = u := by simpa using hw
            rcases hw' with h | h
            · rw [h] at hyw
              exact hΓ' d hdU hd1 y hy hyw
            · rw [h] at hyw
              exact hΓ' u huU hu1 y hy hyw)
        exact hstar (d * u) hduU hdu1 x hx hxo hc
      · exact false_of_all_move h67 hp hq hΩ hK hR hRS hS2 huS hdUS hu2 hfu hfd hfdu hRX
          (hconjR u huS) (fun y hy hyu => hΓ' u huU hu1 y hy hyu)

end CFSG.ClassicalInvolution.Asc77
