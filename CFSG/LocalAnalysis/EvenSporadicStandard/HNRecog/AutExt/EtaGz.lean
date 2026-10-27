module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.EtaStd
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.OutY

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Section3

variable {G : Type} [Group G] {a z : G}

theorem decomp_Y_of_base (h : F5Base a z) {w x : G} (hw : IsConj z w) (hx : IsConj a x)
    (hwx : IsConj z (w * x)) :
    ∀ y ∈ Gxy w x, ∃ u ∈ derivedOf (Gxy w x), y = u ∨ y = w * u ∨ y = x * u ∨ y = w * x * u := by
  rw [Gxy_comm w x]
  intro y hy
  haveI : Finite G := h.finite
  have hcomm : w * x = x * w := h.mul_comm (Or.inr hw) (Or.inl hx) (Or.inr hwx)
  have hxmem : x ∈ Gx w := mem_Gx.2 hcomm
  have hwx' : IsConj w (x * w) := by
    have h1 : IsConj w (w * x) := hw.symm.trans hwx
    rwa [hcomm] at h1
  have hF : F5Base a w := h.of_isConj (IsConj.refl a) hw
  have hY : Y4aStruct a w x := hF.loc.y4a.self.y4a x hxmem hx hwx'
  let Y : Subgroup G := Gxy x w
  let Y' : Subgroup G := derivedOf Y
  let M : Subgroup G := CFSG.Open.pCoreOf 2 Y'
  have hYcard : Nat.card ↥Y = 3840 := card_of_isShapeTwoTwoTimesTwoFourA5 hY.shape
  have hM : Nat.card ↥M = 16 := by
    have h16 : Nat.card ↥M = 2 ^ 4 := hY.orth.1.2
    rw [h16]; norm_num
  obtain ⟨π, hπsurj, hπker, hπab⟩ := y4a_exists_hom hY.shape
  obtain ⟨hY'card, -, hψdata⟩ := y4a_derived_of_hom π hπsurj hπker hπab hM
  obtain ⟨ψ, hψsurj, hψker⟩ := hψdata
  have hY'card' : Nat.card ↥Y' = 960 := hY'card
  have hcentral_triv : ∀ c ∈ Y', (∀ k ∈ Y, k * c = c * k) → c = 1 := by
    intro c hc hck
    have hψc_center : ψ ⟨c, hc⟩ ∈ Subgroup.center (alternatingGroup (Fin 5)) := by
      rw [Subgroup.mem_center_iff]
      intro σ
      obtain ⟨l, rfl⟩ := hψsurj σ
      have hcl : (⟨c, hc⟩ : ↥Y') * l = l * ⟨c, hc⟩ := by
        apply Subtype.ext
        exact (hck (l : G) (derivedOf_le Y l.2)).symm
      calc ψ l * ψ ⟨c, hc⟩ = ψ (l * ⟨c, hc⟩) := by rw [map_mul]
        _ = ψ (⟨c, hc⟩ * l) := by rw [hcl]
        _ = ψ ⟨c, hc⟩ * ψ l := by rw [map_mul]
    have hcenter : Subgroup.center (alternatingGroup (Fin 5)) = ⊥ :=
      alternatingGroup.center_eq_bot (α := Fin 5) (by simp)
    have hψc_one : ψ ⟨c, hc⟩ = 1 := by
      have hmem := hψc_center
      rw [hcenter] at hmem
      simpa using hmem
    have hcM : c ∈ M := by
      have := (hψker ⟨c, hc⟩).mp hψc_one
      simpa using this
    by_contra hcne
    obtain ⟨S, hpart, hS0, hS1⟩ := hY.orth.2
    have hcmem : c ∈ {x : G | x ∈ M ∧ x ≠ 1} := ⟨hcM, hcne⟩
    obtain ⟨i, hi⟩ := hpart.cover c hcmem
    have hSsing : S i = {c} := by
      rw [Set.eq_singleton_iff_unique_mem]
      refine ⟨hi, ?_⟩
      intro c' hc'
      obtain ⟨k, hk, hk'⟩ := (hpart.orbit i).transitive c hi c' hc'
      have hkc : k * c * k⁻¹ = c := by
        rw [hck k (derivedOf_le Y hk)]
        group
      rw [hkc] at hk'
      exact hk'.symm
    have hcard1 : Nat.card ↥(S i) = 1 := by
      haveI : Subsingleton ↥(S i) := ⟨fun a b => by
        apply Subtype.ext
        have ha : (a : G) = c := by simpa [hSsing] using a.2
        have hb : (b : G) = c := by simpa [hSsing] using b.2
        rw [ha, hb]⟩
      haveI : Nonempty ↥(S i) := ⟨⟨c, hi⟩⟩
      exact Nat.card_unique
    by_cases hi0 : i = 0
    · rw [hi0] at hcard1
      rw [hS0] at hcard1
      exact absurd hcard1 (by norm_num)
    · have hi1 : i = 1 := by
        apply Fin.ext
        have hne : (i : ℕ) ≠ 0 := fun hv => hi0 (Fin.ext (by simpa using hv))
        omega
      rw [hi1] at hcard1
      rw [hS1] at hcard1
      exact absurd hcard1 (by norm_num)
  have hwY : w ∈ Y := by
    show w ∈ Gxy x w
    rw [mem_Gxy]
    exact ⟨mem_Gx.2 hcomm.symm, mem_Gx.2 rfl⟩
  have hxY : x ∈ Y := by
    show x ∈ Gxy x w
    rw [mem_Gxy]
    exact ⟨mem_Gx.2 rfl, mem_Gx.2 hcomm⟩
  have hwxY : w * x ∈ Y := Y.mul_mem hwY hxY
  let u : Fin 4 → G := ![1, w, x, w * x]
  have hu_mem : ∀ i, u i ∈ Y := by
    intro i
    fin_cases i
    · simpa [u] using Y.one_mem
    · simpa [u] using hwY
    · simpa [u] using hxY
    · simpa [u] using hwxY
  have hw_ne_one : w ≠ 1 := by
    intro hw1
    have h2 : orderOf w = 2 := h.orderOf_eq_two (Or.inr hw)
    rw [hw1, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  have hx_ne_one : x ≠ 1 := by
    intro hx1
    have h2 : orderOf x = 2 := h.orderOf_eq_two (Or.inl hx)
    rw [hx1, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  have hw_ne_x : w ≠ x := by
    intro hwx_eq
    have hax : IsConj a w := hwx_eq.symm ▸ hx
    exact not_isConj_of_isF5Type h.iface h.typ (hax.trans hw.symm)
  have hwx_ne_one : w * x ≠ 1 := by
    intro hwx1
    have h2 : orderOf (w * x) = 2 := h.orderOf_eq_two (Or.inr hwx)
    rw [hwx1, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  have hwx_ne_w : w * x ≠ w := by
    intro hwxw
    have h' : w * x = w * 1 := by rw [hwxw, mul_one]
    exact hx_ne_one (mul_left_cancel h')
  have hwx_ne_x : w * x ≠ x := by
    intro hwxx
    have h' : w * x = 1 * x := by rw [hwxx, one_mul]
    exact hw_ne_one (mul_right_cancel h')
  have hu_inj : Function.Injective u := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [u] at hij
    all_goals first
      | rfl
      | exact absurd hij hw_ne_one
      | exact absurd hij.symm hw_ne_one
      | exact absurd hij hx_ne_one
      | exact absurd hij.symm hx_ne_one
      | exact absurd hij hw_ne_x
      | exact absurd hij.symm hw_ne_x
      | exact absurd hij hwx_ne_one
      | exact absurd hij.symm hwx_ne_one
      | exact absurd hij hwx_ne_w
      | exact absurd hij.symm hwx_ne_w
      | exact absurd hij hwx_ne_x
      | exact absurd hij.symm hwx_ne_x
  have hw_sq : w * w = 1 := by
    simpa [pow_two, h.orderOf_eq_two (Or.inr hw)] using pow_orderOf_eq_one w
  have hx_sq : x * x = 1 := by
    simpa [pow_two, h.orderOf_eq_two (Or.inl hx)] using pow_orderOf_eq_one x
  have hwx_sq : (w * x) * (w * x) = 1 := by
    simpa [pow_two, h.orderOf_eq_two (Or.inr hwx)] using pow_orderOf_eq_one (w * x)
  have hcomm_u : ∀ i, ∀ k ∈ Y, k * u i = u i * k := by
    intro i k hk
    have hkw : w * k = k * w :=
      mem_Gx.mp (mem_Gxy.mp (show k ∈ Gxy x w from hk)).2
    have hkx : x * k = k * x :=
      mem_Gx.mp (mem_Gxy.mp (show k ∈ Gxy x w from hk)).1
    fin_cases i
    · simp [u]
    · simpa [u] using hkw.symm
    · simpa [u] using hkx.symm
    · calc k * (w * x) = (k * w) * x := by group
        _ = (w * k) * x := by rw [hkw.symm]
        _ = w * (k * x) := by group
        _ = w * (x * k) := by rw [hkx.symm]
        _ = (w * x) * k := by group
  have hsq_u : ∀ i, u i * u i = 1 := by
    intro i
    fin_cases i
    · simp [u]
    · simpa [u] using hw_sq
    · simpa [u] using hx_sq
    · simpa [u] using hwx_sq
  have hinv_u : ∀ i, (u i)⁻¹ = u i := fun i => inv_eq_of_mul_eq_one_right (hsq_u i)
  have hkey : ∀ i j, u i * u j ∈ Y' → i = j := by
    intro i j hij
    have hcommij : ∀ k ∈ Y, k * (u i * u j) = (u i * u j) * k := by
      intro k hk
      calc k * (u i * u j) = (k * u i) * u j := by group
        _ = (u i * k) * u j := by rw [hcomm_u i k hk]
        _ = u i * (k * u j) := by group
        _ = u i * (u j * k) := by rw [hcomm_u j k hk]
        _ = (u i * u j) * k := by group
    have h1 : u i * u j = 1 := hcentral_triv (u i * u j) hij hcommij
    have h2 : u i = u j := by
      calc u i = u i * (u j * u j) := by rw [hsq_u j, mul_one]
        _ = (u i * u j) * u j := by group
        _ = u j := by rw [h1, one_mul]
    exact hu_inj h2
  let F : Fin 4 × ↥Y' → ↥Y :=
    fun p => ⟨u p.1 * (p.2 : G), Y.mul_mem (hu_mem p.1) (derivedOf_le Y p.2.2)⟩
  have hF_inj : Function.Injective F := by
    rintro ⟨i, n⟩ ⟨j, m⟩ h
    have hG : u i * (n : G) = u j * (m : G) := by
      simpa [F] using congrArg Subtype.val h
    have h1 : (u j)⁻¹ * u i = (m : G) * (n : G)⁻¹ := by
      calc (u j)⁻¹ * u i = (u j)⁻¹ * (u i * (n : G)) * (n : G)⁻¹ := by group
        _ = (u j)⁻¹ * (u j * (m : G)) * (n : G)⁻¹ := by rw [hG]
        _ = (m : G) * (n : G)⁻¹ := by group
    have hmem : u j * u i ∈ Y' := by
      rw [show u j * u i = (m : G) * (n : G)⁻¹ from by simpa [hinv_u j] using h1]
      exact Y'.mul_mem m.2 (Y'.inv_mem n.2)
    have hji : j = i := hkey j i hmem
    have hnm : n = m := by
      apply Subtype.ext
      exact mul_left_cancel (by rw [hji] at hG; exact hG)
    exact Prod.ext hji.symm hnm
  have hdom : Nat.card (Fin 4 × ↥Y') = 3840 := by
    rw [Nat.card_prod, Nat.card_fin, hY'card']
  have hF_bij : Function.Bijective F :=
    hF_inj.bijective_of_nat_card_le (by simp [hYcard, hdom])
  obtain ⟨⟨i, n⟩, hn⟩ := hF_bij.surjective ⟨y, hy⟩
  have hyu : y = u i * (n : G) := by
    have := congrArg Subtype.val hn
    simpa [F] using this.symm
  fin_cases i
  · exact ⟨(n : G), n.2, Or.inl (by simpa [u] using hyu)⟩
  · exact ⟨(n : G), n.2, Or.inr (Or.inl (by simpa [u] using hyu))⟩
  · exact ⟨(n : G), n.2, Or.inr (Or.inr (Or.inl (by simpa [u] using hyu)))⟩
  · exact ⟨(n : G), n.2, Or.inr (Or.inr (Or.inr (by simpa [u] using hyu)))⟩

theorem decomp_Y (h : F5Std a z) {w x : G} (hw : IsConj z w) (hx : IsConj a x)
    (hwx : IsConj z (w * x)) :
    ∀ y ∈ Gxy w x, ∃ u ∈ derivedOf (Gxy w x), y = u ∨ y = w * u ∨ y = x * u ∨ y = w * x * u :=
  decomp_Y_of_base h.toF5Base hw hx hwx

theorem exists_eta_Gz (h : F5Std a z) {w x : G} (hw : IsConj z w) (hx : IsConj a x)
    (hwx : IsConj z (w * x)) :
    ∃ η : G → G, IsIsoOn (Gx w) (Gx w) η ∧ η w = w ∧ η x = x ∧
      ¬ ∃ g ∈ derivedOf (Gxy w x), ∀ y ∈ derivedOf (Gxy w x), η y = g * y * g⁻¹ :=
  exists_eta_Gz_of_std h hw hx hwx

theorem out_Y (h : F5Std a z) {w x : G} (hw : IsConj z w) (hx : IsConj a x)
    (hwx : IsConj z (w * x)) {ψ₁ ψ₂ : G → G}
    (h₁ : IsIsoOn (derivedOf (Gxy w x)) (derivedOf (Gxy w x)) ψ₁)
    (h₂ : IsIsoOn (derivedOf (Gxy w x)) (derivedOf (Gxy w x)) ψ₂)
    (n₁ : ¬ ∃ g ∈ derivedOf (Gxy w x), ∀ y ∈ derivedOf (Gxy w x), ψ₁ y = g * y * g⁻¹)
    (n₂ : ¬ ∃ g ∈ derivedOf (Gxy w x), ∀ y ∈ derivedOf (Gxy w x), ψ₂ y = g * y * g⁻¹) :
    ∃ g ∈ derivedOf (Gxy w x), ∀ y ∈ derivedOf (Gxy w x), ψ₁ (ψ₂ y) = g * y * g⁻¹ :=
  out_Y_of_base h.toF5Base hw hx hwx h₁ h₂ n₁ n₂

end CFSG.EvenSporadicStandard.HNRecog.Section4
