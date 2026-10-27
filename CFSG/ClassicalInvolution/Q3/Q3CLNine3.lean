module

public import CFSG.ClassicalInvolution.Q3.Q3CLApi
public import CFSG.ClassicalInvolution.Q3.Q3CPSix67

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3CL

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {W : Subgroup G}

namespace AscP1Nine3

open CFSG.ClassicalInvolution.Asc77.AscP1Nine3

theorem commutes_conjSub_of_not_fixed (h67 : Q3CP.L67Gen) (hΩ : HypOmegaGen Ω)
    {K R S : Subgroup G} (hK : K ∈ Ω)
    (hR : IsSylow2In R K) (hRS : R ≤ S) (hS : IsPGroup 2 S) {a : G} (haS : a ∈ S)
    (haK : conjSub a K ≠ K) : Commutes R (conjSub a R) := by
  have hRset : R ∈ RSet Ω := mem_RSet_of_isSylow2In hK hR
  have hRa : conjSub a R ∈ RSet Ω := RSet.conj hΩ.conjInvariant hRset a
  have hRaS : conjSub a R ≤ S := by
    have := conjSub_mono (n := a) hRS
    rwa [conjSub_eq_self_of_mem haS] at this
  obtain ⟨S', hSS'⟩ := hS.exists_le_sylow
  have h4 : 4 ≤ Nat.card R := by
    have := Sec6Gen.eight_le_of_mem_RSet hΩ hRset
    omega
  have hne : R ≠ conjSub a R := by
    intro h
    apply haK
    refine Sec6Gen.eq_of_le_of_le hΩ (hΩ.conjInvariant a K hK) hK hR.2.1 h4 ?_ hR.1
    calc R = conjSub a R := h
      _ ≤ conjSub a K := conjSub_mono hR.1
  exact h67 G Ω hΩ S' R hRset (conjSub a R) hRa (hRS.trans hSS') (hRaS.trans hSS') hne

theorem eq_one_or_eq_of_mem_inf_conjSub (hΩ : HypOmegaGen Ω)
    {K R : Subgroup G} (hK : K ∈ Ω) (hR : IsSylow2In R K) {z : G} (hz : IsUniqueInvolution K z)
    {a : G} (haK : conjSub a K ≠ K) {e : G} (he : e ∈ R ⊓ conjSub a R) : e = 1 ∨ e = z := by
  have hA2 : IsPGroup 2 ↥(R ⊓ conjSub a R) := hR.2.1.to_le inf_le_left
  have hcard : Nat.card ↥(R ⊓ conjSub a R) ≤ 2 :=
    Sec6Gen.card_le_two_of_le_inf hΩ hK (hΩ.conjInvariant a K hK) (fun h => haK h.symm) hA2
      (inf_le_left.trans hR.1) (inf_le_right.trans (conjSub_mono hR.1))
  have hdvd : orderOf e ∣ Nat.card ↥(R ⊓ conjSub a R) := Subgroup.orderOf_dvd_natCard _ he
  have hle : orderOf e ≤ 2 :=
    (Nat.le_of_dvd Nat.card_pos hdvd).trans hcard
  have hsq : e * e = 1 := by
    have h2 : orderOf e ∣ 2 := by
      rcases Nat.lt_or_ge (orderOf e) 2 with h | h
      · have : orderOf e = 1 := by
          have := orderOf_pos e
          omega
        rw [this]
        exact one_dvd 2
      · have : orderOf e = 2 := le_antisymm hle h
        rw [this]
    rw [← pow_two]
    exact orderOf_dvd_iff_pow_eq_one.mp h2
  exact hz.unique e (hR.1 he.1) hsq

theorem exists_centralizer_orderFour_stab2 (h67 : Q3CP.L67Gen) (hΩ : HypOmegaGen Ω)
    {K R S X : Subgroup G} (hK : K ∈ Ω)
    (hR : IsSylow2In R K) (hRS : R ≤ S) (hS : IsPGroup 2 S) {z : G} (hz : IsUniqueInvolution K z)
    {v a b d : G} (hvS : v ∈ S) (haS : a ∈ S) (hv2 : v * v = 1) (ha2 : a * a = 1)
    (hva : v * a = a * v) (hb : b = v * a) (hvR : conjSub v R = R)
    (haK : conjSub a K ≠ K) (hd : d = v ∨ d = a ∨ d = b) (hXR : R ≤ X) (hXa : conjSub a R ≤ X)
    (hXb : conjSub b R ≤ X)
    (hΓ : ∀ w ∈ ({a, b} : Set G), ∀ y ∈ X, y * w = w * y → y * d = d * y) :
    ∃ x ∈ R, orderOf x = 4 ∧ x * v = v * x := by
  have hRset : R ∈ RSet Ω := mem_RSet_of_isSylow2In hK hR
  have h8 : 8 ≤ Nat.card R := Sec6Gen.eight_le_of_mem_RSet hΩ hRset
  have hab : a * b = v := by
    rw [hb]
    calc a * (v * a) = (a * v) * a := by group
      _ = (v * a) * a := by rw [← hva]
      _ = v * (a * a) := by group
      _ = v := by rw [ha2, mul_one]
  have hba : b * a = v := by
    rw [hb]
    calc v * a * a = v * (a * a) := by group
      _ = v := by rw [ha2, mul_one]
  have hb2 : b * b = 1 := by
    rw [hb]
    calc v * a * (v * a) = v * (a * v) * a := by group
      _ = v * (v * a) * a := by rw [← hva]
      _ = (v * v) * (a * a) := by group
      _ = 1 := by rw [hv2, ha2, one_mul]
  have hbS : b ∈ S := by rw [hb]; exact S.mul_mem hvS haS
  have hRb : conjSub b R = conjSub a R := by
    rw [hb, hva, conjSub_mul, hvR]
  have hcomm_a : Commutes R (conjSub a R) :=
    commutes_conjSub_of_not_fixed h67 hΩ hK hR hRS hS haS haK
  have hcomm_b : Commutes R (conjSub b R) := hRb ▸ hcomm_a
  have hcent : ∀ x ∈ R, x⁻¹ * (v * x * v⁻¹) = 1 ∨ x⁻¹ * (v * x * v⁻¹) = z := by
    intro x hx
    have hx'R : v * x * v⁻¹ ∈ R := hvR ▸ conj_mem_conjSub hx
    have hxa : a * x * a⁻¹ ∈ conjSub a R := conj_mem_conjSub hx
    have hxb : b * x * b⁻¹ ∈ conjSub a R := hRb ▸ conj_mem_conjSub hx
    have hx'a : a * (v * x * v⁻¹) * a⁻¹ ∈ conjSub a R := conj_mem_conjSub hx'R
    have hinf : x⁻¹ * (v * x * v⁻¹) ∈ R ⊓ conjSub a R := by
      rcases hd with h | h | h
      ·
        have hyX : x * (a * x * a⁻¹) ∈ X := X.mul_mem (hXR hx) (hXa hxa)
        have hyC := (Subgroup.mem_centralizer_singleton_iff.mp
          (mul_conj_mem_inf_centralizer hRS haS ha2 hcomm_a hx).2)
        have h1 := hΓ a (by simp) _ hyX hyC
        rw [h] at h1
        have h2 : v * (x * (a * x * a⁻¹)) * v⁻¹ = x * (a * x * a⁻¹) := by
          calc v * (x * (a * x * a⁻¹)) * v⁻¹ = (x * (a * x * a⁻¹)) * v * v⁻¹ := by rw [← h1]
            _ = x * (a * x * a⁻¹) := by group
        refine inv_mul_mem_inf_of_relation hx hx'R hx'a hxa ?_
        calc v * x * v⁻¹ * (a * (v * x * v⁻¹) * a⁻¹)
            = v * (x * (a * x * a⁻¹)) * v⁻¹ := by
              calc v * x * v⁻¹ * (a * (v * x * v⁻¹) * a⁻¹)
                  = v * x * v⁻¹ * ((a * v) * x * (a * v)⁻¹) := by group
                _ = v * x * v⁻¹ * ((v * a) * x * (v * a)⁻¹) := by rw [hva]
                _ = v * (x * (a * x * a⁻¹)) * v⁻¹ := by group
          _ = x * (a * x * a⁻¹) := h2
      ·
        have hyX : x * (b * x * b⁻¹) ∈ X := X.mul_mem (hXR hx) (hXb (conj_mem_conjSub hx))
        have hyC := (Subgroup.mem_centralizer_singleton_iff.mp
          (mul_conj_mem_inf_centralizer hRS hbS hb2 hcomm_b hx).2)
        have h1 := hΓ b (by simp) _ hyX hyC
        rw [h] at h1
        have h2 : a * (x * (b * x * b⁻¹)) * a⁻¹ = x * (b * x * b⁻¹) := by
          calc a * (x * (b * x * b⁻¹)) * a⁻¹ = (x * (b * x * b⁻¹)) * a * a⁻¹ := by rw [← h1]
            _ = x * (b * x * b⁻¹) := by group
        have hc : (v * x * v⁻¹) * (a * x * a⁻¹) = (a * x * a⁻¹) * (v * x * v⁻¹) :=
          hcomm_a _ hx'R _ hxa
        refine inv_mul_mem_inf_of_relation hx hx'R hxa hxb ?_
        rw [hc]
        calc a * x * a⁻¹ * (v * x * v⁻¹) = a * (x * (b * x * b⁻¹)) * a⁻¹ := by
              calc a * x * a⁻¹ * (v * x * v⁻¹) = a * x * a⁻¹ * ((a * b) * x * (a * b)⁻¹) := by
                    rw [hab]
                _ = a * (x * (b * x * b⁻¹)) * a⁻¹ := by group
          _ = x * (b * x * b⁻¹) := h2
      ·
        have hyX : x * (a * x * a⁻¹) ∈ X := X.mul_mem (hXR hx) (hXa hxa)
        have hyC := (Subgroup.mem_centralizer_singleton_iff.mp
          (mul_conj_mem_inf_centralizer hRS haS ha2 hcomm_a hx).2)
        have h1 := hΓ a (by simp) _ hyX hyC
        rw [h] at h1
        have h2 : b * (x * (a * x * a⁻¹)) * b⁻¹ = x * (a * x * a⁻¹) := by
          calc b * (x * (a * x * a⁻¹)) * b⁻¹ = (x * (a * x * a⁻¹)) * b * b⁻¹ := by rw [← h1]
            _ = x * (a * x * a⁻¹) := by group
        have hc : (v * x * v⁻¹) * (b * x * b⁻¹) = (b * x * b⁻¹) * (v * x * v⁻¹) :=
          hcomm_b _ hx'R _ (conj_mem_conjSub hx)
        refine inv_mul_mem_inf_of_relation hx hx'R hxb hxa ?_
        rw [hc]
        calc b * x * b⁻¹ * (v * x * v⁻¹) = b * (x * (a * x * a⁻¹)) * b⁻¹ := by
              calc b * x * b⁻¹ * (v * x * v⁻¹) = b * x * b⁻¹ * ((b * a) * x * (b * a)⁻¹) := by
                    rw [hba]
                _ = b * (x * (a * x * a⁻¹)) * b⁻¹ := by group
          _ = x * (a * x * a⁻¹) := h2
    exact eq_one_or_eq_of_mem_inf_conjSub hΩ hK hR hz haK hinf
  exact exists_centralizer_orderFour_of_central hz hR.1 hR.2.1 h8 hvR hcent

theorem false_of_all_move (h67 : Q3CP.L67Gen) (hΩ : HypOmegaGen Ω) {K R S X : Subgroup G}
    (hK : K ∈ Ω) (hR : IsSylow2In R K)
    (hRS : R ≤ S) (hS : IsPGroup 2 S) {u d : G} (huS : u ∈ S) (hdS : d ∈ S) (hu2 : u * u = 1)
    (huK : conjSub u K ≠ K) (hdK : conjSub d K ≠ K) (hduK : conjSub (d * u) K ≠ K)
    (hXR : R ≤ X) (hXu : conjSub u R ≤ X) (hΓ : ∀ y ∈ X, y * u = u * y → y * d = d * y) :
    False := by
  have hRset : R ∈ RSet Ω := mem_RSet_of_isSylow2In hK hR
  have hquat : IsQuatSub R := Sec6Gen.isQuatSub_of_mem_RSet hΩ hRset
  have hcomm_u : Commutes R (conjSub u R) :=
    commutes_conjSub_of_not_fixed h67 hΩ hK hR hRS hS huS huK
  have hcomm_d : Commutes R (conjSub d R) :=
    commutes_conjSub_of_not_fixed h67 hΩ hK hR hRS hS hdS hdK
  have hcomm_du : Commutes R (conjSub (d * u) R) :=
    commutes_conjSub_of_not_fixed h67 hΩ hK hR hRS hS (S.mul_mem hdS huS) hduK
  obtain ⟨x, hx, y', hy', hne⟩ := hquat.exists_not_commute
  have hxu : u * x * u⁻¹ ∈ conjSub u R := conj_mem_conjSub hx
  have hyX : x * (u * x * u⁻¹) ∈ X := X.mul_mem (hXR hx) (hXu hxu)
  have hyC := Subgroup.mem_centralizer_singleton_iff.mp
    (mul_conj_mem_inf_centralizer hRS huS hu2 hcomm_u hx).2
  have h1 := hΓ _ hyX hyC
  have h2 : d * (x * (u * x * u⁻¹)) * d⁻¹ = x * (u * x * u⁻¹) := by
    calc d * (x * (u * x * u⁻¹)) * d⁻¹ = (x * (u * x * u⁻¹)) * d * d⁻¹ := by rw [← h1]
      _ = x * (u * x * u⁻¹) := by group
  have hrel : x = (d * x * d⁻¹) * ((d * u) * x * (d * u)⁻¹) * (u * x * u⁻¹)⁻¹ := by
    calc x = (x * (u * x * u⁻¹)) * (u * x * u⁻¹)⁻¹ := by group
      _ = (d * (x * (u * x * u⁻¹)) * d⁻¹) * (u * x * u⁻¹)⁻¹ := by rw [h2]
      _ = _ := by group
  have c1 : Commute y' (u * x * u⁻¹) := (hcomm_u y' hy' _ hxu)
  have c2 : Commute y' (d * x * d⁻¹) := (hcomm_d y' hy' _ (conj_mem_conjSub hx))
  have c3 : Commute y' ((d * u) * x * (d * u)⁻¹) :=
    (hcomm_du y' hy' _ (conj_mem_conjSub hx))
  have hc : Commute y' x := by
    rw [hrel]
    exact (c2.mul_right c3).mul_right c1.inv_right
  exact hne hc.eq.symm

end AscP1Nine3

open CFSG.ClassicalInvolution.Asc77.AscP1Nine3

theorem l9_3 (hP : PartIHypG Ω) :
    ∀ K ∈ Ω, ∀ z : G, IsUniqueInvolution K z →
      ∀ S : Subgroup G, IsSylow2In S (Subgroup.centralizer ({z} : Set G)) →
        ∀ U : Subgroup G, U ≤ S → IsElemAbelian2 U 2 → ∀ d ∈ U, d ≠ 1 →
          gamma1 U (S ⊓ ⨆ L ∈ twinSet Ω K, L) ≤ Subgroup.centralizer ({d} : Set G) →
            ∃ x ∈ K, orderOf x = 4 ∧ x * d = d * x := by
  intro K hK z hz S hS U hUS hU d hdU hd1 hΓ
  obtain ⟨hΩ, hcl, -⟩ := hP
  have h67 : Q3CP.L67Gen := Q3CP.l67Gen
  by_contra hno
  have hS2 : IsPGroup 2 S := hS.2.1
  set C : Subgroup G := Subgroup.centralizer ({z} : Set G) with hC
  have hKC : K ≤ C := le_centralizer_of_uniqueInvolution hz
  have hsub : IsSubnormal K C := hcl.isSubnormal_of_uniqueInvolution hK hz
  have hR : IsSylow2In (S ⊓ K) K := isSylow2In_inf_of_isSubnormal hS hsub
  set R : Subgroup G := S ⊓ K with hRdef
  have hRS : R ≤ S := inf_le_left
  have hRK : R ≤ K := inf_le_right
  have hRset : R ∈ RSet Ω := mem_RSet_of_isSylow2In hK hR
  have h8 : 8 ≤ Nat.card R := Sec6Gen.eight_le_of_mem_RSet hΩ hRset
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
      obtain ⟨x, hx, hxo, hc⟩ := AscP1Nine3.exists_centralizer_orderFour_stab2 h67 hΩ hK hR hRS hS2
        hz
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
      obtain ⟨x, hx, hxo, hc⟩ := AscP1Nine3.exists_centralizer_orderFour_stab2 h67 hΩ hK hR hRS hS2
        hz
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
        obtain ⟨x, hx, hxo, hc⟩ := AscP1Nine3.exists_centralizer_orderFour_stab2 h67 hΩ hK hR hRS
          hS2 hz
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
      · exact AscP1Nine3.false_of_all_move h67 hΩ hK hR hRS hS2 huS hdUS hu2 hfu hfd hfdu hRX
          (hconjR u huS) (fun y hy hyu => hΓ' u huU hu1 y hy hyu)


end CFSG.ClassicalInvolution.Q3.Q3CL
