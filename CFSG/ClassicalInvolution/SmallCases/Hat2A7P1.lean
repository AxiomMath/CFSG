module

public import CFSG.ClassicalInvolution.Q3.Q3CLKey
public import CFSG.ClassicalInvolution.Q3.Q3CLNine3

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Hat2A7P1

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

structure ClassicalClause8 (Ω : Set (Subgroup G)) : Prop where
  subnormal : ∀ K ∈ Ω, ∃ z : G, z ∈ K ∧ orderOf z = 2 ∧
    IsSubnormal K (Subgroup.centralizer ({z} : Set G))
  sylow16 : ∀ J ∈ Ω, ∀ R : Subgroup G, IsSylow2In R J → 16 ≤ Nat.card ↥R
  odd8 : ∀ J ∈ Ω, ∀ u d : G, u ∈ J → IsPGroup 2 (Subgroup.zpowers u) → 8 ≤ orderOf u →
    d ∈ J → d * u = u * d → Odd (orderOf d) → d ∈ oddCoreOf J

structure PartIHypG8 (Ω : Set (Subgroup G)) : Prop where
  hyp : HypOmegaGen Ω
  cls : ClassicalClause8 Ω
  aEmpty : ∀ J ∈ Ω, AEmpty Ω J

omit [Group G] in
theorem ClassicalClause8.isSubnormal_of_uniqueInvolution {G : Type} [Group G]
    {Ω : Set (Subgroup G)} (hcl : ClassicalClause8 Ω) {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsUniqueInvolution K z) : IsSubnormal K (Subgroup.centralizer ({z} : Set G)) := by
  obtain ⟨z', hz'K, hz'o, hz'⟩ := hcl.subnormal K hK
  have hz'z : z' = z := by
    have hsq : z' * z' = 1 := by
      have := pow_orderOf_eq_one z'
      rwa [hz'o, pow_two] at this
    rcases hz.unique z' hz'K hsq with h | h
    · exfalso
      rw [h, orderOf_one] at hz'o
      omega
    · exact h
  rw [hz'z] at hz'
  exact hz'

variable [Finite G] {W : Subgroup G}

namespace Sec7

open CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7
  CFSG.ClassicalInvolution.Q3.Q3CL.Sec7

theorem mem_oddCoreOf_of_odd (hcl : ClassicalClause8 Ω) {J W : Subgroup G} (hJ : J ∈ Ω) {u : G}
    (huJ : u ∈ J) (huW : u ∈ W) (hu2 : IsPGroup 2 (Subgroup.zpowers u)) (hu8 : 8 ≤ orderOf u)
    {d : G} (hdC : d ∈ J ⊓ Subgroup.centralizer (W : Set G)) (hodd : Odd (orderOf d)) :
    d ∈ oddCoreOf (J ⊓ Subgroup.centralizer (W : Set G)) := by
  set C := J ⊓ Subgroup.centralizer (W : Set G) with hCdef
  set D := C ⊓ oddCoreOf J with hDdef
  have hCJ : C ≤ J := inf_le_left
  have hdu : d * u = u * d :=
    ((Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hdC).2) u huW).symm
  have hdJ : d ∈ oddCoreOf J := hcl.odd8 J hJ u d huJ hu2 hu8 (hCJ hdC) hdu hodd
  have hDodd : Odd (Nat.card D) :=
    (oddCoreOf_odd_natCard J).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right)
  have hCND : C ≤ Subgroup.normalizer (D : Set G) := fun c hc =>
    mem_normalizer_inf (Subgroup.le_normalizer hc)
      (mem_normalizer_oddCoreOf_of_mem_normalizer (Subgroup.le_normalizer (hCJ hc)))
  have h1 := Balance.le_oddCoreIn_of_normalizes (inf_le_left : D ≤ C) hCND hDodd
  rw [← oddCoreOf_eq_oddCoreIn] at h1
  exact h1 ⟨hdC, hdJ⟩

theorem exists_pow_two_pow_mem (hcl : ClassicalClause8 Ω) {J W : Subgroup G} (hJ : J ∈ Ω)
    (hWJ : W ≤ Subgroup.normalizer (J : Set G)) (hUc : IsCyclic ↥(J ⊓ W))
    (hU2 : IsPGroup 2 ↥(J ⊓ W)) {u : G} (huU : u ∈ J ⊓ W) (hu8 : 8 ≤ orderOf u) {h : G}
    (hhJ : h ∈ J) (hhW : h ∈ Subgroup.normalizer (W : Set G)) :
    ∃ n : ℕ, h ^ (2 ^ n) ∈ oddCoreOf (J ⊓ Subgroup.centralizer (W : Set G)) := by
  obtain ⟨n, m, hm, hnm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos h).ne'
  refine ⟨n, ?_⟩
  have hdvd : 2 ^ n ∣ orderOf h := ⟨m, hnm⟩
  have hord : orderOf (h ^ (2 ^ n)) = m := by
    rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) hdvd, hnm,
      Nat.mul_div_cancel_left _ (pow_pos two_pos n)]
  have hodd : Odd (orderOf (h ^ (2 ^ n))) := hord ▸ hm
  have hJ' : h ^ (2 ^ n) ∈ J := J.pow_mem hhJ _
  have hW' : h ^ (2 ^ n) ∈ Subgroup.normalizer (W : Set G) := Subgroup.pow_mem _ hhW _
  have hC := mem_centralizer_of_odd hWJ hUc hU2 hJ' hW' hodd
  exact mem_oddCoreOf_of_odd hcl hJ (Subgroup.mem_inf.mp huU).1 (Subgroup.mem_inf.mp huU).2
    (hU2.to_le (Subgroup.zpowers_le.mpr huU)) hu8 ⟨hJ', hC⟩ hodd


theorem oddCoreOf_inf_centralizer_le_OCW (hcl : ClassicalClause8 Ω) {J W : Subgroup G}
    (hJ : J ∈ Ω) {z : G} (hz : IsUniqueInvolution J z) (hzW : z ∈ W) :
    oddCoreOf (J ⊓ Subgroup.centralizer (W : Set G)) ≤ OCW W := by
  have hsub := hcl.isSubnormal_of_uniqueInvolution hJ hz
  have hCW : Subgroup.centralizer (W : Set G) ≤ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hzW)
  have h1 := isSubnormal_inf hsub (Subgroup.centralizer (W : Set G))
  rw [inf_eq_right.mpr hCW] at h1
  rw [oddCoreOf_eq_oddCoreIn, OCW, oddCoreOf_eq_oddCoreIn]
  exact Balance.oddCoreIn_le_of_isSubnormal h1


theorem keyOn (hΩ : HypOmegaGen Ω) (hcl : ClassicalClause8 Ω) (habel : Sec7.EtaAbelian Ω)
    (h611 : Sec7.EtaMeets Ω) : KeyOn Ω := by
  intro W hW R hR T hT J hJ hRJ hTJ
  have hRsyl := isSylow2In_of_mem_RSet_of_le hΩ hR.1 hJ hRJ
  have h8 := Sec6Gen.eight_le_of_mem_RSet hΩ hR.1
  have hWJ := le_normalizer_of_mem_DSet hΩ habel h611 hW hR hJ hRJ
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
  have hUU := mem_USet_of_mem_etaG hη hU
  obtain ⟨R'', -, J'', hJ'', hR''J'', -, hUc, hcardU, hU4⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hUU
  have h16 := hcl.sylow16 J'' hJ'' R'' hR''J''
  have hU8 : 8 ≤ Nat.card ↥(J ⊓ W) := by omega
  have hU2 : IsPGroup 2 ↥(J ⊓ W) := Sec6Gen.isPGroup_of_mem_USet hΩ hUU
  obtain ⟨g, hg⟩ := hUc.exists_generator
  have hgord : orderOf (g : G) = Nat.card ↥(J ⊓ W) := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg]
  have hg8 : 8 ≤ orderOf (g : G) := hgord ▸ hU8
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution hΩ hJ
  have hzU : z ∈ J ⊓ W := hz.mem_of_le inf_le_left hU2 (by omega)
  have hOH : oddCoreOf (J ⊓ Subgroup.centralizer (W : Set G)) ≤
      J ⊓ Subgroup.normalizer (W : Set G) :=
    (oddCoreOf_le_self _).trans
      (inf_le_inf_left J (Subgroup.centralizer_le_normalizer (W : Set G)))
  have hHO : J ⊓ Subgroup.normalizer (W : Set G) ≤
      Subgroup.normalizer (oddCoreOf (J ⊓ Subgroup.centralizer (W : Set G)) : Set G) :=
    fun h hh => mem_normalizer_oddCoreOf_of_mem_normalizer
      (mem_normalizer_inf (Subgroup.le_normalizer (Subgroup.mem_inf.mp hh).1)
        (normalizer_le_normalizer_centralizer W (Subgroup.mem_inf.mp hh).2))
  have hRH : IsSylow2In R (J ⊓ Subgroup.normalizer (W : Set G)) :=
    ⟨le_inf hRJ hR.2, hRsyl.2.1, fun V' hV'H hV'2 hRV' =>
      hRsyl.2.2 V' (hV'H.trans inf_le_left) hV'2 hRV'⟩
  have hle := le_sup_of_pow_mem hOH hHO hRH fun h hh =>
    exists_pow_two_pow_mem hcl hJ hWJ hUc hU2 g.2 hg8 (Subgroup.mem_inf.mp hh).1
      (Subgroup.mem_inf.mp hh).2
  have hOX := oddCoreOf_inf_centralizer_le_OCW hcl hJ hz (Subgroup.mem_inf.mp hzU).2
  intro t ht
  exact sup_le (le_sup_left.trans le_sup_left) (hOX.trans le_sup_right) (hle ⟨hTJ ht, hT.2 ht⟩)


theorem l7_1Key (hP : PartIHypG8 Ω) : KeyOn Ω :=
  keyOn hP.hyp hP.cls
    (fun _ ⟨_, hS, hinv⟩ => (Sec6Gen.eta_abelian_of_cyc66 hP.hyp (Sec6Gen.cyc66 hP.hyp) hS hinv).1)
    (Sec6Gen.l6_11Gen G Ω hP.hyp)


end Sec7

open CFSG.ClassicalInvolution.Asc77.AscP1Nine3

theorem l9_3 (hP : PartIHypG8 Ω) :
    ∀ K ∈ Ω, ∀ z : G, IsUniqueInvolution K z →
      ∀ S : Subgroup G, IsSylow2In S (Subgroup.centralizer ({z} : Set G)) →
        ∀ U : Subgroup G, U ≤ S → IsElemAbelian2 U 2 → ∀ d ∈ U, d ≠ 1 →
          gamma1 U (S ⊓ ⨆ L ∈ twinSet Ω K, L) ≤ Subgroup.centralizer ({d} : Set G) →
            ∃ x ∈ K, orderOf x = 4 ∧ x * d = d * x := by
  intro K hK z hz S hS U hUS hU d hdU hd1 hΓ
  obtain ⟨hΩ, hcl, -⟩ := hP
  have h67 : CFSG.ClassicalInvolution.Q3.Q3CP.L67Gen := CFSG.ClassicalInvolution.Q3.Q3CP.l67Gen
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
      obtain ⟨x, hx, hxo, hc⟩ := Q3.Q3CL.AscP1Nine3.exists_centralizer_orderFour_stab2 h67 hΩ hK hR hRS hS2
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
      obtain ⟨x, hx, hxo, hc⟩ := Q3.Q3CL.AscP1Nine3.exists_centralizer_orderFour_stab2 h67 hΩ hK hR hRS hS2
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
        obtain ⟨x, hx, hxo, hc⟩ := Q3.Q3CL.AscP1Nine3.exists_centralizer_orderFour_stab2 h67 hΩ hK hR hRS
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
      · exact Q3.Q3CL.AscP1Nine3.false_of_all_move h67 hΩ hK hR hRS hS2 huS hdUS hu2 hfu hfd hfdu hRX
          (hconjR u huS) (fun y hy hyu => hΓ' u huU hu1 y hy hyu)



end CFSG.ClassicalInvolution.Hat2A7P1
