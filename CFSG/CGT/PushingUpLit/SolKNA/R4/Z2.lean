module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.Std
public import CFSG.ClassicalInvolution.AschTight.T6ASD
public import CFSG.ClassicalInvolution.Q3.Q3T6OpenSDMuC
public import CFSG.ClassicalInvolution.Q3.Q3T6OpenSDType2
public import CFSG.ClassicalInvolution.Q3.TL3S8Four
public import CFSG.ClassicalInvolution.Q3.TL3S8Mu
public import CFSG.ClassicalInvolution.Q3.TL3S8Zstar

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3
open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.Q3T6

variable {G : Type} [Group G] [Finite G] {r : ℕ} {R : Subgroup G} {S : Sylow 2 R} {t : G}
  {T : Sylow 2 G}

namespace StdR

theorem muZ2OrS3 (h : StdR r R S t T) {W : Subgroup G}
    (hW : W ∈ WSet (CoreAssembly.conjClass (tightCore R))) :
    MuIsoZ2 (CoreAssembly.conjClass (tightCore R)) W ∨
      MuIsoS3 (CoreAssembly.conjClass (tightCore R)) W := by
  by_cases hex : ∃ J ∈ CoreAssembly.conjClass (tightCore R),
      (omegaStarNbr (CoreAssembly.conjClass (tightCore R)) J).Nonempty
  · exact Or.inr (Q3T6.Mu.muIsoS3_of_shape h.partIHypG hW h.edgeless hex)
  · refine Or.inl (Q3T6.Mu.muIsoZ2_of_shape h.partIHypG hW
      ⟨tightCore R, CoreAssembly.mem_conjClass_self _⟩ fun J hJ => ?_)
    exact Set.not_nonempty_iff_eq_empty.mp fun hne => hex ⟨J, hJ, hne⟩

theorem not_allTypeTwo_of_muIsoS3 (h : StdR r R S t T) {W : Subgroup G}
    (hW : W ∈ WSet (CoreAssembly.conjClass (tightCore R)))
    (hS3 : MuIsoS3 (CoreAssembly.conjClass (tightCore R)) W) : ¬ AllTypeTwo (tightCore R) t := by
  intro hA
  refine TightSylowStd.not_muIsoZ2_of_muIsoS3 hS3 (Q3T6.Mu.muIsoZ2_of_shape h.partIHypG hW
    ⟨tightCore R, CoreAssembly.mem_conjClass_self _⟩ fun J hJ => ?_)
  refine Set.eq_empty_of_forall_notMem ?_
  rintro J' ⟨hJ', hne, U, hU, hUJ', hUN⟩
  obtain ⟨w, hw⟩ := h.datum.exists_isUniqueInvolution_member hJ
  obtain ⟨u, hu⟩ := h.datum.exists_isUniqueInvolution_member hJ'
  obtain ⟨x, rfl⟩ := CoreAssembly.single_class (tightCore R) J hJ
  have hwx : x * t * x⁻¹ = w := (h.isUniqueInvolution.conj x).eq hw
  have hUw : U ≤ Subgroup.centralizer ({w} : Set G) :=
    (h.datum.normalizer_eq_centralizer_member hJ hw) ▸ hUN
  obtain ⟨R', hR', hUR', -, hidx⟩ := hU
  have h8 := Sec6Gen.eight_le_of_mem_RSet h.hypOmegaGen hR'
  have hcard : Nat.card R' = 2 * Nat.card U := by
    have h1 := Subgroup.relIndex_mul_card (H := U) (K := R')
    rw [inf_eq_left.mpr hUR', hidx] at h1
    exact h1.symm
  have hU2 : IsPGroup 2 U := (isPGroup_of_mem_rSet hR').to_le hUR'
  have huU : u ∈ U := S1911.mem_of_le_member hu hUJ' hU2 (by omega)
  have hwu : w ≠ u := by
    rintro rfl
    exact hne (h.datum.eq_of_isUniqueInvolution_member hJ' hJ hu hw)
  have hcomm : w * u = u * w := (Subgroup.mem_centralizer_singleton_iff.mp (hUw huU)).symm
  have h2 := hA J' hJ' u w hu ⟨x, hwx⟩ hwu hcomm U hU2 hUJ' hUw
  omega

theorem exists_conj_mem_sylow_ne [IsSimpleGroup (genFittingFStar G)]
    (hnab : ∃ a b : genFittingFStar G, a * b ≠ b * a) (h : StdR r R S t T) :
    ∃ g : G, g * t * g⁻¹ ∈ (T : Subgroup G) ∧ g * t * g⁻¹ ≠ t := by
  have hodd : CFSG.oddCore G = ⊥ := classicalInvolutionOddCore_eq_bot_of_fstar hnab
  have hord : orderOf t = 2 := h.datum.order
  have hzS : t ∈ (T : Subgroup G) := h.mem_T
  have hzZ : (⟨t, hzS⟩ : (T : Subgroup G)) ∈ Subgroup.center (T : Subgroup G) := by
    rw [Subgroup.mem_center_iff]
    intro s
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp (h.hTt s.2)
  have hne : t ≠ 1 := fun h1 => by
    have := hord
    rw [h1, orderOf_one] at this
    omega
  exact CFSG.ClassicalInvolution.exists_conj_mem_sylow_ne hodd T ⟨t, hzS⟩ hzZ
    (by rw [Subgroup.orderOf_mk]; exact hord) (not_mem_center_of_fstar hnab hne)

theorem twoSubgroupsFourGenerated_of_allTypeTwo [IsSimpleGroup (genFittingFStar G)]
    (hnab : ∃ a b : genFittingFStar G, a * b ≠ b * a) (hB3 : GoldschmidtB3Tmp)
    (h : StdR r R S t T) (hA : AllTypeTwo (tightCore R) t) :
    TwoSubgroupsFourGenerated (genFittingFStar G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht := h.setup194
  have hI := h.isUniqueInvolution
  have hS2 : IsSylow2Of ((S : Subgroup R).map R.subtype) (tightCore R) := h.sylow_core
  obtain ⟨Q₀, hQ₀⟩ := hS2.exists_sylow
  set R0 : Subgroup G := (Q₀ : Subgroup (tightCore R)).map (tightCore R).subtype with hR0
  have hR : R0 ∈ RSet (CoreAssembly.conjClass (tightCore R)) :=
    ⟨tightCore R, CoreAssembly.mem_conjClass_self _, Q₀, rfl⟩
  have hRK : R0 ≤ tightCore R := Subgroup.map_subtype_le _
  have hzR : IsUniqueInvolution R0 t := ht.isUniqueInvolution_of_mem_rSet_of_le hR hRK
  have hRT : R0 ≤ (T : Subgroup G) := by
    rw [hQ₀]
    exact h.hST
  have hSN : (T : Subgroup G) ≤ Subgroup.normalizer (R0 : Set G) := by
    intro s hs
    have hle : conjSubgroup s R0 ≤ (T : Subgroup G) := by
      intro x hx
      have hx' := mem_conjSubgroup_iff.mp hx
      have e : x = s * (s⁻¹ * x * s) * s⁻¹ := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hs (hRT hx')) (Subgroup.inv_mem _ hs)
    exact conjSubgroup_eq_self_iff.mp (ht.sylow_eq Q₀ T.isPGroup' hRT hle)
  have hSz : (T : Subgroup G) ≤ Subgroup.centralizer ({t} : Set G) := h.hTt
  have hSKR : (T : Subgroup G) ⊓ tightCore R ≤ R0 := by
    have h2 : IsPGroup 2 (((T : Subgroup G) ⊓ tightCore R).subgroupOf (tightCore R)) :=
      (T.isPGroup'.to_le inf_le_left).comap_subtype
    have hle : (Q₀ : Subgroup (tightCore R)) ≤
        ((T : Subgroup G) ⊓ tightCore R).subgroupOf (tightCore R) := by
      intro x hx
      exact Subgroup.mem_subgroupOf.mpr ⟨hRT ⟨x, hx, rfl⟩, x.2⟩
    have heq := Q₀.3 h2 hle
    intro x hx
    have hxK : x ∈ tightCore R := hx.2
    have : (⟨x, hxK⟩ : tightCore R) ∈ ((T : Subgroup G) ⊓ tightCore R).subgroupOf (tightCore R) :=
      Subgroup.mem_subgroupOf.mpr hx
    rw [heq] at this
    exact ⟨⟨x, hxK⟩, this, rfl⟩
  obtain ⟨g, htS, htz⟩ := h.exists_conj_mem_sylow_ne hnab
  set t' := g * t * g⁻¹ with ht'def
  set P := R0 ⊔ Subgroup.zpowers t' with hPdef
  have hPS : P ≤ (T : Subgroup G) := sup_le hRT (Subgroup.zpowers_le.mpr htS)
  have htzc : t' * t = t * t' := Subgroup.mem_centralizer_singleton_iff.mp (hSz htS)
  have hsd := SD.isSemidihedral_sup_of_allTypeTwo ht hA hR hRK (hSN htS) htzc htz
  obtain ⟨a, b, M, hsdd⟩ := exists_sdData (T.isPGroup'.to_le hPS) hsd
  have hcl : fusionStronglyClosed (P : Set G) T := by
    intro x hx y hy
    have := SD.mem_sup_of_conj_mem ht hA hR hRK hRT hSKR hSN hSz htS htz hx (y := y⁻¹)
      (by rwa [inv_inv])
    rwa [inv_inv] at this
  have hNC : ∀ n ∈ Subgroup.normalizer (P : Set G), ∃ k : ℕ,
      n ^ (2 ^ k) ∈ Subgroup.centralizer (P : Set G) := by
    intro n hn
    obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos n).ne'
    refine ⟨k, hsdd.mem_centralizer_of_odd (Subgroup.pow_mem _ hn _) ?_⟩
    rw [orderOf_pow' n (pow_ne_zero _ two_ne_zero), hkm,
      Nat.gcd_mul_right_left, Nat.mul_div_cancel_left _ (by positivity)]
    exact hm
  have hB := hB3 G T P hPS hcl hNC
  set N : Subgroup G := Subgroup.normalClosure (P : Set G) with hNdef
  have hNn : N.Normal := Subgroup.normalClosure_normal
  have htN : t ∈ N := Subgroup.le_normalClosure (Subgroup.mem_sup_left hzR.mem)
  have hFN : genFittingFStar G ≤ N := genFittingFStar_le_of_normal hnab hNn htN hI.ne_one
  have hTN : (T : Subgroup G) ⊓ N = P :=
    hB.2.2 _ inf_le_right (T.isPGroup'.to_le inf_le_left)
      (le_inf hPS (Subgroup.le_normalClosure))
  have hAP : ∀ X : Subgroup G, IsPGroup 2 X → X ≤ genFittingFStar G →
      ∃ g' : G, X ≤ conjSub g' P := by
    intro X hX2 hXF
    obtain ⟨T', hXT'⟩ := hX2.exists_le_sylow
    obtain ⟨g', hg'⟩ := MulAction.exists_smul_eq G T T'
    have hT' : (T' : Subgroup G) = conjSub g' (T : Subgroup G) := by
      rw [← hg', Sylow.coe_subgroup_smul]
      rfl
    refine ⟨g', fun x hx => ?_⟩
    have hxT : x ∈ conjSub g' (T : Subgroup G) := hT' ▸ hXT' hx
    rw [mem_conjSub_iff] at hxT ⊢
    have hxN : g'⁻¹ * x * g' ∈ N := by
      have := hNn.conj_mem x (hFN (hXF hx)) g'⁻¹
      simpa using this
    rw [← hTN]
    exact ⟨hxT, hxN⟩
  refine twoSubgroupsFourGenerated_of_conj_le (fun Q hQP => ?_) hAP
  obtain ⟨c, d, hcd⟩ := T6A.exists_closure_pair_eq hQP fun x hx y hy hxa hya =>
    T6A.sdData_inv_mul_mem_zpowers hsdd hx hy hxa hya
  refine ⟨{c, d}, (Finset.card_insert_le _ _).trans (by simp), ?_⟩
  rw [Finset.coe_insert, Finset.coe_singleton, hcd]

theorem not_muIsoZ2 [IsSimpleGroup (genFittingFStar G)]
    (hnab : ∃ a b : genFittingFStar G, a * b ≠ b * a) (hB3 : GoldschmidtB3Tmp)
    {R : Subgroup G} {S : Sylow 2 R} {t : G} {T : Sylow 2 G} (h : StdR r R S t T)
    {W : Subgroup G} (hW : W ∈ WSet (CoreAssembly.conjClass (tightCore R))) :
    ¬ MuIsoZ2 (CoreAssembly.conjClass (tightCore R)) W := by
  intro hZ
  have hst := SD.omegaStarNbr_eq_empty_of_muIsoZ2 muS3OfShape3 h.partIHypG hW h.edgeless hZ
  have hA := SD.allTypeTwo_of_omegaStarNbr_eq_empty h.hypOmegaGen h.edgeless hst
    h.isUniqueInvolution
  exact h.notFour (h.twoSubgroupsFourGenerated_of_allTypeTwo hnab hB3 hA)

end StdR

end CFSG.CGT.PushingUpLit.SolKNA.R4
