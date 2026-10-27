module

public import CFSG.ClassicalInvolution.Asc77.AscT7HC1
public import CFSG.ClassicalInvolution.Asc77.AscT7HC3
import CFSG.ClassicalInvolution.Asc77.AscIHSectF
public import CFSG.ClassicalInvolution.Asc77.AscT7HLayer

public section

namespace CFSG.ClassicalInvolution.Asc77.T7H

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.ExactLayer AscE184Sect

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)} {c : G}

theorem isUniqueInvolution_exactCore (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω)
    (hcpg : IsPGroup 2 (Subgroup.zpowers c)) {K : Subgroup G} (hK : K ∈ tqMembers Ω c) {z : G}
    (hz : IsUniqueInvolution K z) : IsUniqueInvolution (exactCore c K) z := by
  rw [← secMember_zpowers_eq_exactCore hΩ hcpg hK.1 hK.2]
  exact isUniqueInvolution_secMember hp hΩ hcpg hK.1 (commutator_zpowers_le_iff.mpr hK.2) hz

@[expose] noncomputable def toBar (Ω : Set (Subgroup G)) (c x : G) (hx : x ∈ exactLayer Ω c) :
    ↥(exactLayer Ω c) ⧸ classicalInvolutionOddCore ↥(exactLayer Ω c) :=
  QuotientGroup.mk' (classicalInvolutionOddCore ↥(exactLayer Ω c)) ⟨x, hx⟩

theorem toBar_mul {x y : G} (hx : x ∈ exactLayer Ω c) (hy : y ∈ exactLayer Ω c) :
    toBar Ω c (x * y) ((exactLayer Ω c).mul_mem hx hy) = toBar Ω c x hx * toBar Ω c y hy := rfl

theorem mem_exactImg {K : Subgroup G} {x : G} (hxK : x ∈ exactCore c K)
    (hx : x ∈ exactLayer Ω c) : toBar Ω c x hx ∈ exactImg Ω c K :=
  Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hxK)


theorem exactImg_isUnique (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω)
    (hcpg : IsPGroup 2 (Subgroup.zpowers c)) {K : Subgroup G} (hK : K ∈ tqMembers Ω c) {z : G}
    (hz : IsUniqueInvolution K z) (hzE : z ∈ exactLayer Ω c) :
    IsUniqueInvolution (exactImg Ω c K) (toBar Ω c z hzE) := by
  have hz' := isUniqueInvolution_exactCore hp hΩ hcpg hK hz
  have h1 := isUniqueInvolution_subgroupOf hz' (exactCore_le_exactLayer hK)
  exact isUniqueInvolution_map_mk_of_odd
    (odd_natCard_inf (CFSG.ComponentClassification.OddCore.odd_card ↥(exactLayer Ω c)) _) h1


theorem eq_one_of_mem_odd_of_sq {H : Type} [Group H] {N : Subgroup H} (hN : Odd (Nat.card N))
    {y : H} (hy : y ∈ N) (h2 : y * y = 1) : y = 1 := by
  by_contra hne
  have hord : orderOf y = 2 := orderOf_eq_prime (by rw [pow_two]; exact h2) hne
  have h1 : orderOf y ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hy
  rw [hord] at h1
  exact (Nat.not_even_iff_odd.mpr hN) (even_iff_two_dvd.mpr h1)

theorem eq_of_toBar_eq {x y : G} (hx : x ∈ exactLayer Ω c) (hy : y ∈ exactLayer Ω c)
    (hx2 : x * x = 1) (hy2 : y * y = 1) (hxy : x * y = y * x)
    (h : toBar Ω c x hx = toBar Ω c y hy) : x = y := by
  have hw : (⟨x, hx⟩ : ↥(exactLayer Ω c))⁻¹ * ⟨y, hy⟩ ∈
      classicalInvolutionOddCore ↥(exactLayer Ω c) := QuotientGroup.eq.mp h
  have hw2 : ((⟨x, hx⟩ : ↥(exactLayer Ω c))⁻¹ * ⟨y, hy⟩) *
      ((⟨x, hx⟩ : ↥(exactLayer Ω c))⁻¹ * ⟨y, hy⟩) = 1 := by
    apply Subtype.ext
    have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
    show (x⁻¹ * y) * (x⁻¹ * y) = 1
    rw [hxi]
    calc (x * y) * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [hxy]
      _ = (x * x) * (y * y) := by group
      _ = 1 := by rw [hx2, hy2, mul_one]
  have := eq_one_of_mem_odd_of_sq (CFSG.ComponentClassification.OddCore.odd_card _) hw hw2
  have h1 : x⁻¹ * y = 1 := congrArg Subtype.val this
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  rw [hxi] at h1
  exact (inv_eq_of_mul_eq_one_right h1 : x⁻¹ = y).symm.trans hxi |>.symm


theorem layer_orth_six (hTSF : TwinSquareFact p) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmegaMod p f Ω) (hBelow : CITBelowU p f (Nat.card G))
    (hc2 : c * c = 1) (hnc : ¬ ({c} : Set G) ⊆ Subgroup.center G)
    {K K' L : Subgroup G} {z t b b' : G}
    (hK : K ∈ tqMembers Ω c) (hK' : K' ∈ tqMembers Ω c) (hL : L ∈ tqMembers Ω c)
    (hz : IsUniqueInvolution K z) (hz' : IsUniqueInvolution K' z)
    (hperp : KPerp Ω K = {K, K'}) (hperp' : KPerp Ω K' = {K', K})
    (htL : IsUniqueInvolution L t) (hzt : z * t = t * z) (htz : t ≠ z)
    {R R' : Subgroup G} (hR : IsSylow2In R (exactCore c K)) (hR' : IsSylow2In R' (exactCore c K'))
    (hRR' : Commutes R R')
    (hb : b ∈ exactCore c K) (hb' : b' ∈ exactCore c K') (ob : b * b = z) (ob' : b' * b' = z)
    (hrel : t = b * b' * c) :
    LayerOrthType p f Ω c 6 (piSign p f) := by
  classical
  have hcpg := isPGroup_zpowers_of_sq_eq_one hc2
  set E := exactLayer Ω c with hE
  set N₀ := classicalInvolutionOddCore ↥E with hN₀
  have hN₀odd : Odd (Nat.card N₀) := CFSG.ComponentClassification.OddCore.odd_card ↥E
  have hΛ : HypOmegaMod p f (exactPair Ω c) := hypOmegaMod_exactPair hp hq hΩ hcpg
  have hΦ : HypOmegaMod p f (oddQuotientFamily (exactPair Ω c)) :=
    oddQuotHyp p f hp hq ↥E (exactPair Ω c) hΛ N₀ hN₀odd
  have hzK : z ∈ exactCore c K := (isUniqueInvolution_exactCore hp hΩ hcpg hK hz).mem
  have hzE : z ∈ E := exactCore_le_exactLayer hK hzK
  have htL' : t ∈ exactCore c L := (isUniqueInvolution_exactCore hp hΩ hcpg hL htL).mem
  have htE : t ∈ E := exactCore_le_exactLayer hL htL'
  have hbE : b ∈ E := exactCore_le_exactLayer hK hb
  have hb'E : b' ∈ E := exactCore_le_exactLayer hK' hb'
  have hcE : c ∈ E := by
    have : c = (b * b')⁻¹ * t := by rw [hrel]; group
    rw [this]
    exact E.mul_mem (E.inv_mem (E.mul_mem hbE hb'E)) htE
  have hz2 : z * z = 1 := hz.sq
  have ht2 : t * t = 1 := htL.sq
  have hA : exactImg Ω c K ∈ oddQuotientFamily (exactPair Ω c) := exactImg_mem hK
  have hA' : exactImg Ω c K' ∈ oddQuotientFamily (exactPair Ω c) := exactImg_mem hK'
  have hB : exactImg Ω c L ∈ oddQuotientFamily (exactPair Ω c) := exactImg_mem hL
  have hzA := exactImg_isUnique hp hΩ hcpg hK hz hzE
  have hzA' := exactImg_isUnique hp hΩ hcpg hK' hz' hzE
  have htB := exactImg_isUnique hp hΩ hcpg hL htL htE
  have hne : exactImg Ω c K ≠ exactImg Ω c K' := by
    refine map_ne_of_commutes_sylow (N := N₀) hp hΦ hN₀odd
      (M₁ := (exactCore c K).subgroupOf E) (M₂ := (exactCore c K').subgroupOf E)
      (V₁ := R.subgroupOf E) (V₂ := R'.subgroupOf E)
      ⟨_, exactCore_mem_exactFamily hK, exactCore_le_exactLayer hK, rfl⟩
      (hR.subgroupOf (exactCore_le_exactLayer hK)) (hR'.subgroupOf (exactCore_le_exactLayer hK'))
      ?_
    intro x hx y hy
    exact Subtype.ext (hRR' x (Subgroup.mem_subgroupOf.mp hx) y (Subgroup.mem_subgroupOf.mp hy))
  have hnbA : ∀ M ∈ oddQuotientFamily (exactPair Ω c),
      M ∈ omegaNbr (oddQuotientFamily (exactPair Ω c)) (exactImg Ω c K) → M = exactImg Ω c K' := by
    intro M hM hMn
    obtain ⟨J, hJ, rfl⟩ := exists_exactImg_of_mem hM
    exact exactImg_nbr_eq hp hq hΩ hcpg hK hperp hJ hMn
  have hnbA' : ∀ M ∈ oddQuotientFamily (exactPair Ω c),
      M ∈ omegaNbr (oddQuotientFamily (exactPair Ω c)) (exactImg Ω c K') → M = exactImg Ω c K := by
    intro M hM hMn
    obtain ⟨J, hJ, rfl⟩ := exists_exactImg_of_mem hM
    exact exactImg_nbr_eq hp hq hΩ hcpg hK' hperp' hJ hMn
  have hbarne : toBar Ω c t htE ≠ toBar Ω c z hzE := fun h =>
    htz (eq_of_toBar_eq htE hzE ht2 hz2 hzt.symm h)
  have hBA : exactImg Ω c L ≠ exactImg Ω c K := by
    intro h
    rw [h] at htB
    exact hbarne (htB.eq hzA)
  have hBA' : exactImg Ω c L ≠ exactImg Ω c K' := by
    intro h
    rw [h] at htB
    exact hbarne (htB.eq hzA')
  have hBn : exactImg Ω c L ∉ omegaNbr (oddQuotientFamily (exactPair Ω c)) (exactImg Ω c K) :=
    fun h => hBA' (hnbA _ hB h)
  have hBn' : exactImg Ω c L ∉ omegaNbr (oddQuotientFamily (exactPair Ω c)) (exactImg Ω c K') :=
    fun h => hBA (hnbA' _ hB h)
  have hpath : ∀ N, Relation.ReflTransGen (fun M N : Subgroup (↥E ⧸ N₀) =>
      N ∈ oddQuotientFamily (exactPair Ω c) ∧
        Disconnected.dAdj (oddQuotientFamily (exactPair Ω c)) M N)
      (exactImg Ω c K) N → N = exactImg Ω c K ∨ N = exactImg Ω c K' := by
    intro N hN
    induction hN with
    | refl => exact Or.inl rfl
    | tail hpre hstep ih =>
      rename_i M N'
      obtain ⟨hN'Φ, hadj⟩ := hstep
      have hMΦ : M ∈ oddQuotientFamily (exactPair Ω c) := by
        rcases ih with rfl | rfl
        · exact hA
        · exact hA'
      rcases ih with rfl | rfl
      · refine Or.inr (hnbA N' hN'Φ ?_)
        rcases hadj with h | h
        · exact h
        · exact T3.omegaNbr_symm (l6_2 p f) hp hq hΦ hN'Φ hMΦ h
      · refine Or.inl (hnbA' N' hN'Φ ?_)
        rcases hadj with h | h
        · exact h
        · exact T3.omegaNbr_symm (l6_2 p f) hp hq hΦ hN'Φ hMΦ h
  have hdisc : ¬ Disconnected.DConnected (oddQuotientFamily (exactPair Ω c)) := by
    intro hconn
    rcases hpath _ (hconn _ hA _ hB) with h | h
    · exact hBA h
    · exact hBA' h
  have hlt : Nat.card (↥E ⧸ N₀) < Nat.card G := by
    have h1 : Nat.card (↥E ⧸ N₀) ≤ Nat.card ↥E :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_card N₀)
    have h2 : Nat.card ↥E < Nat.card G := card_exactLayer_lt hnc
    omega
  obtain ⟨D⟩ := ih8_exists_omegaLie hBelow hΦ.conjInvariant hΦ.classical
    ⟨exactImg Ω c K, hA⟩ (CFSG.ComponentClassification.OddCore.quotient_corefree ↥E) hlt
  obtain ⟨i₀, hall⟩ := D.exists_comp_all hA hA' hB hnbA hBA hBA' hBn hBn'
  have hcard : D.card = 1 := D.card_eq_one_of_all_le hΦ hall
  have hgen : omegaGen (oddQuotientFamily (exactPair Ω c)) = ⊤ :=
    omegaGen_quotFamily_eq_top (exactPair Ω c) N₀
      (omegaGen_restrictFamily_eq_top (exactFamily Ω c) E (exactLayer_eq_iSup Ω c).symm)
  have hc1 : c ≠ 1 := by
    rintro rfl
    exact hnc (by intro x hx; rw [Set.mem_singleton_iff] at hx; subst hx; exact Subgroup.one_mem _)
  have heC : toBar Ω c c hcE ∈ Subgroup.center (↥E ⧸ N₀) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨y', rfl⟩ := QuotientGroup.mk'_surjective N₀ y
    show QuotientGroup.mk' N₀ y' * QuotientGroup.mk' N₀ ⟨c, hcE⟩ =
      QuotientGroup.mk' N₀ ⟨c, hcE⟩ * QuotientGroup.mk' N₀ y'
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp
      (exactLayer_le_centralizer Ω c y'.2)
  have hc2' : toBar Ω c c hcE * toBar Ω c c hcE = 1 := by
    unfold toBar
    rw [← map_mul]
    have : (⟨c, hcE⟩ : ↥E) * ⟨c, hcE⟩ = 1 := Subtype.ext hc2
    rw [this, map_one]
  have hc1' : toBar Ω c c hcE ≠ 1 := by
    intro h
    have hmem : (⟨c, hcE⟩ : ↥E) ∈ N₀ := (QuotientGroup.eq_one_iff _).mp h
    have := eq_one_of_mem_odd_of_sq hN₀odd hmem (Subtype.ext hc2)
    exact hc1 (congrArg Subtype.val this)
  have hrel' : toBar Ω c t htE = toBar Ω c b hbE * toBar Ω c b' hb'E * toBar Ω c c hcE := by
    have h1 : (⟨t, htE⟩ : ↥E) = ⟨b, hbE⟩ * ⟨b', hb'E⟩ * ⟨c, hcE⟩ := Subtype.ext hrel
    unfold toBar
    rw [h1, map_mul, map_mul]
  have ob₁ : toBar Ω c b hbE * toBar Ω c b hbE = toBar Ω c z hzE := by
    have h1 : (⟨b, hbE⟩ : ↥E) * ⟨b, hbE⟩ = ⟨z, hzE⟩ := Subtype.ext ob
    unfold toBar
    rw [← map_mul, h1]
  have ob₂ : toBar Ω c b' hb'E * toBar Ω c b' hb'E = toBar Ω c z hzE := by
    have h1 : (⟨b', hb'E⟩ : ↥E) * ⟨b', hb'E⟩ = ⟨z, hzE⟩ := Subtype.ext ob'
    unfold toBar
    rw [← map_mul, h1]
  have hframe : TwinFrame (oddQuotientFamily (exactPair Ω c)) (exactImg Ω c K)
      (exactImg Ω c K') (exactImg Ω c L) (toBar Ω c z hzE) (toBar Ω c b hbE)
      (toBar Ω c b' hb'E) (toBar Ω c t htE) (toBar Ω c c hcE) :=
    ⟨hA, hA', hB, hne, hzA, hzA', mem_exactImg hb hbE, mem_exactImg hb' hb'E, ob₁, ob₂, htB,
      heC, hc2', hc1', hrel'⟩
  have htag := twinFrame_tag hTSF hp hq hΦ D hcard hgen hdisc hframe i₀
  have hort : HasOrthType p f (oddQuotientFamily (exactPair Ω c)) 6 (piSign p f) := by
    rcases htag with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · have hπ : piSign p f = true := by unfold piSign; simp [h3]
      exact ⟨.PSL, 4, Or.inr (Or.inl ⟨rfl, hπ, rfl, rfl⟩), D, hcard, i₀, h1, h2⟩
    · have hπ : piSign p f = false := by unfold piSign; simp [h3]
      exact ⟨.PSU, 4, Or.inr (Or.inr (Or.inl ⟨rfl, hπ, rfl, rfl⟩)), D, hcard, i₀, h1, h2⟩
  exact sectionOrthType_of_hasOrthType hgen hort

end CFSG.ClassicalInvolution.Asc77.T7H
