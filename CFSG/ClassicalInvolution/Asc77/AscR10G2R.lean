module

public import CFSG.ClassicalInvolution.Asc77.AscR10G2S

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Uniform CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
open scoped commutatorElement



section Lift

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {N : Subgroup G} [N.Normal]

theorem eq_one_or_eq_of_map_eq_of_twin_gen (hΩ : HypOmegaGen Ω) (hN : Odd (Nat.card N))
    {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J) {z : G}
    (hzK : IsUniqueInvolution K z) (hzJ : IsUniqueInvolution J z) {x k : G} (hx : x ∈ J)
    (hk : k ∈ K) (hk2 : IsPGroup 2 (Subgroup.zpowers k))
    (hxk : QuotientGroup.mk' N x = QuotientGroup.mk' N k) : k = 1 ∨ k = z := by
  exact E187C.eq_one_or_eq_of_map_eq_of_twin_of
    (fun hK hJ hKJ hzK hzJ => Sec6Gen.comm_le_oddCore_of_twin hΩ hK hJ hKJ hzK hzJ)
    (fun hK hz => Sec6Gen.center_two hΩ hK hz) hN hK hJ hKJ hzK hzJ hx hk hk2 hxk

theorem exists_conj_of_map_eq_gen (hΩ : HypOmegaGen Ω) (hN : Odd (Nat.card N))
    {K L : Subgroup G} (hK : K ∈ Ω) (hL : L ∈ Ω)
    (h : K.map (QuotientGroup.mk' N) = L.map (QuotientGroup.mk' N)) :
    ∃ n ∈ N, L = conjSub n K := by
  exact E187C.exists_conj_of_map_eq_of (fun hK => Sec6Gen.exists_uniqueInvolution hΩ hK)
    hΩ.conjInvariant (fun hQ => Sec6Gen.eight_le_of_mem_RSet hΩ hQ)
    (fun hK hJ hKJ hzK hzJ => Sec6Gen.comm_le_oddCore_of_twin hΩ hK hJ hKJ hzK hzJ)
    (fun hK hz => Sec6Gen.center_two hΩ hK hz) hN hK hL h

end Lift

section Nbr

variable {Y : Type} [Group Y] [Finite Y] {Λ : Set (Subgroup Y)}

theorem exists_conj_omegaNbr_of_commute (hΩ : HypOmegaGen Λ) {N : Subgroup Y} [N.Normal]
    (hN : Odd (Nat.card N)) {K M : Subgroup Y} (hK : K ∈ Λ) (hM : M ∈ Λ)
    (hne : M.map (QuotientGroup.mk' N) ≠ K.map (QuotientGroup.mk' N))
    (hcomm : ∀ x ∈ M, ∀ y ∈ K, QuotientGroup.mk' N x * QuotientGroup.mk' N y =
      QuotientGroup.mk' N y * QuotientGroup.mk' N x) :
    ∃ n ∈ N, M ∈ omegaNbr Λ (conjSub n K) := by
  obtain ⟨R, hR, hRM, -⟩ := exists_mem_RSet_ge hM (isPGroup_two_bot' (G := Y)) bot_le
  have hperm : ∀ v ∈ R, ∃ n ∈ N, conjSub v K = conjSub n K := by
    intro v hv
    have hvM : v ∈ M := hRM.1 hv
    have hvc : QuotientGroup.mk' N v ∈
        Subgroup.centralizer ((K.map (QuotientGroup.mk' N) : Subgroup (Y ⧸ N)) : Set (Y ⧸ N)) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨k, hk, rfl⟩
      exact (hcomm v hvM k hk).symm
    have himg : K.map (QuotientGroup.mk' N) = (conjSub v K).map (QuotientGroup.mk' N) := by
      rw [AscQuot.map_conjSub]
      exact (conjSub_eq_of_mem_normalizer (Subgroup.centralizer_le_normalizer _ hvc)).symm
    obtain ⟨n, hn, hnK⟩ := exists_conj_of_map_eq_gen hΩ hN hK (hΩ.conjInvariant v K hK) himg
    exact ⟨n, hn, hnK⟩
  obtain ⟨n, hn, hRn⟩ := exists_conj_normalizer_of_perm hN K hRM.2.1 hperm
  refine ⟨n, hn, hM, ?_, R, hR, hRM.1, hRn⟩
  intro hMK
  apply hne
  rw [hMK, AscQuot.map_conjSub, show QuotientGroup.mk' N n = 1 from
    (QuotientGroup.eq_one_iff _).mpr hn, conjSub_one]

end Nbr

section Single

variable {Y : Type} [Group Y] [Finite Y] {Λ : Set (Subgroup Y)}

theorem exists_noncomm_map_of_mem (hΩ : HypOmegaGen Λ) {K : Subgroup Y} (hK : K ∈ Λ) :
    ∃ x ∈ K, ∃ y ∈ K, oddQuot Y x * oddQuot Y y ≠ oddQuot Y y * oddQuot Y x := by
  obtain ⟨R₀, hR₀, hR₀1, -⟩ := exists_mem_RSet_ge hK (isPGroup_two_bot' (G := Y)) bot_le
  obtain ⟨x, hx, y, hy, hxy⟩ := (exists_ne_comm_of_mem_rSetGen hΩ hR₀).1
  refine ⟨x, hR₀1.1 hx, y, hR₀1.1 hy, fun h => hxy ?_⟩
  have h1 : oddQuot Y (x * y * x⁻¹ * y⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, h]
    group
  have h3 := quot_injOn_of_isPGroup hR₀1.2.1 _ (R₀.mul_mem (R₀.mul_mem (R₀.mul_mem hx hy)
    (R₀.inv_mem hx)) (R₀.inv_mem hy)) h1
  calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
    _ = y * x := by rw [h3, one_mul]

theorem eq_of_comp_g2 (hΩ : HypOmegaModU (.sl2 3 1) Λ)
    (htw : ∀ M₁ ∈ Λ, ∀ M₂ ∈ omegaNbr Λ M₁, M₂ ∈ twinSet Λ M₁) {K : Subgroup Y} {zK : Y}
    (hK : K ∈ Λ) (hzK : IsUniqueInvolution K zK) {L : Subgroup Y} [hLn : L.Normal]
    (hΛL : ∀ M ∈ Λ, M ≤ L) {ι : Type}
    (D : Q3.LieSystemData3 ι (↥L ⧸ classicalInvolutionOddCore ↥L)
      (oddQuotientFamily (restrictFamily Λ L)))
    {i : ι} {R : Subgroup (D.kind i).G}
    (hKR : (K.subgroupOf L).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥L)) =
      R.map (D.hom i))
    (hk : D.kind i = Q3.CompData.model .G2 0) : ∀ j : ι, j = i := by
  classical
  intro j
  by_contra hji
  have hc : D.kind i = compModel 3 1 .G2 0 := hk
  obtain ⟨-, hcenter, hinj⟩ := comp_g2_facts hc
  have hΩg : HypOmegaGen Λ := hypOmegaGenU_of_modU (MemberType.cert_sl2 3 1) hΩ
  have hodd := CFSG.ComponentClassification.OddCore.odd_card Y
  have hθinj := layerHom_injective L
  obtain ⟨R', hR', hMΦ⟩ := D.meets j
  obtain ⟨M₁, ⟨M₀, hM₀, hM₀L, rfl⟩, hM₁⟩ := hMΦ
  have hKL : K ≤ L := hΛL K hK
  have hcomm : ∀ x ∈ M₀, ∀ y ∈ K,
      oddQuot Y x * oddQuot Y y = oddQuot Y y * oddQuot Y x := by
    intro x hx y hy
    have hxm : QuotientGroup.mk (⟨x, hM₀L hx⟩ : ↥L) ∈
        (M₀.subgroupOf L).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥L)) :=
      ⟨⟨x, hM₀L hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    have hym : QuotientGroup.mk (⟨y, hKL hy⟩ : ↥L) ∈
        (K.subgroupOf L).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥L)) :=
      ⟨⟨y, hKL hy⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
    rw [hM₁] at hxm
    rw [hKR] at hym
    obtain ⟨a, -, hax⟩ := hxm
    obtain ⟨b, -, hby⟩ := hym
    have h1 := D.commute i j (Ne.symm hji) b a
    have h2 := congrArg (layerHom L) h1
    rw [map_mul, map_mul, hax, hby, layerHom_mk, layerHom_mk] at h2
    exact h2.symm
  have hne : M₀.map (QuotientGroup.mk' (classicalInvolutionOddCore Y)) ≠
      K.map (QuotientGroup.mk' (classicalInvolutionOddCore Y)) := by
    intro h
    obtain ⟨x, hx, y, hy, hxy⟩ := exists_noncomm_map_of_mem hΩg hK
    have hy' : oddQuot Y y ∈ M₀.map (oddQuot Y) := h ▸ ⟨y, hy, rfl⟩
    obtain ⟨y', hy'M, hy'e⟩ := hy'
    apply hxy
    rw [← hy'e]
    exact (hcomm y' hy'M x hx).symm
  obtain ⟨n, hn, hnbr⟩ := exists_conj_omegaNbr_of_commute hΩg hodd hK hM₀ hne hcomm
  obtain ⟨-, w, hw1, hw2⟩ := htw _ (hΩ.conjInvariant n K hK) M₀ hnbr
  have hww : w = n * zK * n⁻¹ := hw1.eq (hzK.conj n)
  have hπn : oddQuot Y n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
  have hπw : oddQuot Y w = oddQuot Y zK := by
    rw [hww, map_mul, map_mul, map_inv, hπn, one_mul, inv_one, mul_one]
  have hwL : w ∈ L := hM₀L hw2.mem
  have hzL : zK ∈ L := hKL hzK.mem
  have heq : (QuotientGroup.mk (⟨zK, hzL⟩ : ↥L) : ↥L ⧸ classicalInvolutionOddCore ↥L) =
      QuotientGroup.mk (⟨w, hwL⟩ : ↥L) := by
    apply hθinj
    rw [layerHom_mk, layerHom_mk]
    exact hπw.symm
  have hzm : (QuotientGroup.mk (⟨zK, hzL⟩ : ↥L) : ↥L ⧸ classicalInvolutionOddCore ↥L) ∈
      R.map (D.hom i) := by
    rw [← hKR]
    exact ⟨⟨zK, hzL⟩, Subgroup.mem_subgroupOf.mpr hzK.mem, rfl⟩
  have hwm : (QuotientGroup.mk (⟨w, hwL⟩ : ↥L) : ↥L ⧸ classicalInvolutionOddCore ↥L) ∈
      R'.map (D.hom j) := by
    rw [← hM₁]
    exact ⟨⟨w, hwL⟩, Subgroup.mem_subgroupOf.mpr hw2.mem, rfl⟩
  obtain ⟨g, -, hg⟩ := hzm
  obtain ⟨h, -, hh⟩ := hwm
  have hcen : g ∈ Subgroup.center (D.kind i).G := by
    rw [Subgroup.mem_center_iff]
    intro b
    apply hinj (D.hom i) (D.ker_le_center i)
    rw [map_mul, map_mul, hg, heq, ← hh]
    exact D.commute i j (Ne.symm hji) b h
  rw [hcenter, Subgroup.mem_bot] at hcen
  rw [hcen, map_one] at hg
  have h1 : oddQuot Y zK = 1 := by
    rw [← layerHom_mk L ⟨zK, hzL⟩, ← hg, map_one]
  exact (isUniqueInvolution_map_mk_of_odd (odd_natCard_oddCore_inf K) hzK).ne_one h1

end Single

@[expose] def G2Comp3 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (Λ : Set (Subgroup Y)), HypOmegaModU (.sl2 3 1) Λ →
    ∀ (K J : Subgroup Y) (zK zJ : Y), K ∈ Λ → AViol Λ K J zK zJ →
      ∀ {ι : Type} (D : Q3.LieSystemData3 ι
        (↥(omegaGen Λ) ⧸ classicalInvolutionOddCore ↥(omegaGen Λ))
        (oddQuotientFamily (restrictFamily Λ (omegaGen Λ)))) (j : ι)
        (R : Subgroup (D.kind j).G), R ∈ (D.kind j).fund →
          (K.subgroupOf (omegaGen Λ)).map
            (QuotientGroup.mk' (classicalInvolutionOddCore ↥(omegaGen Λ))) = R.map (D.hom j) →
          D.kind j = Q3.CompData.model .G2 0

theorem g2Sec3_of_g2Comp3 (hC : G2Comp3) : G2Sec3 := by
  intro Y _ _ Λ hΩ htw K J zK zJ hK hv ι D
  have hLn : (omegaGen Λ).Normal := omegaGen_normal hΩ.conjInvariant
  have hKt : (K.subgroupOf (omegaGen Λ)).map
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(omegaGen Λ))) ∈
        oddQuotientFamily (restrictFamily Λ (omegaGen Λ)) :=
    ⟨_, ⟨K, hK, le_omegaGen hK, rfl⟩, rfl⟩
  obtain ⟨i, R, hR, hKR⟩ := D.fundamental _ hKt
  have hk := hC Y Λ hΩ K J zK zJ hK hv D i R hR hKR
  exact ⟨i, eq_of_comp_g2 hΩ htw hK hv.hzK (fun M hM => le_omegaGen hM) D hKR hk, hk⟩

theorem res10aNoConj_nine_of_cit3 (p f : ℕ) [Fact p.Prime] (h3 : Q3.CIT3Inductive)
    (hC : G2Comp3) (h9 : p ^ f = 9) : Res10aNoConj p f :=
  res10aNoConj_nine_of_g2Sec3 p f h3 (g2Sec3_of_g2Comp3 hC) h9

theorem sec3Typing_of_g2Comp3 (h3 : Q3.CIT3Inductive) (hC : G2Comp3) : Sec3Typing :=
  sec3Typing_of_g2Sec3 h3 (g2Sec3_of_g2Comp3 hC)

theorem res10aNoConj9_of_g2Comp3 (p f : ℕ) [Fact p.Prime] (hC : G2Comp3) :
    Q3.CIT3Inductive → p ^ f = 9 → Res10aNoConj p f :=
  fun h3 h9 => res10aNoConj_nine_of_cit3 p f h3 hC h9

end CFSG.ClassicalInvolution.Asc77.T3CII
