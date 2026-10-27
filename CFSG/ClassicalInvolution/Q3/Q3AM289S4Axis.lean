module

public import CFSG.ClassicalInvolution.Q3.Q3AMBadS3Lift
public import CFSG.ClassicalInvolution.Q3.Q3AMBadShape
public import CFSG.ClassicalInvolution.Q3.Q3T8B05

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.Q3T8.Asc77 CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Q3.Q3CP CFSG.ClassicalInvolution.Q3.Q3CH
open scoped MatrixGroups commutatorElement

section Lift


variable {G : Type} [Group G] [Finite G]

theorem exists_s4Axis [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K J K' : Subgroup G}
    {S : Sylow 2 G} {R T W : Subgroup G} {z t : G} (h : PspSetting Ω K J S R T W z t K')
    {N : Subgroup G} (hN : N ∈ omegaNbr Ω K) {u : G} (hu : u ∈ exactCore3 z N)
    (hu4 : orderOf u = 4) (hcomm : ⁅t, u⁆ ∈ oddCoreOf (nbrLayer Ω K z))
    (himgJ : layerImage Ω K z N ≠ layerImage Ω K z J)
    (himgK' : layerImage Ω K z N ≠ layerImage Ω K z K') :
    ∃ s p b₀ : G, p ∈ oddCoreOf (nbrLayer Ω K z) ∧ IsUniqueInvolution N b₀ ∧ u * u = b₀ ∧
      s = p * b₀ * p⁻¹ ∧ S3AxisL Ω K J z t s := by
  classical
  have hbad := h.bad
  have hstd := hbad.std
  have hΩ : HypOmegaMod Ω := hstd.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hstd.stand.trans hstd.noTwins hM
  have hK : K ∈ Ω := hstd.stand.mem
  have hJK : J ∈ omegaNbr Ω K := hstd.hJ
  have hz2 : z * z = 1 := hstd.hz.sq
  have ht2 : t * t = 1 := hstd.ht.sq
  have hzt : z * t = t * z := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hstd.hz hstd.hJ hstd.ht
  have hNC : Subgroup.normalizer (K : Set G) = Subgroup.centralizer ({z} : Set G) :=
    hbad.normalizer_eq_centralizer
  have huK' : IsUniqueInvolution K' (z * t) := h.uniq_K'
  have hK'Ω : K' ∈ Ω := h.nbrK.1
  have hYC : nbrLayer Ω K z ≤ Subgroup.centralizer ({z} : Set G) := nbrLayer_le_centralizer Ω K z
  have htY : t ∈ nbrLayer Ω K z := exactCore3_le_nbrLayer hJK
    ⟨hstd.ht.mem, Subgroup.mem_centralizer_singleton_iff.mpr hzt.symm⟩
  have huY : u ∈ nbrLayer Ω K z := exactCore3_le_nbrLayer hN hu
  obtain ⟨b, hb⟩ := hΩ.exists_uniqueInvolution hN.1
  have hub : u * u = b := by
    have h1 : u * u ∈ N := N.mul_mem hu.1 hu.1
    have hu_4 : u ^ 4 = 1 := by
      have := pow_orderOf_eq_one u
      rwa [hu4] at this
    have h4 : (u * u) * (u * u) = 1 := by
      calc (u * u) * (u * u) = u ^ 4 := by
            rw [show (4 : ℕ) = 2 + 2 by norm_num, pow_add, pow_two]
        _ = 1 := hu_4
    have h1' : u * u ≠ 1 := by
      intro h2
      have h3 : orderOf u ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h2)
      rw [hu4] at h3
      omega
    exact (hb.unique _ h1 h4).resolve_left h1'
  have hA : IsPGroup 2 (Subgroup.zpowers t) :=
    isPGroup_zpowers_of_mul_self_eq_one ht2 hstd.ht.ne_one
  have hB : IsPGroup 2 (Subgroup.zpowers u) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hu4]; norm_num)
  have hAN : Subgroup.zpowers t ≤ Subgroup.normalizer (oddCoreOf (nbrLayer Ω K z) : Set G) :=
    Subgroup.zpowers_le.mpr (mem_normalizer_oddCoreOf_of_mem htY)
  have hBN : Subgroup.zpowers u ≤ Subgroup.normalizer (oddCoreOf (nbrLayer Ω K z) : Set G) :=
    Subgroup.zpowers_le.mpr (mem_normalizer_oddCoreOf_of_mem huY)
  have hAB : ∀ a ∈ Subgroup.zpowers t, ∀ b' ∈ Subgroup.zpowers u,
      ⁅a, b'⁆ ∈ oddCoreOf (nbrLayer Ω K z) := fun a ha b' hb' =>
    commutator_zpowers_mem_oddCoreOf htY huY hcomm ha hb'
  obtain ⟨p, hp, hpc⟩ := exists_conj_commutes_of_commutator_mem hA hB
    (oddCoreOf_odd_natCard (nbrLayer Ω K z)) hAN hBN hAB
  have htu' : t * (p * u * p⁻¹) = (p * u * p⁻¹) * t :=
    hpc t (Subgroup.mem_zpowers t) u (Subgroup.mem_zpowers u)
  have hpY : p ∈ nbrLayer Ω K z := oddCoreOf_le_self _ hp
  have hpC : p ∈ Subgroup.centralizer ({z} : Set G) := hYC hpY
  have hpK : conjSub p K = K := mem_normalizer_iff_conjSub_eq.mp (hNC ▸ hpC)
  have hN' : conjSub p N ∈ omegaNbr Ω K := conjSub_mem_omegaNbr_of_conjSub_eq hΩ hpK hN
  have hcore : exactCore3 z (conjSub p N) = conjSub p (exactCore3 z N) := by
    have h1 := exactCore3_conjSub p z N
    rwa [conj_eq_of_mem_centralizer_singleton hpC] at h1
  have hu' : p * u * p⁻¹ ∈ exactCore3 z (conjSub p N) := by
    rw [hcore]
    exact Subgroup.mem_map.mpr ⟨u, hu, rfl⟩
  have hu'Y : p * u * p⁻¹ ∈ nbrLayer Ω K z := exactCore3_le_nbrLayer hN' hu'
  have hu'N' : p * u * p⁻¹ ∈ conjSub p N := hu'.1
  obtain ⟨s, hs⟩ : ∃ s : G, s = p * b * p⁻¹ := ⟨_, rfl⟩
  have hb's : IsUniqueInvolution (conjSub p N) s := by
    rw [hs]
    exact hb.conj p
  have hs_eq : (p * u * p⁻¹) * (p * u * p⁻¹) = s := by
    rw [hs, ← hub]
    group
  have hsY : s ∈ nbrLayer Ω K z := by
    rw [← hs_eq]
    exact (nbrLayer Ω K z).mul_mem hu'Y hu'Y
  have hNJ : conjSub p N ≠ J := by
    intro hJeq
    apply himgJ
    have h1 : layerImage Ω K z (conjSub p N) = layerImage Ω K z N := by
      show Subgroup.map _ ((exactCore3 z (conjSub p N)).subgroupOf (nbrLayer Ω K z)) =
        Subgroup.map _ ((exactCore3 z N).subgroupOf (nbrLayer Ω K z))
      rw [hcore]
      exact map_mk_subgroupOf_conjSub_oddCore hp (exactCore3_le_nbrLayer hN)
    rw [← h1, hJeq]
  have hN'K' : conjSub p N ≠ K' := by
    intro hK'eq
    apply himgK'
    have h1 : layerImage Ω K z (conjSub p N) = layerImage Ω K z N := by
      show Subgroup.map _ ((exactCore3 z (conjSub p N)).subgroupOf (nbrLayer Ω K z)) =
        Subgroup.map _ ((exactCore3 z N).subgroupOf (nbrLayer Ω K z))
      rw [hcore]
      exact map_mk_subgroupOf_conjSub_oddCore hp (exactCore3_le_nbrLayer hN)
    rw [← h1, hK'eq]
  have hsq : s * s = 1 := by
    rw [hs]
    calc (p * b * p⁻¹) * (p * b * p⁻¹) = p * (b * b) * p⁻¹ := by group
      _ = 1 := by rw [hb.sq]; group
  have hne1 : s ≠ 1 := hb's.ne_one
  have hcz : z * s = s * z :=
    (Subgroup.mem_centralizer_singleton_iff.mp (hYC hsY)).symm
  have hct : t * s = s * t := by
    rw [← hs_eq]
    calc t * ((p * u * p⁻¹) * (p * u * p⁻¹)) = (t * (p * u * p⁻¹)) * (p * u * p⁻¹) := by group
      _ = ((p * u * p⁻¹) * t) * (p * u * p⁻¹) := by rw [htu']
      _ = (p * u * p⁻¹) * (t * (p * u * p⁻¹)) := by group
      _ = (p * u * p⁻¹) * ((p * u * p⁻¹) * t) := by rw [htu']
      _ = ((p * u * p⁻¹) * (p * u * p⁻¹)) * t := by group
  have hind : s ∉ Subgroup.closure ({z, t} : Set G) := by
    intro hmem
    rcases Thompson.eq_of_mem_closure_pair hz2 ht2 hzt hmem with h1 | h1 | h1 | h1
    · exact hne1 h1
    · have : IsUniqueInvolution (conjSub p N) z := by
        rw [← h1]
        exact hb's
      exact hN'.2.1 (hnt K hK _ ⟨hN'.1, z, hstd.hz, this⟩)
    · have : IsUniqueInvolution (conjSub p N) t := by
        rw [← h1]
        exact hb's
      exact hNJ (hnt J hstd.hJ.1 _ ⟨hN'.1, t, hstd.ht, this⟩)
    · have hzs : IsUniqueInvolution (conjSub p N) (z * t) := by
        rw [← h1]
        exact hb's
      exact hN'K' (hnt K' hK'Ω _ ⟨hN'.1, z * t, huK', hzs⟩)
  have hu'4 : orderOf (p * u * p⁻¹) = 4 := by
    have h1 := MulEquiv.orderOf_eq (MulAut.conj p) u
    rw [MulAut.conj_apply] at h1
    rw [h1, hu4]
  have hAJ : Subgroup.zpowers (p * u * p⁻¹) ≤ conjSub p N := Subgroup.zpowers_le.mpr hu'N'
  have hA2 : IsPGroup 2 (Subgroup.zpowers (p * u * p⁻¹)) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hu'4]; norm_num)
  have hA3 : 3 ≤ Nat.card (Subgroup.zpowers (p * u * p⁻¹)) := by
    rw [Nat.card_zpowers, hu'4]
    norm_num
  have hAc : Subgroup.zpowers (p * u * p⁻¹) ≤ Subgroup.centralizer ({t} : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr htu'.symm)
  have hAnorm : Subgroup.zpowers (p * u * p⁻¹) ≤ Subgroup.normalizer (J : Set G) :=
    hΩ.le_normalizer_of_le_centralizer hstd.hJ.1 hN'.1 (Ne.symm hNJ) hstd.ht hAJ hA2 hA3 hAc
  have hsA : s ∈ Subgroup.zpowers (p * u * p⁻¹) := by
    rw [← hs_eq]
    exact Subgroup.mul_mem _ (Subgroup.mem_zpowers _) (Subgroup.mem_zpowers _)
  have hnormJ : conjSub s J = J := mem_normalizer_iff_conjSub_eq.mp (hAnorm hsA)
  have hcl : IsClassicalMember3 (conjSub p N) s :=
    Q3T8.Asc77.isClassicalMember3_of_uniqueInvolution hstd.stand.modU hN'.1 hb's
  have hnbr : ∃ L ∈ omegaNbr Ω K, IsUniqueInvolution L s ∧ L ∈ omegaStarNbr Ω J ∧
      L ∉ insert J (omegaNbr Ω J) := by
    refine ⟨conjSub p N, hN', hb's, ⟨hN'.1, hNJ, Subgroup.zpowers (p * u * p⁻¹), ?_, hAJ, hAnorm⟩,
      ?_⟩
    ·
      have hA' : IsPGroup 2 (Subgroup.zpowers (⟨p * u * p⁻¹, hu'N'⟩ : ↥(conjSub p N))) :=
        IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, hu'4]; norm_num)
      obtain ⟨P, hP⟩ := hA'.exists_le_sylow
      have hR : Subgroup.map (conjSub p N).subtype (P : Subgroup ↥(conjSub p N)) ∈ RSet Ω :=
        ⟨conjSub p N, hN'.1, P, rfl⟩
      have hRsyl : IsSylow2In (Subgroup.map (conjSub p N).subtype (P : Subgroup ↥(conjSub p N)))
          (conjSub p N) :=
        Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hN'.1 hR (Subgroup.map_subtype_le _)
      have hu'R : p * u * p⁻¹ ∈
          Subgroup.map (conjSub p N).subtype (P : Subgroup ↥(conjSub p N)) :=
        ⟨⟨p * u * p⁻¹, hu'N'⟩, hP (Subgroup.mem_zpowers _), rfl⟩
      obtain ⟨e⟩ := hcl.nonempty_equiv
      have h8 := Q3T6.natCard_sylow_eq_eight e hRsyl
      refine mem_USet_of_natCard hN'.1 hRsyl (Subgroup.zpowers_le.mpr hu'R) inferInstance ?_
      rw [h8, Nat.card_zpowers, hu'4]
    · intro hmem
      rcases hmem with h1 | h1
      · exact hNJ h1
      · have hs' : s = z * t := hbad.eq_mul_of_nbr_nbr_at hstd hN' h1 hb's
        have hzs : IsUniqueInvolution (conjSub p N) (z * t) := by
          rw [← hs']
          exact hb's
        exact hN'K' (hnt K' hK'Ω _ ⟨hN'.1, z * t, huK', hzs⟩)
  exact ⟨s, p, b, hp, hb, hub, hs, ⟨hsq, hne1, hcz, hct, hind, hnormJ, hnbr⟩⟩


end Lift

end CFSG.ClassicalInvolution.Q3.Q3AM
