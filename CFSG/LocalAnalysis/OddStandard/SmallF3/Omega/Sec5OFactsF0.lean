module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5OFacts
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5CKPull
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFCoverSylow
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PCMap
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5OFactsF0Aux
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3PkBasic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint
open scoped commutatorElement

theorem asc82FactPockets6_of (hS : Asc82SchurU43) : Asc82FactPockets6 := by
  intro G _ _ L z hL hz
  obtain ⟨V, i1, i2, i3, Q, hQ, φ, hφ⟩ := t5_exists_cover hS hL
  letI := i1
  letI := i2
  letI := i3
  haveI : Finite (OGroup Q) := sec5c_finite_ogroup
  haveI : Finite ↥(omegaGroup hQ) := Subtype.finite
  have hO : OddCentralCover φ := hφ.oddCentralCover hL
  have hzL : z ∈ L := sec5c_mem_of_isI4PlusIn hz
  have hzz : z * z = 1 := by
    rw [← pow_two, ← hz.1]
    exact pow_orderOf_eq_one z
  have hzne : z ≠ 1 := by
    intro h1
    have hord : orderOf z = 2 := hz.1
    rw [h1, orderOf_one] at hord
    omega
  obtain ⟨hztt, hzt4⟩ := sec5c_z_model hL hφ hz hzL
  let t : OGroup Q := sec5cdPhi φ ⟨z, hzL⟩
  have htP : t ∈ omegaGroup hQ := (φ ⟨z, hzL⟩).2
  let D : Om6Par Q t := Om6Par.mk' hQ hφ.finrank_eq hφ.quadSign_eq hztt hzt4
  let P : Subgroup (OGroup Q) := omegaGroup hQ
  have hDLP : D.L ≤ P := (le_sup_left.trans D.le_omega_cent).trans inf_le_left
  have hDRP : D.R ≤ P := (le_sup_right.trans D.le_omega_cent).trans inf_le_left
  let KbarL : Subgroup ↥P := D.L.subgroupOf P
  let KbarR : Subgroup ↥P := D.R.subgroupOf P
  let KtL : Subgroup ↥L := KbarL.comap φ
  let KtR : Subgroup ↥L := KbarR.comap φ
  let K1 : Subgroup G := KtL.map L.subtype
  let K2 : Subgroup G := KtR.map L.subtype
  have hPockDL : Sl23PocketIn P t D.L := (D.sec5Pair.pocket D.twoRes_eq).1
  have hPockDR : Sl23PocketIn P t D.R := (D.sec5Pair.pocket D.twoRes_eq).2
  have hPockDLtop : Sl23PocketIn (⊤ : Subgroup ↥P) ⟨t, htP⟩ KbarL := by
    refine (sec63PC_sl23PocketIn_map_iff P.subtype P.subtype_injective).mp ?_
    have hmap : (⊤ : Subgroup ↥P).map P.subtype = P := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have hsub : KbarL.map P.subtype = D.L := Subgroup.map_subgroupOf_eq_of_le hDLP
    rw [hmap, hsub]
    exact hPockDL
  have hPockDRtop : Sl23PocketIn (⊤ : Subgroup ↥P) ⟨t, htP⟩ KbarR := by
    refine (sec63PC_sl23PocketIn_map_iff P.subtype P.subtype_injective).mp ?_
    have hmap : (⊤ : Subgroup ↥P).map P.subtype = P := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have hsub : KbarR.map P.subtype = D.R := Subgroup.map_subgroupOf_eq_of_le hDRP
    rw [hmap, hsub]
    exact hPockDR
  have hSLDL : Nonempty (↥KbarL ≃* SL2F3) :=
    ⟨(Subgroup.subgroupOfEquivOfLe hDLP).trans D.sec5Pair.iso₁.some⟩
  have hSLDR : Nonempty (↥KbarR ≃* SL2F3) :=
    ⟨(Subgroup.subgroupOfEquivOfLe hDRP).trans D.sec5Pair.iso₂.some⟩
  have hK1 : Sl23PocketIn L z K1 :=
    sl23PocketIn_comap_cover L φ hO hzL hzz hPockDLtop hSLDL
  have hK2 : Sl23PocketIn L z K2 :=
    sl23PocketIn_comap_cover L φ hO hzL hzz hPockDRtop hSLDR
  have hne : K1 ≠ K2 := by
    intro h12
    have hKt : KtL = KtR := Subgroup.map_injective L.subtype_injective h12
    have hKbar : KbarL = KbarR := by
      ext y
      constructor
      · intro hy
        obtain ⟨l, hl⟩ := hφ.surjective y
        have hyl : φ l ∈ KbarL := by rw [hl]; exact hy
        have hl' : l ∈ KbarR.comap φ := by
          show l ∈ KtR
          rw [← hKt]
          exact hyl
        rw [← hl]
        exact hl'
      · intro hy
        obtain ⟨l, hl⟩ := hφ.surjective y
        have hyl : φ l ∈ KbarR := by rw [hl]; exact hy
        have hl' : l ∈ KbarL.comap φ := by
          show l ∈ KtL
          rw [hKt]
          exact hyl
        rw [← hl]
        exact hl'
    have hDLDR : D.L = D.R := by
      have := congrArg (fun X : Subgroup ↥P => X.map P.subtype) hKbar
      rwa [Subgroup.map_subgroupOf_eq_of_le hDLP,
        Subgroup.map_subgroupOf_eq_of_le hDRP] at this
    exact D.sec5Pair.ne hDLDR
  obtain ⟨eKL⟩ := hSLDL
  obtain ⟨eKR⟩ := hSLDR
  have htKbarL : (⟨t, htP⟩ : ↥P) ∈ KbarL := hPockDL.1
  have htKbarR : (⟨t, htP⟩ : ↥P) ∈ KbarR := hPockDR.1
  have htpcL : (⟨⟨t, htP⟩, htKbarL⟩ : ↥KbarL) ∈ CFSG.pCore 2 ↥KbarL := by
    have hv : eKL ⟨⟨t, htP⟩, htKbarL⟩ ∈ CFSG.pCore 2 SL23 := by
      rw [sl23_pCore_eq_Q8, mem_sl23Q8]
      have h2 : eKL ⟨⟨t, htP⟩, htKbarL⟩ * eKL ⟨⟨t, htP⟩, htKbarL⟩ = 1 := by
        rw [← map_mul, ← map_one eKL]
        congr 1
        exact Subtype.ext (Subtype.ext hztt)
      calc eKL ⟨⟨t, htP⟩, htKbarL⟩ ^ 4
          = (eKL ⟨⟨t, htP⟩, htKbarL⟩ * eKL ⟨⟨t, htP⟩, htKbarL⟩) *
            (eKL ⟨⟨t, htP⟩, htKbarL⟩ * eKL ⟨⟨t, htP⟩, htKbarL⟩) := by
              rw [show (4 : ℕ) = 2 + 2 by norm_num, pow_add, pow_two]
        _ = 1 := by rw [h2, one_mul]
    have hmap := CFSG.pCore_map_iso 2 eKL
    have hmem : eKL ⟨⟨t, htP⟩, htKbarL⟩ ∈
        (CFSG.pCore 2 ↥KbarL).map eKL.toMonoidHom := by
      rw [hmap]
      exact hv
    obtain ⟨y, hy, hye⟩ := Subgroup.mem_map.mp hmem
    have hy' : y = ⟨⟨t, htP⟩, htKbarL⟩ := eKL.injective hye
    rwa [hy'] at hy
  have htpcR : (⟨⟨t, htP⟩, htKbarR⟩ : ↥KbarR) ∈ CFSG.pCore 2 ↥KbarR := by
    have hv : eKR ⟨⟨t, htP⟩, htKbarR⟩ ∈ CFSG.pCore 2 SL23 := by
      rw [sl23_pCore_eq_Q8, mem_sl23Q8]
      have h2 : eKR ⟨⟨t, htP⟩, htKbarR⟩ * eKR ⟨⟨t, htP⟩, htKbarR⟩ = 1 := by
        rw [← map_mul, ← map_one eKR]
        congr 1
        exact Subtype.ext (Subtype.ext hztt)
      calc eKR ⟨⟨t, htP⟩, htKbarR⟩ ^ 4
          = (eKR ⟨⟨t, htP⟩, htKbarR⟩ * eKR ⟨⟨t, htP⟩, htKbarR⟩) *
            (eKR ⟨⟨t, htP⟩, htKbarR⟩ * eKR ⟨⟨t, htP⟩, htKbarR⟩) := by
              rw [show (4 : ℕ) = 2 + 2 by norm_num, pow_add, pow_two]
        _ = 1 := by rw [h2, one_mul]
    have hmap := CFSG.pCore_map_iso 2 eKR
    have hmem : eKR ⟨⟨t, htP⟩, htKbarR⟩ ∈
        (CFSG.pCore 2 ↥KbarR).map eKR.toMonoidHom := by
      rw [hmap]
      exact hv
    obtain ⟨y, hy, hye⟩ := Subgroup.mem_map.mp hmem
    have hy' : y = ⟨⟨t, htP⟩, htKbarR⟩ := eKR.injective hye
    rwa [hy'] at hy
  let zL : ↥L := ⟨z, hzL⟩
  have hzLsq : zL * zL = 1 := Subtype.ext hzz
  let RL : Subgroup ↥P := (CFSG.pCore 2 ↥KbarL).map KbarL.subtype
  let RR : Subgroup ↥P := (CFSG.pCore 2 ↥KbarR).map KbarR.subtype
  have hRLK : RL ≤ KbarL := Subgroup.map_subtype_le _
  have hRRK : RR ≤ KbarR := Subgroup.map_subtype_le _
  have hRLn : (RL.subgroupOf KbarL).Normal := by
    have h : RL.subgroupOf KbarL = CFSG.pCore 2 ↥KbarL := by
      change RL.comap KbarL.subtype = CFSG.pCore 2 ↥KbarL
      exact Subgroup.comap_map_eq_self_of_injective KbarL.subtype_injective _
    rw [h]
    exact CFSG.pCore_normal
  have hRRn : (RR.subgroupOf KbarR).Normal := by
    have h : RR.subgroupOf KbarR = CFSG.pCore 2 ↥KbarR := by
      change RR.comap KbarR.subtype = CFSG.pCore 2 ↥KbarR
      exact Subgroup.comap_map_eq_self_of_injective KbarR.subtype_injective _
    rw [h]
    exact CFSG.pCore_normal
  have hRL2 : IsPGroup 2 ↥RL :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥KbarL)).map KbarL.subtype
  have hRR2 : IsPGroup 2 ↥RR :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥KbarR)).map KbarR.subtype
  have htRL : (⟨t, htP⟩ : ↥P) ∈ RL := by
    change (⟨t, htP⟩ : ↥P) ∈ (CFSG.pCore 2 ↥KbarL).map KbarL.subtype
    exact Subgroup.mem_map.mpr ⟨⟨⟨t, htP⟩, htKbarL⟩, htpcL, rfl⟩
  have htRR : (⟨t, htP⟩ : ↥P) ∈ RR := by
    change (⟨t, htP⟩ : ↥P) ∈ (CFSG.pCore 2 ↥KbarR).map KbarR.subtype
    exact Subgroup.mem_map.mpr ⟨⟨⟨t, htP⟩, htKbarR⟩, htpcR, rfl⟩
  have hzQ1 : z ∈ twoCoreIn K1 := by
    have h := mem_twoCoreIn_of_lift (L := L) (φ := φ) hO (K := KbarL) RL hRLK hRLn hRL2
      (r := ⟨t, htP⟩) htRL (w := zL) hzLsq (Subtype.ext rfl)
    simpa [K1, KtL] using h
  have hzQ2 : z ∈ twoCoreIn K2 := by
    have h := mem_twoCoreIn_of_lift (L := L) (φ := φ) hO (K := KbarR) RR hRRK hRRn hRR2
      (r := ⟨t, htP⟩) htRR (w := zL) hzLsq (Subtype.ext rfl)
    simpa [K2, KtR] using h
  have hqL : Nonempty (↥(CFSG.pCore 2 ↥KbarL) ≃* ↥sl23Q8) := by
    refine ⟨(Subgroup.equivMapOfInjective (CFSG.pCore 2 ↥KbarL) eKL.toMonoidHom
      eKL.injective).trans (MulEquiv.subgroupCongr ?_)⟩
    rw [CFSG.pCore_map_iso 2 eKL, sl23_pCore_eq_Q8]
  have hqR : Nonempty (↥(CFSG.pCore 2 ↥KbarR) ≃* ↥sl23Q8) := by
    refine ⟨(Subgroup.equivMapOfInjective (CFSG.pCore 2 ↥KbarR) eKR.toMonoidHom
      eKR.injective).trans (MulEquiv.subgroupCongr ?_)⟩
    rw [CFSG.pCore_map_iso 2 eKR, sl23_pCore_eq_Q8]
  let ψL : ↥KtL →* ↥KbarL := φ.subgroupComap KbarL
  let ψR : ↥KtR →* ↥KbarR := φ.subgroupComap KbarR
  have hOddL : OddCentralCover ψL := hO.subgroupComap KbarL
  have hOddR : OddCentralCover ψR := hO.subgroupComap KbarR
  obtain ⟨ePL⟩ := pCore_iso_of_oddCentralCover (ψ := ψL) hOddL
  obtain ⟨ePR⟩ := pCore_iso_of_oddCentralCover (ψ := ψR) hOddR
  have hpcK1 : Nonempty (↥(CFSG.pCore 2 ↥K1) ≃* ↥(CFSG.pCore 2 ↥KtL)) :=
    ⟨((Subgroup.equivMapOfInjective (CFSG.pCore 2 ↥KtL) (Subgroup.equivMapOfInjective
        KtL L.subtype L.subtype_injective).toMonoidHom
        (Subgroup.equivMapOfInjective KtL L.subtype L.subtype_injective).injective).trans
      (MulEquiv.subgroupCongr (CFSG.pCore_map_iso 2
        (Subgroup.equivMapOfInjective KtL L.subtype L.subtype_injective)))).symm⟩
  have hpcK2 : Nonempty (↥(CFSG.pCore 2 ↥K2) ≃* ↥(CFSG.pCore 2 ↥KtR)) :=
    ⟨((Subgroup.equivMapOfInjective (CFSG.pCore 2 ↥KtR) (Subgroup.equivMapOfInjective
        KtR L.subtype L.subtype_injective).toMonoidHom
        (Subgroup.equivMapOfInjective KtR L.subtype L.subtype_injective).injective).trans
      (MulEquiv.subgroupCongr (CFSG.pCore_map_iso 2
        (Subgroup.equivMapOfInjective KtR L.subtype L.subtype_injective)))).symm⟩
  have hiso1 : Nonempty (↥(twoCoreIn K1) ≃* QuaternionGroup 2) :=
    ⟨(twoCoreInEquivPCore K1).trans (hpcK1.some.trans (ePL.trans (hqL.some.trans
      sl23Q8EquivQuaternionGroup2)))⟩
  have hiso2 : Nonempty (↥(twoCoreIn K2) ≃* QuaternionGroup 2) :=
    ⟨(twoCoreInEquivPCore K2).trans (hpcK2.some.trans (ePR.trans (hqR.some.trans
      sl23Q8EquivQuaternionGroup2)))⟩
  have hff_le_KbarL : ffImg φ (twoCoreIn K1) ≤ KbarL := by
    intro b' hb'
    obtain ⟨l, hl, hfl⟩ := mem_ffImg_iff.mp hb'
    rw [← hfl]
    have hlK1 : (l : G) ∈ K1 := twoCoreIn_le_self K1 hl
    obtain ⟨x, hxKt, hxl⟩ := Subgroup.mem_map.mp hlK1
    have hxl' : x = l := Subtype.ext hxl
    rw [← hxl']
    exact hxKt
  have hff_le_KbarR : ffImg φ (twoCoreIn K2) ≤ KbarR := by
    intro b' hb'
    obtain ⟨l, hl, hfl⟩ := mem_ffImg_iff.mp hb'
    rw [← hfl]
    have hlK2 : (l : G) ∈ K2 := twoCoreIn_le_self K2 hl
    obtain ⟨x, hxKt, hxl⟩ := Subgroup.mem_map.mp hlK2
    have hxl' : x = l := Subtype.ext hxl
    rw [← hxl']
    exact hxKt
  have hK1L : twoCoreIn K1 ≤ L :=
    (twoCoreIn_le_self K1).trans ((hK1.2.1).trans inf_le_left)
  have hK2L : twoCoreIn K2 ≤ L :=
    (twoCoreIn_le_self K2).trans ((hK2.2.1).trans inf_le_left)
  have hcomm : ⁅twoCoreIn K1, twoCoreIn K2⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro q1 hq1
    rw [Subgroup.mem_centralizer_iff]
    intro q2 hq2
    have hq1L : q1 ∈ L := hK1L hq1
    have hq1KbarL : φ ⟨q1, hq1L⟩ ∈ KbarL := by
      have hq1K1 : q1 ∈ K1 := twoCoreIn_le_self K1 hq1
      obtain ⟨x, hxKt, hxq⟩ := Subgroup.mem_map.mp hq1K1
      have hx : x = ⟨q1, hq1L⟩ := Subtype.ext hxq
      rw [← hx]
      exact hxKt
    have hRHS : ∀ b' ∈ ffImg φ (twoCoreIn K2),
        φ ⟨q1, hq1L⟩ * b' = b' * φ ⟨q1, hq1L⟩ := by
      intro b' hb'
      have hbK : b' ∈ KbarR := hff_le_KbarR hb'
      have hbDR : ((b' : ↥P) : OGroup Q) ∈ D.R := hbK
      have hq1DL : ((φ ⟨q1, hq1L⟩ : ↥P) : OGroup Q) ∈ D.L := hq1KbarL
      exact Subtype.ext (D.sec5Pair.comm _ hq1DL _ hbDR)
    have hstep := (ff_cover_commute_iff (φ := φ) hO (B := twoCoreIn K2) hK2L
      (isPGroup_twoCoreIn K2) ⟨q1, hq1L⟩).mpr hRHS
    exact (hstep q2 hq2).symm
  have hcommE : ∀ a ∈ twoCoreIn K1, ∀ b ∈ twoCoreIn K2, a * b = b * a := by
    intro a ha b hb
    have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    exact ((Subgroup.mem_centralizer_iff.mp (hle ha)) b hb).symm
  have hzQ1I : CFSG.ClassicalInvolution.Generic.IsUniqueInvolution (twoCoreIn K1) z := by
    obtain ⟨z1, hz1⟩ :=
      CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf.Q8.exists_isUniqueInvolution_of_mulEquiv
        (R := twoCoreIn K1) hiso1
    have hz1z : z1 = z := by
      rcases hz1.unique z hzQ1 hzz with h | h
      · exact absurd h hzne
      · exact h.symm
    rw [← hz1z]
    exact hz1
  have hzQ2I : CFSG.ClassicalInvolution.Generic.IsUniqueInvolution (twoCoreIn K2) z := by
    obtain ⟨z1, hz1⟩ :=
      CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf.Q8.exists_isUniqueInvolution_of_mulEquiv
        (R := twoCoreIn K2) hiso2
    have hz1z : z1 = z := by
      rcases hz1.unique z hzQ2 hzz with h | h
      · exact absurd h hzne
      · exact h.symm
    rw [← hz1z]
    exact hz1
  have hcard : Nat.card ↥(twoCoreIn K1 ⊔ twoCoreIn K2) = 32 :=
    CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf.Q8.natCard_sup_eq_32
      (R := twoCoreIn K1) (R' := twoCoreIn K2) (z := z) hiso1 hiso2 hzQ1I hzQ2I hcommE
  have hz1central : ∀ v ∈ twoCoreIn K1, z * v = v * z := by
    intro v hv
    have hconj : v * z * v⁻¹ ∈ twoCoreIn K1 :=
      (twoCoreIn K1).mul_mem ((twoCoreIn K1).mul_mem hv hzQ1) ((twoCoreIn K1).inv_mem hv)
    have hsq : (v * z * v⁻¹) * (v * z * v⁻¹) = 1 := by
      calc (v * z * v⁻¹) * (v * z * v⁻¹) = v * (z * z) * v⁻¹ := by group
        _ = 1 := by rw [hzz]; group
    have hne' : v * z * v⁻¹ ≠ 1 := by
      intro h
      apply hzne
      calc z = v⁻¹ * (v * z * v⁻¹) * v := by group
        _ = v⁻¹ * 1 * v := by rw [h]
        _ = 1 := by group
    rcases hzQ1I.unique _ hconj hsq with h1 | h2
    · exact absurd h1 hne'
    · have : v * z = z * v := by
        have h' := congrArg (fun t => t * v) h2
        simpa [mul_assoc] using h'
      exact this.symm
  have hz2central : ∀ v ∈ twoCoreIn K2, z * v = v * z := by
    intro v hv
    have hconj : v * z * v⁻¹ ∈ twoCoreIn K2 :=
      (twoCoreIn K2).mul_mem ((twoCoreIn K2).mul_mem hv hzQ2) ((twoCoreIn K2).inv_mem hv)
    have hsq : (v * z * v⁻¹) * (v * z * v⁻¹) = 1 := by
      calc (v * z * v⁻¹) * (v * z * v⁻¹) = v * (z * z) * v⁻¹ := by group
        _ = 1 := by rw [hzz]; group
    have hne' : v * z * v⁻¹ ≠ 1 := by
      intro h
      apply hzne
      calc z = v⁻¹ * (v * z * v⁻¹) * v := by group
        _ = v⁻¹ * 1 * v := by rw [h]
        _ = 1 := by group
    rcases hzQ2I.unique _ hconj hsq with h1 | h2
    · exact absurd h1 hne'
    · have : v * z = z * v := by
        have h' := congrArg (fun t => t * v) h2
        simpa [mul_assoc] using h'
      exact this.symm
  have hjoinL : twoCoreIn K1 ⊔ twoCoreIn K2 ≤ L := sup_le hK1L hK2L
  have hcenter : centerIn (twoCoreIn K1 ⊔ twoCoreIn K2) = zpowers z := by
    apply le_antisymm
    · intro x hx
      obtain ⟨hxJ, hxcent⟩ := sec5_mem_centerIn_iff.mp hx
      obtain ⟨a, ha, b, hb, hxab⟩ :=
        (CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf.Q8.mem_sup_iff_exists_mul_of_forall_comm
          (R := twoCoreIn K1) (R' := twoCoreIn K2) hcommE).mp hxJ
      have ha_cent : a = 1 ∨ a = z := by
        refine CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf.Q8.eq_one_or_eq_unique_involution_of_forall_comm
          (R := twoCoreIn K1) (z := z) hiso1 hzQ1I ha ?_
        intro v hv
        have hvJ : v ∈ twoCoreIn K1 ⊔ twoCoreIn K2 := Subgroup.mem_sup_left hv
        have hh := hxcent v hvJ
        rw [hxab] at hh
        have hbv : b * v = v * b := (hcommE v hv b hb).symm
        exact mul_right_cancel (b := b) (by
          calc a * v * b = a * (v * b) := by group
            _ = a * (b * v) := by rw [hbv]
            _ = (a * b) * v := by group
            _ = v * (a * b) := hh
            _ = v * a * b := by group)
      have hb_cent : b = 1 ∨ b = z := by
        refine CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf.Q8.eq_one_or_eq_unique_involution_of_forall_comm
          (R := twoCoreIn K2) (z := z) hiso2 hzQ2I hb ?_
        intro v hv
        have hvJ : v ∈ twoCoreIn K1 ⊔ twoCoreIn K2 := Subgroup.mem_sup_right hv
        have hh := hxcent v hvJ
        rw [hxab] at hh
        have hav : a * v = v * a := hcommE a ha v hv
        exact mul_left_cancel (a := a) (by
          calc a * (b * v) = (a * b) * v := by group
            _ = v * (a * b) := hh
            _ = v * a * b := by group
            _ = a * v * b := by rw [hav]
            _ = a * (v * b) := by group)
      rcases ha_cent with h1 | hz1
      · rcases hb_cent with h1' | hz1'
        · rw [hxab, h1, h1', one_mul]; exact one_mem _
        · rw [hxab, h1, hz1', one_mul]; exact Subgroup.mem_zpowers z
      · rcases hb_cent with h1' | hz1'
        · rw [hxab, hz1, h1', mul_one]; exact Subgroup.mem_zpowers z
        · rw [hxab, hz1, hz1', hzz]; exact one_mem _
    · refine Subgroup.zpowers_le.mpr ?_
      rw [sec5_mem_centerIn_iff]
      refine ⟨Subgroup.mem_sup_left hzQ1, ?_⟩
      intro y hy
      obtain ⟨a, ha, b, hb, rfl⟩ :=
        (CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf.Q8.mem_sup_iff_exists_mul_of_forall_comm
          (R := twoCoreIn K1) (R' := twoCoreIn K2) hcommE).mp hy
      calc z * (a * b) = (z * a) * b := by group
        _ = (a * z) * b := by rw [hz1central a ha]
        _ = a * (z * b) := by group
        _ = a * (b * z) := by rw [hz2central b hb]
        _ = (a * b) * z := by group
  have hzord : orderOf z = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact hzz) hzne
  have hznotcenter : z ∉ centerIn L := by
    intro hzc
    obtain ⟨K, hK⟩ := hz.2
    obtain ⟨a, haL, hane⟩ := exists_noncomm_of_sl23PocketIn hL.1 hK
    exact hane ((sec5_mem_centerIn_iff.mp hzc).2 a haL).symm
  have hdisj : (twoCoreIn K1 ⊔ twoCoreIn K2) ⊓ centerIn L = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨hxJ, hxZ⟩ := Subgroup.mem_inf.mp hx
    have hxc : x ∈ centerIn (twoCoreIn K1 ⊔ twoCoreIn K2) := by
      rw [sec5_mem_centerIn_iff]
      exact ⟨hxJ, fun y hy => (sec5_mem_centerIn_iff.mp hxZ).2 y (hjoinL hy)⟩
    rw [hcenter] at hxc
    rcases (CFSG.Timmesfeld.Bridge.mem_zpowers_iff_of_orderOf_eq_two hzord).mp hxc with
      h1 | hz'
    · exact h1
    · exact absurd (hz' ▸ hxZ) hznotcenter
  exact ⟨K1, K2, hK1, hK2, hne, hiso1, hiso2, hcomm, hcard, hcenter, hdisj⟩

end CFSG.OddStandard.SmallF3.Omega
