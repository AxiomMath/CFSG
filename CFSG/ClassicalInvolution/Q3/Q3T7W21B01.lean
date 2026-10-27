module

public import CFSG.ClassicalInvolution.Q3.Q3T7W21DStar
public import CFSG.ClassicalInvolution.Q3.Q3T7Q22SecC
public import CFSG.ClassicalInvolution.Q3.Q3T7W21A03
public import CFSG.ClassicalInvolution.Q3.Q3T8E4A

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
    CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Exotic
    CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement MatrixGroups
section Facts

@[expose] def DStarConnectedTwinGen : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (Φ : Set (Subgroup X)), Q3T7.TransSect3 Φ →
    (∃ D : Uniform.OmegaLieU 3 1 Φ, D.card = 1) → TwinTriple Φ → T3.DStarConnected Φ

end Facts

theorem dstarConnectedTwinGen_of
    : DStarConnectedTwinGen := by
  intro X _ _ Φ hS hD htt
  obtain ⟨D, hcard⟩ := hD
  exact Q3T7.dstarConnected_of_twinTriple3 hS D hcard htt

end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected

@[expose] def C21_12_exclude : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z u : G) (J : Subgroup G) (t : G) (W : Subgroup G), Q3T8.Asc77.Hyp21 Ω K K' z u J t W →
      dComp Ω K ≠ dstarComp Ω K → ¬ MuIsoS3 Ω W ∧ ¬ MuIsoS4 Ω W

theorem c21_12_of
    (h717 : Q3T8.Asc77.L7_17) (hex : Q3T8.Asc77.C21_12_exclude) : Q3T8.Asc77.C21_12 := by
  intro G _ _ _ Ω K K' z u J t W h
  by_cases hSig : dComp Ω K = dstarComp Ω K
  · exact Or.inl hSig
  · refine Or.inr ?_
    have hP : Q3T8.Asc77.PartIHyp Ω :=
      ⟨h.std.stand.hyp, h.std.stand.cls, h.std.stand.aEmpty⟩
    rcases h717 G Ω hP K h.std.stand.mem with heq | hW
    · exact absurd heq hSig
    · obtain ⟨h3, h4⟩ := hex G Ω K K' z u J t W h hSig
      rcases hW W h.hW with h1 | h1 | h1
      · exact absurd h1 h3
      · exact absurd h1 h4
      · exact h1
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77.AscE184Sect
section Quot
variable {Y : Type} [Group Y] [Finite Y] {Λ : Set (Subgroup Y)}
  {N : Subgroup Y} [N.Normal]

theorem twinTriple_quot
    (hΛ' : Q3T7M.HM (quotFamily Λ N))
    (hN : Odd (Nat.card N)) {K K' J R R' T : Subgroup Y} (hK : K ∈ Λ) (hK' : K' ∈ twinSet Λ K)
    (hJ : J ∈ Λ) (hR : IsSylow2In R K) (hR' : IsSylow2In R' K') (hT : IsSylow2In T J)
    (hRR' : Commutes R R') (hRT : Commutes R T) (hR'T : Commutes R' T)
    (hTK : T ≤ Subgroup.normalizer (K : Set Y)) (hTK' : T ≤ Subgroup.normalizer (K' : Set Y)) :
    TwinTriple (quotFamily Λ N) := by
  set mk := QuotientGroup.mk' N with hmk
  obtain ⟨hK'Λ, z, hzK, hzK'⟩ := hK'
  have hKK' : K'.map mk ≠ K.map mk :=
    Q3T8.Asc77.map_ne_of_commutes_sylow hΛ' hN hK'Λ hR' hR hRR'.symm
  have hJK : J.map mk ≠ K.map mk := Q3T8.Asc77.map_ne_of_commutes_sylow hΛ' hN hJ hT hR hRT.symm
  have hJK' : J.map mk ≠ K'.map mk := Q3T8.Asc77.map_ne_of_commutes_sylow hΛ' hN hJ hT hR' hR'T.symm
  have hTset : T.map mk ∈ RSet (quotFamily Λ N) :=
    mem_RSet_of_isSylow2In (map_mem_quotFamily hJ) (isSylow2In_map_mk hN hT)
  refine ⟨K.map mk, map_mem_quotFamily hK, K'.map mk,
    ⟨map_mem_quotFamily hK'Λ, mk z, isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hN K) hzK,
      isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hN K') hzK'⟩, hKK',
    J.map mk, ⟨map_mem_quotFamily hJ, hJK, T.map mk, hTset, Subgroup.map_mono hT.1, ?_⟩,
    ⟨map_mem_quotFamily hJ, hJK', T.map mk, hTset, Subgroup.map_mono hT.1, ?_⟩⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact mk_mem_normalizer_map (hTK hx)
  · rintro _ ⟨x, hx, rfl⟩
    exact mk_mem_normalizer_map (hTK' hx)
end Quot
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Asc77.AscE184Sect CFSG.ClassicalInvolution.Asc77.ExactLayer
open scoped commutatorElement
variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K K' J W :
    Subgroup G} {z u t : G}
section Facts
variable (h : Q3T8.Asc77.Hyp21 Ω K K' z u J t W)
include h
omit [IsSimpleGroup G] in

theorem Hyp21.tz_sq :
    (t * z) * (t * z) = 1 := by
  have hzt : z * t = t * z := h.twinFrameData.comm_zt h.std.stand.modU
  calc (t * z) * (t * z) = t * (z * t) * z := by group
    _ = t * (t * z) * z := by rw [hzt]
    _ = (t * t) * (z * z) := by group
    _ = 1 := by rw [h.ht.sq, h.std.hz.sq, one_mul]
omit [IsSimpleGroup G] in

theorem Hyp21.tz_ne_one :
    t * z ≠ 1 := by
  intro h1
  have h2 : t = z⁻¹ := eq_inv_of_mul_eq_one_left h1
  have h3 : z⁻¹ = z := inv_eq_of_mul_eq_one_right h.std.hz.sq
  exact h.twinFrameData.t_ne_z (h2.trans h3)

theorem Hyp21.oddCore_centralizer_tz_comm
    (h3 : Q3T8.Asc77.C21_3)
    (hα : alphaOf (Subgroup.closure ({u, z} : Set G)) = ⊥) {n : G}
    (hn : n ∈ oddCoreOf (Subgroup.centralizer ({t * z} : Set G))) : n * z = z * n := by
  have hzt : z * t = t * z := h.twinFrameData.comm_zt h.std.stand.modU
  have hE : IsElemAbelian2 (Subgroup.closure ({t, z} : Set G)) 2 :=
    T7A.isElemAbelian2_closure_pair h.ht.sq h.std.hz.sq h.ht.ne_one h.std.hz.ne_one
      h.twinFrameData.t_ne_z hzt.symm
  have hsub : Subgroup.closure ({t, z} : Set G) ≤ Subgroup.closure ({z, u, t} : Set G) := by
    apply Subgroup.closure_mono
    intro x hx
    rcases hx with rfl | rfl <;> simp
  have hA' : alphaOf (Subgroup.closure ({t, z} : Set G)) = ⊥ :=
    ((h3 G Ω K K' z u J t W h).2 _ hsub hE).trans hα
  have hzA : z ∈ Subgroup.closure ({t, z} : Set G) := Subgroup.subset_closure (by simp)
  have htA : t ∈ Subgroup.closure ({t, z} : Set G) := Subgroup.subset_closure (by simp)
  have hcA : t * z ∈ Subgroup.closure ({t, z} : Set G) := Subgroup.mul_mem _ htA hzA
  have hmem : ⁅n, z⁆ ∈ ⁅oddCoreOf (Subgroup.centralizer ({t * z} : Set G)),
      Subgroup.closure ({t, z} : Set G)⁆ := Subgroup.commutator_mem_commutator hn hzA
  have hle : ⁅oddCoreOf (Subgroup.centralizer ({t * z} : Set G)),
      Subgroup.closure ({t, z} : Set G)⁆ ≤ alphaOf (Subgroup.closure ({t, z} : Set G)) := by
    unfold alphaOf
    exact le_sup_of_le_left (le_iSup₂_of_le (t * z) hcA
      (le_iSup_of_le h.tz_ne_one le_rfl))
  rw [hA'] at hle
  exact commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp (hle hmem))
end Facts
section Main
variable (h : Q3T8.Asc77.Hyp21 Ω K K' z u J t W)
include h
omit [IsSimpleGroup G] in

theorem Hyp21.mem_tqMembers_tz_J :
    J ∈
    Q3T8.Asc77.ExactLayer.tqMembers Ω (t * z) := by
  have hΩ : Q3T7M.HM Ω := h.std.stand.modU
  have hK : K ∈ Ω := h.std.stand.mem
  have hz : IsUniqueInvolution K z := h.std.hz
  obtain ⟨S, R, R', T, hRsyl, hR'syl, hTsyl, hRS, hR'S, hTS, hRR', hRT, hR'T⟩ :=
    Q3T8.Asc77.exists_twinSylow hΩ hK hz h.std.hK' h.std.hne h.hJ
  have h8R : 8 ≤ Nat.card R := hΩ.eight_le_of_mem_RSet (mem_RSet_of_isSylow2In hK hRsyl)
  have hzR : z ∈ R := mem_of_isUniqueInvolution_of_isPGroup hz hRsyl.1 hRsyl.2.1 (by omega)
  refine (Q3T8.Asc77.ExactLayer.mem_tqMembers_iff_exists_sylow hΩ
      (Q3T8.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one h.tz_sq)).mpr
    ⟨h.hJ.1, T, hTsyl, fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
  have hxt : x * t = t * x := (h.ht.commute_of_mem (hTsyl.1 hx)).symm
  have hxz : x * z = z * x := (hRT z hzR x hx).symm
  calc x * (t * z) = (x * t) * z := by group
    _ = (t * x) * z := by rw [hxt]
    _ = t * (x * z) := by group
    _ = t * (z * x) := by rw [hxz]
    _ = (t * z) * x := by group
end Main
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson

theorem c21_12_exclude_proved :
    Q3T8.Asc77.C21_12_exclude := by
  intro G _ _ _ Ω K K' z u J t W h _
  have hΩ : Q3T7M.HM Ω := h.std.stand.modU
  have hK : K ∈ Ω := h.std.stand.mem
  have hK'Ω : K' ∈ Ω := h.std.hK'.1
  have hJΩ : J ∈ Ω := h.hJ.1
  have hP : Q3T8.Asc77.PartIHyp Ω := ⟨hΩ, h.std.stand.cls, h.std.stand.aEmpty⟩
  obtain ⟨S, R, R', T, hRsyl, hR'syl, hTsyl, hRS, hR'S, hTS, hRR', hRT, hR'T⟩ :=
    Q3T8.Asc77.exists_twinSylow hΩ hK h.std.hz h.std.hK' h.std.hne h.hJ
  obtain ⟨g, hg⟩ := Q3T8.Asc77.Thompson.exists_conj_mem_DSet hΩ h.hW S
  have hRD : conjSub g R ∈ DSet Ω W := hg R (mem_RSet_of_isSylow2In hK hRsyl) hRS
  have hR'D : conjSub g R' ∈ DSet Ω W := hg R' (mem_RSet_of_isSylow2In hK'Ω hR'syl) hR'S
  have hTD : conjSub g T ∈ DSet Ω W := hg T (mem_RSet_of_isSylow2In hJΩ hTsyl) hTS
  have hKg : conjSub g K ∈ Ω := hΩ.conjInvariant g K hK
  have hK'g : conjSub g K' ∈ Ω := hΩ.conjInvariant g K' hK'Ω
  have hJg : conjSub g J ∈ Ω := hΩ.conjInvariant g J hJΩ
  have hRsylg : IsSylow2In (conjSub g R) (conjSub g K) := hRsyl.conj g
  have hR'sylg : IsSylow2In (conjSub g R') (conjSub g K') := hR'syl.conj g
  have hTsylg : IsSylow2In (conjSub g T) (conjSub g J) := hTsyl.conj g
  have hTT := Q3T8.Asc77.Thompson.isTT_muDelta (hΩ : Q3T8.Asc77.HypOmegaMod Ω) h.hW
      (Q3CL.thompsonCube hP W h.hW)
  obtain ⟨r, hr, hrW⟩ := Q3CL.Thompson.exists_not_mem_of_mem_D hΩ h.hW hRD
  obtain ⟨r', hr', hr'W⟩ := Q3CL.Thompson.exists_not_mem_of_mem_D hΩ h.hW hR'D
  obtain ⟨t', ht', ht'W⟩ := Q3CL.Thompson.exists_not_mem_of_mem_D hΩ h.hW hTD
  obtain ⟨a, ha, haeq⟩ := exists_muDelta_eq_piG hRD hr hrW
  obtain ⟨b, hb, hbeq⟩ := exists_muDelta_eq_piG hR'D hr' hr'W
  obtain ⟨c, hc, hceq⟩ := exists_muDelta_eq_piG hTD ht' ht'W
  have hKK' : conjSub g K ≠ conjSub g K' := fun e => h.std.hne.symm ((conjSub_inj g).mp e)
  have hKJ : conjSub g K ≠ conjSub g J := fun e => by
    have := h.hJ.2 K (mem_twinSet_self hK h.std.hz)
    exact this.2.1 ((conjSub_inj g).mp e).symm
  have hK'J : conjSub g K' ≠ conjSub g J := fun e => by
    have := h.hJ.2 K' h.std.hK'
    exact this.2.1 ((conjSub_inj g).mp e).symm
  have hab : a ≠ b := fun e =>
    Q3T8.Asc77.piG_ne_of_ne_members hΩ h.hW hRD hR'D hKg hK'g hRsylg hR'sylg hKK' hr hr' hr'W
      (haeq.symm.trans ((congrArg Subtype.val e).trans hbeq))
  have hac : a ≠ c := fun e =>
    Q3T8.Asc77.piG_ne_of_ne_members hΩ h.hW hRD hTD hKg hJg hRsylg hTsylg hKJ hr ht' ht'W
      (haeq.symm.trans ((congrArg Subtype.val e).trans hceq))
  have hbc : b ≠ c := fun e =>
    Q3T8.Asc77.piG_ne_of_ne_members hΩ h.hW hR'D hTD hK'g hJg hR'sylg hTsylg hK'J hr' ht' ht'W
      (hbeq.symm.trans ((congrArg Subtype.val e).trans hceq))
  have hab' : a * b = b * a :=
    muGroup_comm_of_comm hRD hR'D hr hr' ((hRR'.conjSub g) r hr r' hr') haeq hbeq
  have hac' : a * c = c * a :=
    muGroup_comm_of_comm hRD hTD hr ht' ((hRT.conjSub g) r hr t' ht') haeq hceq
  have hbc' : b * c = c * b :=
    muGroup_comm_of_comm hR'D hTD hr' ht' ((hR'T.conjSub g) r' hr' t' ht') hbeq hceq
  constructor
  · rintro ⟨e⟩
    have hTT3 := T7A.isTT_map_equiv hTT e
    exact T7A.no_two_commuting_perm3 hTT3 _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      (fun e2 => hab (e.injective e2)) (by rw [← map_mul, ← map_mul, hab'])
  · rintro ⟨e⟩
    have hTT4 := T7A.isTT_map_equiv hTT e
    exact T7A.no_three_commuting_perm4 hTT4 _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩
      (fun e2 => hab (e.injective e2)) (fun e2 => hac (e.injective e2))
      (fun e2 => hbc (e.injective e2))
      (by rw [← map_mul, ← map_mul, hab']) (by rw [← map_mul, ← map_mul, hac'])
      (by rw [← map_mul, ← map_mul, hbc'])

theorem c21_12_proved :
    Q3T8.Asc77.C21_12 := Q3T8.Asc77.c21_12_of Q3T8.Asc77.l7_17_proved
    (Q3T8.Asc77.c21_12_exclude_proved)
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Asc77.AscE184Sect CFSG.ClassicalInvolution.Asc77.ExactLayer
open scoped commutatorElement
section Sections
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {A : Subgroup G}

theorem section_connected_or_orbit
    {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}
    (hΩ : Q3T7M.HM Ω)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (hY : Q3T8.Asc77.ExactLayer.exactLayer Ω c ≠ ⊤)
    (hIH : Uniform.IH8T 3 1 (Nat.card G)) (h3s : Q3T8.Asc77.T3.Thm3SectBelow (Nat.card G))
    {B : Subgroup G} (hB : B ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω c) :
    SectionConnected Ω c ∨
      ∀ M ∈ quotFamily (Q3T8.Asc77.ExactLayer.exactPair Ω c)
          (classicalInvolutionOddCore ↥(Q3T8.Asc77.ExactLayer.exactLayer Ω c)),
        ∃ y : ↥(Q3T8.Asc77.ExactLayer.exactLayer Ω c) ⧸
            classicalInvolutionOddCore ↥(Q3T8.Asc77.ExactLayer.exactLayer Ω c),
          conjSub y (((Q3T8.Asc77.ExactLayer.exactCore c B).subgroupOf
            (Q3T8.Asc77.ExactLayer.exactLayer Ω c)).map
            (QuotientGroup.mk' (classicalInvolutionOddCore
              ↥(Q3T8.Asc77.ExactLayer.exactLayer Ω c)))) = M := by
  set Y := Q3T8.Asc77.ExactLayer.exactLayer Ω c with hYdef
  set Λ : Set (Subgroup ↥Y) := Q3T8.Asc77.ExactLayer.exactPair Ω c with hΛdef
  set N₀ : Subgroup ↥Y := classicalInvolutionOddCore ↥Y with hN₀def
  have hN₀odd : Odd (Nat.card N₀) := CFSG.ComponentClassification.OddCore.odd_card ↥Y
  have hΛ : Q3T7M.HM Λ := Q3T8.Asc77.ExactLayer.hypOmegaMod_exactPair hΩ hc2
  have hΛ' : Q3T7M.HM (quotFamily Λ N₀) := oddQuotHyp ↥Y Λ hΛ N₀ hN₀odd
  have hltY : Nat.card ↥Y < Nat.card G :=
    lt_of_le_of_ne (Subgroup.card_le_card_group _)
      fun h => hY (Subgroup.eq_top_of_card_eq _ h)
  have hlt : Nat.card (↥Y ⧸ N₀) < Nat.card G := by
    have h1 : Nat.card (↥Y ⧸ N₀) ≤ Nat.card ↥Y :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_card N₀)
    omega
  have hOq : classicalInvolutionOddCore (↥Y ⧸ N₀) = ⊥ :=
    CFSG.ComponentClassification.OddCore.quotient_corefree ↥Y
  have hBΛ : (Q3T8.Asc77.ExactLayer.exactCore c B).subgroupOf Y ∈ Λ :=
    ⟨Q3T8.Asc77.ExactLayer.exactCore c B, Q3T8.Asc77.ExactLayer.exactCore_mem_exactFamily hB,
      Q3T8.Asc77.ExactLayer.exactCore_le_exactLayer hB, rfl⟩
  by_cases hconn : T3.DStarConnected (quotFamily Λ N₀)
  · exact Or.inl hconn
  · right
    have hΛA : ∀ L ∈ Λ, AEmpty Λ L := h3s _ hltY Λ hΛ hconn
    have hAΛ' := aEmpty_quotFamily hΛ hΛ' hN₀odd hΛA
    rcases dichotomy_of_thm4 (Q3T8.Asc77.thm4Below_of_ih hIH) hlt hΛ' hOq hAΛ'
      (map_mem_quotFamily hBΛ) with hc | horb
    · exact absurd (T3.dstarConnected_of_pivot (map_mem_quotFamily hBΛ) hc) hconn
    · exact horb

theorem exists_mem_sectionHull_conj_of_orbit
    {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}
    (hΩ : Q3T7M.HM Ω)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) {B : Subgroup G}
    (hB : B ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω c)
    (horb : ∀ M ∈ quotFamily (Q3T8.Asc77.ExactLayer.exactPair Ω c)
          (classicalInvolutionOddCore ↥(Q3T8.Asc77.ExactLayer.exactLayer Ω c)),
        ∃ y : ↥(Q3T8.Asc77.ExactLayer.exactLayer Ω c) ⧸
            classicalInvolutionOddCore ↥(Q3T8.Asc77.ExactLayer.exactLayer Ω c),
          conjSub y (((Q3T8.Asc77.ExactLayer.exactCore c B).subgroupOf
            (Q3T8.Asc77.ExactLayer.exactLayer Ω c)).map
            (QuotientGroup.mk' (classicalInvolutionOddCore
              ↥(Q3T8.Asc77.ExactLayer.exactLayer Ω c)))) = M)
    {J₁ : Subgroup G} (hJ₁ : J₁ ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω c) :
    ∃ g ∈ Q3T8.Asc77.ExactLayer.exactLayer Ω c, J₁ = conjSub g B := by
  set Y := Q3T8.Asc77.ExactLayer.exactLayer Ω c with hYdef
  set Λ : Set (Subgroup ↥Y) := Q3T8.Asc77.ExactLayer.exactPair Ω c with hΛdef
  set N₀ : Subgroup ↥Y := classicalInvolutionOddCore ↥Y with hN₀def
  have hΩg : Disconnected.AschTight.HypOmegaGen Ω := Q3T7.modU_toGen3 hΩ
  have hN₀odd : Odd (Nat.card N₀) := CFSG.ComponentClassification.OddCore.odd_card ↥Y
  have hΛ : Q3T7M.HM Λ := Q3T8.Asc77.ExactLayer.hypOmegaMod_exactPair hΩ hc2
  have hBΛ : (Q3T8.Asc77.ExactLayer.exactCore c B).subgroupOf Y ∈ Λ :=
    ⟨Q3T8.Asc77.ExactLayer.exactCore c B, Q3T8.Asc77.ExactLayer.exactCore_mem_exactFamily hB,
      Q3T8.Asc77.ExactLayer.exactCore_le_exactLayer hB, rfl⟩
  have hJ₁Λ : (Q3T8.Asc77.ExactLayer.exactCore c J₁).subgroupOf Y ∈ Λ :=
    ⟨Q3T8.Asc77.ExactLayer.exactCore c J₁, Q3T8.Asc77.ExactLayer.exactCore_mem_exactFamily hJ₁,
      Q3T8.Asc77.ExactLayer.exactCore_le_exactLayer hJ₁, rfl⟩
  obtain ⟨yb, hyb⟩ := horb _ (map_mem_quotFamily hJ₁Λ)
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N₀ yb
  have hKy : conjSub y ((Q3T8.Asc77.ExactLayer.exactCore c B).subgroupOf Y) ∈ Λ :=
    hΛ.conjInvariant y _ hBΛ
  have himg : (conjSub y ((Q3T8.Asc77.ExactLayer.exactCore c B).subgroupOf Y)).map
      (QuotientGroup.mk' N₀) =
      ((Q3T8.Asc77.ExactLayer.exactCore c J₁).subgroupOf Y).map (QuotientGroup.mk' N₀) := by
    rw [AscQuot.map_conjSub]
    exact hyb
  obtain ⟨n, -, hn⟩ := exists_conj_of_map_eq hΛ hN₀odd hKy hJ₁Λ himg
  refine ⟨((n * y : ↥Y) : G), (n * y).2, ?_⟩
  have hnyC : ((n * y : ↥Y) : G) ∈ Subgroup.centralizer ({c} : Set G) :=
    Q3T8.Asc77.ExactLayer.exactLayer_le_centralizer Ω c (n * y).2
  have h1 : (Q3T8.Asc77.ExactLayer.exactCore c J₁).subgroupOf Y =
      (Q3T8.Asc77.ExactLayer.exactCore c (conjSub ((n * y : ↥Y) : G) B)).subgroupOf Y := by
    rw [hn, ← conjSub_mul]
    have h6 := Q3T8.Asc77.ExactLayer.exactCore_conjSub ((n * y : ↥Y) : G) c B
    rw [Balance.Bootstrap.conj_eq_of_mem_centralizer_singleton hnyC] at h6
    rw [h6]
    exact conjSub_subgroupOf Y (n * y) (Q3T8.Asc77.ExactLayer.exactCore c B)
  have hBg : conjSub ((n * y : ↥Y) : G) B ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω c :=
    Q3T8.Asc77.ExactLayer.conjSub_mem_tqMembers hΩ.conjInvariant hnyC hB
  have h2 : Q3T8.Asc77.ExactLayer.exactCore c J₁ =
      Q3T8.Asc77.ExactLayer.exactCore c (conjSub ((n * y : ↥Y) : G) B) := by
    have hle1 : Q3T8.Asc77.ExactLayer.exactCore c J₁ ≤ Y :=
      Q3T8.Asc77.ExactLayer.exactCore_le_exactLayer hJ₁
    have hle2 : Q3T8.Asc77.ExactLayer.exactCore c (conjSub ((n * y : ↥Y) : G) B) ≤ Y :=
      Q3T8.Asc77.ExactLayer.exactCore_le_exactLayer hBg
    have := congrArg (Subgroup.map Y.subtype) h1
    rwa [Subgroup.map_subgroupOf_eq_of_le hle1, Subgroup.map_subgroupOf_eq_of_le hle2] at this
  exact Q3T7.eq_of_exactCore3_eq hΩg hc2 hJ₁ hBg h2

end Sections
section Frame
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem exists_mem_tqMembers_u
    (hΩ
    : Q3T7M.HM Ω)
    {K K' J : Subgroup G} {z u t : G} (hK : K ∈ Ω) (hz : IsUniqueInvolution K z)
    (hK' : K' ∈ twinSet Ω K) (hne : K' ≠ K) (hu : u ∈ K ⊔ K') (hu2 : u * u = 1) (hu1 : u ≠ 1)
    (hJ : J ∈ omegaOfSet Ω (twinSet Ω K)) (_ht : IsUniqueInvolution J t) :
    ∃ g ∈ K ⊔ K', conjSub g J ∈ omegaOfSet Ω (twinSet Ω K) ∧ conjSub g J ∈
        Q3T8.Asc77.ExactLayer.tqMembers Ω u := by
  have hK'Ω : K' ∈ Ω := hK'.1
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hK'
  have hJΩ : J ∈ Ω := hJ.1
  obtain ⟨R₁, R₂, hR₁, hR₂, hc, huR⟩ :=
    Q3T8.Asc77.T7A.exists_sylow_pair_of_mem (hΩ : Q3T8.Asc77.HypOmegaMod Ω) hK hK'Ω hne hz hzK' hu
        hu2 hu1
  obtain ⟨S₀, R₀, R₀', T₀, hR₀, hR₀', hT₀, hR₀S, hR₀'S, hT₀S, hc₀, hRT₀, hR'T₀⟩ :=
    Q3T8.Asc77.exists_twinSylow hΩ hK hz hK' hne hJ
  obtain ⟨g, hgQ, hgR, hgR'⟩ :=
    Q3T8.Asc77.T7A.exists_conj_sylow_pair hΩ hK hK'Ω hne hz hzK' hR₁ hR₂ hc hR₀ hR₀' hc₀
  have hKN : K' ≤ Subgroup.normalizer (K : Set G) := hΩ.le_normalizer_of_twin hK'Ω hK hne hzK' hz
  have hgiK : conjSub g⁻¹ K = K :=
    mem_normalizer_iff_conjSub_eq.mp (Subgroup.inv_mem _ ((sup_le Subgroup.le_normalizer hKN) hgQ))
  have hJ' : conjSub g J ∈ omegaOfSet Ω (twinSet Ω K) := by
    refine ⟨hΩ.conjInvariant g J hJΩ, fun L hL => ?_⟩
    have hL' : conjSub g⁻¹ L ∈ twinSet Ω K := by
      have := twinSet_conj hΩ.conjInvariant hL g⁻¹
      rwa [hgiK] at this
    have := omegaNbr_conj hΩ.conjInvariant (hJ.2 _ hL') g
    rwa [conjSub_conjSub_inv] at this
  refine ⟨g, hgQ, hJ', ?_⟩
  have hTsyl : IsSylow2In (conjSub g T₀) (conjSub g J) := hT₀.conj g
  have hcRT : Commutes R₁ (conjSub g T₀) := by
    have := hRT₀.conjSub g
    rwa [hgR] at this
  have hcR'T : Commutes R₂ (conjSub g T₀) := by
    have := hR'T₀.conjSub g
    rwa [hgR'] at this
  obtain ⟨x, hx, y, hy, hxy⟩ := AscE186.exists_mul_of_mem_sup_of_commutes hc huR
  have hTc : conjSub g T₀ ≤ Subgroup.centralizer ({u} : Set G) := by
    intro s hs
    rw [Subgroup.mem_centralizer_singleton_iff, ← hxy]
    have h1 : x * s = s * x := hcRT x hx s hs
    have h2 : y * s = s * y := hcR'T y hy s hs
    calc s * (x * y) = (s * x) * y := by group
      _ = (x * s) * y := by rw [h1]
      _ = x * (s * y) := by group
      _ = x * (y * s) := by rw [h2]
      _ = (x * y) * s := by group
  exact (Q3T8.Asc77.ExactLayer.mem_tqMembers_iff_exists_sylow hΩ
      (Q3T8.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hu2)).mpr
    ⟨hΩ.conjInvariant g J hJΩ, conjSub g T₀, hTsyl, hTc⟩

theorem sigmaGen_le_sigmaStarNorm
    (hΩ
    : Q3T8.Asc77.HypOmegaMod Ω) {K : Subgroup G}
    (hK : K ∈ Ω) : sigmaGen Ω K ≤ sigmaStarNorm Ω K := by
  refine iSup₂_le fun M hM g hg => ?_
  have hMd : M ∈ dstarComp Ω K := Q3T8.Asc77.T7A.mem_dstarComp_of_mem_dComp hΩ hM
  have hMΩ : M ∈ Ω := (T3.mem_dstarComp_symm hK hMd).1
  have hgM : conjSub g M = M := mem_normalizer_iff_conjSub_eq.mp (Subgroup.le_normalizer hg)
  have h1 : g ∈ sigmaStarNorm Ω M :=
    T7A.mem_sigmaStarNorm_of_conj hΩ.conjInvariant hMΩ
      (by rw [hgM]; exact Relation.ReflTransGen.refl)
  rwa [sigmaStarNorm_congr (T7A.dstarComp_eq_of_mem hK hMd)] at h1
end Frame
section Main
variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K K' J W :
    Subgroup G} {z u t : G}
omit [IsSimpleGroup G] in

theorem Hyp21.oddCore_centralizer_u_comm
    (h
    : Q3T8.Asc77.Hyp21 Ω K K' z u J t W)
    (hα : alphaOf (Subgroup.closure ({u, z} : Set G)) = ⊥) {n : G}
    (hn : n ∈ oddCoreOf (Subgroup.centralizer ({u} : Set G))) : n * z = z * n := by
  have hzA : z ∈ Subgroup.closure ({u, z} : Set G) := Subgroup.subset_closure (by simp)
  have huA : u ∈ Subgroup.closure ({u, z} : Set G) := Subgroup.subset_closure (by simp)
  have hmem : ⁅n, z⁆ ∈ ⁅oddCoreOf (Subgroup.centralizer ({u} : Set G)),
      Subgroup.closure ({u, z} : Set G)⁆ := Subgroup.commutator_mem_commutator hn hzA
  have hle : ⁅oddCoreOf (Subgroup.centralizer ({u} : Set G)),
      Subgroup.closure ({u, z} : Set G)⁆ ≤ alphaOf (Subgroup.closure ({u, z} : Set G)) := by
    unfold alphaOf
    exact le_sup_of_le_left (le_iSup₂_of_le u huA (le_iSup_of_le h.hu1 le_rfl))
  rw [hα] at hle
  exact commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp (hle hmem))

theorem c21_YSigma_of_sections
    (h3s : ∀ n, Q3T8.Generic.CITBelowU n → Q3T8.Asc77.T3.Thm3SectBelow
    n) :
    Q3T8.Asc77.C21_YSigma := by
  intro G _ _ _ Ω K K' z u J t W h hα hY _
  have hΩ : Q3T7M.HM Ω := h.std.stand.modU
  have hK : K ∈ Ω := h.std.stand.mem
  have hz : IsUniqueInvolution K z := h.std.hz
  have hBelow : Q3T8.Generic.CITBelowU (Nat.card G) := h.std.stand.below
  have hu2 : u * u = 1 := h.hu2
  have hu1 : u ≠ 1 := h.hu1
  have hcA : IsPGroup 2 (Subgroup.zpowers u) := Q3T8.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one
      hu2
  set A : Subgroup G := Subgroup.zpowers u with hAdef
  obtain ⟨g₀, -, hJ₀nbr, hJ₀t⟩ := Q3T8.Asc77.exists_mem_tqMembers_u hΩ hK hz h.std.hK' h.std.hne
      h.hu
    hu2 hu1 h.hJ h.ht
  set J₀ : Subgroup G := conjSub g₀ J with hJ₀def
  have hJ₀Ω : J₀ ∈ Ω := hΩ.conjInvariant g₀ J h.hJ.1
  have hJ₀d : J₀ ∈ dstarComp Ω K :=
    Relation.ReflTransGen.single ⟨hJ₀Ω, Or.inl (Q3T8.Asc77.T3.omegaNbr_subset_omegaStarNbr hΩ K
      (hJ₀nbr.2 K (mem_twinSet_self hK hz)))⟩

  set Y : Subgroup G := Q3T8.Asc77.ExactLayer.exactLayer Ω u with hYdef
  have hYtop : Y ≠ ⊤ := by
    intro htop
    have hle : Y ≤ Subgroup.centralizer ({u} : Set G) :=
      Q3T8.Asc77.ExactLayer.exactLayer_le_centralizer Ω u
    rw [htop, top_le_iff] at hle
    have hcomm : ∀ g : G, g * u = u * g := fun g =>
      Subgroup.mem_centralizer_singleton_iff.mp (hle ▸ Subgroup.mem_top g)
    obtain ⟨V, hV, -⟩ := IsSylow2In.exists_ge (isPGroup_two_bot (G := G)) (bot_le : ⊥ ≤ K)
    have hVR : V ∈ RSet Ω := mem_RSet_of_isSylow2In hK hV
    obtain ⟨x, -, y, -, hxy⟩ := (hΩ.isQuatSub_of_mem_RSet hVR).exists_not_commute
    exact hu1 (T7A.eq_one_of_central ⟨x, y, hxy⟩ hcomm)
  have hinv : ∀ n ∈ oddCoreOf (Subgroup.centralizer ({u} : Set G)), n ∈ sigmaStarNorm Ω K := by
    intro n hn
    have hnz : n * z = z * n := h.oddCore_centralizer_u_comm hα hn
    have hnzn : n * z * n⁻¹ = z := by
      calc n * z * n⁻¹ = (z * n) * n⁻¹ := by rw [hnz]
        _ = z := by group
    have hKn : conjSub n K ∈ twinSet Ω K := ⟨hΩ.conjInvariant n K hK, z, hz, hnzn ▸ hz.conj n⟩
    exact T7A.mem_sigmaStarNorm_of_conj hΩ.conjInvariant hK
      (Q3T8.Asc77.AscE186.mem_dstarComp_of_twin hΩ hK hKn)
  have hYN : ∀ g ∈ Y, g ∈ sigmaStarNorm Ω K := fun g hg =>
    Q3T8.Asc77.sigmaGen_le_sigmaStarNorm hΩ hK (hY hg)
  have hall : ∀ M ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω u, M ∈ dstarComp Ω K := by
    intro M hM
    rcases Q3T8.Asc77.section_connected_or_orbit hΩ hcA hYtop h.std.stand.ih (h3s _ hBelow)
      hJ₀t with hconn | horb
    · obtain ⟨n, hn, J', hJ', hJ'd, rfl⟩ :=
        Q3T8.Asc77.exists_conj_tqMembers_of_connected hΩ hu2 hJ₀t hconn M hM
      exact ((mem_sigmaStarNorm_iff.mp (hinv n hn)) J').mp (hJ₀d.trans hJ'd)
    · obtain ⟨g, hg, rfl⟩ :=
        Q3T8.Asc77.exists_mem_sectionHull_conj_of_orbit hΩ hcA hJ₀t horb hM
      exact ((mem_sigmaStarNorm_iff.mp (hYN g hg)) J₀).mp hJ₀d
  intro c hc
  have h1 : conjSub c J₀ ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω u :=
      Q3T8.Asc77.ExactLayer.conjSub_mem_tqMembers hΩ.conjInvariant hc hJ₀t
  have hJJ : conjSub c J₀ ∈ dstarComp Ω J₀ :=
    (T3.mem_dstarComp_symm hK hJ₀d).2.trans (hall _ h1)
  have hcn : c ∈ sigmaStarNorm Ω J₀ := T7A.mem_sigmaStarNorm_of_conj hΩ.conjInvariant hJ₀Ω hJJ
  rwa [sigmaStarNorm_congr (T7A.dstarComp_eq_of_mem hK hJ₀d)] at hcn

end Main
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Asc77.AscE184Sect CFSG.ClassicalInvolution.Asc77.ExactLayer
open scoped commutatorElement
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {A : Subgroup G}

theorem dstarConnected_quot_of_twinTriple_gen
    {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}
    (hΩ : Q3T7M.HM Ω)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (hY : Q3T8.Asc77.ExactLayer.exactLayer Ω c ≠ ⊤)
    (hIH : Uniform.IH8T 3 1 (Nat.card G)) (hBelow : Q3T8.Generic.CITBelowU (Nat.card G))
    (h3s : Q3T8.Asc77.T3.Thm3SectBelow (Nat.card G)) (hMF : DStarConnectedTwinGen)
    (htt : TwinTriple (quotFamily (Q3T8.Asc77.ExactLayer.exactPair Ω c)
      (classicalInvolutionOddCore ↥(Q3T8.Asc77.ExactLayer.exactLayer Ω c)))) :
    T3.DStarConnected (quotFamily (Q3T8.Asc77.ExactLayer.exactPair Ω c)
      (classicalInvolutionOddCore ↥(Q3T8.Asc77.ExactLayer.exactLayer Ω c))) := by
  set Y := Q3T8.Asc77.ExactLayer.exactLayer Ω c with hYdef
  set Λ : Set (Subgroup ↥Y) := Q3T8.Asc77.ExactLayer.exactPair Ω c with hΛdef
  set N₀ : Subgroup ↥Y := classicalInvolutionOddCore ↥Y with hN₀def
  have hN₀odd : Odd (Nat.card N₀) := CFSG.ComponentClassification.OddCore.odd_card ↥Y
  have hΛ : Q3T7M.HM Λ := Q3T8.Asc77.ExactLayer.hypOmegaMod_exactPair hΩ hc2
  have hΛ' : Q3T7M.HM (quotFamily Λ N₀) := oddQuotHyp ↥Y Λ hΛ N₀ hN₀odd
  have hltY : Nat.card ↥Y < Nat.card G :=
    lt_of_le_of_ne (Subgroup.card_le_card_group _)
      fun h => hY (Subgroup.eq_top_of_card_eq _ h)
  have hlt : Nat.card (↥Y ⧸ N₀) < Nat.card G := by
    have h1 : Nat.card (↥Y ⧸ N₀) ≤ Nat.card ↥Y :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_card N₀)
    omega
  have hOq : classicalInvolutionOddCore (↥Y ⧸ N₀) = ⊥ :=
    CFSG.ComponentClassification.OddCore.quotient_corefree ↥Y
  have hgenΛ : omegaGen Λ = ⊤ :=
    omegaGen_restrictFamily_eq_top (Q3T8.Asc77.ExactLayer.exactFamily Ω c) Y
      (Q3T8.Asc77.ExactLayer.exactLayer_eq_iSup Ω c).symm
  have hgenQ : omegaGen (quotFamily Λ N₀) = ⊤ := omegaGen_quotFamily_eq_top Λ N₀ hgenΛ
  by_contra hdis
  have hΛA : ∀ L ∈ Λ, AEmpty Λ L := h3s _ hltY Λ hΛ hdis
  have hAΛ' := aEmpty_quotFamily hΛ hΛ' hN₀odd hΛA
  obtain ⟨K₀, hK₀, -⟩ := id htt
  rcases dichotomy_of_thm4 (Q3T8.Asc77.thm4Below_of_ih hIH) hlt hΛ' hOq hAΛ' hK₀ with hc | horb
  · exact hdis (T3.dstarConnected_of_pivot hK₀ hc)
  · have htrans : ∀ K ∈ quotFamily Λ N₀, ∀ L ∈ quotFamily Λ N₀,
        ∃ g : ↥Y ⧸ N₀, conjSub g K = L := by
      intro K hK L hL
      obtain ⟨y₁, hy₁⟩ := horb K hK
      obtain ⟨y₂, hy₂⟩ := horb L hL
      exact ⟨y₂ * y₁⁻¹, by rw [conjSub_mul, ← hy₁, conjSub_inv_conjSub, hy₂]⟩
    obtain ⟨D, hD⟩ := Q3T7.exists_omegaLieU_sect hBelow hlt hΛ' hOq hgenQ htrans ⟨_, hK₀⟩
    exact hdis (hMF _ _ ⟨hΛ', hOq, hgenQ, htrans, hAΛ'⟩ ⟨D, hD⟩ htt)

section Main
variable [IsSimpleGroup G] {K K' J W : Subgroup G} {z u t : G}
  (h : Q3T8.Asc77.Hyp21 Ω K K' z u J t W)
include h

theorem tqMembers_subset_dstarComp_gen
    (hMF : Q3T8.Asc77.DStarConnectedTwinGen)
    (h3s : ∀ n, Q3T8.Generic.CITBelowU n → Q3T8.Asc77.T3.Thm3SectBelow n) (h3 : Q3T8.Asc77.C21_3)
    (hα : alphaOf (Subgroup.closure ({u, z} : Set G)) = ⊥) :
    ∀ M ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω (t * z), M ∈ dstarComp Ω K := by
  have hΩ : Q3T7M.HM Ω := h.std.stand.modU
  have hK : K ∈ Ω := h.std.stand.mem
  have hK'Ω : K' ∈ Ω := h.std.hK'.1
  have hJΩ : J ∈ Ω := h.hJ.1
  have hz : IsUniqueInvolution K z := h.std.hz
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz h.std.hK'
  have hBelow : Q3T8.Generic.CITBelowU (Nat.card G) := h.std.stand.below
  set c : G := t * z with hcdef
  have hc2 : c * c = 1 := h.tz_sq
  have hc1 : c ≠ 1 := h.tz_ne_one
  have hcA : IsPGroup 2 (Subgroup.zpowers c) := Q3T8.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one
      hc2
  set A : Subgroup G := Subgroup.zpowers c with hAdef

  obtain ⟨S, R, R', T, hRsyl, hR'syl, hTsyl, hRS, hR'S, hTS, hRR', hRT, hR'T⟩ :=
    Q3T8.Asc77.exists_twinSylow hΩ hK hz h.std.hK' h.std.hne h.hJ
  have h8R : 8 ≤ Nat.card R := hΩ.eight_le_of_mem_RSet (mem_RSet_of_isSylow2In hK hRsyl)
  have h8T : 8 ≤ Nat.card T := hΩ.eight_le_of_mem_RSet (mem_RSet_of_isSylow2In hJΩ hTsyl)
  have hzR : z ∈ R := mem_of_isUniqueInvolution_of_isPGroup hz hRsyl.1 hRsyl.2.1 (by omega)
  have htT : t ∈ T := mem_of_isUniqueInvolution_of_isPGroup h.ht hTsyl.1 hTsyl.2.1 (by omega)
  have hcomm_tz : ∀ x : G, x * t = t * x → x * z = z * x → x * c = c * x := by
    intro x hxt hxz
    calc x * c = (x * t) * z := by rw [hcdef]; group
      _ = (t * x) * z := by rw [hxt]
      _ = t * (x * z) := by group
      _ = t * (z * x) := by rw [hxz]
      _ = c * x := by rw [hcdef]; group
  have hRc : R ≤ Subgroup.centralizer ({c} : Set G) := fun r hr =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (hcomm_tz r (hRT r hr t htT) (hz.commute_of_mem (hRsyl.1 hr)).symm)
  have hR'c : R' ≤ Subgroup.centralizer ({c} : Set G) := fun r hr =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (hcomm_tz r (hR'T r hr t htT) (hzK'.commute_of_mem (hR'syl.1 hr)).symm)
  have hTc : T ≤ Subgroup.centralizer ({c} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (hcomm_tz x (h.ht.commute_of_mem (hTsyl.1 hx)).symm (hRT z hzR x hx).symm)

  have hKt : K ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω c :=
    (Q3T8.Asc77.ExactLayer.mem_tqMembers_iff_exists_sylow hΩ hcA).mpr ⟨hK, R, hRsyl, hRc⟩
  have hK't : K' ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω c :=
    (Q3T8.Asc77.ExactLayer.mem_tqMembers_iff_exists_sylow hΩ hcA).mpr ⟨hK'Ω, R', hR'syl, hR'c⟩
  have hJt : J ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω c :=
    (Q3T8.Asc77.ExactLayer.mem_tqMembers_iff_exists_sylow hΩ hcA).mpr ⟨hJΩ, T, hTsyl, hTc⟩
  have hΩg : Disconnected.AschTight.HypOmegaGen Ω := Q3T7.modU_toGen3 hΩ
  have hRA : IsSylow2In R (Q3T8.Asc77.ExactLayer.exactCore c K) :=
    (Q3T8.Asc77.ExactLayer.isSylow2In_exactCore_iff hΩg hcA hK hKt.2).mpr ⟨hRsyl, hRc⟩
  have hR'A : IsSylow2In R' (Q3T8.Asc77.ExactLayer.exactCore c K') :=
    (Q3T8.Asc77.ExactLayer.isSylow2In_exactCore_iff hΩg hcA hK'Ω hK't.2).mpr ⟨hR'syl, hR'c⟩
  have hTA : IsSylow2In T (Q3T8.Asc77.ExactLayer.exactCore c J) :=
    (Q3T8.Asc77.ExactLayer.isSylow2In_exactCore_iff hΩg hcA hJΩ hJt.2).mpr ⟨hTsyl, hTc⟩

  have hJK : J ≠ K := (h.hJ.2 K (mem_twinSet_self hK hz)).2.1
  have hJK' : J ≠ K' := (h.hJ.2 K' h.std.hK').2.1
  have hT2 : IsPGroup 2 ↥T := hTsyl.2.1
  have hTz : T ≤ Subgroup.centralizer ({z} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hRT z hzR x hx).symm
  have hTNK : T ≤ Subgroup.normalizer (K : Set G) :=
    hΩ.le_normalizer_of_le_centralizer hK hJΩ (Ne.symm hJK) hz hTsyl.1 hT2 (by omega) hTz
  have hTNK' : T ≤ Subgroup.normalizer (K' : Set G) :=
    hΩ.le_normalizer_of_le_centralizer hK'Ω hJΩ (Ne.symm hJK') hzK' hTsyl.1 hT2
      (by omega) hTz
  have hTNKA : T ≤ Subgroup.normalizer
      ((Q3T8.Asc77.ExactLayer.exactCore c K : Subgroup G) : Set G) :=
    fun x hx => mem_normalizer_iff_conjSub_eq.mpr (by
      have h6 := Q3T8.Asc77.ExactLayer.exactCore_conjSub x c K
      rw [Balance.Bootstrap.conj_eq_of_mem_centralizer_singleton (hTc hx),
        mem_normalizer_iff_conjSub_eq.mp (hTNK hx)] at h6
      exact h6.symm)
  have hTNK'A : T ≤ Subgroup.normalizer
      ((Q3T8.Asc77.ExactLayer.exactCore c K' : Subgroup G) : Set G) :=
    fun x hx => mem_normalizer_iff_conjSub_eq.mpr (by
      have h6 := Q3T8.Asc77.ExactLayer.exactCore_conjSub x c K'
      rw [Balance.Bootstrap.conj_eq_of_mem_centralizer_singleton (hTc hx),
        mem_normalizer_iff_conjSub_eq.mp (hTNK' hx)] at h6
      exact h6.symm)
  set Y : Subgroup G := Q3T8.Asc77.ExactLayer.exactLayer Ω c with hYdef
  have hKY : Q3T8.Asc77.ExactLayer.exactCore c K ≤ Y :=
    Q3T8.Asc77.ExactLayer.exactCore_le_exactLayer hKt
  have hK'Y : Q3T8.Asc77.ExactLayer.exactCore c K' ≤ Y :=
    Q3T8.Asc77.ExactLayer.exactCore_le_exactLayer hK't
  have hJY : Q3T8.Asc77.ExactLayer.exactCore c J ≤ Y :=
    Q3T8.Asc77.ExactLayer.exactCore_le_exactLayer hJt
  have hΛ : Q3T7M.HM (Q3T8.Asc77.ExactLayer.exactPair Ω c) :=
    Q3T8.Asc77.ExactLayer.hypOmegaMod_exactPair hΩ hcA
  have hN₀odd : Odd (Nat.card (classicalInvolutionOddCore ↥Y)) :=
    CFSG.ComponentClassification.OddCore.odd_card ↥Y
  have hΛ' : Q3T7M.HM (quotFamily (Q3T8.Asc77.ExactLayer.exactPair Ω c)
      (classicalInvolutionOddCore ↥Y)) :=
    Q3T8.Asc77.oddQuotHyp ↥Y _ hΛ _ hN₀odd
  have hmemΛ : ∀ {M : Subgroup G}, M ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω c →
      (Q3T8.Asc77.ExactLayer.exactCore c M).subgroupOf Y ∈
        Q3T8.Asc77.ExactLayer.exactPair Ω c :=
    fun {M} hM => ⟨Q3T8.Asc77.ExactLayer.exactCore c M,
      Q3T8.Asc77.ExactLayer.exactCore_mem_exactFamily hM,
      Q3T8.Asc77.ExactLayer.exactCore_le_exactLayer hM, rfl⟩
  have htt : TwinTriple (quotFamily (Q3T8.Asc77.ExactLayer.exactPair Ω c)
      (classicalInvolutionOddCore ↥Y)) :=
    Q3T8.Asc77.twinTriple_quot hΛ' hN₀odd (hmemΛ hKt)
      (twinSet_subgroupOf hKY hK'Y (Q3T7.exactCore3_mem_twinSet hΩ hcA hKt hK't h.std.hK'))
      (hmemΛ hJt) (hRA.subgroupOf hKY) (hR'A.subgroupOf hK'Y) (hTA.subgroupOf hJY)
      (commutes_subgroupOf hRR') (commutes_subgroupOf hRT) (commutes_subgroupOf hR'T)
      (le_normalizer_subgroupOf_of_le hKY hTNKA) (le_normalizer_subgroupOf_of_le hK'Y hTNK'A)
  have hYtop : Y ≠ ⊤ := by
    intro htop
    have hle : Y ≤ Subgroup.centralizer ({c} : Set G) :=
      Q3T8.Asc77.ExactLayer.exactLayer_le_centralizer Ω c
    rw [htop, top_le_iff] at hle
    have hcomm : ∀ g : G, g * c = c * g := fun g =>
      Subgroup.mem_centralizer_singleton_iff.mp (hle ▸ Subgroup.mem_top g)
    obtain ⟨V, hV, -⟩ := IsSylow2In.exists_ge (isPGroup_two_bot (G := G)) (bot_le : ⊥ ≤ K)
    have hVR : V ∈ RSet Ω := mem_RSet_of_isSylow2In hK hV
    obtain ⟨x, -, y, -, hxy⟩ := (hΩ.isQuatSub_of_mem_RSet hVR).exists_not_commute
    exact hc1 (T7A.eq_one_of_central ⟨x, y, hxy⟩ hcomm)
  have hconn : Q3T8.Asc77.SectionConnected Ω c :=
    Q3T8.Asc77.dstarConnected_quot_of_twinTriple_gen hΩ hcA hYtop h.std.stand.ih hBelow
      (h3s _ hBelow) hMF htt
  have hJd : J ∈ dstarComp Ω K :=
    Relation.ReflTransGen.single ⟨hJΩ, Or.inl (Q3T8.Asc77.T3.omegaNbr_subset_omegaStarNbr hΩ K
      (h.hJ.2 K (mem_twinSet_self hK hz)))⟩
  intro M hM
  obtain ⟨n, hn, J', hJ', hJ'd, rfl⟩ :=
    Q3T8.Asc77.exists_conj_tqMembers_of_connected hΩ hc2 hJt hconn M hM
  have hnz : n * z = z * n := h.oddCore_centralizer_tz_comm h3 hα hn
  have hnzn : n * z * n⁻¹ = z := by
    calc n * z * n⁻¹ = (z * n) * n⁻¹ := by rw [hnz]
      _ = z := by group
  have hKn : conjSub n K ∈ twinSet Ω K := ⟨hΩ.conjInvariant n K hK, z, hz, hnzn ▸ hz.conj n⟩
  have hnN : n ∈ sigmaStarNorm Ω K :=
    T7A.mem_sigmaStarNorm_of_conj hΩ.conjInvariant hK
      (Q3T8.Asc77.AscE186.mem_dstarComp_of_twin hΩ hK hKn)
  exact ((mem_sigmaStarNorm_iff.mp hnN) J').mp (hJd.trans hJ'd)

theorem centralizer_tz_le_sigmaStarNorm_gen
    (hMF : Q3T8.Asc77.DStarConnectedTwinGen)
    (h3s : ∀ n, Q3T8.Generic.CITBelowU n → Q3T8.Asc77.T3.Thm3SectBelow n) (h3 : Q3T8.Asc77.C21_3)
    (hα : alphaOf (Subgroup.closure ({u, z} : Set G)) = ⊥) :
    Subgroup.centralizer ({t * z} : Set G) ≤ sigmaStarNorm Ω K := by
  have hΩ : Q3T7M.HM Ω := h.std.stand.modU
  have hK : K ∈ Ω := h.std.stand.mem
  have hJΩ : J ∈ Ω := h.hJ.1
  have hJd : J ∈ dstarComp Ω K :=
    Relation.ReflTransGen.single ⟨hJΩ, Or.inl (Q3T8.Asc77.T3.omegaNbr_subset_omegaStarNbr hΩ K
      (h.hJ.2 K (mem_twinSet_self hK h.std.hz)))⟩
  intro g hg
  have hgJ : conjSub g J ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω (t * z) :=
    Q3T8.Asc77.ExactLayer.conjSub_mem_tqMembers hΩ.conjInvariant hg h.mem_tqMembers_tz_J
  have h1 : conjSub g J ∈ dstarComp Ω K :=
    Q3T8.Asc77.tqMembers_subset_dstarComp_gen h hMF h3s h3 hα _ hgJ
  have hJJ : conjSub g J ∈ dstarComp Ω J := (T3.mem_dstarComp_symm hK hJd).2.trans h1
  have hgJn : g ∈ sigmaStarNorm Ω J :=
    T7A.mem_sigmaStarNorm_of_conj hΩ.conjInvariant hJΩ hJJ
  rwa [sigmaStarNorm_congr (T7A.dstarComp_eq_of_mem hK hJd)] at hgJn
end Main

theorem c21_13_star_of_sections_gen
    (hMF : Q3T8.Asc77.DStarConnectedTwinGen)
    (h3s : ∀ n, Q3T8.Generic.CITBelowU n → Q3T8.Asc77.T3.Thm3SectBelow n) (h3 : Q3T8.Asc77.C21_3) :
    Q3T8.Asc77.C21_13_star := by
  intro G _ _ _ Ω K K' z u J t W h hα hD heq
  apply hD
  have hΩ : Q3T7M.HM Ω := h.std.stand.modU
  have hcA : IsPGroup 2 (Subgroup.zpowers (t * z)) :=
      Q3T8.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one h.tz_sq
  refine iSup₂_le fun R hR => iSup_le fun hRc => ?_
  obtain ⟨J', hJ'Ω, hRJ'⟩ := exists_isSylow2In_of_mem_RSet hR
  have hJ't : J' ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω (t * z) :=
    (Q3T8.Asc77.ExactLayer.mem_tqMembers_iff_exists_sylow hΩ hcA).mpr ⟨hJ'Ω, R, hRJ', hRc⟩
  have hdst := Q3T8.Asc77.tqMembers_subset_dstarComp_gen h hMF h3s h3 hα J' hJ't
  rw [← heq] at hdst
  exact hRJ'.1.trans (le_iSup₂_of_le J' hdst le_rfl)

theorem c21_17_tz_of_sections_gen
    (hMF : Q3T8.Asc77.DStarConnectedTwinGen)
    (h3s : ∀ n, Q3T8.Generic.CITBelowU n → Q3T8.Asc77.T3.Thm3SectBelow n) (h3 : Q3T8.Asc77.C21_3) :
    Q3T8.Asc77.C21_17_tz := by
  intro G _ _ _ Ω K K' z u J t W h hα _ _
  exact Q3T8.Asc77.centralizer_tz_le_sigmaStarNorm_gen h hMF h3s h3 hα
end Asc77

end

end CFSG.ClassicalInvolution.Q3.Q3T8
